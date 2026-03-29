import gamelib
import random
import math
from sys import maxsize
import json

"""
=============================================================================
TERMINAL STRATEGY — V4  (Adaptive Zone-Intel Edition)
=============================================================================

ZONE MAP (our half, y = 0..13):
  ┌─────────────────────────────────┐  y=13
  │  LEFT TRI  │  MID RECT  │ RIGHT │
  │  (x < 9)   │ (x 9-18,   │(x>18) │
  │            │  y 8-13)   │       │
  │            ├────────────┤       │
  │            │ DOWN TRI   │       │
  │            │(x 9-18,    │       │
  │            │  y 0-7)    │       │
  └─────────────────────────────────┘  y=0

DEFENSE PHILOSOPHY:
  • No walls ever.  Turrets + interceptors only.
  • Turrets (12,10) and (15,10) deployed on turn 0 first.
  • (13,8) support REMOVED — replaced by turret pressure.
  • Zone-breach log drives reactive turret placement.
  • Interceptors patrol the hottest breach zone.
  • Upgraded support deployed only when enemy is changing tactics.

ATTACK PHILOSOPHY:
  • Max MP per attack = _max_attack_mp (starts 4, grows to 6 adaptively).
  • Early (turns 0-4)  : scouts only, small decoy probes.
  • Mid   (turns 5-14) : scouts + side-switching by intel; NO demolisher.
  • Late  (turns 15+)  : full strategy with demolisher if corner blocked.
  • If avg efficiency < 80% after mid-stage → switch side / strategy.
  • Demolisher spawns at nearest corner point, clears path BEFORE scouts follow.
  • Never dump > _max_attack_mp MP on a single attack wave.

INTELLIGENCE PIPELINE:
  1. on_action_frame → breach log (per zone) + enemy_hp_after
  2. _update_path_intel → simulate paths, measure enemy density/weak-point
  3. _update_enemy_intel → detect tactic changes from efficiency swings
  4. Defense + offense decisions consume this intel every turn.
=============================================================================
"""


class AlgoStrategy(gamelib.AlgoCore):

    # Zone labels
    Z_LEFT  = "left_tri"
    Z_RIGHT = "right_tri"
    Z_MID   = "mid_rect"
    Z_DOWN  = "down_tri"

    def __init__(self):
        super().__init__()
        seed = random.randrange(maxsize)
        random.seed(seed)
        gamelib.debug_write('Random seed: {}'.format(seed))

    # =========================================================================
    # STARTUP
    # =========================================================================

    def on_game_start(self, config):
        gamelib.debug_write('Configuring V4 strategy...')
        self.config = config
        global WALL, SUPPORT, TURRET, SCOUT, DEMOLISHER, INTERCEPTOR, MP, SP
        WALL        = config["unitInformation"][0]["shorthand"]
        SUPPORT     = config["unitInformation"][1]["shorthand"]
        TURRET      = config["unitInformation"][2]["shorthand"]
        SCOUT       = config["unitInformation"][3]["shorthand"]
        DEMOLISHER  = config["unitInformation"][4]["shorthand"]
        INTERCEPTOR = config["unitInformation"][5]["shorthand"]
        MP, SP = 1, 0

        # ---- Zone boundaries ----
        self.MID_X = set(range(9, 19))   # 9..18
        self.MID_Y = set(range(8, 14))   # 8..13
        self.DN_Y  = set(range(0, 8))    # 0..7  (down-tri, same X as mid)

        # ---- Base layout (NO (13,8) support) ----
        # Turrets: (12,10)* and (15,10)* deployed FIRST on turn 0
        self.TURN0_TURRETS        = [[12, 10], [15, 10]]
        self.BASE_TURRETS         = [[11, 9], [16, 9], [12, 10], [15, 10]]
        self.BASE_TURRETS_UPGRADE = [[12, 10], [15, 10]]
        # Supports: (13,8) removed → remaining cluster
        self.BASE_SUPPORTS        = [[12, 9], [13, 9], [14, 9], [15, 9], [14, 8]]
        self.BASE_SUPPORTS_UPG    = [[12, 9], [15, 9]]

        # ---- Breach / zone tracking ----
        self.breach_counts = {}   # (x,y) -> int
        self.breach_turns  = {}   # (x,y) -> [turn#, ...]
        self.zone_breach   = {self.Z_LEFT: 0, self.Z_RIGHT: 0,
                               self.Z_MID: 0,  self.Z_DOWN: 0}
        self.current_turn  = 0

        # ---- Attack log ----
        # {side, eff, turn, spawn, path_density, dmg, units, unit_type}
        self.attack_log = []

        # ---- Path intelligence (per side) ----
        # Stores simulated paths + derived enemy density on those paths
        self.path_intel = {
            'left':  {'recent_paths': [], 'avg_density': 0.0, 'weak_point': None},
            'right': {'recent_paths': [], 'avg_density': 0.0, 'weak_point': None},
        }

        # ---- Enemy intel (aggregated) ----
        self.enemy_intel = {
            'left_density':   0,
            'right_density':  0,
            'left_weak':      None,
            'right_weak':     None,
            'tactic_changes': 0,      # times enemy significantly changed approach
            'last_breach_zone': None,
        }

        # ---- Corridor intel (per probing side) ----
        self.corridor_intel = {
            'left':  {'dmg': 0, 'units': 0, 'last': -99,
                      'blocked': False, 'soft': False, 'eff_history': []},
            'right': {'dmg': 0, 'units': 0, 'last': -99,
                      'blocked': False, 'soft': False, 'eff_history': []},
        }

        # ---- Probe state ----
        self._probing_side             = 'right'
        self._probe_consecutive_blocks = 0

        # ---- Per-turn attack tracking ----
        self.enemy_hp_before         = 30
        self.enemy_hp_after          = 30
        self.attack_side_this_turn   = None
        self.attack_units_this_turn  = 0
        self._last_spawn_coord       = None

        # ---- Adaptive attack budget ----
        # Max MP to commit in a single attack wave (grows with turns)
        self._max_attack_mp  = 4
        self._min_attack_mp  = 3    # don't attack below this

        # ---- Efficiency tracking ----
        self._recent_effs    = []   # rolling window of efficiencies
        self._eff_window     = 5
        self._eff_threshold  = 0.80  # 80% target

        # ---- Reactive placement registry ----
        self._reactive_placed = set()

        # ---- Interceptor patrol map (zone -> spawn point) ----
        self._icept_patrol = {
            self.Z_LEFT:  [5, 12],
            self.Z_RIGHT: [22, 12],
            self.Z_MID:   [13, 12],
            self.Z_DOWN:  [13, 10],
        }

    # =========================================================================
    # ZONE CLASSIFIER
    # =========================================================================

    def zone_of(self, x, y):
        """Classify a tile on OUR side into one of the 4 defense zones."""
        if x in self.MID_X and y in self.MID_Y:
            return self.Z_MID
        if x in self.MID_X and y in self.DN_Y:
            return self.Z_DOWN
        if x < 9:
            return self.Z_LEFT
        return self.Z_RIGHT

    # =========================================================================
    # MAIN TURN
    # =========================================================================

    def on_turn(self, turn_state):
        gs = gamelib.GameState(self.config, turn_state)
        t  = gs.turn_number
        mp = gs.get_resource(MP)
        hp = gs.my_health
        self.current_turn = t
        gs.suppress_warnings(True)
        gamelib.debug_write('=== Turn {} | MP:{:.1f} HP:{} ==='.format(t, mp, hp))

        # 1. Log previous attack result
        self._process_attack_result(gs, t)

        # 2. Update intelligence layers
        self._update_path_intel(gs)
        self._update_enemy_intel()

        # 3. Adapt attack budget for this turn
        self._adapt_budget(t)

        # 4. Defense
        self._build_defense(gs, t, mp)

        # 5. Offense
        self._run_offense(gs, t, hp, mp)

        gs.submit_turn()

    # =========================================================================
    # ATTACK RESULT PROCESSING
    # =========================================================================

    def _process_attack_result(self, gs, t):
        """Record how last turn's attack performed and update corridor / probe state."""
        dmg = max(0, self.enemy_hp_before - self.enemy_hp_after)

        if self.attack_side_this_turn and self.attack_units_this_turn > 0:
            side  = self.attack_side_this_turn
            units = self.attack_units_this_turn
            eff   = dmg / units if units > 0 else 0.0

            entry = {
                'side':     side,
                'eff':      eff,
                'turn':     t - 1,
                'spawn':    self._last_spawn_coord,
                'dmg':      dmg,
                'units':    units,
            }
            self.attack_log.append(entry)
            gamelib.debug_write('AttackLog: {}'.format(entry))

            # Corridor intel update
            ci = self.corridor_intel[side]
            ci['dmg']   += dmg
            ci['units'] += units
            ci['last']   = t - 1
            ci['eff_history'].append(eff)
            if len(ci['eff_history']) > self._eff_window:
                ci['eff_history'].pop(0)

            if units >= 3:
                ci['soft']    = (eff >= 0.3)
                ci['blocked'] = (eff < 0.15)
                if ci['blocked']:
                    self._probe_consecutive_blocks += 1
                else:
                    self._probe_consecutive_blocks = 0

            self._recent_effs.append(eff)
            if len(self._recent_effs) > self._eff_window:
                self._recent_effs.pop(0)

            # Auto-switch probe side after 2 consecutive blocks
            if self._probe_consecutive_blocks >= 2:
                other = 'right' if self._probing_side == 'left' else 'left'
                gamelib.debug_write('Probe switch {} → {}'.format(self._probing_side, other))
                self._probing_side             = other
                self._probe_consecutive_blocks = 0

        # Reset per-turn state
        self.enemy_hp_before        = gs.enemy_health
        self.enemy_hp_after         = gs.enemy_health
        self.attack_side_this_turn  = None
        self.attack_units_this_turn = 0

    # =========================================================================
    # INTELLIGENCE — Path Analysis
    # =========================================================================

    def _update_path_intel(self, gs):
        """
        Simulate the path from each side's best spawn and measure how
        many enemy attackers cover each tile on that path.
        Stores avg density and the weakest (least-covered) tile.
        """
        for side in ('left', 'right'):
            spawn = self._best_spawn(gs, side)
            path  = gs.find_path_to_edge(spawn)
            if not path:
                continue

            density   = 0
            weak_pt   = None
            weak_val  = 99999
            for p in path:
                n = len(gs.get_attackers(p, 0))
                density += n
                if n < weak_val:
                    weak_val = n
                    weak_pt  = p

            pi = self.path_intel[side]
            pi['recent_paths'].append(path)
            if len(pi['recent_paths']) > 5:
                pi['recent_paths'].pop(0)
            pi['avg_density'] = density / max(1, len(path))
            pi['weak_point']  = weak_pt

            self.enemy_intel['{}_density'.format(side)] = density
            self.enemy_intel['{}_weak'.format(side)]    = weak_pt

        gamelib.debug_write(
            'PathIntel L_den={:.2f} R_den={:.2f} L_weak={} R_weak={}'.format(
                self.path_intel['left']['avg_density'],
                self.path_intel['right']['avg_density'],
                self.path_intel['left']['weak_point'],
                self.path_intel['right']['weak_point']))

    # =========================================================================
    # INTELLIGENCE — Enemy Tactic Detection
    # =========================================================================

    def _update_enemy_intel(self):
        """
        Detect if the enemy is changing their defensive tactics by watching
        for large swings in our attack efficiency on the same side.
        Flags enemy_intel['tactic_changes'] which triggers upgraded support.
        """
        for side in ('left', 'right'):
            side_logs = [e for e in self.attack_log if e['side'] == side]
            if len(side_logs) < 2:
                continue
            swing = abs(side_logs[-1]['eff'] - side_logs[-2]['eff'])
            if swing > 0.45:
                self.enemy_intel['tactic_changes'] += 1
                gamelib.debug_write(
                    'Enemy tactic change #{} (side={}, swing={:.2f})'.format(
                        self.enemy_intel['tactic_changes'], side, swing))

    def _avg_eff(self):
        if not self._recent_effs:
            return 1.0
        return sum(self._recent_effs) / len(self._recent_effs)

    # =========================================================================
    # ADAPTIVE ATTACK BUDGET
    # =========================================================================

    def _adapt_budget(self, t):
        """
        Grow max MP per attack wave with the turn count.
        Pull back if efficiency is poor (don't dump MP into a wall).
          turn < 5  → budget 4
          turn 5-14 → budget 5
          turn 15+  → budget 6
        If avg efficiency < 50% (very poor), reduce budget by 1 extra.
        """
        if t < 5:
            self._max_attack_mp = 4
        elif t < 15:
            self._max_attack_mp = 5
        else:
            self._max_attack_mp = 6

        if self._avg_eff() < 0.50 and t >= 5:
            self._max_attack_mp = max(self._min_attack_mp, self._max_attack_mp - 1)

        gamelib.debug_write('Budget={} avg_eff={:.2f}'.format(
            self._max_attack_mp, self._avg_eff()))

    # =========================================================================
    # DEFENSE
    # =========================================================================

    def _build_defense(self, gs, t, mp):
        """
        Turn 0 : Deploy (12,10) and (15,10) turrets FIRST, upgraded immediately.
        Every  : Recover base layout (turrets → upgrade → supports → upgrade).
        Turn 2+: Zone-reactive turrets based on breach log.
        Always : Interceptors to patrol the hottest breach zone.
        Always : If enemy changing tactics → upgraded support in mid-rect.
        """
        if t == 0:
            gs.attempt_spawn(TURRET,   self.TURN0_TURRETS)
            gs.attempt_upgrade(        self.TURN0_TURRETS)

        # Recover base every turn
        gs.attempt_spawn(TURRET,   self.BASE_TURRETS)
        gs.attempt_upgrade(        self.BASE_TURRETS_UPGRADE)
        gs.attempt_spawn(SUPPORT,  self.BASE_SUPPORTS)
        gs.attempt_upgrade(        self.BASE_SUPPORTS_UPG)

        if t >= 2:
            self._reactive_zone_defense(gs)

        self._deploy_interceptors(gs, t, mp)

        if self.enemy_intel['tactic_changes'] >= 2:
            self._deploy_adaptive_support(gs)

    # ---- Reactive zone-based turret placement ----

    def _reactive_zone_defense(self, gs):
        """
        For each breached tile (sorted by severity), place turrets according to zone rules.
        Zone rules mirror the 4-part division:
          LEFT_TRI : corner pocket [4,11],[5,11] (2 turrets if count≥3 else 1)
          RIGHT_TRI: mirror corner [23,11],[22,11]
          MID_RECT : reinforce mid flanks  [11,10],[16,10],[13,11],[14,11]
          DOWN_TRI : junction breaches → 2 turrets at FAR corner (opposite x)
        All reactive turrets are upgraded if SP permits.
        """
        sorted_bc = sorted(self.breach_counts.items(), key=lambda kv: -kv[1])
        for (x, y), count in sorted_bc:
            zone = self.zone_of(x, y)
            dt   = len(set(self.breach_turns.get((x, y), [])))

            if zone == self.Z_LEFT:
                tgts = [[4, 11], [5, 11]] if count >= 3 else [[4, 11]]
                self._place_turrets(gs, tgts)

            elif zone == self.Z_RIGHT:
                tgts = [[23, 11], [22, 11]] if count >= 3 else [[23, 11]]
                self._place_turrets(gs, tgts)

            elif zone == self.Z_MID and dt >= 2:
                self._place_turrets(gs, [[11, 10], [16, 10], [13, 11], [14, 11]])

            elif zone == self.Z_DOWN and dt >= 2:
                # Junction → far corner
                tgts = [[23, 11], [22, 11]] if x <= 13 else [[4, 11], [5, 11]]
                self._place_turrets(gs, tgts)

    def _place_turrets(self, gs, targets):
        for t in targets:
            gs.attempt_spawn(TURRET, t)
            gs.attempt_upgrade([t])
            self._reactive_placed.add(tuple(t))

    # ---- Interceptor deployment ----

    def _deploy_interceptors(self, gs, t, mp):
        """
        Deploy 1-2 interceptors at the patrol point of the zone that has
        received the most enemy breaches. Skip if no breaches or not enough MP.
        Interceptors are DEFENSIVE mobile units — they chase enemy scouts.
        """
        if t < 2:
            return
        if not self.zone_breach or max(self.zone_breach.values()) == 0:
            return

        worst_zone = max(self.zone_breach, key=self.zone_breach.get)
        patrol_pt  = self._icept_patrol.get(worst_zone)
        if not patrol_pt:
            return

        # Reserve enough MP for offense; only spend 3-6 on interceptors
        n = 2 if self.zone_breach[worst_zone] >= 3 else 1
        cost = n * 3
        if mp - cost < self._min_attack_mp:
            return

        spawned = gs.attempt_spawn(INTERCEPTOR, patrol_pt, n)
        if spawned:
            gamelib.debug_write('Interceptor x{} at {} zone={}'.format(
                n, patrol_pt, worst_zone))

    # ---- Adaptive support when enemy is shifting tactics ----

    def _deploy_adaptive_support(self, gs):
        """
        When the enemy is frequently changing their attack approach, we can't
        pinpoint where they'll breach next. Deploy upgraded supports in the
        mid-rect to provide area-wide shielding for our mobile units.
        """
        adaptive = [[13, 9], [14, 9], [13, 10], [14, 10]]
        gs.attempt_spawn(SUPPORT, adaptive)
        gs.attempt_upgrade(adaptive)
        gamelib.debug_write('AdaptiveSupport deployed (tactic_changes={})'.format(
            self.enemy_intel['tactic_changes']))

    # =========================================================================
    # OFFENSE
    # =========================================================================

    def _run_offense(self, gs, t, hp, mp):
        """
        Turn 0            : diagonal rush with scouts (≤ budget).
        Early (t 1-4)     : small probes, scouts only — no demolisher.
        Mid   (t 5-14)    : probing with intel-guided side selection; no demolisher.
                            If avg_eff < 80% → switch strategy using path intel.
        Late  (t 15+)     : full strategy; demolisher corner-clear if needed
                            AND avg_eff (rolling) ≥ 80%.
        Desperation (HP≤15): dump all remaining MP regardless of stage.
        """
        if t == 0:
            self._attack_round0(gs, mp)
            return

        if mp < self._min_attack_mp:
            return

        is_early = (t < 5)
        is_late  = (t >= 15)
        avg_eff  = self._avg_eff()
        desperate = (hp <= 15)

        left_sp  = self._best_spawn(gs, 'left')
        right_sp = self._best_spawn(gs, 'right')
        side, spawn = self._choose_side(gs, left_sp, right_sp)

        # Budget cap (reduced for low efficiency)
        budget = min(int(mp), self._max_attack_mp)
        if desperate:
            budget = int(mp)

        # Graduated probing — avoid dumping all into unknown defense
        if not desperate:
            consec = self._consec_attacks_on(side)
            if consec == 0:
                budget = min(budget, 2)   # fresh probe: tiny decoy
            elif consec == 1:
                budget = min(budget, 4)   # second probe: small burst

        # ---- Demolisher corner-clear (late game only, eff ≥ threshold) ----
        if is_late and not is_early and (avg_eff >= self._eff_threshold or desperate):
            path_dmg = self._path_dmg(gs, spawn)
            # Corner is blocked if path damage would kill all scouts
            if path_dmg > 40 and budget >= 4:
                self._demolisher_clear_then_attack(gs, side, spawn, budget, left_sp, right_sp)
                return

        # ---- Pure scout attack ----
        if budget > 0:
            self._scout_attack(gs, side, spawn, budget)

    def _attack_round0(self, gs, mp):
        """Turn 0: Pick least-damage side, send scout rush (capped at budget)."""
        lsp = self._best_spawn(gs, 'left')
        rsp = self._best_spawn(gs, 'right')
        if self._path_dmg(gs, lsp) <= self._path_dmg(gs, rsp):
            side, spawn = 'left', lsp
        else:
            side, spawn = 'right', rsp

        self._probing_side = side
        budget = min(int(mp), self._max_attack_mp)
        self._scout_attack(gs, side, spawn, budget)

    # ---- Demolisher-first corner clear ----

    def _demolisher_clear_then_attack(self, gs, side, scout_spawn, budget, lsp, rsp):
        """
        Deploy demolisher(s) from the spawn point nearest to the blocked corner
        so the demolisher REACHES and CLEARS the fortified zone BEFORE scouts
        arrive — reducing HP enough for scouts to break through.

        Demolisher spawn selection:
          Left-side attack  (scouts go via bottom-left) →
              demo spawns at [3,10] (our left area, paths into enemy right cluster)
          Right-side attack →
              demo spawns at [24,10]

        After spawning demo, remaining budget → scouts at weakest path point.
        """
        demo_spawn  = [3, 10] if side == 'left' else [24, 10]
        n_demo      = max(1, budget // 4)          # each demolisher costs 4 MP
        mp_used     = n_demo * 4
        n_scouts    = max(0, budget - mp_used)

        # Identify the weakest point on the opposing path for scouts
        weak_pt = self.path_intel[side]['weak_point']
        if weak_pt is None:
            weak_pt = scout_spawn

        gamelib.debug_write(
            'DemoClr: {}x demo at {} then {}x scouts at {}'.format(
                n_demo, demo_spawn, n_scouts, weak_pt))

        d_spawned = gs.attempt_spawn(DEMOLISHER, demo_spawn, n_demo)
        s_spawned = 0
        if n_scouts > 0:
            s_spawned = gs.attempt_spawn(SCOUT, weak_pt, n_scouts)

        self.attack_side_this_turn  = side
        self.attack_units_this_turn = d_spawned + s_spawned
        self._last_spawn_coord      = demo_spawn

    # ---- Scout-only attack ----

    def _scout_attack(self, gs, side, spawn, budget):
        count = gs.attempt_spawn(SCOUT, spawn, budget)
        self.attack_side_this_turn  = side
        self.attack_units_this_turn = count
        self._last_spawn_coord      = spawn
        gamelib.debug_write('Scouts: {} → {} at {}'.format(count, side, spawn))

    # =========================================================================
    # ATTACK SIDE SELECTION (intelligence-driven)
    # =========================================================================

    def _choose_side(self, gs, lsp, rsp):
        """
        Priority order:
          1. If probing side hard-blocked and other is not → switch.
          2. Path-intel density gap ≥ 2 → attack sparser side.
          3. Continue current probing side.
        """
        ci_p = self.corridor_intel[self._probing_side]
        other = 'right' if self._probing_side == 'left' else 'left'
        ci_o  = self.corridor_intel[other]
        p_sp  = lsp if self._probing_side == 'left' else rsp
        o_sp  = rsp if self._probing_side == 'left' else lsp

        # 1. Switch if probe side blocked
        if ci_p['blocked'] and not ci_o['blocked']:
            gamelib.debug_write('SideSwitch (blocked): {} → {}'.format(
                self._probing_side, other))
            self._probing_side             = other
            self._probe_consecutive_blocks = 0
            return other, o_sp

        # 2. Path-intel density override
        dl = self.path_intel['left']['avg_density']
        dr = self.path_intel['right']['avg_density']
        gamelib.debug_write('Density L={:.2f} R={:.2f}'.format(dl, dr))
        if abs(dl - dr) >= 2:
            if dl < dr:
                gamelib.debug_write('DensityOverride → left (sparser)')
                self._probing_side = 'left'
                return 'left', lsp
            else:
                gamelib.debug_write('DensityOverride → right (sparser)')
                self._probing_side = 'right'
                return 'right', rsp

        return self._probing_side, p_sp

    # =========================================================================
    # UTILITIES
    # =========================================================================

    def _best_spawn(self, gs, side):
        """Least path-damage spawn for a given side."""
        cands = [[13, 0], [12, 1], [11, 2]] if side == 'left' else [[14, 0], [15, 1], [16, 2]]
        return self.least_damage_spawn_location(gs, cands)

    def _consec_attacks_on(self, side):
        """Count most-recent consecutive attack-log entries for this side."""
        c = 0
        for e in reversed(self.attack_log):
            if e['side'] == side:
                c += 1
            else:
                break
        return c

    def _path_dmg(self, gs, location):
        path = gs.find_path_to_edge(location)
        if not path:
            return 999999
        dmg  = 0
        unit = gamelib.GameUnit(TURRET, gs.config)
        for p in path:
            dmg += len(gs.get_attackers(p, 0)) * unit.damage_i
        return dmg

    def least_damage_spawn_location(self, gs, opts):
        best, best_d = opts[0], 999999
        for loc in opts:
            d = self._path_dmg(gs, loc)
            if d < best_d:
                best_d, best = d, loc
        return best

    def filter_blocked_locations(self, locs, gs):
        return [l for l in locs if not gs.contains_stationary_unit(l)]

    # =========================================================================
    # ACTION FRAME — breach + HP tracking
    # =========================================================================

    def on_action_frame(self, turn_string):
        state  = json.loads(turn_string)
        events = state.get("events", {})

        for breach in events.get("breach", []):
            loc  = breach[0]
            ours = (breach[4] == 1)   # 1 = our unit, scored against enemy

            if ours:
                # Our unit breached enemy edge → enemy loses 1 HP
                self.enemy_hp_after = max(0, self.enemy_hp_after - 1)
            else:
                # Enemy unit breached our edge → log it
                key = tuple(loc)
                self.breach_counts[key] = self.breach_counts.get(key, 0) + 1
                self.breach_turns.setdefault(key, []).append(self.current_turn)

                zone = self.zone_of(loc[0], loc[1])
                self.zone_breach[zone] = self.zone_breach.get(zone, 0) + 1
                self.enemy_intel['last_breach_zone'] = zone

                gamelib.debug_write('Breach@{} zone={} count={}'.format(
                    key, zone, self.breach_counts[key]))


if __name__ == "__main__":
    algo = AlgoStrategy()
    algo.start()