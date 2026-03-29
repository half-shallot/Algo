import gamelib
import random
import math
from sys import maxsize
import json

"""
=============================================================================
TERMINAL STRATEGY — V5  (Region-Ranked Attack + Zoned Adaptive Defense)
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

ATTACK REGIONS (5 ranked + 2 unranked exit zones):
  L_TRI   x 0-5    Left corner triangle,  spawns [1,12]..[4,9]
  L_RECT  x 6-11   Left rectangle,        spawns [6,7]..[10,11]
  CENTER  x 12-15  Middle corridor,        spawns [13,0]..[16,2]
  R_RECT  x 16-21  Right rectangle,       spawns [19,8]..[22,11]
  R_TRI   x 22-27  Right corner triangle, spawns [23,9]..[26,12]

  + 2 unranked exit zones (TOP_L_TRI, TOP_R_TRI) — where CENTER attacks score.

DEFENSE PHILOSOPHY:
  • No walls.  Turrets + supports + interceptors only.
  • Turn 0: support rectangle (upgraded) → inner turrets → corner turrets
            [0,13]/[27,13] → upgrade supports if SP left → 2 interceptors.
  • After round 1: if Z_MID breach ≥ 1 → place [11,7] and [13,7] once.
  • Side triangles: turret-heavy; ≤2 sparse supports after ≥3 turrets + count ≥5.
  • Mid-rect / down-tri: turrets only (no reactive supports).
  • Corner turret upgrades only when zone breach ≥ 3.
  • Mid-rect turrets are NEVER upgraded reactively.

ATTACK PHILOSOPHY:
  • Score 5 regions every turn using signal-attenuation formula:
      S(R) = 1_{H>0} · (H_end/H0)^γ · exp(-α·T - β·U - λ·C)
  • CENTER uses softer weights (long path to health edge — moderate degradation ok).
  • Blend raw score 75% / historical efficiency 25% for turn-over-turn stability.
  • Graduated probing: no history → budget 2, one test → budget 4, else full budget.
  • Late game (t≥15): demolisher clear if best region score < 0.10.
=============================================================================
"""


class AlgoStrategy(gamelib.AlgoCore):

    Z_LEFT  = "left_tri"
    Z_RIGHT = "right_tri"
    Z_MID   = "mid_rect"
    Z_DOWN  = "down_tri"

    REGION_IDS = ['L_TRI', 'L_RECT', 'CENTER', 'R_RECT', 'R_TRI']

    def __init__(self):
        super().__init__()
        seed = random.randrange(maxsize)
        random.seed(seed)
        gamelib.debug_write('Random seed: {}'.format(seed))

    # =========================================================================
    # STARTUP
    # =========================================================================

    def on_game_start(self, config):
        gamelib.debug_write('Configuring V5 strategy...')
        self.config = config
        global WALL, SUPPORT, TURRET, SCOUT, DEMOLISHER, INTERCEPTOR, MP, SP
        WALL        = config["unitInformation"][0]["shorthand"]
        SUPPORT     = config["unitInformation"][1]["shorthand"]
        TURRET      = config["unitInformation"][2]["shorthand"]
        SCOUT       = config["unitInformation"][3]["shorthand"]
        DEMOLISHER  = config["unitInformation"][4]["shorthand"]
        INTERCEPTOR = config["unitInformation"][5]["shorthand"]
        MP, SP = 1, 0

        # ---- Zone boundaries (our half, y=0..13) ----
        self.MID_X = set(range(9, 19))
        self.MID_Y = set(range(8, 14))
        self.DN_Y  = set(range(0, 8))

        # ---- Base layout ----
        # Turn-0 priority order: supports → inner turrets → corner turrets
        self.TURN0_SUPPORTS    = [[12, 10], [13, 10], [14, 10], [15, 10]]
        self.TURN0_TURRETS     = [[10, 9], [17, 9], [12, 11], [15, 11]]
        self.CORNER_TURRETS    = [[0, 13], [27, 13]]   # wide-angle corner guards

        # Recovery targets (same each turn)
        self.BASE_TURRETS      = [[10, 9], [17, 9], [12, 11], [15, 11]]
        self.BASE_SUPPORTS     = [[12, 10], [13, 10], [14, 10], [15, 10]]
        self.BASE_SUPPORTS_UPG = [[12, 10], [13, 10], [14, 10], [15, 10]]

        # Corner upgrade pools (side-tri breach pressure only — never mid-rect)
        self.CORNER_LEFT_TURRETS  = [[4, 11], [5, 11], [10, 9]]
        self.CORNER_RIGHT_TURRETS = [[23, 11], [22, 11], [17, 9]]

        # Mid-breach reinforcement (once, t≥1, when Z_MID first breached)
        self.MID_BREACH_TURRETS = [[11, 7], [13, 7]]
        self._mid_breach_placed = False

        # ---- Attack regions (5 ranked, sorted left → right) ----
        #
        # Weights rationale:
        #   Corner tris  α=0.15 β=0.09 λ=0.06 γ=1.8 — sharp penalty if blocked;
        #                short paths should be either clean or clearly dead.
        #   Side rects   α=0.12 β=0.08 λ=0.05 γ=1.6 — standard PDF defaults.
        #   CENTER       α=0.07 β=0.05 λ=0.03 γ=1.2 — softer; path goes all the
        #                way to the enemy health edge through top triangles, so
        #                moderate damage accumulation is expected and acceptable.
        #
        # Spawns avoid [0,13] and [27,13] (now occupied by CORNER_TURRETS).
        self.REGIONS = {
            'L_TRI': {
                'spawns': [[1, 12], [2, 11], [3, 10], [4, 9]],
                'w_t': 1.0, 'w_s': 3.5,
                'alpha': 0.15, 'beta': 0.09, 'lam': 0.06, 'gamma': 1.8,
            },
            'L_RECT': {
                'spawns': [[6, 7], [7, 8], [8, 9], [9, 10], [10, 11]],
                'w_t': 1.0, 'w_s': 3.5,
                'alpha': 0.12, 'beta': 0.08, 'lam': 0.05, 'gamma': 1.6,
            },
            'CENTER': {
                'spawns': [[13, 0], [12, 1], [14, 0], [15, 1], [11, 2], [16, 2]],
                'w_t': 1.0, 'w_s': 3.0,
                'alpha': 0.07, 'beta': 0.05, 'lam': 0.03, 'gamma': 1.2,
            },
            'R_RECT': {
                'spawns': [[19, 8], [20, 9], [21, 10], [22, 11]],
                'w_t': 1.0, 'w_s': 3.5,
                'alpha': 0.12, 'beta': 0.08, 'lam': 0.05, 'gamma': 1.6,
            },
            'R_TRI': {
                'spawns': [[26, 12], [25, 11], [24, 10], [23, 9]],
                'w_t': 1.0, 'w_s': 3.5,
                'alpha': 0.15, 'beta': 0.09, 'lam': 0.06, 'gamma': 1.8,
            },
        }

        # ---- Breach / zone tracking ----
        self.breach_counts = {}
        self.breach_turns  = {}
        self.zone_breach   = {self.Z_LEFT: 0, self.Z_RIGHT: 0,
                              self.Z_MID: 0,  self.Z_DOWN: 0}
        self.current_turn  = 0

        # ---- Attack tracking ----
        self.attack_log              = []
        self.enemy_hp_before         = 30
        self.enemy_hp_after          = 30
        self.attack_region_this_turn = None   # region ID attacked last turn
        self.attack_units_this_turn  = 0
        self._last_spawn_coord       = None
        # Per-region rolling efficiency (for score blending)
        self._region_eff_history     = {r: [] for r in self.REGION_IDS}

        # ---- Adaptive attack budget ----
        self._max_attack_mp = 4
        self._min_attack_mp = 3

        # ---- Rolling overall efficiency ----
        self._recent_effs = []
        self._eff_window  = 5

        # ---- Reactive placement registries ----
        self._reactive_placed         = set()
        self._reactive_support_placed = set()

        # ---- Interceptor patrol map (zone → spawn point) ----
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

        # 1. Record previous attack result
        self._process_attack_result(gs, t)

        # 2. Adapt attack budget
        self._adapt_budget(t)

        # 3. Defense
        self._build_defense(gs, t, mp)

        # 4. Offense
        self._run_offense(gs, t, hp, mp)

        gs.submit_turn()

    # =========================================================================
    # ATTACK RESULT PROCESSING
    # =========================================================================

    def _process_attack_result(self, gs, t):
        """Record how last turn's attack performed and update per-region history."""
        dmg = max(0, self.enemy_hp_before - self.enemy_hp_after)

        if self.attack_region_this_turn and self.attack_units_this_turn > 0:
            rid   = self.attack_region_this_turn
            units = self.attack_units_this_turn
            eff   = dmg / units if units > 0 else 0.0

            entry = {
                'region': rid, 'eff': eff, 'turn': t - 1,
                'spawn':  self._last_spawn_coord,
                'dmg': dmg, 'units': units,
            }
            self.attack_log.append(entry)
            gamelib.debug_write('AttackResult: region={} eff={:.2f} dmg={}'.format(
                rid, eff, dmg))

            # Overall rolling efficiency
            self._recent_effs.append(eff)
            if len(self._recent_effs) > self._eff_window:
                self._recent_effs.pop(0)

            # Per-region efficiency history
            if rid in self._region_eff_history:
                hist = self._region_eff_history[rid]
                hist.append(eff)
                if len(hist) > self._eff_window:
                    hist.pop(0)

        # Reset per-turn state
        self.enemy_hp_before         = gs.enemy_health
        self.enemy_hp_after          = gs.enemy_health
        self.attack_region_this_turn = None
        self.attack_units_this_turn  = 0

    # =========================================================================
    # ADAPTIVE ATTACK BUDGET
    # =========================================================================

    def _adapt_budget(self, t):
        """
        Budget cap grows with turns; pulled back when efficiency is very poor.
          t < 5   → 4 MP max
          t 5-14  → 5 MP max
          t ≥ 15  → 6 MP max
        If avg efficiency < 50% (from t≥5), cap reduced by 1 extra.
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
        Turn 0 — spend ALL available resources:
          1. 4-support mid-rect rectangle → upgrade immediately (shields first).
          2. 4 inner turrets (no upgrade).
          3. Corner turrets [0,13] and [27,13].
          4. Upgrade supports again if SP still available.
          5. 2 interceptors at [13,12] as turn-0 mobile wide-area cover.

        Every turn:
          - Recover BASE_TURRETS (no upgrade) + CORNER_TURRETS.
          - Recover + upgrade BASE_SUPPORTS.

        After round 1 (t≥1):
          - If Z_MID breach ≥ 1, place [11,7] and [13,7] once (mid-pass block).

        Turn 2+: zone-reactive placement + interceptor patrol.
        """
        if t == 0:
            gs.attempt_spawn(SUPPORT, self.TURN0_SUPPORTS)
            gs.attempt_upgrade(self.TURN0_SUPPORTS)
            gs.attempt_spawn(TURRET, self.TURN0_TURRETS)
            gs.attempt_spawn(TURRET, self.CORNER_TURRETS)
            gs.attempt_upgrade(self.BASE_SUPPORTS_UPG)          # if SP remaining
            gs.attempt_spawn(INTERCEPTOR, [13, 12], 2)          # mobile cover

        # Recovery every turn
        gs.attempt_spawn(TURRET,  self.BASE_TURRETS)
        gs.attempt_spawn(TURRET,  self.CORNER_TURRETS)
        gs.attempt_spawn(SUPPORT, self.BASE_SUPPORTS)
        gs.attempt_upgrade(self.BASE_SUPPORTS_UPG)

        # Mid-breach reinforcement (deploy once after first Z_MID breach)
        if (t >= 1
                and not self._mid_breach_placed
                and self.zone_breach[self.Z_MID] >= 1):
            for loc in self.MID_BREACH_TURRETS:
                gs.attempt_spawn(TURRET, loc)
            self._mid_breach_placed = True
            gamelib.debug_write('MidBreachReinforce @ {}'.format(self.MID_BREACH_TURRETS))

        if t >= 2:
            self._reactive_zone_defense(gs)

        self._deploy_interceptors(gs, t, mp)

    # ---- Reactive zone-based placement ----

    def _reactive_zone_defense(self, gs):
        """
        Zone-specific reactive placement driven by breach severity.

        LEFT_TRI / RIGHT_TRI  (side triangles — turret-heavy):
          • Fill turret pool scaled to breach severity (1, 2, or full pool).
          • Sparse support: max 1 per side, max 2 total — only when zone has
            ≥3 turrets already AND cumulative breach count ≥ 5.

        MID_RECT  : Turrets only.  No reactive supports regardless of pressure.
                    (Do not add supports in response to corner attacks.)

        DOWN_TRI  : Far-corner junction turrets only (no supports).

        Corner pressure upgrade at end of every pass:
          Upgrades turrets in CORNER_LEFT/RIGHT_TURRETS when that zone's
          breach count ≥ 3.  Mid-rect turrets are NEVER upgraded.
        """
        live_supp = sum(
            1 for loc in self._reactive_support_placed
            if gs.contains_stationary_unit(list(loc))
        )

        POOL = {
            self.Z_LEFT:  [[4, 11], [5, 11], [3, 12], [6, 12], [2, 13]],
            self.Z_RIGHT: [[23, 11], [22, 11], [24, 12], [21, 12], [25, 13]],
            self.Z_MID:   [[11, 10], [16, 10], [13, 11], [14, 11],
                           [11, 11], [16, 11]],
            self.Z_DOWN:  [],
        }
        SIDE_SUPP = {
            self.Z_LEFT:  [4, 12],
            self.Z_RIGHT: [23, 12],
        }

        # Live reactive turret count per zone
        zone_turret_count = {z: 0 for z in [self.Z_LEFT, self.Z_RIGHT,
                                              self.Z_MID,  self.Z_DOWN]}
        for loc in self._reactive_placed:
            if gs.contains_stationary_unit(list(loc)):
                zone_turret_count[self.zone_of(loc[0], loc[1])] += 1

        sorted_bc = sorted(self.breach_counts.items(), key=lambda kv: -kv[1])

        for (x, y), count in sorted_bc:
            zone = self.zone_of(x, y)
            dt   = len(set(self.breach_turns.get((x, y), [])))

            # ── Side triangles ───────────────────────────────────────────────
            if zone in (self.Z_LEFT, self.Z_RIGHT):
                pool   = POOL[zone]
                n_tgts = 1 if count < 3 else (2 if count < 6 else len(pool))
                newly  = self._place_turrets_only(gs, pool[:n_tgts], zone)
                zone_turret_count[zone] += newly

                # Sparse support: max 1 per side, only after dense turrets + heavy breach
                if (live_supp < 2
                        and zone_turret_count[zone] >= 3
                        and count >= 5):
                    supp_loc = SIDE_SUPP[zone]
                    supp_key = tuple(supp_loc)
                    if supp_key not in self._reactive_support_placed:
                        if gs.attempt_spawn(SUPPORT, [supp_loc]):
                            self._reactive_support_placed.add(supp_key)
                            live_supp += 1

            # ── Mid rectangle — turrets only ─────────────────────────────────
            elif zone == self.Z_MID and dt >= 2:
                self._place_turrets_only(gs, POOL[self.Z_MID], zone)

            # ── Down triangle — far-corner turrets only ──────────────────────
            elif zone == self.Z_DOWN and dt >= 2:
                tgts = [[23, 11], [22, 11]] if x <= 13 else [[4, 11], [5, 11]]
                self._place_turrets_only(gs, tgts, zone)

        self._corner_pressure_upgrade(gs)

    def _place_turrets_only(self, gs, targets, zone):
        """Spawn turrets at targets without auto-upgrading. Returns count placed."""
        placed = 0
        for loc in targets:
            key = tuple(loc)
            if not gs.contains_stationary_unit(loc):
                if gs.attempt_spawn(TURRET, loc):
                    self._reactive_placed.add(key)
                    placed += 1
        return placed

    def _corner_pressure_upgrade(self, gs):
        """
        Upgrade corner-zone turrets when that zone's cumulative breach ≥ threshold.
        Mid-rect turrets are NEVER upgraded.
        """
        THRESHOLD = 3
        if self.zone_breach[self.Z_LEFT] >= THRESHOLD:
            for loc in self.CORNER_LEFT_TURRETS:
                if gs.contains_stationary_unit(loc):
                    gs.attempt_upgrade([loc])
        if self.zone_breach[self.Z_RIGHT] >= THRESHOLD:
            for loc in self.CORNER_RIGHT_TURRETS:
                if gs.contains_stationary_unit(loc):
                    gs.attempt_upgrade([loc])

    # ---- Interceptor patrol ----

    def _deploy_interceptors(self, gs, t, mp):
        """
        t=0  : interceptors already spawned in _build_defense — skip here.
        t=1  : skip (breach history too thin).
        t≥2  : 1–2 interceptors at worst-breach-zone patrol point.
               Reserve enough MP for offense before spending here.
        """
        if t < 2:
            return
        if max(self.zone_breach.values()) == 0:
            return

        worst_zone = max(self.zone_breach, key=self.zone_breach.get)
        patrol_pt  = self._icept_patrol.get(worst_zone)
        if not patrol_pt:
            return

        n    = 2 if self.zone_breach[worst_zone] >= 3 else 1
        cost = n * 3
        if mp - cost < self._min_attack_mp:
            return

        spawned = gs.attempt_spawn(INTERCEPTOR, patrol_pt, n)
        if spawned:
            gamelib.debug_write('Interceptor x{} @ {} zone={}'.format(
                n, patrol_pt, worst_zone))

    # =========================================================================
    # REGION SCORING — Signal Attenuation Formula (from PDF)
    # =========================================================================

    def _build_enemy_unit_cache(self, gs):
        """
        Collect all enemy turrets and supports once per turn.
        Caching avoids redundant map scans across the 5 region evaluations.
        Returns list of (x, y, GameUnit).
        """
        cache = []
        for x in range(28):
            for y in range(14, 28):
                units = gs.game_map[x][y]
                if units:
                    for u in units:
                        if u.unit_type in (TURRET, SUPPORT):
                            cache.append((x, y, u))
        return cache

    def _score_region(self, gs, region_id, enemy_cache):
        """
        Compute S(R) for one attack region using the signal-attenuation model.

        Core formula:
          S(R) = 1_{H_end > 0} · (H_end / H0)^γ · exp(-α·T_R - β·U_R - λ·C_R)

        Health decay along path P:
          H_{i+1} = H_i - D_i
          D_i = Σ_{turrets t}  w_t · u_level · f(d_{it})    f(d) = 1/(1 + d²)
              + Σ_{supports s} w_s · u_level · g(d_{is})    g(d) = 1/(1 + d)

        Penalty accumulators over the full path:
          T_R — total turret pressure  = Σ_i Σ_t  w_t · u_level · f(d_{it})
          U_R — upgrade penalty        = Σ_i Σ_obj (u_level - 1)²   (quadratic)
          C_R — clustering penalty     = Σ_i ρ_i²                   (ρ_i = local turret density)

        Weight rationale:
          Turret distance falloff f(d)=1/(1+d²) decays faster than support
          falloff g(d)=1/(1+d), matching Terminal mechanics: turrets are short-
          range burst damage, supports amplify over a wider area.

          CENTER region: softer α/β/λ/γ because the attack must travel all the
          way to the enemy health edge via the top triangles.  Moderate damage
          accumulation on a long path should not zero out the score.

        Returns (score: float, best_spawn: list|None).
        """
        r = self.REGIONS[region_id]

        valid = [s for s in r['spawns'] if gs.can_spawn(SCOUT, s)]
        if not valid:
            return 0.0, None

        spawn = self.least_damage_spawn_location(gs, valid)
        path  = gs.find_path_to_edge(spawn)
        if not path:
            return 0.0, spawn

        H0  = 100.0
        H   = H0
        T_R = 0.0
        U_R = 0.0
        C_R = 0.0
        w_t = r['w_t']
        w_s = r['w_s']

        for (px, py) in path:
            local_dens = 0
            tile_dmg   = 0.0

            for (ex, ey, u) in enemy_cache:
                d    = math.sqrt((ex - px) ** 2 + (ey - py) ** 2)
                ulvl = 2 if u.upgraded else 1

                if u.unit_type == TURRET:
                    fd        = 1.0 / (1.0 + d * d)
                    contrib   = w_t * ulvl * fd
                    tile_dmg += contrib
                    T_R      += contrib
                    U_R      += (ulvl - 1) ** 2
                    local_dens += 1

                elif u.unit_type == SUPPORT:
                    gd        = 1.0 / (1.0 + d)
                    contrib   = w_s * ulvl * gd
                    tile_dmg += contrib
                    U_R      += (ulvl - 1) ** 2

            C_R += local_dens ** 2
            H   -= tile_dmg
            if H <= 0.0:
                return 0.0, spawn

        score = (
            ((H / H0) ** r['gamma'])
            * math.exp(-r['alpha'] * T_R - r['beta'] * U_R - r['lam'] * C_R)
        )
        return max(0.0, score), spawn

    def _rank_regions(self, gs):
        """
        Score all 5 ranked regions each turn and return a sorted ordering.

        Blended score = 0.75 * raw_formula_score + 0.25 * historical_region_eff_avg.
        Blending smooths out single-turn noise (e.g. enemy rebuilt a turret last
        turn) without ignoring recent ground truth from past attacks.

        Returns:
          ranked  — list of region IDs sorted best → worst
          scores  — {region_id: blended_score}
          spawns  — {region_id: chosen spawn point or None}
        """
        enemy_cache = self._build_enemy_unit_cache(gs)
        scores = {}
        spawns = {}

        for rid in self.REGION_IDS:
            raw, sp = self._score_region(gs, rid, enemy_cache)

            hist     = self._region_eff_history.get(rid, [])
            hist_avg = sum(hist) / len(hist) if hist else 0.5
            blended  = 0.75 * raw + 0.25 * hist_avg

            scores[rid] = blended
            spawns[rid] = sp

        ranked = sorted(scores, key=lambda r: -scores[r])
        gamelib.debug_write('RegionRank: {}'.format(
            ' | '.join('{}={:.3f}'.format(r, scores[r]) for r in ranked)))
        return ranked, scores, spawns

    # =========================================================================
    # OFFENSE
    # =========================================================================

    def _run_offense(self, gs, t, hp, mp):
        """
        Turn 0:
          Lightweight scout probe — pick the least-damage exit from three
          representative spawn points (left corner, centre, right corner).

        Turn 1+:
          1. Score all 5 regions using _rank_regions.
          2. Pick the top-ranked region.
          3. Budget is capped by _adapt_budget; desperate HP dumps all MP.
          4. Graduated probing:
               no history → budget capped at 2 (first-time decoy probe)
               1 test     → budget capped at 4 (second probe: small burst)
               2+ tests   → full budget applies
          5. Late game (t≥15) + best score < 0.10 → demolisher clear first.
        """
        if t == 0:
            self._attack_round0(gs, mp)
            return

        if mp < self._min_attack_mp:
            return

        ranked, scores, best_spawns = self._rank_regions(gs)
        best_region = ranked[0]
        best_score  = scores[best_region]
        spawn       = best_spawns[best_region]

        if spawn is None:
            return

        is_late   = (t >= 15)
        desperate = (hp <= 15)

        budget = min(int(mp), self._max_attack_mp)
        if desperate:
            budget = int(mp)

        # Graduated probing for untested / barely-tested regions
        if not desperate:
            hist = self._region_eff_history.get(best_region, [])
            if len(hist) == 0:
                budget = min(budget, 2)   # first probe: tiny decoy
            elif len(hist) == 1:
                budget = min(budget, 4)   # second probe: small burst

        # Demolisher clear: late game + route is nearly impenetrable
        if is_late and best_score < 0.10 and budget >= 4 and not desperate:
            side = 'left' if spawn[0] <= 13 else 'right'
            self._demolisher_clear_then_attack(gs, side, spawn, budget)
            return

        if budget > 0:
            self._scout_attack(gs, best_region, spawn, budget)

    def _attack_round0(self, gs, mp):
        """Turn 0: probe the least-damage exit among three representative spawns."""
        candidates = {
            'L_TRI':  [1, 12],
            'CENTER': [13, 0],
            'R_TRI':  [26, 12],
        }
        best_rid, best_sp, best_dmg = 'CENTER', [13, 0], 999999
        for rid, sp in candidates.items():
            if gs.can_spawn(SCOUT, sp):
                d = self._path_dmg(gs, sp)
                if d < best_dmg:
                    best_dmg, best_rid, best_sp = d, rid, sp

        budget = min(int(mp), self._max_attack_mp)
        self._scout_attack(gs, best_rid, best_sp, budget)

    def _demolisher_clear_then_attack(self, gs, side, scout_spawn, budget):
        """
        Demolisher(s) from our near-corner arc into the blocked region to crack
        fortified defenses, then scouts follow through the opened corridor.
        """
        demo_spawn = [3, 10] if side == 'left' else [24, 10]
        n_demo     = max(1, budget // 4)
        n_scouts   = max(0, budget - n_demo * 4)

        gamelib.debug_write('DemoClr: {}x demo @ {} then {}x scouts @ {}'.format(
            n_demo, demo_spawn, n_scouts, scout_spawn))

        d_sp = gs.attempt_spawn(DEMOLISHER, demo_spawn, n_demo)
        s_sp = gs.attempt_spawn(SCOUT, scout_spawn, n_scouts) if n_scouts > 0 else 0

        rid  = 'L_TRI' if side == 'left' else 'R_TRI'
        self.attack_region_this_turn = rid
        self.attack_units_this_turn  = d_sp + s_sp
        self._last_spawn_coord       = demo_spawn

    def _scout_attack(self, gs, region_id, spawn, budget):
        """Spawn scouts at spawn and record the attack under region_id."""
        count = gs.attempt_spawn(SCOUT, spawn, budget)
        self.attack_region_this_turn = region_id
        self.attack_units_this_turn  = count
        self._last_spawn_coord       = spawn
        gamelib.debug_write('Scouts x{} → region={} spawn={}'.format(
            count, region_id, spawn))

    # =========================================================================
    # UTILITIES
    # =========================================================================

    def _path_dmg(self, gs, location):
        """Estimate total incoming turret damage along the pathfound route."""
        path = gs.find_path_to_edge(location)
        if not path:
            return 999999
        unit = gamelib.GameUnit(TURRET, gs.config)
        return sum(len(gs.get_attackers(p, 0)) * unit.damage_i for p in path)

    def least_damage_spawn_location(self, gs, opts):
        """Return the spawn from opts with the lowest path-damage estimate."""
        best, best_d = opts[0], 999999
        for loc in opts:
            d = self._path_dmg(gs, loc)
            if d < best_d:
                best_d, best = d, loc
        return best

    def filter_blocked_locations(self, locs, gs):
        return [l for l in locs if not gs.contains_stationary_unit(l)]

    def _avg_eff(self):
        if not self._recent_effs:
            return 1.0
        return sum(self._recent_effs) / len(self._recent_effs)

    # =========================================================================
    # ACTION FRAME — breach + HP tracking
    # =========================================================================

    def on_action_frame(self, turn_string):
        state  = json.loads(turn_string)
        events = state.get("events", {})

        for breach in events.get("breach", []):
            loc  = breach[0]
            ours = (breach[4] == 1)   # 1 = our unit scored on enemy edge

            if ours:
                self.enemy_hp_after = max(0, self.enemy_hp_after - 1)
            else:
                key  = tuple(loc)
                self.breach_counts[key] = self.breach_counts.get(key, 0) + 1
                self.breach_turns.setdefault(key, []).append(self.current_turn)
                zone = self.zone_of(loc[0], loc[1])
                self.zone_breach[zone] = self.zone_breach.get(zone, 0) + 1
                gamelib.debug_write('Breach@{} zone={} total={}'.format(
                    key, zone, self.breach_counts[key]))


if __name__ == "__main__":
    algo = AlgoStrategy()
    algo.start()