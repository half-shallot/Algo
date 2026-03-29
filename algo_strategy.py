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
        self.MAP_WIDTH = 28
        self.MAP_HEIGHT = 28

        # ---- Base layout (NO (13,8) support) ----
        self.TURN0_TURRETS        = [[12, 12], [15, 12]]
        self.BASE_TURRETS         = [[11, 11], [16, 11], [12, 12], [15, 12]]
        self.BASE_TURRETS_UPGRADE = [[12, 10], [15, 10]]
        # Supports: (13,8) removed → remaining cluster
        self.BASE_SUPPORTS        = [[12, 11], [13, 11], [14, 11], [15, 11]]
        self.BASE_SUPPORTS_UPG    = [[12, 11], [13, 11],[14,11]]

        # ---- Breach / zone tracking ----
        self.breach_counts = {}   # (x,y) -> int
        self.breach_turns  = {}   # (x,y) -> [turn#, ...]
        self.zone_breach   = {self.Z_LEFT: 0, self.Z_RIGHT: 0,
                               self.Z_MID: 0,  self.Z_DOWN: 0}
        self.region_damage = {self.Z_LEFT: 0, self.Z_RIGHT: 0,
                               self.Z_MID: 0,  self.Z_DOWN: 0}
        self.current_turn  = 0
        self.recent_attack_window = 5

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

        # ---- Region layout + coverage targets ----
        self._init_region_layout()
        self._support_coverage_target = 0.75
        self._strong_defense_support_target = 0.85

    # =========================================================================
    # REGION / ZONE SHAPES
    # =========================================================================

    def _init_region_layout(self):
        """Build explicit region tiles and edges for scoring and placement."""
        self.region_tiles = self._build_region_tiles()
        self.region_edges = self._build_region_edges(self.region_tiles)

    def _build_region_tiles(self):
        """Create explicit tiles for left/right triangles and mid/down regions."""
        tiles = {
            self.Z_LEFT: set(),
            self.Z_RIGHT: set(),
            self.Z_MID: set(),
            self.Z_DOWN: set(),
        }
        for x in range(self.MAP_WIDTH):
            for y in range(14):
                tiles[self._explicit_zone_for_tile(x, y)].add((x, y))
        return tiles

    def _explicit_zone_for_tile(self, x, y):
        if x in self.MID_X and y in self.MID_Y:
            return self.Z_MID
        if x in self.MID_X and y in self.DN_Y:
            return self.Z_DOWN

        left_diag = x <= 8 and y >= x
        right_diag = x >= 19 and y >= (27 - x)

        if left_diag:
            return self.Z_LEFT
        if right_diag:
            return self.Z_RIGHT

        return self.Z_LEFT if x < 9 else self.Z_RIGHT

    def _build_region_edges(self, region_tiles):
        """Mark boundary tiles in each region to identify exposed edges."""
        edges = {zone: set() for zone in region_tiles}
        for zone, tiles in region_tiles.items():
            for (x, y) in tiles:
                for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                    nx, ny = x + dx, y + dy
                    if (nx, ny) not in tiles:
                        edges[zone].add((x, y))
                        break
        return edges

    # =========================================================================
    # ZONE CLASSIFIER
    # =========================================================================

    def zone_of(self, x, y):
        """Classify a tile on OUR side into one of the 4 defense zones."""
        for zone, tiles in self.region_tiles.items():
            if (x, y) in tiles:
                return zone
        return self.Z_LEFT if x < 9 else self.Z_RIGHT

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

        # Live map split (my vs enemy) for scoring/placement
        self._turn_unit_maps = self._collect_unit_maps(gs)

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
    # MAP INTEL — LIVE UNIT SPLIT
    # =========================================================================

    def _collect_unit_maps(self, gs):
        """Split gs.game_map[x, y] → my units vs enemy units in real time."""
        my_units = {}
        enemy_units = {}
        for x in range(self.MAP_WIDTH):
            for y in range(self.MAP_HEIGHT):
                units = gs.game_map[x, y]
                if not units:
                    continue
                for unit in units:
                    target = my_units if unit.player_index == 0 else enemy_units
                    target.setdefault((x, y), []).append(unit)
        return {'my': my_units, 'enemy': enemy_units}

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
        Turn 0 : Deploy (12,10) and (15,10) turrets FIRST.
        Every  : Recover base layout (turrets → supports → upgrade supports).
        Turn 2+: Zone-reactive turrets based on breach log (no turret upgrades).
        Always : Interceptors to patrol the hottest breach zone.
        Always : If enemy changing tactics → upgraded support in mid-rect.
        """
        if t == 0:
            gs.attempt_spawn(TURRET,   self.TURN0_TURRETS)


        # Structural defense updates with live scoring
        if self._turn_unit_maps:
            self._apply_structural_defense(gs, self._turn_unit_maps)

        if t >= 2:
            self._reactive_zone_defense(gs)

        self._deploy_interceptors(gs, t, mp)

        # Recover base every turn
        gs.attempt_spawn(TURRET,   self.BASE_TURRETS)
        gs.attempt_spawn(SUPPORT,  self.BASE_SUPPORTS)
        gs.attempt_upgrade(        self.BASE_SUPPORTS_UPG)

        if self.enemy_intel['tactic_changes'] >= 2:
            self._deploy_adaptive_support(gs)

    # ---- Structural defense scoring and placement ----

    def _apply_structural_defense(self, gs, unit_maps):
        """Rank regions by defense score and reinforce weakest spots."""
        region_scores = self._rank_regions_by_defense(gs, unit_maps)
        if not region_scores:
            return

        weakest = region_scores[0]
        strongest = region_scores[-1]

        self._deploy_support_to_region(gs, unit_maps, weakest)
        self._deploy_turrets_to_region(gs, unit_maps, weakest)
        self._upgrade_supports_if_strong(gs, unit_maps, strongest)

    def _rank_regions_by_defense(self, gs, unit_maps):
        """Return ordered list of region score dicts (weakest → strongest)."""
        scores = [
            self._defensive_score_left(gs, unit_maps),
            self._defensive_score_right(gs, unit_maps),
            self._defensive_score_mid(gs, unit_maps),
            self._defensive_score_down(gs, unit_maps),
        ]
        return sorted(scores, key=lambda entry: entry['score'])

    def _defensive_score_left(self, gs, unit_maps):
        base = self._defensive_score_base(self.Z_LEFT, gs, unit_maps)
        base['score'] *= 0.7
        base['region'] = self.Z_LEFT
        return base

    def _defensive_score_right(self, gs, unit_maps):
        base = self._defensive_score_base(self.Z_RIGHT, gs, unit_maps)
        base['score'] *= 0.7
        base['region'] = self.Z_RIGHT
        return base

    def _defensive_score_mid(self, gs, unit_maps):
        base = self._defensive_score_base(self.Z_MID, gs, unit_maps)
        base['region'] = self.Z_MID
        return base

    def _defensive_score_down(self, gs, unit_maps):
        base = self._defensive_score_base(self.Z_DOWN, gs, unit_maps)
        mid_edge_support = self._mid_edge_support_score(unit_maps)
        base['score'] += 2.5 * mid_edge_support
        base['region'] = self.Z_DOWN
        return base

    def _defensive_score_base(self, region, gs, unit_maps):
        """Compute defense score with turrets, supports, walls, breaches, and exposure."""
        counts = self._count_structures(region, unit_maps)
        edge_turrets = self._edge_neighbor_turrets(region, unit_maps)
        support_positions = self._support_positions(unit_maps)
        support_coverage = self._support_coverage_ratio(region, support_positions)
        recent_breaches = self._recent_breach_count(region)
        health_damage = self.region_damage.get(region, 0)
        edge_exposure = self._edge_exposure(region, gs, unit_maps)

        turret_value = math.sqrt(max(1, counts['turret'])) * 3.0
        support_value = (counts['support'] + 0.5 * edge_turrets) * 2.0
        wall_value = counts['wall'] * 0.4
        coverage_value = (support_coverage ** 2) * 6.0

        penalty = (recent_breaches * 2.0) + (health_damage * 2.5) + (edge_exposure * 1.2)
        score = turret_value + support_value + wall_value + coverage_value - penalty

        return {
            'region': region,
            'score': score,
            'counts': counts,
            'edge_turrets': edge_turrets,
            'support_coverage': support_coverage,
            'recent_breaches': recent_breaches,
            'health_damage': health_damage,
            'edge_exposure': edge_exposure,
        }

    def _count_structures(self, region, unit_maps):
        counts = {'turret': 0, 'support': 0, 'wall': 0}
        for coord, units in unit_maps['my'].items():
            if coord not in self.region_tiles[region]:
                continue
            for unit in units:
                if unit.unit_type == TURRET:
                    counts['turret'] += 1
                elif unit.unit_type == SUPPORT:
                    counts['support'] += 1
                elif unit.unit_type == WALL:
                    counts['wall'] += 1
        return counts

    def _edge_neighbor_turrets(self, region, unit_maps):
        """Count turrets sitting on neighbor edges that help this region."""
        turrets = set()
        for (x, y) in self.region_edges[region]:
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                loc = (x + dx, y + dy)
                for unit in unit_maps['my'].get(loc, []):
                    if unit.unit_type == TURRET:
                        turrets.add(loc)
        return len(turrets)

    def _support_positions(self, unit_maps):
        supports = []
        for coord, units in unit_maps['my'].items():
            for unit in units:
                if unit.unit_type == SUPPORT:
                    supports.append(coord)
        return supports

    def _support_coverage_ratio(self, region, support_positions):
        """Approximate coverage of region tiles by supports (radius 3)."""
        tiles = self.region_tiles[region]
        if not tiles:
            return 0.0
        covered = 0
        for tile in tiles:
            if any(self._manhattan(tile, sp) <= 3 for sp in support_positions):
                covered += 1
        return covered / max(1, len(tiles))

    def _recent_breach_count(self, region):
        cutoff = self.current_turn - self.recent_attack_window
        count = 0
        for coord, turns in self.breach_turns.items():
            if coord in self.region_tiles[region]:
                count += sum(1 for turn in turns if turn >= cutoff)
        return count

    def _edge_exposure(self, region, gs, unit_maps):
        """Count edge tiles without turret coverage to estimate exposure."""
        exposed = 0
        for tile in self.region_edges[region]:
            if self._turret_coverage(tile, gs) == 0:
                exposed += 1
        return exposed

    def _turret_coverage(self, tile, gs):
        return sum(1 for unit in gs.get_attackers(tile, 0) if unit.unit_type == TURRET)

    def _mid_edge_support_score(self, unit_maps):
        boundary_tiles = [tile for tile in self.region_tiles[self.Z_MID] if tile[1] == 8]
        if not boundary_tiles:
            return 0.0
        supports = self._support_positions(unit_maps)
        covered = sum(1 for tile in boundary_tiles if any(self._manhattan(tile, sp) <= 3 for sp in supports))
        return covered / len(boundary_tiles)

    def _critical_points(self, region, gs, unit_maps):
        """Find critical tiles based on breaches and weak coverage."""
        cutoff = self.current_turn - self.recent_attack_window
        breached = []
        for coord, turns in self.breach_turns.items():
            if coord in self.region_tiles[region] and any(turn >= cutoff for turn in turns):
                breached.append((len(turns), coord))
        breached.sort(reverse=True)
        points = [coord for _, coord in breached[:3]]

        if not points:
            edge_tiles = list(self.region_edges[region])
            edge_tiles.sort(key=lambda t: self._turret_coverage(t, gs))
            points = edge_tiles[:3]

        if not points:
            points = list(self.region_tiles[region])[:3]

        return points

    def _deploy_support_to_region(self, gs, unit_maps, region_score):
        """Deploy support to weakest region if coverage is low."""
        region = region_score['region']
        support_positions = self._support_positions(unit_maps)
        coverage = self._support_coverage_ratio(region, support_positions)
        if coverage >= self._support_coverage_target:
            return

        candidates = self._support_candidate_locations(gs, unit_maps, region)
        for loc in candidates:
            if gs.attempt_spawn(SUPPORT, loc):
                if region_score['score'] >= 0:
                    gs.attempt_upgrade([loc])
                break

    def _upgrade_supports_if_strong(self, gs, unit_maps, region_score):
        """Upgrade supports in strong regions that still lack coverage."""
        region = region_score['region']
        support_positions = self._support_positions(unit_maps)
        coverage = self._support_coverage_ratio(region, support_positions)
        if coverage >= self._strong_defense_support_target:
            return

        candidates = self._support_candidate_locations(gs, unit_maps, region)
        for loc in candidates:
            if gs.attempt_spawn(SUPPORT, loc):
                gs.attempt_upgrade([loc])
                break

    def _support_candidate_locations(self, gs, unit_maps, region):
        """Suggest support tiles in/near region (adjacent allowed if it improves coverage)."""
        candidates = []
        for point in self._critical_points(region, gs, unit_maps):
            for dx, dy in ((0, 0), (1, 0), (-1, 0), (0, 1), (0, 2), (2, 0), (-2, 0)):
                loc = (point[0] + dx, point[1] + dy)
                if not gs.game_map.in_arena_bounds(loc):
                    continue
                if gs.contains_stationary_unit(loc):
                    continue
                candidates.append(loc)

        # Allow adjacent regions by widening to nearby tiles if needed
        if not candidates:
            for (x, y) in self.region_edges[region]:
                for dx, dy in ((0, 1), (1, 0), (-1, 0)):
                    loc = (x + dx, y + dy)
                    if not gs.game_map.in_arena_bounds(loc):
                        continue
                    if gs.contains_stationary_unit(loc):
                        continue
                    candidates.append(loc)

        # Preserve order, remove duplicates
        seen = set()
        unique = []
        for loc in candidates:
            if loc in seen:
                continue
            seen.add(loc)
            unique.append(loc)
        return unique

    def _deploy_turrets_to_region(self, gs, unit_maps, region_score):
        """Deploy additional turrets at critical points (no turret upgrades)."""
        region = region_score['region']
        critical = self._critical_points(region, gs, unit_maps)
        for loc in critical:
            if gs.attempt_spawn(TURRET, loc):
                break

    def _manhattan(self, a, b):
        return abs(a[0] - b[0]) + abs(a[1] - b[1])

    # ---- Reactive zone-based turret placement ----

    def _reactive_zone_defense(self, gs):
        """
        For each breached tile (sorted by severity), place turrets according to zone rules.
        Zone rules mirror the 4-part division:
          LEFT_TRI : corner pocket [4,11],[5,11] (2 turrets if count≥3 else 1)
          RIGHT_TRI: mirror corner [23,11],[22,11]
          MID_RECT : reinforce mid flanks  [11,10],[16,10],[13,11],[14,11]
          DOWN_TRI : junction breaches → 2 turrets at FAR corner (opposite x)
        All reactive turrets are deployed without upgrades.
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
            if gs.attempt_spawn(TURRET, t):
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
        """Deploy demolisher(s) from the spawn point nearest to the blocked corner
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
        """Priority order:
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
                self.region_damage[zone] = self.region_damage.get(zone, 0) + 1
                self.enemy_intel['last_breach_zone'] = zone

                gamelib.debug_write('Breach@{} zone={} count={}'.format(
                    key, zone, self.breach_counts[key]))


if __name__ == "__main__":
    algo = AlgoStrategy()
    algo.start()
