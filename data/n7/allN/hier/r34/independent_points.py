"""Check the six recorded point files from the equations and rounded heights alone."""
from collections import Counter, defaultdict
from copy import deepcopy
from decimal import Decimal
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import gzip
import json
import math
import sys

SCALE = 100_000
TOLERANCE = SCALE // 1_000


def scaled(value):
    exact = Decimal(value) * SCALE
    assert exact.is_finite() and exact == exact.to_integral_value(), value
    return int(exact)


def all_cycles(adjacency):
    """Return simple cycles of the finite bipartite multigraph, once per edge set."""
    found = {}

    def extend(start, current, vertices, edges):
        for neighbor, edge in adjacency[current]:
            if edge in edges:
                continue
            if neighbor == start:
                cycle = edges + (edge,)
                found.setdefault(frozenset(cycle), cycle)
            elif neighbor > start and neighbor not in vertices:
                extend(start, neighbor, vertices | {neighbor}, edges + (edge,))

    for vertex in adjacency:
        extend(vertex, vertex, {vertex}, ())
    return found.values()


def data_for(n, point, key, origins):
    values = {}
    for a, b in combinations(range(n), 2):
        values[a, b] = values[b, a] = scaled(point[key][f"{a}{b}"])
    for body in range(n):
        values[body, n] = values[n, body] = scaled(point[origins][body])
    return values


def verify(n, masses, point):
    zeta = data_for(n, point, "zeta", "xi")
    omega = data_for(n, point, "omega", "eta")
    bodies = frozenset(range(n))
    body_pairs = list(combinations(range(n), 2))
    edges = list(combinations(range(n + 1), 2))

    worst_triangle_gap = 0
    for distances in (zeta, omega):
        for a, b, c in combinations(range(n + 1), 3):
            low, second, _ = sorted((distances[a, b], distances[b, c], distances[c, a]))
            worst_triangle_gap = max(worst_triangle_gap, second - low)

    psi2 = {
        (a, b): zeta[a, b] + omega[a, b] - 2 * (masses[a] + masses[b])
        for a, b in body_pairs
    }
    for a in bodies:
        psi2[a, n] = -2 * (zeta[a, n] + omega[a, n] + masses[a])

    worst_cut_gap2 = 0
    for mask in range(1, 1 << n):
        inside = {a for a in bodies if mask & (1 << a)}
        for current, other in ((zeta, omega), (omega, zeta)):
            terms = [-2 * (masses[a] + current[a, n]) for a in inside]
            for a, b in body_pairs:
                if (a in inside) != (b in inside):
                    terms.append(psi2[a, b] + 2 * other[a, b])
            terms.sort()
            worst_cut_gap2 = max(worst_cut_gap2, terms[-1] - terms[-2])

    top2 = max(psi2.values())
    graph = defaultdict(list)
    inconsistent_threshold_nodes = 0
    for a, b in edges:
        if top2 - psi2[a, b] >= 2 * TOLERANCE:
            continue
        vertices = []
        for color, distance in enumerate((zeta, omega)):
            threshold = distance[a, b] - TOLERANCE
            from_a = {k for k in range(n + 1) if k == a or distance[a, k] >= threshold}
            from_b = {k for k in range(n + 1) if k == b or distance[b, k] >= threshold}
            inconsistent_threshold_nodes += from_a != from_b
            vertices.append((color, sum(1 << k for k in from_a)))
        left, right = vertices
        graph[left].append((right, (a, b)))
        graph[right].append((left, (a, b)))

    cycle_coefficients = []
    for cycle in all_cycles(graph):
        assert len(cycle) % 2 == 0
        sigma = 0
        q = [0] * n
        for index, (a, b) in enumerate(cycle):
            sign = -1 if index % 2 == 0 else 1
            if b == n:
                q[a] -= sign
            else:
                sigma += sign
                q[a] += 2 * sign
                q[b] += 2 * sign
        N = 3 * sigma
        if N > 0:
            N = -N
            q = [-coefficient for coefficient in q]
        residual2 = N * top2 + 2 * sum(qj * uj for qj, uj in zip(q, masses))
        cycle_coefficients.append((N, tuple(q), abs(residual2)))

    return {
        "triangle_gap": worst_triangle_gap,
        "cut_gap2": worst_cut_gap2,
        "top2": top2,
        "node_disagreements": inconsistent_threshold_nodes,
        "degrees": tuple(len(edges) for edges in graph.values()),
        "cycles": cycle_coefficients,
    }


def control():
    explicit = {"zeta": {"01": 0}, "omega": {"01": 0}, "xi": [2, 0], "eta": [2, 0]}
    result = verify(2, (0, 2 * SCALE), explicit)
    assert result == {
        "triangle_gap": 0, "cut_gap2": 0, "top2": -4 * SCALE, "node_disagreements": 0,
        "degrees": (2, 2), "cycles": [(-3, (-2, -3), 0)],
    }, result
    changed = deepcopy(explicit)
    changed["xi"][0] = -1
    detected = verify(2, (0, 2 * SCALE), changed)
    assert detected["triangle_gap"] > TOLERANCE and detected["cut_gap2"] > 2 * TOLERANCE, detected
    print("Control: exact two-body witness recovered, including its cycle relation. Corrupted height rejected.")


def main(paths):
    control()
    for path in paths:
        with gzip.open(path, "rt") as compressed:
            data = json.load(compressed, parse_float=Decimal)
        n = data["K"]
        weights = tuple(map(scaled, data["u"]))
        bound = Fraction((2 * n - 1) * sum(map(abs, weights)), 3 * SCALE)
        sample = data.get("sample")
        trees = math.prod(range(1, 2 * n, 2))
        triangular_pairs = trees * (trees + 1) // 2
        candidate_pairs = sample or (triangular_pairs if data["sym"] else trees**2)
        statistics = Counter()
        greatest = Decimal("-Infinity")
        worst_gap2 = worst_triangle = worst_residual2 = psi_delta2 = 0
        for point in data["points"]:
            result = verify(n, weights, point)
            top = Decimal(result["top2"]) / (2 * SCALE)
            greatest = max(top, greatest)
            psi_delta2 = max(psi_delta2, abs(result["top2"] - 2 * scaled(point["psi"])))
            statistics["over_bound"] += Fraction(top) > bound
            statistics["below_threshold"] += (data["far"] is not None
                and top < data["far"] - Decimal(TOLERANCE) / SCALE)
            statistics["triangle_fail"] += result["triangle_gap"] > TOLERANCE
            statistics["cut_fail"] += result["cut_gap2"] > 2 * TOLERANCE
            statistics["nonexact_cut"] += result["cut_gap2"] > 0
            statistics["degree_not_two"] += not result["degrees"] or any(d != 2 for d in result["degrees"])
            statistics["node_disagreements"] += result["node_disagreements"]
            statistics["cycles"] += len(result["cycles"])
            statistics["zero_N"] += sum(N == 0 for N, _, _ in result["cycles"])
            worst_gap2 = max(worst_gap2, result["cut_gap2"])
            worst_triangle = max(worst_triangle, result["triangle_gap"])
            worst_residual2 = max(worst_residual2, max((cycle[2] for cycle in result["cycles"]), default=0))
        print(f"{path.name}: n={n}, weights={', '.join(str(x) for x in data['u'])}, "
              f"all_ordered_pairs={trees**2}, candidate_pairs={candidate_pairs}, "
              f"sym={data['sym']}, sample={sample}, seed={data.get('seed')}, threshold={data['far']}")
        print(f"  points={len(data['points'])}, max_psi={greatest}, bound={bound}, "
              f"max_cut_gap={Decimal(worst_gap2)/(2*SCALE)}, "
              f"max_triangle_gap={Decimal(worst_triangle)/SCALE}, "
              f"max_residual={Decimal(worst_residual2)/(2*SCALE)}, "
              f"max_delta_from_stored_psi={Decimal(psi_delta2)/(2*SCALE)}")
        print(f"  {dict(statistics)}")


if __name__ == "__main__":
    main([Path(name) for name in sys.argv[1:]])
