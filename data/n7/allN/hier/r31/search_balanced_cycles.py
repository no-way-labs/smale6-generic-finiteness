#!/usr/bin/env python3
"""Try to realize balanced Lemma C cycles using exact integer heights."""

from collections import Counter, defaultdict
from itertools import permutations
from math import factorial
from random import Random


def alternating_pairs(rings):
    even, odd = [], []
    position = 0
    for ring in rings:
        for i, a in enumerate(ring):
            edge = tuple(sorted((a, ring[(i + 1) % len(ring)])))
            (even if position % 2 == 0 else odd).append(edge)
            position += 1
    assert len(even) == len(odd)
    assert len(set(even + odd)) == len(even + odd)
    assert Counter(a for edge in even for a in edge) == Counter(
        a for edge in odd for a in edge
    )
    return even, odd


def forced_heights(edges, weights):
    # The first edge runs from the first z-node to the first w-node.
    # Set both the first z-height and the proposed maximal Psi to zero.
    z, w = [0], []
    for i in range(0, len(edges), 2):
        a, b = edges[i]
        c, d = edges[i + 1]
        w.append(2 * (weights[a] + weights[b]) - z[-1])
        z.append(2 * (weights[c] + weights[d]) - w[-1])
    assert z.pop() == 0
    return z, w


def least_ultrametric(n, edges, heights, adjacent_step, floor):
    levels = defaultdict(list)
    for i, height in enumerate(heights):
        adjacent_index = (2 * i + adjacent_step) % len(edges)
        levels[height].append((i, edges[2 * i], edges[adjacent_index]))

    owner = list(range(n))
    members = [[i] for i in range(n)]
    distance = [[floor] * n for _ in range(n)]
    nodes = [None] * len(heights)

    for height in sorted(levels, reverse=True):
        # Each cycle edge must have exactly this height. If its endpoints
        # were already linked at a greater height, no ultrametric works.
        for _, (a, b), (c, d) in levels[height]:
            if owner[a] == owner[b] or owner[c] == owner[d]:
                return "forced greater height", None, None

        # Each node must contain all four endpoints, even for disjoint edges.
        for _, (a, b), (c, d) in levels[height]:
            target = owner[a]
            for x in (b, c, d):
                source = owner[x]
                if source == target:
                    continue
                for p in members[source]:
                    for q in members[target]:
                        distance[p][q] = distance[q][p] = height
                    owner[p] = target
                members[target].extend(members[source])
                members[source].clear()

        for i, (a, _), _ in levels[height]:
            nodes[i] = frozenset(members[owner[a]])

    if len(set(nodes)) < len(nodes):
        return "repeated node", None, None
    return None, distance, nodes


def attempt(edges, weights, hierarchical):
    z, w = forced_heights(edges, weights)
    floor = min(z + w) - abs(max(z + w)) + min(0, 4 * min(weights)) - 1
    n = len(weights)
    failure, dz, zn = least_ultrametric(n, edges, z, -1, floor)
    if failure:
        return failure, None
    failure, dw, wn = least_ultrametric(n, edges, w, 1, floor)
    if failure:
        return failure, None

    if hierarchical:
        pairs_at_l = []
        lightest = max(a for edge in edges for a in edge)
        for k, (a, b) in enumerate(edges):
            i, j = ((k + 1) // 2) % len(z), k // 2
            other_bodies = (zn[i] & wn[j]) - {a, b}
            if any(weights[x] < weights[b] for x in other_bodies):
                return "heavier body in an edge intersection", None
            if b == lightest:
                pairs_at_l.append((i, j, a))

        pairs_at_l.sort(key=lambda pair: z[pair[0]])
        corners = []
        for (i, j, a), (k, l, b) in zip(pairs_at_l, pairs_at_l[1:]):
            assert zn[i] > zn[k] and wn[j] < wn[l]
            lower_bound = z[i] + w[l] - 2 * (weights[a] + weights[b])
            if lower_bound > 0:
                corners.append((i, l, a, b, lower_bound))
        if corners:
            return "corner overtakes cycle", (edges, z, w, corners)

    for a in range(n):
        for b in range(a):
            if dz[a][b] + dw[a][b] > 2 * (weights[a] + weights[b]):
                return "another pair overtakes cycle", None
    return "witness", (edges, z, w, dz, dw)


def placements(even, odd):
    for tail in permutations(even[1:]):
        for right in permutations(odd):
            yield tuple(e for pair in zip((even[0],) + tail, right) for e in pair)


def sampled_placements(even, odd, rng, limit):
    orders = set()
    while len(orders) < limit:
        left = (even[0], *rng.sample(even[1:], len(even) - 1))
        right = rng.sample(odd, len(odd))
        order = tuple(e for pair in zip(left, right) for e in pair)
        if order not in orders:
            orders.add(order)
            yield order


def weight_vector(n):
    return (0, *(pow(n * n + 2, i) for i in range(n - 1)))


def search(label, n, patterns, limit=None):
    weights = weight_vector(n)
    rng = Random(3108)
    counts = Counter()
    first_corner = None
    trials = 0
    for rings in patterns:
        even, odd = alternating_pairs(rings)
        if limit is None:
            orders = placements(even, odd)
            trials += factorial(len(even) - 1) * factorial(len(odd))
        else:
            orders = sampled_placements(even, odd, rng, limit)
            trials += limit
        for edges in orders:
            status, detail = attempt(edges, weights, hierarchical=True)
            counts[status] += 1
            if status == "corner overtakes cycle" and first_corner is None:
                first_corner = detail
            if status == "witness":
                raise AssertionError((weights, detail))

    assert sum(counts.values()) == trials
    print(f"{label}, n={n}, {trials} placements")
    for status, count in sorted(counts.items()):
        print(f"  {status}: {count}")
    if first_corner:
        print(f"  first corner (edges, z, w, (i, j, a, b, 2 Delta Psi))): {first_corner}")


def main():
    # The four active bodies carry a genuine maximum cycle with repeated
    # masses, and the four other bodies can be placed below the used heights.
    even, odd = alternating_pairs(((0, 1, 2, 3),))
    edges = (even[0], odd[0], even[1], odd[1])
    status, detail = attempt(edges, (0, 0, 1, 1, 2, 3, 4, 5), hierarchical=False)
    assert status == "witness", (status, detail)
    print(f"outside-chamber control, n=8: {status}, cycle {edges}")

    octagons = (
        ((0, *tail),) for tail in permutations(range(1, 8)) if tail[0] < tail[-1]
    )
    search("all labelled octagons modulo rotation and reversal", 8, octagons)
    search("square and hexagon sharing two bodies", 8, [((7, 0, 1, 2), (7, 3, 4, 0, 5, 6))])
    search("two pentagons sharing two bodies", 8, [((7, 0, 1, 2, 3), (7, 4, 5, 0, 6))])
    search("square and hexagon sharing the lightest body", 9, [((8, 0, 1, 2), (8, 3, 4, 5, 6, 7))])
    search("triangle and heptagon sharing the lightest body", 9, [((8, 5, 7), (8, 4, 0, 2, 1, 3, 6))])
    three_squares = [((9, 0, 1, 2), (9, 3, 4, 5), (9, 6, 7, 8))]
    search("three squares sharing the lightest body", 10, three_squares)
    search("same three squares with a lighter body off the cycle", 11, three_squares)
    search("twelve bodies on a ring", 12, [(tuple(range(12)),)])
    search(
        "four squares sharing the lightest body, seeded sample",
        13,
        [((12, 0, 1, 2), (12, 3, 4, 5), (12, 6, 7, 8), (12, 9, 10, 11))],
        limit=20_000,
    )


if __name__ == "__main__":
    main()
