"""Exact finite checks for the revised ultrametric proof and nearby examples."""

from fractions import Fraction
from itertools import combinations, product


def check_nodes():
    vertices = range(4)
    origin = 3
    pairs = tuple(combinations(vertices, 2))
    infinity = 2  # Largest rank. Only order comparisons are used.
    orders = (-1, 0, 1, infinity)
    triangles = tuple(combinations(vertices, 3))
    triples = tuple(product(vertices, repeat=3))
    valid = nodes = crossings = 0
    for heights in product(orders, repeat=len(pairs)):
        d = [[infinity] * len(vertices) for _ in vertices]
        for (a, b), height in zip(pairs, heights):
            d[a][b] = d[b][a] = height
        triangle_heights = (sorted((d[a][b], d[b][c], d[a][c])) for a, b, c in triangles)
        if any(low < middle for low, middle, _ in triangle_heights):
            continue
        valid += 1
        assert all(d[a][c] >= min(d[a][b], d[b][c]) for a, b, c in triples)

        def ball(center, threshold):
            return {p for p in vertices if d[center][p] >= threshold}

        for x, y in pairs:
            h = d[x][y]
            if h == infinity:
                continue
            nodes += 1
            node = ball(x, h)
            assert {x, y} <= node and ball(y, h) == node
            assert all(d[p][q] >= h for p, q in product(node, repeat=2))
            for p, q in pairs:
                if d[p][q] < infinity and ball(p, d[p][q]) == node:
                    assert d[p][q] == h
            children = {p: {q for q in node if d[p][q] > h} for p in node}
            assert y not in children[x]
            for p, child in children.items():
                assert p in child
                assert all(children[q] == child for q in child)
                for q in set(vertices) - child:
                    if q in node:
                        assert d[p][q] == h and ball(p, d[p][q]) == node
                    else:
                        assert d[p][q] < h
                    # In Step 1 a cut from a child omitting O can have no
                    # infinite height in this colour, even on an O-edge.
                    if origin not in child and q == origin:
                        crossings += 1
                        assert d[p][q] <= h < infinity
    print(f'Four vertices: {valid} ultrametrics, {nodes} finite generating pairs, '
          f'{crossings} crossings to the origin checked')


def check_negative_tau():
    u = (0, 2, Fraction(3, 2), 1)
    q = (-1, -1, 0, 2)
    tau = Fraction(-1, 2)
    assert u[1] > u[0]
    assert all(u[j] - u[j - 1] > tau * (u[j - 1] - u[0]) for j in (2, 3))
    assert sum(q) == 0
    assert tau == Fraction(abs(q[1]) + abs(q[2]), abs(q[3])) - 1
    assert sum(weight * value for weight, value in zip(u, q)) == 0
    print('Remark 4.2: both gaps satisfy (1.5), and the Lemma 4.1 threshold is -1/2')


def check_roberts_slice():
    masses = (4, 4, 4, 4, 1)
    varying_products = set()
    for t in (Fraction(1, 2), Fraction(1, 3), Fraction(3, 4)):
        a = (1 - t**2) / (1 + t**2)
        b = 2 * t / (1 + t**2)
        points = ((2 * a, 0), (0, 2 * b), (-2 * a, 0), (0, -2 * b), (0, 0))
        reciprocal = {
            (0, 2): 1 / (4 * a), (1, 3): 1 / (4 * b),
            (0, 4): -1 / (2 * a), (2, 4): -1 / (2 * a),
            (1, 4): -1 / (2 * b), (3, 4): -1 / (2 * b),
        }
        for i, j in combinations(range(len(points)), 2):
            distance_squared = sum((x - y)**2 for x, y in zip(points[i], points[j]))
            assert reciprocal.get((i, j), Fraction(1, 2))**2 * distance_squared == 1
        for i, position in enumerate(points):
            for coordinate, value in enumerate(position):
                force = sum(
                    masses[j] * reciprocal.get(tuple(sorted((i, j))), Fraction(1, 2))**3
                    * (value - points[j][coordinate])
                    for j in range(len(points)) if j != i
                )
                assert force == value
        varying_products.add((points[0][0] - points[2][0])**2)
    assert len(varying_products) == 3
    print('Remark 1.4: three rational samples of the signed rhombus give distinct orbit invariants')


if __name__ == '__main__':
    check_nodes()
    check_negative_tau()
    check_roberts_slice()
