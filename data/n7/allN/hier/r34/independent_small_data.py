"""Exact, independent checks of the weight-datum claims in Sections 9 and 11."""
from itertools import combinations, permutations
from z3 import And, BoolVal, Bool, Implies, Not, Or, Real, SolverFor, sat, unsat


class WeightDatum:
    def __init__(self, u):
        self.u = u
        self.n = len(u)
        vertices = range(self.n + 1)
        self.edges = list(combinations(vertices, 2))
        self.solver = SolverFor("QF_LRA")
        self.solver.set(timeout=90_000)
        self.heights = {}
        for color in ("z", "w"):
            for a, b in self.edges:
                infinite = Bool(f"{color}{a}{b}_inf") if b == self.n else BoolVal(False)
                self.heights[color, (a, b)] = infinite, Real(f"{color}{a}{b}")
            for a, b, c in permutations(vertices, 3):
                outer = self.height(color, a, c)
                self.solver.add(Or(self.ge(outer, self.height(color, a, b)),
                                   self.ge(outer, self.height(color, b, c))))

        self.scores = {}
        self.active = {}
        for a, b in self.edges:
            edge = (a, b)
            z_inf, z = self.heights["z", edge]
            w_inf, w = self.heights["w", edge]
            self.active[edge] = And(Not(z_inf), Not(w_inf))
            self.scores[edge] = (-z - w - u[a] if b == self.n
                                 else (z + w) / 2 - u[a] - u[b])

        for mask in range(1, 1 << self.n):
            for color, other in (("z", "w"), ("w", "z")):
                terms = []
                for a, b in self.edges:
                    a_inside = bool(mask & (1 << a))
                    b_inside = bool(mask & (1 << b))
                    if a_inside == b_inside:
                        continue
                    own_inf, own = self.height(color, a, b)
                    _, opposite = self.height(other, a, b)
                    value = (-u[a] - own if b == self.n else self.scores[a, b] + opposite)
                    terms.append((Not(own_inf), value))
                ties = []
                for (first_present, first), (second_present, second) in combinations(terms, 2):
                    ties.append(And(first_present, second_present, first == second,
                                    *(Implies(present, value <= first) for present, value in terms)))
                self.solver.add(Or(*ties))

        self.maximum = Real("maximum")
        self.solver.add(*(Implies(self.active[e], self.scores[e] <= self.maximum)
                          for e in self.edges))
        self.solver.add(Or(*(self.is_maximal(edge) for edge in self.edges)))

    @staticmethod
    def ge(left, right):
        left_inf, left_value = left
        right_inf, right_value = right
        return Or(left_inf, And(Not(right_inf), left_value >= right_value))

    def height(self, color, a, b):
        return self.heights[color, tuple(sorted((a, b)))]

    def is_maximal(self, edge):
        return And(self.active[edge], self.scores[edge] == self.maximum)

    def alternating_cycle(self, edges):
        by_color = ("w", "z")
        return And(*(self.is_maximal(edge) for edge in edges),
                   *(self.heights[by_color[i % 2], edge][1]
                     == self.heights[by_color[i % 2], edges[(i + 1) % len(edges)]][1]
                     for i, edge in enumerate(edges)))

    def check(self, label, condition, expected, show_model=False):
        self.solver.push()
        self.solver.add(condition)
        status = self.solver.check()
        detail = self.solver.reason_unknown() if status not in (sat, unsat) else ""
        print(f"{label}: {status} {detail}", flush=True)
        if show_model and status == sat:
            witness = self.solver.model()
            for color in ("z", "w"):
                values = {}
                for e in self.edges:
                    inf, val = self.heights[color, e]
                    values[e] = ("+inf" if str(witness.eval(inf)) == "True"
                                 else str(witness.eval(val)))
                print(f"  {color} {values}", flush=True)
        self.solver.pop()
        assert status == expected, (label, status, expected)


if __name__ == "__main__":
    three = WeightDatum((0, 1, 30))
    three.check("u=(0,1,30), maximum = -1 positive control", three.maximum == -1, sat)
    three.check("u=(0,1,30), maximum differs from -1, including origin strata",
                three.maximum != -1, unsat)
    four = WeightDatum((0, 1, 2, 3))
    sequence = [(0, 2), (2, 4), (0, 4), (0, 3)]
    four.check("u=(0,1,2,3), printed N=0 sequence with maximum 1000",
               And(four.alternating_cycle(sequence), four.maximum == 1000), sat, show_model=True)
    other = WeightDatum((0, 1, 30, 900))
    other.check("u=(0,1,30,900), same sequence",
                other.alternating_cycle(sequence), unsat)
