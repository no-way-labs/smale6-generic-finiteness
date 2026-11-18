// Independent F9 check. Build ranks by splitting partitions and test equality
// on simple cycles of the rank graph with exact, strict difference bounds.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <utility>
#include <vector>

namespace {
constexpr int max_bodies = 6;
constexpr int max_pairs = 15;
constexpr int max_vertices = 10;
using Mask = unsigned;
using Integer = std::int64_t;
using Ranks = std::array<int, max_pairs>;
using BodyPairs = std::vector<std::pair<int, int>>;

BodyPairs body_pairs(int n) {
    BodyPairs pairs;
    for (int a = 0; a < n; ++a) {
        for (int b = a + 1; b < n; ++b) pairs.emplace_back(a, b);
    }
    return pairs;
}

// A partition is encoded by the mask of body pairs in the same block.
void partitions(Mask remaining, Mask together, const BodyPairs& pairs,
                std::vector<Mask>& result) {
    if (remaining == 0) {
        result.push_back(together);
        return;
    }
    const Mask first = 1u << std::countr_zero(remaining);
    const Mask rest = remaining ^ first;
    for (Mask subset = rest;; subset = (subset - 1) & rest) {
        const Mask block = first | subset;
        Mask with_block = together;
        for (std::size_t e = 0; e < pairs.size(); ++e) {
            const auto [a, b] = pairs[e];
            const Mask endpoints = (1u << a) | (1u << b);
            if ((block & endpoints) == endpoints) with_block |= 1u << e;
        }
        partitions(remaining ^ block, with_block, pairs, result);
        if (subset == 0) break;
    }
}

struct OrderType {
    Ranks rank;
    int levels;
    std::array<Mask, max_pairs> weakly_higher{};
    std::array<Mask, max_pairs> strictly_higher{};

    OrderType(const Ranks& ranks, int count, int pairs) : rank(ranks), levels(count) {
        for (int e = 0; e < pairs; ++e) {
            for (int f = 0; f < pairs; ++f) {
                if (rank[f] >= rank[e]) weakly_higher[e] |= 1u << f;
                if (rank[f] > rank[e]) strictly_higher[e] |= 1u << f;
            }
        }
    }
};

void refinement_chains(Mask together, const std::vector<std::vector<Mask>>& refinements,
                       const Ranks& ranks, int level, int pair_count,
                       std::vector<OrderType>& result) {
    if (together == 0) {
        result.emplace_back(ranks, level, pair_count);
        return;
    }
    for (const Mask next : refinements[together]) {
        Ranks next_ranks = ranks;
        for (Mask separated = together ^ next; separated; separated &= separated - 1) {
            next_ranks[std::countr_zero(separated)] = level;
        }
        refinement_chains(next, refinements, next_ranks, level + 1, pair_count, result);
    }
}

std::vector<OrderType> order_types(int n, const BodyPairs& pairs) {
    std::vector<Mask> states;
    partitions((1u << n) - 1, 0, pairs, states);
    const Mask root = (1u << pairs.size()) - 1;
    std::vector<std::vector<Mask>> refinements(root + 1);
    for (const Mask coarse : states) {
        for (const Mask fine : states) {
            if (coarse != fine && (coarse & fine) == fine) refinements[coarse].push_back(fine);
        }
    }
    std::vector<OrderType> result;
    refinement_chains(root, refinements, {}, 0, static_cast<int>(pairs.size()), result);
    std::set<Ranks> distinct;
    for (const auto& type : result) assert(distinct.insert(type.rank).second);
    return result;
}

struct Costs {
    std::array<Integer, max_pairs> mass_cost{};
    std::array<Mask, max_pairs> cheaper{};
    std::array<Mask, max_pairs> equal{};
    int pair_count;

    Costs(const std::vector<Integer>& u, const BodyPairs& pairs)
        : pair_count(static_cast<int>(pairs.size())) {
        for (int e = 0; e < pair_count; ++e) {
            const auto [a, b] = pairs[e];
            mass_cost[e] = 2 * (u[a] + u[b]);
        }
        for (int e = 0; e < pair_count; ++e) {
            for (int f = 0; f < pair_count; ++f) {
                if (mass_cost[f] < mass_cost[e]) cheaper[e] |= 1u << f;
                if (mass_cost[f] == mass_cost[e]) equal[e] |= 1u << f;
            }
        }
    }
};

struct Counts {
    Integer order_pairs = 0;
    Integer cyclic_pairs = 0;
    Integer simple_cycles = 0;
    Integer balanced = 0;
    Integer feasible = 0;
    Integer length_two = 0;
    Integer length_four = 0;
};

class RankGraph {
public:
    RankGraph(const OrderType& z, const OrderType& w, const Costs& costs)
        : z(z), w(w), costs(costs), vertices(z.levels + w.levels) {}

    void inspect(Counts& counts) {
        ++counts.order_pairs;
        std::array<int, max_vertices> parent{};
        for (int i = 0; i < vertices; ++i) parent[i] = i;
        const auto root = [&parent](int i) {
            while (i != parent[i]) i = parent[i];
            return i;
        };
        bool cyclic = false;
        for (int e = 0; e < costs.pair_count; ++e) {
            left[e] = z.rank[e];
            right[e] = z.levels + w.rank[e];
            const Mask dominates = z.weakly_higher[e] & w.weakly_higher[e];
            const Mask strict = costs.cheaper[e] |
                (costs.equal[e] & (z.strictly_higher[e] | w.strictly_higher[e]));
            if (dominates & strict) continue;
            incident[left[e]] |= 1u << e;
            incident[right[e]] |= 1u << e;
            const int a = root(left[e]);
            const int b = root(right[e]);
            if (a == b) cyclic = true;
            else parent[a] = b;
        }
        if (!cyclic) return;
        ++counts.cyclic_pairs;

        // The least vertex fixes the start. The smaller of its two cycle
        // edges fixes orientation, also for a cycle of two parallel edges.
        for (int start = 0; start < z.levels; ++start) {
            for (Mask edges = incident[start]; edges; edges &= edges - 1) {
                const int first = std::countr_zero(edges);
                const int next = right[first];
                walk(start, next, first, (1u << start) | (1u << next),
                     1u << first, 1, costs.mass_cost[first], counts);
            }
        }
    }

    bool feasible(Mask cycle) const {
        // Normalize the maximum score to zero. Use z_i and -w_j as
        // variables, and represent c - epsilon by the pair (c, -1).
        // A difference system is feasible iff no directed cycle has total
        // bound lexicographically below (0, 0).
        using Bound = std::pair<Integer, int>;
        const Bound infinite{Integer{1} << 50, 0};
        std::array<std::array<Bound, max_vertices>, max_vertices> distance;
        for (int i = 0; i < vertices; ++i) {
            distance[i].fill(infinite);
            distance[i][i] = {0, 0};
        }
        const auto add = [&distance](int from, int to, Bound bound) {
            distance[from][to] = std::min(distance[from][to], bound);
        };
        for (int i = 1; i < z.levels; ++i) add(i, i - 1, {0, -1});
        for (int j = z.levels + 1; j < vertices; ++j) add(j - 1, j, {0, -1});
        for (int e = 0; e < costs.pair_count; ++e) {
            add(right[e], left[e], {costs.mass_cost[e], 0});
            if (cycle & (1u << e)) add(left[e], right[e], {-costs.mass_cost[e], 0});
        }
        for (int via = 0; via < vertices; ++via) {
            for (int i = 0; i < vertices; ++i) {
                if (distance[i][via] == infinite) continue;
                for (int j = 0; j < vertices; ++j) {
                    if (distance[via][j] == infinite) continue;
                    const auto [a, b] = distance[i][via];
                    const auto [c, d] = distance[via][j];
                    add(i, j, {a + c, b + d});
                }
            }
            for (int i = 0; i < vertices; ++i) {
                if (distance[i][i] < Bound{0, 0}) return false;
            }
        }
        return true;
    }

private:
    void walk(int start, int at, int first, Mask seen, Mask cycle, int length,
              Integer balance, Counts& counts) const {
        for (Mask edges = incident[at] & ~cycle; edges; edges &= edges - 1) {
            const int e = std::countr_zero(edges);
            const int next = at == left[e] ? right[e] : left[e];
            const Integer new_balance = balance + (length % 2 ? -1 : 1) * costs.mass_cost[e];
            const Mask new_cycle = cycle | (1u << e);
            if (next == start && e > first) {
                ++counts.simple_cycles;
                if (new_balance == 0) {
                    ++counts.balanced;
                    if (feasible(new_cycle)) {
                        ++counts.feasible;
                        if (length == 1) ++counts.length_two;
                        if (length == 3) ++counts.length_four;
                    }
                }
            }
            if (next > start && !(seen & (1u << next))) {
                walk(start, next, first, seen | (1u << next), new_cycle,
                     length + 1, new_balance, counts);
            }
        }
    }

    const OrderType& z;
    const OrderType& w;
    const Costs& costs;
    int vertices;
    Ranks left{};
    Ranks right{};
    std::array<Mask, max_vertices> incident{};
};

void print(const char* label, const std::vector<Integer>& u, std::size_t types, const Counts& counts) {
    std::cout << label << " n=" << u.size() << " u=(";
    for (std::size_t i = 0; i < u.size(); ++i) std::cout << (i == 0 ? "" : ",") << u[i];
    std::cout << ") types=" << types << " pairs=" << counts.order_pairs
              << " pairs_with_cycles=" << counts.cyclic_pairs
              << " candidate_cycles=" << counts.simple_cycles << " balanced_cycles=" << counts.balanced
              << " feasible_cycles=" << counts.feasible << " feasible_length_2=" << counts.length_two
              << " feasible_length_4=" << counts.length_four << '\n';
}

void search(const char* label, const std::vector<Integer>& u) {
    const int n = static_cast<int>(u.size());
    const auto pairs = body_pairs(n);
    const auto types = order_types(n, pairs);
    const Costs costs(u, pairs);
    Counts counts;
    for (std::size_t i = 0; i < types.size(); ++i) {
        for (std::size_t j = 0; j <= i; ++j) RankGraph(types[i], types[j], costs).inspect(counts);
    }
    print(label, u, types.size(), counts);
}
}  // namespace

int main() {
    const std::vector<Integer> control{0, 0, 1, 1};
    search("control", control);
    const auto pairs = body_pairs(4);
    const Costs costs(control, pairs);
    const OrderType z({0, 0, 0, 1, 1, 1}, 2, 6);
    const OrderType w({0, 1, 1, 0, 0, 1}, 2, 6);
    RankGraph example(z, w, costs);
    Counts counts;
    example.inspect(counts);
    print("printed_example", control, 2, counts);
    // The printed heights are twice the ranks and all six pairs have score zero.
    for (int e = 0; e < costs.pair_count; ++e) {
        assert(2 * (z.rank[e] + w.rank[e]) == costs.mass_cost[e]);
    }
    const std::array<int, 4> cycle{0, 3, 5, 2};  // 01, 12, 23, 03
    assert(w.rank[cycle[0]] == w.rank[cycle[1]] && w.rank[cycle[2]] == w.rank[cycle[3]]);
    assert(z.rank[cycle[1]] == z.rank[cycle[2]] && z.rank[cycle[3]] == z.rank[cycle[0]]);
    Mask example_edges = 0;
    for (const int e : cycle) example_edges |= 1u << e;
    assert(example.feasible(example_edges));

    for (int n = 2; n <= max_bodies; ++n) {
        std::vector<Integer> u(n);
        u[1] = 1;
        for (int j = 2; j < n; ++j) {
            u[j] = (n * n + 2) * u[j - 1];
            assert(u[j] - u[j - 1] > n * n * (u[j - 1] - u[0]));
        }
        search("chamber", u);
    }
}
