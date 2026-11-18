#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <utility>
#include <vector>

namespace {

constexpr int max_bodies = 6;
constexpr int max_edges = max_bodies * (max_bodies - 1) / 2;
constexpr int max_ranks = 2 * (max_bodies - 1);
using Integer = std::int64_t;
using Mask = unsigned;
using Pairs = std::vector<std::pair<int, int>>;
using Levels = std::array<int, max_edges>;
using Labels = std::array<int, max_bodies>;

struct Partition {
    Labels labels{};
    int blocks;
};

struct OrderType {
    Levels rank{};
    int levels;
    std::array<Mask, max_edges> at_least{};
    std::array<Mask, max_edges> higher{};

    OrderType(Levels ranks, int level_count, int edge_count)
        : rank(ranks), levels(level_count) {
        for (int e = 0; e < edge_count; ++e) {
            for (int f = 0; f < edge_count; ++f) {
                if (rank[f] >= rank[e]) at_least[e] |= 1u << f;
                if (rank[f] > rank[e]) higher[e] |= 1u << f;
            }
        }
    }
};

void strict_coarsenings(int old_blocks, int index, int new_blocks,
                        Labels& labels, std::vector<Partition>& result) {
    if (index == old_blocks) {
        if (new_blocks < old_blocks) result.push_back({labels, new_blocks});
        return;
    }
    for (int label = 0; label <= new_blocks; ++label) {
        labels[index] = label;
        strict_coarsenings(old_blocks, index + 1,
                           std::max(new_blocks, label + 1), labels, result);
    }
}

using Coarsenings = std::array<std::vector<Partition>, max_bodies + 1>;

void order_types(const Pairs& pairs, const Coarsenings& coarsenings,
                 const Partition& current, Levels merge_step, int step,
                 std::vector<OrderType>& result) {
    if (current.blocks == 1) {
        Levels rank{};
        for (int e = 0; e < static_cast<int>(pairs.size()); ++e) {
            rank[e] = step - 1 - merge_step[e];
        }
        result.emplace_back(rank, step, static_cast<int>(pairs.size()));
        return;
    }

    for (const auto& coarsening : coarsenings[current.blocks]) {
        Partition next{current.labels, coarsening.blocks};
        for (int& label : next.labels) label = coarsening.labels[label];
        Levels next_steps = merge_step;
        for (int e = 0; e < static_cast<int>(pairs.size()); ++e) {
            const auto [a, b] = pairs[e];
            if (current.labels[a] != current.labels[b] && next.labels[a] == next.labels[b]) {
                next_steps[e] = step;
            }
        }
        order_types(pairs, coarsenings, next, next_steps, step + 1, result);
    }
}

std::vector<OrderType> all_order_types(int n, const Pairs& pairs) {
    Coarsenings coarsenings;
    for (int blocks = 2; blocks <= n; ++blocks) {
        Labels labels{};
        strict_coarsenings(blocks, 0, 0, labels, coarsenings[blocks]);
    }

    Partition singletons{{}, n};
    std::iota(singletons.labels.begin(), singletons.labels.begin() + n, 0);
    std::vector<OrderType> result;
    order_types(pairs, coarsenings, singletons, {}, 0, result);

    const std::array<int, max_bodies + 1> expected_counts{0, 1, 1, 4, 32, 436, 9012};
    assert(result.size() == static_cast<std::size_t>(expected_counts[n]));
    std::set<Levels> distinct;
    for (const auto& type : result) {
        assert(distinct.insert(type.rank).second);
        int rank[max_bodies][max_bodies]{};
        for (int e = 0; e < static_cast<int>(pairs.size()); ++e) {
            const auto [a, b] = pairs[e];
            rank[a][b] = rank[b][a] = type.rank[e];
        }
        for (int a = 0; a < n; ++a) {
            for (int b = 0; b < n; ++b) {
                for (int c = 0; c < n; ++c) {
                    if (a != b && b != c && a != c) {
                        assert(rank[a][c] >= std::min(rank[a][b], rank[b][c]));
                    }
                }
            }
        }
    }
    return result;
}

struct Weights {
    std::array<Integer, max_edges> cost{};
    std::array<Mask, max_edges> lower{};
    std::array<Mask, max_edges> equal{};

    Weights(const Pairs& pairs, const std::vector<Integer>& u) {
        for (int e = 0; e < static_cast<int>(pairs.size()); ++e) {
            const auto [a, b] = pairs[e];
            cost[e] = 2 * (u[a] + u[b]);
        }
        for (int e = 0; e < static_cast<int>(pairs.size()); ++e) {
            for (int f = 0; f < static_cast<int>(pairs.size()); ++f) {
                if (cost[f] < cost[e]) lower[e] |= 1u << f;
                if (cost[f] == cost[e]) equal[e] |= 1u << f;
            }
        }
    }
};

struct Arc {
    int from;
    int to;
    Integer cost;
};

struct Counts {
    Integer order_pairs = 0;
    Integer order_pairs_with_cycles = 0;
    Integer candidate_cycles = 0;
    Integer balanced_cycles = 0;
    Integer feasible_cycles = 0;
    Integer feasible_two_edge_cycles = 0;
    Integer feasible_four_edge_cycles = 0;
};

class HeightGraph {
public:
    HeightGraph(const Pairs& pairs, const Weights& weights,
                const OrderType& z, const OrderType& w)
        : weights(weights), z(z), w(w),
          vertices(z.levels + w.levels), edges(static_cast<int>(pairs.size())) {}

    void inspect(Counts& counts) {
        ++counts.order_pairs;
        // Keep an edge unless some pair is guaranteed to have strictly larger Psi.
        int parent[max_ranks];
        std::iota(parent, parent + vertices, 0);
        bool cyclic = false;
        for (int e = 0; e < edges; ++e) {
            Mask at_least_both = z.at_least[e] & w.at_least[e];
            if ((at_least_both & weights.lower[e]) ||
                (at_least_both & weights.equal[e] & (z.higher[e] | w.higher[e]))) {
                continue;
            }
            const int left = z.rank[e];
            const int right = z.levels + w.rank[e];
            incident[left] |= 1u << e;
            incident[right] |= 1u << e;
            int left_root = left;
            int right_root = right;
            while (parent[left_root] != left_root) left_root = parent[left_root];
            while (parent[right_root] != right_root) right_root = parent[right_root];
            if (left_root == right_root) cyclic = true;
            else parent[left_root] = right_root;
        }
        if (!cyclic) return;
        ++counts.order_pairs_with_cycles;

        // In each cycle use its lowest-numbered edge as the first edge, then
        // follow the rest of the cycle from its z-end to its w-end.
        for (int anchor = 0; anchor < edges; ++anchor) {
            const int start = z.rank[anchor];
            if (!(incident[start] & (1u << anchor))) continue;
            const Mask larger_edges = ~((1u << (anchor + 1)) - 1);
            walk(start, z.levels + w.rank[anchor], 1u << start, larger_edges,
                 1u << anchor, 1, weights.cost[anchor], counts);
        }
    }

private:
    const Weights& weights;
    const OrderType& z;
    const OrderType& w;
    int vertices;
    int edges;
    std::array<Mask, max_ranks> incident{};

    void walk(int here, int end, Mask visited, Mask larger_edges, Mask cycle,
              int length, Integer balance, Counts& counts) const {
        if (here == end) {
            ++counts.candidate_cycles;
            if (balance == 0) {
                ++counts.balanced_cycles;
                if (feasible(cycle)) {
                    ++counts.feasible_cycles;
                    if (length == 2) ++counts.feasible_two_edge_cycles;
                    if (length == 4) ++counts.feasible_four_edge_cycles;
                }
            }
            return;
        }
        const Mask available = incident[here] & larger_edges;
        for (int e = 0; e < edges; ++e) {
            if (!(available & (1u << e))) continue;
            const int next = here < z.levels ? z.levels + w.rank[e] : z.rank[e];
            if (visited & (1u << next)) continue;
            const Integer signed_cost = length % 2 == 0 ? weights.cost[e] : -weights.cost[e];
            walk(next, end, visited | (1u << next), larger_edges, cycle | (1u << e),
                 length + 1, balance + signed_cost, counts);
        }
    }

    bool feasible(Mask cycle) const {
        // Put x_i = z_i and y_j = 2 Psi^o - w_j. An arc a -> b of
        // cost c denotes b - a <= c. Scale integer costs by vertices + 1
        // and use -1 for each strict rank comparison of cost zero.
        const Integer denominator = vertices + 1;
        std::vector<Arc> arcs;
        for (int i = 0; i + 1 < z.levels; ++i) arcs.push_back({i + 1, i, -1});
        for (int j = z.levels; j + 1 < vertices; ++j) arcs.push_back({j, j + 1, -1});
        for (int e = 0; e < edges; ++e) {
            const int x = z.rank[e];
            const int y = z.levels + w.rank[e];
            const Integer cost = denominator * weights.cost[e];
            arcs.push_back({y, x, cost});
            if (cycle & (1u << e)) arcs.push_back({x, y, -cost});
        }

        std::array<Integer, max_ranks> value{};
        for (int pass = 0; pass < vertices; ++pass) {
            bool changed = false;
            for (const auto& [from, to, cost] : arcs) {
                if (value[to] > value[from] + cost) {
                    value[to] = value[from] + cost;
                    changed = true;
                }
            }
            if (!changed) return true;
        }
        return false;  // A negative cycle makes the difference constraints infeasible.
    }
};

void print_counts(const char* label, const std::vector<Integer>& u,
                  std::size_t order_types_count, const Counts& counts) {
    std::cout << label << " n=" << u.size() << " u=(";
    for (std::size_t i = 0; i < u.size(); ++i) std::cout << (i ? "," : "") << u[i];
    std::cout << ") types=" << order_types_count << " pairs=" << counts.order_pairs
              << " pairs_with_cycles=" << counts.order_pairs_with_cycles
              << " candidate_cycles=" << counts.candidate_cycles
              << " balanced_cycles=" << counts.balanced_cycles
              << " feasible_cycles=" << counts.feasible_cycles
              << " feasible_length_2=" << counts.feasible_two_edge_cycles
              << " feasible_length_4=" << counts.feasible_four_edge_cycles << '\n';
}

Pairs body_pairs(int n) {
    Pairs pairs;
    for (int a = 0; a < n; ++a) {
        for (int b = a + 1; b < n; ++b) pairs.emplace_back(a, b);
    }
    return pairs;
}

Counts search(const std::vector<Integer>& u, const char* label) {
    const int n = static_cast<int>(u.size());
    const auto pairs = body_pairs(n);
    const auto types = all_order_types(n, pairs);
    const Weights weights(pairs, u);
    Counts counts;
    for (std::size_t i = 0; i < types.size(); ++i) {
        for (std::size_t j = i; j < types.size(); ++j) {
            HeightGraph(pairs, weights, types[i], types[j]).inspect(counts);
        }
    }
    print_counts(label, u, types.size(), counts);
    return counts;
}

}  // namespace

int main() {
    const std::vector<Integer> control{0, 0, 1, 1};
    const auto control_counts = search(control, "control");
    assert(control_counts.feasible_two_edge_cycles > 0);
    assert(control_counts.feasible_four_edge_cycles > 0);

    const auto pairs = body_pairs(4);
    const Weights weights(pairs, control);
    const OrderType z({0, 0, 0, 1, 1, 1}, 2, 6);
    const OrderType w({0, 1, 1, 0, 0, 1}, 2, 6);
    Counts example;
    HeightGraph(pairs, weights, z, w).inspect(example);
    print_counts("printed_example", control, 2, example);
    assert(example.feasible_two_edge_cycles == 2);
    assert(example.feasible_four_edge_cycles == 4);

    for (int n = 2; n <= max_bodies; ++n) {
        std::vector<Integer> u(n);
        u[1] = 1;
        for (int j = 2; j < n; ++j) {
            u[j] = (n * n + 2) * u[j - 1];
            assert(u[j] - u[j - 1] > n * n * (u[j - 1] - u[0]));
        }
        search(u, "chamber");
    }
}
