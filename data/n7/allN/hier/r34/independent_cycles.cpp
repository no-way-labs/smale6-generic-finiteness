#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <set>
#include <utility>
#include <vector>

namespace {
constexpr int maxBodies = 6;
constexpr int maxPairs = 15;
constexpr int maxNodes = 2 * (maxBodies - 1);
using Mask = std::uint32_t;
using Weight = std::int64_t;
using Heights = std::array<int, maxPairs>;
using Pair = std::pair<int, int>;
using Pairs = std::vector<Pair>;
using Weights = std::array<Weight, maxPairs>;

Pairs bodyPairs(int n) {
    Pairs pairs;
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) pairs.emplace_back(i, j);
    }
    return pairs;
}

void partitions(const Pairs& edges, std::vector<int>& block, int blocks,
                int n, std::vector<Mask>& result) {
    if (static_cast<int>(block.size()) == n) {
        Mask together = 0;
        for (int e = 0; e < static_cast<int>(edges.size()); ++e) {
            const auto [a, b] = edges[e];
            if (block[a] == block[b]) together |= Mask{1} << e;
        }
        result.push_back(together);
        return;
    }
    for (int next = 0; next <= blocks; ++next) {
        block.push_back(next);
        partitions(edges, block, blocks + (next == blocks), n, result);
        block.pop_back();
    }
}

void orderTypes(const std::vector<Mask>& partitionMasks, Mask current, int height,
                Heights ranks, std::vector<Heights>& result) {
    if (current == 0) {
        result.push_back(ranks);
        return;
    }
    for (Mask next : partitionMasks) {
        // The next threshold partition strictly refines the current partition.
        if (next == current || (next & ~current) != 0) continue;
        Heights refined = ranks;
        for (Mask split = current ^ next; split; split &= split - 1) {
            refined[std::countr_zero(split)] = height;
        }
        orderTypes(partitionMasks, next, height + 1, refined, result);
    }
}

struct RankType {
    Heights rank;
    std::array<Mask, maxPairs> atLeast{};
    std::array<Mask, maxPairs> greater{};
    int levels;

    RankType(const Heights& heights, int size)
        : rank(heights), levels(1 + *std::max_element(rank.begin(), rank.begin() + size)) {
        for (int e = 0; e < size; ++e) {
            for (int f = 0; f < size; ++f) {
                if (rank[f] >= rank[e]) atLeast[e] |= Mask{1} << f;
                if (rank[f] > rank[e]) greater[e] |= Mask{1} << f;
            }
        }
    }
};

struct ClusterTree {
    std::array<Mask, maxPairs> cluster;
    Heights node{};
    int nodes = 0;

    ClusterTree(const std::array<Mask, maxPairs>& clusters, int size) : cluster(clusters) {
        for (int e = 0; e < size; ++e) {
            const auto first = std::find(cluster.begin(), cluster.begin() + e, cluster[e]);
            node[e] = first == cluster.begin() + e ? nodes++ : node[first - cluster.begin()];
        }
    }
};

struct Graph {
    std::array<int, maxPairs> left{};
    std::array<int, maxPairs> right{};
    std::array<Mask, maxNodes> incident{};
    std::array<int, maxNodes> parent{};
    bool hasCycle = false;

    Graph() { std::iota(parent.begin(), parent.end(), 0); }

    int root(int node) const {
        while (parent[node] != node) node = parent[node];
        return node;
    }

    void add(int edge, int a, int b) {
        left[edge] = a;
        right[edge] = b;
        incident[a] |= Mask{1} << edge;
        incident[b] |= Mask{1} << edge;
        const int ra = root(a);
        const int rb = root(b);
        if (ra == rb) hasCycle = true;
        else parent[ra] = rb;
    }

    template <typename Visit>
    void walk(int start, int current, Mask vertices, Mask edges, int first,
              Weight alternatingSum, const Weights& weights, const Visit& visit) const {
        for (Mask choices = incident[current] & ~edges; choices; choices &= choices - 1) {
            const int e = std::countr_zero(choices);
            const int next = left[e] == current ? right[e] : left[e];
            const Mask withEdge = edges | (Mask{1} << e);
            const Weight updated = alternatingSum + (std::popcount(edges) % 2 ? -weights[e] : weights[e]);
            if (next == start) {
                // The smallest vertex and this edge inequality select one orientation.
                if (first < e) visit(withEdge, updated);
            } else if (next > start && !(vertices & (Mask{1} << next))) {
                walk(start, next, vertices | (Mask{1} << next), withEdge,
                     edges ? first : e, updated, weights, visit);
            }
        }
    }

    template <typename Visit>
    void cycles(int vertices, const Weights& weights, const Visit& visit) const {
        if (!hasCycle) return;
        for (int start = 0; start < vertices; ++start) {
            walk(start, start, Mask{1} << start, 0, -1, 0, weights, visit);
        }
    }
};

bool feasible(const RankType& z, const RankType& w, const Weights& cost,
              int pairs, Mask cycle) {
    // A_i is a z height and B_j is minus a w height with the maximum score shifted to zero.
    const int vertices = z.levels + w.levels;
    const Weight infinity = Weight{1} << 45;
    Weight dist[maxNodes][maxNodes];
    for (int i = 0; i < vertices; ++i) {
        for (int j = 0; j < vertices; ++j) dist[i][j] = i == j ? 0 : infinity;
    }
    const auto bound = [&](int from, int to, Weight value) {
        dist[from][to] = std::min(dist[from][to], value);
    };
    // Costs are integers. A unit of strictness after multiplying by V+1 detects
    // exactly the obstructing simple circuits, which have at most V arcs.
    for (int i = 1; i < z.levels; ++i) bound(i, i - 1, -1);
    for (int j = 1; j < w.levels; ++j) bound(z.levels + j - 1, z.levels + j, -1);
    for (int e = 0; e < pairs; ++e) {
        const int left = z.rank[e];
        const int right = z.levels + w.rank[e];
        const Weight scaled = cost[e] * (vertices + 1);
        bound(right, left, scaled);
        if (cycle & (Mask{1} << e)) bound(left, right, -scaled);
    }
    for (int through = 0; through < vertices; ++through) {
        for (int from = 0; from < vertices; ++from) {
            if (dist[from][through] == infinity) continue;
            for (int to = 0; to < vertices; ++to) {
                if (dist[through][to] == infinity) continue;
                bound(from, to, dist[from][through] + dist[through][to]);
            }
        }
        for (int i = 0; i < vertices; ++i) if (dist[i][i] < 0) return false;
    }
    return true;
}

struct Counts {
    std::uint64_t graphPairs = 0;
    std::uint64_t candidate = 0;
    std::uint64_t balanced = 0;
    std::uint64_t feasible = 0;
    std::uint64_t lengthTwo = 0;
    std::uint64_t lengthFour = 0;
};

Counts rankedSearch(const std::vector<RankType>& types, const Pairs& edges,
                    const std::vector<Weight>& masses, Mask* knownCycle = nullptr) {
    const int pairs = static_cast<int>(edges.size());
    Weights cost{};
    std::array<Mask, maxPairs> cheaper{}, sameCost{};
    for (int e = 0; e < pairs; ++e) {
        const auto [a, b] = edges[e];
        cost[e] = 2 * (masses[a] + masses[b]);
    }
    for (int e = 0; e < pairs; ++e) {
        for (int f = 0; f < pairs; ++f) {
            if (cost[f] < cost[e]) cheaper[e] |= Mask{1} << f;
            if (cost[f] == cost[e]) sameCost[e] |= Mask{1} << f;
        }
    }
    Counts result;
    for (std::size_t i = 0; i < types.size(); ++i) {
        const auto& z = types[i];
        for (std::size_t j = 0; j <= i; ++j) {
            const auto& w = types[j];
            Graph graph;
            for (int e = 0; e < pairs; ++e) {
                const Mask noLower = z.atLeast[e] & w.atLeast[e];
                const Mask strictlyHigher = z.greater[e] | w.greater[e];
                if (noLower & (cheaper[e] | (sameCost[e] & strictlyHigher))) continue;
                graph.add(e, z.rank[e], z.levels + w.rank[e]);
            }
            result.graphPairs += graph.hasCycle;
            graph.cycles(z.levels + w.levels, cost, [&](Mask cycle, Weight sum) {
                ++result.candidate;
                if (sum != 0) return;
                ++result.balanced;
                if (!feasible(z, w, cost, pairs, cycle)) return;
                ++result.feasible;
                result.lengthTwo += std::popcount(cycle) == 2;
                result.lengthFour += std::popcount(cycle) == 4;
                if (knownCycle != nullptr && cycle == *knownCycle) *knownCycle = 0;
            });
        }
    }
    return result;
}

std::vector<ClusterTree> uniqueTrees(const std::vector<RankType>& types, const Pairs& edges) {
    std::set<std::array<Mask, maxPairs>> clusters;
    for (const auto& type : types) {
        std::array<Mask, maxPairs> tree{};
        for (int e = 0; e < static_cast<int>(edges.size()); ++e) {
            const auto [a, b] = edges[e];
            tree[e] = (Mask{1} << a) | (Mask{1} << b);
            for (int f = 0; f < static_cast<int>(edges.size()); ++f) {
                const auto [x, y] = edges[f];
                if (type.rank[f] < type.rank[e]) continue;
                if (x == a) tree[e] |= Mask{1} << y;
                if (y == a) tree[e] |= Mask{1} << x;
            }
        }
        clusters.insert(tree);
    }
    std::vector<ClusterTree> result;
    for (const auto& tree : clusters) result.emplace_back(tree, static_cast<int>(edges.size()));
    return result;
}

std::uint64_t balancedNodeCycles(const std::vector<ClusterTree>& trees, const Pairs& edges) {
    const int pairs = static_cast<int>(edges.size());
    std::array<Mask, maxPairs> endpoints{};
    Weights incidence{};
    for (int e = 0; e < pairs; ++e) {
        const auto [a, b] = edges[e];
        endpoints[e] = (Mask{1} << a) | (Mask{1} << b);
        // No coefficient difference exceeds 5 in magnitude. Base 16
        // encodes the condition that all signed incidence sums vanish.
        incidence[e] = (Weight{1} << (4 * a)) + (Weight{1} << (4 * b));
    }
    std::uint64_t result = 0;
    for (std::size_t i = 0; i < trees.size(); ++i) {
        const auto& z = trees[i];
        for (std::size_t j = 0; j <= i; ++j) {
            const auto& w = trees[j];
            Graph graph;
            for (int e = 0; e < pairs; ++e) {
                const Mask overlap = z.cluster[e] & w.cluster[e];
                const Mask first = overlap & -overlap;
                const Mask rest = overlap ^ first;
                const Mask firstTwo = first | (rest & -rest);
                if (firstTwo == endpoints[e]) graph.add(e, z.node[e], z.nodes + w.node[e]);
            }
            graph.cycles(z.nodes + w.nodes, incidence, [&](Mask cycle, Weight sum) {
                if (sum != 0) return;
                Mask support = 0;
                for (Mask remaining = cycle; remaining; remaining &= remaining - 1) {
                    support |= endpoints[std::countr_zero(remaining)];
                }
                assert(pairs != 15 || (std::popcount(support) == 6 && std::popcount(cycle) == 6));
                ++result;
            });
        }
    }
    return result;
}

void print(const char* label, std::size_t types, const Counts& counts) {
    std::cout << label << " types=" << types << " pairs=" << types * (types + 1) / 2
              << " cyclic_graphs=" << counts.graphPairs << " candidate=" << counts.candidate
              << " balanced=" << counts.balanced << " feasible=" << counts.feasible
              << " length2=" << counts.lengthTwo << " length4=" << counts.lengthFour << std::endl;
}
} // namespace

int main() {
    for (int n = 2; n <= maxBodies; ++n) {
        const Pairs edges = bodyPairs(n);
        std::vector<int> block;
        std::vector<Mask> partitionMasks;
        partitions(edges, block, 0, n, partitionMasks);
        std::vector<Heights> ranks;
        orderTypes(partitionMasks, (Mask{1} << edges.size()) - 1, 0, {}, ranks);
        std::vector<RankType> types;
        for (const auto& rank : ranks) types.emplace_back(rank, static_cast<int>(edges.size()));
        if (n == 4) {
            Mask example = (Mask{1} << 0) | (Mask{1} << 3) | (Mask{1} << 5) | (Mask{1} << 2);
            const auto result = rankedSearch(types, edges, {0, 0, 1, 1}, &example);
            print("n=4 repeated-mass control", types.size(), result);
            assert(example == 0 && result.feasible == 82 && result.lengthFour == 4);
        }
        std::vector<Weight> masses(n, 0);
        masses[1] = 1;
        for (int k = 2; k < n; ++k) masses[k] = (n * n + 2) * masses[k - 1];
        std::cout << "n=" << n << ' ';
        print("chamber", types.size(), rankedSearch(types, edges, masses));
        const auto trees = uniqueTrees(types, edges);
        std::cout << "n=" << n << " unranked trees=" << trees.size()
                  << " heaviest-pair balanced simple cycles (unordered trees)="
                  << balancedNodeCycles(trees, edges) << std::endl;
    }
}
