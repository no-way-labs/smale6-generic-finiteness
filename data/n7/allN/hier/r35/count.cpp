// R35 independent enumeration. A level is an arbitrary proper coarsening
// of a partition. A graph edge is the label of an unordered pair of bodies.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using std::array; using std::vector;
constexpr int E=15, V=12;
using Levels=array<int,E>;
struct Type { Levels rank{}, cluster{}, atLeast{}, higher{}; int levels=0; };
int n,edges;
array<int,E> leftEnd,rightEnd,cost,cheaper,sameCost;
vector<Type> types;
struct Stats { long long pairs=0, feasible=0, balanced=0, length2=0,length4=0,allBodies=0,example=0; };
void level(const vector<int>& blocks, Type cur);
void partitions(const vector<int>& old, Type cur, int next, vector<int>& bins) {
    if(next==(int)old.size()) {
        if(bins.size()==old.size()) return;
        Type t=cur;
        for(int e=0;e<edges;++e) if(!t.cluster[e]) {
            int both=(1<<leftEnd[e])|(1<<rightEnd[e]);
            for(int b:bins) if((b&both)==both) {t.rank[e]=t.levels;t.cluster[e]=b;break;}
        }
        ++t.levels;
        level(bins,t);
        return;
    }
    for(int i=0;i<(int)bins.size();++i) {
        bins[i]^=old[next]; partitions(old,cur,next+1,bins); bins[i]^=old[next];
    }
    bins.push_back(old[next]); partitions(old,cur,next+1,bins); bins.pop_back();
}
void level(const vector<int>& blocks, Type cur) {
    if(blocks.size()==1) {
        // First merger is the highest finite height.
        for(int e=0;e<edges;++e) cur.rank[e]=cur.levels-1-cur.rank[e];
        for(int e=0;e<edges;++e) for(int f=0;f<edges;++f) {
            if(cur.rank[f]>=cur.rank[e]) cur.atLeast[e]|=1<<f;
            if(cur.rank[f]>cur.rank[e]) cur.higher[e]|=1<<f;
        }
        types.push_back(cur);
        return;
    }
    vector<int> bins; partitions(blocks,cur,0,bins);
}
struct Graph {
    const Type& z; const Type& w; Stats& stats; bool nodes;
    int adj[V]{}, a[E]{},b[E]{}, candidates=0;
    void add(int e,int l,int r) {
        a[e]=l;b[e]=r;adj[l]|=1<<e;adj[r]|=1<<e;candidates|=1<<e;
    }
    bool heightFeasible(int cyc) {
        // Variables are increasing z levels, then NEGATED increasing w levels.
        // All maxima can be translated to zero. Multiply integer weights by k+1,
        // and give each strict inequality a gap of one. A simple directed
        // circuit has at most k strict edges: its feasibility sign is preserved.
        const int k=z.levels+w.levels, shift=k+1; long long ds[V]{};
        for(int pass=0;pass<k;++pass) {
            bool changed=false;
            auto relax=[&](int from,int to,int64_t len) {
                if(ds[to]>ds[from]+len){ ds[to]=ds[from]+len; changed=true; }
            };
            for(int i=1;i<z.levels;++i) relax(i,i-1,-1);
            for(int i=1;i<w.levels;++i) relax(z.levels+i-1,z.levels+i,-1);
            for(int e=0;e<edges;++e){
                int l=z.rank[e],r=z.levels+w.rank[e];
                int64_t lim=2LL*cost[e]*shift;
                relax(r,l,lim);
                if(cyc&(1<<e)) relax(l,r,-lim);
            }
            if(!changed) return true;
        }
        return false;
    }
    void evaluate(int plus,int minus) {
        int delta=0, bodies=0; int coeff[6]{};
        for(int m=plus|minus;m;m&=m-1) {
            int e=__builtin_ctz(m),s=(plus&(1<<e))?1:-1;
            delta+=s*cost[e]; coeff[leftEnd[e]]+=s; coeff[rightEnd[e]]+=s;
            bodies|=(1<<leftEnd[e])|(1<<rightEnd[e]);
        }
        if(nodes && std::any_of(coeff,coeff+n,[](int i){return i!=0;})) return;
        if(!nodes && delta) return;
        ++stats.balanced;
        int cyc=plus|minus;
        if(!nodes && !heightFeasible(cyc)) return;
        ++stats.feasible;
        int len=__builtin_popcount((unsigned)cyc);
        stats.length2+=(len==2);stats.length4+=(len==4);stats.allBodies+=(bodies==(1<<n)-1);
        // Under the lexicographic edge numbering for n=4, 01,03,12,23 = bits 0,2,3,5.
        stats.example+=(n==4 && cyc==45);
    }
    void walk(int start,int here,int visited,int allowed,int plus,int minus,bool positive) {
        for(int m=adj[here]&allowed;m;m&=m-1) {
            int e=__builtin_ctz(m), bit=1<<e;
            int next=a[e]^b[e]^here;
            int p=plus|(positive?bit:0), q=minus|(positive?0:bit);
            if(next==start) evaluate(p,q);
            else if(!(visited&(1<<next)))
                walk(start,next,visited|(1<<next),allowed^bit,p,q,!positive);
        }
    }
    void run() {
        ++stats.pairs;
        for(int e=0;e<edges;++e) {
            if(nodes) {
                unsigned both=z.cluster[e]&w.cluster[e];
                int i=__builtin_ctz(both);both&=both-1;
                if(i!=leftEnd[e] || __builtin_ctz(both)!=rightEnd[e]) continue;
            } else {
                int dominate=z.atLeast[e]&w.atLeast[e];
                if(dominate & (cheaper[e]|(sameCost[e]&(z.higher[e]|w.higher[e])))) continue;
            }
            add(e,z.rank[e],6+w.rank[e]);
        }
        // Remove leaves before enumerating simple cycles.
        for(bool again=true;again;) {
            again=false;
            for(int v=0;v<V;++v) if(adj[v] && !(adj[v]&(adj[v]-1))){
                int bit=adj[v],e=__builtin_ctz(bit);
                adj[a[e]]^=bit;adj[b[e]]^=bit;candidates^=bit;again=true;
            }
        }
        while(candidates) {
            int e=__builtin_ctz(candidates), bit=1<<e;
            candidates^=bit;
            walk(a[e],b[e],(1<<a[e])|(1<<b[e]),candidates,bit,0,false);
        }
    }
};
void count(int size,bool repeated) {
    n=size; edges=0; types.clear(); vector<int> singleton;
    int mass[6]{};
    for(int i=0;i<n;++i) {
        mass[i]=repeated?(i>=2):(i<2?i:(n*n+2)*mass[i-1]);
        singleton.push_back(1<<i);
    }
    for(int i=0;i<n;++i) for(int j=i+1;j<n;++j) {
        leftEnd[edges]=i;rightEnd[edges]=j;cost[edges++]=mass[i]+mass[j];
    }
    for(int e=0;e<edges;++e){
        cheaper[e]=sameCost[e]=0;
        for(int f=0;f<edges;++f){
            if(cost[f]<cost[e]) cheaper[e]|=1<<f;
            if(cost[f]==cost[e]) sameCost[e]|=1<<f;
        }
    }
    level(singleton,Type{});
    Stats ranks,hier;
    for(size_t i=0;i<types.size();++i) for(size_t j=i;j<types.size();++j)
        Graph{types[i],types[j],ranks,false}.run();
    printf("n=%d %s rank types=%zu unordered=%lld balanced=%lld feasible=%lld len2=%lld len4=%lld example=%lld\n",
           n,repeated?"repeated":"chamber",types.size(),ranks.pairs,ranks.balanced,ranks.feasible,ranks.length2,ranks.length4,ranks.example);
    if(repeated) {assert(ranks.feasible==82 && ranks.example>0);return;}
    assert(ranks.feasible==0);
    std::set<Levels> keys;
    vector<Type> unranked;
    for(auto t:types) if(keys.insert(t.cluster).second){
        Levels sorted=t.cluster;
        std::sort(sorted.begin(),sorted.begin()+edges);
        auto stop=std::unique(sorted.begin(),sorted.begin()+edges);
        for(int e=0;e<edges;++e) t.rank[e]=std::lower_bound(sorted.begin(),stop,t.cluster[e])-sorted.begin();
        unranked.push_back(t);
    }
    long long identical=0;
    for(size_t i=0;i<unranked.size();++i) for(size_t j=i;j<unranked.size();++j){
        auto before=hier.feasible; Graph{unranked[i],unranked[j],hier,true}.run();
        if(i==j) identical+=hier.feasible-before;
    }
    printf("   hierarchies=%zu unordered instances=%lld ordered instances=%lld through every body=%lld\n",
           unranked.size(),hier.feasible,2*hier.feasible-identical,hier.allBodies);
    assert(hier.feasible==(n==6?96:0) && hier.allBodies==hier.feasible);
}
int main(){count(4,true);for(int k=2;k<=6;++k) count(k,false);}
