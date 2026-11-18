"""Recur on the minimum/saddle counts using Xia pp. 175-176. No archived code."""
from collections import Counter
def totals(distribution, size):
    for n in range(size,19):
        if n>=4:yield n,sum(distribution.values())
        nxt=Counter()
        for (minima,saddles),copies in distribution.items():
            # Selecting a minimum replaces it by two minima and two saddles.
            nxt[minima+1,saddles+2]+=copies*minima
            # Selecting a saddle replaces it by two saddles.
            nxt[minima,saddles+1]+=copies*saddles
        distribution=nxt
two=dict(totals(Counter({(2,3):1}),2))
three=dict(totals(Counter({(4,6):2,(2,4):3}),3))
for n in two: print(n,two[n],three[n])
assert (two[4],three[4])==(34,38) and (two[5],three[5])==(294,374)

