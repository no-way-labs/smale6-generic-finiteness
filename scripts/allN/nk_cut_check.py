"""Recheck of the recorded points of an nk_fibre.py output (docs/allN-direct-route.md section 4).

For each point of FILE (plain or .gz), from the recorded heights alone and with an absolute tolerance:
  the two ultrametric conditions on the K + 1 leaves (the bodies and the origin O);
  every cut condition of both colours: for a nonempty set S of bodies, the largest of the values
      -u_t - xi_t (t in S)  and  Psi(t, l) + omega_tl (t in S, l not in S)        (colour z; colour w with eta, zeta)
  is attained at least twice.
The script does not use the trees or the LPs of the search.  Standard library.

Usage: nk_cut_check.py FILE [FILE ...] [--tol T]      (default 1e-3)
"""
import gzip, json, sys
from itertools import combinations
tol = 1e-3
args = sys.argv[1:]
if '--tol' in args:
    i = args.index('--tol'); tol = float(args[i + 1]); del args[i:i + 2]
for fn in args:
    d = json.load(gzip.open(fn) if fn.endswith('.gz') else open(fn))
    K, u = d['K'], d['u']
    bad_cut = bad_um = 0
    worst = 0.0
    ex = None
    for p in d['points']:
        z = {}; w = {}
        for a, b in combinations(range(K), 2):
            z[a, b] = z[b, a] = p['zeta']['%d%d' % (a, b)]
            w[a, b] = w[b, a] = p['omega']['%d%d' % (a, b)]
        for t in range(K):
            z[t, K] = z[K, t] = p['xi'][t]
            w[t, K] = w[K, t] = p['eta'][t]
        um = True
        for m in (z, w):
            for a, b, c in combinations(range(K + 1), 3):
                v = sorted((m[a, b], m[b, c], m[a, c]))
                if v[1] - v[0] > tol:
                    um = False
        bad_um += not um
        fail = 0
        for mask in range(1, 1 << K):
            S = [t for t in range(K) if mask >> t & 1]
            for col, hh in (('z', w), ('w', z)):          # colour z: Psi + omega; colour w: Psi + zeta
                pos = z if col == 'z' else w
                vals = [-u[t] - pos[t, K] for t in S]
                vals += [(z[t, l] + w[t, l]) / 2 - u[t] - u[l] + hh[t, l] for t in S for l in range(K) if l not in S]
                vals.sort()
                gap = vals[-1] - vals[-2] if len(vals) > 1 else float('inf')
                if gap > tol:
                    fail += 1
                    worst = max(worst, gap)
        if fail:
            bad_cut += 1
            if ex is None:
                ex = (p['trees'], p['psi'], fail)
    print('%s: points %d, with an ultrametric failure %d, with a cut condition that fails %d (largest gap %.4g; tol %g)%s'
          % (fn.split('/')[-1], len(d['points']), bad_um, bad_cut, worst, tol, '' if ex is None else '  first: trees %s psi %s, %d cuts fail' % ex))
