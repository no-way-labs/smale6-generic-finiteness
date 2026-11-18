"""R29: batches of runs of r29_lp.py.   PY r29_batch.py n3 | n3strata | n3ctl | n4 | n4strata | n4ctl | n4far"""
import sys
import time

import r29_lp as L


def go(n, u, zs, ws, mode, R=None, show=1):
    t0 = time.time()
    found, nlp, nodd, npairs = L.run(n, [float(x) for x in u.split(',')], zs, ws, mode, R, 4)
    L.report(n, u.split(','), zs, ws, mode, R, found, nlp, nodd, npairs, time.time() - t0, show)


W3 = ['0,1,20', '0,1,50', '-3,-2,17', '0,0.3,7', '0,1,20.37']
W4 = ['0,1,34,1156', '0,2,70,2500']

what = sys.argv[1]
if what == 'n3':
    for u in W3:
        go(3, u, None, None, 'list')
        go(3, u, None, None, 'max')
elif what == 'n3strata':
    for u in W3[:2]:
        for zs in (None, 0, 1, 2):
            for ws in (None, 0, 1, 2):
                if zs is None and ws is None:
                    continue
                go(3, u, zs, ws, 'list')
                go(3, u, zs, ws, 'max')
elif what == 'n3ctl':
    for u in ['0,0,0', '0,0,1', '0,1,1', '0,1,1.01', '0,1,1.5', '0,1,2', '0,1,2.37', '0,1,3', '0,1,10']:
        go(3, u, None, None, 'max')
elif what == 'n4':
    for u in W4:
        go(4, u, None, None, 'list', show=3)
        go(4, u, None, None, 'max', show=3)
elif what == 'n4strata':
    u = W4[0]
    for zs in (None, 0, 1, 2, 3):
        for ws in (None, 0, 1, 2, 3):
            if zs is None and ws is None:
                continue
            go(4, u, zs, ws, 'list')
            go(4, u, zs, ws, 'max')
elif what == 'n4ctl':
    for u in ['0,0,0,0', '0,1,2,3', '0,1,2.37,4.91', '0,1,30,900', '0,1,4,16']:
        go(4, u, None, None, 'max', show=2)
elif what == 'n2':
    go(2, '0,1', None, None, 'list')
    go(2, '0,1', None, None, 'max')
    for zs in (None, 0, 1):
        for ws in (None, 0, 1):
            if zs is None and ws is None:
                continue
            go(2, '0,1', zs, ws, 'list')
elif what == 'n3stratactl':
    # control of the search in a stratum: mass weights at which a stratum has points
    for u in ('0,0,0', '0,1,1'):
        for zs in (0, 1, 2):
            go(3, u, zs, None, 'list')
elif what == 'scale':
    # control: a free scale factor in the rows.  The system has a continuum, and Psi* is not bounded.
    for n, u in ((2, '0,1'), (3, '0,1,20'), (4, '0,1,34,1156')):
        t0 = time.time()
        found, nlp, nodd, npairs = L.run(n, [float(x) for x in u.split(',')], None, None, 'max', None, 4,
                                         None, True)
        L.report(n, u.split(','), None, None, 'max', None, found, nlp, nodd, npairs, time.time() - t0, 0)
elif what == 'n5':
    u = '0,1,52,2704,140608'
    t0 = time.time()
    found, nlp, nodd, npairs = L.run(5, [float(x) for x in u.split(',')], None, None, 'list', None, 4,
                                     (int(sys.argv[2]), int(sys.argv[3])))
    print('(sample of the ordered pairs of trees, seed %s)' % sys.argv[3])
    L.report(5, u.split(','), None, None, 'list', None, found, nlp, nodd, npairs, time.time() - t0, 3)
elif what == 'n4far':
    u = W4[0]
    for R in (748.0, 2780.0, 100000.0):
        go(4, u, None, None, 'far', R)
    go(4, u, None, None, 'far', 746.5)
    go(4, '0,0,0,0', None, None, 'far', 100000.0)
