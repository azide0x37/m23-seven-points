#!/usr/bin/env python3
"""Pure-python integer LLL + complex algdep at high precision."""
from fractions import Fraction
from mpmath import mp, mpf, mpc, fabs, nstr

def lll(B, delta=Fraction(3, 4)):
    """B: list of integer row-vectors. Returns LLL-reduced basis."""
    import copy
    B = [list(map(int, r)) for r in B]
    n = len(B)
    def dot(u, v): return sum(a*b for a, b in zip(u, v))
    def gso():
        Bs, mu = [], [[Fraction(0)]*n for _ in range(n)]
        for i in range(n):
            v = [Fraction(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = Fraction(dot(B[i], [x.numerator for x in Bs[j]]), 1) \
                    if False else sum(Fraction(a)*b for a, b in zip(B[i], Bs[j])) / dot2[j]
                v = [a - mu[i][j]*b for a, b in zip(v, Bs[j])]
            Bs.append(v)
            dot2.append(sum(a*a for a in v))
        return Bs, mu
    dot2 = []
    Bs, mu = gso()
    k = 1
    while k < n:
        for j in range(k-1, -1, -1):
            q = mu[k][j]
            r = int(q + Fraction(1, 2)) if q >= 0 else -int(-q + Fraction(1, 2))
            if r:
                B[k] = [a - r*b for a, b in zip(B[k], B[j])]
                dot2 = []; Bs, mu = gso()
        if dot2[k] >= (delta - mu[k][k-1]**2) * dot2[k-1]:
            k += 1
        else:
            B[k], B[k-1] = B[k-1], B[k]
            dot2 = []; Bs, mu = gso()
            k = max(k-1, 1)
    return B

def algdep_c(alpha, deg, prec_digits=85):
    """minimal integer polynomial (degree <= deg) of complex alpha."""
    C = 10**prec_digits
    pows = [mpc(1)]
    for _ in range(deg):
        pows.append(pows[-1]*alpha)
    rows = []
    for k in range(deg+1):
        rows.append([1 if i == k else 0 for i in range(deg+1)]
                    + [int(mp.nint(pows[k].real*C)), int(mp.nint(pows[k].imag*C))])
    R = lll(rows)
    best = None
    for r in R:
        c = r[:deg+1]
        if all(x == 0 for x in c): continue
        val = sum(c[k]*pows[k] for k in range(deg+1))
        if best is None or fabs(val) < best[0]:
            best = (fabs(val), c)
    return best
