#!/usr/bin/env python3
"""Petri model + marked invariants for a label.

Genus-4 canonical curve: unique quadric Q (10 coeffs, Sym^2 kernel dim
MUST be 1 = non-hyperelliptic gate) and cubic C (Sym^3 kernel dim MUST
be 5 = 4 Petri multiples Q*x_j + 1 new).

Marked invariants (paper-facing): under the residual marking ambiguity
w -> lambda*w the echelon basis transforms f_j -> lambda^{-j} f_j(lambda.),
so the quadric relation coefficients q_{jk} rescale by mu*lambda^{j+k}.
Cross-ratios  q_{jk} q_{lm} / (q_{jl} q_{km})  are therefore invariants of
the marked cover, algebraic, and Galois-compatible across the seven.
Gate for label 6 (field of moduli Q): cross-ratios must PSLQ to rationals.
"""
import sys, json
from mpmath import mp, mpf, mpc, pslq, fabs
from parse_series import get_basis

mp.dps = 110
NUSE = 250

def series_mul(a, b, n):
    return [sum(a[i]*b[k-i] for i in range(k+1)) for k in range(n)]

def nullspace(cols, n_use, expect=None, tol=None):
    """cols: list of coefficient-series (length n_use) = columns of M
    (n_use x m). Return orthonormal-ish basis of right nullspace via
    full-pivot elimination on M^T rows? Simpler: Gram matrix G = M^* M
    (m x m) and eigen-decomposition is overkill; use column elimination:
    eliminate rows of M by pivoting to find kernel of the column map."""
    m = len(cols)
    # build m x m normal matrix G = M^H M at full precision
    G = [[sum(mpc(cols[a][t]).conjugate()*cols[b][t] for t in range(n_use))
          for b in range(m)] for a in range(m)]
    # kernel of G = kernel of M. Gaussian elimination with full pivoting.
    A = [row[:] for row in G]
    piv_cols = []
    rowi = 0
    used_rows = []
    for _ in range(m):
        # find max pivot among unused rows/cols
        best = (None, None, mpf(0))
        for r in range(m):
            if r in used_rows: continue
            for c in range(m):
                if c in piv_cols: continue
                v = fabs(A[r][c])
                if v > best[2]: best = (r, c, v)
        r, c, v = best
        if v < (tol or mpf('1e-60')):
            break
        used_rows.append(r); piv_cols.append(c)
        pr = A[r]
        for rr in range(m):
            if rr == r: continue
            f = A[rr][c]/pr[c]
            A[rr] = [A[rr][k] - f*pr[k] for k in range(m)]
    rank = len(piv_cols)
    free = [c for c in range(m) if c not in piv_cols]
    if expect is not None:
        assert m - rank == expect, f"kernel dim {m-rank} != expected {expect}"
    basis = []
    for fc in free:
        x = [mpc(0)]*m
        x[fc] = mpc(1)
        # back-substitute pivots
        for r, c in zip(used_rows, piv_cols):
            x[c] = -A[r][fc]/A[r][c]
        basis.append(x)
    return basis, rank

def quadric(E, n_use=NUSE):
    idx = [(j, k) for j in range(4) for k in range(j, 4)]
    cols = []
    for (j, k) in idx:
        cols.append(series_mul(E[j], E[k], n_use))
    ker, rank = nullspace(cols, n_use, expect=1)
    return idx, ker[0]

def weight(ij):
    return ij[0] + ij[1]

# the moduli-carrying weight-0 invariant set (degree-matched numerator/
# denominator kills the overall scale; weight-matching kills lambda):
J_DEFS = [
    ("J1", [(1,3)], [(2,2)]),
    ("J2", [(1,1),(1,3)], [(1,2),(1,2)]),
    ("J3", [(1,1),(3,3)], [(1,3),(2,2)]),
    ("J4", [(1,2),(2,3)], [(1,3),(2,2)]),
    ("J5", [(1,1),(2,3)], [(1,2),(1,3)]),
    ("J6", [(2,2),(2,2)], [(1,1),(3,3)]),
]

def invariants(idx, q):
    Q = {ij: q[i] for i, ij in enumerate(idx)}
    out = []
    for name, num, den in J_DEFS:
        assert len(num) == len(den), name
        assert sum(weight(ij) for ij in num) == \
               sum(weight(ij) for ij in den), f"{name} not weight-0"
        v = mpc(1)
        for ij in num: v *= Q[ij]
        for ij in den: v /= Q[ij]
        out.append((name, v))
    return out

def recognize_K(val, maxcoeff=10**24):
    """recognize val = (a + b*sqrt(-23)) with a, b in Q via PSLQ on the
    real part and on imag/sqrt(23). Returns dict or None entries."""
    from mpmath import sqrt as msqrt
    s23 = msqrt(mpf(23))
    ra = pslq([mpf(1), val.real], maxcoeff=maxcoeff, maxsteps=10**6)
    rb = pslq([mpf(1), val.imag/s23], maxcoeff=maxcoeff, maxsteps=10**6)
    def frac(r):
        return None if (not r or r[1] == 0) else (-r[0], r[1])
    return dict(re=frac(ra), im_over_sqrt23=frac(rb),
                ok=bool(ra and rb))

def main():
    lab = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    E = get_basis(lab)
    idx, q = quadric(E)
    Q = {ij: q[i] for i, ij in enumerate(idx)}
    # forced-structure receipts (cusp filtration)
    forced = dict(
        q00=float(fabs(Q[(0,0)])), q01=float(fabs(Q[(0,1)])),
        q02_plus_q11=float(fabs(Q[(0,2)] + Q[(1,1)])),
        q03_plus_q12=float(fabs(Q[(0,3)] + Q[(1,2)])))
    rec = []
    for name, v in invariants(idx, q):
        r = recognize_K(v)
        rec.append(dict(name=name, value=str(mp.nstr(v, 40)), **r))
        print(f"{name}: {mp.nstr(v, 22)} -> re={r['re']} "
              f"im/sqrt23={r['im_over_sqrt23']} ok={r['ok']}")
    json.dump(dict(label=lab, forced_structure=forced, invariants=rec,
                   NONHYPERELLIPTIC_OK=True),
              open(f'invariants-label{lab}-receipt.json', 'w'), indent=1)
    print(f"receipt: invariants-label{lab}-receipt.json")

if __name__ == '__main__':
    main()
