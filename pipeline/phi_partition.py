#!/usr/bin/env python3
"""Assemble Phi_J(T) = prod(T - J_i) over the seven labels, PSLQ its
coefficients over K = Q(sqrt(-23)) (integrity gate: G_K-stability +
equivariance Prop force coefficients into K), then factor over K.
Phased: phase 1 computes+caches full-precision J values per label;
phase 2 assembles, recognizes, factors."""
import sys, os, pickle, json
from mpmath import mp, mpf, mpc, pslq, fabs, sqrt as msqrt, nstr
mp.dps = 110
STATE = 'phi_state.pkl'
LABELS = [1, 2, 3, 4, 5, 6, 7]

def compute_label(lab):
    from parse_series import get_basis
    from canonical_curve import quadric, invariants
    E = get_basis(lab)
    idx, q = quadric(E)
    return {name: v for name, v in invariants(idx, q)}

def main():
    st = pickle.load(open(STATE, 'rb')) if os.path.exists(STATE) else dict(done={})
    todo = [l for l in LABELS if l not in st['done']]
    if todo:
        lab = todo[0]
        st['done'][lab] = compute_label(lab)
        pickle.dump(st, open(STATE, 'wb'))
        print(f"phase1: label {lab} cached ({len(st['done'])}/7)")
        return
    # phase 2
    s23 = msqrt(mpf(23))
    out = {}
    for name in ["J1", "J2", "J3", "J4", "J5", "J6"]:
        vals = [st['done'][l][name] for l in LABELS]
        # distinctness (separation) check
        mind = min(fabs(vals[i]-vals[j]) for i in range(7) for j in range(i+1,7))
        # elementary symmetric -> coefficients of prod (T - v)
        coeffs = [mpc(1)]
        for v in vals:
            coeffs = [mpc(0)] + coeffs
            coeffs = [coeffs[k] - v*(coeffs[k+1] if k+1 < len(coeffs) else 0)
                      for k in range(len(coeffs)-1)] + [coeffs[-1]]
        # coeffs[k] = coefficient of T^k, degree 7 monic
        rec = []
        okall = True
        for k in range(7):
            c = coeffs[k]
            ra = pslq([mpf(1), c.real], maxcoeff=10**32, maxsteps=2*10**6)
            rb = pslq([mpf(1), c.imag/s23], maxcoeff=10**32, maxsteps=2*10**6)
            ok = bool(ra and rb and ra[1] and rb[1])
            okall = okall and ok
            rec.append(dict(k=k, re=(-ra[0], ra[1]) if ra else None,
                            im_s23=(-rb[0], rb[1]) if rb else None, ok=ok))
        out[name] = dict(min_separation=float(mind), coeffs=rec, PHI_IN_K=okall)
        print(f"{name}: min|Ji-Jj|={float(mind):.3e}  PHI_IN_K={okall}")
        if okall:
            for r in rec:
                print(f"   T^{r['k']}: {r['re']} + {r['im_s23']}*sqrt(-23)")
    json.dump(out, open('phi-coefficients-receipt.json', 'w'), indent=1)
    print("receipt: phi-coefficients-receipt.json")

main()
