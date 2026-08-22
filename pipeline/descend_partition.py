#!/usr/bin/env python3
"""THE PARTITION PIPELINE (p200). Run when label{1,2,3,4,5,7}-out-p200.m
have been decoded into this directory (label 6 exact values are built in).

Steps (reviewer-specified):
  1. parse p200 series (dps 220), Petri quadric, marked J_r per label
  2. descend: S_r(i) = J_r(i) + conj(J_r(kappa(i))), N_r likewise
  3. GATES: label-6 anchors vs exact rationals (S_1 = -8304/10237,
     N_1 = 2763/10237 + the other ten); Psi-coefficients real to ~1e-190
  4. orbit scan on descended values: singletons, pairs, triples (mc 1e40),
     sextic e_k (mc 1e90), algdep-6 per coordinate (reach ~1e57/coeff)
  5. on recognition: factor over Q (sympy), Galois group of the sextic,
     Frobenius cycle types mod good primes; split primes (-23/p)=+1
     sample A = rho(G_K) <= B, [B:A] <= 2
Receipt: partition-p200-receipt.json
"""
import sys, os, json, pickle
from mpmath import mp, mpf, mpc, pslq, fabs, nstr
sys.path.insert(0, '.')

mp.dps = 220
NUSE = 250
KAP = {1: 2, 2: 1, 3: 3, 4: 4, 5: 7, 6: 6, 7: 5}
LAB = [1, 2, 3, 4, 5, 6, 7]
STATE = 'descend_p200_state.pkl'

ANCHORS6 = {   # exact label-6 (S, N) per invariant r=1..6  (p100-derived)
 1: ((-8304, 10237), (2763, 10237)),
 2: ((-296454, 142129), (350901, 142129)),
 3: ((-32137795, 9428277), (1046734, 325113)),
 4: ((-44137861, 9428277), (5373134, 975339)),
 5: ((113993, 347217), (52491386, 1041651)),
 6: ((183063721, 91065858), (3613661, 3140202)),
}

def get_J(lab):
    import parse_series, canonical_curve
    parse_series.mp.dps = 220
    E = parse_series.get_basis(lab, path=f'label{lab}-out-p200.m')
    idx, q = canonical_curve.quadric(E)
    return dict(canonical_curve.invariants(idx, q))

def esym(vals):
    cs = [mpc(1)]
    for v in vals:
        new = [mpc(0)]*(len(cs)+1)
        for k, c in enumerate(cs):
            new[k] -= v*c; new[k+1] += c
        cs = new
    return cs[:-1]

def main():
    st = pickle.load(open(STATE, 'rb')) if os.path.exists(STATE) else dict(J={})
    todo = [l for l in LAB if l != 6 and l not in st['J']]
    if todo:
        lab = todo[0]
        st['J'][lab] = get_J(lab)
        pickle.dump(st, open(STATE, 'wb'))
        print(f"phase1 {lab} done ({len(st['J'])}/6)")
        return
    if 6 not in st['J']:
        st['J'][6] = get_J(6)   # from p100 file if p200 absent
        pickle.dump(st, open(STATE, 'wb'))

    rec = dict(gates={}, orbits={}, partition=None)
    names = ["J1", "J2", "J3", "J4", "J5", "J6"]
    SS, NN = {}, {}
    for name in names:
        J = {l: st['J'][l][name] for l in LAB}
        SS[name] = {i: J[i] + J[KAP[i]].conjugate() for i in LAB}
        NN[name] = {i: J[i] * J[KAP[i]].conjugate() for i in LAB}
    # gate: anchors
    okA = True
    for r, name in enumerate(names, 1):
        for tag, D, ex in (("S", SS[name], ANCHORS6[r][0]),
                           ("N", NN[name], ANCHORS6[r][1])):
            v = D[6].real
            err = fabs(v - mpf(ex[0])/ex[1])
            good = err < mpf('1e-150')
            okA = okA and good
            rec['gates'][f"{tag}{r}(6)"] = dict(err=float(err), ok=bool(good))
    print("ANCHOR GATE:", okA)
    # orbit scan on S1 (+ cross-check with S3, N1)
    for cname, D in (("S1", SS["J1"]), ("S3", SS["J3"]), ("N1", NN["J1"])):
        found = []
        import itertools
        for size in (1, 2, 3):
            for sub in itertools.combinations([1,2,3,4,5,7], size):
                cs = esym([D[l] for l in sub])
                ok = True
                for c in cs:
                    if fabs(c.imag) > mpf('1e-150'): ok = False; break
                    r_ = pslq([mpf(1), c.real], maxcoeff=10**40,
                              maxsteps=4*10**6)
                    if not r_: ok = False; break
                if ok: found.append(list(sub))
        cs = esym([D[l] for l in [1,2,3,4,5,7]])
        sex, sexcoeffs = True, []
        for c in cs:
            r_ = pslq([mpf(1), c.real], maxcoeff=10**90, maxsteps=10**7)
            if r_:
                sexcoeffs.append((-r_[0], r_[1]))
            else:
                sex = False; sexcoeffs.append(None)
        rec['orbits'][cname] = dict(proper_subsets=found,
                                    sextic_ok=sex, sextic=sexcoeffs)
        print(f"{cname}: proper K-subsets {found}  sextic-rational: {sex}")
        if sex:
            print("   sextic e_k:", sexcoeffs)
    json.dump(rec, open('partition-p200-receipt.json', 'w'), indent=1,
              default=str)
    print("receipt: partition-p200-receipt.json")
    # post-recognition (factor/Galois/Frobenius) runs interactively next.

main()
