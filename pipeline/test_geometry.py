#!/usr/bin/env python3
"""Receipt battery for geometry.py (label-6 triple, Delta(23,2,23)).

Receipts:
  COSETS_GATE_OK        sheet(alpha_i) = i for all 23 cosets
  RHO                   Gamma-FD radius; must match Delta-FD c-vertex radius
                        0.98128349 (reviewer's constant) -- Federalize rho
  GENUS_OK              Riemann-Hurwitz genus of the quotient = 4
  WORD_MATRIX_CONSISTENT word_matrix(word).z == loop point (order convention)
  GAMMA_MEMBERSHIP_OK   gamma = alpha_j^-1 delta acts trivially on sheet 0
  REDUCE_RADIUS_OK      reduced points inside radius rho
  AUTOMORPHY_IM_OK      Im(Mz) = Im(z)/|cz+d|^2 at the input point
  REDUCE_IDEMPOTENT_OK  reducing a reduced point is (near-)trivial
"""
import sys, json, random
sys.path.insert(0, '.'); sys.path.insert(0, '..')
from flint import acb
from geometry import (Triangle, coset_reps, reduce_to_gamma, fd_radius,
                      reduce_to_triangle, word_matrix, uhp_apply,
                      to_disc, to_uhp, word_perm, mm, ginv)
from hm_m23_v2 import parse_cycles

REVIEWER_RHO = 0.98128349

def load_label6():
    rep = json.load(open('../sandbox-report.json'))
    e6 = [e for e in rep['seven_census'] if e['label'] == 6][0]
    x, y, z = (parse_cycles(s) for s in e6['tuple'])
    # (23,2,23) ordering: order-23 vertex at the disc origin
    s0, s1 = y, mm(mm(ginv(y), x), y)
    sInf = ginv(mm(s0, s1))
    return s0, s1, sInf

def genus(s0, s1, sInf):
    def ncyc(p):
        n = len(p); seen = [False]*n; c = 0
        for i in range(n):
            if not seen[i]:
                c += 1; j = i
                while not seen[j]: seen[j] = True; j = p[j]
        return c
    d = len(s0)
    return 1 + (d - ncyc(s0) - ncyc(s1) - ncyc(sInf)) // 2

def main(prec_bits=300, T=40, seed=11):
    s0, s1, sInf = load_label6()
    g = genus(s0, s1, sInf)
    tri = Triangle(23, 2, 23, prec_bits=prec_bits)
    reps = coset_reps(s0, s1, tri=tri)
    gate = all(word_perm(r, s0, s1)[0] == i for i, r in enumerate(reps))
    rho = float(fd_radius(tri, reps).mid())
    def midr(w): return abs(complex(to_disc(w).mid()))
    random.seed(seed)
    okR = okG = okW = okC = okI = 0
    worst = 0.0
    for t in range(T):
        while True:
            wd = acb(random.uniform(-0.9, 0.9), random.uniform(-0.9, 0.9))
            if abs(complex(wd.mid())) < 0.88: break
        zz = to_uhp(wd)
        word, wp = reduce_to_triangle(tri, zz)
        okW += abs(complex((uhp_apply(word_matrix(tri, word), zz) - wp)
                           .mid())) < 1e-40
        M, zr, j, gword = reduce_to_gamma(tri, reps, s0, s1, zz)
        okG += word_perm(gword, s0, s1)[0] == 0
        r = midr(zr); worst = max(worst, r)
        okR += r <= rho + 1e-9
        czd = M[1, 0]*zz + M[1, 1]
        okC += float((zr.imag - zz.imag/(czd.real**2 + czd.imag**2))
                     .abs_upper()) < 1e-40
        w2, wp2 = reduce_to_triangle(tri, wp)
        okI += midr(wp2) <= midr(wp) + 1e-25
    rec = dict(
        prec_bits=prec_bits, T=T, seed=seed,
        COSETS_GATE_OK=gate,
        RHO=rho, RHO_MATCHES_REVIEWER=abs(rho - REVIEWER_RHO) < 5e-9,
        GENUS=g, GENUS_OK=(g == 4),
        WORD_MATRIX_CONSISTENT=f"{okW}/{T}",
        GAMMA_MEMBERSHIP_OK=f"{okG}/{T}",
        REDUCE_RADIUS_OK=f"{okR}/{T}", worst_reduced_radius=worst,
        AUTOMORPHY_IM_OK=f"{okC}/{T}",
        REDUCE_IDEMPOTENT_OK=f"{okI}/{T}",
        rep_word_lengths=sorted(len(r) for r in reps),
        PASS=bool(gate and g == 4 and okW == okG == okR == okC == okI == T
                  and abs(rho - REVIEWER_RHO) < 5e-9))
    json.dump(rec, open('geometry-receipt.json', 'w'), indent=1)
    for k, v in rec.items():
        print(f"{k}: {v}")
    assert rec["PASS"], "RECEIPTS FAILED"

if __name__ == '__main__':
    main()
