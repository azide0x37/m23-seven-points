#!/usr/bin/env python3
"""Parse a label's powser_arnoldi output (.m) at full precision, unscale,
echelonize; expose get_basis(label) -> list of 4 mpmath coefficient lists
(a_{j,n}, echelon: a_{j,i} = delta_{ji} for i,j < 4), truncated to NUSE.

Accuracy note: x_n known to ~1e-92 absolute; a_n = x_n * rho^-n loses
~0.0082n digits; at NUSE=250 that's ~2 digits -> a_n good to ~1e-89.
"""
import re, sys
from mpmath import mp, mpf, mpc, matrix, lu_solve

mp.dps = 110
NUSE = 250

RHO_STR = None

def rho_hi():
    """rho = c-vertex disc radius of Delta(23,2,23) at ~115 digits, taken
    from the RECEIPTED flint geometry stack (Triangle at 400 bits) and
    converted via decimal string -- no convention re-derivation."""
    global RHO_STR
    if RHO_STR is None:
        sys.path.insert(0, '.')
        from geometry import Triangle, to_disc, disc_abs
        from flint import arb
        tri = Triangle(23, 2, 23, prec_bits=400)
        r = arb(to_disc(tri.vc).abs_upper())     # tiny ball; take mid via str
        # use the midpoint of |D(vc)| computed exactly from mid values
        w = to_disc(tri.vc)
        m = (w.real**2 + w.imag**2).sqrt()
        RHO_STR = m.mid().str(115, radius=False)
    return mpf(RHO_STR)

NUMRE = re.compile(r'\[\s*(-?[0-9][0-9.]*(?:E-?\d+)?)p\d+\s*,\s*(-?[0-9][0-9.]*(?:E-?\d+)?)p\d+\s*\]')

def get_basis(label, nuse=NUSE, path=None):
    fn = path or f'label{label}-out-p100.m'
    txt = open(fn).read()
    blocks = txt.split('ComplexField(100) |')
    assert len(blocks) >= 5, f"unexpected .m structure ({len(blocks)} blocks)"
    rho = rho_hi()
    vecs = []
    for b in blocks[1:5]:
        pairs = NUMRE.findall(b)
        v = [mpc(mpf(rs), mpf(is_)) for rs, is_ in pairs[:nuse]]
        assert len(v) == nuse, f"vector too short: {len(v)}"
        vecs.append(v)
    # sanity: check the flint reference value of rho
    assert abs(rho - mpf('0.9812834897968066')) < mpf('1e-15')
    # unscale a_n = x_n * rho^-n
    rinv = [mp.power(rho, -n) for n in range(nuse)]
    A = [[vecs[j][i] * rinv[i] for i in range(nuse)] for j in range(4)]
    # echelonize over the first 4 coefficients
    M4 = matrix(4, 4)
    for j in range(4):
        for i in range(4):
            M4[j, i] = A[j][i]
    # rows of E = M4^-1 * A
    Minv = M4**-1
    E = [[sum(Minv[j, k] * A[k][i] for k in range(4)) for i in range(nuse)]
         for j in range(4)]
    for j in range(4):
        for i in range(4):
            tgt = 1 if i == j else 0
            assert abs(E[j][i] - tgt) < mpf('1e-80'), "echelon fail"
    return E

if __name__ == '__main__':
    lab = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    E = get_basis(lab)
    print(f"label {lab}: basis ok, {len(E[0])} coeffs at {mp.dps} dps")
    for j in range(4):
        print(f"  f{j}: a4..a7 =", [mp.nstr(E[j][i], 12) for i in range(4, 8)])
