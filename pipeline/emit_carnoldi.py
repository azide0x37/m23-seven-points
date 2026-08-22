#!/usr/bin/env python3
"""Emit the CArnoldi (powser_arnoldi) input file for the label-6 M23 cover,
transcribing the Al eq "CArnoldi" writer of powser_iter_arfed.m exactly.

Case facts (all asserted, not assumed):
  Delta = (23,2,23), s0 = 23A (single 23-cycle) => nv = 1, es = [1], ss = [0]
  k = 2, genus = 4 => dim = fulldim = 4, skipcoeffs = [], shifts = [0]
  Federalize rho = Delta-FD radius = c-vertex radius = 0.98128349...
  nv = 1 => permutation block = identity (slot j=0 <-> m=Q)

File layout (verbatim from the writer):
  header:  prec epsdigs cmaxiter dim nv Q 1
  center:  NN e (e*shift mod Q) Ptot          [one line, = "N+1 1 0 Q"]
  points:  Re(xpt) Im(xpt) Re(vnd) Im(vnd)    [Q lines; xpt=wp, vnd=(1-wp*rho)^2]
  Jweights:Re Im                              [Q lines, j=0..Q-1, m=(j==0?Q:j),
                                               jAut^-k / (1-u_m*rho)^k, u_m=e^(2pi i m/Q)]
  perm:    m                                  [Q lines, identity]
  start:   Re Im                              [dim*NN lines, rho-power ramps with
                                               first-dim-slot masking]

Usage: python3 emit_carnoldi.py PREC [CHUNK]   (chunked; state in emit-state-p{PREC}.pkl)
"""
import sys, json, math, pickle, os
sys.path.insert(0, '.'); sys.path.insert(0, '..')
from flint import acb, arb, ctx
from geometry import (Triangle, coset_reps, reduce_to_gamma, fd_radius,
                      to_disc, to_uhp, word_perm, mm, ginv, disc_abs)
from test_geometry import load_label6, genus

K = 2

def fmt(x, digits):
    """Magma-like decimal print of an arb midpoint."""
    s = arb(x.mid()).str(digits, radius=False)
    return s

def main():
    prec = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 900
    prec_bits = max(int(prec * 3.33) + 40, 128)
    statef = f"emit-state-p{prec}.pkl"

    s0, s1, sInf = load_label6()
    g = genus(s0, s1, sInf)
    assert g == 4, "genus gate"
    dim = g

    tri = Triangle(23, 2, 23, prec_bits=prec_bits)
    # Federalize rho = Delta-FD radius (identity translate); assert it agrees
    # with the Gamma-FD radius of our greedy reps (both = c-vertex radius).
    delta_rho = max((disc_abs(to_disc(v)) for v in tri.verts_uhp),
                    key=lambda r: float(r.mid()))
    reps = coset_reps(s0, s1, tri=tri)
    gam_rho = fd_radius(tri, reps)
    assert abs(float(delta_rho.mid()) - float(gam_rho.mid())) < 1e-12
    rho = arb(delta_rho.mid())
    lnrho = float(rho.log().mid())

    N = math.ceil(prec * math.log(10) / (-lnrho))
    Q = N + 2 * math.ceil(math.log(N))
    NN = N + 1                                   # (N+1) div 1 - 0 skipcoeffs
    epsdigs = prec - 2 * math.floor(math.log(prec))
    cmaxiter = 50 + 3 * prec
    eps_thresh = 10.0 ** (-prec + 2 * math.floor(math.log(prec)))

    # sanity: s0 single 23-cycle => nv=1
    def ncyc(p):
        n=len(p); seen=[False]*n; c=0
        for i in range(n):
            if not seen[i]:
                c+=1; j=i
                while not seen[j]: seen[j]=True; j=p[j]
        return c
    assert ncyc(s0) == 1, "nv=1 gate (s0 must be a 23-cycle)"

    st = dict(done=0, ptlines=[], jw=[None]*(Q+1), maxwp=0.0)
    if os.path.exists(statef):
        st = pickle.load(open(statef, 'rb'))
        assert len(st['jw']) == Q+1, "state/param mismatch"
    twopi = 2 * arb.pi()
    m0, m1 = st['done'] + 1, min(st['done'] + chunk, Q)
    for m in range(m0, m1 + 1):
        ang = twopi * m / Q
        u = acb(ang.cos(), ang.sin())            # e^(2 pi i m / Q)
        w0 = u * rho                             # disc circle point
        zz = to_uhp(w0)
        M, zr, j, gword = reduce_to_gamma(tri, reps, s0, s1, zz)
        wpm = to_disc(zr)
        awp = float(disc_abs(wpm).mid())
        assert awp <= float(rho.mid()) + eps_thresh, \
            f"point m={m} radius {awp} exceeds rho"
        st['maxwp'] = max(st['maxwp'], awp)
        wp = wpm / rho                           # adjust with factor rho
        xpt = wp                                 # ^es=1
        vnd = (1 - wp * rho) ** K                # ss=0, shift=0
        st['ptlines'].append(
            f"{fmt(xpt.real,prec)} {fmt(xpt.imag,prec)} "
            f"{fmt(vnd.real,prec)} {fmt(vnd.imag,prec)}")
        jAut = M[1, 0] * zz + M[1, 1]
        jw = jAut ** (-K) / (1 - u * rho) ** K   # / u^ss, ss=0
        st['jw'][m] = (fmt(jw.real, prec), fmt(jw.imag, prec))
        st['done'] = m
    pickle.dump(st, open(statef, 'wb'))
    print(f"points {st['done']}/{Q} done (maxwp {st['maxwp']:.12f})")
    if st['done'] < Q:
        print("RESUME: rerun to continue"); return

    # ---- assemble
    out = [f"{prec} {epsdigs} {cmaxiter} {dim} 1 {Q} 1",
           f"{NN} 1 0 {Q}"]
    out += st['ptlines']
    for j in range(Q):                           # J-weights, slot j=0 <-> m=Q
        m = Q if j == 0 else j
        out.append(f"{st['jw'][m][0]} {st['jw'][m][1]}")
    for j in range(Q):                           # identity permutation
        out.append(str(Q if j == 0 else j))
    rpow = [arb(1)]                              # start vectors
    for n in range(1, NN):
        rpow.append(rpow[-1] * rho)
    for dim_cnt in range(1, dim + 1):
        for n in range(NN):
            v = rpow[n]
            if n < dim and (n + 1) != dim_cnt:   # q1[jdim]=0 for jdim!=dim_cnt
                v = arb(0)
            out.append(f"{fmt(acb(v).real, prec)} 0")
    fn = f"label6-carnoldi-p{prec}.txt"
    with open(fn, 'w') as f:
        f.write("\n".join(out) + "\n")
    exp_lines = 2 + Q + Q + Q + dim * NN
    rec = dict(prec=prec, prec_bits=prec_bits, k=K, dim=dim, nv=1,
               N=N, Q=Q, NN=NN, epsdigs=epsdigs, cmaxiter=cmaxiter,
               rho=float(rho.mid()), maxwp=st['maxwp'],
               MAXWP_LE_RHO=bool(st['maxwp'] <= float(rho.mid()) + eps_thresh),
               n_lines=len(out), n_lines_expected=exp_lines,
               LINES_OK=(len(out) == exp_lines), outfile=fn,
               PASS=bool(len(out) == exp_lines
                         and st['maxwp'] <= float(rho.mid()) + eps_thresh))
    json.dump(rec, open(f"emit-receipt-p{prec}.json", 'w'), indent=1)
    print(json.dumps(rec, indent=1))
    assert rec["PASS"]

if __name__ == '__main__':
    main()
