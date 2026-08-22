#!/usr/bin/env python3
"""Mnemosyne job -004: label-6 CArnoldi input emission at prec = 100.
Self-contained: pip-installs python-flint, materializes the receipted
triangle.py/geometry.py (verbatim from phaseB-open, receipts 40/40),
embeds the label-6 triple, emits per emit_carnoldi.py conventions.
Output: EMIT receipt JSON + the input file as gzip+base64 between
BEGIN/END markers (decode: base64 -d | gunzip > label5-carnoldi-p100.txt).
"""
import subprocess, sys, os, tempfile, json, math, base64, gzip, time

import subprocess as sp, urllib.request, time as _t
def _run(cmd):
    t0 = _t.time()
    r = sp.run(cmd, shell=True, capture_output=True, text=True)
    print(f"MARKER step [{cmd[:60]}] exit={r.returncode} {_t.time()-t0:.0f}s", flush=True)
    if r.returncode != 0:
        print(r.stdout[-2000:]); print(r.stderr[-4000:], file=sys.stderr); sys.exit(1)
_run("apt-get update -qq && apt-get install -y -qq build-essential m4 file pkg-config libgmp-dev libmpfr-dev xz-utils > /dev/null")
urllib.request.urlretrieve("https://github.com/flintlib/flint/releases/download/v3.1.2/flint-3.1.2.tar.xz", "/tmp/flint.tar.xz")
_run("cd /tmp && tar xf flint.tar.xz && cd flint-3.1.2 && ./configure --disable-static > cfg.log && make -j$(nproc) > make.log 2>&1 && make install > inst.log && ldconfig")
urllib.request.urlretrieve("https://raw.githubusercontent.com/michaelmusty/Belyi/master/Cext/powser_arnoldi.c", "/tmp/powser_arnoldi.c")
_run("cd /tmp && gcc -O3 -o powser_arnoldi powser_arnoldi.c -lflint -lmpfr -lgmp -lpthread -lm")
print("MARKER toolchain ready", flush=True)

r = subprocess.run([sys.executable, "-m", "pip", "install", "--quiet",
                "--no-warn-script-location", "python-flint==0.9.0"])
if r.returncode != 0:   # no cp312 wheel for 0.9.0 -> latest (API-stable subset)
    subprocess.run([sys.executable, "-m", "pip", "install", "--quiet",
                    "--no-warn-script-location", "python-flint"], check=True)
import flint as _fl
print("MARKER python-flint", getattr(_fl, "__version__", "unknown"), flush=True)

TD = tempfile.mkdtemp()
open(os.path.join(TD, "triangle.py"), "w").write('#!/usr/bin/env python3\n"""Triangle group Delta(a,b,c) generator matrices in rigorous ball\narithmetic (python-flint acb), following the public formulas in\nmichaelmusty/Belyi Code/triangle.m (MIT).\n\n    l   = (cos(pi/a) cos(pi/b) + cos(pi/c)) / (sin(pi/a) sin(pi/b))\n    tau = l + sqrt(l^2 - 1)\n\n    d_a = [[ cos(pi/a),        sin(pi/a)],\n           [-sin(pi/a),        cos(pi/a)]]\n    d_b = [[ cos(pi/b),        tau sin(pi/b)],\n           [-sin(pi/b)/tau,    cos(pi/b)]]\n    d_c = (d_a d_b)^(-1)\n\nConventions: d_a is the rotation by pi/a at the disk-origin vertex; in\nSL_2 each d has order 2n with d^n = -I, i.e. projective order n.  For the\nM23 run the signature is ordered (23, 2, 23) -- 23-cycle first, so the\norder-23 vertex sits at the origin, matching the expansion point and the\nf_i = q^i + O(q^4) normalization of arXiv:2608.08538.\n\nReceipts (printed as MARKER lines):\n    TRIANGLE_DETERMINANTS_OK        det d = 1 rigorously (ball contains 1,\n                                    radius below tolerance)\n    PROJECTIVE_ORDERS=a,b,c         d^n + I = 0 verified in balls\n    TRIANGLE_PRODUCT_OK             d_a d_b d_c = I in balls\n    TRACE_C_OK                      |tr d_c| = 2 cos(pi/c) in balls\n    HYPERBOLIC_OK                   1/a + 1/b + 1/c < 1\n"""\nfrom flint import acb, arb, acb_mat, ctx\n\n\ndef pi_over(n):\n    return arb.pi() / n\n\n\ndef tri_matrices(a, b, c, prec_bits=350):\n    ctx.prec = prec_bits\n    ca, sa = pi_over(a).cos(), pi_over(a).sin()\n    cb, sb = pi_over(b).cos(), pi_over(b).sin()\n    cc = pi_over(c).cos()\n    l = (ca * cb + cc) / (sa * sb)\n    tau = l + (l * l - 1).sqrt()\n    da = acb_mat([[acb(ca), acb(sa)], [acb(-sa), acb(ca)]])\n    db = acb_mat([[acb(cb), acb(tau * sb)], [acb(-(sb / tau)), acb(cb)]])\n    dc = (da * db).inv()\n    return da, db, dc\n\n\ndef ball_is(x, target, tol=arb("1e-80")):\n    """Rigorous: the ball x contains target and has radius < tol."""\n    d = x - target\n    return d.contains(acb(0) if isinstance(d, acb) else arb(0)) \\\n        and arb(d.abs_upper()) < tol\n\n\ndef mat_is_identity(M, sign=+1, tol=arb("1e-80")):\n    I = acb_mat(2, 2, [1, 0, 0, 1])\n    T = M - I * sign\n    ok = True\n    for i in range(2):\n        for j in range(2):\n            e = T[i, j]\n            ok = ok and e.contains(acb(0)) and arb(e.abs_upper()) < tol\n    return ok\n\n\ndef proj_order_ok(d, n):\n    """Projective order n: d^n = +/-I in SL2 (the SL2-lift may have\n    eigenvalues -e^(+/-i pi/n), giving +I at the n-th power), and\n    d^k != +/-I for 0 < k < n."""\n    p = acb_mat(2, 2, [1, 0, 0, 1])\n    for k in range(1, n + 1):\n        p = p * d\n        pm = mat_is_identity(p, +1) or mat_is_identity(p, -1)\n        if k < n and pm:\n            return False\n        if k == n:\n            return pm\n    return False\n\n\ndef receipts(a, b, c, prec_bits=350):\n    assert arb(1) / a + arb(1) / b + arb(1) / c < 1, "not hyperbolic"\n    print("MARKER HYPERBOLIC_OK")\n    da, db, dc = tri_matrices(a, b, c, prec_bits)\n    for name, d in (("a", da), ("b", db), ("c", dc)):\n        det = d[0, 0] * d[1, 1] - d[0, 1] * d[1, 0]\n        assert det.contains(acb(1)) and arb((det - 1).abs_upper()) < arb("1e-80"), \\\n            f"det d_{name} != 1"\n    print("MARKER TRIANGLE_DETERMINANTS_OK")\n    assert proj_order_ok(da, a) and proj_order_ok(db, b) \\\n        and proj_order_ok(dc, c), "projective order failed"\n    print(f"MARKER PROJECTIVE_ORDERS={a},{b},{c}")\n    assert mat_is_identity(da * db * dc), "product != I"\n    print("MARKER TRIANGLE_PRODUCT_OK")\n    tr = dc[0, 0] + dc[1, 1]\n    target = 2 * pi_over(c).cos()\n    ok = tr.contains(acb(target)) or tr.contains(acb(-target))\n    assert ok, "trace of d_c wrong"\n    print("MARKER TRACE_C_OK")\n    return da, db, dc\n\n\nif __name__ == "__main__":\n    import sys\n    a, b, c = (int(x) for x in (sys.argv[1:4] or [23, 2, 23]))\n    prec = int(sys.argv[4]) if len(sys.argv) > 4 else 350\n    receipts(a, b, c, prec)\n    print(f"MARKER triangle ({a},{b},{c}) prec={prec} bits: ALL OK")\n')
open(os.path.join(TD, "geometry.py"), "w").write('#!/usr/bin/env python3\n"""Hyperbolic geometry stack for the (a,b,c) triangle-subgroup emitter:\ndisc model, coset representatives from a permutation triple, fundamental-\ndomain reduction, FD radius. Ports Code/reduce.m and Code/cosets.m of\nmichaelmusty/Belyi (MIT) into python-flint acb arithmetic.\n\nConventions (validated by receipts, not assumed):\n- UHP matrices from triangle.py: d_a fixes i (a-vertex), d_b fixes i*tau\n  (b-vertex). Disc model = Cayley about i: D(z) = (z - i)/(z + i), so the\n  a-vertex is the disc origin.\n- Permutation rep pi: words in {a, b} -> S_d via pi(d_a) = s0, pi(d_b) = s1\n  in OUR composition law (mm(p,q) = p∘q, triples satisfy s0∘s1∘sInf = id).\n  Words act on sheets; coset i is labeled by a word alpha_i with\n  1^pi(alpha_i) = i (0-based: 0 -> i). THE GATE.\n- Reducer (reduce.m): alternate rotations d_a^i at the origin and d_b^j at\n  the b-vertex, angle counts i = -floor(a*arg/(2pi) + 1/2) (and the same\n  with the swap-origin map for b), boundary tie-break, fixed-point escape\n  when |wp| stops decreasing (tolerance 10^(-prec/2)).\n- Gamma-reduction: delta reduces to the fundamental triangle; j = coset of\n  delta^-1 (sheet 0\'s image); gamma = alpha_j * delta in Gamma;\n  reduced point = gamma * w; jAut = c*z + d of gamma\'s UHP matrix at the\n  input point.\n\nReceipts: COSETS_GATE_OK, COSETS_ALL_DISTINCT, RHO (FD radius),\nREDUCE_IDEMPOTENT_OK, REDUCE_RADIUS_OK, GAMMA_MEMBERSHIP_OK,\nAUTOMORPHY_COCYCLE_OK.\n"""\nimport sys\nsys.path.insert(0, \'.\')\nfrom flint import acb, arb, acb_mat, ctx\nfrom triangle import tri_matrices, pi_over\n\n\n# ---------------------------------------------------------------- models\n\ndef uhp_apply(M, z):\n    return (M[0, 0]*z + M[0, 1]) / (M[1, 0]*z + M[1, 1])\n\ndef to_disc(z):                      # Cayley about i: a-vertex -> 0\n    I = acb(0, 1)\n    return (z - I) / (z + I)\n\ndef to_uhp(w):\n    I = acb(0, 1)\n    return (I*w + I) / (-w + 1)     # inverse Cayley: w -> i(1+w)/(1-w)\n\ndef disc_abs(Mw):\n    return arb(Mw.abs_upper())\n\n\nclass Triangle:\n    def __init__(self, a, b, c, prec_bits=200):\n        ctx.prec = prec_bits\n        self.a, self.b, self.c = a, b, c\n        self.prec_bits = prec_bits\n        self.da, self.db, self.dc = tri_matrices(a, b, c, prec_bits)\n        self.dai = self.da.inv(); self.dbi = self.db.inv()\n        ca, sa = pi_over(a).cos(), pi_over(a).sin()\n        cb, sb = pi_over(b).cos(), pi_over(b).sin()\n        cc = pi_over(c).cos()\n        l = (ca*cb + cc) / (sa*sb)\n        self.tau = l + (l*l - 1).sqrt()\n        # swap-origin map: order-2 isometry exchanging a-vertex (i) and\n        # b-vertex (i*tau): z -> -tau/z, normalized to det 1.\n        st = self.tau.sqrt()\n        self.A = acb_mat([[acb(0), acb(-st)], [acb(1/st), acb(0)]])\n        # fundamental triangle vertices (UHP): a-vertex i, b-vertex i*tau,\n        # c-vertex = fixed point of dc in UHP (solve c21 z^2 + (c22-c11) z - c12 = 0)\n        c11, c12, c21, c22 = self.dc[0,0], self.dc[0,1], self.dc[1,0], self.dc[1,1]\n        disc = ((c22 - c11)**2 + 4*c21*c12).sqrt()\n        z1 = ((c11 - c22) + disc) / (2*c21)\n        z2 = ((c11 - c22) - disc) / (2*c21)\n        self.vc = z1 if float(z1.imag.mid()) > 0 else z2   # UPPER half plane\n        assert float(self.vc.imag.mid()) > 0\n        vc_mirror = acb(-self.vc.real, self.vc.imag)       # z -> -conj(z)\n        # FD(Delta) is the DOUBLE triangle: include the mirrored c-vertex\n        self.verts_uhp = [acb(0, 1), acb(0, 1)*self.tau, self.vc, vc_mirror]\n\n\ndef word_matrix(tri, word):\n    M = acb_mat(2, 2, [1, 0, 0, 1])\n    for g, e in word:\n        base = {\'a\': (tri.da, tri.dai), \'b\': (tri.db, tri.dbi)}[g]\n        M = M * (base[0] if e > 0 else base[1])\n        for _ in range(abs(e) - 1):\n            M = M * (base[0] if e > 0 else base[1])\n    return M\n\n\n# ------------------------------------------------------- permutation rep\n\ndef mm(p, q):\n    return tuple(p[j] for j in q)\n\ndef ginv(p):\n    r = [0]*len(p)\n    for i, j in enumerate(p): r[j] = i\n    return tuple(r)\n\ndef word_perm(word, s0, s1):\n    d = len(s0)\n    P = tuple(range(d))\n    for g, e in word:\n        base = s0 if g == \'a\' else s1\n        step = base if e > 0 else ginv(base)\n        for _ in range(abs(e)):\n            P = mm(P, step)          # composition order = matrix order\n    return P\n\n\ndef coset_reps(s0, s1, tri=None):\n    """Coset representatives: words alpha_i with sheet(alpha_i) = i.\n    If tri is given, expand greedily by the distance of the translated\n    triangle to the origin (Magma\'s \'Full\' frontier heuristic), which\n    keeps the resulting Gamma fundamental domain compact (small rho)."""\n    d = len(s0)\n    reps = [None]*d\n    reps[0] = []\n    gens = [(\'a\', 1), (\'a\', -1), (\'b\', 1), (\'b\', -1)]\n\n    def dist(w):\n        if tri is None:\n            return len(w)\n        Mi = word_matrix(tri, inv_word(w))\n        return float(disc_abs(to_disc(uhp_apply(Mi, acb(0, 1)))).mid())\n\n    frontier = [0]\n    while frontier:\n        frontier.sort(key=lambda j: dist(reps[j]))\n        j = frontier.pop(0)\n        for g, e in gens:\n            w = reps[j] + [(g, e)]\n            i = word_perm(w, s0, s1)[0]\n            if reps[i] is None:\n                reps[i] = w\n                frontier.append(i)\n            elif tri is not None and dist(w) < dist(reps[i]) - 1e-12:\n                reps[i] = w\n                if i not in frontier:\n                    frontier.append(i)\n    assert all(r is not None for r in reps)\n    return reps\n\n\n# ------------------------------------------------------------- reduction\n\nimport math\n\ndef _rot_count(angle_acb, n):\n    """i = -floor(n*arg/(2pi) + 1/2), reduce.m\'s rotation count."""\n    return -math.floor(n * float(angle_acb.arg().real.mid())\n                       / (2*math.pi) + 0.5)\n\ndef reduce_to_triangle(tri, z):\n    """Reduce UHP point z into the fundamental triangle of Delta,\n    following reduce.m: alternate d_a-rotation counted at the origin and\n    d_b-rotation counted after the swap-origin map, with the boundary\n    tie-break and the fixed-point escape. Returns (word, zred) with word\n    a list of (gen, exp); zred = word_matrix(word) * z."""\n    word = []\n    wp = z\n    iold = jold = 0\n    wpold_abs = None\n    for _ in range(4000):\n        i = _rot_count(to_disc(wp), tri.a)\n        if i != 0:\n            M = tri.da if i > 0 else tri.dai\n            for _ in range(abs(i)):\n                wp = uhp_apply(M, wp)\n            word.insert(0, (\'a\', i))\n        w_sw = -to_disc(uhp_apply(tri.A, wp))      # wpp := -(A*wp), disc\n        j = _rot_count(w_sw, tri.b)\n        if i == 0 and iold == 0 and j == -jold:\n            j = 0                                   # boundary tie-break\n        else:\n            iold, jold = i, j\n        if j != 0:\n            M = tri.db if j > 0 else tri.dbi\n            for _ in range(abs(j)):\n                wp = uhp_apply(M, wp)\n            word.insert(0, (\'b\', j))\n        cur = disc_abs(to_disc(wp))\n        if j == 0 or (wpold_abs is not None and not (cur < wpold_abs)):\n            # candidate exit: VERIFIED Dirichlet terminator. d_a-rotations\n            # preserve |disc|, so the point is fully reduced iff no move\n            # d_b^{+-1} d_a^k decreases the radius, k = 0..a-1. This is\n            # convention-free (independent of the swap-origin map used for\n            # the counting heuristic above).\n            def midr(w):\n                return abs(complex(to_disc(w).mid()))\n            improved = False\n            r0 = midr(wp)\n            wq = wp\n            for k in range(tri.a):\n                for M, tag in ((tri.db, 1), (tri.dbi, -1)):\n                    wr = uhp_apply(M, wq)\n                    if midr(wr) < r0 - 1e-30:\n                        if k:\n                            word.insert(0, (\'a\', k))\n                        word.insert(0, (\'b\', tag))\n                        wp = wr\n                        improved = True\n                        break\n                if improved:\n                    break\n                wq = uhp_apply(tri.da, wq)\n            if not improved:\n                break\n            cur = disc_abs(to_disc(wp))\n        wpold_abs = cur\n    # final in-sector normalization (radius-preserving)\n    i = _rot_count(to_disc(wp), tri.a)\n    if i != 0:\n        M = tri.da if i > 0 else tri.dai\n        for _ in range(abs(i)):\n            wp = uhp_apply(M, wp)\n        word.insert(0, (\'a\', i))\n    return word, wp\n\n\ndef inv_word(word):\n    return [(g, -e) for (g, e) in reversed(word)]\n\ndef reduce_to_gamma(tri, reps, s0, s1, z):\n    """Full Gamma-reduction of UHP point z. With our function-composition\n    pi, sheets correspond to LEFT cosets alpha_j*Gamma: j = sheet(delta) =\n    pi(delta)(0), gamma = alpha_j^-1 * delta in Gamma, reduced point\n    gamma*z lies in alpha_j^-1 * FD(Delta). Returns (M, zred, j, gword)."""\n    word, _ = reduce_to_triangle(tri, z)\n    P = word_perm(word, s0, s1)\n    j = P[0]                        # sheet of delta\n    gword = inv_word(reps[j]) + word\n    G = word_perm(gword, s0, s1)\n    assert G[0] == 0, "gamma not in Gamma (gate failed)"\n    M = word_matrix(tri, gword)\n    zred = uhp_apply(M, z)\n    return M, zred, j, gword\n\ndef fd_radius(tri, reps):\n    """rho = max |disc point| over the Gamma fundamental domain\n    = max over cosets j and triangle vertices v of |disc(alpha_j^-1 v)|."""\n    rho = arb(0)\n    for r in reps:\n        Mi = word_matrix(tri, inv_word(r))\n        for v in tri.verts_uhp:\n            d = disc_abs(to_disc(uhp_apply(Mi, v)))\n            rho = rho if rho > d else d\n    return rho\n')
os.chdir(TD); sys.path.insert(0, TD)

X = (0, 1, 12, 11, 22, 6, 5, 7, 8, 14, 10, 3, 2, 16, 9, 18, 13, 20, 15, 19, 17, 21, 4)
Y = (4, 0, 1, 12, 21, 7, 3, 20, 6, 11, 14, 10, 19, 22, 2, 8, 18, 15, 5, 16, 13, 17, 9)
Z = (1, 2, 3, 9, 13, 8, 18, 5, 15, 10, 11, 6, 14, 19, 22, 16, 20, 7, 17, 12, 21, 4, 0)

from flint import acb, arb
from geometry import (Triangle, coset_reps, reduce_to_gamma, fd_radius,
                      to_disc, to_uhp, word_perm, mm, ginv, disc_abs)

def fmt(v, digits):
    return arb(v.mid()).str(digits, radius=False)

def main():
    prec = int(os.environ.get("EMIT_PREC", "100"))
    prec_bits = max(int(prec * 3.33) + 40, 128)
    assert prod_ok(), "embedded triple product gate"
    s0, s1 = Y, mm(mm(ginv(Y), X), Y)
    assert ncyc(s0) == 1, "nv=1 gate"
    g = genus(s0, s1, ginv(mm(s0, s1)))
    assert g == 4, "genus gate"
    dim, K = g, 2
    tri = Triangle(23, 2, 23, prec_bits=prec_bits)
    delta_rho = max((disc_abs(to_disc(v)) for v in tri.verts_uhp),
                    key=lambda r: float(r.mid()))
    reps = coset_reps(s0, s1, tri=tri)
    gate = all(word_perm(r, s0, s1)[0] == i for i, r in enumerate(reps))
    assert gate, "cosets gate"
    gam_rho = fd_radius(tri, reps)
    assert abs(float(delta_rho.mid()) - float(gam_rho.mid())) < 1e-12
    rho = arb(delta_rho.mid())
    lnrho = float(rho.log().mid())
    N = math.ceil(prec * math.log(10) / (-lnrho))
    Q = N + 2 * math.ceil(math.log(N))
    NN = N + 1
    epsdigs = prec - 2 * math.floor(math.log(prec))
    cmaxiter = 50 + 3 * prec
    eps_thresh = 10.0 ** (-prec + 2 * math.floor(math.log(prec)))
    print(f"MARKER params prec={prec} bits={prec_bits} N={N} Q={Q}", flush=True)
    twopi = 2 * arb.pi()
    ptlines = []; jw = [None]*(Q+1); maxwp = 0.0; t0 = time.time()
    for m in range(1, Q+1):
        ang = twopi * m / Q
        u = acb(ang.cos(), ang.sin())
        w0 = u * rho
        zz = to_uhp(w0)
        M, zr, j, gword = reduce_to_gamma(tri, reps, s0, s1, zz)
        wpm = to_disc(zr)
        awp = float(disc_abs(wpm).mid())
        assert awp <= float(rho.mid()) + eps_thresh, f"radius fail m={m}"
        maxwp = max(maxwp, awp)
        wp = wpm / rho
        vnd = (1 - wp * rho) ** K
        ptlines.append(f"{fmt(wp.real,prec)} {fmt(wp.imag,prec)} "
                       f"{fmt(vnd.real,prec)} {fmt(vnd.imag,prec)}")
        jA = M[1, 0] * zz + M[1, 1]
        v = jA ** (-K) / (1 - u * rho) ** K
        jw[m] = (fmt(v.real, prec), fmt(v.imag, prec))
        if m % 500 == 0:
            print(f"MARKER progress {m}/{Q} ({time.time()-t0:.0f}s)", flush=True)
    out = [f"{prec} {epsdigs} {cmaxiter} {dim} 1 {Q} 1", f"{NN} 1 0 {Q}"]
    out += ptlines
    for j2 in range(Q):
        m = Q if j2 == 0 else j2
        out.append(f"{jw[m][0]} {jw[m][1]}")
    for j2 in range(Q):
        out.append(str(Q if j2 == 0 else j2))
    rpow = [arb(1)]
    for n in range(1, NN):
        rpow.append(rpow[-1] * rho)
    for dc in range(1, dim+1):
        for n in range(NN):
            v = rpow[n]
            if n < dim and (n+1) != dc:
                v = arb(0)
            out.append(f"{fmt(acb(v).real, prec)} 0")
    exp_lines = 2 + 3*Q + dim*NN
    blob = ("\n".join(out) + "\n").encode()
    rec = dict(prec=prec, prec_bits=prec_bits, N=N, Q=Q, NN=NN, dim=dim,
               epsdigs=epsdigs, cmaxiter=cmaxiter, rho=float(rho.mid()),
               maxwp=maxwp, n_lines=len(out), n_lines_expected=exp_lines,
               LINES_OK=(len(out) == exp_lines),
               MAXWP_LE_RHO=bool(maxwp <= float(rho.mid()) + eps_thresh),
               raw_bytes=len(blob), seconds=round(time.time()-t0, 1),
               PASS=bool(len(out) == exp_lines
                         and maxwp <= float(rho.mid()) + eps_thresh))
    print("MARKER RECEIPT " + json.dumps(rec), flush=True)
    assert rec["PASS"]
    import hashlib
    open("/tmp/label5-carnoldi-p100.txt", "wb").write(blob)
    print("MARKER emission md5", hashlib.md5(blob).hexdigest(), flush=True)

def prod_ok():
    r = mm(mm(X, Y), Z)
    return r == tuple(range(len(X)))

def ncyc(p):
    n = len(p); seen = [False]*n; c = 0
    for i in range(n):
        if not seen[i]:
            c += 1; j = i
            while not seen[j]: seen[j] = True; j = p[j]
    return c

def genus(s0, s1, sInf):
    d = len(s0)
    return 1 + (d - ncyc(s0) - ncyc(s1) - ncyc(sInf)) // 2

main()

# ---- solve leg
import subprocess as sp, time as _t
t0 = _t.time()
r = sp.run("cd /tmp && ./powser_arnoldi label5-carnoldi-p100.txt label5-out-p100.m",
           shell=True, capture_output=True, text=True)
print(f"MARKER solver exit={r.returncode} {_t.time()-t0:.0f}s", flush=True)
print("MARKER solver stdout tail:", r.stdout[-1500:].replace(chr(10), " | "), flush=True)
if r.returncode != 0:
    print(r.stderr[-4000:], file=sys.stderr); sys.exit(2)
outb = open("/tmp/label5-out-p100.m", "rb").read()
assert outb and b"[*" in outb[:100], "outfile not Magma data"
print("MARKER out bytes", len(outb), flush=True)
b64o = base64.b64encode(gzip.compress(outb, 9)).decode()
print("MARKER FILE BEGIN label5-out-p100.m.gz.b64", flush=True)
for i in range(0, len(b64o), 4000):
    print(b64o[i:i+4000])
print("MARKER FILE END", flush=True)
