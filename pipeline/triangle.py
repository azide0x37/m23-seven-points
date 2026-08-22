#!/usr/bin/env python3
"""Triangle group Delta(a,b,c) generator matrices in rigorous ball
arithmetic (python-flint acb), following the public formulas in
michaelmusty/Belyi Code/triangle.m (MIT).

    l   = (cos(pi/a) cos(pi/b) + cos(pi/c)) / (sin(pi/a) sin(pi/b))
    tau = l + sqrt(l^2 - 1)

    d_a = [[ cos(pi/a),        sin(pi/a)],
           [-sin(pi/a),        cos(pi/a)]]
    d_b = [[ cos(pi/b),        tau sin(pi/b)],
           [-sin(pi/b)/tau,    cos(pi/b)]]
    d_c = (d_a d_b)^(-1)

Conventions: d_a is the rotation by pi/a at the disk-origin vertex; in
SL_2 each d has order 2n with d^n = -I, i.e. projective order n.  For the
M23 run the signature is ordered (23, 2, 23) -- 23-cycle first, so the
order-23 vertex sits at the origin, matching the expansion point and the
f_i = q^i + O(q^4) normalization of arXiv:2608.08538.

Receipts (printed as MARKER lines):
    TRIANGLE_DETERMINANTS_OK        det d = 1 rigorously (ball contains 1,
                                    radius below tolerance)
    PROJECTIVE_ORDERS=a,b,c         d^n + I = 0 verified in balls
    TRIANGLE_PRODUCT_OK             d_a d_b d_c = I in balls
    TRACE_C_OK                      |tr d_c| = 2 cos(pi/c) in balls
    HYPERBOLIC_OK                   1/a + 1/b + 1/c < 1
"""
from flint import acb, arb, acb_mat, ctx


def pi_over(n):
    return arb.pi() / n


def tri_matrices(a, b, c, prec_bits=350):
    ctx.prec = prec_bits
    ca, sa = pi_over(a).cos(), pi_over(a).sin()
    cb, sb = pi_over(b).cos(), pi_over(b).sin()
    cc = pi_over(c).cos()
    l = (ca * cb + cc) / (sa * sb)
    tau = l + (l * l - 1).sqrt()
    da = acb_mat([[acb(ca), acb(sa)], [acb(-sa), acb(ca)]])
    db = acb_mat([[acb(cb), acb(tau * sb)], [acb(-(sb / tau)), acb(cb)]])
    dc = (da * db).inv()
    return da, db, dc


def ball_is(x, target, tol=arb("1e-80")):
    """Rigorous: the ball x contains target and has radius < tol."""
    d = x - target
    return d.contains(acb(0) if isinstance(d, acb) else arb(0)) \
        and arb(d.abs_upper()) < tol


def mat_is_identity(M, sign=+1, tol=arb("1e-80")):
    I = acb_mat(2, 2, [1, 0, 0, 1])
    T = M - I * sign
    ok = True
    for i in range(2):
        for j in range(2):
            e = T[i, j]
            ok = ok and e.contains(acb(0)) and arb(e.abs_upper()) < tol
    return ok


def proj_order_ok(d, n):
    """Projective order n: d^n = +/-I in SL2 (the SL2-lift may have
    eigenvalues -e^(+/-i pi/n), giving +I at the n-th power), and
    d^k != +/-I for 0 < k < n."""
    p = acb_mat(2, 2, [1, 0, 0, 1])
    for k in range(1, n + 1):
        p = p * d
        pm = mat_is_identity(p, +1) or mat_is_identity(p, -1)
        if k < n and pm:
            return False
        if k == n:
            return pm
    return False


def receipts(a, b, c, prec_bits=350):
    assert arb(1) / a + arb(1) / b + arb(1) / c < 1, "not hyperbolic"
    print("MARKER HYPERBOLIC_OK")
    da, db, dc = tri_matrices(a, b, c, prec_bits)
    for name, d in (("a", da), ("b", db), ("c", dc)):
        det = d[0, 0] * d[1, 1] - d[0, 1] * d[1, 0]
        assert det.contains(acb(1)) and arb((det - 1).abs_upper()) < arb("1e-80"), \
            f"det d_{name} != 1"
    print("MARKER TRIANGLE_DETERMINANTS_OK")
    assert proj_order_ok(da, a) and proj_order_ok(db, b) \
        and proj_order_ok(dc, c), "projective order failed"
    print(f"MARKER PROJECTIVE_ORDERS={a},{b},{c}")
    assert mat_is_identity(da * db * dc), "product != I"
    print("MARKER TRIANGLE_PRODUCT_OK")
    tr = dc[0, 0] + dc[1, 1]
    target = 2 * pi_over(c).cos()
    ok = tr.contains(acb(target)) or tr.contains(acb(-target))
    assert ok, "trace of d_c wrong"
    print("MARKER TRACE_C_OK")
    return da, db, dc


if __name__ == "__main__":
    import sys
    a, b, c = (int(x) for x in (sys.argv[1:4] or [23, 2, 23]))
    prec = int(sys.argv[4]) if len(sys.argv) > 4 else 350
    receipts(a, b, c, prec)
    print(f"MARKER triangle ({a},{b},{c}) prec={prec} bits: ALL OK")
