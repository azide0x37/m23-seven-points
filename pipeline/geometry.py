#!/usr/bin/env python3
"""Hyperbolic geometry stack for the (a,b,c) triangle-subgroup emitter:
disc model, coset representatives from a permutation triple, fundamental-
domain reduction, FD radius. Ports Code/reduce.m and Code/cosets.m of
michaelmusty/Belyi (MIT) into python-flint acb arithmetic.

Conventions (validated by receipts, not assumed):
- UHP matrices from triangle.py: d_a fixes i (a-vertex), d_b fixes i*tau
  (b-vertex). Disc model = Cayley about i: D(z) = (z - i)/(z + i), so the
  a-vertex is the disc origin.
- Permutation rep pi: words in {a, b} -> S_d via pi(d_a) = s0, pi(d_b) = s1
  in OUR composition law (mm(p,q) = p∘q, triples satisfy s0∘s1∘sInf = id).
  Words act on sheets; coset i is labeled by a word alpha_i with
  1^pi(alpha_i) = i (0-based: 0 -> i). THE GATE.
- Reducer (reduce.m): alternate rotations d_a^i at the origin and d_b^j at
  the b-vertex, angle counts i = -floor(a*arg/(2pi) + 1/2) (and the same
  with the swap-origin map for b), boundary tie-break, fixed-point escape
  when |wp| stops decreasing (tolerance 10^(-prec/2)).
- Gamma-reduction: delta reduces to the fundamental triangle; j = coset of
  delta^-1 (sheet 0's image); gamma = alpha_j * delta in Gamma;
  reduced point = gamma * w; jAut = c*z + d of gamma's UHP matrix at the
  input point.

Receipts: COSETS_GATE_OK, COSETS_ALL_DISTINCT, RHO (FD radius),
REDUCE_IDEMPOTENT_OK, REDUCE_RADIUS_OK, GAMMA_MEMBERSHIP_OK,
AUTOMORPHY_COCYCLE_OK.
"""
import sys
sys.path.insert(0, '.')
from flint import acb, arb, acb_mat, ctx
from triangle import tri_matrices, pi_over


# ---------------------------------------------------------------- models

def uhp_apply(M, z):
    return (M[0, 0]*z + M[0, 1]) / (M[1, 0]*z + M[1, 1])

def to_disc(z):                      # Cayley about i: a-vertex -> 0
    I = acb(0, 1)
    return (z - I) / (z + I)

def to_uhp(w):
    I = acb(0, 1)
    return (I*w + I) / (-w + 1)     # inverse Cayley: w -> i(1+w)/(1-w)

def disc_abs(Mw):
    return arb(Mw.abs_upper())


class Triangle:
    def __init__(self, a, b, c, prec_bits=200):
        ctx.prec = prec_bits
        self.a, self.b, self.c = a, b, c
        self.prec_bits = prec_bits
        self.da, self.db, self.dc = tri_matrices(a, b, c, prec_bits)
        self.dai = self.da.inv(); self.dbi = self.db.inv()
        ca, sa = pi_over(a).cos(), pi_over(a).sin()
        cb, sb = pi_over(b).cos(), pi_over(b).sin()
        cc = pi_over(c).cos()
        l = (ca*cb + cc) / (sa*sb)
        self.tau = l + (l*l - 1).sqrt()
        # swap-origin map: order-2 isometry exchanging a-vertex (i) and
        # b-vertex (i*tau): z -> -tau/z, normalized to det 1.
        st = self.tau.sqrt()
        self.A = acb_mat([[acb(0), acb(-st)], [acb(1/st), acb(0)]])
        # fundamental triangle vertices (UHP): a-vertex i, b-vertex i*tau,
        # c-vertex = fixed point of dc in UHP (solve c21 z^2 + (c22-c11) z - c12 = 0)
        c11, c12, c21, c22 = self.dc[0,0], self.dc[0,1], self.dc[1,0], self.dc[1,1]
        disc = ((c22 - c11)**2 + 4*c21*c12).sqrt()
        z1 = ((c11 - c22) + disc) / (2*c21)
        z2 = ((c11 - c22) - disc) / (2*c21)
        self.vc = z1 if float(z1.imag.mid()) > 0 else z2   # UPPER half plane
        assert float(self.vc.imag.mid()) > 0
        vc_mirror = acb(-self.vc.real, self.vc.imag)       # z -> -conj(z)
        # FD(Delta) is the DOUBLE triangle: include the mirrored c-vertex
        self.verts_uhp = [acb(0, 1), acb(0, 1)*self.tau, self.vc, vc_mirror]


def word_matrix(tri, word):
    M = acb_mat(2, 2, [1, 0, 0, 1])
    for g, e in word:
        base = {'a': (tri.da, tri.dai), 'b': (tri.db, tri.dbi)}[g]
        M = M * (base[0] if e > 0 else base[1])
        for _ in range(abs(e) - 1):
            M = M * (base[0] if e > 0 else base[1])
    return M


# ------------------------------------------------------- permutation rep

def mm(p, q):
    return tuple(p[j] for j in q)

def ginv(p):
    r = [0]*len(p)
    for i, j in enumerate(p): r[j] = i
    return tuple(r)

def word_perm(word, s0, s1):
    d = len(s0)
    P = tuple(range(d))
    for g, e in word:
        base = s0 if g == 'a' else s1
        step = base if e > 0 else ginv(base)
        for _ in range(abs(e)):
            P = mm(P, step)          # composition order = matrix order
    return P


def coset_reps(s0, s1, tri=None):
    """Coset representatives: words alpha_i with sheet(alpha_i) = i.
    If tri is given, expand greedily by the distance of the translated
    triangle to the origin (Magma's 'Full' frontier heuristic), which
    keeps the resulting Gamma fundamental domain compact (small rho)."""
    d = len(s0)
    reps = [None]*d
    reps[0] = []
    gens = [('a', 1), ('a', -1), ('b', 1), ('b', -1)]

    def dist(w):
        if tri is None:
            return len(w)
        Mi = word_matrix(tri, inv_word(w))
        return float(disc_abs(to_disc(uhp_apply(Mi, acb(0, 1)))).mid())

    frontier = [0]
    while frontier:
        frontier.sort(key=lambda j: dist(reps[j]))
        j = frontier.pop(0)
        for g, e in gens:
            w = reps[j] + [(g, e)]
            i = word_perm(w, s0, s1)[0]
            if reps[i] is None:
                reps[i] = w
                frontier.append(i)
            elif tri is not None and dist(w) < dist(reps[i]) - 1e-12:
                reps[i] = w
                if i not in frontier:
                    frontier.append(i)
    assert all(r is not None for r in reps)
    return reps


# ------------------------------------------------------------- reduction

import math

def _rot_count(angle_acb, n):
    """i = -floor(n*arg/(2pi) + 1/2), reduce.m's rotation count."""
    return -math.floor(n * float(angle_acb.arg().real.mid())
                       / (2*math.pi) + 0.5)

def reduce_to_triangle(tri, z):
    """Reduce UHP point z into the fundamental triangle of Delta,
    following reduce.m: alternate d_a-rotation counted at the origin and
    d_b-rotation counted after the swap-origin map, with the boundary
    tie-break and the fixed-point escape. Returns (word, zred) with word
    a list of (gen, exp); zred = word_matrix(word) * z."""
    word = []
    wp = z
    iold = jold = 0
    wpold_abs = None
    for _ in range(4000):
        i = _rot_count(to_disc(wp), tri.a)
        if i != 0:
            M = tri.da if i > 0 else tri.dai
            for _ in range(abs(i)):
                wp = uhp_apply(M, wp)
            word.insert(0, ('a', i))
        w_sw = -to_disc(uhp_apply(tri.A, wp))      # wpp := -(A*wp), disc
        j = _rot_count(w_sw, tri.b)
        if i == 0 and iold == 0 and j == -jold:
            j = 0                                   # boundary tie-break
        else:
            iold, jold = i, j
        if j != 0:
            M = tri.db if j > 0 else tri.dbi
            for _ in range(abs(j)):
                wp = uhp_apply(M, wp)
            word.insert(0, ('b', j))
        cur = disc_abs(to_disc(wp))
        if j == 0 or (wpold_abs is not None and not (cur < wpold_abs)):
            # candidate exit: VERIFIED Dirichlet terminator. d_a-rotations
            # preserve |disc|, so the point is fully reduced iff no move
            # d_b^{+-1} d_a^k decreases the radius, k = 0..a-1. This is
            # convention-free (independent of the swap-origin map used for
            # the counting heuristic above).
            def midr(w):
                return abs(complex(to_disc(w).mid()))
            improved = False
            r0 = midr(wp)
            wq = wp
            for k in range(tri.a):
                for M, tag in ((tri.db, 1), (tri.dbi, -1)):
                    wr = uhp_apply(M, wq)
                    if midr(wr) < r0 - 1e-30:
                        if k:
                            word.insert(0, ('a', k))
                        word.insert(0, ('b', tag))
                        wp = wr
                        improved = True
                        break
                if improved:
                    break
                wq = uhp_apply(tri.da, wq)
            if not improved:
                break
            cur = disc_abs(to_disc(wp))
        wpold_abs = cur
    # final in-sector normalization (radius-preserving)
    i = _rot_count(to_disc(wp), tri.a)
    if i != 0:
        M = tri.da if i > 0 else tri.dai
        for _ in range(abs(i)):
            wp = uhp_apply(M, wp)
        word.insert(0, ('a', i))
    return word, wp


def inv_word(word):
    return [(g, -e) for (g, e) in reversed(word)]

def reduce_to_gamma(tri, reps, s0, s1, z):
    """Full Gamma-reduction of UHP point z. With our function-composition
    pi, sheets correspond to LEFT cosets alpha_j*Gamma: j = sheet(delta) =
    pi(delta)(0), gamma = alpha_j^-1 * delta in Gamma, reduced point
    gamma*z lies in alpha_j^-1 * FD(Delta). Returns (M, zred, j, gword)."""
    word, _ = reduce_to_triangle(tri, z)
    P = word_perm(word, s0, s1)
    j = P[0]                        # sheet of delta
    gword = inv_word(reps[j]) + word
    G = word_perm(gword, s0, s1)
    assert G[0] == 0, "gamma not in Gamma (gate failed)"
    M = word_matrix(tri, gword)
    zred = uhp_apply(M, z)
    return M, zred, j, gword

def fd_radius(tri, reps):
    """rho = max |disc point| over the Gamma fundamental domain
    = max over cosets j and triangle vertices v of |disc(alpha_j^-1 v)|."""
    rho = arb(0)
    for r in reps:
        Mi = word_matrix(tri, inv_word(r))
        for v in tri.verts_uhp:
            d = disc_abs(to_disc(uhp_apply(Mi, v)))
            rho = rho if rho > d else d
    return rho
