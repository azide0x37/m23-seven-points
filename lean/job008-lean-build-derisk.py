#!/usr/bin/env python3
"""Mnemosyne job -008: build + check the m23-lean census formalization.
Installs elan/Lean 4.15 in-container, regenerates Data.lean via the
inlined certificate generator (paper generators + seven tuples embedded),
runs `lake build` (mathlib-free), and reports per-step timings — the
kernel-decide budget derisk. Census.lean has `sorry` glue: expected
result is 'build completes with sorry warnings, no errors', proving
Defs/Sims/Data/Kernel/Native all elaborate and every `decide` /
`native_decide` certificate CHECKS."""
import subprocess as sp, sys, os, json, time, urllib.request, re

G1_STR = '(1,11)(2,23)(3,8)(4,16)(5,21)(7,20)(15,19)(18,22)'
G2_STR = '(1,2,11,10,16,9,6,3,23,19,20,14,21,17,4,8,22,5,18,15,13,7,12)'
G3_STR = '(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)'
SEVEN = [[1, ["(6,14)(7,20)(8,21)(9,19)(10,22)(12,15)(13,18)(16,23)", "(1,16,19,20,6,21,17,23,12,11,22,8,13,7,15,18,9,14,5,10,4,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]], [2, ["(6,19)(7,15)(8,13)(9,14)(10,16)(12,20)(18,21)(22,23)", "(1,22,18,6,13,12,11,16,14,5,23,7,20,9,19,15,8,21,17,10,4,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]], [3, ["(3,5)(4,17)(6,15)(8,20)(9,22)(12,23)(13,14)(16,18)", "(1,12,11,10,17,18,19,7,23,6,20,13,8,16,22,21,4,5,9,15,14,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]], [4, ["(3,7)(5,18)(6,21)(9,10)(11,14)(13,23)(15,20)(17,22)", "(1,13,15,23,20,11,9,21,22,6,8,5,17,16,10,4,7,12,14,18,19,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]], [5, ["(3,13)(4,12)(5,23)(6,7)(10,15)(14,17)(16,19)(18,21)", "(1,5,22,18,16,9,7,4,13,20,17,19,6,8,21,14,23,10,12,11,15,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]], [6, ["(3,21)(5,9)(6,16)(8,13)(10,12)(11,15)(17,23)(19,20)", "(1,17,6,13,19,7,10,4,21,23,11,12,15,8,18,20,14,9,16,5,22,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]], [7, ["(3,21)(4,12)(5,6)(7,23)(9,20)(11,22)(13,18)(16,19)", "(1,7,4,21,17,19,23,15,18,16,20,14,6,8,13,9,5,11,10,12,22,3,2)", "(1,2,3,4,10,11,12,7,19,18,8,6,9,16,17,21,22,5,14,20,13,15,23)"]]]
LEAN_FILES = {"lakefile.toml": "name = \"m23\"\ndefaultTargets = [\"M23\"]\n\n[[lean_lib]]\nname = \"M23\"\n", "lean-toolchain": "leanprover/lean4:v4.15.0\n", "M23.lean": "import M23.Census\n", "M23/Defs.lean": "/- M23 census formalization: core definitions.\n   Mathlib-free. Permutations of {0..22} as `List (Fin 23)` of length 23\n   (the image list: p.get i = image of i). All predicates decidable so the\n   certificate layer runs under `decide` (kernel) / `native_decide`. -/\n\nnamespace M23\n\nabbrev P := List Nat          -- permutation as image list (length 23, entries < 23)\n\ndef n : Nat := 23\n\ndef isPerm (p : P) : Bool :=\n  p.length == n && (List.range n).all (fun i => p.contains i)\n\ndef idP : P := List.range n\n\n/-- apply p to a point -/\ndef ap (p : P) (i : Nat) : Nat := p.getD i 0\n\n/-- composition p \u2218 q : first q, then p?  We fix the CONVENTION\n    (mul p q) i = p (q i)  \u2014 matches the campaign's mm(p,q) = p\u2218q. -/\ndef mul (p q : P) : P := q.map (fun i => ap p i)\n\ndef inv (p : P) : P :=\n  (List.range n).map (fun i => (p.idxOf i))\n\n/-- conjugation c\u207b\u00b9 p c (campaign convention conj(g,c) = c\u207b\u00b9gc) -/\ndef conjP (p c : P) : P := mul (mul (inv c) p) c\n\ndef orderDivides (p : P) (k : Nat) : Bool :=\n  (Nat.fold k (fun _ _ acc => mul acc p) idP) == idP\n\n/-- word in two generators: `true` = a, `false` = b (applied left-to-right\n    as multiplication: w = [x,y] \u21a6 gx * gy) -/\ndef wordEval (ga gb : P) (w : List Bool) : P :=\n  w.foldl (fun acc c => mul acc (if c then ga else gb)) idP\n\nend M23\n", "M23/Sims.lean": "/- Verified Sims (BSGS) certificate checker.\n\n   A chain certificate for G = \u27e8gens\u27e9 is a list of levels; level j carries:\n     base point b\u2c7c, strong generators S\u2c7c (must fix b\u2081..b\u2c7c\u208b\u2081),\n     transversal: list of (point, permutation) with the perm mapping b\u2c7c to\n     the point (orbit of b\u2c7c under S\u2c7c).\n   `checkChain` verifies (all Bool, decidable):\n     1. S\u2081 \u2287 input generators (as a set),\n     2. each S\u2c7c\u208a\u2081 element fixes b\u2081..b\u2c7c,\n     3. each transversal entry t maps b\u2c7c to its claimed point; entry for b\u2c7c\n        itself is present; claimed orbit is duplicate-free,\n     4. closure + strong generation (Sims verification): for every\n        transversal entry (q, t) and s \u2208 S\u2c7c, the Schreier element\n        u := (transversal at s(q))\u207b\u00b9 * s * t   sifts to the identity\n        through levels j+1.. (sifting: repeatedly divide by the transversal\n        entry at the image of the level's base point; fails Bool-false if an\n        image is outside a lower orbit).\n   Soundness (proved in Census.lean glue, not assumed): if checkChain holds\n   then |\u27e8gens\u27e9| = product of orbit lengths.  -/\n\nimport M23.Defs\n\nnamespace M23\n\nstructure Level where\n  base   : Nat\n  sgens  : List P\n  transv : List (Nat \u00d7 P)     -- (point, perm with ap perm base = point)\nderiving Repr\n\nabbrev Chain := List Level\n\ndef transvLookup (L : Level) (q : Nat) : Option P :=\n  (L.transv.find? (fun e => e.fst == q)).map (\u00b7.snd)\n\n/-- sift w through the chain; true iff it reduces to the identity -/\ndef sift : Chain \u2192 P \u2192 Bool\n  | [], w => w == idP\n  | L :: rest, w =>\n    match transvLookup L (ap w L.base) with\n    | none => false\n    | some t => sift rest (mul (inv t) w)\n\ndef fixesAll (p : P) (pts : List Nat) : Bool :=\n  pts.all (fun b => ap p b == b)\n\ndef checkLevel (prevBases : List Nat) (L : Level) (rest : Chain) : Bool :=\n  L.sgens.all (fun s => fixesAll s prevBases) &&\n  (L.transv.map (\u00b7.fst)).Nodup &&\n  L.transv.any (fun e => e.fst == L.base && e.snd == idP) &&\n  L.transv.all (fun e => ap e.snd L.base == e.fst) &&\n  L.transv.all (fun (q, t) =>\n    L.sgens.all (fun s =>\n      match transvLookup L (ap s q) with\n      | none => false\n      | some t' =>\n        -- Schreier element t'\u207b\u00b9 * s * t fixes the base and must sift\n        -- through the stabilizer chain (rest) to the identity:\n        sift rest (mul (inv t') (mul s t))))\n\ndef checkChain (gens : List P) : Chain \u2192 Bool\n  | [] => gens.all (fun g => g == idP)\n  | ch =>\n    -- generators sift through the whole chain\n    gens.all (fun g => sift ch g) &&\n    -- generators are among level-1 strong gens (containment as words is\n    -- implied by sifting; we additionally require S\u2081 \u2287 gens for strong\n    -- generation of the top group)\n    (match ch with\n     | [] => false\n     | L :: _ => gens.all (fun g => L.sgens.contains g)) &&\n    go [] ch\nwhere\n  go (prevBases : List Nat) : Chain \u2192 Bool\n    | [] => true\n    | L :: rest => checkLevel prevBases L rest && go (prevBases ++ [L.base]) rest\n\ndef chainOrder (ch : Chain) : Nat :=\n  ch.foldl (fun acc L => acc * L.transv.length) 1\n\nend M23\n", "M23/Kernel.lean": "/- Kernel-checked certificate layer: every fact here is a closed Bool\n   evaluated by `decide` (no compiler trust). If kernel reduction proves\n   too slow for the chain checks on your machine, flip individual proofs\n   to `native_decide` \u2014 each theorem isolates one certificate so the\n   trusted-computing-base tradeoff is per-fact and explicit. -/\n\nimport M23.Data\n\nset_option maxHeartbeats 40000000\n\nnamespace M23\n\n-- basic sanity ---------------------------------------------------------\ntheorem g_perms : (isPerm g1 && isPerm g2 && isPerm g3) = true := by decide\n\ntheorem product_id : mul (mul g1 g2) g3 == idP := by decide\n\ntheorem orders : (orderDivides g1 2 && orderDivides g2 23\n                  && orderDivides g3 23) = true := by decide\n\ntheorem ys_perms : ys.all isPerm = true := by decide\n\n-- |G| = 10,200,960 via the verified Sims chain -------------------------\ntheorem chainG_ok : checkChain [g1, g2] chainG = true := by decide\n\ntheorem chainG_order : chainOrder chainG = 10200960 := by decide\n\n-- the seven pairs generate a group of the same order -------------------\ntheorem pairs_full_order :\n    (List.range 7).all (fun i =>\n      let ch := [chainPair1, chainPair2, chainPair3, chainPair4,\n                 chainPair5, chainPair6, chainPair7].getD i []\n      checkChain [g1, ys.getD i idP] ch && chainOrder ch == 10200960)\n    = true := by decide\n\n-- class membership certificates ----------------------------------------\ntheorem cls_certs :\n    (List.range 7).all (fun i =>\n      let y := ys.getD i idP\n      let u := clsYCerts.getD i idP\n      let v := clsZCerts.getD i idP\n      conjP g2 u == y && conjP g3 v == inv (mul g1 y)\n      && sift chainG u && sift chainG v)\n    = true := by decide\n\n-- centralizer generators: commute with g1, lie in G --------------------\ntheorem hGens_ok :\n    hGens.all (fun h => mul h g1 == mul g1 h && sift chainG h)\n    = true := by decide\n\n-- kappa certificates: c_i \u2208 C(g1) \u2229 G conjugates g1*y_i to y_{sigma(i)}\ntheorem sigma_certs_ok :\n    (List.range 7).all (fun i =>\n      let c := sigmaCerts.getD i idP\n      let y := ys.getD i idP\n      let ytgt := ys.getD (sigmaPerm.getD i 1 - 1) idP\n      mul c g1 == mul g1 c && sift chainG c\n      && conjP (mul g1 y) c == ytgt)\n    = true := by decide\n\n-- sigma is the involution (1 2)(5 7) fixing 3,4,6 ----------------------\ntheorem sigma_shape : sigmaPerm = [2,1,3,4,7,6,5] := by decide\n\nend M23\n", "M23/Native.lean": "/- The single big-enumeration certificate, evaluated once by\n   `native_decide` (trusts the Lean compiler \u2014 the one such fact in the\n   development, quarantined here).\n\n   bigCheck materializes:\n     C     := closure of hGens                         (claim: 2688)\n     clsY  := conjugation orbit of g2 under {g1,g2}    (claim: 443520)\n     clsZ  := conjugation orbit of g3 under {g1,g2}    (claim: 443520)\n     Y     := {y \u2208 clsY | (g1*y)\u207b\u00b9 \u2208 clsZ}             (claim: 18816)\n     orb\u1d62  := C-conjugation orbit of ys\u1d62               (claim: each 2688)\n   and checks: sizes; orb\u1d62 pairwise disjoint; \u22c3orb\u1d62 = Y.\n\n   Together with the kernel layer this gives: the seven anchored pairs\n   (g1, ys\u1d62) hit every C-orbit on Y exactly once. -/\n\nimport M23.Data\nimport Std.Data.HashSet\nimport Std.Data.HashMap\n\nnamespace M23\n\n/-- pack a perm into a Nat for hashing/equality (23 digits base 23) -/\ndef enc (p : P) : Nat := p.foldr (fun d acc => acc * 23 + d) 0\n\ndef conjB (g cInv c : P) : P := mul (mul cInv g) c\n\n/-- BFS conjugation orbit of x under gens (with precomputed inverses) -/\npartial def conjOrbit (x : P) (gens : List (P \u00d7 P)) : Std.HashSet Nat \u00d7 List P :=\n  go ({} : Std.HashSet Nat).insert (enc x) [x] [x]\nwhere\n  go (seen : Std.HashSet Nat) (fr acc : List P) : Std.HashSet Nat \u00d7 List P :=\n    match fr with\n    | [] => (seen, acc)\n    | _ =>\n      let (seen', nf, acc') := fr.foldl (init := (seen, ([] : List P), acc))\n        fun (s, nf, ac) u =>\n          gens.foldl (init := (s, nf, ac)) fun (s, nf, ac) (c, cInv) =>\n            let v := conjB u cInv c\n            let e := enc v\n            if s.contains e then (s, nf, ac)\n            else (s.insert e, v :: nf, v :: ac)\n      go seen' nf acc'\n\n/-- group closure (right multiplication BFS) -/\npartial def closure (gens : List P) : Std.HashSet Nat \u00d7 List P :=\n  go ({} : Std.HashSet Nat).insert (enc idP) [idP] [idP]\nwhere\n  go (seen : Std.HashSet Nat) (fr acc : List P) : Std.HashSet Nat \u00d7 List P :=\n    match fr with\n    | [] => (seen, acc)\n    | _ =>\n      let (seen', nf, acc') := fr.foldl (init := (seen, ([] : List P), acc))\n        fun (s, nf, ac) u =>\n          gens.foldl (init := (s, nf, ac)) fun (s, nf, ac) g =>\n            let v := mul u g\n            let e := enc v\n            if s.contains e then (s, nf, ac)\n            else (s.insert e, v :: nf, v :: ac)\n      go seen' nf acc'\n\ndef bigCheck : Bool := Id.run do\n  let gg := [(g1, inv g1), (g2, inv g2)]\n  let (setY, listY) := conjOrbit g2 gg\n  let (setZ, _) := conjOrbit g3 gg\n  let (setC, listC) := closure hGens\n  if listC.length != 2688 then return false\n  if listY.length != 443520 then return false\n  if setZ.size != 443520 then return false\n  -- Y filter\n  let Y := listY.filter (fun y => setZ.contains (enc (inv (mul g1 y))))\n  if Y.length != 18816 then return false\n  let setYfil : Std.HashSet Nat := Y.foldl (fun s y => s.insert (enc y)) {}\n  -- seven C-orbits\n  let hg := hGens.map (fun h => (h, inv h))\n  let mut union : Std.HashSet Nat := {}\n  let mut total := 0\n  for y in ys do\n    let (so, lo) := conjOrbit y hg\n    if lo.length != 2688 then return false\n    for v in lo do\n      let e := enc v\n      if union.contains e then return false        -- disjointness\n      if !(setYfil.contains e) then return false   -- orb \u2286 Y\n      union := union.insert e\n    total := total + lo.length\n  -- coverage\n  if total != 18816 then return false\n  if union.size != 18816 then return false\n  -- also record: setY really is closed (orbit BFS guarantees), sizes match\n  let _ := setY\n  let _ := setC\n  return true\n\ntheorem census_native : bigCheck = true := by native_decide\n\nend M23\n", "M23/Census.lean": "/- Main statements + glue roadmap.\n\n   TARGET THEOREM (paper-facing):\n     Let G := \u27e8g1,g2\u27e9 \u2264 Sym(23) (the paper's M23 copy), and\n     T := {(x,y) | x \u2208 cls_G g1, y \u2208 cls_G g2, (x*y)\u207b\u00b9 \u2208 cls_G g3,\n                   \u27e8x,y\u27e9 = G}\n     with G acting by simultaneous conjugation. Then:\n       (a) T has exactly 7 orbits, represented by (g1, ys\u1d62), i = 1..7\n           (the paper's labels 1..7);\n       (b) the map \u03ba(x,y) := (x, x*y) (= (x, z\u207b\u00b9) on triples) sends orbits\n           to orbits by the involution sigmaPerm = (1 2)(5 7), fixing\n           labels 3, 4, 6;\n       (c) hence any subgroup of Sym(T-orbits) commuting with \u03ba-transport\n           constraints preserves the partition menu {2+2+1+1, 2+2+2,\n           3+2+1, 3+3, 4+1+1, 4+2, 5+1, 6} \u2014 the unconditional bridge\n           consumer.\n\n   PROOF PLAN (glue lemmas, ~the 1-2 month estimate):\n     G1. checkChain sound: checkChain gens ch = true \u2192\n         Fintype.card \u27e8gens\u27e9 = chainOrder ch.\n         (Orbit\u2013stabilizer induction along the chain; the Schreier\u2013Sims\n          verification conditions are exactly what the induction needs.\n          Mathlib-free: hand-rolled subgroup-as-closure over lists.)\n     G2. Anchoring: the orbit set of T under G-conjugation is in bijection\n         with the orbit set of C := Stab_conj(g1) \u2229 G on\n         Y := {y | (g1,y) \u2208 T}.  (Standard transport; needs cls_G g1 =\n          conj-orbit of g1, from BFS closure semantics.)\n     G3. bigCheck sound: bigCheck = true \u2192 Y (as a set) is partitioned by\n         the seven C-orbits of ys\u1d62.  (Reflection of the HashSet BFS into\n          the abstract orbit definition \u2014 the fiddly part; alternative:\n          re-express bigCheck as a straight List-based check and prove\n          List-BFS soundness once, reusing it for all orbits.)\n     G4. Generation vacuity: for y \u2208 Y in the orbit of ys\u1d62,\n         \u27e8g1,y\u27e9 = G follows from pairs_full_order (order equality) +\n         conjugation-invariance of generated-subgroup order.\n     G5. \u03ba well-defined + involutive on orbits: from sigma_certs_ok\n         (each certificate is an element of C \u2229 G conjugating \u03ba(anchor)\n          to the target anchor) + sigma_shape.\n\n   Everything below compiles once G1\u2013G5 are discharged; statements are\n   final now so downstream (paper appendix) can cite them stably. -/\n\nimport M23.Kernel\nimport M23.Native\n\nnamespace M23\n\n-- abstract definitions used by the final statements ---------------------\ndef inG (p : P) : Prop := sift chainG p = true    -- membership via sifting\n\n/-- simultaneous conjugacy of anchored pairs by an element of C\u2229G -/\ndef pairEquiv (y y' : P) : Prop :=\n  \u2203 c : P, (mul c g1 = mul g1 c) \u2227 inG c \u2227 conjP y c = y'\n\ndef kappaAnchored (y : P) : P := mul g1 y\n\n-- final statements (proofs = glue plan G1-G5) ---------------------------\n\n/-- (a) seven orbits: every valid anchored y is equivalent to exactly one ys\u1d62 -/\ntheorem seven_orbits :\n    \u2200 y : P, isPerm y = true \u2192\n      (\u2203 u, inG u \u2227 conjP g2 u = y) \u2192\n      (\u2203 v, inG v \u2227 conjP g3 v = inv (mul g1 y)) \u2192\n      \u2203! i : Fin 7, pairEquiv (ys.getD i idP) y := by\n  sorry -- G2 + G3\n\n/-- (b) \u03ba acts on labels by (1 2)(5 7) -/\ntheorem kappa_action :\n    \u2200 i : Fin 7, pairEquiv (kappaAnchored (ys.getD i idP))\n                           (ys.getD (sigmaPerm.getD i 1 - 1) idP) := by\n  intro i\n  -- direct from sigma_certs_ok: the certificate element is the witness\n  sorry -- G5\n\n/-- (c) each anchored pair generates G -/\ntheorem pairs_generate :\n    \u2200 i : Fin 7, True := by   -- statement to be refined with \u27e8\u00b7,\u00b7\u27e9 = G\n  sorry -- G1 + G4\n\nend M23\n"}

def parse_cycles(s, n=23):
    p = list(range(n))
    for cyc in re.findall(r"\(([^)]*)\)", s):
        el = [int(t)-1 for t in cyc.replace(",", " ").split()]
        for i in range(len(el)):
            p[el[i]] = el[(i+1) % len(el)]
    return tuple(p)

N = 23
IDENT = bytes(range(N))
STATE = 'lean_certgen_state.pkl'

def mm(p, q): return bytes(p[q[i]] for i in range(N))
def gin(p):
    r = bytearray(N)
    for i in range(N): r[p[i]] = i
    return bytes(r)
def conj(g, c): return mm(mm(gin(c), g), c)

def sims_chain(gens):
    """Schreier-Sims; returns chain [(base, sgens, transv{pt:perm})] with
    perm mapping base -> pt under ap(perm, base) = perm[base]."""
    chain = []
    G = [g for g in gens if g != IDENT]
    while G:
        b = next(p for p in range(N) if any(g[p] != p for g in G))
        tr = {b: IDENT}; fr = [b]
        while fr:
            nf = []
            for q in fr:
                for g in G:
                    r = g[q]
                    if r not in tr:
                        tr[r] = mm(g, tr[q]); nf.append(r)
            fr = nf
        S = set()
        for q, w in tr.items():
            for g in G:
                s = mm(gin(tr[g[q]]), mm(g, w))
                if s != IDENT: S.add(s)
        chain.append((b, list(G), tr))
        G = sorted(S)
    return chain

def verify_chain(gens, chain):
    def sift(w, lv):
        for b, S, tr in chain[lv:]:
            t = tr.get(w[b])
            if t is None: return None
            w = mm(gin(t), w)
        return w == IDENT
    for g in gens:
        assert sift(g, 0), "gen sift"
    for lv, (b, S, tr) in enumerate(chain):
        for q, t in tr.items():
            assert t[b] == q
            for s in S:
                t2 = tr.get(s[q])
                assert t2 is not None
                assert sift(mm(gin(t2), mm(s, t)), lv + 1), "schreier sift"
    order = 1
    for _, _, tr in chain: order *= len(tr)
    return order



def run(cmd, timeout=None, env=None):
    t0 = time.time()
    r = sp.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout, env=env)
    print(f"MARKER step [{cmd[:70]}] exit={r.returncode} {time.time()-t0:.0f}s", flush=True)
    if r.returncode != 0:
        print(r.stdout[-3000:]); print(r.stderr[-5000:], file=sys.stderr)
    return r

def gen_data():
    g1 = bytes(parse_cycles(G1_STR)); g2 = bytes(parse_cycles(G2_STR))
    g3 = bytes(parse_cycles(G3_STR))
    assert mm(mm(g1, g2), g3) == IDENT
    # anchors + witnesses (2A BFS)
    seen = {g1: IDENT}; fr = [g1]
    while fr:
        nf = []
        for u in fr:
            for c in (g1, g2):
                v = conj(u, c)
                if v not in seen:
                    seen[v] = mm(seen[u], c); nf.append(v)
        fr = nf
    anchors = {}
    for lab, tup in SEVEN:
        x, y, z = (bytes(parse_cycles(s)) for s in tup)
        w = seen[x]; assert conj(g1, w) == x
        anchors[lab] = conj(y, gin(w))
    sch = set()
    for u, w in seen.items():
        for c in (g1, g2):
            s = mm(w, mm(c, gin(seen[conj(u, c)])))
            if s != IDENT: sch.add(s)
    import random as R
    R.seed(7)
    small, cur = [], {IDENT}
    for s in R.sample(sorted(sch), 40):
        if s not in cur:
            small.append(s)
            cl = {IDENT}; fr2 = [IDENT]
            while fr2:
                nf2 = []
                for u in fr2:
                    for t in small:
                        v = mm(u, t)
                        if v not in cl: cl.add(v); nf2.append(v)
                fr2 = nf2
            cur = cl
            if len(cur) == 2688: break
    assert len(cur) == 2688
    Clist = sorted(cur)
    sig = {1:2, 2:1, 3:3, 4:4, 5:7, 6:6, 7:5}
    cs = {}
    for lab, y in anchors.items():
        ky = mm(g1, y); tgt = anchors[sig[lab]]
        cs[lab] = next(c for c in Clist if conj(ky, c) == tgt)
    wit = {g2: IDENT}; fr = [g2]
    while fr:
        nf = []
        for u in fr:
            for c in (g1, g2):
                v = conj(u, c)
                if v not in wit:
                    wit[v] = mm(wit[u], c); nf.append(v)
        fr = nf
    us = {lab: wit[y] for lab, y in anchors.items()}
    witZ = {g3: IDENT}; fr = [g3]
    while fr:
        nf = []
        for u in fr:
            for c in (g1, g2):
                v = conj(u, c)
                if v not in witZ:
                    witZ[v] = mm(witZ[u], c); nf.append(v)
        fr = nf
    vs = {lab: witZ[gin(mm(g1, y))] for lab, y in anchors.items()}
    chainG = sims_chain([g1, g2]); assert verify_chain([g1, g2], chainG) == 10200960
    chains7 = {}
    for lab, y in anchors.items():
        ch = sims_chain([g1, y]); assert verify_chain([g1, y], ch) == 10200960
        chains7[lab] = ch
    def lp(p): return "[" + ",".join(str(b) for b in p) + "]"
    def llev(ch):
        out = []
        for b, S, tr in ch:
            trs = ",".join(f"({q},{lp(t)})" for q, t in sorted(tr.items()))
            sg = ",".join(lp(s) for s in S)
            out.append(f"⟨{b},[{sg}],[{trs}]⟩")
        return "[" + ",\n   ".join(out) + "]"
    L = ["/- AUTO-GENERATED in-container -/", "import M23.Sims", "namespace M23", ""]
    L.append(f"def g1 : P := {lp(g1)}")
    L.append(f"def g2 : P := {lp(g2)}")
    L.append(f"def g3 : P := {lp(g3)}")
    L.append("def ys : List P := [" + ",".join(lp(anchors[i]) for i in range(1, 8)) + "]")
    L.append("def sigmaPerm : List Nat := [2,1,3,4,7,6,5]")
    L.append("def sigmaCerts : List P := [" + ",".join(lp(cs[i]) for i in range(1, 8)) + "]")
    L.append("def clsYCerts : List P := [" + ",".join(lp(us[i]) for i in range(1, 8)) + "]")
    L.append("def clsZCerts : List P := [" + ",".join(lp(vs[i]) for i in range(1, 8)) + "]")
    L.append("def hGens : List P := [" + ",".join(lp(h) for h in small) + "]")
    L.append(f"def chainG : Chain :=\n  {llev(chainG)}")
    for i in range(1, 8):
        L.append(f"def chainPair{i} : Chain :=\n  {llev(chains7[i])}")
    L.append("end M23")
    return "\n".join(L) + "\n"

t0 = time.time()
os.makedirs("/root/proj/M23", exist_ok=True)
for f, src in LEAN_FILES.items():
    path = os.path.join("/root/proj", f)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write(src)
data = gen_data()
open("/root/proj/M23/Data.lean", "w").write(data)
print(f"MARKER Data.lean regenerated {len(data)//1024}KB ({time.time()-t0:.0f}s)", flush=True)
run("apt-get update -qq && apt-get install -y -qq curl git > /dev/null")
urllib.request.urlretrieve("https://elan.lean-lang.org/elan-init.sh", "/tmp/elan-init.sh")
r = run("sh /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.15.0", timeout=1800)
if r.returncode != 0: sys.exit(1)
env = dict(os.environ, PATH="/root/.elan/bin:" + os.environ["PATH"])
r = sp.run("cd /root/proj && lake build 2>&1", shell=True, capture_output=True,
           text=True, env=env)
print(f"MARKER lake build exit={r.returncode}", flush=True)
print("MARKER BUILD LOG BEGIN", flush=True)
print(r.stdout[-8000:], flush=True)
print("MARKER BUILD LOG END", flush=True)
nsorry = r.stdout.count("declaration uses 'sorry'")
print(f"MARKER verdict exit={r.returncode} sorries={nsorry} total={time.time()-t0:.0f}s", flush=True)
sys.exit(0 if r.returncode == 0 else 3)
