/- Main statements + glue roadmap.

   TARGET THEOREM (paper-facing):
     Let G := ⟨g1,g2⟩ ≤ Sym(23) (the paper's M23 copy), and
     T := {(x,y) | x ∈ cls_G g1, y ∈ cls_G g2, (x*y)⁻¹ ∈ cls_G g3,
                   ⟨x,y⟩ = G}
     with G acting by simultaneous conjugation. Then:
       (a) T has exactly 7 orbits, represented by (g1, ysᵢ), i = 1..7
           (the paper's labels 1..7);
       (b) the map κ(x,y) := (x, x*y) (= (x, z⁻¹) on triples) sends orbits
           to orbits by the involution sigmaPerm = (1 2)(5 7), fixing
           labels 3, 4, 6;
       (c) hence any subgroup of Sym(T-orbits) commuting with κ-transport
           constraints preserves the partition menu {2+2+1+1, 2+2+2,
           3+2+1, 3+3, 4+1+1, 4+2, 5+1, 6} — the unconditional bridge
           consumer.

   PROOF PLAN (glue lemmas, ~the 1-2 month estimate):
     G1. checkChain sound: checkChain gens ch = true →
         Fintype.card ⟨gens⟩ = chainOrder ch.
         (Orbit–stabilizer induction along the chain; the Schreier–Sims
          verification conditions are exactly what the induction needs.
          Mathlib-free: hand-rolled subgroup-as-closure over lists.)
     G2. Anchoring: the orbit set of T under G-conjugation is in bijection
         with the orbit set of C := Stab_conj(g1) ∩ G on
         Y := {y | (g1,y) ∈ T}.  (Standard transport; needs cls_G g1 =
          conj-orbit of g1, from BFS closure semantics.)
     G3. bigCheck sound: bigCheck = true → Y (as a set) is partitioned by
         the seven C-orbits of ysᵢ.  (Reflection of the HashSet BFS into
          the abstract orbit definition — the fiddly part; alternative:
          re-express bigCheck as a straight List-based check and prove
          List-BFS soundness once, reusing it for all orbits.)
     G4. Generation vacuity: for y ∈ Y in the orbit of ysᵢ,
         ⟨g1,y⟩ = G follows from pairs_full_order (order equality) +
         conjugation-invariance of generated-subgroup order.
     G5. κ well-defined + involutive on orbits: from sigma_certs_ok
         (each certificate is an element of C ∩ G conjugating κ(anchor)
          to the target anchor) + sigma_shape.

   Everything below compiles once G1–G5 are discharged; statements are
   final now so downstream (paper appendix) can cite them stably. -/

import M23.Kernel
import M23.Native

namespace M23

-- abstract definitions used by the final statements ---------------------
def inG (p : P) : Prop := sift chainG p = true    -- membership via sifting

/-- simultaneous conjugacy of anchored pairs by an element of C∩G -/
def pairEquiv (y y' : P) : Prop :=
  ∃ c : P, (mul c g1 = mul g1 c) ∧ inG c ∧ conjP y c = y'

def kappaAnchored (y : P) : P := mul g1 y

-- final statements (proofs = glue plan G1-G5) ---------------------------

/-- (a) seven orbits: every valid anchored y is equivalent to exactly one ysᵢ -/
theorem seven_orbits :
    ∀ y : P, isPerm y = true →
      (∃ u, inG u ∧ conjP g2 u = y) →
      (∃ v, inG v ∧ conjP g3 v = inv (mul g1 y)) →
      ∃! i : Fin 7, pairEquiv (ys.getD i.val idP) y := by
  sorry -- G2 + G3

/-- (b) κ acts on labels by (1 2)(5 7) -/
theorem kappa_action :
    ∀ i : Fin 7, pairEquiv (kappaAnchored (ys.getD i.val idP))
                           (ys.getD (sigmaPerm.getD i.val 1 - 1) idP) := by
  intro i
  -- direct from sigma_certs_ok: the certificate element is the witness
  sorry -- G5

/-- (c) each anchored pair generates G -/
theorem pairs_generate :
    ∀ i : Fin 7, True := by   -- statement to be refined with ⟨·,·⟩ = G
  sorry -- G1 + G4

end M23
