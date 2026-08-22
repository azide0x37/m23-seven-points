/- Kernel-checked certificate layer: every fact is a closed Bool under
   `decide` (kernel only, no compiler trust). If a chain check exceeds
   kernel budget on your machine, flip THAT proof to `native_decide` —
   one theorem per certificate keeps the TCB tradeoff per-fact. -/

import M23.Data

set_option maxHeartbeats 400000000
set_option maxRecDepth 100000

namespace M23

-- basic sanity ---------------------------------------------------------
theorem g_perms : (isPerm g1 && isPerm g2 && isPerm g3) = true := by decide

theorem product_id : (mul (mul g1 g2) g3 == idP) = true := by decide

theorem orders : (orderDivides g1 2 && orderDivides g2 23
                  && orderDivides g3 23) = true := by decide

theorem ys_perms : (ys.all isPerm) = true := by decide

-- |G| = 10,200,960 via the verified Sims chain -------------------------
theorem chainG_ok : checkChain [g1, g2] chainG = true := by decide

theorem chainG_order : chainOrder chainG = 10200960 := by decide

-- the seven pairs generate a group of the same order -------------------
def pairChains : List Chain :=
  [chainPair1, chainPair2, chainPair3, chainPair4,
   chainPair5, chainPair6, chainPair7]

theorem pairs_full_order :
    ((List.range 7).all (fun i =>
      checkChain [g1, ys.getD i idP] (pairChains.getD i [])
      && chainOrder (pairChains.getD i []) == 10200960)) = true := by decide

-- class membership certificates ----------------------------------------
theorem cls_certs :
    ((List.range 7).all (fun i =>
      (conjP g2 (clsYCerts.getD i idP) == ys.getD i idP)
      && (conjP g3 (clsZCerts.getD i idP) == inv (mul g1 (ys.getD i idP)))
      && sift chainG (clsYCerts.getD i idP)
      && sift chainG (clsZCerts.getD i idP))) = true := by decide

-- centralizer generators: commute with g1, lie in G --------------------
theorem hGens_ok :
    (hGens.all (fun h => (mul h g1 == mul g1 h) && sift chainG h))
    = true := by decide

-- kappa certificates: c_i ∈ C(g1) ∩ G conjugates g1*y_i to y_{sigma(i)}
theorem sigma_certs_ok :
    ((List.range 7).all (fun i =>
      (mul (sigmaCerts.getD i idP) g1 == mul g1 (sigmaCerts.getD i idP))
      && sift chainG (sigmaCerts.getD i idP)
      && (conjP (mul g1 (ys.getD i idP)) (sigmaCerts.getD i idP)
          == ys.getD (sigmaPerm.getD i 1 - 1) idP))) = true := by decide

-- sigma is the involution (1 2)(5 7) fixing 3,4,6 ----------------------
theorem sigma_shape : sigmaPerm = [2,1,3,4,7,6,5] := by decide

end M23
