/- Verified Sims (BSGS) certificate checker. See README for the format.
   All Bool, decidable; conservative core API. -/

import M23.Defs

namespace M23

structure Level where
  base   : Nat
  sgens  : List P
  transv : List (Nat × P)     -- (point, perm with ap perm base = point)

abbrev Chain := List Level

def transvLookup (L : Level) (q : Nat) : Option P :=
  (L.transv.find? (fun e => e.fst == q)).map (fun e => e.snd)

/-- sift w through the chain; true iff it reduces to the identity -/
def sift : Chain → P → Bool
  | [], w => w == idP
  | L :: rest, w =>
    match transvLookup L (ap w L.base) with
    | none => false
    | some t => sift rest (mul (inv t) w)

def fixesAll (p : P) (pts : List Nat) : Bool :=
  pts.all (fun b => ap p b == b)

def checkLevel (prevBases : List Nat) (L : Level) (rest : Chain) : Bool :=
  L.sgens.all (fun s => fixesAll s prevBases) &&
  nodupB (L.transv.map (fun e => e.fst)) &&
  L.transv.any (fun e => e.fst == L.base && e.snd == idP) &&
  L.transv.all (fun e => ap e.snd L.base == e.fst) &&
  L.transv.all (fun e =>
    L.sgens.all (fun s =>
      match transvLookup L (ap s e.fst) with
      | none => false
      | some t' =>
        -- Schreier element t'⁻¹ * s * t fixes the base and must sift
        -- through the stabilizer chain (rest) to the identity:
        sift rest (mul (inv t') (mul s e.snd))))

def checkLevels : List Nat → Chain → Bool
  | _, [] => true
  | prevBases, L :: rest =>
    checkLevel prevBases L rest && checkLevels (prevBases ++ [L.base]) rest

def checkChain (gens : List P) (ch : Chain) : Bool :=
  gens.all (fun g => sift ch g) &&
  (match ch with
   | [] => gens.all (fun g => g == idP)
   | L :: _ => gens.all (fun g => L.sgens.contains g)) &&
  checkLevels [] ch

def chainOrder (ch : Chain) : Nat :=
  ch.foldl (fun acc L => acc * L.transv.length) 1

end M23
