/- The single big-enumeration certificate, one `native_decide` (trusts the
   compiler; quarantined here). Materializes cls(g2), cls(g3) (443,520
   each), Y (18,816), and the seven C-orbits; checks sizes, disjointness,
   coverage. Conservative core API (Lean 4.15 Std.HashSet). -/

import M23.Data
import Std.Data.HashSet

open Std (HashSet)

namespace M23

/-- pack a perm into a Nat for hashing/equality (base-23 digits) -/
def enc (p : P) : Nat := p.foldr (fun d acc => acc * 23 + d) 0

structure BfsState where
  seen : HashSet Nat
  acc  : List P

/-- BFS layers with a per-neighbor expansion function; fuel ≥ diameter -/
def bfsGo (nbrs : P → List P) : Nat → BfsState → List P → BfsState
  | 0, st, _ => st
  | _, st, [] => st
  | Nat.succ f, st, fr =>
    let step := fr.foldl (init := (st, ([] : List P))) fun acc u =>
      (nbrs u).foldl (init := acc) fun acc2 v =>
        let e := enc v
        if acc2.fst.seen.contains e then acc2
        else ({ seen := acc2.fst.seen.insert e, acc := v :: acc2.fst.acc },
              v :: acc2.snd)
    bfsGo nbrs f step.fst step.snd

/-- BFS conjugation orbit of x under gens -/
def conjOrbit (x : P) (gens : List P) (fuel : Nat) : BfsState :=
  let gpairs := gens.map (fun g => (inv g, g))
  bfsGo (fun u => gpairs.map (fun gp => mul (mul gp.fst u) gp.snd))
        fuel { seen := (HashSet.empty.insert (enc x)), acc := [x] } [x]

/-- group closure under right multiplication; fuel-bounded -/
def closure (gens : List P) (fuel : Nat) : BfsState :=
  go fuel { seen := (HashSet.empty.insert (enc idP)), acc := [idP] } [idP]
where
  go : Nat → BfsState → List P → BfsState
    | 0, st, _ => st
    | _, st, [] => st
    | Nat.succ f, st, fr =>
      let step := fr.foldl (init := (st, ([] : List P))) fun acc u =>
        gens.foldl (init := acc) fun (s, nf) g =>
          let v := mul u g
          let e := enc v
          if s.seen.contains e then (s, nf)
          else ({ seen := s.seen.insert e, acc := v :: s.acc }, v :: nf)
      go f step.fst step.snd

def bigCheck : Bool := Id.run do
  let oY := conjOrbit g2 [g1, g2] 1000
  let oZ := conjOrbit g3 [g1, g2] 1000
  let oC := closure hGens 1000
  if oC.acc.length != 2688 then return false
  if oY.acc.length != 443520 then return false
  if oZ.acc.length != 443520 then return false
  let Y := oY.acc.filter (fun y => oZ.seen.contains (enc (inv (mul g1 y))))
  if Y.length != 18816 then return false
  let setY : HashSet Nat := Y.foldl (fun s y => s.insert (enc y)) HashSet.empty
  let mut union : HashSet Nat := HashSet.empty
  let mut total := 0
  for y in ys do
    let ob := conjOrbit y hGens 1000
    if ob.acc.length != 2688 then return false
    for v in ob.acc do
      let e := enc v
      if union.contains e then return false        -- disjointness
      if !(setY.contains e) then return false      -- orbit ⊆ Y
      union := union.insert e
    total := total + ob.acc.length
  if total != 18816 then return false
  if union.size != 18816 then return false
  return true

theorem census_native : bigCheck = true := by native_decide

end M23
