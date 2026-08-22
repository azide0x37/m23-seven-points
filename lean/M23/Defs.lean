/- M23 census formalization: core definitions.
   Mathlib-free, conservative Lean 4.15 core API only.
   Permutations of {0..22} as `List Nat` image lists (length 23). -/

namespace M23

abbrev P := List Nat          -- permutation as image list

def n : Nat := 23

def isPerm (p : P) : Bool :=
  p.length == n && (List.range n).all (fun i => p.contains i)

def idP : P := List.range n

/-- apply p to a point -/
def ap (p : P) (i : Nat) : Nat := p.getD i 0

/-- composition: (mul p q) i = p (q i)  (campaign's mm(p,q) = p∘q) -/
def mul (p q : P) : P := q.map (fun i => ap p i)

def inv (p : P) : P :=
  (List.range n).map (fun i => p.findIdx (fun x => x == i))

/-- conjugation c⁻¹ p c (campaign convention conj(g,c) = c⁻¹gc) -/
def conjP (p c : P) : P := mul (mul (inv c) p) c

def powP (p : P) (k : Nat) : P :=
  (List.range k).foldl (fun acc _ => mul acc p) idP

def orderDivides (p : P) (k : Nat) : Bool := powP p k == idP

def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupB xs

end M23
