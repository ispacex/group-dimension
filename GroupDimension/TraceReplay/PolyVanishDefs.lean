module

public import GroupDimension.TraceReplay.Check

@[expose] public section

/-!
# The kernel check of `Vanish`: the computable part (MATH-314)

The functions `checkVanish` runs (exact sparse vectors over `ℤ`, the truncated Magnus image of a relator,
`λ(X_U v X_V)` at positions), with no Mathlib import, so that data modules checked by `decide +kernel`
load little. Their meaning and the soundness proof (`vanish_of_check`) are in `PolyVanish.lean`.
-/

namespace GroupDimension.TraceReplay

/-! ## Exact sparse vectors (computable) -/

/-- A sparse integer vector: `(position, coefficient)`, positions as in `e`. -/
abbrev VecZ := List (Nat × Int)

/-- Merge two vectors sorted by position, adding equal positions and dropping zero sums. When the
fuel runs out the rest is appended, which is still the sum (sorting only matters for speed). -/
def mergeZ : Nat → VecZ → VecZ → VecZ
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a :: as, [] => a :: as
  | n + 1, (i, x) :: a, (j, y) :: b =>
    bif Nat.blt i j then (i, x) :: mergeZ n a ((j, y) :: b)
    else bif Nat.blt j i then (j, y) :: mergeZ n ((i, x) :: a) b
    else bif x + y == 0 then mergeZ n a b else (i, x + y) :: mergeZ n a b

/-- `x · (a' X_{c'})` below degree `k`, where `c'` has degree `h` and index `i'`. -/
def shiftZ (d k h i' : Nat) (a' : Int) : VecZ → VecZ
  | [] => []
  | t :: x =>
    bif Nat.blt (degOf d t.1 + h) k then
      (off d (degOf d t.1 + h) + (t.1 - off d (degOf d t.1)) * d ^ h + i', t.2 * a') :: shiftZ d k h i' a' x
    else shiftZ d k h i' a' x

/-- `x · y` below degree `k`. -/
def mulZ (d k : Nat) (x y : VecZ) : VecZ :=
  y.foldl (fun acc t => mergeZ (acc.length + x.length) acc
    (shiftZ d k (degOf d t.1) (t.1 - off d (degOf d t.1)) t.2 x)) []

/-- The index of `X_j^m` within degree `m`. -/
def jIdx (d j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => jIdx d j m * d + j

/-- `Σ_{m<k} C(e, m) X_j^m`. -/
def sVec (d j : Nat) (ex : Int) : Nat → VecZ
  | 0 => []
  | k + 1 => sVec d j ex k ++ (bif binom ex k == 0 then [] else [(off d k + jIdx d j k, binom ex k)])

/-- `μ(w)` of a flat word below degree `k` (generators `1..d`, read modulo `d` as in `gword`). -/
def magnusW (d k : Nat) (w : List (Nat × Int)) : VecZ :=
  w.foldl (fun x f => mulZ d k x (sVec d ((f.1 - 1) % d) f.2 k)) [(0, 1)]

/-- `acc · b^n` by repeated squaring (`fuel` steps at most). -/
def powZ (d k : Nat) : Nat → VecZ → VecZ → Nat → VecZ
  | 0, acc, _, _ => acc
  | f + 1, acc, b, n =>
    bif n == 0 then acc
    else powZ d k f (bif n % 2 == 1 then mulZ d k acc b else acc) (mulZ d k b b) (n / 2)

/-- The inverse of a flat word. -/
def invW (w : List (Nat × Int)) : List (Nat × Int) := w.reverse.map fun f => (f.1, -f.2)

/-- `μ(r)` below degree `k` for a relator `r = Π w_i^{k_i}`. -/
def magnusN (d k : Nat) (r : List (List (Nat × Int) × Int)) : VecZ :=
  r.foldl (fun acc f => mulZ d k acc
    (powZ d k f.2.natAbs [(0, 1)] (magnusW d k (bif decide (f.2 < 0) then invW f.1 else f.1)) f.2.natAbs))
    [(0, 1)]

/-- The position of `X_c X_{c'}`. -/
def posMul (d c c' : Nat) : Nat :=
  off d (degOf d c + degOf d c') + (c - off d (degOf d c)) * d ^ degOf d c' + (c' - off d (degOf d c'))

/-- `λ` on the monomial at position `p` (degrees `1..w`, else `0`). -/
def lamPos (d : Nat) (m : Nat × List Int) (p : Nat) : Int :=
  bif Nat.blt 0 (degOf d p) && Nat.ble (degOf d p) m.1 then m.2.getD (p - 1) 0 else 0

/-- `λ(X_U v X_V)`, `U` the word of length `a` and index `u`, `V` of length `b` and index `vv`. -/
def vanVal (d : Nat) (m : Nat × List Int) (v : VecZ) (a u b vv : Nat) : Int :=
  v.foldl (fun s t => s + t.2 * lamPos d m (posMul d (posMul d (off d a + u) t.1) (off d b + vv))) 0

/-- `v − 1`. -/
def subOne (v : VecZ) : VecZ := mergeZ (v.length + 1) v [(0, -1)]

/-- The terms with their degree and index: `(g, i, c)` for `c · X` at position `off g + i`. -/
def withDeg (d : Nat) (v : VecZ) : List (Nat × Nat × Int) :=
  v.map fun t => (degOf d t.1, t.1 - off d (degOf d t.1), t.2)

/-- `vanVal` on the terms with degrees (the position of `X_U X_c X_V` by arithmetic, `vanValD_eq`). -/
def vanValD (d : Nat) (m : Nat × List Int) (vd : List (Nat × Nat × Int)) (a u b vv : Nat) : Int :=
  vd.foldl (fun s t =>
    bif Nat.blt 0 (a + t.1 + b) && Nat.ble (a + t.1 + b) m.1 then
      s + t.2.2 * m.2.getD (off d (a + t.1 + b) + (u * d ^ t.1 + t.2.1) * d ^ b + vv - 1) 0
    else s) 0

/-- Check 1 for one map, given `vd = withDeg (μ(r) − 1)`: `λ(X_U (μ(r) − 1) X_V) = 0` for
`|U| + |V| ≤ w − 1`. -/
def checkMap (d : Nat) (m : Nat × List Int) (vd : List (Nat × Nat × Int)) : Bool :=
  (List.range m.1).all fun a => (List.range (m.1 - a)).all fun b =>
    (List.range (d ^ a)).all fun u => (List.range (d ^ b)).all fun vv => vanValD d m vd a u b vv == 0

/-- Check 1 for one relator and all maps, `μ(r)` computed once below degree `K` (`K > w` for every
map). -/
def checkVanishRel (d K : Nat) (maps : List (Nat × List Int)) (r : List (List (Nat × Int) × Int)) : Bool :=
  let vd := withDeg d (subOne (magnusN d K r))
  maps.all fun m => Nat.ble (m.1 + 1) K && checkMap d m vd

/-- Check 1 for all maps against all relators. -/
def checkVanish (d K : Nat) (maps : List (Nat × List Int)) (rels : List (List (List (Nat × Int) × Int))) :
    Bool :=
  rels.all fun r => checkVanishRel d K maps r

/-- A relator written out as a flat word (each factor `(w, k)` as `w^k`, `w⁻¹^|k|` for `k < 0`). -/
def expandRel (r : List (List (Nat × Int) × Int)) : List (Nat × Int) :=
  r.flatMap fun f => (List.replicate f.2.natAbs (bif decide (f.2 < 0) then invW f.1 else f.1)).flatten

/-- `checkVanish` over a concatenation. -/
theorem checkVanish_append {d K : Nat} {maps : List (Nat × List Int)} {a b : List (List (List (Nat × Int) × Int))}
    (ha : checkVanish d K maps a = true) (hb : checkVanish d K maps b = true) :
    checkVanish d K maps (a ++ b) = true := by
  simp only [checkVanish, List.all_append, Bool.and_eq_true] at *
  exact ⟨ha, hb⟩

end GroupDimension.TraceReplay
