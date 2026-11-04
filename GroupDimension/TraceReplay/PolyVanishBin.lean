module

public import GroupDimension.TraceReplay.PolyVanishDefs

@[expose] public section

/-!
# `checkVanish` with powers by the binomial series (MATH-314)

`checkVanishB` is `checkVanish` (PolyVanishDefs.lean) with each factor `w^e` of a relator computed as
`Σ_{m<K} C(e, m) (μ(w) − 1)^m` (`powB`): `μ(w) − 1` has no constant term, so its `K`-th power is `0` below
degree `K`, and the series is exact for every `e ∈ ℤ`. That takes `K − 2` products where squaring takes
about `2 log₂ |e|` of them (a factor `u^2048` with `K = 5`, `d = 6`: 3 against 22 products of vectors with
up to 1555 terms). Computable, no Mathlib import; soundness `vanish_of_checkB` in PolyVanish.lean.
-/

namespace GroupDimension.TraceReplay

/-- `c · v`. -/
def scaleZ (c : Int) (v : VecZ) : VecZ := v.map fun t => (t.1, c * t.2)

/-- `acc + Σ_{i ∈ [m, m + f)} C(e, i) y^i`, given `ym = y^m`, below degree `K`. -/
def powBAux (d K : Nat) (y : VecZ) (e : Int) : Nat → VecZ → VecZ → Nat → VecZ
  | 0, acc, _, _ => acc
  | f + 1, acc, ym, m =>
    powBAux d K y e f
      (bif binom e m == 0 then acc else mergeZ (acc.length + ym.length) acc (scaleZ (binom e m) ym))
      (mulZ d K ym y) (m + 1)

/-- `Σ_{m<K} C(e, m) y^m` below degree `K`. -/
def powB (d K : Nat) (y : VecZ) (e : Int) : VecZ := powBAux d K y e (K - 1) [(0, 1)] y 1

/-- `μ(r)` below degree `K`, each factor `w^e` by the binomial series. -/
def magnusNB (d K : Nat) (r : List (List (Nat × Int) × Int)) : VecZ :=
  r.foldl (fun acc f => mulZ d K acc (powB d K (subOne (magnusW d K f.1)) f.2)) [(0, 1)]

/-- `checkVanishRel` with `magnusNB`. -/
def checkVanishRelB (d K : Nat) (maps : List (Nat × List Int)) (r : List (List (Nat × Int) × Int)) : Bool :=
  let vd := withDeg d (subOne (magnusNB d K r))
  maps.all fun m => Nat.ble (m.1 + 1) K && checkMap d m vd

/-- `checkVanish` with `magnusNB`. -/
def checkVanishB (d K : Nat) (maps : List (Nat × List Int)) (rels : List (List (List (Nat × Int) × Int))) :
    Bool :=
  rels.all fun r => checkVanishRelB d K maps r

/-- `checkVanishB` over a concatenation. -/
theorem checkVanishB_append {d K : Nat} {maps : List (Nat × List Int)}
    {a b : List (List (List (Nat × Int) × Int))}
    (ha : checkVanishB d K maps a = true) (hb : checkVanishB d K maps b = true) :
    checkVanishB d K maps (a ++ b) = true := by
  simp only [checkVanishB, List.all_append, Bool.and_eq_true] at *
  exact ⟨ha, hb⟩

end GroupDimension.TraceReplay
