module

public import GroupDimension.TraceReplay.PolyExact

@[expose] public section

/-!
# `checkPolyF` in pieces (MATH-314)

For the largest certificate (`c4m4_P6` at `n = 6`, |F| = 56, maps of weight 4) one `decide` of
`checkPolyF` needs more memory than a kimmy job has. `checkPolyF_of_split` gives `checkPolyF d n F P = true`
from pieces the kernel checks one at a time:

* the matrix `M = colMat d P.maps P.funcs F`, written out, one row per product (`colMat_of_forall₂`);
* the weights (`headOk`);
* `C · M = diag(D)` for the free columns in blocks `[s, s + m)` (`rowOkM`, joined by `allRange'_append`).

Nothing is assumed beyond these checks: they are the conjuncts of `checkPolyF` with `M` in place of the
matrix it computes.
-/

namespace GroupDimension.TraceReplay

/-- The weights in `checkPolyF`: every base map and every product has weight `< n`, indices valid. -/
def headOk (n : Nat) (P : PolyCert) : Bool :=
  P.maps.all (fun m => Nat.blt m.1 n) &&
  P.funcs.all (fun κ => κ.all (fun i => Nat.blt i P.maps.length) && Nat.blt (wt P.maps κ) n)

/-- Row `i` of `C · M = diag(D)` in `checkPolyF`, for a given matrix `M`. -/
def rowOkM (F : List Nat) (P : PolyCert) (M : List (List Int)) (i : Nat) : Bool :=
  decide ((P.rows.getD i ([], 0)).2 ≠ 0) &&
    (List.range F.length).all (fun j => decide (
      lsum P.funcs.length (fun k => (P.rows.getD i ([], 0)).1.getD k 0 * (M.getD k []).getD j 0) =
      if i = j then (P.rows.getD i ([], 0)).2 else 0))

theorem checkPolyF_eq (d n : Nat) [NeZero d] (F : List Nat) (P : PolyCert) :
    checkPolyF d n F P = (headOk n P && (List.range F.length).all (rowOkM F P (colMat d P.maps P.funcs F))) :=
  rfl

theorem colMat_of_forall₂ {d : Nat} [NeZero d] {maps : List (Nat × List Int)} {F : List Nat} :
    ∀ {funcs : List (List Nat)} {M : List (List Int)},
      List.Forall₂ (fun κ r => F.map (fun f => colValP d maps κ f) = r) funcs M → colMat d maps funcs F = M
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    simp only [colMat, List.map_cons] at *
    rw [h, colMat_of_forall₂ t]

theorem allRange'_append {p : Nat → Bool} {s m k : Nat} (h1 : (List.range' s m).all p = true)
    (h2 : (List.range' (s + m) k).all p = true) : (List.range' s (m + k)).all p = true := by
  simp only [List.all_eq_true, List.mem_range'_1] at *
  intro i hi
  by_cases h : i < s + m
  · exact h1 i ⟨hi.1, h⟩
  · exact h2 i ⟨by omega, by omega⟩

/-- `checkPolyF` from its pieces. -/
theorem checkPolyF_of_split {d n : Nat} [NeZero d] {F : List Nat} {P : PolyCert} {M : List (List Int)}
    (hM : colMat d P.maps P.funcs F = M) (hh : headOk n P = true)
    (hr : (List.range' 0 F.length).all (rowOkM F P M) = true) : checkPolyF d n F P = true := by
  rw [checkPolyF_eq, hM, hh, Bool.true_and, List.range_eq_range']
  exact hr

end GroupDimension.TraceReplay
