module

public import GroupDimension.Star.Row
public import GroupDimension.Star.VW

@[expose] public section

/-!
# The exact identity `(⋆)` (Theorem 6.11 of the paper, wiki page 891 §3; MATH-448)

`two_smul_gen_eq`: in a group of class `≤ 4`, for Tahara's data and any family `τ` satisfying
(A)–(F) (only (B), (D₂), (E), (F₂) are used), `2 A(g(τ)) = T₁ + T₂ + T₃ + T₄ + T₅` for every map
`A` additive on `γ₃`. Assembly as in `ExpThree.SetupB.two_smul_gen`: the rows of
`Star.row_exact` summed give `2 A(genA) = T₁ + T₂ + V - ∑ ⟨E^w⟩`, then `Star.v_exact` and
`Star.w_exact`.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- **`(⋆)`**: `2 A(g(τ)) = T₁ + T₂ + T₃ + T₄ + T₅`. -/
@[d5 "own:ab399" "the exact identity (⋆)"]
theorem two_smul_gen_eq {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (hv : T.Valid) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    (2 : ℤ) • A (T.gen τ) = T1 T τ A + T2 T τ A + T3 T τ A + T4 T τ A + T5 T τ A := by
  classical
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have x2mem : ∀ k, T.x₂ k ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := hv.basis₂.mem
  have x3mem : ∀ l, T.x₃ l ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hv.basis₃.mem
  have Y1 : ∀ h, T.x₁ h ^ T.d h ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    intro h
    have hm := hv.hb h
    have hP : oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h) ∈
        (⊤ : Subgroup G).lowerCentralSeries 1 :=
      mul_mem (oprod_mem x2mem _) (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _)
    rw [← mul_inv_cancel_left (oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h)) (T.x₁ h ^ T.d h)]
    exact mul_mem hP (lcs_mem_of_le (by norm_num) hm)
  have hY2 : ∀ i j, tc (T.x₁ i ^ T.d i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    fun i j => tc_mem (by omega) (Y1 i) (mem_lcs_zero _)
  have hfacA : ∀ i j, (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j)
      else 1) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    intro i j
    split_ifs
    · exact zpow_mem (hY2 i j) _
    · exact one_mem _
  have hrowA : ∀ i, (List.ofFn fun j => if i < j then
      tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := fun i =>
    list_prod_mem fun y hy => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact hfacA i j
  have hgA : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    unfold Data.genA
    exact list_prod_mem fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; exact hrowA i
  have hfacB : ∀ i k l, (if k < l then tc (T.x₂ l) (T.x₂ k) ^ T.b i l else 1) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i k l
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (x2mem l) (x2mem k)) _
    · exact one_mem _
  have hinnerB : ∀ i k, (List.ofFn fun l => if k < l then
      tc (T.x₂ l) (T.x₂ k) ^ T.b i l else 1).prod ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun i k => list_prod_mem fun y hy => by
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
      exact hfacB i k l
  have hrowB : ∀ i, (List.ofFn fun k => (List.ofFn fun l => if k < l then
      tc (T.x₂ l) (T.x₂ k) ^ T.b i l else 1).prod ^ τ.v i k).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun i =>
    list_prod_mem fun y hy => by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
      exact zpow_mem (hinnerB i k) _
  have hgB : T.genB τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    apply h32
    unfold Data.genB
    exact list_prod_mem fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; exact hrowB i
  have hfacC : ∀ i j k, (if i ≤ j ∧ j ≤ k then
      tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ^ τ.w i j k else 1) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i j k
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (hY2 i j) (mem_lcs_zero _)) _
    · exact one_mem _
  have hinnerC : ∀ i j, (List.ofFn fun k => if i ≤ j ∧ j ≤ k then
      tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ^ τ.w i j k else 1).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun i j =>
    list_prod_mem fun y hy => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact hfacC i j k
  have hrowC : ∀ i, (List.ofFn fun j => (List.ofFn fun k => if i ≤ j ∧ j ≤ k then
      tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ^ τ.w i j k else 1).prod).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun i =>
    list_prod_mem fun y hy => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact hinnerC i j
  have hgC : T.genC τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    apply h32
    unfold Data.genC
    exact list_prod_mem fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; exact hrowC i
  have hAgen : A (T.gen τ) = A (T.genA τ) + A (T.genB τ) + A (T.genC τ) := by
    rw [Data.gen, hA _ (mul_mem hgA hgB) _ hgC, hA _ hgA _ hgB]
  let a : Fin T.s → Fin T.s → N := fun h r => A (tc (T.x₁ h ^ T.d h) (T.x₁ r))
  let Uq : N := ∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) • a i j else 0
  let Up : N := ∑ r, ∑ h, if r < h then τ.u r h • a h r else 0
  let V : N := ∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r))
  let Cr : N := ∑ r, ∑ h, crow T τ r h • a h r
  let Rt : N := ∑ r, ∑ h, if h < r then (τ.u h r * T.q h r) •
    A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ r)) (T.x₁ r)) else 0
  let EwSum : N := ∑ r, ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r))
  have hAA : A (T.genA τ) = Uq := by
    simp only [Uq]
    unfold Data.genA
    rw [addMapG_ofFn hA _ hrowA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [addMapG_ofFn hA _ (hfacA i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact addMapG_zpow hA (hY2 i j) _
    · exact addMapG_one hA
  have hrows : V + Cr = Rt + EwSum := by
    simp only [V, Cr, Rt, EwSum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => row_exact h5 hv hτ hA r
  have hcrow : Cr = Up - A (T.genA τ) := by
    rw [hAA]
    simp only [Cr, Up, Uq]
    rw [Finset.sum_comm (f := fun i j => if i < j then (τ.u i j * T.q i j) • a i j else 0),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [crow, sub_smul]
    by_cases h1 : r < h <;> by_cases h2 : h < r <;>
      simp only [h1, h2, ↓reduceIte, zero_smul, sub_zero, zero_sub, sub_self]
  have hgA' : A (T.genA τ) = Up + V - Rt - EwSum := by
    have e : Up - A (T.genA τ) = Rt + EwSum - V := by
      calc
        Up - A (T.genA τ) = Cr := hcrow.symm
        _ = Rt + EwSum - V := by
          apply eq_sub_of_add_eq
          rw [add_comm]
          exact hrows
    calc
      A (T.genA τ) = Up - (Up - A (T.genA τ)) := by abel
      _ = Up - (Rt + EwSum - V) := by rw [e]
      _ = Up + V - Rt - EwSum := by abel
  have d_mul_q : ∀ {i j : Fin T.s}, i ≤ j → T.d i * (T.d j / T.d i) = T.d j := by
    intro i j hij
    exact Nat.mul_div_cancel' (hv.basis₁.dvd i j hij)
  have hpair : ∀ i j, i < j → (τ.u i j * T.q i j) • a i j + τ.u i j • a j i =
      τ.u i j • A (tc (T.x₁ i ^ T.d j) (T.x₁ j) * tc (T.x₁ j ^ T.d j) (T.x₁ i)) := by
    intro i j hij
    have e1 : T.x₁ i ^ T.d j = (T.x₁ i ^ T.d i) ^ (T.d j / T.d i) := by
      rw [← pow_mul, d_mul_q hij.le]
    have ht1 : tc (T.x₁ i ^ T.d j) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (by omega) (by rw [e1]; exact pow_mem (Y1 i) _) (mem_lcs_zero _)
    have ht2 : tc (T.x₁ j ^ T.d j) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hY2 j i
    have hA1 : A (tc (T.x₁ i ^ T.d j) (T.x₁ j)) = ((T.d j / T.d i : ℕ) : ℤ) • a i j := by
      rw [e1, tc_pow_left_L1 h5 (Y1 i), addMapG_pow hA (hY2 i j)]
    calc
      (τ.u i j * T.q i j) • a i j + τ.u i j • a j i =
          τ.u i j • (A (tc (T.x₁ i ^ T.d j) (T.x₁ j)) + A (tc (T.x₁ j ^ T.d j) (T.x₁ i))) := by
        rw [hA1, smul_add, mul_smul]
        rfl
      _ = τ.u i j • A (tc (T.x₁ i ^ T.d j) (T.x₁ j) * tc (T.x₁ j ^ T.d j) (T.x₁ i)) := by
        rw [hA _ ht1 _ ht2]
  have hpairs : Uq + Up = T1 T τ A := by
    simp only [Uq, Up, T1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · exact hpair i j hij
    · simp only [zero_add, zero_smul]
  have hRt : Rt = -T2 T τ A := by
    simp only [Rt, T2, neg_neg]
    rw [Finset.sum_comm]
  have hV : V + (2 : ℤ) • A (T.genB τ) = T5 T τ A := by
    simpa only [V] using v_exact h5 hv hτ hA
  have hW : (2 : ℤ) • A (T.genC τ) - EwSum = T3 T τ A + T4 T τ A := by
    simpa only [EwSum] using w_exact h5 hv hτ hA
  calc
    (2 : ℤ) • A (T.gen τ) = A (T.genA τ) + A (T.genA τ) +
        (2 : ℤ) • A (T.genB τ) + (2 : ℤ) • A (T.genC τ) := by
      rw [hAgen, smul_add, smul_add, two_smul]
    _ = Uq + (Up + V - Rt - EwSum) + (2 : ℤ) • A (T.genB τ) + (2 : ℤ) • A (T.genC τ) := by
      rw [← hAA, ← hgA']
    _ = (Uq + Up) + (V + (2 : ℤ) • A (T.genB τ)) +
        ((2 : ℤ) • A (T.genC τ) - EwSum) - Rt := by abel
    _ = T1 T τ A + T5 T τ A + (T3 T τ A + T4 T τ A) - -T2 T τ A := by
      rw [hpairs, hV, hW, hRt]
    _ = T1 T τ A + T2 T τ A + T3 T τ A + T4 T τ A + T5 T τ A := by abel

end Star

end GroupDimension
