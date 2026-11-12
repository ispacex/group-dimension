module

public import GroupDimension.Star.VWAux

@[expose] public section

/-!
# `(⋆)`, Lemmas 2 and 3: exact identities (MATH-448)

Wiki page 891, §3, with no condition on the exponent of `γ₄`.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- **Lemma 2, exact.** K3 followed by `(F₂)` with its true moduli. -/
theorem v_exact {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (hv : T.Valid)
    {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    ∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) + (2 : ℤ) • A (T.genB τ) =
      T5 T τ A := by
  classical
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have x2mem : ∀ k, T.x₂ k ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := hv.basis₂.mem
  have x3mem : ∀ l, T.x₃ l ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hv.basis₃.mem
  have Y1 : ∀ r, T.x₁ r ^ T.d r ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    intro r
    have hm := hv.hb r
    have hP : oprod T.x₂ (T.b r) * oprod T.x₃ (T.c r) ∈
        (⊤ : Subgroup G).lowerCentralSeries 1 :=
      mul_mem (oprod_mem x2mem _) (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _)
    rw [← mul_inv_cancel_left (oprod T.x₂ (T.b r) * oprod T.x₃ (T.c r)) (T.x₁ r ^ T.d r)]
    exact mul_mem hP (lcs_mem_of_le (by norm_num) hm)
  have x2e : ∀ k, T.x₂ k ^ T.e k ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    intro k
    have hm := hv.hdd k
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.dd k)) (T.x₂ k ^ T.e k)]
    exact mul_mem (oprod_mem x3mem _) (lcs_mem_of_le (by norm_num) hm)
  have hcomm : ∀ l k, tc (T.x₂ l) (T.x₂ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun l k => tc_mem (i := 1) (j := 1) (by omega) (x2mem l) (x2mem k)
  have hKpoint : ∀ r k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) =
      τ.v r k • A (tc (T.x₂ k) (T.x₁ r ^ T.d r)) -
        (τ.v r k * T.ch r 2) • A (tc (tc (T.x₂ k) (T.x₁ r)) (T.x₁ r)) := by
    intro r k
    have hc2 : tc (T.x₂ k) (T.x₁ r) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (by omega) (x2mem k) (mem_lcs_zero _)
    have ht3 : tc (tc (T.x₂ k) (T.x₁ r)) (T.x₁ r) ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (by omega) hc2 (mem_lcs_zero _)
    have he : A (tc (T.x₂ k) (T.x₁ r ^ T.d r)) = (T.d r : ℤ) • A (tc (T.x₂ k) (T.x₁ r)) +
        T.ch r 2 • A (tc (tc (T.x₂ k) (T.x₁ r)) (T.x₁ r)) := by
      rw [tc_pow_right_K3 (x2mem k) h5, hA _ (lcs_mem_of_le (by norm_num) (pow_mem hc2 _))
        _ (lcs_mem_of_le (by norm_num) (pow_mem ht3 _)),
        addMapG_pow hA (lcs_mem_of_le (by norm_num) hc2),
        addMapG_pow hA (lcs_mem_of_le (by norm_num) ht3)]
      rfl
    calc
      (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) =
          τ.v r k • ((T.d r : ℤ) • A (tc (T.x₂ k) (T.x₁ r))) := by rw [smul_smul]
      _ = τ.v r k • (A (tc (T.x₂ k) (T.x₁ r ^ T.d r)) -
          T.ch r 2 • A (tc (tc (T.x₂ k) (T.x₁ r)) (T.x₁ r))) := by rw [he]; abel
      _ = _ := by rw [smul_sub, smul_smul]
  let γ : Fin T.t → Fin T.t → N := fun l k => A (tc (T.x₂ l) (T.x₂ k))
  let Nc : Fin T.t → Fin T.t → ℤ := fun l k => ∑ r, τ.v r k * T.b r l
  let β : Fin T.s → Fin T.t → N := fun r k => A (tc (T.x₁ r ^ T.d r) (T.x₂ k))
  have hβ : ∀ r k, β r k = ∑ l, T.b r l • γ l k := by
    intro r k
    exact map_Y_expand_vw h5 hv hA r (x2mem k)
  have hleft : ∀ r k, A (tc (T.x₂ k) (T.x₁ r ^ T.d r)) = -β r k := by
    intro r k
    have hm : tc (T.x₂ k) (T.x₁ r ^ T.d r) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 1) (j := 1) (by omega) (x2mem k) (Y1 r)
    change A (tc (T.x₂ k) (T.x₁ r ^ T.d r)) = -A (tc (T.x₁ r ^ T.d r) (T.x₂ k))
    have hs : A (tc (T.x₂ k) (T.x₁ r ^ T.d r)) +
        A (tc (T.x₁ r ^ T.d r) (T.x₂ k)) = 0 := by
      rw [← tc_inv (T.x₂ k) (T.x₁ r ^ T.d r)]
      rw [← hA _ (h32 hm) _ (inv_mem (h32 hm)), mul_inv_cancel, addMapG_one hA]
    apply sub_eq_zero.mp
    simp only [sub_neg_eq_add]
    exact hs
  have hγ0 : ∀ k, γ k k = 0 := by
    intro k
    change A (tc (T.x₂ k) (T.x₂ k)) = 0
    rw [show tc (T.x₂ k) (T.x₂ k) = 1 by simp [tc], addMapG_one hA]
  have hγanti : ∀ l k, γ l k + γ k l = 0 := by
    intro l k
    simp only [γ]
    rw [← tc_inv (T.x₂ k) (T.x₂ l), addMapG_inv hA (h32 (hcomm k l)), neg_add_cancel]
  have heγ : ∀ l k, (T.e k : ℤ) • γ l k = 0 := by
    intro l k
    have hm := addMapG_pow hA (h32 (hcomm l k)) (T.e k)
    have hone : tc (T.x₂ l) (T.x₂ k ^ T.e k) = 1 := by
      rw [← tc_inv, tc_L2_L1 h5 (x2e k) (x2mem l), inv_one]
    rw [← tc_pow_right_L1 h5 (x2mem l) (x2mem k), hone, addMapG_one hA] at hm
    simpa only [γ] using hm.symm
  have hcond0 : ∀ {l k}, k < l → (Nc l k + Nc k l) • γ l k = 0 := by
    intro l k hkl
    obtain ⟨q, hq⟩ := Int.modEq_zero_iff_dvd.mp (hτ.F₂ k l hkl)
    have hq' : Nc l k + Nc k l = (T.e k : ℤ) * q := by simpa only [Nc] using hq
    rw [hq', show ((T.e k : ℤ) * q) • γ l k = q • ((T.e k : ℤ) • γ l k) by
      rw [smul_smul, mul_comm], heγ, smul_zero]
  have hcond : ∀ l k, (Nc l k + Nc k l) • γ l k = 0 := by
    intro l k
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · exact hcond0 hkl
    · simp only [hγ0, smul_zero]
    · have hs := hcond0 hlk
      rw [add_comm (Nc k l) (Nc l k)] at hs
      have hg : γ l k = -γ k l := eq_neg_of_add_eq_zero_right (hγanti k l)
      rw [hg, smul_neg, neg_eq_zero]
      exact hs
  have hβsum : (∑ r, ∑ k, τ.v r k • β r k) = ∑ l, ∑ k, Nc l k • γ l k := by
    calc
      _ = ∑ r, ∑ k, ∑ l, (τ.v r k * T.b r l) • γ l k := by
        simp_rw [hβ, Finset.smul_sum, smul_smul]
      _ = ∑ r, ∑ l, ∑ k, (τ.v r k * T.b r l) • γ l k :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ l, ∑ r, ∑ k, (τ.v r k * T.b r l) • γ l k := Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ r, (τ.v r k * T.b r l) • γ l k :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = _ := by simp only [Nc, Finset.sum_smul, smul_smul]
  have hS : (∑ r, ∑ k, τ.v r k • A (tc (T.x₂ k) (T.x₁ r ^ T.d r))) =
      -∑ l, ∑ k, Nc l k • γ l k := by
    calc
      _ = ∑ r, ∑ k, -(τ.v r k • β r k) := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
        rw [hleft, smul_neg]
      _ = -∑ r, ∑ k, τ.v r k • β r k := by simp only [Finset.sum_neg_distrib]
      _ = _ := by rw [hβsum]
  have hfac : ∀ r k l, (if k < l then tc (T.x₂ l) (T.x₂ k) ^ T.b r l else 1) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro r k l
    split_ifs
    · exact zpow_mem (hcomm l k) _
    · exact one_mem _
  have hinner : ∀ r k, (List.ofFn fun l => if k < l then
      tc (T.x₂ l) (T.x₂ k) ^ T.b r l else 1).prod ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun r k => list_prod_mem fun y hy => by obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy; exact hfac r k l
  have hrow : ∀ r, (List.ofFn fun k => (List.ofFn fun l => if k < l then
      tc (T.x₂ l) (T.x₂ k) ^ T.b r l else 1).prod ^ τ.v r k).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun r =>
    list_prod_mem fun y hy => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact zpow_mem (hinner r k) _
  have hB0 : A (T.genB τ) = ∑ r, ∑ k, τ.v r k • ∑ l,
      (if k < l then T.b r l • γ l k else 0) := by
    unfold Data.genB
    rw [addMapG_ofFn hA _ (fun r => h32 (hrow r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [addMapG_ofFn hA _ (fun k => h32 (zpow_mem (hinner r k) _))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [addMapG_zpow hA (h32 (hinner r k)), addMapG_ofFn hA _ (fun l => h32 (hfac r k l))]
    refine congrArg (τ.v r k • ·) (Finset.sum_congr rfl fun l _ => ?_)
    split_ifs
    · exact addMapG_zpow hA (h32 (hcomm l k)) _
    · exact addMapG_one hA
  have hB : A (T.genB τ) = ∑ l, ∑ k, if k < l then Nc l k • γ l k else 0 := by
    rw [hB0]
    calc
      _ = ∑ r, ∑ k, ∑ l, if k < l then (τ.v r k * T.b r l) • γ l k else 0 := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs <;> simp only [smul_smul, zero_smul, smul_zero]
      _ = ∑ r, ∑ l, ∑ k, if k < l then (τ.v r k * T.b r l) • γ l k else 0 :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ l, ∑ r, ∑ k, if k < l then (τ.v r k * T.b r l) • γ l k else 0 := Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ r, if k < l then (τ.v r k * T.b r l) • γ l k else 0 :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
        by_cases hkl : k < l
        · simp only [hkl, if_true, Nc, Finset.sum_smul, smul_smul]
        · simp only [hkl, if_false, Finset.sum_const_zero, zero_smul]
  have hSkew := sum_skew_exact_vw Nc γ hγ0 hγanti hcond
  have hV0 : (∑ r, ∑ k, τ.v r k • A (tc (T.x₂ k) (T.x₁ r ^ T.d r))) +
      (2 : ℤ) • A (T.genB τ) = 0 := by
    rw [hB, hS, hSkew, neg_add_cancel]
  let R : N := ∑ r, ∑ k, (τ.v r k * T.ch r 2) •
    A (tc (tc (T.x₂ k) (T.x₁ r)) (T.x₁ r))
  have hKsum : (∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r))) =
      (∑ r, ∑ k, τ.v r k • A (tc (T.x₂ k) (T.x₁ r ^ T.d r))) - R := by
    simp only [R, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => hKpoint r k
  calc
    _ = (∑ r, ∑ k, τ.v r k • A (tc (T.x₂ k) (T.x₁ r ^ T.d r))) +
        (2 : ℤ) • A (T.genB τ) - R := by rw [hKsum]; abel
    _ = -R := by rw [hV0, zero_sub]
    _ = T5 T τ A := by simp only [T5, R, Finset.sum_neg_distrib]

/-- Condition `D₂`, paired with `ω(x₂ₘ, cⱼₖ)` and summed over `m`. -/
private theorem d2_exact_vw {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (hv : T.Valid) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    {j k : Fin T.s} (hjk : j < k) :
    (∑ g, if g ≤ j then τ.w g j k • A (tc (T.x₁ g ^ T.d g) (tc (T.x₁ j) (T.x₁ k))) else 0) +
      (∑ g, if j < g ∧ g ≤ k then
        τ.w' j g k • A (tc (T.x₁ g ^ T.d g) (tc (T.x₁ j) (T.x₁ k))) else 0) +
      (∑ g, if k < g then
        τ.w'' j k g • A (tc (T.x₁ g ^ T.d g) (tc (T.x₁ j) (T.x₁ k))) else 0) = 0 := by
  classical
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have x2mem : ∀ m, T.x₂ m ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := hv.basis₂.mem
  have x2e : ∀ k, T.x₂ k ^ T.e k ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    intro m
    have hm := hv.hdd m
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.dd m)) (T.x₂ m ^ T.e m)]
    exact mul_mem (oprod_mem hv.basis₃.mem _) (lcs_mem_of_le (by norm_num) hm)
  have hc1 : tc (T.x₁ j) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := tc_mem_L1_vw _ _
  let Γ : Fin T.t → N := fun m => A (tc (T.x₂ m) (tc (T.x₁ j) (T.x₁ k)))
  let ω : Fin T.s → N := fun g => A (tc (T.x₁ g ^ T.d g) (tc (T.x₁ j) (T.x₁ k)))
  have hω : ∀ g, ω g = ∑ m, T.b g m • Γ m := by
    intro g
    exact map_Y_expand_vw h5 hv hA g hc1
  have hΓmem : ∀ m, tc (T.x₂ m) (tc (T.x₁ j) (T.x₁ k)) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun m =>
    tc_mem (i := 1) (j := 1) (by omega) (x2mem m) hc1
  have heΓ : ∀ m, (T.e m : ℤ) • Γ m = 0 := by
    intro m
    have hm := addMapG_pow hA (h32 (hΓmem m)) (T.e m)
    have hone : tc (T.x₂ m ^ T.e m) (tc (T.x₁ j) (T.x₁ k)) = 1 :=
      tc_L2_L1 h5 (x2e m) hc1
    rw [← tc_pow_left_L1 h5 (x2mem m), hone, addMapG_one hA] at hm
    simpa only [Γ] using hm.symm
  have hdΓ : ∀ m, (T.d j : ℤ) • Γ m = 0 := by
    intro m
    have hm := addMapG_pow hA (h32 (hΓmem m)) (T.d j)
    have hone : tc (T.x₂ m) (tc (T.x₁ j) (T.x₁ k) ^ T.d j) = 1 := by
      rw [← tc_inv, tc_L2_L1 h5 (tc_c_d_mem_vw h5 hv j k) (x2mem m), inv_one]
    rw [← tc_pow_right_L1 h5 (x2mem m) hc1, hone, addMapG_one hA] at hm
    simpa only [Γ] using hm.symm
  have hgcd : ∀ m, (Nat.gcd (T.d j) (T.e m) : ℤ) • Γ m = 0 := by
    intro m
    rw [Nat.gcd_eq_gcd_ab, add_smul, mul_comm (T.d j : ℤ), mul_smul,
      mul_comm (T.e m : ℤ), mul_smul, hdΓ, heΓ, smul_zero, smul_zero, add_zero]
  have hpoint : ∀ m, ((∑ g, if g ≤ j then τ.w g j k * T.b g m else 0) +
      (∑ g, if j < g ∧ g ≤ k then τ.w' j g k * T.b g m else 0) +
      (∑ g, if k < g then τ.w'' j k g * T.b g m else 0)) • Γ m = 0 := by
    intro m
    obtain ⟨q, hq⟩ := Int.modEq_zero_iff_dvd.mp (hτ.D₂ j k m hjk)
    have hq' : (∑ g, if g ≤ j then τ.w g j k * T.b g m else 0) +
        (∑ g, if j < g ∧ g ≤ k then τ.w' j g k * T.b g m else 0) +
        (∑ g, if k < g then τ.w'' j k g * T.b g m else 0) =
        (Nat.gcd (T.d j) (T.e m) : ℤ) * q := by simpa only using hq
    rw [hq', show ((Nat.gcd (T.d j) (T.e m) : ℤ) * q) • Γ m =
      q • ((Nat.gcd (T.d j) (T.e m) : ℤ) • Γ m) by rw [smul_smul, mul_comm],
      hgcd, smul_zero]
  have hzero : (∑ m, ((∑ g, if g ≤ j then τ.w g j k * T.b g m else 0) • Γ m +
      (∑ g, if j < g ∧ g ≤ k then τ.w' j g k * T.b g m else 0) • Γ m +
      (∑ g, if k < g then τ.w'' j k g * T.b g m else 0) • Γ m)) = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← add_smul, ← add_smul]
    exact hpoint m
  rw [← sum_cond_contract_vw (fun g => g ≤ j) (fun g => τ.w g j k) T.b Γ ω hω,
    ← sum_cond_contract_vw (fun g => j < g ∧ g ≤ k) (fun g => τ.w' j g k) T.b Γ ω hω,
    ← sum_cond_contract_vw (fun g => k < g) (fun g => τ.w'' j k g) T.b Γ ω hω,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact hzero

/-- **Lemma 3, exact.** -/
theorem w_exact {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (hv : T.Valid)
    {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    (2 : ℤ) • A (T.genC τ) - ∑ r, ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r)) =
      T3 T τ A + T4 T τ A := by
  classical
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  let η : Fin T.s → Fin T.s → Fin T.s → N := fun g j k =>
    A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ j)) (T.x₁ k))
  let ω : Fin T.s → Fin T.s → Fin T.s → N := fun g j k =>
    A (tc (T.x₁ g ^ T.d g) (tc (T.x₁ j) (T.x₁ k)))
  let W0 : N := ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h • η g r h else 0
  let E1 : N := ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h • η g h r else 0
  let E3 : N := ∑ r, ∑ h, ∑ g, if r < g ∧ g ≤ h then τ.w' r g h • η g h r else 0
  let E3n : N := ∑ r, ∑ h, ∑ g, if r < g ∧ g ≤ h then τ.w' r g h • η g r h else 0
  let DL : N := ∑ r, ∑ h, ∑ g, if g ≤ r ∧ r < h then τ.w g r h • ω g r h else 0
  let DM : N := ∑ r, ∑ h, ∑ g, if r < g ∧ g ≤ h ∧ r < h then τ.w' r g h • ω g r h else 0
  let DR : N := ∑ r, ∑ h, ∑ g, if r < h ∧ h < g then τ.w'' r h g • ω g r h else 0
  have hmemC : ∀ g j k, tc (tc (T.x₁ g ^ T.d g) (T.x₁ j)) (T.x₁ k) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro g j k
    exact tc_mem (i := 2) (j := 0) (by omega)
      (tc_mem (i := 1) (j := 0) (by omega) (mem_Y_vw hv g) (mem_lcs_zero _)) (mem_lcs_zero _)
  have hfacC : ∀ g r h, (if g ≤ r ∧ r ≤ h then
      tc (tc (T.x₁ g ^ T.d g) (T.x₁ r)) (T.x₁ h) ^ τ.w g r h else 1) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro g r h
    split_ifs
    · exact zpow_mem (hmemC g r h) _
    · exact one_mem _
  have hinnerC : ∀ g r, (List.ofFn fun h => if g ≤ r ∧ r ≤ h then
      tc (tc (T.x₁ g ^ T.d g) (T.x₁ r)) (T.x₁ h) ^ τ.w g r h else 1).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun g r =>
    list_prod_mem fun y hy => by obtain ⟨h, rfl⟩ := List.mem_ofFn.mp hy; exact hfacC g r h
  have hrowC : ∀ g, (List.ofFn fun r => (List.ofFn fun h => if g ≤ r ∧ r ≤ h then
      tc (tc (T.x₁ g ^ T.d g) (T.x₁ r)) (T.x₁ h) ^ τ.w g r h else 1).prod).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun g =>
    list_prod_mem fun y hy => by obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy; exact hinnerC g r
  have hW : A (T.genC τ) = W0 := by
    simp only [W0, η]
    unfold Data.genC
    rw [addMapG_ofFn hA _ (fun g => h32 (hrowC g))]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [addMapG_ofFn hA _ (fun r => h32 (hinnerC g r))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [addMapG_ofFn hA _ (fun h => h32 (hfacC g r h))]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs
    · exact addMapG_zpow hA (h32 (hmemC g r h)) _
    · exact addMapG_one hA
  let E1raw : N := ∑ r, ∑ l, (∑ g, ∑ h, if g ≤ r ∧ r ≤ h then
    τ.w g r h * T.α g h l else 0) • A (tc (T.x₃ l) (T.x₁ r))
  let E2raw : N := ∑ r, ∑ l, (∑ g, ∑ h, if g ≤ h ∧ h ≤ r then
    τ.w g h r * T.α g h l else 0) • A (tc (T.x₃ l) (T.x₁ r))
  let E3raw : N := ∑ r, ∑ l, (∑ g, ∑ h, if r < g ∧ g ≤ h then
    τ.w' r g h * T.α g h l else 0) • A (tc (T.x₃ l) (T.x₁ r))
  have hEwSplit : (∑ r, ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r))) =
      E1raw + E2raw + E3raw := by
    simp only [Ew, E1raw, E2raw, E3raw, add_smul, Finset.sum_add_distrib]
  have hE1 : E1raw = E1 := by
    calc
      E1raw = ∑ r, ∑ l, ∑ g, ∑ h, (if g ≤ r ∧ r ≤ h then τ.w g r h * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) := by
        simp only [E1raw, Finset.sum_smul]
      _ = ∑ r, ∑ g, ∑ l, ∑ h, (if g ≤ r ∧ r ≤ h then τ.w g r h * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) := Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r, ∑ g, ∑ h, ∑ l, (if g ≤ r ∧ r ≤ h then τ.w g r h * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
      _ = ∑ r, ∑ g, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h • η g h r else 0 := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun g _ =>
          Finset.sum_congr rfl fun h _ => ?_
        by_cases hc : g ≤ r ∧ r ≤ h
        · simp only [if_pos hc]
          calc
            _ = τ.w g r h • ∑ l, T.α g h l • A (tc (T.x₃ l) (T.x₁ r)) := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
            _ = _ := by rw [← map_alpha_vw h5 hv hA (hc.1.trans hc.2) (T.x₁ r)]
        · simp only [if_neg hc, zero_smul, Finset.sum_const_zero]
      _ = ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h • η g h r else 0 := by
        exact sum_swap_outer_vw (M := N) (fun r g h =>
          if g ≤ r ∧ r ≤ h then τ.w g r h • η g h r else 0)
  have hE2 : E2raw = W0 := by
    calc
      E2raw = ∑ r, ∑ l, ∑ g, ∑ h, (if g ≤ h ∧ h ≤ r then τ.w g h r * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) := by
        simp only [E2raw, Finset.sum_smul]
      _ = ∑ r, ∑ g, ∑ l, ∑ h, (if g ≤ h ∧ h ≤ r then τ.w g h r * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) := Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r, ∑ g, ∑ h, ∑ l, (if g ≤ h ∧ h ≤ r then τ.w g h r * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
      _ = ∑ r, ∑ g, ∑ h, if g ≤ h ∧ h ≤ r then τ.w g h r •
          A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ h)) (T.x₁ r)) else 0 := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun g _ =>
          Finset.sum_congr rfl fun h _ => ?_
        by_cases hc : g ≤ h ∧ h ≤ r
        · simp only [if_pos hc]
          calc
            _ = τ.w g h r • ∑ l, T.α g h l • A (tc (T.x₃ l) (T.x₁ r)) := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
            _ = _ := by rw [← map_alpha_vw h5 hv hA hc.1 (T.x₁ r)]
        · simp only [if_neg hc, zero_smul, Finset.sum_const_zero]
      _ = ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h •
          A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ r)) (T.x₁ h)) else 0 := by
        rw [show (∑ r, ∑ g, ∑ h, if g ≤ h ∧ h ≤ r then τ.w g h r •
          A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ h)) (T.x₁ r)) else 0) =
          ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h •
          A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ r)) (T.x₁ h)) else 0 from ew_second_perm_vw τ]
  have hE3 : E3raw = E3 := by
    calc
      E3raw = ∑ r, ∑ l, ∑ g, ∑ h, (if r < g ∧ g ≤ h then τ.w' r g h * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) := by
        simp only [E3raw, Finset.sum_smul]
      _ = ∑ r, ∑ g, ∑ l, ∑ h, (if r < g ∧ g ≤ h then τ.w' r g h * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) := Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r, ∑ g, ∑ h, ∑ l, (if r < g ∧ g ≤ h then τ.w' r g h * T.α g h l else 0) •
          A (tc (T.x₃ l) (T.x₁ r)) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
      _ = ∑ r, ∑ g, ∑ h, if r < g ∧ g ≤ h then τ.w' r g h • η g h r else 0 := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun g _ =>
          Finset.sum_congr rfl fun h _ => ?_
        by_cases hc : r < g ∧ g ≤ h
        · simp only [if_pos hc]
          calc
            _ = τ.w' r g h • ∑ l, T.α g h l • A (tc (T.x₃ l) (T.x₁ r)) := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
            _ = _ := by rw [← map_alpha_vw h5 hv hA hc.2 (T.x₁ r)]
        · simp only [if_neg hc, zero_smul, Finset.sum_const_zero]
      _ = ∑ r, ∑ h, ∑ g, if r < g ∧ g ≤ h then τ.w' r g h • η g h r else 0 :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hDiff : W0 - E1 = ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h • ω g r h else 0 := by
    simp only [W0, E1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun h _ => ?_
    by_cases hc : g ≤ r ∧ r ≤ h
    · simp only [if_pos hc, ← smul_sub]
      rw [map_jacobi_vw h5 hA (mem_Y_vw hv g)]
    · simp only [if_neg hc, zero_smul, sub_self]
  have hStage : (2 : ℤ) • A (T.genC τ) -
      (∑ r, ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r))) = DL - E3 := by
    have hWD : (∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h • ω g r h else 0) = DL := by
      have hself : ∀ g r, ω g r r = 0 := by
        intro g r
        simp only [ω]
        have hi : tc (T.x₁ r) (T.x₁ r) = 1 := by simp [tc]
        have hone : tc (T.x₁ g ^ T.d g) 1 = 1 := by simp [tc]
        rw [hi, hone, addMapG_one hA]
      have hsplit : ∀ g r h, (if g ≤ r ∧ r ≤ h then τ.w g r h • ω g r h else 0) =
          (if g ≤ r ∧ r < h then τ.w g r h • ω g r h else 0) +
          (if g ≤ r ∧ r = h then τ.w g r h • ω g r h else 0) := by
        intro g r h
        split_ifs with h1 h2 h3
        all_goals grind [zero_smul, zero_add, add_zero]
      simp only [DL, E3]
      calc
        _ = ∑ g, ∑ r, ∑ h, ((if g ≤ r ∧ r < h then τ.w g r h • ω g r h else 0) +
            (if g ≤ r ∧ r = h then τ.w g r h • ω g r h else 0)) := by
          exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun r _ =>
            Finset.sum_congr rfl fun h _ => hsplit g r h
        _ = (∑ g, ∑ r, ∑ h, if g ≤ r ∧ r < h then τ.w g r h • ω g r h else 0) +
            ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r = h then τ.w g r h • ω g r h else 0 := by
          simp only [Finset.sum_add_distrib]
        _ = ∑ r, ∑ h, ∑ g, if g ≤ r ∧ r < h then τ.w g r h • ω g r h else 0 := by
          have hz : (∑ g, ∑ r, ∑ h, if g ≤ r ∧ r = h then τ.w g r h • ω g r h else 0) = 0 := by
            refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun r _ =>
              Finset.sum_eq_zero fun h _ => ?_
            by_cases hc : g ≤ r ∧ r = h
            · obtain ⟨hgr, rfl⟩ := hc
              rw [if_pos ⟨hgr, rfl⟩, hself, smul_zero]
            · rw [if_neg hc]
          rw [hz, add_zero, Finset.sum_comm]
          exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    rw [hEwSplit]
    calc
      (2 : ℤ) • A (T.genC τ) - (E1raw + E2raw + E3raw) =
          (W0 - E1) - E3 := by
        rw [hW, hE1, hE2, hE3]
        abel_nf
      _ = DL - E3 := by rw [hDiff, hWD]
  have hDall : DL + DM + DR = 0 := by
    simp only [DL, DM, DR, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun h _ => ?_
    by_cases hrh : r < h
    · simpa only [hrh, and_true, true_and, and_iff_left, ω, Finset.sum_add_distrib] using
      d2_exact_vw h5 hv hτ hA hrh
    · simp only [hrh, and_false, false_and, ↓reduceIte, Finset.sum_const_zero, add_zero]
  have hMid : DM + E3 = E3n := by
    simp only [DM, E3, E3n, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun h _ =>
      Finset.sum_congr rfl fun g _ => ?_
    by_cases hc : r < g ∧ g ≤ h
    · have hrh : r < h := hc.1.trans_le hc.2
      simp only [if_pos hc, if_pos (show r < g ∧ g ≤ h ∧ r < h from ⟨hc.1, hc.2, hrh⟩), ω]
      rw [← smul_add]
      exact congrArg (τ.w' r g h • ·)
        ((sub_eq_iff_eq_add).mp (map_jacobi_vw h5 hA (mem_Y_vw hv g) _ _)).symm
    · have hcm : ¬(r < g ∧ g ≤ h ∧ r < h) := by
        rintro ⟨h1, h2, h3⟩
        exact hc ⟨h1, h2⟩
      simp only [if_neg hc, if_neg hcm, zero_add, zero_smul]
  have hE3n : E3n = -T3 T τ A := by
    simp only [E3n, T3, neg_neg, η]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_comm
  have hDR : DR = -T4 T τ A := by simp only [DR, T4, neg_neg, ω]
  have hDL : DL = -DM - DR := by
    have hd : DL + DM = -DR := by
      apply sub_eq_zero.mp
      simpa only [sub_neg_eq_add] using hDall
    calc
      DL = (DL + DM) - DM := by abel
      _ = -DR - DM := by rw [hd]
      _ = -DM - DR := by abel
  rw [hStage, hDL]
  calc
    (-DM - DR) - E3 = -(DM + E3) - DR := by abel
    _ = -E3n - DR := by rw [hMid]
    _ = T3 T τ A + T4 T τ A := by rw [hE3n, hDR]; abel

end Star

end GroupDimension
