module

public import GroupDimension.Star.Defs

@[expose] public section

/-!
# Auxiliary exact identities for Lemmas 2 and 3 of `(⋆)`

These are variants of the identities in `G4Cube.lean`, without any condition on the exponent of
`γ₄`. In particular, K5 is obtained from `ClassFour.jacobi4`, not from a mod-3 argument.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- For `u ∈ γ₃`, left inversion passes through Tahara's commutator in class `≤ 4`. -/
theorem tc_inv_left_L2_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {u : G} (hu : u ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (x : G) :
    tc (u⁻¹) x = (tc u x)⁻¹ := by
  have hmul : ∀ {a b : G}, a ∈ (⊤ : Subgroup G).lowerCentralSeries 2 →
      b ∈ (⊤ : Subgroup G).lowerCentralSeries 2 → tc (a * b) x = tc a x * tc b x := by
    intro a b ha hb
    have h1 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (by omega) ha (mem_lcs_zero x)
    have hcom : b * tc a x = tc a x * b := central_L3 h5 h1 b
    rw [tc_mul_left a b x]
    calc
      b⁻¹ * tc a x * b * tc b x = b⁻¹ * (tc a x * b) * tc b x := by group
      _ = b⁻¹ * (b * tc a x) * tc b x := by rw [hcom]
      _ = tc a x * tc b x := by group
  have h := hmul hu (inv_mem hu)
  rw [mul_inv_cancel, show tc (1 : G) x = 1 by simp [tc]] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Conjugation as a commutator. -/
theorem conj_tc_vw (u y : G) : y⁻¹ * u * y = u * tc u y := by
  simp only [tc]
  group

/-- Right multiplicativity of `a ↦ [a, ·]` on `γ₂`, where its values are central. -/
theorem tc_mul_right_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {a x y : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc a (x * y) = tc a x * tc a y := by
  have hx3 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (by omega) ha hx
  have hy3 : tc a y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (by omega) ha hy
  rw [tc_mul_right]
  calc
    tc a y * (y⁻¹ * tc a x * y) = tc a y * tc a x := by
      rw [mul_assoc, ← central_L3 h5 hx3 y]
      group
    _ = tc a x * tc a y := central_L3 h5 hx3 (tc a y)

/-- The induced map to an additive target is right additive on `γ₂`. -/
theorem map_tc_right_add_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    {a x y : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    A (tc a (x * y)) = A (tc a x) + A (tc a y) := by
  rw [tc_mul_right_vw h5 ha hx hy]
  have hx3 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (by omega) ha hx
  have hy3 : tc a y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (by omega) ha hy
  exact hA _ (lcs_mem_of_le (by norm_num) hx3) _ (lcs_mem_of_le (by norm_num) hy3)

/-- Right additivity on ordered products in `γ₂`. -/
theorem map_tc_oprod_right_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) {n : ℕ}
    {x : Fin n → G} (hx : ∀ i, x i ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (b : Fin n → ℤ) :
    A (tc a (oprod x b)) = ∑ i, b i • A (tc a (x i)) := by
  exact addMapG_oprod (A := fun b => A (tc a b))
    (fun u hu v hv => map_tc_right_add_vw h5 hA ha hu hv) hx b

/-- Left additivity on ordered products in `γ₂`. -/
theorem map_tc_oprod_left_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    {n : ℕ} {x : Fin n → G} (hx : ∀ i, x i ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (y : G) (b : Fin n → ℤ) :
    A (tc (oprod x b) y) = ∑ i, b i • A (tc (x i) y) := by
  apply addMapG_oprod (A := fun a => A (tc a y)) ?_ hx b
  intro a ha c hc
  rw [tc_mul_left_L1 h5 ha hc]
  exact hA _ (tc_mem (by omega) ha (mem_lcs_zero y)) _
    (tc_mem (by omega) hc (mem_lcs_zero y))

/-- Expansion of `Yᵢ` along the second-layer basis, after applying `A [·, y]`. -/
theorem map_Y_expand_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {T : Data G} (hv : T.Valid) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    (i : Fin T.s) {y : G} (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    A (tc (T.x₁ i ^ T.d i) y) = ∑ k, T.b i k • A (tc (T.x₂ k) y) := by
  have hm := hv.hb i
  have hb1 : oprod T.x₂ (T.b i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    oprod_mem hv.basis₂.mem _
  have hc2 : oprod T.x₃ (T.c i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    oprod_mem hv.basis₃.mem _
  have hc1 : oprod T.x₃ (T.c i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    lcs_mem_of_le (by norm_num) hc2
  have hm1 : (oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i))⁻¹ *
      (T.x₁ i ^ T.d i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    lcs_mem_of_le (by norm_num) hm
  rw [← mul_inv_cancel_left (oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i)) (T.x₁ i ^ T.d i),
    tc_mul_left_L1 h5 (mul_mem hb1 hc1) hm1, tc_L3 h5 hm y, mul_one,
    tc_mul_left_L1 h5 hb1 hc1, tc_L2_L1 h5 hc2 hy, mul_one]
  exact map_tc_oprod_left_vw h5 hA hv.basis₂.mem y (T.b i)

/-- **K3**, exact: `[a,xⁿ] = `[a,x]ⁿ [a,x,x]^{C(n,2)}` for `a ∈ γ₂`. -/
theorem tc_pow_right_K3 {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (x : G) (n : ℕ) :
    tc a (x ^ n) = tc a x ^ n * tc (tc a x) x ^ n.choose 2 := by
  have hc1 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (by omega) ha (mem_lcs_zero x)
  have ht3 : tc (tc a x) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) hc1 (mem_lcs_zero x)
  have ht : ∀ z : G, Commute z (tc (tc a x) x) := fun z => central_L3 h5 ht3 z
  induction n with
  | zero => simp [tc]
  | succ n ih =>
    have he : tc a (x ^ (n + 1)) = tc a x * (x⁻¹ * tc a (x ^ n) * x) := by
      rw [pow_succ, tc_mul_right]
    have hpow : ∀ k : ℕ, x⁻¹ * tc a x ^ k * x = (tc a x * tc (tc a x) x) ^ k := by
      intro k
      calc
        x⁻¹ * tc a x ^ k * x = (x⁻¹ * tc a x * x) ^ k := by
          simpa using (conj_pow (a := x⁻¹) (b := tc a x) (i := k)).symm
        _ = (tc a x * tc (tc a x) x) ^ k := by rw [conj_tc_vw]
    have hcpow : ∀ k : ℕ, x⁻¹ * tc (tc a x) x ^ k * x = tc (tc a x) x ^ k := by
      intro k
      rw [mul_assoc, ← central_L3 h5 (pow_mem ht3 k) x]
      group
    have hC : (n + 1).choose 2 = n + n.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    rw [he, ih]
    calc
      tc a x * (x⁻¹ * (tc a x ^ n * tc (tc a x) x ^ n.choose 2) * x) =
          tc a x * ((x⁻¹ * tc a x ^ n * x) *
            (x⁻¹ * tc (tc a x) x ^ n.choose 2 * x)) := by group
      _ = tc a x * ((tc a x * tc (tc a x) x) ^ n * tc (tc a x) x ^ n.choose 2) := by
        rw [hpow, hcpow]
      _ = tc a x ^ (n + 1) * tc (tc a x) x ^ (n + 1).choose 2 := by
        rw [hC, pow_add, (ht (tc a x)).mul_pow, pow_succ']
        group

/-- The exact skew-total identity: antisymmetry and divisibility are used only after pairing. -/
theorem sum_skew_exact_vw {t : ℕ} (M : Fin t → Fin t → ℤ) (γ : Fin t → Fin t → N)
    (hdiag : ∀ i, γ i i = 0) (hanti : ∀ i j, γ i j + γ j i = 0)
    (hcond : ∀ i j, (M i j + M j i) • γ i j = 0) :
    (∑ i, ∑ j, M i j • γ i j) =
      (2 : ℤ) • ∑ i, ∑ j, if j < i then M i j • γ i j else 0 := by
  classical
  let strict : Fin t → Fin t → N := fun i j => if j < i then M i j • γ i j else 0
  let other : Fin t → Fin t → N := fun i j => if i < j then M i j • γ i j else 0
  let diag : Fin t → Fin t → N := fun i j => if i = j then M i j • γ i j else 0
  have hsplit : ∀ i j, M i j • γ i j = strict i j + other i j + diag i j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp only [strict, other, diag, hij, not_lt.mpr hij.le, if_true, if_false, ne_eq,
        ne_of_lt hij, not_false_eq_true, add_zero, zero_add]
    · simp only [strict, other, diag, lt_self_iff_false, if_false, if_true, hdiag, smul_zero,
        zero_add, add_zero]
    · simp only [strict, other, diag, hji, not_lt.mpr hji.le, if_true, if_false, ne_eq,
        ne_of_gt hji, not_false_eq_true, add_zero, zero_add]
  have hdiag0 : ∑ i, ∑ j, diag i j = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp only [diag]
    split_ifs with hij
    · subst j
      rw [hdiag, smul_zero]
    · rfl
  have hother : ∑ i, ∑ j, other i j = ∑ i, ∑ j, strict i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [other, strict]
    by_cases hji : j < i
    · simp only [hji, if_true]
      have hγ : γ j i = -γ i j := eq_neg_of_add_eq_zero_right (hanti i j)
      have hc := hcond i j
      rw [add_smul] at hc
      rw [hγ, smul_neg]
      simpa only [neg_neg] using congrArg Neg.neg (eq_neg_of_add_eq_zero_right hc)
    · simp only [hji, if_false]
  calc
    (∑ i, ∑ j, M i j • γ i j) = ∑ i, ∑ j, (strict i j + other i j + diag i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = (∑ i, ∑ j, strict i j) + (∑ i, ∑ j, other i j) + ∑ i, ∑ j, diag i j := by
      simp only [Finset.sum_add_distrib]
    _ = (2 : ℤ) • ∑ i, ∑ j, strict i j := by rw [hother, hdiag0, add_zero, two_smul]
    _ = _ := rfl

/-- Tahara commutators lie in `γ₂`. -/
theorem tc_mem_L1_vw (u v : G) : tc u v ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
  tc_mem (i := 0) (j := 0) (by omega) (mem_lcs_zero u) (mem_lcs_zero v)

/-- Swap the outer two indices of a triple sum. -/
theorem sum_swap_outer_vw {s : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin s → Fin s → Fin s → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ j, ∑ i, ∑ k, F i j k := by
  exact Finset.sum_comm

/-- Rotate the indices of a triple sum to the left: `(i,j,k) ↦ (j,k,i)`. -/
theorem sum_rotate_left_vw {s : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin s → Fin s → Fin s → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ j, ∑ k, ∑ i, F i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, F i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, F i j k := Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- Swap the inner two indices of a triple sum: `(i,j,k) ↦ (i,k,j)`. -/
theorem sum_swap_inner_vw {s : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin s → Fin s → Fin s → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ i, ∑ k, ∑ j, F i j k := by
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Rotate the indices of a triple sum to the right: `(i,j,k) ↦ (k,i,j)`. -/
theorem sum_rotate_right_vw {s : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin s → Fin s → Fin s → M) :
    (∑ i, ∑ j, ∑ k, F i j k) = ∑ k, ∑ i, ∑ j, F i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm

/-- The permutation used by the concrete second `Ew` summand. -/
theorem ew_second_perm_vw {T : Data G} {A : G → N} (τ : Coeffs T.s T.t) :
    (∑ r, ∑ g, ∑ h, if g ≤ h ∧ h ≤ r then τ.w g h r •
      A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ h)) (T.x₁ r)) else 0) =
      ∑ g, ∑ r, ∑ h, if g ≤ r ∧ r ≤ h then
        τ.w g r h • A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ r)) (T.x₁ h)) else 0 := by
  let F : Fin T.s → Fin T.s → Fin T.s → N := fun r g h =>
    if g ≤ h ∧ h ≤ r then τ.w g h r • A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ h)) (T.x₁ r)) else 0
  exact sum_rotate_left_vw (M := N) F

/-- Contract one conditional row of a finite double sum. -/
theorem sum_cond_contract_vw {s t : ℕ} (p : Fin s → Prop) [DecidablePred p]
    (w : Fin s → ℤ) (b : Fin s → Fin t → ℤ) (γ : Fin t → N) (ω : Fin s → N)
    (hω : ∀ i, ω i = ∑ m, b i m • γ m) :
    (∑ m, (∑ i, if p i then w i * b i m else 0) • γ m) =
      ∑ i, if p i then w i • ω i else 0 := by
  classical
  calc
    _ = ∑ m, ∑ i, (if p i then w i * b i m else 0) • γ m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_smul]
    _ = ∑ i, ∑ m, (if p i then w i * b i m else 0) • γ m := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : p i
      · simp only [hi, if_true]
        rw [hω i, Finset.smul_sum]
        exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
      · simp only [hi, if_false, Finset.sum_const_zero, zero_smul]

/-- **K5**, exact, after applying an additive map: `[a,x,y] - [a,y,x] = [a,[x,y]]`
for `a ∈ γ₂`. -/
theorem map_jacobi_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x y : G) :
    A (tc (tc a x) y) - A (tc (tc a y) x) = A (tc a (tc x y)) := by
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have hF : ∀ u ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      ∀ v ∈ (⊤ : Subgroup G).lowerCentralSeries 3, A (u * v) = A u + A v := by
    intro u hu v hv
    exact hA u (h32 hu) v (h32 hv)
  have B_mul_left : ∀ {a a' u : G}, ⁅a, u⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      ⁅a', u⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      A ⁅a * a', u⁆ = A ⁅a, u⁆ + A ⁅a', u⁆ := by
    intro a a' u h h'
    rw [comm_mul_left, conj_central h5 h', hF _ h' _ h, add_comm]
  have B_mul_right : ∀ {a u u' : G}, ⁅a, u⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      ⁅a, u'⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      A ⁅a, u * u'⁆ = A ⁅a, u⁆ + A ⁅a, u'⁆ := by
    intro a u u' h h'
    rw [comm_mul_right, conj_central h5 h', hF _ h _ h']
  have addL2x : ∀ u : G, ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A ⁅a * b, u⁆ = A ⁅a, u⁆ + A ⁅b, u⁆ := by
    intro u a ha b hb
    exact B_mul_left (commutator_mem_lcs (by norm_num) ha (mem_lcs_zero u))
      (commutator_mem_lcs (by norm_num) hb (mem_lcs_zero u))
  have addL1z : ∀ {z : G}, z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 →
      ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      A ⁅a * b, z⁆ = A ⁅a, z⁆ + A ⁅b, z⁆ := by
    intro z hz a ha b hb
    exact B_mul_left (commutator_mem_lcs (by norm_num) ha hz)
      (commutator_mem_lcs (by norm_num) hb hz)
  have B_L3 : ∀ {s : G}, s ∈ (⊤ : Subgroup G).lowerCentralSeries 3 → ∀ u : G, A ⁅s, u⁆ = 0 := by
    intro s hs u
    rw [comm_eq_one h5 (by norm_num) hs (mem_lcs_zero u), addMapG_one hA]
  have B_L2_L1 : ∀ {s z : G}, s ∈ (⊤ : Subgroup G).lowerCentralSeries 2 →
      z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 → A ⁅s, z⁆ = 0 := by
    intro s z hs hz
    rw [comm_eq_one h5 (by norm_num) hs hz, addMapG_one hA]
  have B_conj_L2 : ∀ {u : G}, u ∈ (⊤ : Subgroup G).lowerCentralSeries 2 →
      ∀ g x : G, A ⁅g * u * g⁻¹, x⁆ = A ⁅u, x⁆ := by
    intro u hu g x
    have hgu : ⁅g, u⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      commutator_mem_lcs (by norm_num) (mem_lcs_zero g) hu
    rw [conj_eq_comm_mul, addL2x x _ (lcs_mem_of_le (by norm_num) hgu) _ hu,
      B_L3 hgu, zero_add]
  have B_conj_L1 : ∀ {v z : G}, v ∈ (⊤ : Subgroup G).lowerCentralSeries 1 →
      z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 → ∀ g : G,
      A ⁅g * v * g⁻¹, z⁆ = A ⁅v, z⁆ := by
    intro v z hv hz g
    have hgv : ⁅g, v⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) (mem_lcs_zero g) hv
    rw [conj_eq_comm_mul, addL1z hz _ (lcs_mem_of_le (by norm_num) hgv) _ hv,
      B_L2_L1 hgv hz, zero_add]
  have addRight1 : ∀ {z : G}, z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 →
      ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      A ⁅z, a * b⁆ = A ⁅z, a⁆ + A ⁅z, b⁆ := by
    intro z hz a ha b hb
    exact B_mul_right (commutator_mem_lcs (by norm_num) hz ha)
      (commutator_mem_lcs (by norm_num) hz hb)
  have addRight2 : ∀ {u : G}, u ∈ (⊤ : Subgroup G).lowerCentralSeries 2 →
      ∀ a b : G, A ⁅u, a * b⁆ = A ⁅u, a⁆ + A ⁅u, b⁆ := by
    intro u hu a b
    exact B_mul_right (commutator_mem_lcs (by norm_num) hu (mem_lcs_zero a))
      (commutator_mem_lcs (by norm_num) hu (mem_lcs_zero b))
  have J_right : ∀ (x : G) {z : G}, z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 →
      ∀ a b : G, A ⁅⁅x, a * b⁆, z⁆ = A ⁅⁅x, a⁆, z⁆ + A ⁅⁅x, b⁆, z⁆ := by
    intro x z hz a b
    have ha : ⁅x, a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one x a
    have hb : ⁅x, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one x b
    rw [comm_mul_right, addL1z hz _ ha _ (conj_mem_lcs 1 hb a), B_conj_L1 hb hz]
  have K_right : ∀ {z : G}, z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 → ∀ y a b : G,
      A ⁅⁅z, a * b⁆, y⁆ = A ⁅⁅z, a⁆, y⁆ + A ⁅⁅z, b⁆, y⁆ := by
    intro z hz y a b
    have ha : ⁅z, a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) hz (mem_lcs_zero a)
    have hb : ⁅z, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) hz (mem_lcs_zero b)
    rw [comm_mul_right, addL2x y _ ha _ (conj_mem_lcs 2 hb a), B_conj_L2 hb]
  have K_mid : ∀ (y x : G) {z : G}, z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 →
      ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      A ⁅⁅y, a * b⁆, x⁆ = A ⁅⁅y, a⁆, x⁆ + A ⁅⁅y, b⁆, x⁆ := by
    intro y x z hz a ha b hb
    have ha' : ⁅y, a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) (mem_lcs_zero y) ha
    have hb' : ⁅y, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) (mem_lcs_zero y) hb
    rw [comm_mul_right, addL2x x _ ha' _ (conj_mem_lcs 2 hb' a), B_conj_L2 hb']
  have jacobi4v : ∀ (x y : G) {z : G}, z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 →
      A ⁅⁅x, y⁆, z⁆ + A ⁅⁅z, x⁆, y⁆ + A ⁅⁅y, z⁆, x⁆ = 0 := by
    intro x y z hz
    have hxy : ⁅x, y⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one x _
    have hzx : ⁅z, x⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) hz (mem_lcs_zero _)
    have hyz : ⁅y, z⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      commutator_mem_lcs (by norm_num) (mem_lcs_zero y) (inv_mem hz)
    have h0 : ⁅⁅x, y⁻¹⁆, z⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      commutator_mem_lcs (by norm_num) hxy (inv_mem hz)
    have h2 : ⁅⁅z, x⁻¹⁆, y⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      commutator_mem_lcs (by norm_num) hzx (mem_lcs_zero _)
    have h1 : ⁅⁅y, z⁻¹⁆, x⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      commutator_mem_lcs (by norm_num) hyz (mem_lcs_zero _)
    have hw := hall_witt x y z
    rw [conj_central' h5 h0, conj_central' h5 h2, conj_central' h5 h1] at hw
    have hs := congrArg A hw
    rw [hF _ (mul_mem h0 h2) _ h1, hF _ h0 _ h2, addMapG_one hA] at hs
    have e0a : A ⁅⁅x, y⁻¹⁆, z⁻¹⁆ = -A ⁅⁅x, y⁻¹⁆, z⁆ :=
      addMapG_inv (A := fun b => A ⁅⁅x, y⁻¹⁆, b⁆) (addRight1 hxy) hz
    have e0b : A ⁅⁅x, y⁻¹⁆, z⁆ = -A ⁅⁅x, y⁆, z⁆ :=
      addMapG_inv (A := fun b => A ⁅⁅x, b⁆, z⁆)
        (fun a _ b _ => J_right x hz a b) (mem_lcs_zero y)
    have e2a : A ⁅⁅z, x⁻¹⁆, y⁻¹⁆ = -A ⁅⁅z, x⁻¹⁆, y⁆ :=
      addMapG_inv (A := fun b => A ⁅⁅z, x⁻¹⁆, b⁆)
        (fun a _ b _ => addRight2 hzx a b) (mem_lcs_zero y)
    have e2b : A ⁅⁅z, x⁻¹⁆, y⁆ = -A ⁅⁅z, x⁆, y⁆ :=
      addMapG_inv (A := fun b => A ⁅⁅z, b⁆, y⁆)
        (fun a _ b _ => K_right hz y a b) (mem_lcs_zero x)
    have e1a : A ⁅⁅y, z⁻¹⁆, x⁻¹⁆ = -A ⁅⁅y, z⁻¹⁆, x⁆ :=
      addMapG_inv (A := fun b => A ⁅⁅y, z⁻¹⁆, b⁆)
        (fun a _ b _ => addRight2 hyz a b) (mem_lcs_zero x)
    have e1b : A ⁅⁅y, z⁻¹⁆, x⁆ = -A ⁅⁅y, z⁆, x⁆ :=
      addMapG_inv (A := fun b => A ⁅⁅y, b⁆, x⁆) (K_mid y x hz) hz
    rw [e0a, e0b, e2a, e2b, e1a, e1b] at hs
    simpa only [neg_neg, add_comm, add_left_comm, add_assoc] using hs
  have hj := jacobi4v y⁻¹ x⁻¹ (inv_mem ha)
  have hfirst : A ⁅⁅y⁻¹, x⁻¹⁆, a⁻¹⁆ = A (tc (tc x y) a) := by
    simp only [tc_eq, commutatorElement_def]
    group
  have hsecond : A ⁅⁅a⁻¹, y⁻¹⁆, x⁻¹⁆ = A (tc (tc a y) x)⁻¹ := by
    have hu : tc a y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (by omega) ha (mem_lcs_zero y)
    have heq : tc (tc y a) x = (tc (tc a y) x)⁻¹ := by
      rw [← tc_inv a y, tc_inv_left_L2_vw h5 hu]
    calc
      A ⁅⁅a⁻¹, y⁻¹⁆, x⁻¹⁆ = A (tc (tc y a) x) := by
        simp only [tc_eq, commutatorElement_inv]
      _ = A (tc (tc a y) x)⁻¹ := by rw [heq]
  have hthird : A ⁅⁅x⁻¹, a⁻¹⁆, y⁻¹⁆ = A (tc (tc a x) y) := by
    simp only [tc_eq, commutatorElement_def]
    group
  rw [hfirst, hsecond, hthird] at hj
  have hq3 : tc (tc x y) a ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (by omega) (tc_mem_L1_vw x y) ha
  have hs3 : tc (tc a y) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (by omega)
      (tc_mem (i := 1) (j := 0) (by omega) ha (mem_lcs_zero y)) (mem_lcs_zero x)
  rw [addMapG_inv hA (h32 hs3)] at hj
  have hinv : A (tc (tc x y) a) = -A (tc a (tc x y)) := by
    have hm : tc a (tc x y) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 1) (j := 1) (by omega) ha (tc_mem_L1_vw x y)
    rw [← tc_inv, addMapG_inv hA (h32 hm)]
  rw [hinv] at hj
  apply sub_eq_zero.mp
  simpa only [neg_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hj

/-- The first-layer powers lie in `γ₂`, as in `SetupB.Y1`, but without `h4`. -/
theorem mem_Y_vw {T : Data G} (hv : T.Valid) (i : Fin T.s) :
    T.x₁ i ^ T.d i ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  have hm := hv.hb i
  have hP : oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i) ∈
      (⊤ : Subgroup G).lowerCentralSeries 1 :=
    mul_mem (oprod_mem hv.basis₂.mem _)
      (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (hv.basis₃.mem l)) _)
  rw [← mul_inv_cancel_left (oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i)) (T.x₁ i ^ T.d i)]
  exact mul_mem hP (lcs_mem_of_le (by norm_num) hm)

/-- Pairing `Valid.hα` with an arbitrary group element. -/
theorem map_alpha_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {T : Data G} (hv : T.Valid) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b)
    {g h : Fin T.s} (hgh : g ≤ h) (y : G) :
    A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ h)) y) =
      ∑ l, T.α g h l • A (tc (T.x₃ l) y) := by
  let Φ : G → N := fun z => A (tc z y)
  have hΦadd : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1, Φ (a * b) = Φ a + Φ b := by
    intro a ha b hb
    simp only [Φ]
    rw [tc_mul_left_L1 h5 ha hb]
    exact hA _ (tc_mem (by omega) ha (mem_lcs_zero y)) _
      (tc_mem (by omega) hb (mem_lcs_zero y))
  have hm := hv.hα g h hgh
  have ho : oprod T.x₃ (T.α g h) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    oprod_mem hv.basis₃.mem _
  rw [← mul_inv_cancel_left (oprod T.x₃ (T.α g h)) (tc (T.x₁ g ^ T.d g) (T.x₁ h)),
    tc_mul_left_L1 h5 (lcs_mem_of_le (by norm_num) ho) (lcs_mem_of_le (by norm_num) hm),
    tc_L3 h5 hm y, mul_one]
  exact addMapG_oprod hΦadd (fun l => lcs_mem_of_le (by norm_num) (hv.basis₃.mem l)) _

/-- The `d(j)`-power of `c_{jk}` belongs to `γ₃`; this is the modulus calculation for `D₂`. -/
theorem tc_c_d_mem_vw (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    {T : Data G} (hv : T.Valid) (j k : Fin T.s) :
    tc (T.x₁ j) (T.x₁ k) ^ T.d j ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  have hY : T.x₁ j ^ T.d j ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := mem_Y_vw hv j
  have hc : tc (T.x₁ j) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem_L1_vw _ _
  have hf : tc (tc (T.x₁ j) (T.x₁ k)) (T.x₁ j) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (by omega) hc (mem_lcs_zero _)
  have hg : tc (tc (tc (T.x₁ j) (T.x₁ k)) (T.x₁ j)) (T.x₁ j) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (by omega) hf (mem_lcs_zero _)
  have he : tc (T.x₁ j) (T.x₁ k) ^ T.d j =
      (tc (T.x₁ j ^ T.d j) (T.x₁ k)) *
        (tc (tc (T.x₁ j) (T.x₁ k)) (T.x₁ j) ^ (T.d j).choose 2 *
          tc (tc (tc (T.x₁ j) (T.x₁ k)) (T.x₁ j)) (T.x₁ j) ^ (T.d j).choose 3)⁻¹ := by
    rw [tc_pow_formula h5]
    group
  rw [he]
  exact mul_mem (tc_mem (by omega) hY (mem_lcs_zero _))
    (inv_mem (mul_mem (pow_mem (lcs_mem_of_le (by norm_num) hf) _)
      (pow_mem (lcs_mem_of_le (by norm_num) hg) _)))

end Star

end GroupDimension
