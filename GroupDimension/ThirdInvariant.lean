module

public import GroupDimension.Ab399

@[expose] public section

/-!
# `D₅ ⊆ Ω_{μ-1}(γ₄)`: the third invariant of `Q_ab` (Theorem 12.6 of wiki 891; MATH-468)

Let `Q` be a finite `3`-group of class `≤ 4` and `3^μ` the third largest invariant of `Q_ab`
(`μ = 0` when `Q_ab` has at most two invariants). Theorem 12.6 of the notes (MATH wiki page 891,
§12.3, MATH-451) states `D₅(Q) ⊆ Ω_{μ-1}(γ₄(Q))` (`Ω_{-1} = 1`); with `μ ≤ 1` it gives
Theorem 11.2: `D₅(Q) = 1` when at most two invariants of `Q_ab` are `≥ 9`, with no condition
on `γ₄`.

This file proves the core: in the situation `Setup` (Tahara's data with a basis adapted to the
kernel of the cube map, as in `Ab399.Setup`, with every `d(i)` a power of `3` and
`d(i) ∣ 3^μ` whenever two indices lie above `i`), every generator `g(τ)` of Tahara's Theorem 6.1
satisfies `g(τ)^{3^{μ-1}} = 1` (`Setup.gen_pow_eq_one`). The proof evaluates the exact identity
`(⋆)` (`Star.two_smul_gen_eq`) after the additive map `3^{μ-1} • A`: every term of
`T₁ + ⋯ + T₅` is `3 y` with `3^μ y = 0`:
* a term whose distinguished (smallest) index `i` has two indices above it: all the forms in it are
  killed by `d(i) ∣ 3^μ` (`c_pow_kill`, `c_triple_kill`, `triple_pow_mid`), and the factor `3` comes
  from (c1)–(c3) or from `Ȳ_h ∈ 3 L₂` (inactive `h`);
* the top pair `(i, h)` (only `h` lies above `i`): the values are `ω(c̄_{ih}, ·)` on `γ₂`, which is
  killed by `3^μ` (`omega_top`), because `γ₂/γ₃` is spanned by the `c̄_{ab}` and every pair other
  than `(i, h)` has a small first index.
The coefficients of `T₁` come from the general degree-`n` defect `delta_general`
(`n = d(h)`, coefficients `(n-1)/2` and `K n = C(n,3) - (n-1)/2 C(n,2) = -n(n²-1)/12`).
-/

namespace GroupDimension

namespace ThirdInvariant

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The situation of Theorem 12.6: class `≤ 4`, Tahara's data whose first-layer orders are powers
of `3`, the active indices `act` of the basis adapted to the kernel of the cube map (as in
`Ab399.Setup`), and `d(i) ∣ 3^μ` for every index `i` with two indices above it. -/
structure Setup (T : Data G) (act : Fin T.s → Prop) (μ : ℕ) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  htor : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1
  valid : T.Valid
  hd : ∀ i, ∃ m : ℕ, T.d i = 3 ^ (m + 1)
  he : ∀ k, 3 ∣ T.e k
  hf : ∀ l, 3 ∣ T.f l
  hsmall : ∀ i j k : Fin T.s, i < j → j < k → T.d i ∣ 3 ^ μ
  hK : ∀ i, ¬ act i → ∃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, T.x₁ i ^ T.d i = a ^ 3 * c
  hind : ∀ cf : Fin T.s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * T.b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h

namespace Setup

variable {T : Data G} {act : Fin T.s → Prop} {μ : ℕ} (S : Setup T act μ)
include S

theorem three_dvd_d (i : Fin T.s) : 3 ∣ T.d i := by
  obtain ⟨m, hm⟩ := S.hd i
  rw [hm, pow_succ]; exact dvd_mul_left 3 _

theorem d_dvd {i j : Fin T.s} (h : i ≤ j) : T.d i ∣ T.d j := S.valid.basis₁.dvd i j h

theorem gcd_e3 (i : Fin T.s) (k : Fin T.t) : 3 ∣ Nat.gcd (T.d i) (T.e k) :=
  Nat.dvd_gcd (S.three_dvd_d i) (S.he k)

theorem gcd_f3 (i : Fin T.s) (l : Fin T.u) : 3 ∣ Nat.gcd (T.d i) (T.f l) :=
  Nat.dvd_gcd (S.three_dvd_d i) (S.hf l)

theorem ch2_dvd (i : Fin T.s) : (3 : ℤ) ∣ T.ch i 2 := by
  obtain ⟨r, hr⟩ := S.three_dvd_d i
  have h2 : (T.d i).choose 2 * 2 = T.d i * (T.d i - 1) := by
    rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self (T.d i)).two_dvd]
  have h3 : 3 ∣ (T.d i).choose 2 * 2 := by rw [h2, hr, mul_assoc]; exact dvd_mul_right 3 _
  have : 3 ∣ (T.d i).choose 2 := (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h3)
  unfold Data.ch
  exact_mod_cast this

theorem x2mem (k : Fin T.t) : T.x₂ k ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := S.valid.basis₂.mem k

theorem x3mem (l : Fin T.u) : T.x₃ l ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := S.valid.basis₃.mem l

theorem Y1 (i : Fin T.s) : T.x₁ i ^ T.d i ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  have h := S.valid.hb i
  have hP : oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    mul_mem (oprod_mem S.x2mem _) (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _)
  rw [← mul_inv_cancel_left (oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i)) (T.x₁ i ^ T.d i)]
  exact mul_mem hP (lcs_mem_of_le (by norm_num) h)

theorem x2e (k : Fin T.t) : T.x₂ k ^ T.e k ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  have h := S.valid.hdd k
  rw [← mul_inv_cancel_left (oprod T.x₃ (T.dd k)) (T.x₂ k ^ T.e k)]
  exact mul_mem (oprod_mem S.x3mem _) (lcs_mem_of_le (by norm_num) h)

/-- `d(i) q(i, j) = d(j)` for `i ≤ j`. -/
theorem d_mul_q {i j : Fin T.s} (hij : i ≤ j) : T.d i * (T.d j / T.d i) = T.d j :=
  Nat.mul_div_cancel' (S.d_dvd hij)

/-- `3 ∣ d(j)/d(i)` when `i ≤ j` and `d(i) ≠ d(j)`. -/
theorem three_dvd_q {i j : Fin T.s} (hij : i ≤ j) (hne : T.d i ≠ T.d j) : 3 ∣ T.d j / T.d i := by
  obtain ⟨a, ha⟩ := S.hd i
  obtain ⟨b, hb⟩ := S.hd j
  have hdv := S.d_dvd hij
  rw [ha, hb] at hdv hne ⊢
  have hab : a + 1 ≤ b + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdv
  have hlt : a + 1 < b + 1 := lt_of_le_of_ne hab (fun h => hne (by rw [h]))
  rw [Nat.pow_div hab (by norm_num)]
  exact dvd_pow_self 3 (by omega)


/-- For `c ∈ γ₂`, the right argument of `[c, ·]` is multiplicative in class `≤ 4`. -/
theorem tc_mul_right_L1 {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (b : G) : tc c (a * b) = tc c a * tc c b := by
  have hz : tc c a ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (n := 3) (by norm_num) hc ha
  have hconj : b⁻¹ * tc c a * b = tc c a := by
    rw [mul_assoc, ← central_L3 S.h5 hz b]; group
  rw [tc_mul_right, hconj, central_L3 S.h5 hz]

/-- The inverse form of right-linearity, for `c, a ∈ γ₂`. -/
theorem tc_inv_right_L1 {c a : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : tc c a⁻¹ = (tc c a)⁻¹ := by
  have h := S.tc_mul_right_L1 hc ha a⁻¹
  rw [mul_inv_cancel] at h
  have h1 : tc c (1 : G) = 1 := by simp [tc]
  rw [h1] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- (K4), with the power in the middle argument. -/
theorem triple_pow_mid {a x : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (y : G) {n : ℕ} (hx : x ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc (tc a x) y ^ n = 1 := by
  have hc2 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (by omega) ha (mem_lcs_zero x)
  have hf3 : tc (tc a x) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) hc2 (mem_lcs_zero x)
  have hz : tc a (x ^ n) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (by omega) ha hx
  have h1 : tc (tc a (x ^ n)) y = 1 := tc_L3 S.h5 hz y
  rw [Star.tc_pow_right_K3 ha S.h5 x n,
    tc_mul_left_L1 S.h5 (lcs_mem_of_le (by norm_num) (pow_mem hc2 n))
      (lcs_mem_of_le (by norm_num) (pow_mem hf3 (n.choose 2))),
    tc_pow_left_L1 S.h5 (lcs_mem_of_le (by norm_num) hc2),
    tc_L3 S.h5 (pow_mem hf3 (n.choose 2)), mul_one] at h1
  exact h1

/-- (K4), with the power in the last argument. -/
theorem triple_pow_last {a x y : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    {n : ℕ} (hy : y ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc (tc a x) y ^ n = 1 := by
  have hc2 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (by omega) ha (mem_lcs_zero x)
  have hz : tc (tc a x) (y ^ n) ∈ (⊤ : Subgroup G).lowerCentralSeries 4 :=
    tc_mem (i := 2) (j := 1) (by omega) hc2 hy
  have h1 : tc (tc a x) (y ^ n) = 1 := by rwa [S.h5, mem_bot] at hz
  rwa [Star.tc_pow_right_L2 hc2 S.h5 y n] at h1

/-- Left inverses in the first argument of a class-four commutator. -/
theorem tc_inv_left_L1 {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc c⁻¹ x = (tc c x)⁻¹ := by
  have h := tc_mul_left_L1 S.h5 hc (inv_mem hc) x
  rw [mul_inv_cancel] at h
  have h1 : tc (1 : G) x = 1 := by simp [tc]
  rw [h1] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- (K2), followed by one more commutator. -/
theorem triple_pow_left_decomp (x y z : G) (n : ℕ) :
    tc (tc (x ^ n) y) z = tc (tc x y) z ^ n *
      tc (tc (tc x y) x) z ^ (n.choose 2) *
      tc (tc (tc (tc x y) x) x) z ^ (n.choose 3) := by
  have hc1 : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hf2 : tc (tc x y) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc1 (mem_lcs_zero _)
  have he3 : tc (tc (tc x y) x) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hf2 (mem_lcs_zero _)
  rw [tc_pow_formula S.h5 x y n,
    tc_mul_left_L1 S.h5
      (mul_mem (pow_mem (lcs_mem_of_le (by norm_num) hc1) n)
        (pow_mem (lcs_mem_of_le (by norm_num) hf2) (n.choose 2)))
      (lcs_mem_of_le (by norm_num) (pow_mem he3 (n.choose 3))),
    tc_mul_left_L1 S.h5 (pow_mem (lcs_mem_of_le (by norm_num) hc1) n)
      (lcs_mem_of_le (by norm_num) (pow_mem hf2 _)),
    tc_pow_left_L1 S.h5 hc1, tc_pow_left_L1 S.h5 (lcs_mem_of_le (by norm_num) hf2),
    tc_L3 S.h5 (pow_mem he3 (n.choose 3)), tc_L3 S.h5 he3, one_pow, mul_one]

/-- (F4): pairing the power expansion with another first-layer generator. -/
theorem F4 (g i h : Fin T.s) :
    tc (tc (T.x₁ g ^ T.d g) (T.x₁ i)) (T.x₁ h) =
      tc (tc (T.x₁ g) (T.x₁ i)) (T.x₁ h) ^ T.d g := by
  rw [S.triple_pow_left_decomp]
  have hc1 : tc (T.x₁ g) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hf2 : tc (tc (T.x₁ g) (T.x₁ i)) (T.x₁ g) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc1 (mem_lcs_zero _)
  have he3 : tc (tc (tc (T.x₁ g) (T.x₁ i)) (T.x₁ g)) (T.x₁ g) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hf2 (mem_lcs_zero _)
  have hpow : tc (tc (tc (T.x₁ g) (T.x₁ i)) (T.x₁ g)) (T.x₁ h) ^ T.d g = 1 :=
    S.triple_pow_mid hc1 (T.x₁ h) (S.Y1 g)
  have hC : T.d g ∣ (T.d g).choose 2 := by
    obtain ⟨m, hm⟩ := S.hd g
    rw [hm]
    exact ⟨(3 ^ (m + 1) - 1) / 2, ExpThree.choose2_eq m⟩
  obtain ⟨q, hq⟩ := hC
  rw [hq, pow_mul, hpow, one_pow, tc_L3 S.h5 he3, one_pow, mul_one, mul_one]

/-- The order `d(i)` divides `C(d(i),2)`, since every `d(i)` is an odd power of `3`. -/
theorem ch2_dvd_d (i : Fin T.s) : (T.d i : ℤ) ∣ T.ch i 2 := by
  obtain ⟨m, hm⟩ := S.hd i
  refine ⟨(((3 ^ (m + 1) - 1) / 2 : ℕ) : ℤ), ?_⟩
  unfold Data.ch
  rw [hm]
  exact_mod_cast ExpThree.choose2_eq m

section Coefficients

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

/-- Condition (C₁): `3 ∣ u_{ij}` when `d(i) = d(j)`. -/
theorem u3_eq {i j : Fin T.s} (hij : i < j) (hd : T.d i = T.d j) : (3 : ℤ) ∣ τ.u i j := by
  have h0 := hτ.C₁ i j hij
  have hq : T.q i j = 1 := by
    have e : T.d j / T.d i = 1 := by
      rw [← hd]; exact Nat.div_self (lt_trans Nat.zero_lt_one (S.valid.basis₁.one_lt i))
    simp [Data.q, e]
  rw [hq] at h0
  have h := Int.ModEq.dvd h0
  unfold Data.ch at h
  rw [zero_sub, dvd_neg, mul_one] at h
  obtain ⟨m, hm⟩ := S.hd i
  have hone := S.valid.basis₁.one_lt i
  generalize T.d i = d at h hm hone
  obtain ⟨e, he⟩ : ∃ e : ℕ, d = 3 * e := ⟨3 ^ m, by rw [hm, pow_succ, mul_comm]⟩
  have he0 : 0 < e := by omega
  have hde : (d : ℤ) = 3 * e := by exact_mod_cast he
  -- `C(d,2) = d (d-1)/2`, `2 C(d,3) = e (3e-1)(3e-2)`
  have c2 : d.choose 2 = d * ((d - 1) / 2) := by rw [hm]; exact choose2_eq m
  have c3 : ((d.choose 3 : ℕ) : ℤ) * 2 = (e : ℤ) * (3 * e - 1) * (3 * e - 2) := by
    have hdf := Nat.descFactorial_eq_factorial_mul_choose d 3
    have hd' : d.descFactorial 3 = (d - 2) * ((d - 1) * ((d - 0) * 1)) := by
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
    rw [hd', Nat.sub_zero] at hdf
    have h6 : (3 : ℕ).factorial = 6 := rfl
    rw [h6] at hdf
    have hd1 : 1 ≤ d := by omega
    have hd2 : 2 ≤ d := by omega
    have hz : ((d - 2 : ℕ) : ℤ) * (((d - 1 : ℕ) : ℤ) * ((d : ℤ) * 1)) = 6 * (d.choose 3 : ℤ) := by
      exact_mod_cast hdf
    push_cast [Nat.cast_sub hd1, Nat.cast_sub hd2] at hz
    rw [hde] at hz
    linarith
  -- `d ∣ u C(d,3)`, so `3e ∣ 2 u C(d,3) = e u (3e-1)(3e-2)`
  have h1 : (d : ℤ) ∣ τ.u i j * ((d.choose 3 : ℕ) : ℤ) := by
    have hw : (d : ℤ) ∣ τ.w i i j * (d.choose 2 : ℤ) := by
      rw [c2, Nat.cast_mul]; exact ⟨τ.w i i j * (((d - 1) / 2 : ℕ) : ℤ), by ring⟩
    have := dvd_sub h hw
    rwa [add_sub_cancel_right] at this
  have h3 : (3 : ℤ) ∣ τ.u i j * ((3 * e - 1) * (3 * e - 2)) := by
    have hh := h1.mul_right 2
    rw [mul_assoc, c3, hde] at hh
    have e2 : τ.u i j * ((e : ℤ) * (3 * e - 1) * (3 * e - 2)) =
        (τ.u i j * ((3 * e - 1) * (3 * e - 2))) * e := by ring
    rw [e2] at hh
    exact (mul_dvd_mul_iff_right (by exact_mod_cast he0.ne')).mp hh
  have e2 : τ.u i j * ((3 * e - 1) * (3 * e - 2)) =
      3 * (τ.u i j * (3 * e * e - 3 * e)) + 2 * τ.u i j := by ring
  rw [e2] at h3
  generalize τ.u i j * (3 * e * e - 3 * e) = Z at h3
  omega

/-- `3 ∣ u_{hi} q_{hi}` for `h < i`. -/
theorem uq3 {h i : Fin T.s} (hhi : h < i) : (3 : ℤ) ∣ τ.u h i * T.q h i := by
  by_cases hd : T.d h = T.d i
  · exact (S.u3_eq hτ hhi hd).mul_right _
  · refine Dvd.dvd.mul_left ?_ _
    simp only [Data.q]
    exact_mod_cast S.three_dvd_q hhi.le hd

/-- (c2): `3 ∣ crow_{rh}` for an active `h`; condition (B) modulo `3`. -/
theorem crow_act (r : Fin T.s) {h : Fin T.s} (hh : act h) : (3 : ℤ) ∣ crow T τ r h := by
  refine S.hind (fun y => crow T τ r y) (fun k => ?_) h hh
  have hB := hτ.B r k
  have ec : ∑ y, crow T τ r y * T.b y k = (∑ y, if r < y then τ.u r y * T.b y k else 0) -
      ∑ y, if y < r then τ.u y r * T.q y r * T.b y k else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [crow]
    split_ifs <;> ring
  rw [ec]
  have hd : (3 : ℤ) ∣ τ.v r k * T.d r := (by exact_mod_cast S.three_dvd_d r : (3 : ℤ) ∣ T.d r).mul_left _
  have he : (3 : ℤ) ∣ τ.v' r k * T.e k := (by exact_mod_cast S.he k : (3 : ℤ) ∣ T.e k).mul_left _
  generalize (∑ y, if r < y then τ.u r y * T.b y k else 0) = X at hB ⊢
  generalize (∑ y, if y < r then τ.u y r * T.q y r * T.b y k else 0) = Y at hB ⊢
  generalize τ.v r k * T.d r = P at hB hd
  generalize τ.v' r k * T.e k = Q at hB he
  omega

/-- Condition (D₁) modulo `3`, at an active index. -/
theorem D1_cf (a : Fin T.s) {x : Fin T.s} (hx : act x) :
    (3 : ℤ) ∣ (if x ≤ a then τ.w x a a else 0) + (if a < x then τ.w'' a a x else 0) := by
  refine S.hind (fun y => (if y ≤ a then τ.w y a a else 0) + (if a < y then τ.w'' a a y else 0))
    (fun kk => ?_) x hx
  have hD := dvd3_mod (hτ.D₁ a kk) (S.gcd_e3 a kk)
  have hc : (3 : ℤ) ∣ τ.v a kk * T.ch a 2 := (S.ch2_dvd a).mul_left _
  have e : (∑ y, ((if y ≤ a then τ.w y a a else 0) + (if a < y then τ.w'' a a y else 0)) *
      T.b y kk) = (∑ y, if y ≤ a then τ.w y a a * T.b y kk else 0) +
      ∑ y, if a < y then τ.w'' a a y * T.b y kk else 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
  rw [e]
  generalize τ.v a kk * T.ch a 2 = Z at hD hc
  generalize (∑ y, if y ≤ a then τ.w y a a * T.b y kk else 0) = A at hD ⊢
  generalize (∑ y, if a < y then τ.w'' a a y * T.b y kk else 0) = B at hD ⊢
  omega

/-- Condition (D₂) modulo `3`, at an active index. -/
theorem D2_cf {a c : Fin T.s} (hac : a < c) {x : Fin T.s} (hx : act x) :
    (3 : ℤ) ∣ (if x ≤ a then τ.w x a c else 0) + (if a < x ∧ x ≤ c then τ.w' a x c else 0) +
      (if c < x then τ.w'' a c x else 0) := by
  refine S.hind (fun y => (if y ≤ a then τ.w y a c else 0) +
    (if a < y ∧ y ≤ c then τ.w' a y c else 0) + (if c < y then τ.w'' a c y else 0))
    (fun kk => ?_) x hx
  have hD := dvd3_mod (hτ.D₂ a c kk hac) (S.gcd_e3 a kk)
  have e : (∑ y, ((if y ≤ a then τ.w y a c else 0) + (if a < y ∧ y ≤ c then τ.w' a y c else 0) +
      (if c < y then τ.w'' a c y else 0)) * T.b y kk) =
      (∑ y, if y ≤ a then τ.w y a c * T.b y kk else 0) +
      (∑ y, if a < y ∧ y ≤ c then τ.w' a y c * T.b y kk else 0) +
      (∑ y, if c < y then τ.w'' a c y * T.b y kk else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
  rw [e]
  exact hD

/-- (c3): `3 ∣ w_{hjk}` for an active `h`. -/
theorem w3 {h : Fin T.s} (hact : act h) {j k : Fin T.s} (hhj : h ≤ j) (hjk : j ≤ k) :
    (3 : ℤ) ∣ τ.w h j k := by
  rcases eq_or_lt_of_le hjk with rfl | hjk'
  · simpa [hhj, not_lt.mpr hhj] using S.D1_cf hτ j hact
  · simpa [hhj, not_lt.mpr hhj, not_lt.mpr (hhj.trans hjk'.le)] using S.D2_cf hτ hjk' hact

/-- (c3): `3 ∣ w'_{igh}` for an active `g`. -/
theorem w'3 {g : Fin T.s} (hact : act g) {i h : Fin T.s} (hig : i < g) (hgh : g ≤ h) :
    (3 : ℤ) ∣ τ.w' i g h := by
  simpa [not_le.mpr hig, hig, hgh, not_lt.mpr hgh] using S.D2_cf hτ (hig.trans_le hgh) hact


/-- (c3): `3 ∣ w''_{jkh}` for an active `h`. -/
theorem w''3 {j k h : Fin T.s} (hact : act h) (hjk : j < k) (hkh : k < h) :
    (3 : ℤ) ∣ τ.w'' j k h := by
  simpa [not_le.mpr (hjk.trans hkh), not_le.mpr hkh, hkh] using S.D2_cf hτ hjk hact

end Coefficients

/-! ### Small indices and the forms they kill -/

/-- An index with two distinct indices above it is small: `d(i) ∣ 3^μ`. -/
theorem small {i j k : Fin T.s} (hij : i < j) (hik : i < k) (hjk : j ≠ k) : T.d i ∣ 3 ^ μ := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact S.hsmall i j k hij h
  · exact S.hsmall i k j hik h

/-- `3^μ ∣ 3 · 3^{μ-1}` (truncated subtraction: `1 ∣ 3` when `μ = 0`). -/
theorem three_pow_dvd (μ : ℕ) : 3 ^ μ ∣ 3 * 3 ^ (μ - 1) := by
  rcases μ with _ | μ
  · simp
  · simp [pow_succ, mul_comm]

/-- (F2) for any pair: `c_{ab}^{d(a)} ∈ γ₃`. -/
theorem c_pow_mem (a b : Fin T.s) :
    tc (T.x₁ a) (T.x₁ b) ^ T.d a ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  sorry

/-- `[c_{ab}, w]^{d(a)} = 1` for `w ∈ γ₂`: the form `ω(c̄_{ab}, ·)` is killed by `d(a)`. -/
theorem c_pow_kill (a b : Fin T.s) {w : G} (hw : w ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc (tc (T.x₁ a) (T.x₁ b)) w ^ T.d a = 1 := by
  sorry

/-- A triple commutator beginning with `c_{ab}` is killed by `d(a)`. -/
theorem c_triple_kill (a b : Fin T.s) (x y : G) :
    tc (tc (tc (T.x₁ a) (T.x₁ b)) x) y ^ T.d a = 1 := by
  sorry

/-- `(n-1)/2` and `K n = C(n,3) - (n-1)/2 · C(n,2)` (`= -n(n²-1)/12` for odd `n`): the coefficients
of the degree-`n` defect `delta_general`. -/
def K (n : ℕ) : ℤ := ((n.choose 3 : ℕ) : ℤ) - (((n - 1) / 2 : ℕ) : ℤ) * ((n.choose 2 : ℕ) : ℤ)

omit S in
/-- `3^m ∣ K (3^{m+1})`: from `12 K n = -n(n-1)(n+1)`. -/
theorem K_dvd (m : ℕ) : ((3 ^ m : ℕ) : ℤ) ∣ K (3 ^ (m + 1)) := by
  sorry

section Values

variable {N : Type*} [AddCommGroup N] {A : G → N}
  (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
    A (a * b) = A a + A b)
include hA

/-- An additive map sends an `n`-torsion element to an `n`-torsion value. -/
theorem smul_of_pow_eq_one {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    {n : ℕ} (hp : z ^ n = 1) : (n : ℤ) • A z = 0 := by
  have h := addMapG_pow hA hz n
  rw [hp, addMapG_one hA] at h
  exact h.symm

/-- A multiple of `n` kills a value whose group element has order dividing `n`. -/
theorem smul_of_nat_dvd_of_pow_eq_one {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    {n : ℕ} {w : ℤ} (hw : (n : ℤ) ∣ w) (hp : z ^ n = 1) : w • A z = 0 := by
  obtain ⟨q, rfl⟩ := hw
  have h := S.smul_of_pow_eq_one hA hz hp
  have h' : ((n : ℤ) * q) • A z = q • ((n : ℤ) • A z) := by rw [smul_smul, mul_comm]
  rw [h', h, smul_zero]

/-- The degree-`n` defect for odd `n`:
`A([xⁿ,y][yⁿ,x]) = (n-1)/2 (A[c,xⁿ] - A[c,yⁿ]) + K n (A[c,x,x] - A[c,y,y])`, `c = [x,y]`
(this generalizes `Ab399.Setup.delta_reduced`, the case `n = 9`). -/
theorem delta_general (x y : G) {n : ℕ} (hn : Odd n) :
    A (tc (x ^ n) y * tc (y ^ n) x) =
      (((n - 1) / 2 : ℕ) : ℤ) • (A (tc (tc x y) (x ^ n)) - A (tc (tc x y) (y ^ n))) +
        K n • (A (tc (tc (tc x y) x) x) - A (tc (tc (tc x y) y) y)) := by
  sorry

/-- The top pair: if `h` is the only index above `i`, then `ω(c̄_{ih}, ·)` is killed by `3^μ` on
`γ₂` (generalizes `Ab399.Setup.omega_three`). -/
theorem omega_top {i h : Fin T.s} (hih : i < h) (htop : ∀ k, i < k → k = h) (a : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ((3 ^ μ : ℕ) : ℤ) • A (tc (tc (T.x₁ i) (T.x₁ h)) a) = 0 := by
  sorry

/-- For every pair `i < h`, `ω(c̄_{ih}, ·)` is killed by `3^μ` on `γ₂`: by `d(i) ∣ 3^μ` when a
second index lies above `i`, by `omega_top` otherwise. -/
theorem omega_le {i h : Fin T.s} (hih : i < h) (a : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ((3 ^ μ : ℕ) : ℤ) • A (tc (tc (T.x₁ i) (T.x₁ h)) a) = 0 := by
  sorry

/-- The reverse orientation of `omega_le`. -/
theorem omega_le_rev {i h : Fin T.s} (hih : i < h) (a : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ((3 ^ μ : ℕ) : ℤ) • A (tc a (tc (T.x₁ i) (T.x₁ h))) = 0 := by
  sorry

/-- A coefficient divisible by `3`, times `3^{μ-1}`, kills a value killed by `3^μ`. -/
theorem kill {v : N} (hv : ((3 ^ μ : ℕ) : ℤ) • v = 0) {w : ℤ} (hw : (3 : ℤ) ∣ w) :
    ((3 ^ (μ - 1) : ℕ) : ℤ) • (w • v) = 0 := by
  sorry

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

/-- The `h`-term `u_{ih} ω(c̄_{ih}, Ȳ_h)`, times `3^{μ-1}`, vanishes: `3 ∣ u_{ih}` by (c2) for an
active `h`, `Ȳ_h ∈ 3 L₂` for an inactive one. -/
theorem cY {i h : Fin T.s} (hih : i < h) :
    ((3 ^ (μ - 1) : ℕ) : ℤ) • (τ.u i h • A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h ^ T.d h))) = 0 := by
  sorry

/-- The `q`-term `u_{ih} q_{ih} ω(c̄_{ih}, Ȳ_i)`, times `3^{μ-1}`, vanishes: `3 ∣ u_{ih} q_{ih}`. -/
theorem cYlow {i h : Fin T.s} (hih : i < h) :
    ((3 ^ (μ - 1) : ℕ) : ℤ) • ((τ.u i h * T.q i h) •
      A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d i))) = 0 := by
  sorry

/-- `d(i) ∣ u_{ih} K(d(h))` for `i < h` (Theorem 1 of §10.2: the `t`-part of `T₁` vanishes). -/
theorem uK_dvd {i h : Fin T.s} (hih : i < h) : (T.d i : ℤ) ∣ τ.u i h * K (T.d h) := by
  sorry

theorem T1_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T1 T τ A = 0 := by
  sorry

theorem T2_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T2 T τ A = 0 := by
  sorry

theorem T3_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T3 T τ A = 0 := by
  sorry

theorem T4_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T4 T τ A = 0 := by
  sorry

theorem T5_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T5 T τ A = 0 := by
  sorry

end Values

end Setup

/-- **Every generator of Tahara's Theorem 6.1 has order dividing `3^{μ-1}`** in the situation
`Setup` (Theorem 12.6 of wiki 891, §12.3). -/
theorem Setup.gen_pow_eq_one {T : Data G} {act : Fin T.s → Prop} {μ : ℕ}
    (S : Setup T act μ) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) :
    T.gen τ ^ (3 ^ (μ - 1)) = 1 := by
  sorry

end ThirdInvariant

end GroupDimension
