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

omit S in
/-- `3^μ ∣ 3 · 3^{μ-1}` (truncated subtraction: `1 ∣ 3` when `μ = 0`). -/
theorem three_pow_dvd (μ : ℕ) : 3 ^ μ ∣ 3 * 3 ^ (μ - 1) := by
  rcases μ with _ | μ
  · simp
  · simp [pow_succ, mul_comm]

/-- (F2) for any pair: `c_{ab}^{d(a)} ∈ γ₃`. -/
theorem c_pow_mem (a b : Fin T.s) :
    tc (T.x₁ a) (T.x₁ b) ^ T.d a ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  have hY : T.x₁ a ^ T.d a ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := S.Y1 a
  have hc1 : tc (T.x₁ a) (T.x₁ b) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hleft : tc (T.x₁ a ^ T.d a) (T.x₁ b) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hY (mem_lcs_zero _)
  have hd2 : tc (tc (T.x₁ a) (T.x₁ b)) (T.x₁ a) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc1 (mem_lcs_zero _)
  have he3 : tc (tc (tc (T.x₁ a) (T.x₁ b)) (T.x₁ a)) (T.x₁ a) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hd2 (mem_lcs_zero _)
  have hf := tc_pow_formula S.h5 (T.x₁ a) (T.x₁ b) (T.d a)
  have hR : tc (tc (T.x₁ a) (T.x₁ b)) (T.x₁ a) ^ (T.d a).choose 2 *
      tc (tc (tc (T.x₁ a) (T.x₁ b)) (T.x₁ a)) (T.x₁ a) ^ (T.d a).choose 3 ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (pow_mem hd2 _) (lcs_mem_of_le (by norm_num) (pow_mem he3 _))
  have heq : tc (T.x₁ a) (T.x₁ b) ^ T.d a = tc (T.x₁ a ^ T.d a) (T.x₁ b) *
      (tc (tc (T.x₁ a) (T.x₁ b)) (T.x₁ a) ^ (T.d a).choose 2 *
        tc (tc (tc (T.x₁ a) (T.x₁ b)) (T.x₁ a)) (T.x₁ a) ^ (T.d a).choose 3)⁻¹ := by
    rw [hf]; group
  rw [heq]
  exact mul_mem hleft (inv_mem hR)

/-- `[c_{ab}, w]^{d(a)} = 1` for `w ∈ γ₂`: the form `ω(c̄_{ab}, ·)` is killed by `d(a)`. -/
theorem c_pow_kill (a b : Fin T.s) {w : G} (hw : w ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc (tc (T.x₁ a) (T.x₁ b)) w ^ T.d a = 1 := by
  have hc1 : tc (T.x₁ a) (T.x₁ b) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hz : tc (tc (T.x₁ a) (T.x₁ b) ^ T.d a) w ∈ (⊤ : Subgroup G).lowerCentralSeries 4 :=
    tc_mem (i := 2) (j := 1) (n := 4) (by omega) (S.c_pow_mem a b) hw
  have h1 : tc (tc (T.x₁ a) (T.x₁ b) ^ T.d a) w = 1 := by rwa [S.h5, mem_bot] at hz
  rwa [tc_pow_left_L1 S.h5 hc1 w] at h1

/-- A triple commutator beginning with `c_{ab}` is killed by `d(a)`. -/
theorem c_triple_kill (a b : Fin T.s) (x y : G) :
    tc (tc (tc (T.x₁ a) (T.x₁ b)) x) y ^ T.d a = 1 := by
  have hc1 : tc (T.x₁ a) (T.x₁ b) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hd2 : tc (tc (T.x₁ a) (T.x₁ b)) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc1 (mem_lcs_zero x)
  have hz : tc (tc (tc (T.x₁ a) (T.x₁ b) ^ T.d a) x) y ∈
      (⊤ : Subgroup G).lowerCentralSeries 4 := by
    have h3 : tc (tc (T.x₁ a) (T.x₁ b) ^ T.d a) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) (S.c_pow_mem a b) (mem_lcs_zero x)
    exact tc_mem (i := 3) (j := 0) (n := 4) (by omega) h3 (mem_lcs_zero y)
  have h1 : tc (tc (tc (T.x₁ a) (T.x₁ b) ^ T.d a) x) y = 1 := by rwa [S.h5, mem_bot] at hz
  rwa [tc_pow_left_L1 S.h5 hc1 x, tc_pow_left_L1 S.h5 (lcs_mem_of_le (by norm_num) hd2) y] at h1

/-- `(n-1)/2` and `K n = C(n,3) - (n-1)/2 · C(n,2)` (`= -n(n²-1)/12` for odd `n`): the coefficients
of the degree-`n` defect `delta_general`. -/
def K (n : ℕ) : ℤ := ((n.choose 3 : ℕ) : ℤ) - (((n - 1) / 2 : ℕ) : ℤ) * ((n.choose 2 : ℕ) : ℤ)

omit S in
/-- `3^m ∣ K (3^{m+1})`: from `12 K n = -n(n-1)(n+1)`. -/
theorem K_dvd (m : ℕ) : ((3 ^ m : ℕ) : ℤ) ∣ K (3 ^ (m + 1)) := by
  set n := 3 ^ (m + 1) with hn
  have hn3 : n = 3 * 3 ^ m := by rw [hn, pow_succ, mul_comm]
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ (by norm_num)
  have hn2 : 2 ≤ n := by
    have : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hodd : (n - 1) / 2 * 2 = n - 1 := by
    obtain ⟨k, hk⟩ : Odd n := Odd.pow (by decide)
    omega
  have c2n : n.choose 2 * 2 = n * (n - 1) := by
    rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd]
  have c3n : n.descFactorial 3 = 6 * n.choose 3 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have hdf : n.descFactorial 3 = (n - 2) * ((n - 1) * ((n - 0) * 1)) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  have hodd' : ((((n - 1) / 2 : ℕ) : ℤ)) * 2 = (n : ℤ) - 1 := by
    have h1 : (((n - 1) / 2 * 2 : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) := congrArg _ hodd
    rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_ofNat, Nat.cast_one] at h1
    exact h1
  have c2 : ((n.choose 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
    have := congrArg (fun t : ℕ => (t : ℤ)) c2n
    push_cast [Nat.cast_sub hn1] at this
    exact this
  have c3 : ((n.choose 3 : ℕ) : ℤ) * 6 = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
    have := congrArg (fun t : ℕ => (t : ℤ)) (c3n.symm.trans hdf)
    push_cast [Nat.cast_sub hn1, Nat.cast_sub hn2] at this
    linear_combination this
  have h12 : K n * 12 = -(n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) + 1) := by
    unfold K
    linear_combination 2 * c3 - 3 * ((((n - 1) / 2 : ℕ) : ℤ) * 2) * c2 -
      3 * ((n : ℤ) * ((n : ℤ) - 1)) * hodd'
  have hn3' : (n : ℤ) = 3 * ((3 ^ m : ℕ) : ℤ) := by exact_mod_cast hn3
  set e : ℤ := ((3 ^ m : ℕ) : ℤ)
  have h4 : K n * 4 = e * (-(3 * e - 1) * (3 * e + 1)) := by
    have h3 : (K n * 4 - e * (-(3 * e - 1) * (3 * e + 1))) * 3 = 0 := by
      rw [hn3'] at h12
      linear_combination h12
    rcases mul_eq_zero.mp h3 with h | h
    · linear_combination h
    · norm_num at h
  have hcop : IsCoprime e 4 := by
    have h34 : IsCoprime (3 : ℤ) 4 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      rfl
    have := h34.pow_left (m := m)
    simpa [e] using this
  exact hcop.dvd_of_dvd_mul_right ⟨_, h4⟩

section Values

variable {N : Type*} [AddCommGroup N] {A : G → N}
  (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
    A (a * b) = A a + A b)
include hA

omit S in
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
  have h := smul_of_pow_eq_one hA hz hp
  have h' : ((n : ℤ) * q) • A z = q • ((n : ℤ) • A z) := by rw [smul_smul, mul_comm]
  rw [h', h, smul_zero]

/-- The degree-`n` defect for odd `n`:
`A([xⁿ,y][yⁿ,x]) = (n-1)/2 (A[c,xⁿ] - A[c,yⁿ]) + K n (A[c,x,x] - A[c,y,y])`, `c = [x,y]`
(this generalizes `Ab399.Setup.delta_reduced`, the case `n = 9`). -/
theorem delta_general (x y : G) {n : ℕ} (hn : Odd n) :
    A (tc (x ^ n) y * tc (y ^ n) x) =
      (((n - 1) / 2 : ℕ) : ℤ) • (A (tc (tc x y) (x ^ n)) - A (tc (tc x y) (y ^ n))) +
        K n • (A (tc (tc (tc x y) x) x) - A (tc (tc (tc x y) y) y)) := by
  have hc : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hfx : tc (tc x y) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
  have hfy : tc (tc x y) y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
  have hgx : tc (tc (tc x y) x) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hfx (mem_lcs_zero _)
  have hgy : tc (tc (tc x y) y) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hfy (mem_lcs_zero _)
  have key : ∀ (c F₁ G₁ F₂ G₂ : G) (n : ℕ), Commute (F₁ * G₁) (c⁻¹ ^ n) →
      c ^ n * F₁ * G₁ * (c⁻¹ ^ n * F₂ * G₂) = F₁ * G₁ * (F₂ * G₂) := by
    intro c F₁ G₁ F₂ G₂ n h
    calc c ^ n * F₁ * G₁ * (c⁻¹ ^ n * F₂ * G₂) =
          c ^ n * ((F₁ * G₁) * c⁻¹ ^ n) * (F₂ * G₂) := by group
      _ = c ^ n * (c⁻¹ ^ n * (F₁ * G₁)) * (F₂ * G₂) := by rw [h.eq]
      _ = F₁ * G₁ * (F₂ * G₂) := by rw [inv_pow]; group
  have hx2 : tc (tc x y) x ^ n.choose 2 * tc (tc (tc x y) x) x ^ n.choose 3 ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (pow_mem hfx _) (lcs_mem_of_le (by norm_num) (pow_mem hgx _))
  have hfy' : tc (tc y x) y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega)
      (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _))
      (mem_lcs_zero _)
  have hgy' : tc (tc (tc y x) y) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hfy' (mem_lcs_zero _)
  have hy2 : tc (tc y x) y ^ n.choose 2 * tc (tc (tc y x) y) y ^ n.choose 3 ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (pow_mem hfy' _) (lcs_mem_of_le (by norm_num) (pow_mem hgy' _))
  have hcomm : Commute (tc (tc x y) x ^ n.choose 2 * tc (tc (tc x y) x) x ^ n.choose 3)
      ((tc x y)⁻¹ ^ n) :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (comm_eq_one S.h5 (by norm_num) hx2 (pow_mem (inv_mem hc) n))
  have hinv : tc y x = (tc x y)⁻¹ := (tc_inv x y).symm
  have hprod : tc (x ^ n) y * tc (y ^ n) x =
      tc (tc x y) x ^ n.choose 2 * tc (tc (tc x y) x) x ^ n.choose 3 *
        (tc (tc y x) y ^ n.choose 2 * tc (tc (tc y x) y) y ^ n.choose 3) := by
    rw [tc_pow_formula S.h5 x y n, tc_pow_formula S.h5 y x n, hinv]
    exact key _ _ _ _ _ _ hcomm
  have hFy : A (tc (tc y x) y) = -A (tc (tc x y) y) := by
    rw [hinv, S.tc_inv_left_L1 hc, addMapG_inv hA hfy]
  have hGy : A (tc (tc (tc y x) y) y) = -A (tc (tc (tc x y) y) y) := by
    rw [hinv, S.tc_inv_left_L1 hc, S.tc_inv_left_L1 (lcs_mem_of_le (by norm_num) hfy),
      addMapG_inv hA (lcs_mem_of_le (by norm_num) hgy)]
  have hsum : A (tc (x ^ n) y * tc (y ^ n) x) =
      ((n.choose 2 : ℕ) : ℤ) • (A (tc (tc x y) x) - A (tc (tc x y) y)) +
        ((n.choose 3 : ℕ) : ℤ) • (A (tc (tc (tc x y) x) x) - A (tc (tc (tc x y) y) y)) := by
    rw [hprod, hA _ hx2 _ hy2,
      hA _ (pow_mem hfx _) _ (lcs_mem_of_le (by norm_num) (pow_mem hgx _)),
      hA _ (pow_mem hfy' _) _ (lcs_mem_of_le (by norm_num) (pow_mem hgy' _)),
      addMapG_pow hA hfx, addMapG_pow hA hfy',
      addMapG_pow hA (lcs_mem_of_le (by norm_num) hgx),
      addMapG_pow hA (lcs_mem_of_le (by norm_num) hgy'), hFy, hGy]
    module
  have hC2 : ((n.choose 2 : ℕ) : ℤ) = (n : ℤ) * (((n - 1) / 2 : ℕ) : ℤ) := by
    have hev : 2 ∣ n - 1 := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, by omega⟩
    have : n.choose 2 = n * ((n - 1) / 2) := by
      rw [Nat.choose_two_right, Nat.mul_div_assoc n hev]
    exact_mod_cast this
  have kz : ∀ z : G, ((n.choose 2 : ℕ) : ℤ) • A (tc (tc x y) z) =
      (((n - 1) / 2 : ℕ) : ℤ) • A (tc (tc x y) (z ^ n)) -
        ((((n - 1) / 2 : ℕ) : ℤ) * ((n.choose 2 : ℕ) : ℤ)) • A (tc (tc (tc x y) z) z) := by
    intro z
    have hfz : tc (tc x y) z ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have hgz : tc (tc (tc x y) z) z ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) hfz (mem_lcs_zero _)
    have e := congrArg A (Star.tc_pow_right_K3 hc S.h5 z n)
    rw [hA _ (pow_mem hfz _) _ (lcs_mem_of_le (by norm_num) (pow_mem hgz _)),
      addMapG_pow hA hfz, addMapG_pow hA (lcs_mem_of_le (by norm_num) hgz)] at e
    rw [e, hC2]
    module
  rw [hsum, smul_sub, kz x, kz y]
  unfold K
  module

/-- The top pair: if `h` is the only index above `i`, then `ω(c̄_{ih}, ·)` is killed by `3^μ` on
`γ₂` (generalizes `Ab399.Setup.omega_three`). -/
theorem omega_top {i h : Fin T.s} (hih : i < h) (htop : ∀ k, i < k → k = h) (a : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ((3 ^ μ : ℕ) : ℤ) • A (tc (tc (T.x₁ i) (T.x₁ h)) a) = 0 := by
  classical
  set c : G := tc (T.x₁ i) (T.x₁ h) with hcdef
  let z : G := c⁻¹
  let X : Fin T.s → G := fun j => (T.x₁ j)⁻¹
  let F0 : G → N := fun b => ((3 ^ μ : ℕ) : ℤ) • A b
  have hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := inv_mem hc
  have hF : ∀ u ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      ∀ v ∈ (⊤ : Subgroup G).lowerCentralSeries 3, F0 (u * v) = F0 u + F0 v := by
    intro u hu v hv
    simp only [F0]
    rw [hA u (lcs_mem_of_le (by norm_num) hu) v (lcs_mem_of_le (by norm_num) hv), smul_add]
  have hconvert (p q : Fin T.s) : F0 ⁅z, ⁅X p, X q⁆⁆ =
      ((3 ^ μ : ℕ) : ℤ) • A (tc c (tc (T.x₁ q) (T.x₁ p))) := by
    simp only [F0, z, X]
    congr 2
    rw [tc_eq c (tc (T.x₁ q) (T.x₁ p)), tc_inv (T.x₁ q) (T.x₁ p),
      tc_eq (T.x₁ p) (T.x₁ q)]
  have hmem (p q : Fin T.s) : tc c (tc (T.x₁ p) (T.x₁ q)) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    lcs_mem_of_le (by norm_num)
      (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc
        (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)))
  have hfwd (p q : Fin T.s) : tc c (tc (T.x₁ p) (T.x₁ q)) ^ T.d p = 1 := by
    have hp := S.c_pow_kill p q hc
    rw [← tc_inv, inv_pow, hp, inv_one]
  have hrev (p q : Fin T.s) : tc c (tc (T.x₁ q) (T.x₁ p)) ^ T.d p = 1 := by
    have hcpq : tc (T.x₁ p) (T.x₁ q) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have e : tc (T.x₁ q) (T.x₁ p) = (tc (T.x₁ p) (T.x₁ q))⁻¹ := (tc_inv _ _).symm
    rw [e, S.tc_inv_right_L1 hc hcpq, inv_pow, hfwd p q, inv_one]
  have hsmallpair : ∀ p q : Fin T.s, p < q → ¬ (p = i ∧ q = h) → T.d p ∣ 3 ^ μ := by
    intro p q hpq hne
    rcases lt_trichotomy p i with hpi | hpi | hpi
    · exact S.small hpi (hpi.trans hih) hih.ne
    · exact absurd ⟨hpi, htop q (hpi ▸ hpq)⟩ hne
    · have hp := htop p hpi
      have hq := htop q (hpi.trans hpq)
      rw [hp, hq] at hpq
      exact absurd hpq (lt_irrefl _)
  have hcc : tc c c = 1 := by simp only [tc]; group
  have hcc' : tc c c⁻¹ = 1 := by simp only [tc]; group
  have hbase (p q : Fin T.s) : F0 ⁅z, ⁅X p, X q⁆⁆ = 0 := by
    rw [hconvert]
    rcases lt_trichotomy p q with hpq | hpq | hpq
    · by_cases hpair : p = i ∧ q = h
      · rw [hpair.1, hpair.2, ← tc_inv (T.x₁ i) (T.x₁ h), ← hcdef, hcc', addMapG_one hA,
          smul_zero]
      · obtain ⟨r, hr⟩ := hsmallpair p q hpq hpair
        exact S.smul_of_nat_dvd_of_pow_eq_one hA (hmem q p) ⟨r, by exact_mod_cast hr⟩ (hrev p q)
    · rw [hpq, show tc (T.x₁ q) (T.x₁ q) = 1 by simp only [tc]; group,
        show tc c 1 = 1 by simp only [tc]; group, addMapG_one hA, smul_zero]
    · by_cases hpair : q = i ∧ p = h
      · rw [hpair.1, hpair.2, ← hcdef, hcc, addMapG_one hA, smul_zero]
      · obtain ⟨r, hr⟩ := hsmallpair q p hpq hpair
        exact S.smul_of_nat_dvd_of_pow_eq_one hA (hmem q p) ⟨r, by exact_mod_cast hr⟩ (hfwd q p)
  have hgen : ∀ g ∈ (⊤ : Subgroup G), ∀ h ∈ (⊤ : Subgroup G), F0 ⁅z, ⁅g, h⁆⁆ = 0 := by
    intro g _ h _
    obtain ⟨α, hα⟩ := S.valid.basis₁.span g (mem_lcs_zero g)
    obtain ⟨β, hβ⟩ := S.valid.basis₁.span h (mem_lcs_zero h)
    have hprodα : oprod X (fun i => -α i) = oprod T.x₁ α := by
      unfold oprod
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      simp only [X, inv_zpow', neg_neg]
    have hprodβ : oprod X (fun i => -β i) = oprod T.x₁ β := by
      unfold oprod
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      simp only [X, inv_zpow', neg_neg]
    have hα' : (oprod X (fun i => -α i))⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
      rw [hprodα]
      exact hα
    have hβ' : (oprod X (fun i => -β i))⁻¹ * h ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
      rw [hprodβ]
      exact hβ
    have hzero (u v : G) (hu : u ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
        F0 ⁅z, ⁅u, v⁆⁆ = 0 :=
      ClassFour.B_L1_L2 S.h5 F0 hF hz
        (commutator_mem_lcs (i := 1) (j := 0) (n := 2) (by omega) hu (mem_lcs_zero v))
    have hzeroR (u v : G) (hv : v ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
        F0 ⁅z, ⁅u, v⁆⁆ = 0 :=
      ClassFour.B_L1_L2 S.h5 F0 hF hz
        (commutator_mem_lcs (i := 0) (j := 1) (n := 2) (by omega) (mem_lcs_zero u) hv)
    have eg : F0 ⁅z, ⁅g, h⁆⁆ = ∑ i, (-α i) • F0 ⁅z, ⁅X i, h⁆⁆ := by
      simpa only [] using (Ab399.GenericMaps.addMap_oprod_expandM
        (K := (⊤ : Subgroup G)) (N := (⊤ : Subgroup G).lowerCentralSeries 1)
        (F := fun u => F0 ⁅z, ⁅u, h⁆⁆) (x := X) (a := fun i => -α i) (v := g)
        (hNK := le_top)
        (hF := Ab399.GenericMaps.nested_left S.h5 F0 hF hz (h := h))
        (hF0 := fun u hu => hzero u h hu) (hx := fun i => mem_lcs_zero (X i)) (hv := hα'))
    have eh (i : Fin T.s) : F0 ⁅z, ⁅X i, h⁆⁆ = ∑ j, (-β j) • F0 ⁅z, ⁅X i, X j⁆⁆ := by
      simpa only [] using (Ab399.GenericMaps.addMap_oprod_expandM
        (K := (⊤ : Subgroup G)) (N := (⊤ : Subgroup G).lowerCentralSeries 1)
        (F := fun u => F0 ⁅z, ⁅X i, u⁆⁆) (x := X) (a := fun j => -β j) (v := h)
        (hNK := le_top)
        (hF := Ab399.GenericMaps.nested_right S.h5 F0 hF hz (h := X i))
        (hF0 := fun u hu => hzeroR (X i) u hu) (hx := fun j => mem_lcs_zero (X j)) (hv := hβ'))
    rw [eg]
    simp_rw [eh]
    simp only [hbase, smul_zero, Finset.sum_const_zero]
  rw [tc_eq]
  change F0 ⁅z, a⁻¹⁆ = 0
  exact ClassFour.addMap_vanish
    (N := (⊤ : Subgroup G).lowerCentralSeries 1) (H := ⊤) (K := ⊤)
    (A := fun u => F0 ⁅z, u⁆)
    (hle := le_rfl) (hA := ClassFour.addRight1 S.h5 F0 hF hz) (hgen := hgen)
    (a := a⁻¹) (inv_mem ha)

/-- For every pair `i < h`, `ω(c̄_{ih}, ·)` is killed by `3^μ` on `γ₂`: by `d(i) ∣ 3^μ` when a
second index lies above `i`, by `omega_top` otherwise. -/
theorem omega_le {i h : Fin T.s} (hih : i < h) (a : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ((3 ^ μ : ℕ) : ℤ) • A (tc (tc (T.x₁ i) (T.x₁ h)) a) = 0 := by
  by_cases htop : ∀ k, i < k → k = h
  · exact S.omega_top hA hih htop a ha
  · obtain ⟨k, hk⟩ := not_forall.mp htop
    obtain ⟨hik, hkh⟩ := not_imp.mp hk
    obtain ⟨r, hr⟩ := S.small hih hik (Ne.symm hkh)
    have hc : tc (T.x₁ i) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have hz : tc (tc (T.x₁ i) (T.x₁ h)) a ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc ha)
    exact S.smul_of_nat_dvd_of_pow_eq_one hA hz ⟨r, by exact_mod_cast hr⟩ (S.c_pow_kill i h ha)

/-- The reverse orientation of `omega_le`. -/
theorem omega_le_rev {i h : Fin T.s} (hih : i < h) (a : G)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ((3 ^ μ : ℕ) : ℤ) • A (tc a (tc (T.x₁ i) (T.x₁ h))) = 0 := by
  have hz : tc (tc (T.x₁ i) (T.x₁ h)) a ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (n := 3) (by omega)
      (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)) ha
  rw [← tc_inv, addMapG_inv hA (lcs_mem_of_le (by norm_num) hz), smul_neg,
    S.omega_le hA hih a ha, neg_zero]

omit S hA in
/-- A coefficient divisible by `3`, times `3^{μ-1}`, kills a value killed by `3^μ`. -/
theorem kill {v : N} (hv : ((3 ^ μ : ℕ) : ℤ) • v = 0) {w : ℤ} (hw : (3 : ℤ) ∣ w) :
    ((3 ^ (μ - 1) : ℕ) : ℤ) • (w • v) = 0 := by
  obtain ⟨w', rfl⟩ := hw
  obtain ⟨r, hr⟩ := three_pow_dvd μ
  have e : ((3 ^ (μ - 1) : ℕ) : ℤ) • (((3 : ℤ) * w') • v) =
      (w' * r) • (((3 ^ μ : ℕ) : ℤ) • v) := by
    rw [smul_smul, smul_smul]
    congr 1
    have hr' : ((3 : ℤ) * ((3 ^ (μ - 1) : ℕ) : ℤ)) = ((3 ^ μ : ℕ) : ℤ) * r := by exact_mod_cast hr
    linear_combination w' * hr'
  rw [e, hv, smul_zero]

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

/-- The `h`-term `u_{ih} ω(c̄_{ih}, Ȳ_h)`, times `3^{μ-1}`, vanishes: `3 ∣ u_{ih}` by (c2) for an
active `h`, `Ȳ_h ∈ 3 L₂` for an inactive one. -/
theorem cY {i h : Fin T.s} (hih : i < h) :
    ((3 ^ (μ - 1) : ℕ) : ℤ) • (τ.u i h • A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h ^ T.d h))) = 0 := by
  have hc : tc (T.x₁ i) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  by_cases hact : act h
  · have hu : (3 : ℤ) ∣ τ.u i h := by
      have h' := S.crow_act hτ i hact
      simpa [crow, hih, not_lt.mpr hih.le] using h'
    exact kill (S.omega_le hA hih _ (S.Y1 h)) hu
  · obtain ⟨a, ha, c, hc3, hY⟩ := S.hK h hact
    have hzero : tc (tc (T.x₁ i) (T.x₁ h)) c = 1 := by
      rw [← tc_inv, tc_L2_L1 S.h5 hc3 hc, inv_one]
    have hmap : tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h ^ T.d h) =
        tc (tc (T.x₁ i) (T.x₁ h)) a ^ 3 := by
      rw [hY, S.tc_mul_right_L1 hc (pow_mem ha 3), tc_pow_right_L1 S.h5 hc ha, hzero, mul_one]
    have hza : tc (tc (T.x₁ i) (T.x₁ h)) a ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc ha)
    rw [hmap, addMapG_pow hA hza, smul_smul (τ.u i h)]
    refine kill (S.omega_le hA hih a ha) ?_
    push_cast
    exact dvd_mul_left _ _

/-- The `q`-term `u_{ih} q_{ih} ω(c̄_{ih}, Ȳ_i)`, times `3^{μ-1}`, vanishes: `3 ∣ u_{ih} q_{ih}`. -/
theorem cYlow {i h : Fin T.s} (hih : i < h) :
    ((3 ^ (μ - 1) : ℕ) : ℤ) • ((τ.u i h * T.q i h) •
      A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d i))) = 0 := by
  exact kill (S.omega_le hA hih _ (S.Y1 i)) (S.uq3 hτ hih)

omit hA in
/-- `d(i) ∣ u_{ih} K(d(h))` for `i < h` (Theorem 1 of §10.2: the `t`-part of `T₁` vanishes). -/
theorem uK_dvd {i h : Fin T.s} (hih : i < h) : (T.d i : ℤ) ∣ τ.u i h * K (T.d h) := by
  obtain ⟨a, ha⟩ := S.hd i
  obtain ⟨b, hb⟩ := S.hd h
  have hdv := S.d_dvd hih.le
  rw [ha, hb] at hdv
  have hab : a + 1 ≤ b + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdv
  have hK := K_dvd b
  rw [hb]
  rcases lt_or_eq_of_le hab with hlt | heq
  · have h1 : ((T.d i : ℕ) : ℤ) ∣ ((3 ^ b : ℕ) : ℤ) := by
      rw [ha]
      exact_mod_cast Nat.pow_dvd_pow 3 (by omega)
    exact (h1.trans hK).mul_left _
  · have hu := S.u3_eq hτ hih (by rw [ha, hb, heq])
    have e : ((T.d i : ℕ) : ℤ) = 3 * ((3 ^ b : ℕ) : ℤ) := by
      rw [ha, heq]
      push_cast
      ring
    rw [e]
    exact mul_dvd_mul hu hK

theorem T1_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T1 T τ A = 0 := by
  classical
  unfold Star.T1
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun h _ => ?_
  split_ifs with hih
  · have hodd : Odd (T.d h) := by
      obtain ⟨m, hm⟩ := S.hd h
      rw [hm]
      exact Odd.pow (by decide)
    have hc : tc (T.x₁ i) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have hYi : tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d i) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc (S.Y1 i))
    have hxi : T.x₁ i ^ T.d h = (T.x₁ i ^ T.d i) ^ (T.d h / T.d i) := by
      rw [← pow_mul, S.d_mul_q hih.le]
    have hA1 : A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d h)) =
        T.q i h • A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d i)) := by
      rw [hxi, tc_pow_right_L1 S.h5 hc (S.Y1 i), addMapG_pow hA hYi]
      rfl
    have htri (z : G) : tc (tc (tc (T.x₁ i) (T.x₁ h)) z) z ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      lcs_mem_of_le (by norm_num) (tc_mem (i := 2) (j := 0) (n := 3) (by omega)
        (tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)) (mem_lcs_zero _))
    rw [S.delta_general hA _ _ hodd, hA1]
    set P : ℤ := (((T.d h - 1) / 2 : ℕ) : ℤ)
    set M : ℤ := ((3 ^ (μ - 1) : ℕ) : ℤ)
    have e : M • (τ.u i h • (P • (T.q i h • A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d i)) -
        A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h ^ T.d h))) +
        K (T.d h) • (A (tc (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i)) (T.x₁ i)) -
          A (tc (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h)) (T.x₁ h))))) =
        P • (M • ((τ.u i h * T.q i h) • A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i ^ T.d i)))) -
          P • (M • (τ.u i h • A (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h ^ T.d h)))) +
          (M * (τ.u i h * K (T.d h))) •
            A (tc (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ i)) (T.x₁ i)) -
          (M * (τ.u i h * K (T.d h))) •
            A (tc (tc (tc (T.x₁ i) (T.x₁ h)) (T.x₁ h)) (T.x₁ h)) := by
      module
    rw [e, S.cYlow hA hτ hih, S.cY hA hτ hih]
    simp only [smul_zero, sub_zero, zero_add]
    have hdv : ((T.d i : ℕ) : ℤ) ∣ M * (τ.u i h * K (T.d h)) := (S.uK_dvd hτ hih).mul_left _
    rw [S.smul_of_nat_dvd_of_pow_eq_one hA (htri _) hdv
        (S.c_triple_kill i h (T.x₁ i) (T.x₁ i)),
      S.smul_of_nat_dvd_of_pow_eq_one hA (htri _) hdv
        (S.c_triple_kill i h (T.x₁ h) (T.x₁ h)), sub_zero]
  · rw [smul_zero]

theorem T2_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T2 T τ A = 0 := by
  classical
  unfold Star.T2
  rw [smul_neg, neg_eq_zero, Finset.smul_sum]
  refine Finset.sum_eq_zero fun h _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hhi
  · have hc : tc (T.x₁ h) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have htri : tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have htriple : tc (tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i)) (T.x₁ i) ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) htri (mem_lcs_zero _)
    have hK3 : A (tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i ^ T.d i)) =
        ((T.d i : ℕ) : ℤ) • A (tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i)) +
          (((T.d i).choose 2 : ℕ) : ℤ) • A (tc (tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i)) (T.x₁ i)) := by
      rw [Star.tc_pow_right_K3 hc S.h5 (T.x₁ i) (T.d i),
        hA _ (pow_mem htri _) _ (lcs_mem_of_le (by norm_num) (pow_mem htriple _)),
        addMapG_pow hA htri, addMapG_pow hA (lcs_mem_of_le (by norm_num) htriple)]
    have hq : T.q h i * ((T.d h : ℕ) : ℤ) = ((T.d i : ℕ) : ℤ) := by
      unfold Data.q
      rw [mul_comm]
      exact_mod_cast S.d_mul_q hhi.le
    have hterm : (τ.u h i * T.q h i) • A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ i)) (T.x₁ i)) =
        τ.u h i • A (tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i ^ T.d i)) -
          (τ.u h i * (((T.d i).choose 2 : ℕ) : ℤ)) •
            A (tc (tc (tc (T.x₁ h) (T.x₁ i)) (T.x₁ i)) (T.x₁ i)) := by
      rw [S.F4 h i i, addMapG_pow hA htri, hK3, smul_smul,
        show τ.u h i * T.q h i * ((T.d h : ℕ) : ℤ) = τ.u h i * ((T.d i : ℕ) : ℤ) by
          rw [mul_assoc, hq]]
      module
    rw [hterm, smul_sub, S.cY hA hτ hhi, zero_sub, neg_eq_zero, smul_smul]
    have hC : ((T.d h : ℕ) : ℤ) ∣ (((T.d i).choose 2 : ℕ) : ℤ) := by
      have h1 : ((T.d h : ℕ) : ℤ) ∣ ((T.d i : ℕ) : ℤ) := by exact_mod_cast S.d_dvd hhi.le
      have h2 := S.ch2_dvd_d i
      unfold Data.ch at h2
      exact h1.trans h2
    exact S.smul_of_nat_dvd_of_pow_eq_one hA (lcs_mem_of_le (by norm_num) htriple)
      ((hC.mul_left _).mul_left _) (S.c_triple_kill h i (T.x₁ i) (T.x₁ i))
  · rw [smul_zero]

theorem T3_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T3 T τ A = 0 := by
  classical
  unfold Star.T3
  rw [smul_neg, neg_eq_zero, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun h _ => ?_
  split_ifs with high
  · obtain ⟨hig, hgh⟩ := high
    by_cases htop : ∀ k, i < k → k = g
    · -- the top pair: `h = g`, and the value is `[Y_g, c_{ig}]` (Jacobi)
      have hhg : h = g := htop h (hig.trans_le hgh)
      subst hhg
      have hF : ∀ u ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
          ∀ v ∈ (⊤ : Subgroup G).lowerCentralSeries 3, A (u * v) = A u + A v := by
        intro u hu v hv
        exact hA u (lcs_mem_of_le (by norm_num) hu) v (lcs_mem_of_le (by norm_num) hv)
      have hYself : tc (T.x₁ h ^ T.d h) (T.x₁ h) = 1 :=
        tc_eq_one_iff.mpr (Commute.pow_left (Commute.refl _) _)
      have hU : A ⁅⁅(T.x₁ h)⁻¹, (T.x₁ i)⁻¹⁆, (T.x₁ h ^ T.d h)⁻¹⁆ =
          -A (tc (T.x₁ h ^ T.d h) (tc (T.x₁ i) (T.x₁ h))) := by
        calc A ⁅⁅(T.x₁ h)⁻¹, (T.x₁ i)⁻¹⁆, (T.x₁ h ^ T.d h)⁻¹⁆ =
            A ⁅tc (T.x₁ h) (T.x₁ i), (T.x₁ h ^ T.d h)⁻¹⁆ := by rw [tc_eq]
          _ = -A ⁅(T.x₁ h ^ T.d h)⁻¹, tc (T.x₁ h) (T.x₁ i)⁆ :=
            Ab399.GenericMaps.B_swap S.h5 A hF
              (commutator_mem_lcs (i := 1) (j := 1) (n := 3) (by omega)
                (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _)
                  (mem_lcs_zero _))
                (inv_mem (S.Y1 h)))
          _ = -A (tc (T.x₁ h ^ T.d h) (tc (T.x₁ i) (T.x₁ h))) := by
              rw [tc_eq (T.x₁ h ^ T.d h) (tc (T.x₁ i) (T.x₁ h)),
                tc_inv (T.x₁ i) (T.x₁ h), tc_eq (T.x₁ h) (T.x₁ i)]
      have hV : A ⁅⁅(T.x₁ h ^ T.d h)⁻¹, (T.x₁ h)⁻¹⁆, (T.x₁ i)⁻¹⁆ = 0 := by
        rw [← tc_eq (T.x₁ h ^ T.d h) (T.x₁ h), hYself, commutatorElement_one_left,
          addMapG_one hF]
      have hW : A ⁅⁅(T.x₁ i)⁻¹, (T.x₁ h ^ T.d h)⁻¹⁆, (T.x₁ h)⁻¹⁆ =
          A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ i)) (T.x₁ h)) := by
        calc A ⁅⁅(T.x₁ i)⁻¹, (T.x₁ h ^ T.d h)⁻¹⁆, (T.x₁ h)⁻¹⁆ =
            A ⁅(tc (T.x₁ h ^ T.d h) (T.x₁ i))⁻¹, (T.x₁ h)⁻¹⁆ := by
              rw [tc_inv (T.x₁ h ^ T.d h) (T.x₁ i), tc_eq (T.x₁ i) (T.x₁ h ^ T.d h)]
          _ = A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ i)) (T.x₁ h)) := by
            rw [tc_eq (tc (T.x₁ h ^ T.d h) (T.x₁ i)) (T.x₁ h)]
      have hJ := ClassFour.jacobi4 S.h5 A hF (T.x₁ h)⁻¹ (T.x₁ i)⁻¹
        (z := (T.x₁ h ^ T.d h)⁻¹) (inv_mem (S.Y1 h))
      rw [hU, hV, hW, add_zero] at hJ
      have hAB : A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ i)) (T.x₁ h)) =
          A (tc (T.x₁ h ^ T.d h) (tc (T.x₁ i) (T.x₁ h))) := by
        apply eq_of_sub_eq_zero
        rw [sub_eq_add_neg, add_comm]
        exact hJ
      rw [hAB]
      by_cases ha : act h
      · exact kill (S.omega_le_rev hA hig _ (S.Y1 h)) (S.w'3 hτ ha hig le_rfl)
      · obtain ⟨a, ha1, c, hc3, hY⟩ := S.hK h ha
        have hc12 : tc (T.x₁ i) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
          tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
        have hza : tc a (tc (T.x₁ i) (T.x₁ h)) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
          lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 1) (n := 3) (by omega) ha1 hc12)
        rw [hY, tc_mul_left_L1 S.h5 (pow_mem ha1 3) (lcs_mem_of_le (by norm_num) hc3),
          tc_pow_left_L1 S.h5 ha1, tc_L2_L1 S.h5 hc3 hc12, mul_one, addMapG_pow hA hza,
          smul_smul (τ.w' i h h)]
        refine kill (S.omega_le_rev hA hig a ha1) ?_
        push_cast
        exact dvd_mul_left _ _
    · -- a second index above `i`: everything is killed by `d(i) ∣ 3^μ`
      obtain ⟨k, hk⟩ := not_forall.mp htop
      obtain ⟨hik, hkg⟩ := not_imp.mp hk
      obtain ⟨r, hr⟩ := S.small hig hik (Ne.symm hkg)
      have hrr : ((T.d i : ℕ) : ℤ) ∣ ((3 ^ μ : ℕ) : ℤ) := ⟨r, by exact_mod_cast hr⟩
      have hkill : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
          ((3 ^ μ : ℕ) : ℤ) • A (tc (tc a (T.x₁ i)) (T.x₁ h)) = 0 := by
        intro a ha
        have hi2 : tc a (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
          tc_mem (i := 1) (j := 0) (n := 2) (by omega) ha (mem_lcs_zero _)
        have hz3 : tc (tc a (T.x₁ i)) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
          tc_mem (i := 2) (j := 0) (n := 3) (by omega) hi2 (mem_lcs_zero _)
        exact S.smul_of_nat_dvd_of_pow_eq_one hA (lcs_mem_of_le (by norm_num) hz3) hrr
          (S.triple_pow_mid ha (T.x₁ h) (S.Y1 i))
      by_cases ha : act g
      · exact kill (hkill _ (S.Y1 g)) (S.w'3 hτ ha hig hgh)
      · obtain ⟨a, ha1, c, hc, hY⟩ := S.hK g ha
        have hinner : tc a (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
          tc_mem (i := 1) (j := 0) (n := 2) (by omega) ha1 (mem_lcs_zero _)
        have hsecond : tc c (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
          tc_mem (i := 2) (j := 0) (n := 3) (by omega) hc (mem_lcs_zero _)
        have hz3 : tc (tc a (T.x₁ i)) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
          tc_mem (i := 2) (j := 0) (n := 3) (by omega) hinner (mem_lcs_zero _)
        have hz : tc (tc (T.x₁ g ^ T.d g) (T.x₁ i)) (T.x₁ h) =
            tc (tc a (T.x₁ i)) (T.x₁ h) ^ 3 := by
          rw [hY, tc_mul_left_L1 S.h5 (pow_mem ha1 3) (lcs_mem_of_le (by norm_num) hc),
            tc_pow_left_L1 S.h5 ha1,
            tc_mul_left_L1 S.h5 (lcs_mem_of_le (by norm_num) (pow_mem hinner 3))
              (lcs_mem_of_le (by norm_num) hsecond),
            tc_pow_left_L1 S.h5 (lcs_mem_of_le (by norm_num) hinner),
            tc_L3 S.h5 hsecond, mul_one]
        rw [hz, addMapG_pow hA (lcs_mem_of_le (by norm_num) hz3), smul_smul (τ.w' i g h)]
        refine kill (hkill a ha1) ?_
        push_cast
        exact dvd_mul_left _ _
  · rw [smul_zero]

theorem T4_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T4 T τ A = 0 := by
  classical
  unfold Star.T4
  rw [smul_neg, neg_eq_zero, Finset.smul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun h _ => ?_
  split_ifs with hjkh
  · obtain ⟨hjk, hkh⟩ := hjkh
    obtain ⟨r, hr⟩ := S.hsmall j k h hjk hkh
    have hrr : ((T.d j : ℕ) : ℤ) ∣ ((3 ^ μ : ℕ) : ℤ) := ⟨r, by exact_mod_cast hr⟩
    have hc : tc (T.x₁ j) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have hkill : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
        ((3 ^ μ : ℕ) : ℤ) • A (tc a (tc (T.x₁ j) (T.x₁ k))) = 0 := by
      intro a ha
      have hz : tc a (tc (T.x₁ j) (T.x₁ k)) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (i := 1) (j := 1) (n := 3) (by omega) ha hc
      have hp : tc a (tc (T.x₁ j) (T.x₁ k)) ^ T.d j = 1 := by
        have h' := S.c_pow_kill j k ha
        rw [← tc_inv, inv_pow, h', inv_one]
      exact S.smul_of_nat_dvd_of_pow_eq_one hA (lcs_mem_of_le (by norm_num) hz) hrr hp
    by_cases ha : act h
    · exact kill (hkill _ (S.Y1 h)) (S.w''3 hτ ha hjk hkh)
    · obtain ⟨a, ha1, c, hc3, hY⟩ := S.hK h ha
      have hz : tc (T.x₁ h ^ T.d h) (tc (T.x₁ j) (T.x₁ k)) =
          tc a (tc (T.x₁ j) (T.x₁ k)) ^ 3 := by
        rw [hY, tc_mul_left_L1 S.h5 (pow_mem ha1 3) (lcs_mem_of_le (by norm_num) hc3),
          tc_pow_left_L1 S.h5 ha1, tc_L2_L1 S.h5 hc3 hc, mul_one]
      have hza : tc a (tc (T.x₁ j) (T.x₁ k)) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
        lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 1) (n := 3) (by omega) ha1 hc)
      rw [hz, addMapG_pow hA hza, smul_smul (τ.w'' j k h)]
      refine kill (hkill a ha1) ?_
      push_cast
      exact dvd_mul_left _ _
  · rw [smul_zero]

omit hτ in
theorem T5_eq : ((3 ^ (μ - 1) : ℕ) : ℤ) • Star.T5 T τ A = 0 := by
  suffices h : Star.T5 T τ A = 0 by rw [h, smul_zero]
  unfold Star.T5
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  have hc2 : tc (T.x₂ k) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) (S.x2mem k) (mem_lcs_zero _)
  have ht3 : tc (tc (T.x₂ k) (T.x₁ i)) (T.x₁ i) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hc2 (mem_lcs_zero _)
  have hp : tc (tc (T.x₂ k) (T.x₁ i)) (T.x₁ i) ^ T.d i = 1 :=
    S.triple_pow_mid (S.x2mem k) (T.x₁ i) (S.Y1 i)
  exact S.smul_of_nat_dvd_of_pow_eq_one hA (lcs_mem_of_le (by norm_num) ht3)
    ((S.ch2_dvd_d i).mul_left _) hp

end Values

/-- Tahara's generators lie in `γ₃`. -/
theorem gen_mem {τ : Coeffs T.s T.t} (_hτ : T.Admissible τ) :
    T.gen τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  classical
  have hgA : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    unfold Data.genA
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
        split_ifs
        · exact zpow_mem (tc_mem (i := 1) (j := 0) (n := 2) (by omega) (S.Y1 i)
            (mem_lcs_zero _)) _
        · exact one_mem _
  have memB : ∀ (i : Fin T.s) (k : Fin T.t) (v : ℤ), (List.ofFn fun l => if k < l then
      tc (T.x₂ l) (T.x₂ k) ^ T.b i l else 1).prod ^ v ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i k v
    refine zpow_mem (list_prod_mem fun y hy => ?_) _
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
    split_ifs
    · exact zpow_mem (tc_mem (i := 1) (j := 1) (n := 3) (by omega) (S.x2mem l) (S.x2mem k)) _
    · exact one_mem _
  have hgB : T.genB τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    unfold Data.genB
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
        exact memB i k _
  have hgC : T.genC τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    unfold Data.genC
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
        exact list_prod_mem fun y hy => by
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
          split_ifs
          · exact zpow_mem (tc_mem (i := 2) (j := 0) (n := 3) (by omega)
              (tc_mem (i := 1) (j := 0) (n := 2) (by omega) (S.Y1 i) (mem_lcs_zero _))
              (mem_lcs_zero _)) _
          · exact one_mem _
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    Subgroup.lowerCentralSeries_antitone ⊤ (by norm_num)
  rw [Data.gen]
  exact mul_mem (mul_mem hgA (h32 hgB)) (h32 hgC)

end Setup

/-- **Every generator of Tahara's Theorem 6.1 has order dividing `3^{μ-1}`** in the situation
`Setup` (Theorem 12.6 of wiki 891, §12.3). -/
theorem Setup.gen_pow_eq_one {T : Data G} {act : Fin T.s → Prop} {μ : ℕ}
    (S : Setup T act μ) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) :
    T.gen τ ^ (3 ^ (μ - 1)) = 1 := by
  classical
  have hg2 := S.gen_mem hτ
  let _ : CommGroup ↥((⊤ : Subgroup G).lowerCentralSeries 2) :=
    commGroupOfComm _ (fun a ha b hb => comm_L2 S.h5 ha hb)
  let A : G → Additive ↥((⊤ : Subgroup G).lowerCentralSeries 2) := fun g =>
    if hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2 then Additive.ofMul ⟨g, hg⟩ else 0
  have hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2, A (a * b) = A a + A b := by
    intro a ha b hb
    simp only [A, ha, hb, mul_mem ha hb, ↓reduceDIte]
    rfl
  have h2 := Star.two_smul_gen_eq S.h5 S.valid hτ hA
  have hM : ((3 ^ (μ - 1) : ℕ) : ℤ) • ((2 : ℤ) • A (T.gen τ)) = 0 := by
    have h2' := congrArg (fun v => ((3 ^ (μ - 1) : ℕ) : ℤ) • v) h2
    simp only [smul_add] at h2'
    rw [S.T1_eq hA hτ, S.T2_eq hA hτ, S.T3_eq hA hτ, S.T4_eq hA hτ, S.T5_eq hA] at h2'
    simp only [add_zero] at h2'
    exact h2'
  have hg' : T.gen τ ^ (3 ^ (μ - 1)) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := pow_mem hg2 _
  have hsq : (T.gen τ ^ (3 ^ (μ - 1))) ^ 2 = 1 := by
    have e : A ((T.gen τ ^ (3 ^ (μ - 1))) ^ 2) = 0 := by
      rw [addMapG_pow hA hg', addMapG_pow hA hg2, smul_smul, mul_comm, ← smul_smul]
      exact_mod_cast hM
    simp only [A, pow_mem hg' 2, ↓reduceDIte] at e
    have e' := congrArg Additive.toMul e
    rw [toMul_ofMul, toMul_zero] at e'
    simpa using congrArg Subtype.val e'
  obtain ⟨m, hm⟩ := S.htor _ hg'
  have hcop : Nat.gcd 2 (3 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 2 3)
  have hord : orderOf (T.gen τ ^ (3 ^ (μ - 1))) = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hm)
    rw [hcop] at h
    exact Nat.dvd_one.mp h
  exact orderOf_eq_one_iff.mp hord

end ThirdInvariant

end GroupDimension
