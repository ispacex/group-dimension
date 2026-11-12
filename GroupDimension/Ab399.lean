module

public import GroupDimension.Star

@[expose] public section

/-!
# `D₅ = 1` for `Q_ab ≅ C₃ × C₉ × C₉` (MATH-448)

`Q_ab` of type `[3, 9, 9]`, with no condition on `γ₄`; the substantive case is `exp γ₄ = 9` (e.g.
`γ₄ ≅ C₉`), left open by Theorem 6.11 (remark 6.13 of the paper). The proof (MATH-446, Kimi's note `case_b.md`, Theorem 2 and Corollary 3 with the
corrections of the review, comment 8041, and the conclusion of comment 8035) evaluates the exact
identity `(⋆)` (`Star.two_smul_gen_eq`) term by term in the basis of `G4Cube.lean` (heights flag and
the kernel of the cube map; `act` = the index set `A`):
* `T₅ = 0`: `d(i) ∣ binom(d(i), 2)` and `[a, x_i, x_i]^{d(i)} = 1` (K4);
* every term with the index `i₀` (`d(i₀) = 3`) vanishes: `c̄_{i₀ j}` has order `3` in `L₂`, and each
  coefficient carries a factor `3` by (c1)–(c3), or the class `Ȳ_h` lies in `3 L₂` (inactive `h`);
* the terms with the pair `(i₁, i₂)` (`d = 9, 9`) vanish because `ω(c̄_{i₁ i₂}, ·)` is `3`-torsion:
  `L₂` is spanned by `c̄_{i₀ i₁}`, `c̄_{i₀ i₂}` (of order `3`) and `c̄_{i₁ i₂}`, and
  `ω(c̄, c̄) = 0`; the coefficients are `u_{i₁ i₂} = 3U` (c1), `(n-1)/2 = 4`, `n(n²-1)/12 = 60`.
No condition on `γ₄` is needed (its exponent divides `9` automatically).
-/

namespace GroupDimension

namespace Ab399

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The situation: class `≤ 4`, Tahara's data whose first-layer basis has exactly three elements
`x_{i₀}, x_{i₁}, x_{i₂}` of orders `3, 9, 9`, the active indices `act` of the basis adapted to the
kernel of the cube map (as in `ExpThree.SetupB`, without `γ₄³ = 1`). -/
structure Setup (T : Data G) (act : Fin T.s → Prop) (i₀ i₁ i₂ : Fin T.s) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  htor : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1
  valid : T.Valid
  h01 : i₀ < i₁
  h12 : i₁ < i₂
  hall : ∀ i, i = i₀ ∨ i = i₁ ∨ i = i₂
  hd₀ : T.d i₀ = 3
  hd₁ : T.d i₁ = 9
  hd₂ : T.d i₂ = 9
  he : ∀ k, 3 ∣ T.e k
  hf : ∀ l, 3 ∣ T.f l
  hK : ∀ i, ¬ act i → ∃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, T.x₁ i ^ T.d i = a ^ 3 * c
  hind : ∀ cf : Fin T.s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * T.b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h

/-! Helpers for maps into an abelian group `M` that are additive on `γ₄`, beyond those of
`ClassFour` (section `F`, now stated for any `AddCommGroup`; `F_one`, `B_L1_L2`, `addRight1`,
`jacobi4`, … are used from there). -/
namespace GenericMaps

variable {M : Type*} [AddCommGroup M]
variable (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
include h5
variable (F : G → M)
  (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
    F (a * b) = F a + F b)
include hF

omit h5 hF in
/-- Expansion of a uniqueness-basis product through a map additive on `K` and zero on `N`. -/
theorem addMap_oprod_expandM {K N : Subgroup G} (hNK : N ≤ K) {F : G → M}
    (hF : ∀ a ∈ K, ∀ b ∈ K, F (a * b) = F a + F b) (hF0 : ∀ a ∈ N, F a = 0)
    {n : ℕ} {x : Fin n → G} (hx : ∀ i, x i ∈ K) {a : Fin n → ℤ} {v : G}
    (hv : (oprod x a)⁻¹ * v ∈ N) : F v = ∑ i, a i • F (x i) := by
  have e : v = oprod x a * ((oprod x a)⁻¹ * v) := (mul_inv_cancel_left _ _).symm
  rw [e, hF _ (oprod_mem hx a) _ (hNK hv), hF0 _ hv, add_zero, addMapG_oprod hF hx]

/-- Skew-symmetry of a degree-four commutator read through `F`. -/
theorem B_swap {a b : G} (hab : ⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3) :
    F ⁅a, b⁆ = -F ⁅b, a⁆ := by
  rw [← commutatorElement_inv a b]
  rw [addMapG_inv hF hab, neg_neg]

/-- Additivity of `(a,b) ↦ F [c,[a,b]]` in `a`, for `c ∈ γ₂`. -/
theorem nested_left {c h : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ∀ a ∈ (⊤ : Subgroup G), ∀ b ∈ (⊤ : Subgroup G),
      F ⁅c, ⁅a * b, h⁆⁆ = F ⁅c, ⁅a, h⁆⁆ + F ⁅c, ⁅b, h⁆⁆ := by
  intro a _ b _
  have ha : ⁅a, h⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one _ _
  have hb : ⁅b, h⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one _ _
  have hcj : F ⁅c, a * ⁅b, h⁆ * a⁻¹⁆ = F ⁅c, ⁅b, h⁆⁆ := by
    calc F ⁅c, a * ⁅b, h⁆ * a⁻¹⁆ = -F ⁅a * ⁅b, h⁆ * a⁻¹, c⁆ :=
        B_swap h5 F hF (commutator_mem_lcs (by norm_num) hc (conj_mem_lcs 1 hb a))
      _ = -F ⁅⁅b, h⁆, c⁆ := by rw [B_conj_L1 h5 F hF hb hc]
      _ = F ⁅c, ⁅b, h⁆⁆ := (B_swap h5 F hF (commutator_mem_lcs (by norm_num) hc hb)).symm
  rw [comm_mul_left, addRight1 h5 F hF hc _ (conj_mem_lcs 1 hb a) _ ha, hcj, add_comm]

/-- Additivity of `(a,b) ↦ F [c,[a,b]]` in `b`, for `c ∈ γ₂`. -/
theorem nested_right {c h : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ∀ a ∈ (⊤ : Subgroup G), ∀ b ∈ (⊤ : Subgroup G),
      F ⁅c, ⁅h, a * b⁆⁆ = F ⁅c, ⁅h, a⁆⁆ + F ⁅c, ⁅h, b⁆⁆ := by
  intro a _ b _
  have ha : ⁅h, a⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one _ _
  have hb : ⁅h, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := commutator_mem_lcs_one _ _
  have hcj : F ⁅c, a * ⁅h, b⁆ * a⁻¹⁆ = F ⁅c, ⁅h, b⁆⁆ := by
    calc F ⁅c, a * ⁅h, b⁆ * a⁻¹⁆ = -F ⁅a * ⁅h, b⁆ * a⁻¹, c⁆ :=
        B_swap h5 F hF (commutator_mem_lcs (by norm_num) hc (conj_mem_lcs 1 hb a))
      _ = -F ⁅⁅h, b⁆, c⁆ := by rw [B_conj_L1 h5 F hF hb hc]
      _ = F ⁅c, ⁅h, b⁆⁆ := (B_swap h5 F hF (commutator_mem_lcs (by norm_num) hc hb)).symm
  rw [comm_mul_right, addRight1 h5 F hF hc _ ha _ (conj_mem_lcs 1 hb a), hcj]

end GenericMaps

namespace Setup

variable {T : Data G} {act : Fin T.s → Prop} {i₀ i₁ i₂ : Fin T.s} (S : Setup T act i₀ i₁ i₂)
include S

/-- Every displayed order is a positive power of `3`; this packages `hd₀`, `hd₁`, `hd₂`
in the form used by the general congruence arguments of `G4Cube.lean`. -/
theorem hd (i : Fin T.s) : ∃ m : ℕ, T.d i = 3 ^ (m + 1) := by
  rcases S.hall i with rfl | rfl | rfl
  · exact ⟨0, by norm_num [S.hd₀]⟩
  · exact ⟨1, by norm_num [S.hd₁]⟩
  · exact ⟨1, by norm_num [S.hd₂]⟩

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

/-- Every finite sum over the first-layer indices has only the three displayed terms. -/
theorem sum_three {M : Type*} [AddCommGroup M] (f : Fin T.s → M) :
    ∑ i, f i = f i₀ + f i₁ + f i₂ := by
  classical
  have hu : (Finset.univ : Finset (Fin T.s)) = {i₀, i₁, i₂} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact S.hall i
  have hi₀ : i₀ ∉ ({i₁, i₂} : Finset (Fin T.s)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨S.h01.ne, (S.h01.trans S.h12).ne⟩
  have hi₁ : i₁ ∉ ({i₂} : Finset (Fin T.s)) := by
    simpa only [Finset.mem_singleton] using S.h12.ne
  rw [hu, Finset.sum_insert hi₀, Finset.sum_insert hi₁, Finset.sum_singleton, add_assoc]

/-- (F2): the cube of a commutator involving `x_{i₀}` lies in `γ₃`. -/
theorem c0_cube_mem (j : Fin T.s) : tc (T.x₁ i₀) (T.x₁ j) ^ 3 ∈
    (⊤ : Subgroup G).lowerCentralSeries 2 := by
  have hY0 : T.x₁ i₀ ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [← S.hd₀]
    exact S.Y1 i₀
  have hleft : tc (T.x₁ i₀ ^ 3) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hY0 (mem_lcs_zero _)
  have hd2 : tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega)
      (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _))
      (mem_lcs_zero _)
  have he3 : tc (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀)) (T.x₁ i₀) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hd2 (mem_lcs_zero _)
  have hf := tc_pow_formula S.h5 (T.x₁ i₀) (T.x₁ j) 3
  norm_num at hf
  have hR : tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀) ^ 3 *
      tc (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀)) (T.x₁ i₀) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (pow_mem hd2 3) (lcs_mem_of_le (by norm_num) he3)
  have heq : tc (T.x₁ i₀) (T.x₁ j) ^ 3 = tc (T.x₁ i₀ ^ 3) (T.x₁ j) *
      (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀) ^ 3 *
        tc (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀)) (T.x₁ i₀))⁻¹ := by
    calc tc (T.x₁ i₀) (T.x₁ j) ^ 3 =
        (tc (T.x₁ i₀) (T.x₁ j) ^ 3 * tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀) ^ 3 *
          tc (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀)) (T.x₁ i₀)) *
        (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀) ^ 3 *
          tc (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ i₀)) (T.x₁ i₀))⁻¹ := by group
      _ = _ := by rw [← hf]
  rw [heq]
  exact mul_mem hleft (inv_mem hR)

/-- (F2): `[c_{i₀j}, a]³ = 1` for `a ∈ γ₂`. -/
theorem c0_pow_three (j : Fin T.s) {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc (tc (T.x₁ i₀) (T.x₁ j)) a ^ 3 = 1 := by
  have hc1 : tc (T.x₁ i₀) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hz : tc (tc (T.x₁ i₀) (T.x₁ j) ^ 3) a ∈
      (⊤ : Subgroup G).lowerCentralSeries 4 :=
    tc_mem (i := 2) (j := 1) (n := 4) (by omega) (S.c0_cube_mem j) ha
  have h1 : tc (tc (T.x₁ i₀) (T.x₁ j) ^ 3) a = 1 := by rwa [S.h5, mem_bot] at hz
  rwa [tc_pow_left_L1 S.h5 hc1 a 3] at h1

/-- (F2): a triple commutator beginning with `c_{i₀j}` is killed by `3`. -/
theorem c0_triple_three (j : Fin T.s) (x y : G) :
    tc (tc (tc (T.x₁ i₀) (T.x₁ j)) x) y ^ 3 = 1 := by
  have hc1 : tc (T.x₁ i₀) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hd2 : tc (tc (T.x₁ i₀) (T.x₁ j)) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc1 (mem_lcs_zero x)
  have hz : tc (tc (tc (T.x₁ i₀) (T.x₁ j) ^ 3) x) y ∈
      (⊤ : Subgroup G).lowerCentralSeries 4 := by
    have h3 : tc (tc (T.x₁ i₀) (T.x₁ j) ^ 3) x ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) (S.c0_cube_mem j) (mem_lcs_zero x)
    exact tc_mem (i := 3) (j := 0) (n := 4) (by omega) h3 (mem_lcs_zero y)
  have h1 : tc (tc (tc (T.x₁ i₀) (T.x₁ j) ^ 3) x) y = 1 := by rwa [S.h5, mem_bot] at hz
  rw [tc_pow_left_L1 S.h5 hc1 x 3, tc_pow_left_L1 S.h5 (lcs_mem_of_le (by norm_num) hd2) y 3] at h1
  exact h1


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

/-- A coefficient divisible by `3` kills a value of order dividing `3`. -/
theorem smul_of_three_dvd {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    {w : ℤ} (hw : (3 : ℤ) ∣ w) (hp : z ^ 3 = 1) : w • A z = 0 := by
  obtain ⟨q, rfl⟩ := hw
  have h3 := S.smul_of_pow_eq_one hA hz hp
  norm_num at h3
  rw [show (3 : ℤ) * q = q * 3 by ring, ← smul_smul, h3, smul_zero]

/-- A coefficient divisible by `3` kills a value already known to be `3`-torsion. -/
theorem smul_of_three_dvd_of_three_smul_zero {z : G} {w : ℤ} (hw : (3 : ℤ) ∣ w)
    (h3 : (3 : ℤ) • A z = 0) : w • A z = 0 := by
  obtain ⟨q, rfl⟩ := hw
  rw [show (3 : ℤ) * q = q * 3 by ring, ← smul_smul, h3, smul_zero]

/-- A multiple of `n` kills a value whose group element has order dividing `n`. -/
theorem smul_of_nat_dvd_of_pow_eq_one {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    {n : ℕ} {w : ℤ} (hw : (n : ℤ) ∣ w) (hp : z ^ n = 1) : w • A z = 0 := by
  obtain ⟨q, rfl⟩ := hw
  have h := S.smul_of_pow_eq_one hA hz hp
  have h' : ((n : ℤ) * q) • A z = q • ((n : ℤ) • A z) := by rw [smul_smul, mul_comm]
  rw [h', h, smul_zero]

/-- `ω(c̄_{i₁ i₂}, ·)` is `3`-torsion on `γ₂`. -/
theorem omega_three (a : G) (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    (3 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) a) = 0 := by
  classical
  let c : G := tc (T.x₁ i₁) (T.x₁ i₂)
  let z : G := c⁻¹
  let X : Fin T.s → G := fun i => (T.x₁ i)⁻¹
  let F0 : G → N := fun b => (3 : ℤ) • A b
  have hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := inv_mem hc
  have hF : ∀ u ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      ∀ v ∈ (⊤ : Subgroup G).lowerCentralSeries 3, F0 (u * v) = F0 u + F0 v := by
    intro u hu v hv
    simp only [F0]
    rw [hA u (lcs_mem_of_le (by norm_num) hu) v (lcs_mem_of_le (by norm_num) hv), smul_add]
  have hconvert (i j : Fin T.s) : F0 ⁅z, ⁅X i, X j⁆⁆ =
      (3 : ℤ) • A (tc c (tc (T.x₁ j) (T.x₁ i))) := by
    simp only [F0, z, X]
    congr 2
    rw [tc_eq c (tc (T.x₁ j) (T.x₁ i)), tc_inv (T.x₁ j) (T.x₁ i),
      tc_eq (T.x₁ i) (T.x₁ j)]
  have hpow_forward (j : Fin T.s) : tc c (tc (T.x₁ i₀) (T.x₁ j)) ^ 3 = 1 := by
    have hp := S.c0_pow_three j hc
    rw [← tc_inv, inv_pow, hp, inv_one]
  have hpow_reverse (j : Fin T.s) : tc c (tc (T.x₁ j) (T.x₁ i₀)) ^ 3 = 1 := by
    have hcj : tc (T.x₁ i₀) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have hrev : tc (T.x₁ j) (T.x₁ i₀) = (tc (T.x₁ i₀) (T.x₁ j))⁻¹ := (tc_inv _ _).symm
    rw [hrev, S.tc_inv_right_L1 hc hcj, inv_pow, hpow_forward, inv_one]
  have hmem (i j : Fin T.s) : tc c (tc (T.x₁ i) (T.x₁ j)) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    lcs_mem_of_le (by norm_num)
      (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc
        (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)))
  have hleft (j : Fin T.s) : F0 ⁅z, ⁅X i₀, X j⁆⁆ = 0 := by
    rw [hconvert]
    have h := S.smul_of_pow_eq_one hA (hmem j i₀) (hpow_reverse j)
    norm_num at h
    exact h
  have hright (i : Fin T.s) : F0 ⁅z, ⁅X i, X i₀⁆⁆ = 0 := by
    rw [hconvert]
    have h := S.smul_of_pow_eq_one hA (hmem i₀ i) (hpow_forward i)
    norm_num at h
    exact h
  have hself (i : Fin T.s) : F0 ⁅z, ⁅X i, X i⁆⁆ = 0 := by
    rw [commutatorElement_self, commutatorElement_one_right, ClassFour.F_one F0 hF]
  have hbase (i j : Fin T.s) : F0 ⁅z, ⁅X i, X j⁆⁆ = 0 := by
    rcases S.hall i with hi | hi | hi
    · subst i
      exact hleft j
    · subst i
      rcases S.hall j with hj | hj | hj
      · subst j
        exact hright i₁
      · subst j
        exact hself i₁
      · subst j
        rw [hconvert]
        have hrev : tc (T.x₁ i₂) (T.x₁ i₁) = c⁻¹ := (tc_inv _ _).symm
        have hone : tc c c⁻¹ = 1 := by simp [tc]
        rw [hrev, hone, addMapG_one hA, smul_zero]
    · subst i
      rcases S.hall j with hj | hj | hj
      · subst j
        exact hright i₂
      · subst j
        rw [hconvert]
        change (3 : ℤ) • A (tc c c) = 0
        have hone : tc c c = 1 := by simp [tc]
        rw [hone, addMapG_one hA, smul_zero]
      · subst j
        exact hself i₂
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
      simpa only [] using (GenericMaps.addMap_oprod_expandM
        (K := (⊤ : Subgroup G)) (N := (⊤ : Subgroup G).lowerCentralSeries 1)
        (F := fun u => F0 ⁅z, ⁅u, h⁆⁆) (x := X) (a := fun i => -α i) (v := g)
        (hNK := le_top)
        (hF := GenericMaps.nested_left S.h5 F0 hF hz (h := h))
        (hF0 := fun u hu => hzero u h hu) (hx := fun i => mem_lcs_zero (X i)) (hv := hα'))
    have eh (i : Fin T.s) : F0 ⁅z, ⁅X i, h⁆⁆ = ∑ j, (-β j) • F0 ⁅z, ⁅X i, X j⁆⁆ := by
      simpa only [] using (GenericMaps.addMap_oprod_expandM
        (K := (⊤ : Subgroup G)) (N := (⊤ : Subgroup G).lowerCentralSeries 1)
        (F := fun u => F0 ⁅z, ⁅X i, u⁆⁆) (x := X) (a := fun j => -β j) (v := h)
        (hNK := le_top)
        (hF := GenericMaps.nested_right S.h5 F0 hF hz (h := X i))
        (hF0 := fun u hu => hzeroR (X i) u hu) (hx := fun j => mem_lcs_zero (X j)) (hv := hβ'))
    rw [eg]
    simp_rw [eh]
    simp only [S.sum_three, hbase, smul_zero, add_zero, zero_add]
  rw [tc_eq]
  change F0 ⁅z, a⁻¹⁆ = 0
  exact ClassFour.addMap_vanish
    (N := (⊤ : Subgroup G).lowerCentralSeries 1) (H := ⊤) (K := ⊤)
    (A := fun u => F0 ⁅z, u⁆)
    (hle := le_rfl) (hA := ClassFour.addRight1 S.h5 F0 hF hz) (hgen := hgen)
    (a := a⁻¹) (inv_mem ha)

/-- The reverse orientation of `omega_three`. -/
theorem omega_three_rev (a : G) (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    (3 : ℤ) • A (tc a (tc (T.x₁ i₁) (T.x₁ i₂))) = 0 := by
  have hz : tc (tc (T.x₁ i₁) (T.x₁ i₂)) a ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (n := 3) (by omega)
      (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)) ha
  rw [← tc_inv, addMapG_inv hA (lcs_mem_of_le (by norm_num) hz), smul_neg,
    S.omega_three hA a ha, neg_zero]

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

/-- Pairing `c_{i₀j}` with `Y_j` vanishes with its Tahara coefficient, using (c2) when `j`
is active and the adapted decomposition when it is inactive. -/
theorem c0_Y_smul_zero {j : Fin T.s} (hij : i₀ < j) :
    τ.u i₀ j • A (tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ j ^ T.d j)) = 0 := by
  have hc : tc (T.x₁ i₀) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hz : tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ j ^ T.d j) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc (S.Y1 j))
  by_cases hact : act j
  · have hu : (3 : ℤ) ∣ τ.u i₀ j := by
      have h := S.crow_act hτ i₀ hact
      simpa [crow, hij, not_lt.mpr hij.le] using h
    exact S.smul_of_three_dvd hA hz hu (S.c0_pow_three j (S.Y1 j))
  · obtain ⟨a, ha, c, hc3, hY⟩ := S.hK j hact
    have hzero : tc (tc (T.x₁ i₀) (T.x₁ j)) c = 1 := by
      rw [← tc_inv, tc_L2_L1 S.h5 hc3 hc, inv_one]
    have hmap : tc (tc (T.x₁ i₀) (T.x₁ j)) (T.x₁ j ^ T.d j) =
        tc (tc (T.x₁ i₀) (T.x₁ j)) a ^ 3 := by
      rw [hY, S.tc_mul_right_L1 hc (pow_mem ha 3), tc_pow_right_L1 S.h5 hc ha, hzero, mul_one]
    rw [hmap, addMapG_pow hA (lcs_mem_of_le (by norm_num)
      (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc ha))]
    norm_num
    have h := S.smul_of_pow_eq_one hA (lcs_mem_of_le (by norm_num)
      (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc ha)) (S.c0_pow_three j ha)
    norm_num at h
    rw [h, smul_zero]

/-- The degree-nine defect, with coefficients `4` and `-60`. -/
theorem delta_reduced (x y : G) :
    A (tc (x ^ 9) y * tc (y ^ 9) x) =
      (4 : ℤ) • (A (tc (tc x y) (x ^ 9)) - A (tc (tc x y) (y ^ 9))) -
        (60 : ℤ) • (A (tc (tc (tc x y) x) x) - A (tc (tc (tc x y) y) y)) := by
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
  have hx2 : tc (tc x y) x ^ 36 * tc (tc (tc x y) x) x ^ 84 ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (pow_mem hfx 36) (lcs_mem_of_le (by norm_num) (pow_mem hgx 84))
  have hfy' : tc (tc y x) y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (n := 2) (by omega)
      (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _))
      (mem_lcs_zero _)
  have hgy' : tc (tc (tc y x) y) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (n := 3) (by omega) hfy' (mem_lcs_zero _)
  have hy2 : tc (tc y x) y ^ 36 * tc (tc (tc y x) y) y ^ 84 ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (pow_mem hfy' 36) (lcs_mem_of_le (by norm_num) (pow_mem hgy' 84))
  have hcomm : Commute (tc (tc x y) x ^ 36 * tc (tc (tc x y) x) x ^ 84) ((tc x y)⁻¹ ^ 9) :=
    commutatorElement_eq_one_iff_mul_comm.mp
      (comm_eq_one S.h5 (by norm_num) hx2 (pow_mem (inv_mem hc) 9))
  have hinv : tc y x = (tc x y)⁻¹ := (tc_inv x y).symm
  have hprod : tc (x ^ 9) y * tc (y ^ 9) x =
      tc (tc x y) x ^ 36 * tc (tc (tc x y) x) x ^ 84 *
        (tc (tc y x) y ^ 36 * tc (tc (tc y x) y) y ^ 84) := by
    rw [tc_pow_formula S.h5 x y 9, tc_pow_formula S.h5 y x 9]
    norm_num [Nat.choose]
    rw [hinv]
    exact key _ _ _ _ _ _ hcomm
  have hFy : A (tc (tc y x) y) = -A (tc (tc x y) y) := by
    rw [hinv, S.tc_inv_left_L1 hc, addMapG_inv hA hfy]
  have hGy : A (tc (tc (tc y x) y) y) = -A (tc (tc (tc x y) y) y) := by
    rw [hinv, S.tc_inv_left_L1 hc, S.tc_inv_left_L1 (lcs_mem_of_le (by norm_num) hfy),
      addMapG_inv hA (lcs_mem_of_le (by norm_num) hgy)]
  have hninety : A (tc (x ^ 9) y * tc (y ^ 9) x) =
      (36 : ℤ) • (A (tc (tc x y) x) - A (tc (tc x y) y)) +
        (84 : ℤ) • (A (tc (tc (tc x y) x) x) - A (tc (tc (tc x y) y) y)) := by
    rw [hprod, hA _ hx2 _ hy2,
      hA _ (pow_mem hfx 36) _ (lcs_mem_of_le (by norm_num) (pow_mem hgx 84)),
      hA _ (pow_mem hfy' 36) _ (lcs_mem_of_le (by norm_num) (pow_mem hgy' 84)),
      addMapG_pow hA hfx, addMapG_pow hA hfy',
      addMapG_pow hA (lcs_mem_of_le (by norm_num) hgx),
      addMapG_pow hA (lcs_mem_of_le (by norm_num) hgy'), hFy, hGy]
    norm_num
    module
  have k36 (z : G) : (36 : ℤ) • A (tc (tc x y) z) =
      (4 : ℤ) • A (tc (tc x y) (z ^ 9)) -
        (144 : ℤ) • A (tc (tc (tc x y) z) z) := by
    have hfz : tc (tc x y) z ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have hgz : tc (tc (tc x y) z) z ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) hfz (mem_lcs_zero _)
    have e := congrArg A (Star.tc_pow_right_K3 hc S.h5 z 9)
    norm_num [Nat.choose] at e
    rw [hA _ (pow_mem hfz 9) _ (lcs_mem_of_le (by norm_num) (pow_mem hgz 36)),
      addMapG_pow hA hfz, addMapG_pow hA (lcs_mem_of_le (by norm_num) hgz)] at e
    norm_num at e
    calc (36 : ℤ) • A (tc (tc x y) z)
        = (4 : ℤ) • ((9 : ℤ) • A (tc (tc x y) z)) := by rw [smul_smul]; norm_num
      _ = (4 : ℤ) • (A (tc (tc x y) (z ^ 9)) -
            (36 : ℤ) • A (tc (tc (tc x y) z) z)) := by rw [e]; abel
      _ = _ := by rw [smul_sub, smul_smul]; norm_num
  rw [hninety, smul_sub, k36 x, k36 y, smul_sub]
  module

theorem T1_eq : Star.T1 T τ A = 0 := by
  classical
  have h02 : i₀ < i₂ := S.h01.trans S.h12
  unfold Star.T1
  simp only [S.sum_three, S.h01, S.h12, h02, lt_irrefl, not_lt.mpr S.h01.le,
    not_lt.mpr S.h12.le, not_lt.mpr h02.le, false_and, true_and, and_false, and_true,
    ↓reduceIte, zero_smul, add_zero, zero_add, neg_zero]
  have hzero0 (h : Fin T.s) (hh : i₀ < h) (dh : T.d h = 9) :
      τ.u i₀ h • A (tc (T.x₁ i₀ ^ T.d h) (T.x₁ h) * tc (T.x₁ h ^ T.d h) (T.x₁ i₀)) = 0 := by
    rw [dh, S.delta_reduced hA hτ]
    have hc : tc (T.x₁ i₀) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have hx9 : T.x₁ i₀ ^ 9 = (T.x₁ i₀ ^ T.d i₀) ^ 3 := by rw [S.hd₀, ← pow_mul]
    have htriX : tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have htriH : tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have htriY : tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀ ^ T.d i₀) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      lcs_mem_of_le (by norm_num)
        (tc_mem (i := 1) (j := 1) (n := 3) (by omega) hc (S.Y1 i₀))
    have hBx : A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀ ^ 9)) = 0 := by
      rw [hx9, tc_pow_right_L1 S.h5 hc (S.Y1 i₀), addMapG_pow hA htriY]
      norm_num
      exact S.smul_of_pow_eq_one hA htriY (S.c0_pow_three h (S.Y1 i₀))
    have hB : τ.u i₀ h • A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ 9)) = 0 := by
      rw [← dh]
      exact S.c0_Y_smul_zero hA hτ hh
    have hfirst : τ.u i₀ h • ((4 : ℤ) •
        (A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀ ^ 9)) -
          A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ 9)))) = 0 := by
      rw [hBx, zero_sub]
      have heq : τ.u i₀ h • ((4 : ℤ) •
          (-A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ 9)))) =
          -(4 : ℤ) • (τ.u i₀ h • A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ 9))) := by
        module
      rw [heq, hB, smul_zero]
    have hsecond : τ.u i₀ h • ((60 : ℤ) •
        (A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀)) (T.x₁ i₀)) -
          A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h)))) = 0 := by
      simp only [smul_sub]
      have hX : τ.u i₀ h • ((60 : ℤ) •
          A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀)) (T.x₁ i₀))) = 0 := by
        have h3 := S.smul_of_pow_eq_one hA (lcs_mem_of_le (by norm_num)
          (tc_mem (i := 2) (j := 0) (n := 3) (by omega) htriX (mem_lcs_zero _)))
          (S.c0_triple_three h (T.x₁ i₀) (T.x₁ i₀))
        norm_num at h3
        have heq : τ.u i₀ h • ((60 : ℤ) •
            A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀)) (T.x₁ i₀))) =
            (20 * τ.u i₀ h) • ((3 : ℤ) •
              A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀)) (T.x₁ i₀))) := by module
        rw [heq, h3, smul_zero]
      have hH : τ.u i₀ h • ((60 : ℤ) •
          A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h))) = 0 := by
        have h3 := S.smul_of_pow_eq_one hA (lcs_mem_of_le (by norm_num)
          (tc_mem (i := 2) (j := 0) (n := 3) (by omega) htriH (mem_lcs_zero _)))
          (S.c0_triple_three h (T.x₁ h) (T.x₁ h))
        norm_num at h3
        have heq : τ.u i₀ h • ((60 : ℤ) •
            A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h))) =
            (20 * τ.u i₀ h) • ((3 : ℤ) •
              A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h))) := by module
        rw [heq, h3, smul_zero]
      rw [hX, hH, sub_self]
    calc
      _ = τ.u i₀ h • ((4 : ℤ) •
            (A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀ ^ 9)) -
              A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ 9)))) -
          τ.u i₀ h • ((60 : ℤ) •
            (A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ i₀)) (T.x₁ i₀)) -
              A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h)))) :=
        smul_sub _ _ _
      _ = 0 := by rw [hfirst, hsecond, sub_self]
  have hlast : τ.u i₁ i₂ • A (tc (T.x₁ i₁ ^ T.d i₂) (T.x₁ i₂) *
      tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁)) = 0 := by
    rw [S.hd₂, S.delta_reduced hA hτ]
    obtain ⟨U, hU⟩ := S.u3_eq hτ S.h12 (S.hd₁.trans S.hd₂.symm)
    rw [hU]
    have hc : tc (T.x₁ i₁) (T.x₁ i₂) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have htri (j : Fin T.s) : tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ j) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have hfirst : (3 * U) • ((4 : ℤ) •
        (A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁ ^ 9)) -
          A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ 9)))) = 0 := by
      simp only [smul_sub]
      have h1 : (3 * U) • ((4 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁ ^ 9))) = 0 := by
        have heq : (3 * U) • ((4 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁ ^ 9))) =
            (4 * U) • ((3 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁ ^ 9))) := by module
        rw [heq, S.omega_three hA _ (by rw [← S.hd₁]; exact S.Y1 i₁), smul_zero]
      have h2 : (3 * U) • ((4 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ 9))) = 0 := by
        have heq : (3 * U) • ((4 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ 9))) =
            (4 * U) • ((3 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ 9))) := by module
        rw [heq, S.omega_three hA _ (by rw [← S.hd₂]; exact S.Y1 i₂), smul_zero]
      rw [h1, h2, sub_self]
    have hsecond : (3 * U) • ((60 : ℤ) •
        (A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁)) (T.x₁ i₁)) -
          A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂)))) = 0 := by
      simp only [smul_sub]
      have hX : (3 * U) • ((60 : ℤ) •
          A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁)) (T.x₁ i₁))) = 0 := by
        have hpow : tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁)) (T.x₁ i₁) ^ 9 = 1 :=
          S.triple_pow_mid hc (T.x₁ i₁) (by rw [← S.hd₁]; exact S.Y1 i₁)
        have h9 := S.smul_of_pow_eq_one hA (lcs_mem_of_le (by norm_num)
          (tc_mem (i := 2) (j := 0) (n := 3) (by omega) (htri i₁) (mem_lcs_zero _))) hpow
        norm_num at h9
        have heq : (3 * U) • ((60 : ℤ) •
            A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁)) (T.x₁ i₁))) =
            (20 * U) • ((9 : ℤ) •
              A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁)) (T.x₁ i₁))) := by module
        rw [heq, h9, smul_zero]
      have hY : (3 * U) • ((60 : ℤ) •
          A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂))) = 0 := by
        have hpow : tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂) ^ 9 = 1 :=
          S.triple_pow_mid hc (T.x₁ i₂) (by rw [← S.hd₂]; exact S.Y1 i₂)
        have h9 := S.smul_of_pow_eq_one hA (lcs_mem_of_le (by norm_num)
          (tc_mem (i := 2) (j := 0) (n := 3) (by omega) (htri i₂) (mem_lcs_zero _))) hpow
        norm_num at h9
        have heq : (3 * U) • ((60 : ℤ) •
            A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂))) =
            (20 * U) • ((9 : ℤ) •
              A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂))) := by module
        rw [heq, h9, smul_zero]
      rw [hX, hY, sub_self]
    calc
      _ = (3 * U) • ((4 : ℤ) •
            (A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁ ^ 9)) -
              A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ 9)))) -
          (3 * U) • ((60 : ℤ) •
            (A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₁)) (T.x₁ i₁)) -
              A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂)))) :=
        smul_sub _ _ _
      _ = 0 := by rw [hfirst, hsecond, sub_self]
  simp only [hzero0 i₁ S.h01 S.hd₁, hzero0 i₂ h02 S.hd₂, hlast, add_zero, zero_add]

theorem T2_eq : Star.T2 T τ A = 0 := by
  classical
  have h02 : i₀ < i₂ := S.h01.trans S.h12
  unfold Star.T2
  simp only [S.sum_three, S.h01, S.h12, h02, lt_irrefl, not_lt.mpr S.h01.le,
    not_lt.mpr S.h12.le, not_lt.mpr h02.le, false_and, true_and, and_false, and_true,
    ↓reduceIte, zero_smul, add_zero, zero_add, neg_zero]
  rw [neg_eq_zero]
  have hzero0 (h : Fin T.s) (hh : i₀ < h) (dh : T.d h = 9) :
      (τ.u i₀ h * T.q i₀ h) • A (tc (tc (T.x₁ i₀ ^ T.d i₀) (T.x₁ h)) (T.x₁ h)) = 0 := by
    have hc : tc (T.x₁ i₀) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have htri : tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have htriple : tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h) ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) htri (mem_lcs_zero _)
    have hq : T.q i₀ h = 3 := by
      simp only [Data.q, S.hd₀, dh]
      norm_num
    rw [hq, S.F4 i₀ h h, S.hd₀]
    have hnine : (9 : ℤ) • A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) =
        A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ 9)) -
          (36 : ℤ) • A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h)) := by
      have e := congrArg A (Star.tc_pow_right_K3 hc S.h5 (T.x₁ h) 9)
      norm_num [Nat.choose] at e
      rw [hA _ (pow_mem htri 9) _ (lcs_mem_of_le (by norm_num) (pow_mem htriple 36)),
        addMapG_pow hA htri, addMapG_pow hA (lcs_mem_of_le (by norm_num) htriple)] at e
      norm_num at e ⊢
      rw [e]
      abel
    have hbase : (τ.u i₀ h * 3) • A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h) ^ 3) =
        τ.u i₀ h • (A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h ^ T.d h)) -
          (36 : ℤ) • A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h))) := by
      rw [dh]
      calc (τ.u i₀ h * 3) • A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h) ^ 3)
          = τ.u i₀ h • ((9 : ℤ) • A (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h))) := by
            rw [addMapG_pow hA htri, smul_smul]
            norm_num only [Nat.cast_ofNat]
            module
        _ = _ := by rw [hnine]
    rw [hbase, smul_sub, S.c0_Y_smul_zero hA hτ hh]
    have h36 : (36 : ℤ) • A (tc (tc (tc (T.x₁ i₀) (T.x₁ h)) (T.x₁ h)) (T.x₁ h)) = 0 :=
      S.smul_of_three_dvd hA (lcs_mem_of_le (by norm_num) htriple) (by norm_num)
        (S.c0_triple_three h (T.x₁ h) (T.x₁ h))
    rw [h36, smul_zero, sub_zero]
  have hlast : (τ.u i₁ i₂ * T.q i₁ i₂) • A (tc (tc (T.x₁ i₁ ^ T.d i₁) (T.x₁ i₂)) (T.x₁ i₂)) = 0 := by
    have hq : T.q i₁ i₂ = 1 := by
      simp only [Data.q, S.hd₁, S.hd₂]
      norm_num
    rw [S.F4 i₁ i₂ i₂, hq, mul_one, S.hd₁]
    obtain ⟨U, hU⟩ := S.u3_eq hτ S.h12 (S.hd₁.trans S.hd₂.symm)
    rw [hU]
    have hc : tc (T.x₁ i₁) (T.x₁ i₂) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have htri : tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂) ∈
        (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) hc (mem_lcs_zero _)
    have htriple : tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂) ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) htri (mem_lcs_zero _)
    have hnine : (9 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) =
        A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ 9)) -
          (36 : ℤ) • A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂)) := by
      have e := congrArg A (Star.tc_pow_right_K3 hc S.h5 (T.x₁ i₂) 9)
      norm_num [Nat.choose] at e
      rw [hA _ (pow_mem htri 9) _ (lcs_mem_of_le (by norm_num) (pow_mem htriple 36)),
        addMapG_pow hA htri, addMapG_pow hA (lcs_mem_of_le (by norm_num) htriple)] at e
      norm_num at e ⊢
      rw [e]
      abel
    have hbase : (3 * U) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂) ^ 9) =
        (3 * U) • (A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ T.d i₂)) -
          (36 : ℤ) • A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂))) := by
      rw [S.hd₂]
      calc (3 * U) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂) ^ 9)
          = (3 * U) • ((9 : ℤ) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂))) := by
            rw [addMapG_pow hA htri]
            norm_num
        _ = _ := by rw [hnine]
    rw [hbase, smul_sub]
    have hfirst : (3 * U) • A (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂ ^ T.d i₂)) = 0 :=
      S.smul_of_three_dvd_of_three_smul_zero hA ⟨U, rfl⟩ (S.omega_three hA _ (S.Y1 i₂))
    have hsecond : (3 * U) • ((36 : ℤ) •
        A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂))) = 0 := by
      refine (smul_smul (3 * U) (36 : ℤ)
        (A (tc (tc (tc (T.x₁ i₁) (T.x₁ i₂)) (T.x₁ i₂)) (T.x₁ i₂)))).trans ?_
      exact S.smul_of_nat_dvd_of_pow_eq_one hA (lcs_mem_of_le (by norm_num) htriple)
        (n := 9) (by exact (show (9 : ℤ) ∣ 36 by norm_num).mul_left (3 * U))
        (S.triple_pow_mid hc (T.x₁ i₂) (by rw [← S.hd₂]; exact S.Y1 i₂))
    rw [hfirst, hsecond, sub_zero]
  simp only [hzero0 i₁ S.h01 S.hd₁, hzero0 i₂ h02 S.hd₂, hlast, add_zero, zero_add]

theorem T3_eq : Star.T3 T τ A = 0 := by
  classical
  have h02 : i₀ < i₂ := S.h01.trans S.h12
  unfold Star.T3
  simp only [S.sum_three, S.h01, S.h12, h02, le_refl, S.h01.le, S.h12.le, h02.le,
    lt_irrefl, not_lt.mpr S.h01.le, not_lt.mpr S.h12.le, not_lt.mpr h02.le,
    not_le.mpr S.h01, not_le.mpr S.h12, not_le.mpr h02, false_and, true_and, and_false,
    and_true, ↓reduceIte, zero_smul, add_zero, zero_add, neg_zero]
  rw [neg_eq_zero]
  have hx0 : T.x₁ i₀ ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [← S.hd₀]
    exact S.Y1 i₀
  have hmid (g h : Fin T.s) (hig : i₀ < g) (hgh : g ≤ h) :
      τ.w' i₀ g h • A (tc (tc (T.x₁ g ^ T.d g) (T.x₁ i₀)) (T.x₁ h)) = 0 := by
    have hi2 : tc (T.x₁ g ^ T.d g) (T.x₁ i₀) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (n := 2) (by omega) (S.Y1 g) (mem_lcs_zero _)
    have hz3 : tc (tc (T.x₁ g ^ T.d g) (T.x₁ i₀)) (T.x₁ h) ∈
        (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (i := 2) (j := 0) (n := 3) (by omega) hi2 (mem_lcs_zero _)
    have hp : tc (tc (T.x₁ g ^ T.d g) (T.x₁ i₀)) (T.x₁ h) ^ 3 = 1 :=
      S.triple_pow_mid (S.Y1 g) (T.x₁ h) hx0
    by_cases ha : act g
    · exact S.smul_of_three_dvd hA (lcs_mem_of_le (by norm_num) hz3)
        (S.w'3 hτ ha hig hgh) hp
    · obtain ⟨a, ha1, c, hc, hY⟩ := S.hK g ha
      have hinner : tc a (T.x₁ i₀) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
        tc_mem (i := 1) (j := 0) (n := 2) (by omega) ha1 (mem_lcs_zero _)
      have hsecond : tc c (T.x₁ i₀) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (i := 2) (j := 0) (n := 3) (by omega) hc (mem_lcs_zero _)
      have hpa : tc (tc a (T.x₁ i₀)) (T.x₁ h) ^ 3 = 1 :=
        S.triple_pow_mid ha1 (T.x₁ h) hx0
      have hz : tc (tc (T.x₁ g ^ T.d g) (T.x₁ i₀)) (T.x₁ h) = 1 := by
        rw [hY, tc_mul_left_L1 S.h5 (pow_mem ha1 3) (lcs_mem_of_le (by norm_num) hc),
          tc_pow_left_L1 S.h5 ha1,
          tc_mul_left_L1 S.h5 (lcs_mem_of_le (by norm_num) (pow_mem hinner 3))
            (lcs_mem_of_le (by norm_num) hsecond),
          tc_pow_left_L1 S.h5 (lcs_mem_of_le (by norm_num) hinner),
          tc_L3 S.h5 hsecond, mul_one, hpa]
      rw [hz, addMapG_one hA, smul_zero]
  have hlast : τ.w' i₁ i₂ i₂ •
      A (tc (tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁)) (T.x₁ i₂)) = 0 := by
    have hF : ∀ u ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
        ∀ v ∈ (⊤ : Subgroup G).lowerCentralSeries 3, A (u * v) = A u + A v := by
      intro u hu v hv
      exact hA u (lcs_mem_of_le (by norm_num) hu) v (lcs_mem_of_le (by norm_num) hv)
    have hYself : tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₂) = 1 :=
      tc_eq_one_iff.mpr (Commute.pow_left (Commute.refl _) _)
    have hU : A ⁅⁅(T.x₁ i₂)⁻¹, (T.x₁ i₁)⁻¹⁆, (T.x₁ i₂ ^ T.d i₂)⁻¹⁆ =
        -A (tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₁) (T.x₁ i₂))) := by
      calc A ⁅⁅(T.x₁ i₂)⁻¹, (T.x₁ i₁)⁻¹⁆, (T.x₁ i₂ ^ T.d i₂)⁻¹⁆ =
          A ⁅tc (T.x₁ i₂) (T.x₁ i₁), (T.x₁ i₂ ^ T.d i₂)⁻¹⁆ := by rw [tc_eq]
        _ = -A ⁅(T.x₁ i₂ ^ T.d i₂)⁻¹, tc (T.x₁ i₂) (T.x₁ i₁)⁆ :=
          GenericMaps.B_swap S.h5 A hF
            (commutator_mem_lcs (i := 1) (j := 1) (n := 3) (by omega)
              (tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _))
              (inv_mem (S.Y1 i₂)))
        _ = -A (tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₁) (T.x₁ i₂))) := by
            rw [tc_eq (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₁) (T.x₁ i₂)),
              tc_inv (T.x₁ i₁) (T.x₁ i₂), tc_eq (T.x₁ i₂) (T.x₁ i₁)]
    have hV : A ⁅⁅(T.x₁ i₂ ^ T.d i₂)⁻¹, (T.x₁ i₂)⁻¹⁆, (T.x₁ i₁)⁻¹⁆ = 0 := by
      rw [← tc_eq (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₂), hYself, commutatorElement_one_left,
        addMapG_one hF]
    have hW : A ⁅⁅(T.x₁ i₁)⁻¹, (T.x₁ i₂ ^ T.d i₂)⁻¹⁆, (T.x₁ i₂)⁻¹⁆ =
        A (tc (tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁)) (T.x₁ i₂)) := by
      calc A ⁅⁅(T.x₁ i₁)⁻¹, (T.x₁ i₂ ^ T.d i₂)⁻¹⁆, (T.x₁ i₂)⁻¹⁆ =
          A ⁅(tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁))⁻¹, (T.x₁ i₂)⁻¹⁆ := by
            rw [tc_inv (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁), tc_eq (T.x₁ i₁) (T.x₁ i₂ ^ T.d i₂)]
        _ = A (tc (tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁)) (T.x₁ i₂)) := by
          rw [tc_eq (tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁)) (T.x₁ i₂)]
    have hJ := ClassFour.jacobi4 S.h5 A hF (T.x₁ i₂)⁻¹ (T.x₁ i₁)⁻¹
      (z := (T.x₁ i₂ ^ T.d i₂)⁻¹) (inv_mem (S.Y1 i₂))
    rw [hU, hV, hW, add_zero] at hJ
    have hAB : A (tc (tc (T.x₁ i₂ ^ T.d i₂) (T.x₁ i₁)) (T.x₁ i₂)) =
        A (tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₁) (T.x₁ i₂))) := by
      apply eq_of_sub_eq_zero
      rw [sub_eq_add_neg, add_comm]
      exact hJ
    rw [hAB]
    by_cases ha : act i₂
    · exact S.smul_of_three_dvd_of_three_smul_zero hA (S.w'3 hτ ha S.h12 le_rfl)
        (S.omega_three_rev hA _ (S.Y1 i₂))
    · obtain ⟨a, ha1, c, hc, hY⟩ := S.hK i₂ ha
      have hc12 : tc (T.x₁ i₁) (T.x₁ i₂) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
        tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
      have hzero : A (tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₁) (T.x₁ i₂))) = 0 := by
        rw [hY, tc_mul_left_L1 S.h5 (pow_mem ha1 3) (lcs_mem_of_le (by norm_num) hc),
          tc_pow_left_L1 S.h5 ha1, tc_L2_L1 S.h5 hc hc12, mul_one,
          addMapG_pow hA (lcs_mem_of_le (by norm_num)
            (tc_mem (i := 1) (j := 1) (n := 3) (by omega) ha1 hc12))]
        norm_num
        exact S.omega_three_rev hA a ha1
      rw [hzero, smul_zero]
  simp only [hmid i₁ i₁ S.h01 le_rfl, hmid i₁ i₂ S.h01 S.h12.le,
    hmid i₂ i₂ h02 le_rfl, hlast, add_zero, zero_add]

theorem T4_eq : Star.T4 T τ A = 0 := by
  classical
  have h02 : i₀ < i₂ := S.h01.trans S.h12
  unfold Star.T4
  simp only [S.sum_three, S.h01, S.h12, h02, lt_irrefl, not_lt.mpr S.h01.le,
    not_lt.mpr S.h12.le, not_lt.mpr h02.le, false_and, true_and, and_false, and_true,
    ↓reduceIte, zero_smul, add_zero, zero_add, neg_zero]
  rw [neg_eq_zero]
  have hc01 : tc (T.x₁ i₀) (T.x₁ i₁) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (n := 1) (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
  have hz3 : tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₀) (T.x₁ i₁)) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 1) (j := 1) (n := 3) (by omega) (S.Y1 i₂) hc01
  have hp : tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₀) (T.x₁ i₁)) ^ 3 = 1 := by
    have h := S.c0_pow_three i₁ (S.Y1 i₂)
    rw [← tc_inv, inv_pow, h, inv_one]
  by_cases ha : act i₂
  · exact S.smul_of_three_dvd hA (lcs_mem_of_le (by norm_num) hz3)
      (S.w''3 hτ ha S.h01 S.h12) hp
  · obtain ⟨a, ha1, c, hc, hY⟩ := S.hK i₂ ha
    have hpa : tc a (tc (T.x₁ i₀) (T.x₁ i₁)) ^ 3 = 1 := by
      have h := S.c0_pow_three i₁ ha1
      rw [← tc_inv, inv_pow, h, inv_one]
    have hz : tc (T.x₁ i₂ ^ T.d i₂) (tc (T.x₁ i₀) (T.x₁ i₁)) = 1 := by
      rw [hY, tc_mul_left_L1 S.h5 (pow_mem ha1 3) (lcs_mem_of_le (by norm_num) hc),
        tc_pow_left_L1 S.h5 ha1, tc_L2_L1 S.h5 hc hc01, mul_one, hpa]
    rw [hz, addMapG_one hA, smul_zero]

theorem T5_eq : Star.T5 T τ A = 0 := by
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
  have hpow := addMapG_pow hA (lcs_mem_of_le (by norm_num) ht3) (T.d i)
  rw [hp, addMapG_one hA] at hpow
  have hdA : (T.d i : ℤ) • A (tc (tc (T.x₂ k) (T.x₁ i)) (T.x₁ i)) = 0 := hpow.symm
  obtain ⟨q, hq⟩ := S.ch2_dvd_d i
  rw [hq]
  calc (τ.v i k * ((T.d i : ℤ) * q)) • A (tc (tc (T.x₂ k) (T.x₁ i)) (T.x₁ i))
      = (τ.v i k * q) • ((T.d i : ℤ) • A (tc (tc (T.x₂ k) (T.x₁ i)) (T.x₁ i))) := by
        rw [smul_smul]
        congr 1
        ring
    _ = 0 := by rw [hdA, smul_zero]

end Setup

/-- **Every generator of Tahara's Theorem 6.1 is trivial** in the situation `Setup`. -/
theorem Setup.gen_eq_one {T : Data G} {act : Fin T.s → Prop} {i₀ i₁ i₂ : Fin T.s}
    (S : Setup T act i₀ i₁ i₂) {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) : T.gen τ = 1 := by
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
  have hg2 : T.gen τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    rw [Data.gen]
    exact mul_mem (mul_mem hgA (h32 hgB)) (h32 hgC)
  let _ : CommGroup ↥((⊤ : Subgroup G).lowerCentralSeries 2) :=
    commGroupOfComm _ (fun a ha b hb => comm_L2 S.h5 ha hb)
  let A : G → Additive ↥((⊤ : Subgroup G).lowerCentralSeries 2) := fun g =>
    if hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2 then Additive.ofMul ⟨g, hg⟩ else 0
  have hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b := by
    intro a ha b hb
    simp only [A, ha, hb, mul_mem ha hb, ↓reduceDIte]
    rfl
  have h2 := Star.two_smul_gen_eq S.h5 S.valid hτ hA
  rw [S.T1_eq hA hτ, S.T2_eq hA hτ, S.T3_eq hA hτ, S.T4_eq hA hτ, S.T5_eq hA hτ] at h2
  simp only [add_zero] at h2
  have hsq : T.gen τ ^ 2 = 1 := by
    have e : A (T.gen τ ^ 2) = 0 := by
      rw [addMapG_pow hA hg2]
      exact_mod_cast h2
    simp only [A, pow_mem hg2 2, ↓reduceDIte] at e
    have e' := congrArg Additive.toMul e
    rw [toMul_ofMul, toMul_zero] at e'
    simpa using congrArg Subtype.val e'
  obtain ⟨m, hm⟩ := S.htor _ hg2
  have hcop : Nat.gcd 2 (3 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 2 3)
  have hord : orderOf (T.gen τ) = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hm)
    rw [hcop] at h
    exact Nat.dvd_one.mp h
  exact orderOf_eq_one_iff.mp hord


end Ab399

end GroupDimension
