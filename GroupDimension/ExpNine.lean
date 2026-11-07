module

public import GroupDimension.ExpThreeGen

@[expose] public section

/-!
# `D₅ = γ₅` when `γ₄³ ⊆ γ₅` and `γ₂⁹ ⊆ γ₄` (Theorem 6.10 of the lab notebook, MATH-444)

**Theorem 6.10** (`thm:exp3h9`; `D_five_eq_gamma_five_g4_cube_g2_nine`): if `G/γ₂(G)` is a finite
`3`-group, `γ₄(G)³ ⊆ γ₅(G)` and `γ₂(G)⁹ ⊆ γ₄(G)`, then `D₅(G) = γ₅(G)`. The finite form
(`D_five_eq_bot_of_class_four_g4_cube_g2_nine`): a finite group `Q` of class `≤ 4` with `Q/γ₂` a
`3`-group, `c³ = 1` for `c ∈ γ₄` and `a⁹ ∈ γ₄` for `a ∈ γ₂` has `D₅(Q) = 1`. It contains Theorem 6.9
(`γ₂/γ₃` of exponent dividing `3`), which is derived from it in `TaharaTheorem.lean`. The proof takes
Tahara's Theorem 6.1 (`TaharaFiveOne`) as an explicit hypothesis, discharged in
`TaharaTheorem.lean`.

The proof follows the wiki page of MATH-444 (§2–§5), with one simplification of the bookkeeping:

* the identities (I1)–(I7) in class `≤ 4` under the two hypotheses (`tc_pow_three_rightA`,
  `pow_nine_L2A`, `tc_pow_nineA`, `tc_pow_27A`, `tc_L1_pow_nineA`, `cube_mul_mod'`);
* a basis of `Ω₁(G/γ₂)` adapted to the height filtration and to the kernel `K` of the cube map
  `Ω₁(G/γ₂) → L₂/3L₂` (`exists_socle_family`, built on `exists_flag_ker_basis`), lifted to a
  uniqueness basis (`exists_layer_basis`); the uniqueness bases of `L₂` and `L₃` are arbitrary.
  An index `i` is *active* if `x_i^{d(i)} ∉ γ₂³γ₃`; for the active ones the coefficients of
  conditions (D) vanish modulo `3` (`SetupA.hind`), since the classes of the inactive cubes are
  zero and those of the active ones are independent modulo `3L₂`;
* the computation (`SetupA.gen_eq_one`). The `v`-part is evaluated through the skew-symmetry of
  `N = vᵀb` given by condition (F) modulo `3`, so that no adapted basis of `L₂` (the chain
  `ker P̄ ⊆ P̄⁻¹(W)` of the wiki page) is needed. Conditions (B) and (E) of a row `r` with
  `d(r) ∈ {3, 9}` are combined into one identity in the abelian group `γ₃`, paired with `x_r`
  (`SetupA.row`; this is the reformulation `(∗)` of the wiki page, the terms with `c_{hl}` cancel
  exactly); the rows of order `3` give step (4), the rows of order `9` step (5).
-/

namespace GroupDimension

namespace ExpThree

open Subgroup Tahara ClassFour
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Identities in class `≤ 4` -/

/-- `(xy)³ ≡ x³y³[y, x]³` modulo `γ₃` (Hall–Petrescu for `n = 3`). -/
theorem cube_mul_mod' (x y : G) :
    (x ^ 3 * y ^ 3 * tc y x ^ 3)⁻¹ * (x * y) ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  rw [← QuotientGroup.eq]
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries 2)
  have hc : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero y) (mem_lcs_zero x)
  have hba : π y * π x = π x * π y * π (tc y x) := by
    rw [← map_mul, ← map_mul, ← map_mul]; congr 1; simp only [tc]; group
  have hz : ∀ g, π (tc y x) * π g = π g * π (tc y x) := fun g =>
    (mk_commute (commutator_mem_lcs (i := 1) (j := 0) (by omega) hc (mem_lcs_zero g))).eq
  have hπ : ∀ g, π g = (g : G ⧸ (⊤ : Subgroup G).lowerCentralSeries 2) := fun _ => rfl
  have key := mul_pow_three_of_central hba (fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ((⊤ : Subgroup G).lowerCentralSeries 2) g
    exact hz g)
  simp only [hπ] at key
  exact key.symm

/-- `cl (a³) = 3 • cl a`. -/
theorem cl_pow3 {k : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    cl G k (a ^ 3) = (3 : ℤ) • cl G k a := by
  have := cl_zpow ha 3
  rwa [zpow_ofNat] at this

/-- The cube of a product in `γ₁/γ₂`-torsion, in `L₂`: `cl((xy)³) = cl(x³) + cl(y³) + 3 cl[y, x]`. -/
theorem cl_cube_mul {x y : G} (hx : x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hy : y ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    (x * y) ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 ∧
      cl G 1 ((x * y) ^ 3) = cl G 1 (x ^ 3) + cl G 1 (y ^ 3) + (3 : ℤ) • cl G 1 (tc y x) := by
  have hc : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero y) (mem_lcs_zero x)
  have hP : x ^ 3 * y ^ 3 * tc y x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    mul_mem (mul_mem hx hy) (pow_mem hc 3)
  have hm := cube_mul_mod' x y
  have hxy : (x * y) ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [← mul_inv_cancel_left (x ^ 3 * y ^ 3 * tc y x ^ 3) ((x * y) ^ 3)]
    exact mul_mem hP (lcs_mem_of_le (by norm_num) hm)
  refine ⟨hxy, ?_⟩
  rw [← (cl_eq_cl hP hxy).mpr hm, cl_mul (mul_mem hx hy) (pow_mem hc 3), cl_mul hx hy, cl_pow3 hc]

section ClassFourIdentities

variable (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
include h5

/-- `[ab, x] = [a, x][b, x]` for `a, b ∈ γ₂` (I1). -/
theorem tc_mul_left_L1 {a b : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc (a * b) x = tc a x * tc b x := by
  have hta : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := tc_mem (by omega) ha (mem_lcs_zero x)
  have hc : b * tc a x = tc a x * b :=
    commutatorElement_eq_one_iff_mul_comm.mp (comm_eq_one h5 (by norm_num) hb hta)
  rw [tc_mul_left]
  calc b⁻¹ * tc a x * b * tc b x = b⁻¹ * (tc a x * b) * tc b x := by group
    _ = b⁻¹ * (b * tc a x) * tc b x := by rw [hc]
    _ = tc a x * tc b x := by group

/-- Elements of `γ₃` commute. -/
theorem comm_L2 {a b : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 2) : a * b = b * a :=
  commutatorElement_eq_one_iff_mul_comm.mp (comm_eq_one h5 (by norm_num) ha hb)

/-- `[c, z] = 1` for `c ∈ γ₃`, `z ∈ γ₂`. -/
theorem tc_L2_L1 {c z : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : tc c z = 1 := by
  have : tc c z ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := tc_mem (by omega) hc hz
  rwa [h5, mem_bot] at this

/-- `[c, x] = 1` for `c ∈ γ₄`. -/
theorem tc_L3 {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (x : G) : tc c x = 1 := by
  have : tc c x ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := tc_mem (by omega) hc (mem_lcs_zero x)
  rwa [h5, mem_bot] at this

/-- The expansion of `[X³, y]` in class `≤ 4` (I5): with `c = [X, y]`, `f = [c, X]`,
`g = [f, X]`, `[X³, y] = c³ f³ g`. -/
theorem tc_cube_formula (X y : G) :
    tc (X ^ 3) y = tc X y ^ 3 * tc (tc X y) X ^ 3 * tc (tc (tc X y) X) X := by
  obtain ⟨c, hc⟩ : ∃ c, c = tc X y := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = tc c X := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = tc f X := ⟨_, rfl⟩
  have hc1 : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    hc ▸ tc_mem (by omega) (mem_lcs_zero X) (mem_lcs_zero y)
  have hf2 : f ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hf ▸ tc_mem (by omega) hc1 (mem_lcs_zero X)
  have hg3 : g ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := hg ▸ tc_mem (by omega) hf2 (mem_lcs_zero X)
  have hgz : ∀ z : G, z * g = g * z := fun z => central_L3 h5 hg3 z
  have hcf : c * f = f * c :=
    commutatorElement_eq_one_iff_mul_comm.mp (comm_eq_one h5 (by norm_num) hc1 hf2)
  have hc' : X⁻¹ * c * X = c * f := by rw [hf, tc]; group
  have hf' : X⁻¹ * f * X = f * g := by rw [hg, tc]; group
  have hmul : ∀ p r : G, X⁻¹ * (p * r) * X = (X⁻¹ * p * X) * (X⁻¹ * r * X) := fun p r => by group
  have hfc : ∀ Z, f * (c * Z) = c * (f * Z) := fun Z => by rw [← mul_assoc, ← hcf, mul_assoc]
  have hgc0 : g * c = c * g := (hgz c).symm
  have hgf0 : g * f = f * g := (hgz f).symm
  have hgc : ∀ Z, g * (c * Z) = c * (g * Z) := fun Z => by rw [← mul_assoc, hgc0, mul_assoc]
  have hgf : ∀ Z, g * (f * Z) = f * (g * Z) := fun Z => by rw [← mul_assoc, hgf0, mul_assoc]
  rw [← hc, ← hf, ← hg, tc_cube_expand, ← hc, hc', hmul, hc', hf']
  simp only [pow_three, mul_assoc, hfc, hgc, hgf, hgc0]

end ClassFourIdentities

section Hyp

variable (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
  (h4 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 3, c ^ 3 = 1)
  (h9 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 9 ∈ (⊤ : Subgroup G).lowerCentralSeries 3)

include h5 h4 in
/-- `[Y, x³] = [Y, x]³` for `Y ∈ γ₂` when `γ₄³ = 1` (I4). -/
theorem tc_pow_three_rightA {Y : G} (hY : Y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc Y (x ^ 3) = tc Y x ^ 3 := by
  obtain ⟨c, hc⟩ : ∃ c, c = tc Y x := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = tc c x := ⟨_, rfl⟩
  have hc2 : c ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hc ▸ tc_mem (by omega) hY (mem_lcs_zero x)
  have he3 : e ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := he ▸ tc_mem (by omega) hc2 (mem_lcs_zero x)
  have hez : ∀ g : G, g * e = e * g := fun g => central_L3 h5 he3 g
  have hY' : x⁻¹ * Y * x = Y * c := by rw [hc, tc]; group
  have hc' : x⁻¹ * c * x = c * e := by rw [he, tc]; group
  have he' : x⁻¹ * e * x = e := by rw [hez x⁻¹]; group
  have hmul : ∀ p q : G, x⁻¹ * (p * q) * x = (x⁻¹ * p * x) * (x⁻¹ * q * x) := fun p q => by group
  have key : (x ^ 3)⁻¹ * Y * x ^ 3 = x⁻¹ * (x⁻¹ * (x⁻¹ * Y * x) * x) * x := by
    simp only [pow_three]; group
  rw [← hc]
  calc tc Y (x ^ 3) = Y⁻¹ * ((x ^ 3)⁻¹ * Y * x ^ 3) := by simp only [tc]; group
    _ = Y⁻¹ * (Y * c * (c * e) * (c * e * e)) := by
      rw [key, hY', hmul Y c, hY', hc', hmul (Y * c) (c * e), hmul Y c, hY', hc', hmul c e, hc',
        he']
    _ = c * c * (e * c) * (e * e) := by group
    _ = c * c * (c * e) * (e * e) := by rw [← hez c]
    _ = c ^ 3 * e ^ 3 := by simp only [pow_three, mul_assoc]
    _ = c ^ 3 := by rw [h4 e he3, mul_one]

include h5 h9 in
/-- `[a, x]⁹ = 1` for `a ∈ γ₂`, since `[a, x]⁹ = [a⁹, x]` and `a⁹ ∈ γ₄`. -/
theorem tc_pow_nine_L1A {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc a x ^ 9 = 1 := by
  have e : tc ((a ^ 3) ^ 3) x = tc a x ^ (3 * 3) := by
    rw [tc_pow_three_left h5 (pow_mem ha 3), tc_pow_three_left h5 ha, ← pow_mul]
  show tc a x ^ (3 * 3) = 1
  rw [← e, ← pow_mul]
  exact tc_of_central (fun g => central_L3 h5 (h9 a ha) g) x

include h5 h9 in
/-- `γ₃` has exponent dividing `9` (from (I6)). -/
theorem pow_nine_L2A {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 2) : c ^ 9 = 1 := by
  let S : Subgroup G :=
    { carrier := {c | c ∈ (⊤ : Subgroup G).lowerCentralSeries 2 ∧ c ^ 9 = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha9⟩ ⟨hb, hb9⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hab : Commute a b := comm_L2 h5 ha hb
        rw [hab.mul_pow, ha9, hb9, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha9⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha9, inv_one]⟩ }
  have hle : (⊤ : Subgroup G).lowerCentralSeries 2 ≤ S := by
    show ⁅(⊤ : Subgroup G).lowerCentralSeries 1, ⊤⁆ ≤ S
    rw [commutator_le]
    intro a ha g _
    have e : ⁅a, g⁆ = tc a⁻¹ g⁻¹ := by rw [tc_eq, inv_inv, inv_inv]
    refine ⟨commutator_mem_lcs (by omega) ha (mem_lcs_zero g), ?_⟩
    rw [e]
    exact tc_pow_nine_L1A h5 h9 (inv_mem ha) _
  exact (hle hc).2

include h5 h4 h9 in
/-- `[x⁹, y] = [x, y]⁹` (I6, with (H2)). -/
theorem tc_pow_nineA (x y : G) : tc (x ^ 9) y = tc x y ^ 9 := by
  have hd : tc (x ^ 3) y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero _) (mem_lcs_zero y)
  have hdx : tc (tc (x ^ 3) y) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (by omega) hd (mem_lcs_zero x)
  have hf : tc (tc (x ^ 3) y) (x ^ 3) ^ 3 = 1 := by
    rw [tc_pow_three_rightA h5 h4 hd, ← pow_mul]
    exact pow_nine_L2A h5 h9 hdx
  have hg : tc (tc (tc (x ^ 3) y) (x ^ 3)) (x ^ 3) = 1 := by
    rw [tc_pow_three_rightA h5 h4 hd x, tc_pow_three_left h5 (lcs_mem_of_le (by norm_num) hdx)]
    exact h4 _ (tc_mem (by omega) hdx (mem_lcs_zero _))
  have e1 : tc (x ^ 9) y = tc (x ^ 3) y ^ 3 := by
    rw [show x ^ 9 = (x ^ 3) ^ 3 by rw [← pow_mul], tc_cube_formula h5 (x ^ 3) y, hf, hg,
      mul_one, mul_one]
  have hc : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero x) (mem_lcs_zero y)
  have hf2 : tc (tc x y) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := tc_mem (by omega) hc (mem_lcs_zero x)
  have hg3 : tc (tc (tc x y) x) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) hf2 (mem_lcs_zero x)
  have hcf : Commute (tc x y ^ 3) (tc (tc x y) x ^ 3) :=
    (show Commute (tc x y) (tc (tc x y) x) from
      commutatorElement_eq_one_iff_mul_comm.mp (comm_eq_one h5 (by norm_num) hc hf2)).pow_pow 3 3
  have hgc : Commute (tc x y ^ 3 * tc (tc x y) x ^ 3) (tc (tc (tc x y) x) x) :=
    central_L3 h5 hg3 _
  have hf9 : tc (tc x y) x ^ (3 * 3) = 1 := pow_nine_L2A h5 h9 hf2
  rw [e1, tc_cube_formula h5 x y, hgc.mul_pow, hcf.mul_pow, ← pow_mul, ← pow_mul, h4 _ hg3,
    mul_one, hf9, mul_one]

include h5 h4 h9 in
/-- `[x⁹, y] ∈ γ₄`. -/
theorem tc_pow_nine_memA (x y : G) :
    tc (x ^ 9) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  rw [tc_pow_nineA h5 h4 h9]
  exact h9 _ (tc_mem (by omega) (mem_lcs_zero x) (mem_lcs_zero y))

include h5 h4 h9 in
theorem tc_pow_nine_mul_memA (x y : G) (k : ℕ) :
    tc (x ^ (9 * k)) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  rw [show 9 * k = k * 9 from mul_comm 9 k, pow_mul]
  exact tc_pow_nine_memA h5 h4 h9 _ y

include h5 h4 h9 in
/-- `[x²⁷, y] = 1`. -/
theorem tc_pow_27A (x y : G) : tc (x ^ 27) y = 1 := by
  have hc := tc_pow_nine_memA h5 h4 h9 x y
  rw [show x ^ 27 = (x ^ 9) ^ 3 by rw [← pow_mul], tc_cube_formula h5 (x ^ 9) y,
    tc_L3 h5 hc (x ^ 9), one_pow, mul_one, show tc (1 : G) (x ^ 9) = 1 by simp [tc], mul_one]
  exact h4 _ hc

include h5 h4 h9 in
theorem tc_pow_27_mulA (x y : G) (k : ℕ) : tc (x ^ (27 * k)) y = 1 := by
  rw [show 27 * k = k * 27 from mul_comm 27 k, pow_mul]
  exact tc_pow_27A h5 h4 h9 _ y

include h5 h4 h9 in
/-- `[b, x⁹] = 1` for `b ∈ γ₂`. -/
theorem tc_L1_pow_nineA {b : G} (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc b (x ^ 9) = 1 := by
  rw [show x ^ 9 = (x ^ 3) ^ 3 by rw [← pow_mul], tc_pow_three_rightA h5 h4 hb,
    tc_pow_three_rightA h5 h4 hb, ← pow_mul]
  exact tc_pow_nine_L1A h5 h9 hb x

include h5 h4 h9 in
theorem tc_L1_pow_nine_mulA {b : G} (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G)
    (k : ℕ) : tc b (x ^ (9 * k)) = 1 := by
  rw [pow_mul]
  exact tc_eq_one_iff.mpr ((tc_eq_one_iff.mp (tc_L1_pow_nineA h5 h4 h9 hb x)).pow_right k)

include h5 h4 h9 in
theorem tc_pow_nine_mul_L1A {b : G} (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G)
    (k : ℕ) : tc (x ^ (9 * k)) b = 1 := by
  rw [← tc_inv, tc_L1_pow_nine_mulA h5 h4 h9 hb, inv_one]

end Hyp

/-! ## Maps with values in an abelian group, additive on a subgroup -/

section AddMapG

variable {M : Type*} [AddCommGroup M] {S : Subgroup G} {A : G → M}

theorem addMapG_one (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) : A 1 = 0 := by
  have h := hA 1 (one_mem S) 1 (one_mem S)
  rw [mul_one] at h
  calc A 1 = A 1 + A 1 - A 1 := by abel
    _ = A 1 - A 1 := by rw [← h]
    _ = 0 := sub_self _

theorem addMapG_inv (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {a : G} (ha : a ∈ S) :
    A a⁻¹ = -A a := by
  have h := hA a ha a⁻¹ (inv_mem ha)
  rw [mul_inv_cancel, addMapG_one hA] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem addMapG_zpow (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {a : G} (ha : a ∈ S)
    (k : ℤ) : A (a ^ k) = k • A a := by
  induction k using Int.induction_on with
  | zero => simp [addMapG_one hA]
  | succ n ih => rw [zpow_add_one, hA _ (zpow_mem ha _) _ ha, ih, add_smul, one_smul]
  | pred n ih =>
    rw [zpow_sub_one, hA _ (zpow_mem ha _) _ (inv_mem ha), ih, addMapG_inv hA ha, sub_smul,
      one_smul, sub_eq_add_neg]

theorem addMapG_pow (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {a : G} (ha : a ∈ S)
    (n : ℕ) : A (a ^ n) = (n : ℤ) • A a := by
  rw [← addMapG_zpow hA ha, zpow_natCast]

theorem addMapG_oprod (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {n : ℕ} {x : Fin n → G}
    (hx : ∀ i, x i ∈ S) (a : Fin n → ℤ) : A (oprod x a) = ∑ i, a i • A (x i) := by
  unfold oprod
  have : ∀ l : List G, (∀ y ∈ l, y ∈ S) → A l.prod = (l.map A).sum := by
    intro l
    induction l with
    | nil => intro _; simp [addMapG_one hA]
    | cons y l ih =>
      intro hl
      rw [List.prod_cons, hA _ (hl y List.mem_cons_self) _
        (list_prod_mem fun z hz => hl z (List.mem_cons_of_mem _ hz)),
        ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.sum_cons]
  rw [this _ (fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; exact zpow_mem (hx i) _),
    List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ => addMapG_zpow hA (hx i) _

end AddMapG

/-- A `𝔽₃`-valued map additive on an additive subgroup is additive on finite sums. -/
theorem addMapS_sum {M : Type*} [AddCommGroup M] {S : AddSubgroup M} {A : M → ZMod 3}
    (hA : ∀ a ∈ S, ∀ b ∈ S, A (a + b) = A a + A b) {ι : Type*} (s : Finset ι) (f : ι → M)
    (hf : ∀ i ∈ s, f i ∈ S) : A (∑ i ∈ s, f i) = ∑ i ∈ s, A (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hA 0 (zero_mem S) 0 (zero_mem S)
    rw [add_zero] at h
    simp only [Finset.sum_empty]
    linear_combination -h
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, hA _ (hf x (Finset.mem_insert_self x s)) _
      (sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem dvd3_mod {X : ℤ} {n : ℕ} (h : X ≡ 0 [ZMOD n]) (hn : 3 ∣ n) : (3 : ℤ) ∣ X := by
  have h1 := Int.ModEq.dvd h
  have h2 : (3 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
  have h3 := h2.trans h1
  rwa [zero_sub, dvd_neg] at h3

/-! ## The computation -/

/-- The situation of the proof of Theorem 6.10: class `≤ 4`, `γ₄³ = 1`, `γ₂⁹ ⊆ γ₄`, the orders of
the first layer are `3`, `9` or divisible by `27`, those of the second and third layers are
divisible by `3`. `act i` says that `x_i` is *active*; an inactive `x_i` has
`x_i^{d(i)} ∈ γ₂³γ₃`, and the coefficients of conditions (D) at the active indices are seen
modulo `3` through the matrix `b` (`hind`). -/
structure SetupA (T : Data G) (act : Fin T.s → Prop) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  h4 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 3, c ^ 3 = 1
  h9 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 9 ∈ (⊤ : Subgroup G).lowerCentralSeries 3
  valid : T.Valid
  hd : ∀ i, T.d i = 3 ∨ T.d i = 9 ∨ 27 ∣ T.d i
  he : ∀ k, 3 ∣ T.e k
  hf : ∀ l, 3 ∣ T.f l
  hK : ∀ i, ¬ act i → ∃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, T.x₁ i ^ T.d i = a ^ 3 * c
  hind : ∀ cf : Fin T.s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * T.b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h

/-- The coefficient of `b_{h·}` in row `r` of condition (B):
`[r < h] u_{rh} - [h < r] u_{hr} (d(r)/d(h))`. -/
def crow (T : Data G) (τ : Coeffs T.s T.t) (r h : Fin T.s) : ℤ :=
  (if r < h then τ.u r h else 0) - (if h < r then τ.u h r * T.q h r else 0)

namespace SetupA

variable {T : Data G} {act : Fin T.s → Prop} (S : SetupA T act)
include S

theorem three_dvd_d (i : Fin T.s) : 3 ∣ T.d i := by
  rcases S.hd i with h | h | h
  · rw [h]
  · rw [h]; norm_num
  · exact (show (3 : ℕ) ∣ 27 by norm_num).trans h

theorem d_dvd {i j : Fin T.s} (h : i ≤ j) : T.d i ∣ T.d j := S.valid.basis₁.dvd i j h

theorem d_three_of_le {h i : Fin T.s} (hhi : h ≤ i) (hi : T.d i = 3) : T.d h = 3 := by
  have h1 := S.d_dvd hhi
  rw [hi] at h1
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
  · exact absurd (S.valid.basis₁.one_lt h) (by omega)
  · exact h1

theorem d_le_nine {h j : Fin T.s} (hhj : h ≤ j) (hj : T.d j = 9) : T.d h = 3 ∨ T.d h = 9 := by
  have h1 := S.d_dvd hhj
  rw [hj] at h1
  rcases S.hd h with h3 | h9 | h27
  · exact Or.inl h3
  · exact Or.inr h9
  · exact absurd (h27.trans h1) (by norm_num)

theorem d39_of_le {h i : Fin T.s} (hhi : h ≤ i) (hi : T.d i = 3 ∨ T.d i = 9) :
    T.d h = 3 ∨ T.d h = 9 := by
  rcases hi with h3 | h9
  · exact Or.inl (S.d_three_of_le hhi h3)
  · exact S.d_le_nine hhi h9

theorem d_ge_nine {i j : Fin T.s} (hij : i ≤ j) (hi : 9 ∣ T.d i) : T.d j = 9 ∨ 27 ∣ T.d j := by
  have h1 := hi.trans (S.d_dvd hij)
  rcases S.hd j with h3 | h9 | h27
  · rw [h3] at h1; norm_num at h1
  · exact Or.inl h9
  · exact Or.inr h27

theorem nine_dvd_of_ne {i : Fin T.s} (hi : T.d i ≠ 3) : 9 ∣ T.d i := by
  rcases S.hd i with h3 | h9 | h27
  · exact absurd h3 hi
  · rw [h9]
  · exact (show (9 : ℕ) ∣ 27 by norm_num).trans h27

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

theorem ch_of_three {i : Fin T.s} (hi : T.d i = 3) : T.ch i 2 = 3 ∧ T.ch i 3 = 1 := by
  unfold Data.ch; rw [hi]; exact ⟨rfl, rfl⟩

theorem ch_of_nine {i : Fin T.s} (hi : T.d i = 9) : T.ch i 2 = 36 ∧ T.ch i 3 = 84 := by
  unfold Data.ch; rw [hi]; exact ⟨rfl, rfl⟩

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

theorem tcY_L1 {i : Fin T.s} (h9 : 9 ∣ T.d i) {b : G}
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : tc (T.x₁ i ^ T.d i) b = 1 := by
  obtain ⟨r, hr⟩ := h9
  rw [hr]; exact tc_pow_nine_mul_L1A S.h5 S.h4 S.h9 hb _ _

theorem tcY_mem {i : Fin T.s} (h9 : 9 ∣ T.d i) (y : G) :
    tc (T.x₁ i ^ T.d i) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  obtain ⟨r, hr⟩ := h9
  rw [hr]; exact tc_pow_nine_mul_memA S.h5 S.h4 S.h9 _ _ _

theorem tcY_one {i : Fin T.s} (h27 : 27 ∣ T.d i) (y : G) : tc (T.x₁ i ^ T.d i) y = 1 := by
  obtain ⟨r, hr⟩ := h27
  rw [hr]; exact tc_pow_27_mulA S.h5 S.h4 S.h9 _ _ _

/-- `[x_i^{3 d(i)}, y] ∈ γ₄` when `d(i) = 3`. -/
theorem tc9_mem {i : Fin T.s} (hi : T.d i = 3) (y : G) :
    tc ((T.x₁ i ^ T.d i) ^ 3) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  rw [hi, ← pow_mul]
  exact tc_pow_nine_memA S.h5 S.h4 S.h9 _ _

/-- For an inactive `i`, `[[x_i^{d(i)}, x], z] = 1`. -/
theorem tcK {i : Fin T.s} (hi : ¬ act i) (x z : G) : tc (tc (T.x₁ i ^ T.d i) x) z = 1 := by
  obtain ⟨a, ha, c, hc, he⟩ := S.hK i hi
  have h1 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := tc_mem (by omega) ha (mem_lcs_zero x)
  have h2 : tc c x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) hc (mem_lcs_zero x)
  rw [he, tc_mul_left_L1 S.h5 (pow_mem ha 3) (lcs_mem_of_le (by norm_num) hc),
    tc_pow_three_left S.h5 ha,
    tc_mul_left_L1 S.h5 (lcs_mem_of_le (by norm_num) (pow_mem h1 3)) (lcs_mem_of_le (by norm_num) h2),
    tc_L3 S.h5 h2, mul_one, tc_pow_three_left S.h5 (lcs_mem_of_le (by norm_num) h1)]
  exact S.h4 _ (tc_mem (by omega) h1 (mem_lcs_zero z))

/-- For an inactive `g`, the constants `α^{(gh)}` vanish modulo `3`. -/
theorem α3 {g : Fin T.s} (hg : ¬ act g) {h : Fin T.s} (hgh : g ≤ h) (l : Fin T.u) :
    (3 : ℤ) ∣ T.α g h l := by
  obtain ⟨a, ha, c, hc, he⟩ := S.hK g hg
  have hm := S.valid.hα g h hgh
  have h1 : tc a (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (by omega) ha (mem_lcs_zero _)
  have h2 : tc c (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) hc (mem_lcs_zero _)
  have e1 : tc (T.x₁ g ^ T.d g) (T.x₁ h) = tc a (T.x₁ h) ^ 3 * tc c (T.x₁ h) := by
    rw [he, tc_mul_left_L1 S.h5 (pow_mem ha 3) (lcs_mem_of_le (by norm_num) hc),
      tc_pow_three_left S.h5 ha]
  have hY : tc (T.x₁ g ^ T.d g) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (by omega) (S.Y1 g) (mem_lcs_zero _)
  obtain ⟨a', ha'⟩ := S.valid.basis₃.span _ h1
  have hX : cl G 2 (oprod T.x₃ (T.α g h)) = (3 : ℤ) • cl G 2 (oprod T.x₃ a') := by
    rw [(cl_eq_cl (oprod_mem S.x3mem _) hY).mpr hm, e1,
      cl_mul (pow_mem h1 3) (lcs_mem_of_le (by norm_num) h2),
      (cl_eq_zero_iff (lcs_mem_of_le (by norm_num) h2)).mpr h2, add_zero,
      (cl_eq_cl (oprod_mem S.x3mem _) h1).mpr ha', cl_pow3 h1]
  have hP : oprod T.x₃ (fun l => T.α g h l - 3 * a' l) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [← cl_eq_zero_iff (oprod_mem S.x3mem _), cl_oprod S.x3mem]
    rw [cl_oprod S.x3mem, cl_oprod S.x3mem, Finset.smul_sum] at hX
    simp only [sub_smul, Finset.sum_sub_distrib, hX, mul_smul, sub_self]
  have hd : (T.f l : ℤ) ∣ T.α g h l - 3 * a' l := (S.valid.basis₃.indep _).mp hP l
  have h3 : (3 : ℤ) ∣ (T.f l : ℤ) := by exact_mod_cast S.hf l
  have := dvd_add (h3.trans hd) (dvd_mul_right 3 (a' l))
  rwa [sub_add_cancel] at this

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

/-- Condition (C): `3 ∣ u_{ij}` when `d(i) = d(j) ∈ {3, 9}`. -/
theorem u3_eq {i j : Fin T.s} (hij : i < j) (hd : T.d i = T.d j) (h39 : T.d i = 3 ∨ T.d i = 9) :
    (3 : ℤ) ∣ τ.u i j := by
  have h := hτ.C₁ i j hij
  have hq : T.q i j = 1 := by
    have e : T.d j / T.d i = 1 := by
      rw [← hd]; exact Nat.div_self (lt_trans Nat.zero_lt_one (S.valid.basis₁.one_lt i))
    simp [Data.q, e]
  rw [hq] at h
  have h' := Int.ModEq.dvd h
  rcases h39 with h3 | h9
  · rw [(S.ch_of_three h3).1, (S.ch_of_three h3).2, h3] at h'
    push_cast at h'
    omega
  · rw [(S.ch_of_nine h9).1, (S.ch_of_nine h9).2, h9] at h'
    push_cast at h'
    omega

/-- `3 ∣ u_{hi} q_{hi}` for `h < i` when `d(h) ∈ {3, 9}`. -/
theorem uq3 {h i : Fin T.s} (hhi : h < i) (hh : T.d h = 3 ∨ T.d h = 9) :
    (3 : ℤ) ∣ τ.u h i * T.q h i := by
  rcases hh with h3 | h9
  · rcases S.hd i with i3 | i9 | ⟨r, hr⟩
    · exact (S.u3_eq hτ hhi (h3.trans i3.symm) (Or.inl h3)).mul_right _
    · refine Dvd.dvd.mul_left ?_ _
      have e : T.d i / T.d h = 3 := by simp [h3, i9]
      simp [Data.q, e]
    · refine Dvd.dvd.mul_left ?_ _
      have e : T.d i / T.d h = 9 * r := by rw [h3, hr]; omega
      simp only [Data.q, e]
      exact_mod_cast (show 3 ∣ 9 * r from Dvd.intro (3 * r) (by ring))
  · rcases S.d_ge_nine hhi.le (by simp [h9]) with i9 | ⟨r, hr⟩
    · exact (S.u3_eq hτ hhi (h9.trans i9.symm) (Or.inr h9)).mul_right _
    · refine Dvd.dvd.mul_left ?_ _
      have e : T.d i / T.d h = 3 * r := by rw [h9, hr]; omega
      simp only [Data.q, e]
      exact_mod_cast (show 3 ∣ 3 * r from Dvd.intro r rfl)

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

/-- Condition (E) in a row `r` of order `3` or `9`, modulo `3`:
`∑_k v'_{rk} d_{kl} ≡ ∑_h crow_{rh} c_{hl}`. -/
theorem Erow (r : Fin T.s) (hr : T.d r = 3 ∨ T.d r = 9) (l : Fin T.u) :
    (3 : ℤ) ∣ (∑ k, τ.v' r k * T.dd k l) - ∑ h, crow T τ r h * T.c h l := by
  have h' := dvd3_mod (hτ.E r l) (S.gcd_f3 r l)
  have hu : ∀ h, h < r → (3 : ℤ) ∣ τ.u h r * T.q h r := fun h hh =>
    S.uq3 hτ hh (S.d39_of_le hh.le hr)
  have s1 : (3 : ℤ) ∣ ∑ h, if h < r then τ.u h r * T.q h r * T.α h r l else 0 :=
    dvd_sum_ite _ _ fun h hh => (hu h hh).mul_right _
  have s5 : (3 : ℤ) ∣ ∑ g, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h * T.α g h l else 0 := by
    refine Finset.dvd_sum fun g _ => dvd_sum_ite _ _ fun h hh => ?_
    by_cases hg : act g
    · exact (S.w3 hτ hg hh.1 hh.2).mul_right _
    · exact (S.α3 hg (hh.1.trans hh.2) l).mul_left _
  have s6 : (3 : ℤ) ∣ ∑ g, ∑ h, if g ≤ h ∧ h ≤ r then τ.w g h r * T.α g h l else 0 := by
    refine Finset.dvd_sum fun g _ => dvd_sum_ite _ _ fun h hh => ?_
    by_cases hg : act g
    · exact (S.w3 hτ hg hh.1 hh.2).mul_right _
    · exact (S.α3 hg hh.1 l).mul_left _
  have s7 : (3 : ℤ) ∣ ∑ g, ∑ h, if r < g ∧ g ≤ h then τ.w' r g h * T.α g h l else 0 := by
    refine Finset.dvd_sum fun g _ => dvd_sum_ite _ _ fun h hh => ?_
    by_cases hg : act g
    · exact (S.w'3 hτ hg hh.1 hh.2).mul_right _
    · exact (S.α3 hg hh.2 l).mul_left _
  have ec : ∑ h, crow T τ r h * T.c h l = (∑ h, if r < h then τ.u r h * T.c h l else 0) -
      ∑ h, if h < r then τ.u h r * T.q h r * T.c h l else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [crow]
    split_ifs <;> ring
  rw [ec]
  generalize (∑ k, τ.v' r k * T.dd k l) = A at h' ⊢
  generalize (∑ h, if h < r then τ.u h r * T.q h r * T.α h r l else 0) = B1 at h' s1
  generalize (∑ h, if r < h then τ.u r h * T.c h l else 0) = B2 at h' ⊢
  generalize (∑ h, if h < r then τ.u h r * T.q h r * T.c h l else 0) = B3 at h' ⊢
  generalize (∑ g, ∑ h, if g ≤ r ∧ r ≤ h then τ.w g r h * T.α g h l else 0) = B5 at h' s5
  generalize (∑ g, ∑ h, if g ≤ h ∧ h ≤ r then τ.w g h r * T.α g h l else 0) = B6 at h' s6
  generalize (∑ g, ∑ h, if r < g ∧ g ≤ h then τ.w' r g h * T.α g h l else 0) = B7 at h' s7
  omega

/-- Condition (B) in row `r`: `v'_{rk} e(k) = -∑_h crow_{rh} b_{hk} - v_{rk} d(r)`. -/
theorem Brow (r : Fin T.s) (k : Fin T.t) :
    τ.v' r k * (T.e k : ℤ) = -(∑ h, crow T τ r h * T.b h k) - τ.v r k * (T.d r : ℤ) := by
  have h := hτ.B r k
  have ec : ∑ h, crow T τ r h * T.b h k = (∑ h, if r < h then τ.u r h * T.b h k else 0) -
      ∑ h, if h < r then τ.u h r * T.q h r * T.b h k else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [crow]
    split_ifs <;> ring
  rw [ec]
  linarith

/-- `3 ∣ crow_{rh}` when `d(h) = 3` (and `d(r) ∈ {3, 9}`). -/
theorem crow3 (r : Fin T.s) {h : Fin T.s} (h3 : T.d h = 3) : (3 : ℤ) ∣ crow T τ r h := by
  unfold crow
  rcases lt_trichotomy r h with hrh | rfl | hhr
  · rw [if_pos hrh, if_neg (not_lt.mpr hrh.le), sub_zero]
    have hr3 : T.d r = 3 := S.d_three_of_le hrh.le h3
    exact S.u3_eq hτ hrh (hr3.trans h3.symm) (Or.inl hr3)
  · simp
  · rw [if_neg (not_lt.mpr hhr.le), if_pos hhr, zero_sub, dvd_neg]
    exact S.uq3 hτ hhr (Or.inl h3)

/-- The factors `[x_h^{d(h)}, x_r]^{crow_{rh}}` lie in `γ₄`. -/
theorem memY (r h : Fin T.s) :
    tc (T.x₁ h ^ T.d h) (T.x₁ r) ^ crow T τ r h ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  by_cases h3 : T.d h = 3
  · obtain ⟨m, hm⟩ := S.crow3 hτ r h3
    rw [hm, zpow_mul, zpow_ofNat, ← tc_pow_three_left S.h5 (S.Y1 h)]
    exact zpow_mem (S.tc9_mem h3 _) _
  · exact zpow_mem (S.tcY_mem (S.nine_dvd_of_ne h3) _) _

omit hτ in
/-- `[x_{2k}, x_r]^{d(r)} ∈ γ₄` when `d(r) ∈ {3, 9}`. -/
theorem mem2 (r : Fin T.s) (hr : T.d r = 3 ∨ T.d r = 9) (k : Fin T.t) :
    tc (T.x₂ k) (T.x₁ r) ^ T.d r ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  rcases hr with h3 | h9
  · have hY : T.x₁ r ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
      have := S.Y1 r; rwa [h3] at this
    rw [h3, ← tc_pow_three_rightA S.h5 S.h4 (S.x2mem k)]
    exact tc_mem (by omega) (S.x2mem k) hY
  · rw [h9, tc_pow_nine_L1A S.h5 S.h9 (S.x2mem k)]
    exact one_mem _

/-- **The row identity** (wiki §4, `(∗)`, paired with `x_r`): for a row `r` with `d(r) ∈ {3, 9}`,
conditions (B) and (E) in row `r` give
`∑_k v_{rk} F([x_{2k}, x_r]^{d(r)}) + ∑_h F([x_h^{d(h)}, x_r]^{crow_{rh}}) = 0`
for every `F` additive on `γ₄`. The proof evaluates `[∏_k x_{2k}^{e(k) v'_{rk}}, x_r]` in the
abelian group `γ₃` in two ways; the terms with `c_{hl}` cancel exactly. -/
theorem row (r : Fin T.s) (hr : T.d r = 3 ∨ T.d r = 9) {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b) :
    ∑ k, (τ.v r k : ZMod 3) * F (tc (T.x₂ k) (T.x₁ r) ^ T.d r) +
      ∑ h, F (tc (T.x₁ h ^ T.d h) (T.x₁ r) ^ crow T τ r h) = 0 := by
  classical
  -- additivity of `c ↦ F [c, x_r]` on `γ₃`, and its vanishing on `γ₄`
  have hL2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      F (tc (a * b) (T.x₁ r)) = F (tc a (T.x₁ r)) + F (tc b (T.x₁ r)) := by
    intro a ha b hb
    rw [tc_mul_left_L1 S.h5 (lcs_mem_of_le (by norm_num) ha) (lcs_mem_of_le (by norm_num) hb),
      hF _ (tc_mem (by omega) ha (mem_lcs_zero _)) _ (tc_mem (by omega) hb (mem_lcs_zero _))]
  have hL3 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, F (tc a (T.x₁ r)) = 0 := by
    intro a ha
    rw [tc_L3 S.h5 ha]; exact addMap_one hF
  have hx3 : ∀ {y : G} {a : Fin T.u → ℤ},
      (oprod T.x₃ a)⁻¹ * y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      F (tc y (T.x₁ r)) = ∑ l, (a l : ZMod 3) * F (tc (T.x₃ l) (T.x₁ r)) := by
    intro y a hy
    rw [← mul_inv_cancel_left (oprod T.x₃ a) y,
      addMap_mul_mem (A := fun c => F (tc c (T.x₁ r)))
        ((Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)) hL2 hL3 (oprod_mem S.x3mem _) hy,
      addMap_oprod (A := fun c => F (tc c (T.x₁ r))) hL2 S.x3mem]
  -- the element `A_r = ∏_k (x_{2k}^{e(k)})^{v'_{rk}}` of `γ₃`
  have hA3 : oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    oprod_mem S.x2e _
  -- the value from (E)
  have hE : F (tc (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) (T.x₁ r)) =
      ∑ h, (crow T τ r h : ZMod 3) * F (tc (oprod T.x₃ (T.c h)) (T.x₁ r)) := by
    rw [addMap_oprod (A := fun c => F (tc c (T.x₁ r))) hL2 S.x2e]
    have hdd' : ∀ k, F (tc (T.x₂ k ^ T.e k) (T.x₁ r)) =
        ∑ l, (T.dd k l : ZMod 3) * F (tc (T.x₃ l) (T.x₁ r)) := fun k => hx3 (S.valid.hdd k)
    simp_rw [hdd']
    have hc : ∀ h, F (tc (oprod T.x₃ (T.c h)) (T.x₁ r)) =
        ∑ l, (T.c h l : ZMod 3) * F (tc (T.x₃ l) (T.x₁ r)) := fun h =>
      hx3 (by rw [inv_mul_cancel]; exact one_mem _)
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun k l => (τ.v' r k : ZMod 3) *
      ((T.dd k l : ZMod 3) * F (tc (T.x₃ l) (T.x₁ r)))),
      Finset.sum_comm (f := fun h l => (crow T τ r h : ZMod 3) *
      ((T.c h l : ZMod 3) * F (tc (T.x₃ l) (T.x₁ r))))]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hz := cast3_eq_zero (S.Erow hτ r hr l)
    rw [Int.cast_sub, sub_eq_zero] at hz
    push_cast at hz
    calc ∑ k, (τ.v' r k : ZMod 3) * ((T.dd k l : ZMod 3) * F (tc (T.x₃ l) (T.x₁ r)))
        = (∑ k, (τ.v' r k : ZMod 3) * (T.dd k l : ZMod 3)) * F (tc (T.x₃ l) (T.x₁ r)) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = (∑ h, (crow T τ r h : ZMod 3) * (T.c h l : ZMod 3)) * F (tc (T.x₃ l) (T.x₁ r)) := by
          rw [hz]
      _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun h _ => by ring
  -- the abelian group `γ₃` and the map `Φ = [·, x_r]` on `γ₂`
  letI : CommGroup ↥((⊤ : Subgroup G).lowerCentralSeries 2) :=
    commGroupOfComm _ (fun a ha b hb => comm_L2 S.h5 ha hb)
  let Φ : G → Additive ↥((⊤ : Subgroup G).lowerCentralSeries 2) := fun g =>
    if hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 1 then
      Additive.ofMul ⟨tc g (T.x₁ r), tc_mem (by omega) hg (mem_lcs_zero _)⟩ else 0
  have hΦ : ∀ g (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 1),
      Φ g = Additive.ofMul ⟨tc g (T.x₁ r), tc_mem (by omega) hg (mem_lcs_zero _)⟩ :=
    fun g hg => dif_pos hg
  have hΦadd : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      Φ (a * b) = Φ a + Φ b := by
    intro a ha b hb
    rw [hΦ _ ha, hΦ _ hb, hΦ _ (mul_mem ha hb), ← ofMul_mul]
    exact congrArg Additive.ofMul (Subtype.ext (tc_mul_left_L1 S.h5 ha hb _))
  let Fm : Additive ↥((⊤ : Subgroup G).lowerCentralSeries 2) → ZMod 3 := fun m =>
    F ((Additive.toMul m : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G)
  let M4 : AddSubgroup (Additive ↥((⊤ : Subgroup G).lowerCentralSeries 2)) :=
    { carrier := {m | ((Additive.toMul m : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G) ∈
        (⊤ : Subgroup G).lowerCentralSeries 3}
      add_mem' := fun {a b} ha hb => by
        show (((Additive.toMul a * Additive.toMul b : ↥((⊤ : Subgroup G).lowerCentralSeries 2))) : G) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3
        exact mul_mem (ha : ((Additive.toMul a : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3)
          (hb : ((Additive.toMul b : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3)
      zero_mem' := by
        show ((1 : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3
        exact one_mem _
      neg_mem' := fun {a} ha => by
        show (((Additive.toMul a)⁻¹ : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3
        exact inv_mem (ha : ((Additive.toMul a : ↥((⊤ : Subgroup G).lowerCentralSeries 2)) : G) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3) }
  have hFm : ∀ a ∈ M4, ∀ b ∈ M4, Fm (a + b) = Fm a + Fm b := fun a ha b hb => hF _ ha _ hb
  have hFmΦ : ∀ g (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (n : ℤ),
      Fm (n • Φ g) = F (tc g (T.x₁ r) ^ n) := by
    intro g hg n; rw [hΦ g hg]; rfl
  have hM4Φ : ∀ g (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (n : ℤ),
      tc g (T.x₁ r) ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries 3 → n • Φ g ∈ M4 := by
    intro g hg n h; rw [hΦ g hg]; exact h
  -- `Φ(x_h^{d(h)}) = ∑_k b_{hk} Φ(x_{2k}) + Φ(ȳ_h)`
  have hY : ∀ h, ∑ k, T.b h k • Φ (T.x₂ k) = Φ (T.x₁ h ^ T.d h) - Φ (oprod T.x₃ (T.c h)) := by
    intro h
    have hv := S.valid.hb h
    have hb1 : oprod T.x₂ (T.b h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := oprod_mem S.x2mem _
    have hc1 : oprod T.x₃ (T.c h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _
    have hn1 := lcs_mem_of_le (show 1 ≤ 3 by norm_num) hv
    have hn : Φ ((oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h))⁻¹ * T.x₁ h ^ T.d h) = 0 := by
      rw [hΦ _ hn1]
      have : tc ((oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h))⁻¹ * T.x₁ h ^ T.d h) (T.x₁ r) = 1 :=
        tc_L3 S.h5 hv _
      exact congrArg Additive.ofMul (Subtype.ext this)
    rw [← addMapG_oprod (A := Φ) hΦadd S.x2mem (T.b h), ← mul_inv_cancel_left
      (oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h)) (T.x₁ h ^ T.d h),
      hΦadd _ (mul_mem hb1 hc1) _ hn1, hn, add_zero, hΦadd _ hb1 _ hc1]
    abel
  -- the identity in `γ₃`
  have hM : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) +
      ∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) + ∑ h, crow T τ r h • Φ (T.x₁ h ^ T.d h) =
      ∑ h, crow T τ r h • Φ (oprod T.x₃ (T.c h)) := by
    have hA : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) =
        ∑ k, (τ.v' r k * (T.e k : ℤ)) • Φ (T.x₂ k) := by
      rw [addMapG_oprod hΦadd (fun k => lcs_mem_of_le (by norm_num) (S.x2e k))]
      exact Finset.sum_congr rfl fun k _ => by rw [addMapG_pow hΦadd (S.x2mem k), smul_smul]
    have hsum : ∑ k, (τ.v' r k * (T.e k : ℤ)) • Φ (T.x₂ k) +
        ∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) =
        -∑ h, crow T τ r h • ∑ k, T.b h k • Φ (T.x₂ k) := by
      calc _ = ∑ k, (τ.v' r k * (T.e k : ℤ) + τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
        _ = ∑ k, (-(∑ h, crow T τ r h * T.b h k)) • Φ (T.x₂ k) :=
            Finset.sum_congr rfl fun k _ => by rw [S.Brow hτ r k]; congr 1; ring
        _ = -∑ h, crow T τ r h • ∑ k, T.b h k • Φ (T.x₂ k) := by
            simp only [neg_smul, Finset.sum_smul, Finset.sum_neg_distrib, Finset.smul_sum,
              smul_smul]
            rw [Finset.sum_comm]
    rw [hA, hsum]
    simp_rw [hY, smul_sub, Finset.sum_sub_distrib]
    abel
  -- apply `F` on the `γ₄`-part
  have hFΦA : Fm (Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r))) =
      F (tc (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) (T.x₁ r)) := by
    have := hFmΦ _ (lcs_mem_of_le (by norm_num) hA3) 1
    rwa [one_smul, zpow_one] at this
  have hmA : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) ∈ M4 := by
    have := hM4Φ _ (lcs_mem_of_le (by norm_num) hA3) 1
      (by rw [zpow_one]; exact tc_mem (by omega) hA3 (mem_lcs_zero _))
    rwa [one_smul] at this
  have hd : ∀ k, tc (T.x₂ k) (T.x₁ r) ^ (τ.v r k * (T.d r : ℤ)) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro k
    rw [mul_comm (τ.v r k), zpow_mul, zpow_natCast]
    exact zpow_mem (S.mem2 r hr k) _
  have hm1 : ∀ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) ∈ M4 := fun k =>
    hM4Φ _ (S.x2mem k) _ (hd k)
  have hm2 : ∀ h, crow T τ r h • Φ (T.x₁ h ^ T.d h) ∈ M4 := fun h =>
    hM4Φ _ (S.Y1 h) _ (S.memY hτ r h)
  have hc4 : ∀ h, tc (oprod T.x₃ (T.c h)) (T.x₁ r) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun h => tc_mem (by omega) (oprod_mem S.x3mem _) (mem_lcs_zero _)
  have hm3 : ∀ h, crow T τ r h • Φ (oprod T.x₃ (T.c h)) ∈ M4 := fun h =>
    hM4Φ _ (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _) _
      (zpow_mem (hc4 h) _)
  have hFM := congrArg Fm hM
  rw [hFm _ (add_mem hmA (sum_mem fun k _ => hm1 k)) _ (sum_mem fun h _ => hm2 h),
    hFm _ hmA _ (sum_mem fun k _ => hm1 k), addMapS_sum hFm _ _ (fun k _ => hm1 k),
    addMapS_sum hFm _ _ (fun h _ => hm2 h), addMapS_sum hFm _ _ (fun h _ => hm3 h), hFΦA, hE]
    at hFM
  have e1 : ∀ k, Fm ((τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k)) =
      (τ.v r k : ZMod 3) * F (tc (T.x₂ k) (T.x₁ r) ^ T.d r) := by
    intro k
    rw [hFmΦ _ (S.x2mem k), mul_comm (τ.v r k), zpow_mul, zpow_natCast, addMap_zpow hF (S.mem2 r hr k)]
  have e2 : ∀ h, Fm (crow T τ r h • Φ (T.x₁ h ^ T.d h)) =
      F (tc (T.x₁ h ^ T.d h) (T.x₁ r) ^ crow T τ r h) := fun h => hFmΦ _ (S.Y1 h) _
  have e3 : ∀ h, Fm (crow T τ r h • Φ (oprod T.x₃ (T.c h))) =
      (crow T τ r h : ZMod 3) * F (tc (oprod T.x₃ (T.c h)) (T.x₁ r)) := by
    intro h
    rw [hFmΦ _ (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _),
      addMap_zpow hF (hc4 h)]
  simp only [e1, e2, e3] at hFM
  linear_combination hFM

/-- The row identity for a row of order `3`, evaluated. -/
theorem row3 (i : Fin T.s) (hi : T.d i = 3) {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b) :
    ∑ k, (τ.v i k : ZMod 3) * F (tc (T.x₁ i ^ T.d i) (T.x₂ k)) =
      ∑ h, (if T.d h = 3 then ((crow T τ i h / 3 : ℤ) : ZMod 3) *
          F (tc (T.x₁ h ^ T.d h) (T.x₁ i ^ T.d i)) else 0) -
      ∑ h, (if T.d h = 9 ∧ i < h then (τ.u i h : ZMod 3) *
          F (tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ h)) else 0) := by
  have hrow := S.row hτ i (Or.inl hi) hF
  have hYi : T.x₁ i ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    have := S.Y1 i; rwa [hi] at this
  have e1 : ∀ k, F (tc (T.x₂ k) (T.x₁ i) ^ T.d i) = -F (tc (T.x₁ i ^ T.d i) (T.x₂ k)) := by
    intro k
    rw [hi, ← tc_pow_three_rightA S.h5 S.h4 (S.x2mem k), ← tc_inv (T.x₁ i ^ 3) (T.x₂ k),
      addMap_inv hF (tc_mem (by omega) hYi (S.x2mem k))]
  have e2 : ∀ h, F (tc (T.x₁ h ^ T.d h) (T.x₁ i) ^ crow T τ i h) =
      (if T.d h = 3 then ((crow T τ i h / 3 : ℤ) : ZMod 3) *
          F (tc (T.x₁ h ^ T.d h) (T.x₁ i ^ T.d i)) else 0) -
      (if T.d h = 9 ∧ i < h then (τ.u i h : ZMod 3) *
          F (tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ h)) else 0) := by
    intro h
    by_cases h3 : T.d h = 3
    · obtain ⟨m, hm⟩ := S.crow3 hτ i h3
      rw [if_pos h3, if_neg (fun hc => by have := hc.1; omega), sub_zero, hm,
        show 3 * m / 3 = m by omega, zpow_mul, zpow_ofNat,
        ← tc_pow_three_rightA S.h5 S.h4 (S.Y1 h),
        show T.x₁ i ^ 3 = T.x₁ i ^ T.d i by rw [hi]]
      exact addMap_zpow hF (tc_mem (by omega) (S.Y1 h) (S.Y1 i)) _
    · rw [if_neg h3, zero_sub]
      rcases S.hd h with h3' | h9 | h27
      · exact absurd h3' h3
      · have hih : i < h := by
          rcases lt_trichotomy i h with hlt | heq | hgt
          · exact hlt
          · subst heq; omega
          · have := S.d_dvd hgt.le; rw [hi, h9] at this; norm_num at this
        have hc : crow T τ i h = τ.u i h := by
          simp [crow, hih, not_lt.mpr hih.le]
        rw [if_pos ⟨h9, hih⟩, hc, addMap_zpow hF (S.tcY_mem (by simp [h9]) _)]
        -- `F [x_h⁹, x_i] = -F [x_i⁹, x_h]`
        have hs : F (tc (T.x₁ h ^ T.d h) (T.x₁ i)) = -F (tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ h)) := by
          have hz : tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
            S.tc9_mem hi _
          have e : tc (T.x₁ h ^ T.d h) (T.x₁ i) = (tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ h))⁻¹ := by
            rw [h9, hi, ← pow_mul, show (3 * 3 : ℕ) = 9 from rfl, tc_pow_nineA S.h5 S.h4 S.h9,
              tc_pow_nineA S.h5 S.h4 S.h9, ← tc_inv, inv_pow]
          rw [e, addMap_inv hF hz]
        rw [hs]; ring
      · have h9' : ¬ T.d h = 9 := by obtain ⟨c, hc⟩ := h27; omega
        rw [if_neg (fun hc => h9' hc.1), S.tcY_one h27, one_zpow, addMap_one hF, neg_zero]
  simp only [e1, e2, Finset.sum_sub_distrib] at hrow
  simp only [mul_neg, Finset.sum_neg_distrib] at hrow
  linear_combination -hrow

/-- The row identity for a row of order `9`: `∑_{h < j, d(h) = 3} u_{hj} [x_h⁹, x_j] = 0`
(step (5)). -/
theorem row9 (j : Fin T.s) (hj : T.d j = 9) {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b) :
    ∑ h, (if T.d h = 3 ∧ h < j then (τ.u h j : ZMod 3) *
      F (tc ((T.x₁ h ^ T.d h) ^ 3) (T.x₁ j)) else 0) = 0 := by
  have hrow := S.row hτ j (Or.inr hj) hF
  have e1 : ∀ k, F (tc (T.x₂ k) (T.x₁ j) ^ T.d j) = 0 := by
    intro k
    rw [hj, tc_pow_nine_L1A S.h5 S.h9 (S.x2mem k)]; exact addMap_one hF
  have e2 : ∀ h, F (tc (T.x₁ h ^ T.d h) (T.x₁ j) ^ crow T τ j h) =
      -(if T.d h = 3 ∧ h < j then (τ.u h j : ZMod 3) *
        F (tc ((T.x₁ h ^ T.d h) ^ 3) (T.x₁ j)) else 0) := by
    intro h
    rcases S.hd h with h3 | h9 | h27
    · have hhj : h < j := by
        rcases lt_trichotomy h j with hlt | heq | hgt
        · exact hlt
        · subst heq; omega
        · have := S.d_dvd hgt.le; rw [hj, h3] at this; norm_num at this
      have hq : T.q h j = 3 := by simp [Data.q, h3, hj]
      have hc : crow T τ j h = 3 * (-τ.u h j) := by
        simp only [crow, if_neg (not_lt.mpr hhj.le), if_pos hhj, hq]; ring
      rw [if_pos ⟨h3, hhj⟩, hc, zpow_mul, zpow_ofNat, ← tc_pow_three_left S.h5 (S.Y1 h),
        addMap_zpow hF (S.tc9_mem h3 _), Int.cast_neg]
      ring
    · have hz := S.tcY_mem (i := h) (by simp [h9]) (T.x₁ j)
      have h3 : ¬ T.d h = 3 := by omega
      rw [if_neg (fun hc => h3 hc.1), neg_zero, addMap_zpow hF hz]
      have hc : (3 : ℤ) ∣ crow T τ j h := by
        unfold crow
        rcases lt_trichotomy j h with hjh | rfl | hhj
        · rw [if_pos hjh, if_neg (not_lt.mpr hjh.le), sub_zero]
          exact S.u3_eq hτ hjh (hj.trans h9.symm) (Or.inr hj)
        · simp
        · rw [if_neg (not_lt.mpr hhj.le), if_pos hhj, zero_sub, dvd_neg]
          exact S.uq3 hτ hhj (Or.inr h9)
      rw [cast3_eq_zero hc, zero_mul]
    · have h3 : ¬ T.d h = 3 := by obtain ⟨c, hc⟩ := h27; omega
      rw [if_neg (fun hc => h3 hc.1), neg_zero, S.tcY_one h27, one_zpow, addMap_one hF]
  simp only [e1, mul_zero, Finset.sum_const_zero, zero_add, e2, Finset.sum_neg_distrib] at hrow
  linear_combination -hrow

/-- The `w`-part is trivial. -/
theorem genC_eq : T.genC τ = 1 := by
  unfold Data.genC
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
  split_ifs with hijk
  · by_cases hact : act i
    · have hz : tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (i := 2) (j := 0) (by omega)
          (tc_mem (i := 1) (j := 0) (by omega) (S.Y1 i) (mem_lcs_zero _)) (mem_lcs_zero _)
      obtain ⟨w0, hw0⟩ := S.w3 hτ hact hijk.1 hijk.2
      rw [hw0, zpow_mul, zpow_ofNat, S.h4 _ hz, one_zpow]
    · rw [S.tcK hact, one_zpow]
  · rfl

/-- The factors of the `u`-part: `[x_i^{d(i)}, x_j]^{u_{ij} q_{ij}}` is
`[x_i^{d(i)}, x_j^{d(j)}]^{u_{ij}/3}` for `d(i) = d(j) = 3`, `[x_i^{3d(i)}, x_j]^{u_{ij}}` for
`d(i) = 3`, `d(j) = 9`, and `1` otherwise. -/
theorem factor (i j : Fin T.s) :
    (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1) =
      (if i < j ∧ T.d i = 3 ∧ T.d j = 3 then
        tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ^ (τ.u i j / 3) else 1) *
      (if i < j ∧ T.d i = 3 ∧ T.d j = 9 then
        tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j) ^ τ.u i j else 1) := by
  by_cases hij : i < j
  swap
  · simp only [hij, false_and, if_false, mul_one]
  rw [if_pos hij]
  have hY1i := S.Y1 i
  rcases S.hd i with hi3 | hi9 | hi27
  · rcases S.hd j with hj3 | hj9 | ⟨r, hr⟩
    · have hq : T.q i j = 1 := by simp [Data.q, hi3, hj3]
      obtain ⟨m, hm⟩ := S.u3_eq hτ hij (hi3.trans hj3.symm) (Or.inl hi3)
      rw [if_pos ⟨hij, hi3, hj3⟩, if_neg (fun h => by have := h.2.2; omega), mul_one, hq,
        mul_one, hm, show 3 * m / 3 = m by omega, zpow_mul, zpow_ofNat,
        ← tc_pow_three_rightA S.h5 S.h4 hY1i, hj3]
    · have hq : T.q i j = 3 := by simp [Data.q, hi3, hj9]
      rw [if_neg (fun h => by have := h.2.2; omega), if_pos ⟨hij, hi3, hj9⟩, one_mul, hq,
        show τ.u i j * 3 = 3 * τ.u i j by ring, zpow_mul, zpow_ofNat,
        ← tc_pow_three_left S.h5 hY1i]
    · have e : T.d j / T.d i = 9 * r := by rw [hi3, hr]; omega
      have hq : T.q i j = 9 * r := by simp [Data.q, e]
      have hj3 : T.d j ≠ 3 := by omega
      have hj9 : T.d j ≠ 9 := by omega
      rw [hq, show τ.u i j * (9 * (r : ℤ)) = 9 * (τ.u i j * r) by ring, zpow_mul, zpow_ofNat,
        tc_pow_nine_L1A S.h5 S.h9 hY1i, one_zpow]
      simp [hj3, hj9]
  · have hz : tc (T.x₁ i ^ T.d i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      S.tcY_mem (by simp [hi9]) _
    obtain ⟨r, hr⟩ := S.uq3 hτ hij (Or.inr hi9)
    rw [hr, zpow_mul, zpow_ofNat, S.h4 _ hz, one_zpow]
    have hi3 : T.d i ≠ 3 := by omega
    simp [hi3]
  · rw [S.tcY_one hi27, one_zpow]
    have hi3 : T.d i ≠ 3 := by obtain ⟨r, hr⟩ := hi27; omega
    simp [hi3]

/-- **Every generator of Tahara's Theorem 6.1 is trivial** in the situation `SetupA`. -/
theorem gen_eq_one : T.gen τ = 1 := by
  classical
  have hle34 : (⊤ : Subgroup G).lowerCentralSeries 4 ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  let A1 : Fin T.s → Fin T.s → G := fun i j =>
    if i < j ∧ T.d i = 3 ∧ T.d j = 3 then
      tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ^ (τ.u i j / 3) else 1
  let A2 : Fin T.s → Fin T.s → G := fun i j =>
    if i < j ∧ T.d i = 3 ∧ T.d j = 9 then tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j) ^ τ.u i j else 1
  have memA1 : ∀ i j, A1 i j ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i j
    simp only [A1]
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (S.Y1 i) (S.Y1 j)) _
    · exact one_mem _
  have memA2 : ∀ i j, A2 i j ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i j
    simp only [A2]
    split_ifs with h
    · exact zpow_mem (S.tc9_mem h.2.1 _) _
    · exact one_mem _
  have memB : ∀ i k, (List.ofFn fun l => if k < l then tc (T.x₂ l) (T.x₂ k) ^ T.b i l
      else 1).prod ^ τ.v i k ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i k
    refine zpow_mem (list_prod_mem fun y hy => ?_) _
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (S.x2mem l) (S.x2mem k)) _
    · exact one_mem _
  have hA : T.genA τ = (List.ofFn fun i => (List.ofFn fun j => A1 i j * A2 i j).prod).prod := by
    unfold Data.genA
    simp only [S.factor hτ, A1, A2]
  have memGA : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [hA]
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact mul_mem (memA1 i j) (memA2 i j)
  have memGB : T.genB τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    unfold Data.genB
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact memB i k
  have hgen : T.gen τ = T.genA τ * T.genB τ := by
    rw [Data.gen, S.genC_eq hτ, mul_one]
  have key : T.gen τ ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := by
    rw [hgen]
    refine mem_of_forall_F (p := 3) ((⊤ : Subgroup G).lowerCentralSeries 3)
      ((⊤ : Subgroup G).lowerCentralSeries 4) hle34
      (fun a ha b _ => commutator_mem_lcs (i := 3) (j := 0) (by omega) ha (mem_lcs_zero b))
      (fun z hz => by rw [S.h4 z hz]; exact one_mem _) (mul_mem memGA memGB) ?_
    intro F hF _
    rw [hF _ memGA _ memGB]
    -- notation
    let β : Fin T.s → Fin T.s → ZMod 3 := fun i j =>
      F (tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j))
    let β' : Fin T.s → Fin T.t → ZMod 3 := fun i k => F (tc (T.x₁ i ^ T.d i) (T.x₂ k))
    let ε : Fin T.s → Fin T.s → ZMod 3 := fun i j => F (tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j))
    let W : Fin T.s → Fin T.s → ZMod 3 := fun i j =>
      if i < j then ((τ.u i j / 3 : ℤ) : ZMod 3) else 0
    have hβskew : ∀ i j, β j i = -β i j := by
      intro i j
      have ht : tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (by omega) (S.Y1 i) (S.Y1 j)
      simp only [β]
      rw [← tc_inv, addMap_inv hF ht]
    -- the `u`-part
    have FA : F (T.genA τ) = ∑ i, ∑ j, (if T.d i = 3 ∧ T.d j = 3 then W i j * β i j else 0) +
        ∑ i, ∑ j, (if i < j ∧ T.d i = 3 ∧ T.d j = 9 then (τ.u i j : ZMod 3) * ε i j else 0) := by
      rw [hA, addMap_ofFn hF _ fun i => list_prod_mem fun y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact mul_mem (memA1 i j) (memA2 i j)]
      have e1 : ∀ i, F (List.ofFn fun j => A1 i j * A2 i j).prod =
          ∑ j, F (A1 i j) + ∑ j, F (A2 i j) := by
        intro i
        rw [addMap_ofFn hF _ fun j => mul_mem (memA1 i j) (memA2 i j), ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => hF _ (memA1 i j) _ (memA2 i j)
      simp_rw [e1]
      rw [Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [A1, W, β]
        by_cases hc : i < j ∧ T.d i = 3 ∧ T.d j = 3
        · rw [if_pos hc, if_pos ⟨hc.2.1, hc.2.2⟩, if_pos hc.1]
          exact addMap_zpow hF (tc_mem (by omega) (S.Y1 i) (S.Y1 j)) _
        · rw [if_neg hc, addMap_one hF]
          by_cases hd : T.d i = 3 ∧ T.d j = 3
          · rw [if_pos hd, if_neg (fun h => hc ⟨h, hd⟩), zero_mul]
          · rw [if_neg hd]
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [A2, ε]
        split_ifs with hc
        · exact addMap_zpow hF (S.tc9_mem hc.2.1 _) _
        · exact addMap_one hF
    -- the `v`-part: `2 F(genB) = ∑_{i,k} v_{ik} β'_{ik}`
    let γ : Fin T.t → Fin T.t → ZMod 3 := fun l k => F (tc (T.x₂ l) (T.x₂ k))
    let N : Fin T.t → Fin T.t → ZMod 3 := fun l k => ∑ i, (τ.v i k : ZMod 3) * (T.b i l : ZMod 3)
    have FB0 : F (T.genB τ) =
        ∑ i, ∑ k, (τ.v i k : ZMod 3) * ∑ l, (if k < l then (T.b i l : ZMod 3) * γ l k else 0) := by
      unfold Data.genB
      rw [addMap_ofFn hF _ fun i => list_prod_mem fun y hy => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact memB i k]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [addMap_ofFn hF _ (memB i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [addMap_zpow hF (by
        refine list_prod_mem fun y hy => ?_
        obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
        split_ifs
        · exact zpow_mem (tc_mem (by omega) (S.x2mem l) (S.x2mem k)) _
        · exact one_mem _), addMap_ofFn hF _ (fun l => by
        split_ifs
        · exact zpow_mem (tc_mem (by omega) (S.x2mem l) (S.x2mem k)) _
        · exact one_mem _)]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs
      · exact addMap_zpow hF (tc_mem (by omega) (S.x2mem l) (S.x2mem k)) _
      · exact addMap_one hF
    let T3 : Fin T.s → Fin T.t → Fin T.t → ZMod 3 := fun i k l =>
      if k < l then (τ.v i k : ZMod 3) * (T.b i l : ZMod 3) * γ l k else 0
    have FB1 : F (T.genB τ) =
        ∑ l, ∑ k, (if True ∧ True ∧ k < l then N l k * γ l k else 0) := by
      rw [FB0]
      calc _ = ∑ i, ∑ k, ∑ l, T3 i k l := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            simp only [T3]
            split_ifs <;> ring
        _ = ∑ i, ∑ l, ∑ k, T3 i k l := Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ l, ∑ i, ∑ k, T3 i k l := Finset.sum_comm
        _ = ∑ l, ∑ k, ∑ i, T3 i k l := Finset.sum_congr rfl fun l _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
            simp only [T3, N, true_and]
            by_cases hkl : k < l
            · simp only [hkl, ↓reduceIte, Finset.sum_mul]
            · simp [hkl]
    have hNd : ∀ k, N k k = 0 := by
      intro k
      have := cast3_eq_zero (dvd3_mod (hτ.F₁ k) (S.he k))
      push_cast at this
      exact this
    have hN : ∀ l k, True → True → N l k + N k l = 0 := by
      intro l k _ _
      rcases lt_trichotomy k l with hkl | rfl | hlk
      · have := cast3_eq_zero (dvd3_mod (hτ.F₂ k l hkl) (S.he k))
        push_cast at this
        exact this
      · rw [hNd, add_zero]
      · have := cast3_eq_zero (dvd3_mod (hτ.F₂ l k hlk) (S.he l))
        push_cast at this
        simp only [N]
        rw [add_comm]; exact this
    have hγ : ∀ l k, γ l k + γ k l = 0 := by
      intro l k
      have ht : tc (T.x₂ l) (T.x₂ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (by omega) (S.x2mem l) (S.x2mem k)
      have ht' : tc (T.x₂ k) (T.x₂ l) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (by omega) (S.x2mem k) (S.x2mem l)
      simp only [γ]
      rw [← tc_inv (T.x₂ k) (T.x₂ l), addMap_inv hF ht', neg_add_cancel]
    have hsk := skew_total_rel (fun _ : Fin T.t => True) (fun a b => a < b) N γ hN
      (fun k _ => hNd k) hγ (fun i j _ _ hij => lt_or_gt_of_ne hij) (fun i j h => not_lt.mpr h.le)
    have hβ' : ∀ i k, β' i k = ∑ l, (T.b i l : ZMod 3) * γ l k := by
      intro i k
      have hAk : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
          ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
          F (tc (a * b) (T.x₂ k)) = F (tc a (T.x₂ k)) + F (tc b (T.x₂ k)) := by
        intro a ha b hb
        rw [tc_mul_left_L1 S.h5 ha hb, hF _ (tc_mem (by omega) ha (S.x2mem k)) _
          (tc_mem (by omega) hb (S.x2mem k))]
      have hA0 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, F (tc a (T.x₂ k)) = 0 := by
        intro a ha
        rw [tc_L2_L1 S.h5 ha (S.x2mem k)]; exact addMap_one hF
      have hv := S.valid.hb i
      have hb1 : oprod T.x₂ (T.b i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := oprod_mem S.x2mem _
      have hc2 : oprod T.x₃ (T.c i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := oprod_mem S.x3mem _
      simp only [β', γ]
      rw [← mul_inv_cancel_left (oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i)) (T.x₁ i ^ T.d i),
        addMap_mul_mem (A := fun a => F (tc a (T.x₂ k))) (show (⊤ : Subgroup G).lowerCentralSeries 2 ≤ (⊤ : Subgroup G).lowerCentralSeries 1
          from (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)) hAk hA0
          (mul_mem hb1 (lcs_mem_of_le (by norm_num) hc2)) (lcs_mem_of_le (by norm_num) hv),
        hAk _ hb1 _ (lcs_mem_of_le (by norm_num) hc2), hA0 _ hc2, add_zero,
        addMap_oprod (A := fun a => F (tc a (T.x₂ k))) hAk S.x2mem]
    have FB : 2 * F (T.genB τ) = ∑ i, ∑ k, (τ.v i k : ZMod 3) * β' i k := by
      rw [FB1, ← hsk]
      simp only [true_and, ↓reduceIte]
      calc ∑ l, ∑ k, N l k * γ l k = ∑ l, ∑ k, ∑ i, (τ.v i k : ZMod 3) * ((T.b i l : ZMod 3) * γ l k) :=
            Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by
              simp only [N, Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ l, ∑ i, ∑ k, (τ.v i k : ZMod 3) * ((T.b i l : ZMod 3) * γ l k) :=
            Finset.sum_congr rfl fun l _ => Finset.sum_comm
        _ = ∑ i, ∑ l, ∑ k, (τ.v i k : ZMod 3) * ((T.b i l : ZMod 3) * γ l k) := Finset.sum_comm
        _ = ∑ i, ∑ k, ∑ l, (τ.v i k : ZMod 3) * ((T.b i l : ZMod 3) * γ l k) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by
              rw [hβ', Finset.mul_sum]
    -- rows of order `≥ 9` do not contribute
    have hrows : ∑ i, ∑ k, (τ.v i k : ZMod 3) * β' i k =
        ∑ i, (if T.d i = 3 then ∑ k, (τ.v i k : ZMod 3) * β' i k else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · refine Finset.sum_eq_zero fun k _ => ?_
        simp only [β']
        rw [S.tcY_L1 (S.nine_dvd_of_ne hi) (S.x2mem k), addMap_one hF, mul_zero]
    -- the rows of order `3` (step (4))
    have hcW : ∀ i h, T.d i = 3 → T.d h = 3 → ((crow T τ i h / 3 : ℤ) : ZMod 3) = W i h - W h i := by
      intro i h hi hh
      simp only [W, crow]
      rcases lt_trichotomy i h with hih | rfl | hhi
      · rw [if_pos hih, if_neg (not_lt.mpr hih.le), sub_zero, if_pos hih, if_neg (not_lt.mpr hih.le),
          sub_zero]
      · simp
      · have hq : T.q h i = 1 := by simp [Data.q, hi, hh]
        obtain ⟨m, hm⟩ := S.u3_eq hτ hhi (hh.trans hi.symm) (Or.inl hh)
        rw [if_neg (not_lt.mpr hhi.le), if_pos hhi, hq, mul_one, zero_sub, if_neg (not_lt.mpr hhi.le),
          if_pos hhi, zero_sub, hm, show -(3 * m) / 3 = -m by omega, show 3 * m / 3 = m by omega]
        exact Int.cast_neg m
    have hstep4 : ∑ i, (if T.d i = 3 then ∑ k, (τ.v i k : ZMod 3) * β' i k else 0) =
        -2 * ∑ i, ∑ j, (if T.d i = 3 ∧ T.d j = 3 then W i j * β i j else 0) -
        ∑ i, ∑ j, (if i < j ∧ T.d i = 3 ∧ T.d j = 9 then (τ.u i j : ZMod 3) * ε i j else 0) := by
      have e1 : ∀ i, (if T.d i = 3 then ∑ k, (τ.v i k : ZMod 3) * β' i k else 0) =
          ∑ h, (if T.d i = 3 ∧ T.d h = 3 then (W i h - W h i) * β h i else 0) -
          ∑ h, (if i < h ∧ T.d i = 3 ∧ T.d h = 9 then (τ.u i h : ZMod 3) * ε i h else 0) := by
        intro i
        split_ifs with hi
        · simp only [β, β', ε]
          rw [S.row3 hτ i hi hF]
          congr 1
          · refine Finset.sum_congr rfl fun h _ => ?_
            by_cases hh : T.d h = 3
            · rw [if_pos hh, if_pos ⟨hi, hh⟩, hcW i h hi hh]
            · rw [if_neg hh, if_neg (fun hc => hh hc.2)]
          · refine Finset.sum_congr rfl fun h _ => ?_
            by_cases hc : T.d h = 9 ∧ i < h
            · rw [if_pos hc, if_pos ⟨hc.2, hi, hc.1⟩]
            · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.2.2, h'.1⟩)]
        · simp [hi]
      rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_sub_distrib]
      congr 1
      have e2 : ∀ i h, (if T.d i = 3 ∧ T.d h = 3 then (W i h - W h i) * β h i else 0) =
          -(if T.d i = 3 ∧ T.d h = 3 then W i h * β i h else 0) -
          (if T.d h = 3 ∧ T.d i = 3 then W h i * β h i else 0) := by
        intro i h
        by_cases hc : T.d i = 3 ∧ T.d h = 3
        · rw [if_pos hc, if_pos hc, if_pos ⟨hc.2, hc.1⟩, hβskew h i]; ring
        · rw [if_neg hc, if_neg hc, if_neg (fun h' => hc ⟨h'.2, h'.1⟩)]; ring
      simp_rw [e2, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun i h => if T.d h = 3 ∧ T.d i = 3 then W h i * β h i else 0)]
      ring
    -- the rows of order `9` (step (5))
    have hU2 : ∑ i, ∑ j, (if i < j ∧ T.d i = 3 ∧ T.d j = 9 then (τ.u i j : ZMod 3) * ε i j else 0) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : T.d j = 9
      · refine Eq.trans (Finset.sum_congr rfl fun h _ => ?_) (S.row9 hτ j hj hF)
        simp only [ε]
        by_cases hc : h < j ∧ T.d h = 3
        · rw [if_pos ⟨hc.1, hc.2, hj⟩, if_pos ⟨hc.2, hc.1⟩]
        · rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩), if_neg (fun h' => hc ⟨h'.2, h'.1⟩)]
      · exact Finset.sum_eq_zero fun h _ => if_neg (fun h' => hj h'.2.2)
    have h2 : 2 * F (T.genA τ) + 2 * F (T.genB τ) = 0 := by
      rw [FB, hrows, hstep4, FA, hU2]
      ring
    exact zmod3_add_eq_zero h2
  rwa [S.h5, mem_bot] at key

end SetupA

/-! ## Uniqueness bases from the socle -/

/-- In a finite abelian `3`-group `A`, for any subgroup `Ker` there is a basis `y_i`
(`3^{h_i+1} y_i = 0`, `A = ⊕ ⟨y_i⟩`) whose socle vectors `3^{h_i} y_i` are adapted to `Ker`:
a combination of them in `Ker` has coefficients divisible by `3` at the vectors outside `Ker`. -/
theorem exists_socle_family {A : Type*} [AddCommGroup A] [Finite A]
    (hexp : ∀ v : A, ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0) (Ker : AddSubgroup A) :
    ∃ (n : ℕ) (y : Fin n → A) (ht : Fin n → ℕ), Monotone ht ∧
      (∀ a : Fin n → ℤ, ∑ i, a i • y i = 0 ↔ ∀ i, (3 : ℤ) ^ (ht i + 1) ∣ a i) ∧
      (∀ v : A, ∃ a : Fin n → ℤ, v = ∑ i, a i • y i) ∧
      (∀ c : Fin n → ℤ, ∑ i, c i • ((3 : ℤ) ^ ht i • y i) ∈ Ker →
        ∀ i, (3 : ℤ) ^ ht i • y i ∉ Ker → (3 : ℤ) ∣ c i) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v : A, ((3 : ℤ) ^ N) • v = 0 := by
    letI := Fintype.ofFinite A
    choose kf hkf using hexp
    refine ⟨Finset.univ.sup kf, fun v => ?_⟩
    have hle : kf v ≤ Finset.univ.sup kf := Finset.le_sup (Finset.mem_univ v)
    rw [show Finset.univ.sup kf = (Finset.univ.sup kf - kf v) + kf v by omega, pow_add, mul_smul,
      hkf, smul_zero]
  obtain ⟨W, hWmem⟩ : ∃ W : AddSubgroup A, ∀ v, v ∈ W ↔ (3 : ℕ) • v = 0 :=
    ⟨{ carrier := {v | (3 : ℕ) • v = 0}
       add_mem' := fun {u v} hu hv => by
         simp only [Set.mem_setOf_eq] at *; rw [smul_add, hu, hv, add_zero]
       zero_mem' := by simp
       neg_mem' := fun {u} hu => by
         simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hu, neg_zero] }, fun v => Iff.rfl⟩
  have hW3 : ∀ v : W, (3 : ℕ) • v = 0 := fun v => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact (hWmem _).mp v.2)
  letI : Module (ZMod 3) W := AddCommGroup.zmodModule hW3
  let H : ℕ → AddSubgroup A := fun j =>
    { carrier := {v | ∃ a, ((3 : ℤ) ^ j) • a = v}
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, smul_add _ _ _⟩
      zero_mem' := ⟨0, smul_zero _⟩
      neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, smul_neg _ _⟩ }
  let Wf : ℕ → Submodule (ZMod 3) W := fun j =>
    AddSubgroup.toZModSubmodule 3 ((H j).comap W.subtype)
  have hWf : ∀ j (w : W), w ∈ Wf j ↔ ∃ a, ((3 : ℤ) ^ j) • a = (w : A) :=
    fun _ _ => Iff.rfl
  have hWanti : Antitone Wf := by
    intro j j' hjj w hw
    obtain ⟨a, ha⟩ := (hWf j' w).mp hw
    refine (hWf j w).mpr ⟨(3 : ℤ) ^ (j' - j) • a, ?_⟩
    rw [smul_smul, ← pow_add, show j + (j' - j) = j' by omega, ha]
  have hWN : Wf N = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨a, ha⟩ := (hWf N w).mp hw
    rw [Submodule.mem_bot]
    exact Subtype.ext (by rw [← ha, hN]; rfl)
  let KerW : Submodule (ZMod 3) W := AddSubgroup.toZModSubmodule 3 (Ker.comap W.subtype)
  have hKerW : ∀ w : W, w ∈ KerW ↔ (w : A) ∈ Ker := fun _ => Iff.rfl
  obtain ⟨B, hB, -, hBj, hBK⟩ := exists_flag_ker_basis Wf hWanti hWN KerW
  have hWf0 : ∀ w : W, w ∈ Wf 0 := fun w => (hWf 0 w).mpr ⟨w, by simp⟩
  have hsp : ⊤ ≤ Submodule.span (ZMod 3) (Set.range ((↑) : B → W)) := by
    rw [Subtype.range_coe]
    intro w _
    exact Submodule.span_mono Set.inter_subset_left (hBj 0 (hWf0 w))
  let b0 : Module.Basis B (ZMod 3) W :=
    Module.Basis.mk (v := ((↑) : B → W)) hB.linearIndependent hsp
  have hb0 : ∀ β : B, b0 β = β := fun β => by simp [b0]
  have hset : ∀ S : Set W, B ∩ S = b0 '' {β : B | (β : W) ∈ S} := by
    intro S
    ext w
    constructor
    · rintro ⟨hwB, hwS⟩; exact ⟨⟨w, hwB⟩, hwS, hb0 _⟩
    · rintro ⟨β, hβ, rfl⟩; rw [hb0]; exact ⟨β.2, hβ⟩
  haveI : Finite B := Module.Finite.finite_basis b0
  letI := Fintype.ofFinite B
  let eqv : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let htw : W → ℕ := fun w => Nat.findGreatest (fun j => (w : A) ∈ H j) N
  let ht0 : Fin (Fintype.card B) → ℕ := fun i => htw (eqv.symm i)
  let π := Tuple.sort ht0
  let e : Module.Basis (Fin (Fintype.card B)) (ZMod 3) W := b0.reindex (eqv.trans π.symm)
  let ht : Fin (Fintype.card B) → ℕ := fun i => ht0 (π i)
  have hmono : Monotone ht := Tuple.monotone_sort ht0
  have he : ∀ i, e i = (eqv.symm (π i) : W) := fun i => by
    simp only [e, Module.Basis.reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm, hb0]
  have hrepr : ∀ (v : W) i, e.repr v i = b0.repr v (eqv.symm (π i)) := fun v i => by
    simp only [e, Module.Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  have hE1 : ∀ i, ∃ a : A, ((3 : ℤ) ^ ht i) • a = (e i : A) := by
    intro i
    rw [he i]
    exact Nat.findGreatest_spec (P := fun j => ((eqv.symm (π i) : W) : A) ∈ H j)
      (Nat.zero_le N) ⟨((eqv.symm (π i) : W) : A), by simp⟩
  have hE2 : ∀ j (v : W), v ∈ Wf j → ∀ i, e.repr v i ≠ 0 → j ≤ ht i := by
    intro j v hv i hi
    have hsub := hBj j hv
    rw [hset] at hsub
    have hmem : eqv.symm (π i) ∈ {β : B | (β : W) ∈ Wf j} := by
      apply (b0.mem_span_image.mp hsub)
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hrepr]
      exact hi
    have hHj := (hWf j _).mp hmem
    by_cases hjN : j ≤ N
    · exact Nat.le_findGreatest hjN hHj
    · exfalso
      obtain ⟨a, ha⟩ := hHj
      have h0 : ((eqv.symm (π i) : B) : W) = 0 := Subtype.ext (by
        rw [← ha, show j = (j - N) + N by omega, pow_add, mul_comm, mul_smul, hN]; try rfl)
      exact b0.ne_zero (eqv.symm (π i)) (by rw [hb0]; exact h0)
  have hE3 : ∀ v : W, v ∈ KerW → ∀ i, e.repr v i ≠ 0 → e i ∈ KerW := by
    intro v hv i hi
    have hsub := hBK (Submodule.mem_inf.mpr ⟨hWf0 v, hv⟩)
    rw [hset] at hsub
    have hmem : eqv.symm (π i) ∈ {β : B | (β : W) ∈ KerW} := by
      apply (b0.mem_span_image.mp hsub)
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hrepr]
      exact hi
    rw [he i]
    exact hmem
  choose a0 ha0 using hE1
  have hord : ∀ i, ((3 : ℤ) ^ (ht i + 1)) • a0 i = 0 := by
    intro i
    rw [pow_succ', mul_smul, ha0 i]
    have := (hWmem _).mp (e i).2
    rw [← natCast_zsmul] at this
    exact_mod_cast this
  have hind : ∀ c : Fin (Fintype.card B) → ℤ,
      ∑ i, c i • ((3 : ℤ) ^ ht i • a0 i) = 0 → ∀ i, (3 : ℤ) ∣ c i := by
    intro c hc
    exact basis_indep' W e c (by simpa only [ha0] using hc)
  have hflag : ∀ (j : ℕ) (v : A), (3 : ℤ) • v = 0 → (∃ a, ((3 : ℤ) ^ j) • a = v) →
      ∃ c : Fin (Fintype.card B) → ℤ, v = ∑ i, c i • ((3 : ℤ) ^ ht i • a0 i) ∧
        ∀ i, ht i < j → c i = 0 := by
    intro j v hv3 hvj
    have hvW : v ∈ W := (hWmem v).mpr (by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, natCast_zsmul] at hv3; exact hv3)
    refine ⟨fun i => ((e.repr ⟨v, hvW⟩ i).val : ℤ),
      (basis_coords' W e v hvW).trans (Finset.sum_congr rfl fun i _ => by rw [ha0 i]),
      fun i hi => ?_⟩
    by_contra hne
    have hne' : e.repr ⟨v, hvW⟩ i ≠ 0 := fun h0 => hne (by simp [h0])
    have := hE2 j ⟨v, hvW⟩ ((hWf j _).mpr hvj) i hne'
    omega
  obtain ⟨h1, h2⟩ := socle_basis a0 ht hord hind hflag hexp
  refine ⟨Fintype.card B, a0, ht, hmono, h1, h2, fun c hc i hi => ?_⟩
  have hvW : ∑ j, c j • ((3 : ℤ) ^ ht j • a0 j) ∈ W := by
    rw [hWmem, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_comm, ha0 j, (hWmem _).mp (e j).2, smul_zero]
  have hv_eq : (⟨_, hvW⟩ : W) = ∑ j, ((c j : ℤ) : ZMod 3) • e j := by
    apply W.subtype_injective
    rw [map_sum]
    show (∑ j, c j • ((3 : ℤ) ^ ht j • a0 j)) = ∑ j, W.subtype (((c j : ℤ) : ZMod 3) • e j)
    simp only [Int.cast_smul_eq_zsmul, map_zsmul, AddSubgroup.coe_subtype, ha0]
  have hrep : e.repr ⟨_, hvW⟩ i = ((c i : ℤ) : ZMod 3) := by
    rw [hv_eq, Module.Basis.repr_sum_self]
  by_contra hne
  have hne' : e.repr ⟨_, hvW⟩ i ≠ 0 := by
    rw [hrep]
    intro h0
    exact hne (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0)
  have := hE3 _ ((hKerW _).mpr hc) i hne'
  rw [hKerW, ← ha0 i] at this
  exact hi this

/-- The lift of a socle basis as in `socle_basis` is a uniqueness basis of the layer
`γ_{k+1}/γ_{k+2}`. -/
theorem isLayerBasis_of_socle {k n : ℕ} (x : Fin n → G)
    (hx : ∀ i, x i ∈ (⊤ : Subgroup G).lowerCentralSeries k) (ht : Fin n → ℕ) (hmono : Monotone ht)
    (hb : (∀ a : Fin n → ℤ, ∑ i, a i • cl G k (x i) = 0 ↔ ∀ i, (3 : ℤ) ^ (ht i + 1) ∣ a i) ∧
      ∀ v, ∃ a : Fin n → ℤ, v = ∑ i, a i • cl G k (x i)) :
    IsLayerBasis k x (fun i => 3 ^ (ht i + 1)) := by
  refine ⟨hx, fun i => Nat.one_lt_pow (by omega) (by norm_num),
    fun i j hij => Nat.pow_dvd_pow 3 (by have := hmono hij; omega), fun a => ?_, fun g hg => ?_⟩
  · rw [← cl_eq_zero_iff (oprod_mem hx a), cl_oprod hx, hb.1]
    exact ⟨fun h i => by exact_mod_cast h i, fun h i => by exact_mod_cast h i⟩
  · obtain ⟨a, ha⟩ := hb.2 (cl G k g)
    refine ⟨a, ?_⟩
    rw [← cl_eq_cl (oprod_mem hx a) hg, cl_oprod hx, ← ha]

/-- A uniqueness basis of a layer that is a finite `3`-group, with normal forms in range, the
orders `3^{h_i+1}`, and socle vectors adapted to a given subgroup `Ker` of the layer. -/
theorem exists_layer_basis (k : ℕ) [Finite (Additive (Layer G k))]
    (hexp : ∀ v : Additive (Layer G k), ∃ m : ℕ, ((3 : ℤ) ^ m) • v = 0)
    (Ker : AddSubgroup (Additive (Layer G k))) :
    ∃ (n : ℕ) (x : Fin n → G) (ht : Fin n → ℕ),
      IsLayerBasis k x (fun i => 3 ^ (ht i + 1)) ∧
      (∀ i, x i ^ (3 ^ (ht i + 1)) ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1)) ∧
      (∀ g ∈ (⊤ : Subgroup G).lowerCentralSeries k, ∃ a : Fin n → ℤ,
        (∀ i, 0 ≤ a i ∧ a i < ((3 ^ (ht i + 1) : ℕ) : ℤ)) ∧
        (oprod x a)⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1)) ∧
      (∀ c : Fin n → ℤ, ∑ i, c i • cl G k (x i ^ (3 ^ ht i)) ∈ Ker →
        ∀ i, cl G k (x i ^ (3 ^ ht i)) ∉ Ker → (3 : ℤ) ∣ c i) := by
  classical
  obtain ⟨n, y, ht, hmono, hb1, hb2, hK⟩ := exists_socle_family hexp Ker
  choose x hx using fun i => cl_surj (G := G) k (y i)
  have hxk : ∀ i, x i ∈ (⊤ : Subgroup G).lowerCentralSeries k := fun i => (hx i).1
  have hxy : ∀ i, cl G k (x i) = y i := fun i => (hx i).2
  have hnp : ∀ i (m : ℕ), cl G k (x i ^ m) = (m : ℤ) • y i := by
    intro i m
    rw [← zpow_natCast, cl_zpow (hxk i), hxy]
  have hb : (∀ a : Fin n → ℤ, ∑ i, a i • cl G k (x i) = 0 ↔ ∀ i, (3 : ℤ) ^ (ht i + 1) ∣ a i) ∧
      ∀ v, ∃ a : Fin n → ℤ, v = ∑ i, a i • cl G k (x i) := by
    simp only [hxy]; exact ⟨hb1, hb2⟩
  refine ⟨n, x, ht, isLayerBasis_of_socle x hxk ht hmono hb, fun i => ?_, fun g hg => ?_,
    fun c hc i hi => ?_⟩
  · rw [← cl_eq_zero_iff (pow_mem (hxk i) _), hnp]
    have := (hb1 (fun j => if j = i then (3 : ℤ) ^ (ht i + 1) else 0)).mpr (fun j => by
      split_ifs with h
      · subst h; exact dvd_refl _
      · exact dvd_zero _)
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at this
    push_cast
    exact this
  · obtain ⟨a, ha⟩ := hb2 (cl G k g)
    let a' : Fin n → ℤ := fun i => a i % ((3 ^ (ht i + 1) : ℕ) : ℤ)
    have hpos : ∀ i, (0 : ℤ) < ((3 ^ (ht i + 1) : ℕ) : ℤ) := fun i => by positivity
    refine ⟨a', fun i => ⟨Int.emod_nonneg _ (hpos i).ne', Int.emod_lt_of_pos _ (hpos i)⟩, ?_⟩
    have hdiff : ∑ i, (a i - a' i) • y i = 0 := by
      rw [hb1]
      intro i
      have : (3 : ℤ) ^ (ht i + 1) = ((3 ^ (ht i + 1) : ℕ) : ℤ) := by norm_cast
      rw [this]
      exact ⟨a i / ((3 ^ (ht i + 1) : ℕ) : ℤ), by simp only [a']; rw [Int.emod_def]; ring⟩
    rw [← cl_eq_cl (oprod_mem hxk a') hg, cl_oprod hxk, ha]
    simp only [hxy]
    rw [eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    simpa only [sub_smul] using hdiff
  · have e : ∀ j, cl G k (x j ^ (3 ^ ht j)) = (3 : ℤ) ^ ht j • y j := by
      intro j; rw [hnp]; norm_num
    simp only [e] at hc hi
    exact hK c hc i hi

/-! ## The theorem for finite groups of class `≤ 4` -/

/-- **Theorem 6.10, finite case, modulo Tahara.** Let `Q` be a finite group of class `≤ 4` such
that `Q/γ₂(Q)` is a `3`-group, `γ₄(Q)` has exponent dividing `3` and `a⁹ ∈ γ₄` for `a ∈ γ₂`.
Then `D₅(Q) = 1`. -/
theorem D_five_eq_bot_of_class_four_g4_cube_g2_nine (hT : TaharaFiveOne) {Q : Type} [Group Q]
    [Finite Q] (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (h3grp : ∀ x : Q, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1)
    (h4 : ∀ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 3, c ^ 3 = 1)
    (h9 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 1, a ^ 9 ∈ (⊤ : Subgroup Q).lowerCentralSeries 3) :
    D 5 Q = ⊥ := by
  classical
  have hcl_pow : ∀ (g : Q) (k : ℕ),
      (k • cl Q 0 g = 0 ↔ g ^ k ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) := by
    intro g k
    rw [← natCast_zsmul, ← cl_zpow (mem_lcs_zero g), zpow_natCast, cl_eq_zero_iff (mem_lcs_zero _)]
  have hexp0 : ∀ v : Additive (Layer Q 0), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, -, rfl⟩ := cl_surj (G := Q) 0 v
    obtain ⟨k, hk⟩ := h3grp g
    refine ⟨k, ?_⟩
    rw [show ((3 : ℤ) ^ k) = ((3 ^ k : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul]
    exact (hcl_pow g _).mpr hk
  have hexp1 : ∀ v : Additive (Layer Q 1), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 1 v
    refine ⟨2, ?_⟩
    rw [← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _),
      show ((3 : ℤ) ^ 2) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact lcs_mem_of_le (by norm_num) (h9 g hg)
  have hexp2 : ∀ v : Additive (Layer Q 2), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 2 v
    refine ⟨2, ?_⟩
    rw [← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _),
      show ((3 : ℤ) ^ 2) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_nine_L2A h5 h9 hg]
    exact one_mem _
  -- the cube map `Ω₁(Q/γ₂) → L₂/3L₂` and its kernel
  choose L0 hL0 using fun v : Additive (Layer Q 0) => cl_surj (G := Q) 0 v
  let T3 : AddSubgroup (Additive (Layer Q 1)) :=
    { carrier := {v | ∃ w, (3 : ℤ) • w = v}
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, smul_add _ _ _⟩
      zero_mem' := ⟨0, smul_zero _⟩
      neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, smul_neg _ _⟩ }
  have hT3 : ∀ w, (3 : ℤ) • w ∈ T3 := fun w => ⟨w, rfl⟩
  have hmemW : ∀ x : Q, (3 : ℕ) • cl Q 0 x = 0 → x ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
    fun x h => (hcl_pow x 3).mp h
  have hwd : ∀ x y : Q, (3 : ℕ) • cl Q 0 x = 0 → cl Q 0 x = cl Q 0 y →
      cl Q 1 (y ^ 3) - cl Q 1 (x ^ 3) ∈ T3 := by
    intro x y hx hxy
    have hm : x⁻¹ * y ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
      (cl_eq_cl (mem_lcs_zero _) (mem_lcs_zero _)).mp hxy
    obtain ⟨-, he⟩ := cl_cube_mul (hmemW x hx) (pow_mem hm 3)
    rw [mul_inv_cancel_left] at he
    rw [he, cl_pow3 hm]
    have : cl Q 1 (x ^ 3) + (3 : ℤ) • cl Q 1 (x⁻¹ * y) + (3 : ℤ) • cl Q 1 (tc (x⁻¹ * y) x) -
        cl Q 1 (x ^ 3) = (3 : ℤ) • (cl Q 1 (x⁻¹ * y) + cl Q 1 (tc (x⁻¹ * y) x)) := by
      rw [smul_add]; abel
    rw [this]; exact hT3 _
  have hL0W : ∀ v : Additive (Layer Q 0), (3 : ℕ) • v = 0 → (3 : ℕ) • cl Q 0 (L0 v) = 0 :=
    fun v hv => by rw [(hL0 v).2]; exact hv
  let Ker0 : AddSubgroup (Additive (Layer Q 0)) :=
    { carrier := {v | (3 : ℕ) • v = 0 ∧ cl Q 1 (L0 v ^ 3) ∈ T3}
      zero_mem' := by
        refine ⟨smul_zero _, ?_⟩
        have h0 : L0 0 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
          (cl_eq_zero_iff (mem_lcs_zero _)).mp (hL0 0).2
        rw [cl_pow3 h0]; exact hT3 _
      add_mem' := by
        rintro u v ⟨hu3, hu⟩ ⟨hv3, hv⟩
        refine ⟨by rw [smul_add, hu3, hv3, add_zero], ?_⟩
        have hg : cl Q 0 (L0 u * L0 v) = u + v := by
          rw [cl_mul (mem_lcs_zero _) (mem_lcs_zero _), (hL0 u).2, (hL0 v).2]
        have hg3 : (3 : ℕ) • cl Q 0 (L0 u * L0 v) = 0 := by rw [hg, smul_add, hu3, hv3, add_zero]
        have h1 := hwd _ _ hg3 (hg.trans (hL0 (u + v)).2.symm)
        obtain ⟨-, he⟩ := cl_cube_mul (hmemW _ (hL0W u hu3)) (hmemW _ (hL0W v hv3))
        have : cl Q 1 (L0 (u + v) ^ 3) = (cl Q 1 (L0 (u + v) ^ 3) - cl Q 1 ((L0 u * L0 v) ^ 3)) +
            (cl Q 1 (L0 u ^ 3) + cl Q 1 (L0 v ^ 3) + (3 : ℤ) • cl Q 1 (tc (L0 v) (L0 u))) := by
          rw [← he]; abel
        rw [this]
        exact add_mem h1 (add_mem (add_mem hu hv) (hT3 _))
      neg_mem' := by
        rintro v ⟨hv3, hv⟩
        refine ⟨by rw [smul_neg, hv3, neg_zero], ?_⟩
        have hg : cl Q 0 (L0 v)⁻¹ = -v := by rw [cl_inv (mem_lcs_zero _), (hL0 v).2]
        have hg3 : (3 : ℕ) • cl Q 0 (L0 v)⁻¹ = 0 := by rw [hg, smul_neg, hv3, neg_zero]
        have h1 := hwd _ _ hg3 (hg.trans (hL0 (-v)).2.symm)
        have hv1 := hmemW _ (hL0W v hv3)
        have hinv : cl Q 1 ((L0 v)⁻¹ ^ 3) = -cl Q 1 (L0 v ^ 3) := by
          rw [inv_pow, cl_inv hv1]
        have : cl Q 1 (L0 (-v) ^ 3) = (cl Q 1 (L0 (-v) ^ 3) - cl Q 1 ((L0 v)⁻¹ ^ 3)) +
            -cl Q 1 (L0 v ^ 3) := by rw [← hinv]; abel
        rw [this]
        exact add_mem h1 (neg_mem hv) }
  -- the three uniqueness bases
  obtain ⟨s, x1, ht, B1, hpow1, -, hKer⟩ := exists_layer_basis (G := Q) 0 hexp0 Ker0
  obtain ⟨t, x2, ht2, B2, hpow2, nf2, -⟩ := exists_layer_basis (G := Q) 1 hexp1 ⊥
  obtain ⟨u, x3, ht3, B3, -, nf3, -⟩ := exists_layer_basis (G := Q) 2 hexp2 ⊥
  have hY1 : ∀ i, x1 i ^ (3 ^ (ht i + 1)) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := hpow1
  -- the structure constants
  choose b hbr hbm using fun i => nf2 _ (hY1 i)
  have hrem : ∀ i, (oprod x2 (b i))⁻¹ * x1 i ^ (3 ^ (ht i + 1)) ∈
      (⊤ : Subgroup Q).lowerCentralSeries 2 := hbm
  choose c hcr hcm using fun i => nf3 _ (hrem i)
  have hx2e : ∀ k, x2 k ^ (3 ^ (ht2 k + 1)) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := hpow2
  choose dd hddr hddm using fun k => nf3 _ (hx2e k)
  have hαm : ∀ g h, tc (x1 g ^ (3 ^ (ht g + 1))) (x1 h) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 :=
    fun g h => tc_mem (i := 1) (j := 0) (by omega) (hY1 g) (mem_lcs_zero (x1 h))
  choose α hαr hαm' using fun g h => nf3 _ (hαm g h)
  let T : Tahara.Data Q :=
    { s := s, t := t, u := u, x₁ := x1, d := fun i => 3 ^ (ht i + 1), x₂ := x2,
      e := fun k => 3 ^ (ht2 k + 1), x₃ := x3, f := fun l => 3 ^ (ht3 l + 1),
      b := b, c := c, dd := dd, α := α }
  have hvalid : T.Valid := by
    refine ⟨B1, B2, B3, fun i k => hbr i k, fun i l => hcr i l, fun k l => hddr k l,
      fun g h l _ => hαr g h l, fun i => ?_, fun k => hddm k, fun g h _ => hαm' g h⟩
    show (oprod x2 (b i) * oprod x3 (c i))⁻¹ * x1 i ^ (3 ^ (ht i + 1)) ∈ _
    rw [mul_inv_rev, mul_assoc]
    exact hcm i
  have hd : ∀ i, T.d i = 3 ∨ T.d i = 9 ∨ 27 ∣ T.d i := by
    intro i
    show 3 ^ (ht i + 1) = 3 ∨ 3 ^ (ht i + 1) = 9 ∨ 27 ∣ 3 ^ (ht i + 1)
    rcases Nat.lt_or_ge (ht i) 2 with h | h
    · interval_cases (ht i) <;> simp
    · right; right
      exact ⟨3 ^ (ht i - 2), by rw [show (27 : ℕ) = 3 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
  let act : Fin s → Prop := fun i => ¬ ∃ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, x1 i ^ (3 ^ (ht i + 1)) = a ^ 3 * c
  -- the socle vectors `z_i = 3^{h_i} x̄_i`, with `z_i ∈ Ker0` exactly for the inactive `i`
  have hz3 : ∀ i, (3 : ℕ) • cl Q 0 (x1 i ^ (3 ^ ht i)) = 0 := by
    intro i
    rw [← natCast_zsmul, ← cl_zpow (mem_lcs_zero _), zpow_natCast, ← pow_mul, ← pow_succ,
      cl_eq_zero_iff (mem_lcs_zero _)]
    exact hY1 i
  have hcube : ∀ i, (x1 i ^ (3 ^ ht i)) ^ 3 = x1 i ^ (3 ^ (ht i + 1)) := fun i => by
    rw [← pow_mul, ← pow_succ]
  have hnotK : ∀ i, act i → cl Q 0 (x1 i ^ (3 ^ ht i)) ∉ Ker0 := by
    intro i hi hK
    apply hi
    obtain ⟨-, hT⟩ := hK
    have h1 := hwd _ _ (hL0W _ (hz3 i)) (hL0 _).2
    rw [hcube] at h1
    obtain ⟨w, hw⟩ := add_mem h1 hT
    rw [sub_add_cancel] at hw
    obtain ⟨a, ha, rfl⟩ := cl_surj (G := Q) 1 w
    rw [← cl_pow3 ha] at hw
    refine ⟨a, ha, (a ^ 3)⁻¹ * x1 i ^ (3 ^ (ht i + 1)),
      (cl_eq_cl (pow_mem ha 3) (hY1 i)).mp hw, by group⟩
  -- the cube of a product of the `z_i`
  have hprod : ∀ l : List Q, (∀ w ∈ l, w ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) →
      l.prod ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 ∧
      cl Q 1 (l.prod ^ 3) - (l.map fun w => cl Q 1 (w ^ 3)).sum ∈ T3 := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.prod_nil, one_pow, List.map_nil, List.sum_nil, sub_zero]
      exact ⟨one_mem _, by rw [cl_one]; exact zero_mem _⟩
    | cons w l ih =>
      intro hl
      obtain ⟨hl3, hlT⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
      obtain ⟨hm, he⟩ := cl_cube_mul (hl w List.mem_cons_self) hl3
      refine ⟨by rw [List.prod_cons]; exact hm, ?_⟩
      rw [List.prod_cons, he, List.map_cons, List.sum_cons]
      have : cl Q 1 (w ^ 3) + cl Q 1 (l.prod ^ 3) + (3 : ℤ) • cl Q 1 (tc l.prod w) -
          (cl Q 1 (w ^ 3) + (l.map fun w => cl Q 1 (w ^ 3)).sum) =
          (cl Q 1 (l.prod ^ 3) - (l.map fun w => cl Q 1 (w ^ 3)).sum) +
            (3 : ℤ) • cl Q 1 (tc l.prod w) := by abel
      rw [this]
      exact add_mem hlT (hT3 _)
  have hind : ∀ cf : Fin s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h := by
    intro cf hcf h hh
    refine hKer cf ?_ h (hnotK h hh)
    -- `∑ cf_i z_i ∈ Ker0`
    let z : Fin s → Q := fun i => x1 i ^ (3 ^ ht i)
    have e3 : ∀ i, (z i ^ cf i) ^ 3 = (z i ^ 3) ^ cf i := fun i => by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hz1 : ∀ i, (z i ^ cf i) ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := fun i => by
      rw [e3]
      exact zpow_mem (hmemW _ (hz3 i)) _
    have hcl : cl Q 0 (oprod z cf) = ∑ i, cf i • cl Q 0 (x1 i ^ (3 ^ ht i)) :=
      cl_oprod (fun i => mem_lcs_zero _) cf
    have hsum3 : (3 : ℕ) • ∑ i, cf i • cl Q 0 (x1 i ^ (3 ^ ht i)) = 0 := by
      rw [Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_comm, hz3 i, smul_zero]
    refine ⟨hsum3, ?_⟩
    have hwd' := hwd _ _ (by rw [hcl]; exact hsum3) (hcl.trans (hL0 _).2.symm)
    have hP := hprod (List.ofFn fun i => z i ^ cf i) (fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw; exact hz1 i)
    have hsumY : (List.map (fun w => cl Q 1 (w ^ 3)) (List.ofFn fun i => z i ^ cf i)).sum =
        ∑ i, cf i • cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) := by
      rw [List.map_ofFn, List.sum_ofFn]
      refine Finset.sum_congr rfl fun i _ => ?_
      show cl Q 1 ((z i ^ cf i) ^ 3) = _
      rw [e3 i, cl_zpow (hmemW _ (hz3 i)), show z i ^ 3 = x1 i ^ (3 ^ (ht i + 1)) from hcube i]
    have hYb : ∀ i, cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) = ∑ k, b i k • cl Q 1 (x2 k) := by
      intro i
      rw [← cl_oprod (k := 1) (y := x2) (fun k => B2.mem k) (b i)]
      exact ((cl_eq_cl (oprod_mem (fun k => B2.mem k) _) (hY1 i)).mpr (hrem i)).symm
    have hT : ∑ i, cf i • cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) ∈ T3 := by
      simp_rw [hYb, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      refine sum_mem fun k _ => ?_
      obtain ⟨m, hm⟩ := hcf k
      rw [hm, mul_smul]
      exact hT3 _
    have hS : (List.map (fun w => cl Q 1 (w ^ 3)) (List.ofFn fun i => z i ^ cf i)).sum ∈ T3 := by
      rw [hsumY]; exact hT
    have hP2 : cl Q 1 ((oprod z cf) ^ 3) ∈ T3 := by
      have := add_mem hP.2 hS
      rwa [sub_add_cancel] at this
    have := add_mem hwd' hP2
    rwa [sub_add_cancel] at this
  have S : SetupA T act :=
    ⟨h5, h4, h9, hvalid, hd, fun k => dvd_pow_self 3 (Nat.succ_ne_zero _),
      fun l => dvd_pow_self 3 (Nat.succ_ne_zero _), fun i hi => not_not.mp hi, hind⟩
  have hle := hT Q h5 T hvalid
  rw [eq_bot_iff]
  refine hle.trans ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨τ, hτ, rfl⟩
  rw [SetLike.mem_coe, S.gen_eq_one hτ]
  exact one_mem _

/-- **Theorem 6.10, modulo Tahara's Theorem 6.1** (MATH-444). Let `G/γ₂(G)` be a finite
`3`-group with `γ₄(G)³ ⊆ γ₅(G)` and `γ₂(G)⁹ ⊆ γ₄(G)`. Then `D₅(G) = γ₅(G)`. -/
theorem D_five_eq_gamma_five_g4_cube_g2_nine (hT : TaharaFiveOne) (G : Type) [Group G]
    (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (h3grp : ∀ x : G, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h4 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 3, c ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 4)
    (h9 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 9 ∈ (⊤ : Subgroup G).lowerCentralSeries 3) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 := by
  refine le_antisymm (D_le_of_D_quotient_eq_bot _ 5 ?_) (gamma_le_D G 5 (by norm_num))
  haveI : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4) := finite_quotient_lcs hfin 3
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries 4)
  have hmap : ∀ (k : ℕ) (y : G), y ∈ (⊤ : Subgroup G).lowerCentralSeries k →
      π y ∈ (⊤ : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4)).lowerCentralSeries k :=
    fun k y hy => by rw [← lcs_map_mk]; exact Subgroup.mem_map_of_mem _ hy
  refine D_five_eq_bot_of_class_four_g4_cube_g2_nine hT (lowerCentralSeries_quotient_eq_bot 4)
    (fun x => ?_) (fun c hc => ?_) (fun a ha => ?_)
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⊤ : Subgroup G).lowerCentralSeries 4) x
    obtain ⟨k, hk⟩ := h3grp x
    exact ⟨k, by rw [← map_pow]; exact hmap 1 _ hk⟩
  · rw [← lcs_map_mk] at hc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (h4 y hy)
  · rw [← lcs_map_mk] at ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow]
    exact hmap 3 _ (h9 y hy)

end ExpThree

end GroupDimension
