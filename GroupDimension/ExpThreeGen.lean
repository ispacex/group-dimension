module

public import GroupDimension.ExpThreePlus

@[expose] public section

/-!
# `D₅ = γ₅` when `γ₂/γ₃` has exponent `3`, for any invariants of `G/γ₂` (Theorem 6.9, MATH-443)

**Theorem 6.9** of the paper (`D_five_eq_gamma_five_exp_L1`): if `G/γ₂(G)` is a finite `3`-group and
`γ₂(G)/γ₃(G)` has exponent dividing `3` (hypothesis `h2`: `a³ ∈ γ₃` for `a ∈ γ₂`;
equivalently `[x³, y] ∈ γ₃` for all `x, y`, `cube_L1_of_comm_cube`), then `D₅(G) = γ₅(G)`.
There is no restriction on the invariants of `G/γ₂`. The proof takes Tahara's Theorem 6.1
(`TaharaFiveOne`) as an explicit hypothesis, discharged in `TaharaTheorem.lean`
(`D_five_eq_gamma_five_of_exp_L1_three`). It follows the wiki page 886 (MATH-443, §3, checked by
the review in comment 7634):

* the identities of `ExpThreePlus.lean` (Lemma 3 of wiki 693) need only `h5` and `h2`;
  added here: `[x^{9k}, y] ∈ γ₄`, `[x^{27k}, y] = 1` (`tc_pow_nine_mul_mem`, `tc_pow_27_mul`);
* the uniqueness basis of `G/γ₂` (`d(i) = 3^{h_i+1}`) comes from a basis of the `3`-torsion
  `Ω₁(G/γ₂)` adapted at once to the height filtration `Ω₁ ∩ 3^j(G/γ₂)` and to the kernel `K` of
  the cube map `Ω₁ → γ₂/γ₃` (`exists_flag_ker_basis`); lifting it gives a uniqueness basis
  (`socle_basis`, `isLayerBasis_zero_of_socle`). The indices split into the *active* ones
  (`z_i ∉ K`, then `x_i^{d(i)}` is a basis vector of `γ₂/γ₃`) and the others (`x_i^{d(i)} ∈ γ₃`);
* the computation (`SetupGen.gen_eq_one`): for `d(i) ≥ 9` the active `x_i^{d(i)}` commute with
  `γ₂`; the pairing of the active indices of order `3` gives `−∑ u_{ij}[x_i⁹, x_j]` over the
  inactive `j` of order `9`, and the row `j` of condition (E), together with the row `j` of (B),
  kills this sum for each such `j`.

Theorems 6.6 and 6.8 (`D_five_eq_gamma_five`, `D_five_eq_gamma_five_cyclic`) are special cases:
their hypotheses give `h2` (`cube_succ`, `cube_L1_of_cubes`), see
`D_five_eq_gamma_five_of_exp_three_of_exp_L1` and `D_five_eq_gamma_five_cyclic_of_exp_L1`.
-/

namespace GroupDimension

namespace ExpThree

open Subgroup Tahara ClassFour
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Identities and the hypothesis `[x³, y] ∈ γ₃` -/

section Identities

variable (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
  (h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
include h5 h2

/-- `[x^{9k}, y] ∈ γ₄`. -/
theorem tc_pow_nine_mul_mem (x y : G) (k : ℕ) :
    tc (x ^ (9 * k)) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  rw [show 9 * k = k * 9 from mul_comm 9 k, pow_mul, tc_pow_nine' h5 h2]
  have hc : tc (x ^ k) y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero _) (mem_lcs_zero y)
  rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]
  exact cube_L2 h2 _ (h2 _ hc)

/-- `[x^{27k}, y] = 1`. -/
theorem tc_pow_27_mul (x y : G) (k : ℕ) : tc (x ^ (27 * k)) y = 1 := by
  rw [show 27 * k = k * 27 from mul_comm 27 k, pow_mul]
  exact tc_pow_27 h5 h2 _ y

end Identities

/-- `γ₂/γ₃` has exponent `3` as soon as `[x³, y] ∈ γ₃` for all `x, y` (the two are equivalent,
since `[x, y]³ ≡ [x³, y]` modulo `γ₃`). -/
theorem cube_L1_of_comm_cube (h : ∀ x y : G, ⁅x ^ 3, y⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  have hgen : ∀ x y : G, ⁅x, y⁆ ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    intro x y
    have hm := comm_pow_left_mod (k := 0) (mem_lcs_zero x) y 3
    have e : ⁅x, y⁆ ^ 3 = ⁅x ^ 3, y⁆ * ((⁅x, y⁆ ^ 3)⁻¹ * ⁅x ^ 3, y⁆)⁻¹ := by group
    rw [e]
    exact mul_mem (h x y) (inv_mem hm)
  -- the elements of `γ₂` with cube in `γ₃` form a subgroup
  let S : Subgroup G :=
    { carrier := {a | a ∈ (⊤ : Subgroup G).lowerCentralSeries 1 ∧
        a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2}
      one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have h' := pow_mul_mod (N := (⊤ : Subgroup G).lowerCentralSeries 2)
          (commutator_mem_lcs (i := 1) (j := 0) (by omega) ha (mem_lcs_zero b)) 3
        have := mul_mem (mul_mem ha3 hb3) h'
        rwa [mul_inv_cancel_left] at this
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        exact ⟨inv_mem ha, by rw [inv_pow]; exact inv_mem ha3⟩ }
  have hle : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ S := by
    show ⁅(⊤ : Subgroup G).lowerCentralSeries 0, ⊤⁆ ≤ S
    rw [commutator_le]
    intro c _ g _
    exact ⟨commutator_mem_lcs (by omega) (mem_lcs_zero c) (mem_lcs_zero g), hgen c g⟩
  exact fun a ha => (hle ha).2

/-- The pairing identity for skew-symmetric data, for any strict total order `r` on `P`:
`∑_{i,j ∈ P} M_{ij} β_{ij} = 2 ∑_{j r i} M_{ij} β_{ij}`. -/
theorem skew_total_rel {s : ℕ} (P : Fin s → Prop) [DecidablePred P]
    (r : Fin s → Fin s → Prop) [DecidableRel r] (M β : Fin s → Fin s → ZMod 3)
    (hM : ∀ i j, P i → P j → M i j + M j i = 0) (hMd : ∀ i, P i → M i i = 0)
    (hβ : ∀ i j, β i j + β j i = 0)
    (htri : ∀ i j, P i → P j → i ≠ j → r i j ∨ r j i) (hasymm : ∀ i j, r i j → ¬ r j i) :
    ∑ i, ∑ j, (if P i ∧ P j then M i j * β i j else 0) =
      2 * ∑ i, ∑ j, (if P i ∧ P j ∧ r j i then M i j * β i j else 0) := by
  have split : ∀ i j, (if P i ∧ P j then M i j * β i j else 0) =
      (if P i ∧ P j ∧ r j i then M i j * β i j else 0) +
      (if P i ∧ P j ∧ r i j then M i j * β i j else 0) +
      (if P i ∧ P j ∧ i = j then M i j * β i j else 0) := by
    intro i j
    by_cases hp : P i ∧ P j
    · by_cases hij : i = j
      · subst hij
        have hn : ¬ r i i := fun h => hasymm i i h h
        simp [hp.1, hn]
      · rcases htri i j hp.1 hp.2 hij with h | h
        · simp [hp.1, hp.2, h, hasymm i j h, hij]
        · simp [hp.1, hp.2, h, hasymm j i h, hij]
    · rw [if_neg hp, if_neg (fun h' => hp ⟨h'.1, h'.2.1⟩), if_neg (fun h' => hp ⟨h'.1, h'.2.1⟩),
        if_neg (fun h' => hp ⟨h'.1, h'.2.1⟩)]; ring
  have hdiag : ∑ i, ∑ j, (if P i ∧ P j ∧ i = j then M i j * β i j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · obtain ⟨hpi, _, rfl⟩ := hc
      rw [hMd i hpi, zero_mul]
    · rfl
  have hup : ∑ i, ∑ j, (if P i ∧ P j ∧ r i j then M i j * β i j else 0) =
      ∑ i, ∑ j, (if P i ∧ P j ∧ r j i then M i j * β i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : P j ∧ P i ∧ r j i
    · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, hc.2.2⟩]
      have e1 : M j i = -M i j := by linear_combination hM j i hc.1 hc.2.1
      have e2 : β j i = -β i j := by linear_combination hβ j i
      rw [e1, e2]; ring
    · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.2.1, h'.1, h'.2.2⟩)]
  simp_rw [split, Finset.sum_add_distrib]
  rw [hdiag, hup, add_zero, two_mul]

theorem zmod3_add_eq_zero {a b : ZMod 3} (h : 2 * a + 2 * b = 0) : a + b = 0 := by
  have h4 : (2 : ZMod 3) * 2 = 1 := by decide
  calc a + b = 2 * 2 * (a + b) := by rw [h4, one_mul]
    _ = 2 * (2 * a + 2 * b) := by ring
    _ = 0 := by rw [h, mul_zero]

/-! ## The computation for arbitrary orders `d(i) ∈ {3, 9} ∪ 27ℕ` -/

/-- The situation of the proof (wiki 886, §3.2): the orders of the first layer are `3`, `9` or
divisible by `27`, the second and third layers are elementary, and the basis is adapted to the
cube map: `σ i = some k` says that `x_{1i}` is *active*, with `x_{1i}^{d(i)} = x_{2k}`; inactive
`x_{1i}` have `x_{1i}^{d(i)} ∈ γ₃`. -/
structure SetupGen (T : Data G) (σ : Fin T.s → Option (Fin T.t)) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2
  valid : T.Valid
  hd : ∀ i, T.d i = 3 ∨ T.d i = 9 ∨ 27 ∣ T.d i
  he : ∀ k, T.e k = 3
  hf : ∀ l, T.f l = 3
  inj : ∀ i j k, σ i = some k → σ j = some k → i = j
  hb : ∀ i k, T.b i k = if σ i = some k then 1 else 0
  hY : ∀ i k, σ i = some k → T.x₂ k = T.x₁ i ^ T.d i
  hK : ∀ i, σ i = none → T.x₁ i ^ T.d i ∈ (⊤ : Subgroup G).lowerCentralSeries 2

/-- The exponent of `x_{1h}^{d(h)}` in `a_j = ∏_k x_{2k}^{v'_{jk}}` modulo `γ₃`, read off from the
row `j` of condition (B) (for an inactive `j` of order `9`). -/
def nrow (T : Data G) (τ : Coeffs T.s T.t) (j h : Fin T.s) : ℤ :=
  ((if h < j then τ.u h j * T.q h j else 0) - (if j < h then τ.u j h else 0)) / 3

namespace SetupGen

variable {T : Data G} {σ : Fin T.s → Option (Fin T.t)} (S : SetupGen T σ)
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

theorem gcd_e (i : Fin T.s) (k : Fin T.t) : ((Nat.gcd (T.d i) (T.e k) : ℕ) : ℤ) = 3 := by
  rw [S.he, Nat.gcd_eq_right (S.three_dvd_d i)]; rfl

theorem gcd_f (i : Fin T.s) (l : Fin T.u) : ((Nat.gcd (T.d i) (T.f l) : ℕ) : ℤ) = 3 := by
  rw [S.hf, Nat.gcd_eq_right (S.three_dvd_d i)]; rfl

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

theorem bcol {h0 : Fin T.s} {k0 : Fin T.t} (hk : σ h0 = some k0) (x : Fin T.s) :
    T.b x k0 = if x = h0 then 1 else 0 := by
  rw [S.hb]
  by_cases hx : x = h0
  · subst hx; simp [hk]
  · rw [if_neg hx, if_neg]
    intro h'
    exact hx (S.inj _ _ _ h' hk)

theorem bzero {k : Fin T.t} (hk : ∀ h, σ h ≠ some k) (x : Fin T.s) : T.b x k = 0 := by
  rw [S.hb, if_neg (hk x)]

theorem brow {h : Fin T.s} (hh : σ h = none) (k : Fin T.t) : T.b h k = 0 := by
  rw [S.hb, hh]; simp

/-- `x_i^{d(i)}` commutes with `γ₂` when `9 ∣ d(i)`. -/
theorem tcY_L1 {i : Fin T.s} (h9 : 9 ∣ T.d i) {b : G}
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : tc (T.x₁ i ^ T.d i) b = 1 := by
  obtain ⟨r, hr⟩ := h9
  rw [hr]; exact tc_pow_nine_mul_L1 S.h5 S.h2 hb _ _

theorem tcL1_Y {i : Fin T.s} (h9 : 9 ∣ T.d i) {b : G}
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : tc b (T.x₁ i ^ T.d i) = 1 := by
  rw [← tc_inv, S.tcY_L1 h9 hb, inv_one]

theorem tcY_mem {i : Fin T.s} (h9 : 9 ∣ T.d i) (y : G) :
    tc (T.x₁ i ^ T.d i) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  obtain ⟨r, hr⟩ := h9
  rw [hr]; exact tc_pow_nine_mul_mem S.h5 S.h2 _ _ _

theorem tcY_one {i : Fin T.s} (h27 : 27 ∣ T.d i) (y : G) : tc (T.x₁ i ^ T.d i) y = 1 := by
  obtain ⟨r, hr⟩ := h27
  rw [hr]; exact tc_pow_27_mul S.h5 S.h2 _ _ _

omit S in
theorem lcs34 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)

theorem cube_add {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      F (a * b) = F a + F b)
    (hF0 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, F a = 0) :
    ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      F ((a * b) ^ 3) = F (a ^ 3) + F (b ^ 3) := by
  intro a ha b hb
  have hn := pow_mul_mod (N := (⊤ : Subgroup G).lowerCentralSeries 3)
    (commutator_mem_lcs (i := 1) (j := 1) (by omega) ha hb) 3
  rw [← mul_inv_cancel_left (a ^ 3 * b ^ 3) ((a * b) ^ 3),
    addMap_mul_mem lcs34 hF hF0 (mul_mem (S.h2 a ha) (S.h2 b hb)) hn,
    hF _ (S.h2 a ha) _ (S.h2 b hb)]

theorem addMap_tc_right {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b)
    {Y : G} (hY : Y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      F (tc Y (a * b)) = F (tc Y a) + F (tc Y b) := by
  intro a ha b hb
  have hta : tc Y a ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) hY ha
  have htb : tc Y b ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) hY hb
  rw [tc_mul_right, show b⁻¹ * tc Y a * b = tc Y a by
    rw [central_L3 S.h5 hta b⁻¹]; group, hF _ htb _ hta, add_comm]

/-- `c ↦ F [c, x]` is additive on `γ₃`. -/
theorem addMap_tc_left {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b)
    (x : G) : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      F (tc (a * b) x) = F (tc a x) + F (tc b x) := by
  intro a ha b hb
  have hta : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) ha (mem_lcs_zero x)
  have htb : tc b x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) hb (mem_lcs_zero x)
  rw [tc_mul_left, show b⁻¹ * tc a x * b = tc a x by
    rw [central_L3 S.h5 hta b⁻¹]; group, hF _ hta _ htb]

theorem F_tc_L3 {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b)
    {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (x : G) : F (tc c x) = 0 := by
  have : tc c x ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := tc_mem (by omega) hc (mem_lcs_zero x)
  rw [S.h5, mem_bot] at this
  rw [this]; exact addMap_one hF

/-- `F [x³, a⁻¹] = F [a³, x]` for `a ∈ γ₂`. -/
theorem F_pairing_swap {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3,
      F (a * b) = F a + F b)
    {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    F (tc (x ^ 3) a⁻¹) = F (tc (a ^ 3) x) := by
  have h3 : a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := S.h2 a ha
  have e : tc (x ^ 3) a⁻¹ = (tc ((a ^ 3)⁻¹) x)⁻¹ := by
    rw [← tc_inv, tc_pow_three_right S.h5 S.h2 (inv_mem ha), ← tc_pow_three_left S.h5 (inv_mem ha),
      inv_pow]
  have hm : tc ((a ^ 3)⁻¹) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) (inv_mem h3) (mem_lcs_zero x)
  rw [e, addMap_inv hF hm]
  have hadd := S.addMap_tc_left hF x
  have := addMap_inv (A := fun c => F (tc c x)) hadd h3
  rw [this, neg_neg]

omit S in
theorem lcs_mem_two_of_three {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 3) :
    c ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := lcs34 hc

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

/-- Condition (B) in the column of an active `h > i`: `3 ∣ u_{ih}`. -/
theorem u3_act {i h : Fin T.s} (hih : i < h) {kh : Fin T.t} (hh : σ h = some kh) :
    (3 : ℤ) ∣ τ.u i h := by
  have hB := hτ.B i kh
  rw [col_sum T.b (S.bcol hh) (fun x => i < x) (fun x => τ.u i x),
    col_sum T.b (S.bcol hh) (fun x => x < i) (fun x => τ.u x i * T.q x i),
    if_pos hih, if_neg (not_lt.mpr hih.le), S.he] at hB
  have hd3 : (3 : ℤ) ∣ τ.v i kh * (T.d i : ℤ) :=
    Dvd.dvd.mul_left (by exact_mod_cast S.three_dvd_d i) _
  generalize τ.v i kh * (T.d i : ℤ) = Z at hB hd3
  push_cast at hB
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

theorem w3 {h : Fin T.s} {kh : Fin T.t} (hact : σ h = some kh) {j k : Fin T.s} (hhj : h ≤ j)
    (hjk : j ≤ k) : (3 : ℤ) ∣ τ.w h j k := by
  rcases eq_or_lt_of_le hjk with rfl | hjk'
  · have hD := hτ.D₁ j kh
    rw [col_sum T.b (S.bcol hact) (fun x => x ≤ j) (fun x => τ.w x j j),
      col_sum T.b (S.bcol hact) (fun x => j < x) (fun x => τ.w'' j j x), if_pos hhj,
      if_neg (not_lt.mpr hhj), S.gcd_e] at hD
    have := Int.ModEq.dvd hD
    have hc : (3 : ℤ) ∣ τ.v j kh * T.ch j 2 := (S.ch2_dvd j).mul_left _
    generalize τ.v j kh * T.ch j 2 = Z at this hc
    omega
  · have hD := hτ.D₂ j k kh hjk'
    rw [col_sum T.b (S.bcol hact) (fun x => x ≤ j) (fun x => τ.w x j k),
      col_sum T.b (S.bcol hact) (fun x => j < x ∧ x ≤ k) (fun x => τ.w' j x k),
      col_sum T.b (S.bcol hact) (fun x => k < x) (fun x => τ.w'' j k x), if_pos hhj,
      if_neg (fun h' => absurd h'.1 (not_lt.mpr hhj)),
      if_neg (not_lt.mpr (hhj.trans hjk)), S.gcd_e] at hD
    have := Int.ModEq.dvd hD
    omega

theorem w'3 {g : Fin T.s} {kg : Fin T.t} (hact : σ g = some kg) {i h : Fin T.s} (hig : i < g)
    (hgh : g ≤ h) : (3 : ℤ) ∣ τ.w' i g h := by
  have hD := hτ.D₂ i h kg (hig.trans_le hgh)
  rw [col_sum T.b (S.bcol hact) (fun x => x ≤ i) (fun x => τ.w x i h),
    col_sum T.b (S.bcol hact) (fun x => i < x ∧ x ≤ h) (fun x => τ.w' i x h),
    col_sum T.b (S.bcol hact) (fun x => h < x) (fun x => τ.w'' i h x),
    if_neg (not_le.mpr hig), if_pos ⟨hig, hgh⟩, if_neg (not_lt.mpr hgh), S.gcd_e] at hD
  have := Int.ModEq.dvd hD
  omega

omit hτ in
theorem α3 {g : Fin T.s} (hg : σ g = none) {h : Fin T.s} (hgh : g ≤ h) (l : Fin T.u) :
    (3 : ℤ) ∣ T.α g h l := by
  have hm := S.valid.hα g h hgh
  have ht : tc (T.x₁ g ^ T.d g) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) (S.hK g hg) (mem_lcs_zero _)
  have hP : oprod T.x₃ (T.α g h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    have := mul_mem ht (inv_mem hm)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  have := (S.valid.basis₃.indep _).mp hP l
  rw [S.hf] at this
  exact_mod_cast this

/-- Condition (E) for a row `i` of order `3` or `9`, modulo `3`:
`∑_k v'_{ik} d_{kl} ≡ ∑_{h > i inactive} u_{ih} c_{hl}`. -/
theorem E3 (i : Fin T.s) (hi : T.d i = 3 ∨ T.d i = 9) (l : Fin T.u) :
    (3 : ℤ) ∣ (∑ k, τ.v' i k * T.dd k l) -
      ∑ h, (if i < h ∧ σ h = none then τ.u i h * T.c h l else 0) := by
  have h := hτ.E i l
  rw [S.gcd_f] at h
  have h' := Int.ModEq.dvd h
  have hu : ∀ h, h < i → (3 : ℤ) ∣ τ.u h i * T.q h i := fun h hh =>
    S.uq3 hτ hh (S.d39_of_le hh.le hi)
  have s1 : (3 : ℤ) ∣ ∑ h, if h < i then τ.u h i * T.q h i * T.α h i l else 0 :=
    dvd_sum_ite _ _ fun h hh => (hu h hh).mul_right _
  have s3 : (3 : ℤ) ∣ ∑ h, if h < i then τ.u h i * T.q h i * T.c h l else 0 :=
    dvd_sum_ite _ _ fun h hh => (hu h hh).mul_right _
  have s2 : (3 : ℤ) ∣ (∑ h, if i < h then τ.u i h * T.c h l else 0) -
      ∑ h, (if i < h ∧ σ h = none then τ.u i h * T.c h l else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun h _ => ?_
    by_cases hih : i < h
    · rcases hσ : σ h with _ | kh
      · simp [hih]
      · rw [if_pos hih, if_neg (fun hc => by simp at hc), sub_zero]
        exact (S.u3_act hτ hih hσ).mul_right _
    · simp [hih]
  have s5 : (3 : ℤ) ∣ ∑ g, ∑ h, if g ≤ i ∧ i ≤ h then τ.w g i h * T.α g h l else 0 := by
    refine Finset.dvd_sum fun g _ => dvd_sum_ite _ _ fun h hh => ?_
    rcases hσ : σ g with _ | kg
    · exact (S.α3 hσ (hh.1.trans hh.2) l).mul_left _
    · exact (S.w3 hτ hσ hh.1 hh.2).mul_right _
  have s6 : (3 : ℤ) ∣ ∑ g, ∑ h, if g ≤ h ∧ h ≤ i then τ.w g h i * T.α g h l else 0 := by
    refine Finset.dvd_sum fun g _ => dvd_sum_ite _ _ fun h hh => ?_
    rcases hσ : σ g with _ | kg
    · exact (S.α3 hσ hh.1 l).mul_left _
    · exact (S.w3 hτ hσ hh.1 hh.2).mul_right _
  have s7 : (3 : ℤ) ∣ ∑ g, ∑ h, if i < g ∧ g ≤ h then τ.w' i g h * T.α g h l else 0 := by
    refine Finset.dvd_sum fun g _ => dvd_sum_ite _ _ fun h hh => ?_
    rcases hσ : σ g with _ | kg
    · exact (S.α3 hσ hh.2 l).mul_left _
    · exact (S.w'3 hτ hσ hh.1 hh.2).mul_right _
  omega

/-- `F(a_i³)` for `a_i = ∏_k x_{2k}^{v'_{ik}}` and a row `i` of order `3` or `9`, from (E):
`a_i³ ≡ ∏_{h > i inactive} (x_h^{d(h)})^{u_{ih}}` modulo `γ₄`. -/
theorem F_a3 (i : Fin T.s) (hi : T.d i = 3 ∨ T.d i = 9) {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      F (a * b) = F a + F b)
    (hF0 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, F a = 0) :
    F (oprod T.x₂ (τ.v' i) ^ 3) =
      ∑ h, if i < h ∧ σ h = none then (τ.u i h : ZMod 3) * F (T.x₁ h ^ T.d h) else 0 := by
  have hsum := addMap_oprod (A := fun y => F (y ^ 3)) (S.cube_add hF hF0) S.x2mem (τ.v' i)
  have hxk : ∀ k, F (T.x₂ k ^ 3) = ∑ l, (T.dd k l : ZMod 3) * F (T.x₃ l) := by
    intro k
    have h := S.valid.hdd k
    rw [S.he] at h
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.dd k)) (T.x₂ k ^ 3),
      addMap_mul_mem lcs34 hF hF0 (oprod_mem S.x3mem _) h, addMap_oprod hF S.x3mem]
  have hYh : ∀ h, σ h = none → F (T.x₁ h ^ T.d h) = ∑ l, (T.c h l : ZMod 3) * F (T.x₃ l) := by
    intro h hh
    have hv := S.valid.hb h
    have hb0 : T.b h = 0 := funext fun k => S.brow hh k
    rw [hb0, oprod_zero, one_mul] at hv
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.c h)) (T.x₁ h ^ T.d h),
      addMap_mul_mem lcs34 hF hF0 (oprod_mem S.x3mem _) hv, addMap_oprod hF S.x3mem]
  have hL : (∑ k, (τ.v' i k : ZMod 3) * F (T.x₂ k ^ 3)) =
      ∑ l, ((∑ k, τ.v' i k * T.dd k l : ℤ) : ZMod 3) * F (T.x₃ l) := by
    simp_rw [hxk]
    push_cast
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  have hR : (∑ h, if i < h ∧ σ h = none then (τ.u i h : ZMod 3) * F (T.x₁ h ^ T.d h) else 0) =
      ∑ l, ((∑ h, if i < h ∧ σ h = none then τ.u i h * T.c h l else 0 : ℤ) : ZMod 3) *
        F (T.x₃ l) := by
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hc
    · rw [hYh h hc.2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    · simp
  rw [hsum, hL, hR]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hz := cast3_eq_zero (S.E3 hτ i hi l)
  rw [Int.cast_sub, sub_eq_zero] at hz
  rw [hz]

/-- Condition (B) for a row `i` of order `3`, divided by `3`. -/
theorem B' (i : Fin T.s) (hi : T.d i = 3) (k : Fin T.t) :
    (∑ h, if i < h then τ.u i h / 3 * T.b h k else 0)
      - (∑ h, if h < i then τ.u h i / 3 * T.b h k else 0) + τ.v i k + τ.v' i k = 0 := by
  have h := hτ.B i k
  have e0 : (∑ h, if h < i then τ.u h i * T.q h i * T.b h k else 0) =
      ∑ h, if h < i then τ.u h i * T.b h k else 0 := by
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hh
    · have hq : T.q h i = 1 := by simp [Data.q, hi, S.d_three_of_le hh.le hi]
      rw [hq, mul_one]
    · rfl
  rw [e0, hi, S.he] at h
  have e1 : (∑ h, if i < h then τ.u i h * T.b h k else 0) =
      3 * ∑ h, if i < h then τ.u i h / 3 * T.b h k else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hh
    · rcases hσ : σ h with _ | kh
      · rw [S.brow hσ, mul_zero, mul_zero, mul_zero]
      · rw [← mul_assoc, Int.mul_ediv_cancel' (S.u3_act hτ hh hσ)]
    · rw [mul_zero]
  have e2 : (∑ h, if h < i then τ.u h i * T.b h k else 0) =
      3 * ∑ h, if h < i then τ.u h i / 3 * T.b h k else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hh
    · have hh3 := S.d_three_of_le hh.le hi
      rw [← mul_assoc, Int.mul_ediv_cancel' (S.u3_eq hτ hh (hh3.trans hi.symm) (Or.inl hh3))]
    · rw [mul_zero]
  rw [e1, e2] at h
  push_cast at h
  omega

/-- Condition (B) for an inactive row `j` of order `9`:
`v'_{jk} = ∑_h b_{hk} n_h - 3 v_{jk}` with `n_h = nrow T τ j h`. -/
theorem Bnine (j : Fin T.s) (hj : T.d j = 9) (hjn : σ j = none) (k : Fin T.t) :
    τ.v' j k = (∑ h, T.b h k * nrow T τ j h) - 3 * τ.v j k := by
  have h := hτ.B j k
  have e : (∑ h, if j < h then τ.u j h * T.b h k else 0) -
      (∑ h, if h < j then τ.u h j * T.q h j * T.b h k else 0) =
      -(3 * ∑ h, T.b h k * nrow T τ j h) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rcases hσ : σ h with _ | kh
    · rw [S.brow hσ]; simp
    · have hdv : (3 : ℤ) ∣ (if h < j then τ.u h j * T.q h j else 0) -
          (if j < h then τ.u j h else 0) := by
        rcases lt_trichotomy h j with hhj | rfl | hjh
        · rw [if_pos hhj, if_neg (not_lt.mpr hhj.le), sub_zero]
          exact S.uq3 hτ hhj (S.d_le_nine hhj.le hj)
        · simp [hjn] at hσ
        · rw [if_neg (not_lt.mpr hjh.le), if_pos hjh, zero_sub]
          exact dvd_neg.mpr (S.u3_act hτ hjh hσ)
      simp only [nrow]
      rw [mul_left_comm, Int.mul_ediv_cancel' hdv]
      split_ifs <;> ring
  rw [e, hj, S.he] at h
  push_cast at h
  linarith

/-- For an inactive row `j` of order `9` and `F` additive on `γ₂` and zero on `γ₃`:
`F(a_j) = ∑_h n_h F(x_h^{d(h)})`. -/
theorem F_row_nine (j : Fin T.s) (hj : T.d j = 9) (hjn : σ j = none) {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      F (a * b) = F a + F b)
    (hF0 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, F a = 0) :
    F (oprod T.x₂ (τ.v' j)) = ∑ h, (nrow T τ j h : ZMod 3) * F (T.x₁ h ^ T.d h) := by
  rw [addMap_oprod hF S.x2mem]
  have hYF : ∀ h, F (T.x₁ h ^ T.d h) = ∑ k, (T.b h k : ZMod 3) * F (T.x₂ k) := by
    intro h
    rcases hσh : σ h with _ | kh
    · rw [hF0 _ (S.hK h hσh)]; simp [S.brow hσh]
    · rw [Finset.sum_eq_single kh]
      · simp [S.hb, hσh, S.hY h kh hσh]
      · intro k _ hk
        rw [S.hb, hσh, if_neg (fun e => hk (Option.some_inj.mp e).symm)]; simp
      · intro h'; exact absurd (Finset.mem_univ _) h'
  have h3 : (3 : ZMod 3) = 0 := rfl
  calc ∑ k, (τ.v' j k : ZMod 3) * F (T.x₂ k)
      = ∑ k, ∑ h, (T.b h k : ZMod 3) * (nrow T τ j h : ZMod 3) * F (T.x₂ k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [S.Bnine hτ j hj hjn k]
        push_cast
        simp only [h3, zero_mul, sub_zero, Finset.sum_mul]
    _ = ∑ h, (nrow T τ j h : ZMod 3) * F (T.x₁ h ^ T.d h) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [hYF h, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

theorem F1 {i : Fin T.s} {k : Fin T.t} (hk : σ i = some k) : (3 : ℤ) ∣ τ.v i k := by
  have h := hτ.F₁ k
  rw [col_sum' T.b (S.bcol hk), S.he] at h
  have := Int.ModEq.dvd h
  push_cast at this
  omega

theorem F2 {i j : Fin T.s} {ki kj : Fin T.t} (hi : σ i = some ki) (hj : σ j = some kj) :
    (3 : ℤ) ∣ τ.v i kj + τ.v j ki := by
  by_cases hk : ki = kj
  · subst hk
    obtain rfl := S.inj _ _ _ hi hj
    have := S.F1 hτ hi
    omega
  rcases lt_or_gt_of_ne hk with hlt | hlt
  · have h := hτ.F₂ ki kj hlt
    rw [col_sum' T.b (S.bcol hj), col_sum' T.b (S.bcol hi), S.he] at h
    have := Int.ModEq.dvd h
    push_cast at this
    omega
  · have h := hτ.F₂ kj ki hlt
    rw [col_sum' T.b (S.bcol hi), col_sum' T.b (S.bcol hj), S.he] at h
    have := Int.ModEq.dvd h
    push_cast at this
    omega

theorem F3 {i : Fin T.s} {ki k : Fin T.t} (hi : σ i = some ki) (hk : ∀ h, σ h ≠ some k) :
    (3 : ℤ) ∣ τ.v i k := by
  have hne : ki ≠ k := fun e => hk i (e ▸ hi)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h := hτ.F₂ ki k hlt
    rw [row_zero T.b (S.bzero hk), col_sum' T.b (S.bcol hi), S.he] at h
    have := Int.ModEq.dvd h
    push_cast at this
    omega
  · have h := hτ.F₂ k ki hlt
    rw [col_sum' T.b (S.bcol hi), row_zero T.b (S.bzero hk), S.he] at h
    have := Int.ModEq.dvd h
    push_cast at this
    omega

theorem genC_eq : T.genC τ = 1 := by
  unfold Data.genC
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
  split_ifs with hijk
  · rcases hσ : σ i with _ | ki
    · have : tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 4 :=
        tc_mem (i := 3) (j := 0) (by omega)
          (tc_mem (i := 2) (j := 0) (by omega) (S.hK i hσ) (mem_lcs_zero _)) (mem_lcs_zero _)
      rw [S.h5, mem_bot] at this
      rw [this, one_zpow]
    · have hz : tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ∈
          (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (i := 2) (j := 0) (by omega)
          (tc_mem (i := 1) (j := 0) (by omega) (S.Y1 i) (mem_lcs_zero _)) (mem_lcs_zero _)
      obtain ⟨w0, hw0⟩ := S.w3 hτ hσ hijk.1 hijk.2
      rw [hw0, zpow_mul, zpow_ofNat, cube_L3 S.h5 S.h2 _ hz, one_zpow]
  · rfl

/-- The factors of the `u`-part: `[x_i^{d(i)}, x_j]^{u_{ij} q_{ij}}` is `[Y_i, Y_j]^{u_{ij}/3}`
for active `i, j` of order `3`, `[Y_i³, x_j]^{u_{ij}}` for an active `i` of order `3` and an
inactive `j` of order `9`, and `1` otherwise. -/
theorem factor (i j : Fin T.s) :
    (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1) =
      (if i < j ∧ (σ i ≠ none ∧ T.d i = 3) ∧ (σ j ≠ none ∧ T.d j = 3) then
        tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ^ (τ.u i j / 3) else 1) *
      (if i < j ∧ (σ i ≠ none ∧ T.d i = 3) ∧ (σ j = none ∧ T.d j = 9) then
        tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j) ^ τ.u i j else 1) := by
  by_cases hij : i < j
  swap
  · simp only [hij, false_and, if_false, mul_one]
  rw [if_pos hij]
  have hY1i := S.Y1 i
  rcases S.hd i with hi3 | hi9 | hi27
  · rcases hσi : σ i with _ | ki
    · -- inactive `i` of order `3`
      obtain ⟨r, hr⟩ := S.uq3 hτ hij (Or.inl hi3)
      have hz : tc (T.x₁ i ^ T.d i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (by omega) (S.hK i hσi) (mem_lcs_zero _)
      rw [hr, zpow_mul, zpow_ofNat, cube_L3 S.h5 S.h2 _ hz, one_zpow]
      simp
    · rcases S.hd j with hj3 | hj9 | ⟨r, hr⟩
      · -- `d(j) = 3`: `q = 1`, `3 ∣ u`
        have hq : T.q i j = 1 := by simp [Data.q, hi3, hj3]
        obtain ⟨r, hr⟩ := S.u3_eq hτ hij (hi3.trans hj3.symm) (Or.inl hi3)
        have e : tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) =
            tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ^ (τ.u i j / 3) := by
          rw [hq, mul_one, hr, show 3 * r / 3 = r by omega, zpow_mul, zpow_ofNat,
            ← tc_pow_three_right S.h5 S.h2 hY1i, hj3]
        rw [e]
        rcases hσj : σ j with _ | kj
        · have h4 : tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ∈ (⊤ : Subgroup G).lowerCentralSeries 4 :=
            tc_mem (i := 1) (j := 2) (by omega) hY1i (S.hK j hσj)
          rw [S.h5, mem_bot] at h4
          rw [h4, one_zpow]
          simp [hj3]
        · simp [hij, hi3, hj3]
      · -- `d(j) = 9`: `q = 3`
        have hq : T.q i j = 3 := by simp [Data.q, hi3, hj9]
        have e : tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) =
            tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j) ^ τ.u i j := by
          rw [hq, show τ.u i j * 3 = 3 * τ.u i j by ring, zpow_mul, zpow_ofNat,
            ← tc_pow_three_left S.h5 hY1i]
        rw [e]
        rcases hσj : σ j with _ | kj
        · simp [hij, hi3, hj9]
        · obtain ⟨r, hr⟩ := S.u3_act hτ hij hσj
          have hz : tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
            tc_mem (by omega) (S.h2 _ hY1i) (mem_lcs_zero _)
          rw [hr, zpow_mul, zpow_ofNat, cube_L3 S.h5 S.h2 _ hz, one_zpow]
          simp [hj9]
      · -- `27 ∣ d(j)`: `9 ∣ q`
        have e : T.d j / T.d i = 9 * r := by rw [hi3, hr]; omega
        have hq : T.q i j = 9 * r := by simp [Data.q, e]
        have hj3 : T.d j ≠ 3 := by omega
        have hj9 : T.d j ≠ 9 := by omega
        rw [hq, show τ.u i j * (9 * (r : ℤ)) = 9 * (τ.u i j * r) by ring, zpow_mul, zpow_ofNat,
          pow_nine_L2 S.h5 S.h2 (tc_mem (by omega) hY1i (mem_lcs_zero _)), one_zpow]
        simp [hj3, hj9]
  · -- `d(i) = 9`
    have hz : tc (T.x₁ i ^ T.d i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      S.tcY_mem (by simp [hi9]) _
    obtain ⟨r, hr⟩ := S.uq3 hτ hij (Or.inr hi9)
    rw [hr, zpow_mul, zpow_ofNat, cube_L3 S.h5 S.h2 _ hz, one_zpow]
    have hi3 : T.d i ≠ 3 := by omega
    simp [hi3]
  · -- `27 ∣ d(i)`
    rw [S.tcY_one hi27, one_zpow]
    have hi3 : T.d i ≠ 3 := by obtain ⟨r, hr⟩ := hi27; omega
    simp [hi3]

/-- **Every generator of Tahara's Theorem 6.1 is trivial** in the situation `SetupGen`. -/
theorem gen_eq_one : T.gen τ = 1 := by
  classical
  have hle34 : (⊤ : Subgroup G).lowerCentralSeries 4 ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  -- membership facts
  let A1 : Fin T.s → Fin T.s → G := fun i j =>
    if i < j ∧ (σ i ≠ none ∧ T.d i = 3) ∧ (σ j ≠ none ∧ T.d j = 3) then
      tc (T.x₁ i ^ T.d i) (T.x₁ j ^ T.d j) ^ (τ.u i j / 3) else 1
  let A2 : Fin T.s → Fin T.s → G := fun i j =>
    if i < j ∧ (σ i ≠ none ∧ T.d i = 3) ∧ (σ j = none ∧ T.d j = 9) then
      tc ((T.x₁ i ^ T.d i) ^ 3) (T.x₁ j) ^ τ.u i j else 1
  have memA1 : ∀ i j, A1 i j ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i j
    simp only [A1]
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (S.Y1 i) (S.Y1 j)) _
    · exact one_mem _
  have memA2 : ∀ i j, A2 i j ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i j
    simp only [A2]
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (S.h2 _ (S.Y1 i)) (mem_lcs_zero _)) _
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
      (fun z hz => by rw [cube_L3 S.h5 S.h2 z hz]; exact one_mem _) (mul_mem memGA memGB) ?_
    intro F hF hF0
    rw [hF _ memGA _ memGB]
    -- notation
    let Y : Fin T.s → G := fun i => T.x₁ i ^ T.d i
    let β : Fin T.s → Fin T.s → ZMod 3 := fun i j => F (tc (Y i) (Y j))
    let γ : Fin T.s → Fin T.t → ZMod 3 := fun i k => F (tc (Y i) (T.x₂ k))
    let ε : Fin T.s → Fin T.s → ZMod 3 := fun i j => F (tc (Y i ^ 3) (T.x₁ j))
    let P' : Fin T.s → Prop := fun i => σ i ≠ none ∧ T.d i = 3
    let N9 : Fin T.s → Prop := fun j => σ j = none ∧ T.d j = 9
    let rσ : Fin T.s → Fin T.s → Prop := fun j i =>
      ∃ kj ki, σ j = some kj ∧ σ i = some ki ∧ kj < ki
    let Uz : Fin T.s → Fin T.s → ℤ := fun i j =>
      if i < j then τ.u i j / 3 else if j < i then -(τ.u j i / 3) else 0
    let V : Fin T.s → Fin T.s → ZMod 3 := fun i j =>
      ∑ k, if σ j = some k then (τ.v i k : ZMod 3) else 0
    let M : Fin T.s → Fin T.s → ZMod 3 := fun i j => V i j + (Uz i j : ZMod 3)
    have hγβ : ∀ i j kj, σ j = some kj → γ i kj = β i j := by
      intro i j kj hj; simp only [γ, β, Y, S.hY j kj hj]
    have hβskew : ∀ i j, β i j + β j i = 0 := by
      intro i j
      have ht : tc (Y i) (Y j) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (by omega) (S.Y1 i) (S.Y1 j)
      simp only [β]
      rw [show tc (Y j) (Y i) = (tc (Y i) (Y j))⁻¹ from (tc_inv _ _).symm, addMap_inv hF ht,
        add_neg_cancel]
    have hV : ∀ i j kj, σ j = some kj → V i j = τ.v i kj := by
      intro i j kj hj
      simp only [V, hj, Option.some.injEq]
      rw [Finset.sum_ite_eq]; simp
    have hβbig : ∀ i j, T.d j ≠ 3 → β i j = 0 := by
      intro i j hj
      simp only [β, Y]
      rw [S.tcL1_Y (S.nine_dvd_of_ne hj) (S.Y1 i)]
      exact addMap_one hF
    -- `[x_h⁹, x_i] = [x_i⁹, x_h]⁻¹`
    have hεsym : ∀ i h, T.d i = 3 → T.d h = 9 → F (tc (Y h) (T.x₁ i)) = -ε i h := by
      intro i h hi3 hh9
      have hc : tc (T.x₁ i) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
        tc_mem (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
      have hz : tc (T.x₁ i) (T.x₁ h) ^ 9 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
        rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul]; exact cube_L2 S.h2 _ (S.h2 _ hc)
      have e1 : Y h = T.x₁ h ^ 9 := by simp only [Y]; rw [hh9]
      have e2 : Y i ^ 3 = T.x₁ i ^ 9 := by simp only [Y]; rw [hi3, ← pow_mul]
      simp only [ε]
      rw [e1, e2, tc_pow_nine' S.h5 S.h2, tc_pow_nine' S.h5 S.h2, ← tc_inv, inv_pow]
      exact addMap_inv hF hz
    -- the `u`-part
    have FA : F (T.genA τ) = ∑ i, ∑ j,
        (if P' i ∧ P' j ∧ j < i then (Uz i j : ZMod 3) * β i j else 0) +
        ∑ i, ∑ j, (if P' i ∧ N9 j ∧ i < j then (τ.u i j : ZMod 3) * ε i j else 0) := by
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
      · -- the pairs of active indices of order `3`
        have e2 : ∀ i j, F (A1 i j) = if i < j ∧ P' i ∧ P' j then
            ((τ.u i j / 3 : ℤ) : ZMod 3) * β i j else 0 := by
          intro i j
          simp only [A1]
          split_ifs
          · exact addMap_zpow hF (tc_mem (by omega) (S.Y1 i) (S.Y1 j)) _
          · exact addMap_one hF
        simp_rw [e2]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        by_cases hc : j < i ∧ P' j ∧ P' i
        · rw [if_pos hc, if_pos ⟨hc.2.2, hc.2.1, hc.1⟩]
          have hU : Uz i j = -(τ.u j i / 3) := by
            simp only [Uz, if_neg (not_lt.mpr hc.1.le), if_pos hc.1]
          rw [hU]
          have := hβskew i j
          push_cast
          linear_combination (↑(τ.u j i / 3) : ZMod 3) * this
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.2, h.2.1, h.1⟩)]
      · -- the terms `u_{ij} [x_i⁹, x_j]` with `j` inactive of order `9`
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [A2]
        by_cases hc : i < j ∧ (σ i ≠ none ∧ T.d i = 3) ∧ (σ j = none ∧ T.d j = 9)
        · rw [if_pos hc, if_pos ⟨hc.2.1, hc.2.2, hc.1⟩]
          exact addMap_zpow hF (tc_mem (by omega) (S.h2 _ (S.Y1 i)) (mem_lcs_zero _)) _
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.2, h.1, h.2.1⟩)]
          exact addMap_one hF
    -- the `v`-part
    have FB : F (T.genB τ) = ∑ i, ∑ j,
        (if P' i ∧ P' j ∧ rσ j i then V i j * β i j else 0) := by
      unfold Data.genB
      rw [addMap_ofFn hF _ fun i => list_prod_mem fun y hy => by
        obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact memB i k]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [addMap_ofFn hF _ (memB i)]
      have inner : ∀ k, F ((List.ofFn fun l => if k < l then tc (T.x₂ l) (T.x₂ k) ^ T.b i l
          else 1).prod ^ τ.v i k) =
          (τ.v i k : ZMod 3) * ∑ l, if k < l then (T.b i l : ZMod 3) * F (tc (T.x₂ l) (T.x₂ k))
            else 0 := by
        intro k
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
      simp_rw [inner]
      by_cases hσn : σ i = none
      · have hb0 : ∀ l, (T.b i l : ZMod 3) = 0 := fun l => by rw [S.hb, hσn]; simp
        have hP : ¬ P' i := fun h => h.1 hσn
        simp [hb0, hP]
      · obtain ⟨li, hσi⟩ := Option.ne_none_iff_exists'.mp hσn
        have hrow : ∀ k, (∑ l, if k < l then (T.b i l : ZMod 3) * F (tc (T.x₂ l) (T.x₂ k))
            else 0) = if k < li then γ i k else 0 := by
          intro k
          rw [Finset.sum_eq_single li]
          · simp only [S.hb, hσi, if_true, Int.cast_one, one_mul, γ, Y, S.hY i li hσi]
          · intro l _ hl
            rw [S.hb, hσi, if_neg (fun h => hl (Option.some_inj.mp h).symm)]
            simp
          · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hrow]
        by_cases hi3 : T.d i = 3
        swap
        · -- a row of order `≥ 9` vanishes
          have hP : ¬ P' i := fun h => hi3 h.2
          simp only [hP, false_and, if_false, Finset.sum_const_zero]
          refine Finset.sum_eq_zero fun k _ => ?_
          split_ifs
          · simp only [γ, Y]
            rw [S.tcY_L1 (S.nine_dvd_of_ne hi3) (S.x2mem k), addMap_one hF, mul_zero]
          · rw [mul_zero]
        have e2 : (∑ k, (τ.v i k : ZMod 3) * (if k < li then γ i k else 0)) =
            ∑ k, if k < li then (τ.v i k : ZMod 3) * γ i k else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> simp
        rw [e2, sum_option_image σ S.inj _ (fun k hk => by
          split_ifs
          · rw [cast3_eq_zero (S.F3 hτ hσi hk), zero_mul]
          · rfl)]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hσjn : σ j = none
        · have hP : ¬ P' j := fun h => h.1 hσjn
          simp [hP, hσjn]
        · obtain ⟨kj, hσj⟩ := Option.ne_none_iff_exists'.mp hσjn
          have hiff : rσ j i ↔ kj < li := by
            constructor
            · rintro ⟨a, b, ha, hb, hab⟩
              rw [hσj, Option.some_inj] at ha
              rw [hσi, Option.some_inj] at hb
              rw [ha, hb]; exact hab
            · intro h; exact ⟨kj, li, hσj, hσi, h⟩
          rw [Finset.sum_eq_single kj]
          · rw [if_pos hσj]
            by_cases hj3 : T.d j = 3
            · have hPi : P' i := ⟨hσn, hi3⟩
              have hPj : P' j := ⟨hσjn, hj3⟩
              by_cases hlt : kj < li
              · rw [if_pos hlt, if_pos ⟨hPi, hPj, hiff.mpr hlt⟩, hV i j kj hσj, hγβ i j kj hσj]
              · rw [if_neg hlt, if_neg (fun h => hlt (hiff.mp h.2.2))]
            · have hPj : ¬ P' j := fun h => hj3 h.2
              rw [if_neg (show ¬ (P' i ∧ P' j ∧ rσ j i) from fun h => hPj h.2.1)]
              split_ifs
              · rw [hγβ i j kj hσj, hβbig i j hj3, mul_zero]
              · rfl
          · intro k _ hk
            rw [if_neg (fun h => hk (Option.some_inj.mp (h.symm.trans hσj)))]
          · intro h; exact absurd (Finset.mem_univ _) h
    -- the pairing for an active row `i` of order `3`, from (B), (E) and (F)
    have pairing : ∀ i, P' i → ∑ j, (if P' j then M i j * β i j else 0) =
        -∑ h, (if N9 h ∧ i < h then (τ.u i h : ZMod 3) * ε i h else 0) := by
      intro i hPi
      obtain ⟨li, hσi⟩ := Option.ne_none_iff_exists'.mp hPi.1
      have hi3 : T.d i = 3 := hPi.2
      have ha1 : oprod T.x₂ (τ.v' i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := oprod_mem S.x2mem _
      have hYi : Y i = T.x₁ i ^ 3 := by simp only [Y]; rw [hi3]
      -- the value from (E)
      have hR : F (tc (Y i) (oprod T.x₂ (τ.v' i))⁻¹) =
          -∑ h, (if N9 h ∧ i < h then (τ.u i h : ZMod 3) * ε i h else 0) := by
        rw [hYi, S.F_pairing_swap hF ha1,
          S.F_a3 hτ i (Or.inl hi3) (F := fun c => F (tc c (T.x₁ i))) (S.addMap_tc_left hF _)
            (fun a ha => S.F_tc_L3 hF ha _),
          ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        by_cases hc : i < h ∧ σ h = none
        · rw [if_pos hc]
          rcases S.hd h with hh3 | hh9 | hh27
          · have hu := S.u3_eq hτ hc.1 (hi3.trans hh3.symm) (Or.inl hi3)
            have hN : ¬ (N9 h ∧ i < h) := fun h' => by have := h'.1.2; omega
            rw [cast3_eq_zero hu, zero_mul, if_neg hN, neg_zero]
          · have hN : N9 h ∧ i < h := ⟨⟨hc.2, hh9⟩, hc.1⟩
            rw [if_pos hN]
            have e := hεsym i h hi3 hh9
            simp only [Y] at e
            rw [e]; ring
          · have hN : ¬ (N9 h ∧ i < h) := fun h' => by
              obtain ⟨r, hr⟩ := hh27; have := h'.1.2; omega
            rw [S.tcY_one hh27, addMap_one hF, mul_zero, if_neg hN, neg_zero]
        · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.2, h'.1.1⟩), neg_zero]
      -- the value from (B) and (F)
      have hadd := S.addMap_tc_right hF (S.Y1 i)
      have hinv := addMap_inv (A := fun y => F (tc (Y i) y)) hadd ha1
      have hsum := addMap_oprod (A := fun y => F (tc (Y i) y)) hadd S.x2mem (τ.v' i)
      rw [hR, hsum] at hinv
      have hW : ∀ k, (∑ h, if i < h then τ.u i h / 3 * T.b h k else 0)
          - (∑ h, if h < i then τ.u h i / 3 * T.b h k else 0) =
          ∑ h, if σ h = some k then Uz i h else 0 := by
        intro k
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [S.hb]
        by_cases hk : σ h = some k
        · rcases lt_trichotomy i h with hih | rfl | hhi
          · simp [hk, hih, not_lt.mpr hih.le, Uz]
          · simp [hk, Uz]
          · simp [hk, hhi, not_lt.mpr hhi.le, Uz]
        · simp [hk]
      have hv' : ∀ k, (τ.v' i k : ZMod 3) =
          -(τ.v i k : ZMod 3) - ∑ h, if σ h = some k then (Uz i h : ZMod 3) else 0 := by
        intro k
        have e := S.B' hτ i hi3 k
        rw [hW k] at e
        have e' : τ.v' i k = -τ.v i k - ∑ h, if σ h = some k then Uz i h else 0 := by linarith
        rw [e']
        push_cast
        ring
      simp_rw [hv'] at hinv
      have hv0 : ∀ k, (∀ h, σ h ≠ some k) → (τ.v i k : ZMod 3) * γ i k = 0 := fun k hk => by
        rw [cast3_eq_zero (S.F3 hτ hσi hk), zero_mul]
      have e3 : ∑ k, (τ.v i k : ZMod 3) * γ i k =
          ∑ h, ∑ k, if σ h = some k then (τ.v i k : ZMod 3) * γ i k else 0 :=
        sum_option_image σ S.inj _ hv0
      have e4 : ∑ k, (∑ h, if σ h = some k then (Uz i h : ZMod 3) else 0) * γ i k =
          ∑ h, ∑ k, if σ h = some k then (Uz i h : ZMod 3) * γ i k else 0 := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
      have e5 : ∑ k, (-(τ.v i k : ZMod 3) - ∑ h, if σ h = some k then (Uz i h : ZMod 3)
          else 0) * γ i k = -(∑ k, (τ.v i k : ZMod 3) * γ i k
            + ∑ k, (∑ h, if σ h = some k then (Uz i h : ZMod 3) else 0) * γ i k) := by
        rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e5, e3, e4, ← Finset.sum_add_distrib] at hinv
      have hinv' : (∑ h, ((∑ k, if σ h = some k then (τ.v i k : ZMod 3) * γ i k else 0) +
          ∑ k, if σ h = some k then (Uz i h : ZMod 3) * γ i k else 0)) =
          -∑ h, (if N9 h ∧ i < h then (τ.u i h : ZMod 3) * ε i h else 0) := by
        rw [neg_neg] at hinv; exact hinv.symm
      rw [← hinv']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      by_cases hσjn : σ j = none
      · have hP : ¬ P' j := fun h => h.1 hσjn
        simp [hP, hσjn]
      · obtain ⟨kj, hσj⟩ := Option.ne_none_iff_exists'.mp hσjn
        simp only [hσj]
        rw [Finset.sum_eq_single kj]
        · by_cases hj3 : T.d j = 3
          · have hP : P' j := ⟨hσjn, hj3⟩
            rw [if_pos hP, if_pos rfl, if_pos rfl, hγβ i j kj hσj]
            simp only [M, hV i j kj hσj]
            ring
          · have hP : ¬ P' j := fun h => hj3 h.2
            rw [if_neg hP, if_pos rfl, if_pos rfl, hγβ i j kj hσj, hβbig i j hj3]
            ring
        · intro k _ hk
          rw [if_neg (fun h => hk (Option.some_inj.mp h).symm),
            if_neg (fun h => hk (Option.some_inj.mp h).symm), add_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
    -- an inactive row `j` of order `9` kills its half: `∑_i u_{ij} [x_i⁹, x_j] = 0`
    have hS : ∀ j, N9 j →
        ∑ h, (if P' h ∧ h < j then (τ.u h j : ZMod 3) * ε h j else 0) = 0 := by
      intro j hj
      obtain ⟨hjn, hj9⟩ := hj
      let C : G → ZMod 3 := fun y => F (tc (y ^ 3) (T.x₁ j))
      have hC : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
          ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1, C (a * b) = C a + C b := by
        intro a ha b hb
        have hn := pow_mul_mod (N := (⊤ : Subgroup G).lowerCentralSeries 3)
          (commutator_mem_lcs (i := 1) (j := 1) (by omega) ha hb) 3
        simp only [C]
        rw [← mul_inv_cancel_left (a ^ 3 * b ^ 3) ((a * b) ^ 3),
          S.addMap_tc_left hF _ _ (mul_mem (S.h2 a ha) (S.h2 b hb)) _
            (lcs_mem_two_of_three hn), S.F_tc_L3 hF hn, add_zero,
          S.addMap_tc_left hF _ _ (S.h2 a ha) _ (S.h2 b hb)]
      have hC0 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, C a = 0 := fun a ha =>
        S.F_tc_L3 hF (cube_L2 S.h2 _ ha) _
      have h1 := S.F_row_nine hτ j hj9 hjn hC hC0
      have hzero : C (oprod T.x₂ (τ.v' j)) = 0 := by
        simp only [C]
        rw [S.F_a3 hτ j (Or.inr hj9) (F := fun c => F (tc c (T.x₁ j))) (S.addMap_tc_left hF _)
          (fun a ha => S.F_tc_L3 hF ha _)]
        refine Finset.sum_eq_zero fun h _ => ?_
        split_ifs with hc
        · rcases S.d_ge_nine hc.1.le (by simp [hj9]) with hh9 | hh27
          · rw [cast3_eq_zero (S.u3_eq hτ hc.1 (hj9.trans hh9.symm) (Or.inr hj9)), zero_mul]
          · rw [S.tcY_one hh27, addMap_one hF, mul_zero]
        · rfl
      rw [hzero] at h1
      have e : ∑ h, (if P' h ∧ h < j then (τ.u h j : ZMod 3) * ε h j else 0) =
          ∑ h, (nrow T τ j h : ZMod 3) * C (T.x₁ h ^ T.d h) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        by_cases hσh : σ h = none
        · have hP : ¬ P' h := fun hp => hp.1 hσh
          rw [if_neg (fun hc => hP hc.1), hC0 _ (S.hK h hσh), mul_zero]
        · by_cases hh3 : T.d h = 3
          · have hhj : h < j := by
              rcases lt_trichotomy h j with hlt | heq | hgt
              · exact hlt
              · subst heq; omega
              · have := S.d_dvd hgt.le
                rw [hj9, hh3] at this; norm_num at this
            have hP : P' h ∧ h < j := ⟨⟨hσh, hh3⟩, hhj⟩
            rw [if_pos hP]
            have hn : nrow T τ j h = τ.u h j := by
              have hq : T.q h j = 3 := by simp [Data.q, hh3, hj9]
              simp only [nrow, if_pos hhj, if_neg (not_lt.mpr hhj.le), sub_zero, hq]
              omega
            have hCε : C (T.x₁ h ^ T.d h) = ε h j := rfl
            rw [hn, hCε]
          · have hP : ¬ (P' h ∧ h < j) := fun hc => hh3 hc.1.2
            rw [if_neg hP]
            have hz : C (T.x₁ h ^ T.d h) = 0 := by
              obtain ⟨r, hr⟩ := S.nine_dvd_of_ne hh3
              simp only [C]
              rw [← pow_mul, hr, show 9 * r * 3 = 27 * r by ring, tc_pow_27_mul S.h5 S.h2,
                addMap_one hF]
            rw [hz, mul_zero]
      rw [e, ← h1]
    have hEtot : ∑ i, ∑ j, (if P' i ∧ N9 j ∧ i < j then (τ.u i j : ZMod 3) * ε i j else 0) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : N9 j
      · refine Eq.trans (Finset.sum_congr rfl fun h _ => ?_) (hS j hj)
        by_cases hc : P' h ∧ h < j
        · rw [if_pos ⟨hc.1, hj, hc.2⟩, if_pos hc]
        · rw [if_neg (fun h' => hc ⟨h'.1, h'.2.2⟩), if_neg hc]
      · exact Finset.sum_eq_zero fun h _ => by rw [if_neg (fun h' => hj h'.2.1)]
    -- the whole pairing vanishes
    have hfull : ∑ i, ∑ j, (if P' i ∧ P' j then M i j * β i j else 0) = 0 := by
      have hrow : ∀ i, ∑ j, (if P' i ∧ P' j then M i j * β i j else 0) =
          if P' i then -∑ h, (if N9 h ∧ i < h then (τ.u i h : ZMod 3) * ε i h else 0) else 0 := by
        intro i
        by_cases hPi : P' i
        · rw [if_pos hPi, ← pairing i hPi]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hPj : P' j
          · rw [if_pos ⟨hPi, hPj⟩, if_pos hPj]
          · rw [if_neg (fun h => hPj h.2), if_neg hPj]
        · rw [if_neg hPi]
          exact Finset.sum_eq_zero fun j _ => by rw [if_neg (fun h => hPi h.1)]
      rw [Finset.sum_congr rfl fun i _ => hrow i]
      have e : ∑ i, (if P' i then
          -∑ h, (if N9 h ∧ i < h then (τ.u i h : ZMod 3) * ε i h else 0) else 0) =
          -∑ i, ∑ j, (if P' i ∧ N9 j ∧ i < j then (τ.u i j : ZMod 3) * ε i j else 0) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hPi : P' i
        · rw [if_pos hPi]
          congr 1
          refine Finset.sum_congr rfl fun h _ => ?_
          by_cases hc : N9 h ∧ i < h
          · rw [if_pos hc, if_pos ⟨hPi, hc.1, hc.2⟩]
          · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.2.1, h'.2.2⟩)]
        · rw [if_neg hPi, Finset.sum_eq_zero (fun h _ => if_neg (fun h' => hPi h'.1)), neg_zero]
      rw [e, hEtot, neg_zero]
    -- skew-symmetry and the end
    have hUskew : ∀ i j, P' i → P' j → (Uz i j : ZMod 3) + (Uz j i : ZMod 3) = 0 := by
      intro i j _ _
      have h2 : Uz i j + Uz j i = 0 := by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [Uz, h, not_lt.mpr h.le]
        · simp [Uz]
        · simp [Uz, h, not_lt.mpr h.le]
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h2
    have hUd : ∀ i, P' i → (Uz i i : ZMod 3) = 0 := fun i _ => by simp [Uz]
    have hVskew : ∀ i j, P' i → P' j → V i j + V j i = 0 := by
      intro i j hi hj
      obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp hi.1
      obtain ⟨kj, hkj⟩ := Option.ne_none_iff_exists'.mp hj.1
      rw [hV i j kj hkj, hV j i ki hki]
      have h1 := cast3_eq_zero (S.F2 hτ hki hkj)
      push_cast at h1
      exact h1
    have hVd : ∀ i, P' i → V i i = 0 := by
      intro i hi
      obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp hi.1
      rw [hV i i ki hki]
      exact cast3_eq_zero (S.F1 hτ hki)
    have hU := skew_total_rel P' (fun a b => a < b) (fun i j => (Uz i j : ZMod 3)) β hUskew hUd
      hβskew (fun i j _ _ hij => lt_or_gt_of_ne hij) (fun i j h => not_lt.mpr h.le)
    have hVs := skew_total_rel P' (fun j i => rσ j i) V β hVskew hVd hβskew
      (fun i j hi hj hij => by
        obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp hi.1
        obtain ⟨kj, hkj⟩ := Option.ne_none_iff_exists'.mp hj.1
        have hk : ki ≠ kj := fun e => hij (S.inj _ _ _ hki (e ▸ hkj))
        rcases lt_or_gt_of_ne hk with h | h
        · exact Or.inl ⟨ki, kj, hki, hkj, h⟩
        · exact Or.inr ⟨kj, ki, hkj, hki, h⟩)
      (fun i j h h' => by
        obtain ⟨a, b, ha, hb, hab⟩ := h
        obtain ⟨c, d, hc, hd, hcd⟩ := h'
        rw [ha, Option.some_inj] at hd
        rw [hb, Option.some_inj] at hc
        subst hd hc
        exact lt_asymm hab hcd)
    have hsplit : ∑ i, ∑ j, (if P' i ∧ P' j then M i j * β i j else 0) =
        ∑ i, ∑ j, (if P' i ∧ P' j then V i j * β i j else 0) +
        ∑ i, ∑ j, (if P' i ∧ P' j then (Uz i j : ZMod 3) * β i j else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · simp only [M]; ring
      · simp
    rw [hsplit, hU, hVs] at hfull
    rw [FA, FB, hEtot, add_zero]
    exact zmod3_add_eq_zero (by rw [add_comm]; exact hfull)
  rwa [S.h5, mem_bot] at key

end SetupGen


/-! ## A basis adapted to a flag and a subspace -/

section FlagBasis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For a descending chain of subspaces `W 0 ⊇ W 1 ⊇ ⋯` with `W N = 0` and a subspace `Ker`
there is a linearly independent set `B ⊆ W 0` such that every `W j` is spanned by `B ∩ W j` and
`W 0 ∩ Ker` by `B ∩ Ker` (wiki 886, §3.2, the lemma). -/
theorem exists_flag_ker_basis (W : ℕ → Submodule K V) (hW : Antitone W) {N : ℕ} (hN : W N = ⊥)
    (Ker : Submodule K V) :
    ∃ B : Set V, LinearIndepOn K id B ∧ B ⊆ W 0 ∧
      (∀ j, W j ≤ Submodule.span K (B ∩ W j)) ∧ W 0 ⊓ Ker ≤ Submodule.span K (B ∩ Ker) := by
  have key : ∀ m, m ≤ N → ∃ B : Set V, LinearIndepOn K id B ∧ B ⊆ W (N - m) ∧
      (∀ j, N - m ≤ j → W j ≤ Submodule.span K (B ∩ W j)) ∧
      W (N - m) ⊓ Ker ≤ Submodule.span K (B ∩ Ker) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨∅, linearIndepOn_empty K id, Set.empty_subset _, fun j hj => ?_, ?_⟩
      · rw [Nat.sub_zero] at hj
        exact ((hW hj).trans hN.le).trans bot_le
      · rw [Nat.sub_zero, hN, bot_inf_eq]; exact bot_le
    | succ m ih =>
      intro hm
      obtain ⟨B, hB, hBW, hBj, hBK⟩ := ih (by omega)
      have hj0 : N - m = N - (m + 1) + 1 := by omega
      rw [hj0] at hBW hBj hBK
      -- extend `B` inside `B ∪ (W j₀ ⊓ Ker)`
      obtain ⟨b, hbt, hBb, htb, hb⟩ := exists_linearIndepOn_id_extension hB
        (Set.subset_union_left (t := ((W (N - (m + 1)) ⊓ Ker : Submodule K V) : Set V)))
      have hbW : b ⊆ W (N - (m + 1)) := fun x hx => by
        rcases hbt hx with h | h
        · exact hW (Nat.le_succ _) (hBW h)
        · exact (Submodule.mem_inf.mp h).1
      have hbK : W (N - (m + 1)) ⊓ Ker ≤ Submodule.span K (b ∩ Ker) := by
        intro v hv
        have hvb : v ∈ Submodule.span K b := htb (Set.mem_union_right _ hv)
        have hbs : b ⊆ B ∪ (b ∩ Ker) := fun x hx => by
          by_cases hxB : x ∈ B
          · exact Or.inl hxB
          · rcases hbt hx with h | h
            · exact absurd h hxB
            · exact Or.inr ⟨hx, (Submodule.mem_inf.mp h).2⟩
        have hv' : v ∈ Submodule.span K B ⊔ Submodule.span K (b ∩ Ker) := by
          rw [← Submodule.span_union]; exact Submodule.span_mono hbs hvb
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv'
        have hzK : z ∈ Ker := (Submodule.span_le.mpr (fun x hx => hx.2)) hz
        have hyW : y ∈ W (N - (m + 1) + 1) := (Submodule.span_le.mpr hBW) hy
        have hyK : y ∈ Ker := by
          have e : y = (y + z) - z := by abel
          rw [e]; exact sub_mem (Submodule.mem_inf.mp hv).2 hzK
        have hy' := hBK (Submodule.mem_inf.mpr ⟨hyW, hyK⟩)
        exact add_mem (Submodule.span_mono (Set.inter_subset_inter_left _ hBb) hy') hz
      -- extend `b` to a basis of `W j₀`
      obtain ⟨B', hB't, hbB', htB', hB'⟩ := exists_linearIndepOn_id_extension hb hbW
      refine ⟨B', hB', hB't, fun j hj => ?_, ?_⟩
      · rcases eq_or_lt_of_le hj with h | h
        · subst h
          intro v hv
          have := htB' hv
          rwa [Set.inter_eq_left.mpr hB't]
        · exact (hBj j (by omega)).trans
            (Submodule.span_mono (Set.inter_subset_inter_left _ (hBb.trans hbB')))
      · exact hbK.trans (Submodule.span_mono (Set.inter_subset_inter_left _ hbB'))
  obtain ⟨B, hB, hBW, hBj, hBK⟩ := key N le_rfl
  rw [Nat.sub_self] at hBW hBK
  exact ⟨B, hB, hBW, fun j => hBj j (by omega), hBK⟩

end FlagBasis

/-! ## Uniqueness bases from the socle -/

/-- A family `y_i` in an abelian group with `3^{h_i+1} y_i = 0`, whose socle vectors
`3^{h_i} y_i` are independent modulo `3` and adapted to the heights (every element of order `3`
in `3^j A` is a combination of the `3^{h_i} y_i` with `h_i ≥ j`), in a group of exponent a power
of `3`, is a basis: `∑ a_i y_i = 0 ↔ 3^{h_i+1} ∣ a_i`, and every element is such a sum. -/
theorem socle_basis {A : Type*} [AddCommGroup A] {n : ℕ} (y : Fin n → A) (ht : Fin n → ℕ)
    (hord : ∀ i, ((3 : ℤ) ^ (ht i + 1)) • y i = 0)
    (hind : ∀ c : Fin n → ℤ, ∑ i, c i • ((3 : ℤ) ^ ht i • y i) = 0 → ∀ i, (3 : ℤ) ∣ c i)
    (hflag : ∀ (j : ℕ) (v : A), (3 : ℤ) • v = 0 → (∃ a : A, ((3 : ℤ) ^ j) • a = v) →
      ∃ c : Fin n → ℤ, v = ∑ i, c i • ((3 : ℤ) ^ ht i • y i) ∧ ∀ i, ht i < j → c i = 0)
    (hexp : ∀ v : A, ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0) :
    (∀ a : Fin n → ℤ, ∑ i, a i • y i = 0 ↔ ∀ i, (3 : ℤ) ^ (ht i + 1) ∣ a i) ∧
      ∀ v : A, ∃ a : Fin n → ℤ, v = ∑ i, a i • y i := by
  have hz0 : ∀ i (r : ℤ), ((3 : ℤ) ^ (ht i + 1) * r) • y i = 0 := fun i r => by
    rw [mul_comm, mul_smul, hord, smul_zero]
  -- independence, by induction on the power of `3` that makes all coefficients divisible
  have hind' : ∀ m : ℕ, ∀ a : Fin n → ℤ, ∑ i, a i • y i = 0 →
      (∀ i, (3 : ℤ) ^ (ht i + 1) ∣ 3 ^ m * a i) → ∀ i, (3 : ℤ) ^ (ht i + 1) ∣ a i := by
    intro m
    induction m with
    | zero => intro a _ h i; simpa using h i
    | succ m ih =>
      intro a ha h
      apply ih a ha
      choose k hk using h
      have hk' : ∀ i, 3 ^ m * a i = 3 ^ ht i * k i := fun i => by
        have h3 : (3 : ℤ) * (3 ^ m * a i) = 3 * (3 ^ ht i * k i) := by
          linear_combination hk i
        exact mul_left_cancel₀ (by norm_num) h3
      have hsum : ∑ i, k i • ((3 : ℤ) ^ ht i • y i) = 0 := by
        have e : ∑ i, k i • ((3 : ℤ) ^ ht i • y i) = (3 : ℤ) ^ m • ∑ i, a i • y i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, smul_smul, mul_comm (k i), ← hk' i]
        rw [e, ha, smul_zero]
      intro i
      obtain ⟨r, hr⟩ := hind k hsum i
      exact ⟨r, by rw [hk' i, hr]; ring⟩
  refine ⟨fun a => ⟨fun ha i => ?_, fun ha => ?_⟩, fun v => ?_⟩
  · refine hind' (∑ j, (ht j + 1)) a ha (fun j => Dvd.dvd.mul_right (pow_dvd_pow 3 ?_) _) i
    exact Finset.single_le_sum (f := fun j => ht j + 1) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ j)
  · refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨r, hr⟩ := ha i
    rw [hr, hz0]
  -- spanning: one step of the induction on the order
  have step : ∀ (a : Fin n → ℤ) (v : A), (3 : ℤ) • v = ∑ i, a i • y i → ∀ H : ℕ,
      (∀ j, H < ht j → (3 : ℤ) ∣ a j) → ∀ i, ht i = H → (3 : ℤ) ∣ a i := by
    intro a v ha H hup
    choose! a' ha' using hup
    obtain ⟨u, hu_def⟩ : ∃ u : A, u = ∑ i, (if ht i = H then a i else 0) • ((3 : ℤ) ^ ht i • y i) :=
      ⟨_, rfl⟩
    have hu3 : (3 : ℤ) • u = 0 := by
      rw [hu_def, Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_comm, smul_smul (3 : ℤ), ← pow_succ', hord, smul_zero]
    have hu : u = (3 : ℤ) ^ (H + 1) • (v - ∑ i, (if H < ht i then a' i else 0) • y i) := by
      rw [hu_def, smul_sub, pow_succ, mul_smul, ha, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
      rcases lt_trichotomy (ht i) H with hlt | heq | hgt
      · rw [if_neg (ne_of_lt hlt), if_neg (not_lt.mpr hlt.le), zero_mul, zero_smul, mul_zero,
          sub_zero, show (3 : ℤ) ^ H * a i = 3 ^ (ht i + 1) * (3 ^ (H - (ht i + 1)) * a i) by
            rw [← mul_assoc, ← pow_add]; congr 2; omega, hz0]
      · rw [if_pos heq, if_neg (by omega), heq]
        congr 1; ring
      · rw [if_neg (ne_of_gt hgt), if_pos hgt, ha' i hgt]
        congr 1; ring
    obtain ⟨c, hc, hc0⟩ := hflag (H + 1) u hu3 ⟨_, hu.symm⟩
    have hz : ∑ i, ((if ht i = H then a i else 0) - c i) • ((3 : ℤ) ^ ht i • y i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hu_def, ← hc, sub_self]
    intro i hi
    have := hind _ hz i
    rw [if_pos hi, hc0 i (by omega), sub_zero] at this
    exact this
  have hspan : ∀ k : ℕ, ∀ v : A, (3 : ℤ) ^ k • v = 0 → ∃ a : Fin n → ℤ, v = ∑ i, a i • y i := by
    intro k
    induction k with
    | zero => intro v hv; exact ⟨0, by simpa using hv⟩
    | succ k ih =>
      intro v hv
      obtain ⟨a, ha⟩ := ih ((3 : ℤ) • v) (by rw [smul_smul, ← pow_succ]; exact hv)
      let Mx := ∑ i, (ht i + 1)
      have hlt : ∀ i, ht i < Mx := fun i => by
        have := Finset.single_le_sum (f := fun j => ht j + 1) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        omega
      have claim : ∀ t, ∀ i, Mx - t ≤ ht i → (3 : ℤ) ∣ a i := by
        intro t
        induction t with
        | zero => intro i hi; have := hlt i; omega
        | succ t ih' =>
          intro i hi
          by_cases h : Mx - t ≤ ht i
          · exact ih' i h
          · exact step a v ha (ht i) (fun j hj => ih' j (by omega)) i rfl
      have hdiv : ∀ i, (3 : ℤ) ∣ a i := fun i => claim Mx i (by omega)
      choose a' ha' using hdiv
      have hw : (3 : ℤ) • (v - ∑ i, a' i • y i) = 0 := by
        rw [smul_sub, ha, Finset.smul_sum, sub_eq_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← ha']
      obtain ⟨c, hc, -⟩ := hflag 0 _ hw ⟨_, by rw [pow_zero, one_smul]⟩
      refine ⟨fun i => a' i + c i * 3 ^ ht i, ?_⟩
      calc v = (v - ∑ i, a' i • y i) + ∑ i, a' i • y i := (sub_add_cancel _ _).symm
        _ = ∑ i, c i • ((3 : ℤ) ^ ht i • y i) + ∑ i, a' i • y i := by rw [← hc]
        _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [add_smul, smul_smul, add_comm]
  obtain ⟨k, hk⟩ := hexp v
  exact hspan k v hk

/-- The lift of a socle basis as in `socle_basis` is a uniqueness basis of `G/γ₂`. -/
theorem isLayerBasis_zero_of_socle {n : ℕ} (x : Fin n → G) (ht : Fin n → ℕ) (hmono : Monotone ht)
    (hb : (∀ a : Fin n → ℤ, ∑ i, a i • cl G 0 (x i) = 0 ↔ ∀ i, (3 : ℤ) ^ (ht i + 1) ∣ a i) ∧
      ∀ v, ∃ a : Fin n → ℤ, v = ∑ i, a i • cl G 0 (x i)) :
    IsLayerBasis 0 x (fun i => 3 ^ (ht i + 1)) := by
  refine ⟨fun i => mem_lcs_zero _, fun i => Nat.one_lt_pow (by omega) (by norm_num),
    fun i j hij => Nat.pow_dvd_pow 3 (by have := hmono hij; omega), fun a => ?_, fun g _ => ?_⟩
  · rw [← cl_eq_zero_iff (oprod_mem (fun i => mem_lcs_zero (x i)) a),
      cl_oprod (fun i => mem_lcs_zero (x i)), hb.1]
    exact ⟨fun h i => by exact_mod_cast h i, fun h i => by exact_mod_cast h i⟩
  · obtain ⟨a, ha⟩ := hb.2 (cl G 0 g)
    refine ⟨a, ?_⟩
    rw [← cl_eq_cl (oprod_mem (fun i => mem_lcs_zero (x i)) a) (mem_lcs_zero g),
      cl_oprod (fun i => mem_lcs_zero (x i)), ← ha]

section Coords'

variable {V : Type*} [AddCommGroup V] (W : AddSubgroup V) [Module (ZMod 3) W] {n : ℕ}
  (e : Module.Basis (Fin n) (ZMod 3) W)

theorem basis_coords' (v : V) (hv : v ∈ W) :
    v = ∑ i, ((e.repr ⟨v, hv⟩ i).val : ℤ) • (e i : V) := by
  have hzs : ∀ (r : ZMod 3) (u : W), r • u = ((r.val : ℕ) : ℤ) • u := fun r u => by
    rw [← Int.cast_smul_eq_zsmul (ZMod 3), Int.cast_natCast, ZMod.natCast_zmod_val]
  have hr := e.sum_repr ⟨v, hv⟩
  simp only [hzs] at hr
  have h1 := congrArg W.subtype hr
  rw [map_sum] at h1
  simp only [map_zsmul, AddSubgroup.coe_subtype] at h1
  exact h1.symm

theorem basis_indep' (c : Fin n → ℤ) (h0 : ∑ i, c i • (e i : V) = 0) : ∀ i, (3 : ℤ) ∣ c i := by
  have hzs : ∀ (r : ℤ) (u : W), ((r : ZMod 3)) • u = r • u :=
    fun r u => Int.cast_smul_eq_zsmul (ZMod 3) r u
  have h0W : ∑ i, c i • e i = 0 := by
    apply W.subtype_injective
    rw [map_sum, map_zero]
    simp only [map_zsmul, AddSubgroup.coe_subtype]
    exact h0
  have hli := Fintype.linearIndependent_iff.mp e.linearIndependent (fun i => (c i : ZMod 3))
    (by simp only [hzs]; exact h0W)
  intro i
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (hli i)

end Coords'

/-! ## The theorem for finite groups of class `≤ 4` -/

/-- **`D₅ = 1` when `γ₂/γ₃` has exponent `3`, finite case, modulo Tahara.** Let `Q` be finite of
class `≤ 4` such that `Q/γ₂(Q)` is a `3`-group and `γ₂/γ₃` has exponent dividing `3`. Then
`D₅(Q) = 1`. -/
theorem D_five_eq_bot_of_class_four_exp_L1 (hT : TaharaFiveOne) {Q : Type} [Group Q] [Finite Q]
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (h3grp : ∀ x : Q, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1)
    (h2 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) :
    D 5 Q = ⊥ := by
  classical
  have h3 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, a ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 :=
    cube_succ h2
  have hcl_pow : ∀ (g : Q) (k : ℕ),
      (k • cl Q 0 g = 0 ↔ g ^ k ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) := by
    intro g k
    rw [← natCast_zsmul, ← cl_zpow (mem_lcs_zero g), zpow_natCast, cl_eq_zero_iff (mem_lcs_zero _)]
  have hcl_npow : ∀ (g : Q) (k : ℕ), cl Q 0 (g ^ k) = k • cl Q 0 g := by
    intro g k
    rw [← zpow_natCast, cl_zpow (mem_lcs_zero g), natCast_zsmul]
  letI : Module (ZMod 3) (Additive (Layer Q 1)) := AddCommGroup.zmodModule (three_smul_cl h2)
  letI : Module (ZMod 3) (Additive (Layer Q 2)) := AddCommGroup.zmodModule (three_smul_cl h3)
  -- `Q/γ₂` has exponent a power of `3`
  have hexp : ∀ v : Additive (Layer Q 0), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, -, rfl⟩ := cl_surj (G := Q) 0 v
    obtain ⟨k, hk⟩ := h3grp g
    refine ⟨k, ?_⟩
    rw [show ((3 : ℤ) ^ k) = ((3 ^ k : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul]
    exact (hcl_pow g _).mpr hk
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v : Additive (Layer Q 0), ((3 : ℤ) ^ N) • v = 0 := by
    letI := Fintype.ofFinite (Additive (Layer Q 0))
    choose kf hkf using hexp
    refine ⟨Finset.univ.sup kf, fun v => ?_⟩
    have hle : kf v ≤ Finset.univ.sup kf := Finset.le_sup (Finset.mem_univ v)
    rw [show Finset.univ.sup kf = (Finset.univ.sup kf - kf v) + kf v by omega, pow_add, mul_smul,
      hkf, smul_zero]
  -- the `3`-torsion `W` of `Q/γ₂`, an `𝔽₃`-space
  obtain ⟨W, hWmem⟩ : ∃ W : AddSubgroup (Additive (Layer Q 0)),
      ∀ v, v ∈ W ↔ (3 : ℕ) • v = 0 :=
    ⟨{ carrier := {v | (3 : ℕ) • v = 0}
       add_mem' := fun {u v} hu hv => by
         simp only [Set.mem_setOf_eq] at *; rw [smul_add, hu, hv, add_zero]
       zero_mem' := by simp
       neg_mem' := fun {u} hu => by
         simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hu, neg_zero] }, fun v => Iff.rfl⟩
  have hW3 : ∀ v : W, (3 : ℕ) • v = 0 := fun v => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact (hWmem _).mp v.2)
  letI : Module (ZMod 3) W := AddCommGroup.zmodModule hW3
  -- the cube map `W → γ₂/γ₃`
  choose L0 hL0 using fun v : Additive (Layer Q 0) => cl_surj (G := Q) 0 v
  choose L1 hL1 using fun v : Additive (Layer Q 1) => cl_surj (G := Q) 1 v
  choose L2 hL2 using fun v : Additive (Layer Q 2) => cl_surj (G := Q) 2 v
  have hmemW : ∀ x : Q, (3 : ℕ) • cl Q 0 x = 0 → x ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
    fun x h => (hcl_pow x 3).mp h
  let p : W → Additive (Layer Q 1) := fun v => cl Q 1 ((L0 v) ^ 3)
  have hp : ∀ (x : Q) (v : W), (v : Additive (Layer Q 0)) = cl Q 0 x → p v = cl Q 1 (x ^ 3) := by
    intro x v hv
    have hy : cl Q 0 (L0 v) = v := (hL0 v).2
    have hyx : (L0 v)⁻¹ * x ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
      (cl_eq_cl (mem_lcs_zero _) (mem_lcs_zero _)).mp (hy.trans hv)
    have hy3 : (L0 v) ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
      hmemW _ (by rw [hy]; exact (hWmem _).mp v.2)
    have hx3 : x ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
      hmemW x (by rw [← hv]; exact (hWmem _).mp v.2)
    show cl Q 1 ((L0 v) ^ 3) = cl Q 1 (x ^ 3)
    rw [cl_eq_cl hy3 hx3]
    have hn := cube_mul_mod h2 (L0 v) ((L0 v)⁻¹ * x)
    rw [mul_inv_cancel_left] at hn
    have e : ((L0 v) ^ 3)⁻¹ * x ^ 3 =
        ((L0 v)⁻¹ * x) ^ 3 * (((L0 v) ^ 3 * ((L0 v)⁻¹ * x) ^ 3)⁻¹ * x ^ 3) := by group
    rw [e]; exact mul_mem (h2 _ hyx) hn
  have hpadd : ∀ u v : W, p (u + v) = p u + p v := by
    intro u v
    have hu3 := hmemW (L0 u) (by rw [(hL0 u).2]; exact (hWmem _).mp u.2)
    have hv3 := hmemW (L0 v) (by rw [(hL0 v).2]; exact (hWmem _).mp v.2)
    rw [hp (L0 u * L0 v) (u + v) (by
      rw [cl_mul (mem_lcs_zero _) (mem_lcs_zero _), (hL0 u).2, (hL0 v).2]; rfl)]
    have hn := cube_mul_mod h2 (L0 u) (L0 v)
    have huv3 : (L0 u * L0 v) ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
      rw [← mul_inv_cancel_left ((L0 u) ^ 3 * (L0 v) ^ 3) ((L0 u * L0 v) ^ 3)]
      exact mul_mem (mul_mem hu3 hv3) (lcs_mem_of_le (by norm_num) hn)
    show cl Q 1 ((L0 u * L0 v) ^ 3) = cl Q 1 ((L0 u) ^ 3) + cl Q 1 ((L0 v) ^ 3)
    rw [← cl_mul hu3 hv3, eq_comm, cl_eq_cl (mul_mem hu3 hv3) huv3]
    exact hn
  let P : W →ₗ[ZMod 3] Additive (Layer Q 1) := (AddMonoidHom.mk' p hpadd).toZModLinearMap 3
  have hPv : ∀ v, P v = p v := fun v => rfl
  -- the height filtration of `W`
  let H : ℕ → AddSubgroup (Additive (Layer Q 0)) := fun j =>
    { carrier := {v | ∃ a, ((3 : ℤ) ^ j) • a = v}
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, smul_add _ _ _⟩
      zero_mem' := ⟨0, smul_zero _⟩
      neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, smul_neg _ _⟩ }
  let Wf : ℕ → Submodule (ZMod 3) W := fun j =>
    AddSubgroup.toZModSubmodule 3 ((H j).comap W.subtype)
  have hWf : ∀ j (w : W), w ∈ Wf j ↔ ∃ a, ((3 : ℤ) ^ j) • a = (w : Additive (Layer Q 0)) :=
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
  obtain ⟨B, hB, -, hBj, hBK⟩ := exists_flag_ker_basis Wf hWanti hWN (LinearMap.ker P)
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
  -- the basis, sorted by height
  let eqv : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let htw : W → ℕ := fun w => Nat.findGreatest (fun j => (w : Additive (Layer Q 0)) ∈ H j) N
  let ht0 : Fin (Fintype.card B) → ℕ := fun i => htw (eqv.symm i)
  let π := Tuple.sort ht0
  let e : Module.Basis (Fin (Fintype.card B)) (ZMod 3) W := b0.reindex (eqv.trans π.symm)
  let ht : Fin (Fintype.card B) → ℕ := fun i => ht0 (π i)
  have hmono : Monotone ht := Tuple.monotone_sort ht0
  have he : ∀ i, e i = (eqv.symm (π i) : W) := fun i => by
    simp only [e, Module.Basis.reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm, hb0]
  have hrepr : ∀ (v : W) i, e.repr v i = b0.repr v (eqv.symm (π i)) := fun v i => by
    simp only [e, Module.Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  have hE1 : ∀ i, ∃ a : Additive (Layer Q 0), ((3 : ℤ) ^ ht i) • a = (e i : Additive (Layer Q 0)) := by
    intro i
    rw [he i]
    exact Nat.findGreatest_spec (P := fun j => ((eqv.symm (π i) : W) : Additive (Layer Q 0)) ∈ H j)
      (Nat.zero_le N) ⟨((eqv.symm (π i) : W) : Additive (Layer Q 0)), by simp⟩
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
  have hE3 : ∀ v : W, v ∈ LinearMap.ker P → ∀ i, e.repr v i ≠ 0 → P (e i) = 0 := by
    intro v hv i hi
    have hsub := hBK (Submodule.mem_inf.mpr ⟨hWf0 v, hv⟩)
    rw [hset] at hsub
    have hmem : eqv.symm (π i) ∈ {β : B | (β : W) ∈ LinearMap.ker P} := by
      apply (b0.mem_span_image.mp hsub)
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hrepr]
      exact hi
    rw [he i]
    exact hmem
  -- the first layer
  choose a0 ha0 using hE1
  obtain ⟨x1, hx1⟩ : ∃ x1 : Fin (Fintype.card B) → Q, ∀ i, cl Q 0 (x1 i) = a0 i :=
    ⟨fun i => L0 (a0 i), fun i => (hL0 _).2⟩
  have hz : ∀ i, (3 : ℤ) ^ ht i • cl Q 0 (x1 i) = (e i : Additive (Layer Q 0)) := fun i => by
    rw [hx1]; exact ha0 i
  have hecl : ∀ i, ((e i : W) : Additive (Layer Q 0)) = cl Q 0 (x1 i ^ (3 ^ ht i)) := by
    intro i
    rw [hcl_npow, ← hz i, ← natCast_zsmul, Nat.cast_pow, Nat.cast_ofNat]
  have hord : ∀ i, ((3 : ℤ) ^ (ht i + 1)) • cl Q 0 (x1 i) = 0 := by
    intro i
    rw [pow_succ', mul_smul, hz i]
    have := (hWmem _).mp (e i).2
    rw [← natCast_zsmul] at this
    exact_mod_cast this
  have hdpow : ∀ i, x1 i ^ (3 ^ (ht i + 1)) = (x1 i ^ (3 ^ ht i)) ^ 3 := fun i => by
    rw [← pow_mul, pow_succ]
  have hx1d : ∀ i, x1 i ^ (3 ^ (ht i + 1)) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
    intro i
    rw [hdpow]
    exact hmemW _ (by rw [← hecl]; exact (hWmem _).mp (e i).2)
  have hpe : ∀ i, P (e i) = cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) := by
    intro i
    rw [hPv, hdpow]
    exact hp _ _ (hecl i)
  have hind : ∀ c : Fin (Fintype.card B) → ℤ,
      ∑ i, c i • ((3 : ℤ) ^ ht i • cl Q 0 (x1 i)) = 0 → ∀ i, (3 : ℤ) ∣ c i := by
    intro c hc
    exact basis_indep' W e c (by simpa only [hz] using hc)
  have hflag : ∀ (j : ℕ) (v : Additive (Layer Q 0)), (3 : ℤ) • v = 0 →
      (∃ a, ((3 : ℤ) ^ j) • a = v) →
      ∃ c : Fin (Fintype.card B) → ℤ, v = ∑ i, c i • ((3 : ℤ) ^ ht i • cl Q 0 (x1 i)) ∧
        ∀ i, ht i < j → c i = 0 := by
    intro j v hv3 hvj
    have hvW : v ∈ W := (hWmem v).mpr (by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, natCast_zsmul] at hv3; exact hv3)
    refine ⟨fun i => ((e.repr ⟨v, hvW⟩ i).val : ℤ),
      (basis_coords' W e v hvW).trans (Finset.sum_congr rfl fun i _ => by rw [hz i]), fun i hi => ?_⟩
    by_contra hne
    have hne' : e.repr ⟨v, hvW⟩ i ≠ 0 := fun h0 => hne (by simp [h0])
    have := hE2 j ⟨v, hvW⟩ ((hWf j _).mpr hvj) i hne'
    omega
  have B1 : IsLayerBasis 0 x1 (fun i => 3 ^ (ht i + 1)) :=
    isLayerBasis_zero_of_socle x1 ht hmono
      (socle_basis (fun i => cl Q 0 (x1 i)) ht hord hind hflag hexp)
  -- the active indices and the second layer
  let act : Fin (Fintype.card B) → Prop := fun i => P (e i) ≠ 0
  let g : {i // act i} → Additive (Layer Q 1) := fun i => P (e i)
  have hg : LinearIndependent (ZMod 3) g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i0
    let c' : Fin (Fintype.card B) → ZMod 3 := fun i => if h : act i then c ⟨i, h⟩ else 0
    have h1 : ∑ j : {i // act i}, c j • g j = ∑ j : {i // act i}, c' j • P (e j) :=
      Finset.sum_congr rfl fun j _ => by simp only [c', dif_pos j.2, g]
    have h2 : ∑ j : {i // act i}, c' j • P (e j) = ∑ i, c' i • P (e i) := by
      rw [← Finset.sum_subtype (Finset.univ.filter act) (fun x => by simp)
        (fun i => c' i • P (e i)), Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : act i
      · rw [if_pos h]
      · rw [if_neg h]; simp [c', h]
    let v : W := ∑ i, c' i • e i
    have hv : v ∈ LinearMap.ker P := by
      rw [LinearMap.mem_ker]
      simp only [v, map_sum, map_smul]
      rw [← h2, ← h1, hc]
    by_contra hne
    have hrep : e.repr v i0 = c i0 := by
      simp only [v, e.repr_sum_self, c', dif_pos i0.2]
    exact i0.2 (hE3 v hv i0 (by rw [hrep]; exact hne))
  have hgs := hg.linearIndepOn_id
  let J := hgs.extend (Set.subset_univ (Set.range g))
  let f0 : Module.Basis J (ZMod 3) (Additive (Layer Q 1)) := Module.Basis.extend hgs
  haveI : Finite J := Module.Finite.finite_basis f0
  letI := Fintype.ofFinite J
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let f : Module.Basis (Fin (Fintype.card J)) (ZMod 3) (Additive (Layer Q 1)) := f0.reindex eJ
  have hf : ∀ k, f k = (eJ.symm k : Additive (Layer Q 1)) := fun k => by
    show (f0.reindex eJ) k = _
    rw [Module.Basis.reindex_apply]
    exact Module.Basis.extend_apply_self hgs _
  have hmemJ : ∀ i (h : act i), P (e i) ∈ J := fun i h =>
    Module.Basis.subset_extend hgs ⟨⟨i, h⟩, rfl⟩
  let σ : Fin (Fintype.card B) → Option (Fin (Fintype.card J)) := fun i =>
    if h : act i then some (eJ ⟨P (e i), hmemJ i h⟩) else none
  have hinj : ∀ i j k, σ i = some k → σ j = some k → i = j := by
    intro i j k hi hj
    simp only [σ] at hi hj
    split_ifs at hi hj with h1 h2
    · rw [← hj, Option.some_inj, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at hi
      have := hg.injective (a₁ := ⟨i, h1⟩) (a₂ := ⟨j, h2⟩) hi
      exact congrArg Subtype.val this
  have hact : ∀ i k, σ i = some k → P (e i) = f k := by
    intro i k hi
    simp only [σ] at hi
    split_ifs at hi with h1
    rw [Option.some_inj] at hi
    rw [hf, ← hi, Equiv.symm_apply_apply]
  have hinact : ∀ i, σ i = none → P (e i) = 0 := by
    intro i hi
    simp only [σ] at hi
    split_ifs at hi with h1
    exact not_not.mp h1
  let x2 : Fin (Fintype.card J) → Q := fun k =>
    if h : ∃ i, σ i = some k then x1 h.choose ^ (3 ^ (ht h.choose + 1)) else L1 (f k)
  have hx2 : ∀ k, x2 k ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 ∧ cl Q 1 (x2 k) = f k := by
    intro k
    by_cases h : ∃ i, σ i = some k
    · simp only [x2, dif_pos h]
      exact ⟨hx1d _, by rw [← hpe, hact _ _ h.choose_spec]⟩
    · simp only [x2, dif_neg h]; exact hL1 (f k)
  have hY : ∀ i k, σ i = some k → x2 k = x1 i ^ (3 ^ (ht i + 1)) := by
    intro i k hik
    have h : ∃ i, σ i = some k := ⟨i, hik⟩
    simp only [x2, dif_pos h]
    rw [hinj _ _ _ h.choose_spec hik]
  have hK : ∀ i, σ i = none → x1 i ^ (3 ^ (ht i + 1)) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := by
    intro i hi
    rw [← cl_eq_zero_iff (hx1d i), ← hpe, hinact i hi]
  have B2 := (isLayerBasis_of_basis (fun k => (hx2 k).1) f (fun k => (hx2 k).2.symm)).1
  let e3 := Module.finBasis (ZMod 3) (Additive (Layer Q 2))
  let x3 : Fin (Module.finrank (ZMod 3) (Additive (Layer Q 2))) → Q := fun l => L2 (e3 l)
  obtain ⟨B3, nf3⟩ := isLayerBasis_of_basis (fun l => (hL2 (e3 l)).1) e3
    (fun l => (hL2 (e3 l)).2.symm)
  -- the structure constants
  let c : Fin (Fintype.card B) → Fin _ → ℤ := fun i =>
    if h : σ i = none then Classical.choose (nf3 _ (hK i h)) else 0
  let dd : Fin (Fintype.card J) → Fin _ → ℤ := fun k => Classical.choose (nf3 _ (h2 _ (hx2 k).1))
  have hαm : ∀ g h, tc (x1 g ^ (3 ^ (ht g + 1))) (x1 h) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 :=
    fun g h => tc_mem (i := 1) (j := 0) (by omega) (hx1d g) (mem_lcs_zero (x1 h))
  let α : Fin (Fintype.card B) → Fin (Fintype.card B) → Fin _ → ℤ := fun g h =>
    Classical.choose (nf3 _ (hαm g h))
  let T : Tahara.Data Q :=
    { s := Fintype.card B, t := Fintype.card J, u := _, x₁ := x1,
      d := fun i => 3 ^ (ht i + 1), x₂ := x2, e := fun _ => 3, x₃ := x3,
      f := fun _ => 3, b := fun i k => if σ i = some k then 1 else 0, c := c, dd := dd, α := α }
  have hvalid : T.Valid := by
    refine ⟨B1, B2, B3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k
      change 0 ≤ (if σ i = some k then (1 : ℤ) else 0) ∧
        (if σ i = some k then (1 : ℤ) else 0) < ((3 : ℕ) : ℤ)
      split_ifs <;> norm_num
    · intro i l
      change 0 ≤ c i l ∧ c i l < ((3 : ℕ) : ℤ)
      simp only [c]
      split_ifs with h
      · have := (Classical.choose_spec (nf3 _ (hK i h))).1 l; exact_mod_cast this
      · norm_num
    · intro k l
      have := (Classical.choose_spec (nf3 _ (h2 _ (hx2 k).1))).1 l; exact_mod_cast this
    · intro g h l _
      have := (Classical.choose_spec (nf3 _ (hαm g h))).1 l
      exact_mod_cast this
    · intro i
      show (oprod x2 (fun k => if σ i = some k then 1 else 0) * oprod x3 (c i))⁻¹ *
        x1 i ^ (3 ^ (ht i + 1)) ∈ _
      by_cases h : σ i = none
      · have hb0' : (fun k => if σ i = some k then (1 : ℤ) else 0) = 0 := by
          funext k; simp [h]
        simp only [c, dif_pos h, hb0', oprod_zero, one_mul]
        exact (Classical.choose_spec (nf3 _ (hK i h))).2
      · obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp h
        have hb1 : (fun k => if σ i = some k then (1 : ℤ) else 0) =
            fun k => if k = ki then 1 else 0 := by
          funext k
          rw [hki]
          by_cases hk : k = ki
          · simp [hk]
          · simp [hk, Ne.symm hk]
        simp only [c, dif_neg h, hb1, oprod_single, hY i ki hki, oprod_zero, mul_one,
          inv_mul_cancel]
        exact one_mem _
    · intro k
      exact (Classical.choose_spec (nf3 _ (h2 _ (hx2 k).1))).2
    · intro g h _
      exact (Classical.choose_spec (nf3 _ (hαm g h))).2
  have hd : ∀ i, T.d i = 3 ∨ T.d i = 9 ∨ 27 ∣ T.d i := by
    intro i
    show 3 ^ (ht i + 1) = 3 ∨ 3 ^ (ht i + 1) = 9 ∨ 27 ∣ 3 ^ (ht i + 1)
    rcases Nat.lt_or_ge (ht i) 2 with h | h
    · interval_cases (ht i) <;> simp
    · right; right
      exact ⟨3 ^ (ht i - 2), by rw [show (27 : ℕ) = 3 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
  have S : SetupGen T σ :=
    ⟨h5, h2, hvalid, hd, fun _ => rfl, fun _ => rfl, hinj, fun _ _ => rfl, hY, hK⟩
  have hle := hT Q h5 T hvalid
  rw [eq_bot_iff]
  refine hle.trans ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨τ, hτ, rfl⟩
  rw [SetLike.mem_coe, S.gen_eq_one hτ]
  exact one_mem _

/-- **`D₅ = γ₅` when `γ₂/γ₃` has exponent `3`, modulo Tahara's Theorem 6.1** (wiki 886,
MATH-443). Let `G/γ₂(G)` be a finite `3`-group and let `γ₂(G)/γ₃(G)` have exponent dividing `3`
(`a³ ∈ γ₃` for `a ∈ γ₂`; equivalently `[x³, y] ∈ γ₃` for all `x, y`). Then `D₅(G) = γ₅(G)`; the
invariants of `G/γ₂(G)` are arbitrary. -/
theorem D_five_eq_gamma_five_exp_L1 (hT : TaharaFiveOne) (G : Type) [Group G]
    (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (h3grp : ∀ x : G, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 := by
  refine le_antisymm (D_le_of_D_quotient_eq_bot _ 5 ?_) (gamma_le_D G 5 (by norm_num))
  haveI : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4) := finite_quotient_lcs hfin 3
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries 4)
  have hmap : ∀ (k : ℕ) (y : G), y ∈ (⊤ : Subgroup G).lowerCentralSeries k →
      π y ∈ (⊤ : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4)).lowerCentralSeries k :=
    fun k y hy => by rw [← lcs_map_mk]; exact Subgroup.mem_map_of_mem _ hy
  refine D_five_eq_bot_of_class_four_exp_L1 hT (lowerCentralSeries_quotient_eq_bot 4)
    (fun x => ?_) (fun a ha => ?_)
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⊤ : Subgroup G).lowerCentralSeries 4) x
    obtain ⟨k, hk⟩ := h3grp x
    exact ⟨k, by rw [← map_pow]; exact hmap 1 _ hk⟩
  · rw [← lcs_map_mk] at ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_pow]
    exact hmap 2 _ (h2 y hy)

/-- Theorem 6.6 (`D_five_eq_gamma_five`) as a special case: `G/γ₂` of exponent `3` gives `h2`. -/
theorem D_five_eq_gamma_five_of_exp_three_of_exp_L1 (hT : TaharaFiveOne) (G : Type) [Group G]
    (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (h1 : ∀ x : G, x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 :=
  D_five_eq_gamma_five_exp_L1 hT G hfin (fun x => ⟨1, by simpa using h1 x⟩)
    (cube_succ (k := 0) (fun a _ => h1 a))

/-- Theorem 6.8 (`D_five_eq_gamma_five_cyclic`) as a special case: cyclic cubes give `h2`
(`cube_L1_of_cubes`). -/
theorem D_five_eq_gamma_five_cyclic_of_exp_L1 (hT : TaharaFiveOne) (G : Type) [Group G]
    (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (h3grp : ∀ x : G, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (t : G)
    (ht : ∀ x : G, ∃ n : ℕ, (t ^ (3 * n))⁻¹ * x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 :=
  D_five_eq_gamma_five_exp_L1 hT G hfin h3grp (cube_L1_of_cubes t ht)

end ExpThree

end GroupDimension
