module

public import GroupDimension.ExpThreePlus

@[expose] public section

/-!
# `D₅ = γ₅` when `γ₂/γ₃` has exponent `3`, for any invariants of `G/γ₂` (MATH-443)

**Theorem** (`D_five_eq_gamma_five_exp_L1`): if `G/γ₂(G)` is a finite `3`-group and
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
              rw [if_neg (fun h => hPj h.2.1)]
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
        rcases hσh : σ h with _ | kh
        · have hP : ¬ P' h := fun hp => hp.1 hσh
          rw [if_neg (fun hc => hP hc.1), hC0 _ (S.hK h hσh), mul_zero]
        · by_cases hh3 : T.d h = 3
          · have hhj : h < j := by
              rcases lt_trichotomy h j with hlt | heq | hgt
              · exact hlt
              · subst heq; omega
              · have := S.d_dvd hgt.le
                rw [hj9, hh3] at this; norm_num at this
            have hP : P' h ∧ h < j := ⟨⟨by simp [hσh], hh3⟩, hhj⟩
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

end ExpThree

end GroupDimension
