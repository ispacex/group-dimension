module

public import GroupDimension.ExpNine

@[expose] public section

/-!
# `D₅ = γ₅` when `γ₄³ ⊆ γ₅` (Theorem B, MATH-444 step 2)

**Theorem B** (`D_five_eq_gamma_five_g4_cube`): if `G/γ₂(G)` is a finite `3`-group and
`γ₄(G)³ ⊆ γ₅(G)`, then `D₅(G) = γ₅(G)`. The finite form (`D_five_eq_bot_of_class_four_g4_cube`): a
finite group `Q` of class `≤ 4` with `Q/γ₂` a `3`-group and `c³ = 1` for `c ∈ γ₄` has `D₅(Q) = 1`.
It contains Theorem 6.10 (`ExpNine.lean`, which needs `γ₂⁹ ⊆ γ₄` in addition) and Theorem 6.9.
As there, Tahara's Theorem 6.1 (`TaharaFiveOne`) is an explicit hypothesis, discharged in
`TaharaTheorem.lean`.

The proof follows the wiki page of MATH-444, step 2 (MATH page 891, §2–§4):

* the expansion `[xⁿ, y] = cⁿ [c, x]^{n choose 2} [c, x, x]^{n choose 3}` in class `≤ 4`
  (`tc_pow_formula`) and the "defect of antisymmetry"
  `Δ = [xⁿ, y][yⁿ, x]` for `n = 3^{m+1}` (`delta_formula`), which lies in `γ₄`;
* the row identity (`SetupB.rowB`): conditions (B) and (E) of a row `r` (any order `d(r)`), paired
  with `x_r`, give `∑_k v_{rk} d(r) [x_{2k}, x_r] + ∑_h crow_{rh} [x_h^{d(h)}, x_r] = 0` exactly in
  the abelian group `γ₃` (for any map additive on `γ₃`);
* summing the row identities over all rows, `2 g(τ)` becomes `∑_{i<h} u_{ih} Δ_{ih}` plus
  `∑_r [R_r, Y_r] + 2 V`; the latter vanishes by condition (F), the former term by term
  (conditions (C) and (B) modulo `3` and the basis adapted to the kernel of the cube map,
  `SetupB.delta_pow_eq_one`); the `w`-part is trivial as in Theorem 6.10.

The route differs slightly from `(⋆)` of the wiki page: the `w`-part is shown trivial directly
(`genC_eq`, conditions (D) modulo `3`), and condition (E) is used modulo `3` inside the row identity
(`Erow`), so the terms `T₂`–`T₅` of `(⋆)` never appear; only `T₁` (`delta_pow_eq_one`) and the
`v`-part (`Vpart`, which also uses (F₁)) are evaluated.
-/

namespace GroupDimension

namespace ExpThree

open Subgroup Tahara ClassFour
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Identities in class `≤ 4` -/

section Expansion

variable (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
include h5

/-- (K2): `[xⁿ, y] = cⁿ fⁿᶜ² gⁿᶜ³` with `c = [x, y]`, `f = [c, x]`, `g = [f, x]`. -/
theorem tc_pow_formula (x y : G) (n : ℕ) :
    tc (x ^ n) y = tc x y ^ n * tc (tc x y) x ^ (n.choose 2) *
      tc (tc (tc x y) x) x ^ (n.choose 3) := by
  obtain ⟨c, hc⟩ : ∃ c, c = tc x y := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = tc c x := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = tc f x := ⟨_, rfl⟩
  rw [← hc, ← hf, ← hg]
  have hc1 : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    hc ▸ tc_mem (by omega) (mem_lcs_zero x) (mem_lcs_zero y)
  have hf2 : f ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    hf ▸ tc_mem (by omega) hc1 (mem_lcs_zero x)
  have hg3 : g ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    hg ▸ tc_mem (by omega) hf2 (mem_lcs_zero x)
  have hgz : ∀ z : G, Commute z g := fun z => central_L3 h5 hg3 z
  have hcf : Commute c f :=
    commutatorElement_eq_one_iff_mul_comm.mp (comm_eq_one h5 (by norm_num) hc1 hf2)
  have hc' : x⁻¹ * c * x = c * f := by rw [hf, tc]; group
  have hf' : x⁻¹ * f * x = f * g := by rw [hg, tc]; group
  have hg' : x⁻¹ * g * x = g := by
    rw [mul_assoc, ← (hgz x).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hconj : ∀ (b : G) (k : ℕ), x⁻¹ * b ^ k * x = (x⁻¹ * b * x) ^ k := fun b k => by
    simpa using (conj_pow (a := x⁻¹) (b := b) (i := k)).symm
  have hm : ∀ p q : G, x⁻¹ * (p * q) * x = (x⁻¹ * p * x) * (x⁻¹ * q * x) := fun p q => by group
  induction n with
  | zero => simp [tc]
  | succ n ih =>
    have e : tc (x ^ (n + 1)) y = x⁻¹ * tc (x ^ n) y * x * tc x y := by
      rw [pow_succ]; exact tc_mul_left _ _ _
    have e2 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    have e3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ']
    rw [e, ih, ← hc, hm, hm, hconj, hconj, hconj, hc', hf', hg', hcf.mul_pow, (hgz f).mul_pow,
      e2, e3, pow_succ, pow_add, pow_add]
    have hG : Commute (g ^ n.choose 2 * g ^ n.choose 3) c :=
      ((hgz c).symm.pow_left _).mul_left ((hgz c).symm.pow_left _)
    have hF : Commute (f ^ n * f ^ n.choose 2) c :=
      (hcf.symm.pow_left _).mul_left (hcf.symm.pow_left _)
    calc c ^ n * f ^ n * (f ^ n.choose 2 * g ^ n.choose 2) * g ^ n.choose 3 * c
        = c ^ n * (f ^ n * f ^ n.choose 2) * ((g ^ n.choose 2 * g ^ n.choose 3) * c) := by group
      _ = c ^ n * ((f ^ n * f ^ n.choose 2) * c) * (g ^ n.choose 2 * g ^ n.choose 3) := by
          rw [hG.eq]; group
      _ = c ^ n * (c * (f ^ n * f ^ n.choose 2)) * (g ^ n.choose 2 * g ^ n.choose 3) := by
          rw [hF.eq]
      _ = c ^ n * c * (f ^ n * f ^ n.choose 2) * (g ^ n.choose 2 * g ^ n.choose 3) := by group

/-- `[aⁿ, x] = [a, x]ⁿ` for `a ∈ γ₂`. -/
theorem tc_pow_left_L1 {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) (n : ℕ) :
    tc (a ^ n) x = tc a x ^ n := by
  induction n with
  | zero => simp [tc]
  | succ n ih => rw [pow_succ, tc_mul_left_L1 h5 (pow_mem ha n) ha, ih, pow_succ]

/-- `[c, aⁿ] = [c, a]ⁿ` for `c, a ∈ γ₂`. -/
theorem tc_pow_right_L1 {c a : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (n : ℕ) : tc c (a ^ n) = tc c a ^ n := by
  induction n with
  | zero => simp [tc]
  | succ n ih =>
    have hz : tc c (a ^ n) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (by omega) hc (pow_mem ha n)
    have hconj : a⁻¹ * tc c (a ^ n) * a = tc c (a ^ n) := by
      rw [mul_assoc, ← central_L3 h5 hz a]; group
    rw [pow_succ, tc_mul_right, hconj, ih, ← pow_succ']

variable (h4 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 3, c ^ 3 = 1)
include h4

/-- `[Y, x^{3^m}] = [Y, x]^{3^m}` for `Y ∈ γ₂` when `γ₄³ = 1` (I4, iterated). -/
theorem tc_pow3_right {Y : G} (hY : Y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) (m : ℕ) :
    tc Y (x ^ (3 ^ m)) = tc Y x ^ (3 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, tc_pow_three_rightA h5 h4 hY, ih, ← pow_mul]

omit h5 h4 in
theorem choose2_eq (m : ℕ) : (3 ^ (m + 1)).choose 2 = 3 ^ (m + 1) * ((3 ^ (m + 1) - 1) / 2) := by
  rw [Nat.choose_two_right]
  have hodd : Odd (3 ^ (m + 1)) := Odd.pow (by decide)
  have h2 : 2 ∣ 3 ^ (m + 1) - 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]; omega
  exact Nat.mul_div_assoc _ h2

omit h5 h4 in
theorem three_dvd_choose3 (m : ℕ) : 3 ∣ (3 ^ (m + 1 + 1)).choose 3 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (3 ^ (m + 1 + 1)) 3
  have hd : (3 ^ (m + 1 + 1)).descFactorial 3 =
      (3 ^ (m + 1 + 1) - 2) * ((3 ^ (m + 1 + 1) - 1) * ((3 ^ (m + 1 + 1) - 0) * 1)) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  have h9 : 9 ∣ (3 ^ (m + 1 + 1)).descFactorial 3 := by
    rw [hd]
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _) _
    rw [Nat.sub_zero]
    exact ⟨3 ^ m, by ring⟩
  rw [h] at h9
  have : (3 : ℕ).factorial = 6 := rfl
  rw [this] at h9
  omega

/-- The defect of antisymmetry `Δ = [xⁿ, y][yⁿ, x]` for `n = 3^{m+1}`. -/
theorem delta_formula (x y : G) (m : ℕ) :
    tc (x ^ (3 ^ (m + 1))) y * tc (y ^ (3 ^ (m + 1))) x =
      tc (tc x y) (x ^ (3 ^ (m + 1))) ^ ((3 ^ (m + 1) - 1) / 2) *
        tc (tc (tc x y) x) x ^ ((3 ^ (m + 1)).choose 3) *
      (tc (tc y x) (y ^ (3 ^ (m + 1))) ^ ((3 ^ (m + 1) - 1) / 2) *
        tc (tc (tc y x) y) y ^ ((3 ^ (m + 1)).choose 3)) := by
  have hc1 : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero x) (mem_lcs_zero y)
  have hc1' : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero y) (mem_lcs_zero x)
  rw [tc_pow_formula h5 x y, tc_pow_formula h5 y x, choose2_eq, pow_mul, pow_mul,
    ← tc_pow3_right h5 h4 hc1, ← tc_pow3_right h5 h4 hc1']
  -- `[y, x] = [x, y]⁻¹`, and the `γ₃`-part commutes with `γ₂`
  have hinv : tc y x = (tc x y)⁻¹ := (tc_inv x y).symm
  have key : ∀ (c F₁ G₁ F₂ G₂ : G) (n : ℕ), Commute (F₁ * G₁) (c⁻¹ ^ n) →
      c ^ n * F₁ * G₁ * (c⁻¹ ^ n * F₂ * G₂) = F₁ * G₁ * (F₂ * G₂) := by
    intro c F₁ G₁ F₂ G₂ n h
    calc c ^ n * F₁ * G₁ * (c⁻¹ ^ n * F₂ * G₂) = c ^ n * ((F₁ * G₁) * c⁻¹ ^ n) * (F₂ * G₂) := by
          group
      _ = c ^ n * (c⁻¹ ^ n * (F₁ * G₁)) * (F₂ * G₂) := by rw [h.eq]
      _ = F₁ * G₁ * (F₂ * G₂) := by rw [inv_pow]; group
  have hX2 : tc (tc x y) (x ^ (3 ^ (m + 1))) ^ ((3 ^ (m + 1) - 1) / 2) *
      tc (tc (tc x y) x) x ^ ((3 ^ (m + 1)).choose 3) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    refine mul_mem (pow_mem ?_ _) (pow_mem ?_ _)
    · exact tc_mem (i := 1) (j := 0) (by omega) hc1 (mem_lcs_zero _)
    · exact lcs_mem_of_le (show 2 ≤ 3 by norm_num) (tc_mem (i := 2) (j := 0) (n := 3) (by omega)
        (tc_mem (by omega) hc1 (mem_lcs_zero x)) (mem_lcs_zero x))
  have hcomm := commutatorElement_eq_one_iff_mul_comm.mp
      (comm_eq_one h5 (by norm_num) hX2 (pow_mem (inv_mem hc1) (3 ^ (m + 1))))
  rw [hinv]
  exact key _ _ _ _ _ _ hcomm

/-- `Δ ∈ γ₄` when `xⁿ, yⁿ ∈ γ₂`. -/
theorem delta_mem {x y : G} {m : ℕ} (hx : x ^ (3 ^ (m + 1)) ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hy : y ^ (3 ^ (m + 1)) ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc (x ^ (3 ^ (m + 1))) y * tc (y ^ (3 ^ (m + 1))) x ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  have hc1 : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero x) (mem_lcs_zero y)
  have hc1' : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero y) (mem_lcs_zero x)
  rw [delta_formula h5 h4]
  refine mul_mem (mul_mem (pow_mem (tc_mem (by omega) hc1 hx) _) (pow_mem ?_ _))
    (mul_mem (pow_mem (tc_mem (by omega) hc1' hy) _) (pow_mem ?_ _))
  · exact tc_mem (i := 2) (j := 0) (by omega) (tc_mem (by omega) hc1 (mem_lcs_zero x)) (mem_lcs_zero x)
  · exact tc_mem (i := 2) (j := 0) (by omega) (tc_mem (by omega) hc1' (mem_lcs_zero y)) (mem_lcs_zero y)

/-- `Δ = 1` when `9 ∣ n` and `[[x, y], xⁿ] = [[y, x], yⁿ] = 1`. -/
theorem delta_one {x y : G} {m : ℕ}
    (h1 : tc (tc x y) (x ^ (3 ^ (m + 1 + 1))) = 1) (h2 : tc (tc y x) (y ^ (3 ^ (m + 1 + 1))) = 1) :
    tc (x ^ (3 ^ (m + 1 + 1))) y * tc (y ^ (3 ^ (m + 1 + 1))) x = 1 := by
  have hc1 : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero x) (mem_lcs_zero y)
  have hc1' : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (by omega) (mem_lcs_zero y) (mem_lcs_zero x)
  rw [delta_formula h5 h4 x y (m + 1), h1, h2]
  simp only [one_pow, one_mul]
  obtain ⟨k, hk⟩ := three_dvd_choose3 m
  have g1 := h4 _ (tc_mem (i := 2) (j := 0) (by omega) (tc_mem (by omega) hc1 (mem_lcs_zero x))
    (mem_lcs_zero x))
  have g2 := h4 _ (tc_mem (i := 2) (j := 0) (by omega) (tc_mem (by omega) hc1' (mem_lcs_zero y))
    (mem_lcs_zero y))
  rw [hk, pow_mul, pow_mul, g1, g2]
  simp

end Expansion

/-! ## Maps with values in an abelian group: products -/

theorem addMapG_ofFn {M : Type*} [AddCommGroup M] {S : Subgroup G} {A : G → M}
    (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {n : ℕ} (f : Fin n → G)
    (hf : ∀ i, f i ∈ S) : A (List.ofFn f).prod = ∑ i, A (f i) := by
  have : ∀ l : List G, (∀ y ∈ l, y ∈ S) → A l.prod = (l.map A).sum := by
    intro l
    induction l with
    | nil => intro _; simp [addMapG_one hA]
    | cons y l ih =>
      intro hl
      rw [List.prod_cons, hA _ (hl y List.mem_cons_self) _
        (list_prod_mem fun z hz => hl z (List.mem_cons_of_mem _ hz)),
        ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.sum_cons]
  rw [this _ (fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; exact hf i), List.map_ofFn,
    List.sum_ofFn]
  rfl

/-! ## The computation -/

/-- The situation of the proof of Theorem B: class `≤ 4`, `γ₄³ = 1`, `γ₃` a `3`-group, the
orders of the first layer powers `3^{m+1}`, those of the second and third layers divisible by `3`.
`act i` says that `x_i` is *active*; an inactive `x_i` has `x_i^{d(i)} ∈ γ₂³γ₃`, and the
coefficients of combinations of the classes `x_h^{d(h)}` modulo `3 L₂` are seen at the active
indices (`hind`). -/
structure SetupB (T : Data G) (act : Fin T.s → Prop) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  h4 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 3, c ^ 3 = 1
  htor : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1
  valid : T.Valid
  hd : ∀ i, ∃ m : ℕ, T.d i = 3 ^ (m + 1)
  he : ∀ k, 3 ∣ T.e k
  hf : ∀ l, 3 ∣ T.f l
  hK : ∀ i, ¬ act i → ∃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, T.x₁ i ^ T.d i = a ^ 3 * c
  hind : ∀ cf : Fin T.s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * T.b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h

namespace SetupB

variable {T : Data G} {act : Fin T.s → Prop} (S : SetupB T act)
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

/-- For an inactive `h`, `[c, x_h^{d(h)}] = 1` for `c ∈ γ₂`. -/
theorem tcK_right {h : Fin T.s} (hh : ¬ act h) {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    tc c (T.x₁ h ^ T.d h) = 1 := by
  obtain ⟨a, ha, e, he, hY⟩ := S.hK h hh
  have hce : tc c e = 1 := by
    rw [← tc_inv, tc_L2_L1 S.h5 he hc, inv_one]
  rw [hY, tc_mul_right, hce, one_mul, tc_pow_right_L1 S.h5 hc ha, S.h4 _ (tc_mem (by omega) hc ha)]
  group

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

/-- Condition (E) in any row `r`, modulo `3`: `∑_k v'_{rk} d_{kl} ≡ ∑_h crow_{rh} c_{hl}`. -/
theorem Erow (r : Fin T.s) (l : Fin T.u) :
    (3 : ℤ) ∣ (∑ k, τ.v' r k * T.dd k l) - ∑ h, crow T τ r h * T.c h l := by
  have h' := dvd3_mod (hτ.E r l) (S.gcd_f3 r l)
  have s1 : (3 : ℤ) ∣ ∑ h, if h < r then τ.u h r * T.q h r * T.α h r l else 0 :=
    dvd_sum_ite _ _ fun h hh => (S.uq3 hτ hh).mul_right _
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

omit S in
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

/-- **The row identity** (wiki page 891, Lemma 1): for every row `r` and every map `A` additive
on `γ₃`, `∑_k v_{rk} d(r) A[x_{2k}, x_r] + ∑_h crow_{rh} A[x_h^{d(h)}, x_r] = 0`. -/
theorem rowB (r : Fin T.s) {N : Type*} [AddCommGroup N] {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) +
      ∑ h, crow T τ r h • A (tc (T.x₁ h ^ T.d h) (T.x₁ r)) = 0 := by
  classical
  -- the map `Φ = A [·, x_r]`, additive on `γ₂`, zero on `γ₄`
  let Φ : G → N := fun g => A (tc g (T.x₁ r))
  have hΦadd : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1, Φ (a * b) = Φ a + Φ b := by
    intro a ha b hb
    simp only [Φ]
    rw [tc_mul_left_L1 S.h5 ha hb, hA _ (tc_mem (by omega) ha (mem_lcs_zero _)) _
      (tc_mem (by omega) hb (mem_lcs_zero _))]
  have hΦ3 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, Φ a = 0 := by
    intro a ha
    simp only [Φ]
    rw [tc_L3 S.h5 ha]; exact addMapG_one hA
  have hΦrem : ∀ {y : G} {a : Fin T.u → ℤ}, (oprod T.x₃ a)⁻¹ * y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 → Φ y = ∑ l, a l • Φ (T.x₃ l) := by
    intro y a hy hy1
    have ho : oprod T.x₃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _
    rw [← mul_inv_cancel_left (oprod T.x₃ a) y, hΦadd _ ho _ (lcs_mem_of_le (by norm_num) hy),
      hΦ3 _ hy, add_zero, addMapG_oprod hΦadd (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l))]
  -- `3 Φ(x_{3l}) = 0`
  have h3l : ∀ l, (3 : ℤ) • Φ (T.x₃ l) = 0 := by
    intro l
    have hz : tc (T.x₃ l) (T.x₁ r) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (by omega) (S.x3mem l) (mem_lcs_zero _)
    have := addMapG_pow hA (lcs_mem_of_le (by norm_num) hz) 3
    rw [S.h4 _ hz, addMapG_one hA] at this
    simpa [Φ] using this.symm
  -- `Φ(x_h^{d(h)}) = ∑_k b_{hk} Φ(x_{2k}) + Φ(ȳ_h)`
  have hY : ∀ h, ∑ k, T.b h k • Φ (T.x₂ k) = Φ (T.x₁ h ^ T.d h) - Φ (oprod T.x₃ (T.c h)) := by
    intro h
    have hv := S.valid.hb h
    have hb1 : oprod T.x₂ (T.b h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := oprod_mem S.x2mem _
    have hc1 : oprod T.x₃ (T.c h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _
    have hn1 := lcs_mem_of_le (show 1 ≤ 3 by norm_num) hv
    rw [← addMapG_oprod (A := Φ) hΦadd S.x2mem (T.b h), ← mul_inv_cancel_left
      (oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h)) (T.x₁ h ^ T.d h),
      hΦadd _ (mul_mem hb1 hc1) _ hn1, hΦ3 _ hv, add_zero, hΦadd _ hb1 _ hc1]
    abel
  -- the element `A_r = ∏_k (x_{2k}^{e(k)})^{v'_{rk}}` of `γ₃`
  have hA3 : oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    oprod_mem S.x2e _
  have hM : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) +
      ∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) + ∑ h, crow T τ r h • Φ (T.x₁ h ^ T.d h) =
      ∑ h, crow T τ r h • Φ (oprod T.x₃ (T.c h)) := by
    have hAk : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) =
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
            Finset.sum_congr rfl fun k _ => by rw [SetupB.Brow hτ r k]; congr 1; ring
        _ = -∑ h, crow T τ r h • ∑ k, T.b h k • Φ (T.x₂ k) := by
            simp only [neg_smul, Finset.sum_smul, Finset.sum_neg_distrib, Finset.smul_sum,
              smul_smul]
            rw [Finset.sum_comm]
    rw [hAk, hsum]
    simp_rw [hY, smul_sub, Finset.sum_sub_distrib]
    abel
  -- (E) modulo `3`: `Φ(A_r) = ∑_h crow_{rh} Φ(ȳ_h)`
  have hE : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) =
      ∑ h, crow T τ r h • Φ (oprod T.x₃ (T.c h)) := by
    have hAk : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) =
        ∑ l, (∑ k, τ.v' r k * T.dd k l) • Φ (T.x₃ l) := by
      have hd' : ∀ k, Φ (T.x₂ k ^ T.e k) = ∑ l, T.dd k l • Φ (T.x₃ l) := fun k =>
        hΦrem (S.valid.hdd k) (lcs_mem_of_le (by norm_num) (S.x2e k))
      rw [addMapG_oprod hΦadd (fun k => lcs_mem_of_le (by norm_num) (S.x2e k))]
      simp_rw [hd', Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have hc : ∀ h, Φ (oprod T.x₃ (T.c h)) = ∑ l, T.c h l • Φ (T.x₃ l) := fun h =>
      hΦrem (by rw [inv_mul_cancel]; exact one_mem _)
        (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _)
    simp_rw [hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, hAk]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul]
    obtain ⟨q, hq⟩ := S.Erow hτ r l
    have e : (∑ k, τ.v' r k * T.dd k l) = (∑ h, crow T τ r h * T.c h l) + 3 * q := by
      rw [← hq]; ring
    rw [e, add_smul, show ((3 : ℤ) * q) • Φ (T.x₃ l) = q • ((3 : ℤ) • Φ (T.x₃ l)) by
      rw [smul_smul, mul_comm], h3l, smul_zero, add_zero]
  rw [hE] at hM
  have : ∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) + ∑ h, crow T τ r h • Φ (T.x₁ h ^ T.d h) = 0 := by
    have := hM
    rw [add_assoc] at this
    exact (add_eq_left.mp this)
  exact this

/-- The defect `Δ_{ij}^{u_{ij}} = 1` for `i < j`: if `d(i) = d(j)` or `x_j` is active, `3 ∣ u_{ij}`
and `Δ ∈ γ₄`; otherwise `Δ = 1` (the pairings with `x_i^{d(j)} = (x_i^{d(i)})^q`, `3 ∣ q`, and
with the inactive `x_j^{d(j)}` vanish). -/
theorem delta_pow_eq_one {i j : Fin T.s} (hij : i < j) :
    (tc (T.x₁ i ^ T.d j) (T.x₁ j) * tc (T.x₁ j ^ T.d j) (T.x₁ i)) ^ τ.u i j = 1 := by
  obtain ⟨m, hm⟩ := S.hd j
  have hxi : T.x₁ i ^ T.d j ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    rw [← S.d_mul_q hij.le, pow_mul]; exact pow_mem (S.Y1 i) _
  have hxj : T.x₁ j ^ T.d j ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := S.Y1 j
  have hmem : tc (T.x₁ i ^ T.d j) (T.x₁ j) * tc (T.x₁ j ^ T.d j) (T.x₁ i) ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [hm] at hxi hxj ⊢; exact delta_mem S.h5 S.h4 hxi hxj
  by_cases h3 : (3 : ℤ) ∣ τ.u i j
  · obtain ⟨k, hk⟩ := h3
    rw [hk, zpow_mul, zpow_ofNat, S.h4 _ hmem, one_zpow]
  · have hne : T.d i ≠ T.d j := fun hd => h3 (S.u3_eq hτ hij hd)
    have hj : ¬ act j := by
      intro hj
      apply h3
      have := S.crow_act hτ i hj
      simpa [crow, hij, not_lt.mpr hij.le] using this
    -- `m ≥ 1`
    obtain ⟨a, ha⟩ := S.hd i
    have hm1 : 1 ≤ m := by
      have hdv := S.d_dvd hij.le
      rw [ha, hm] at hdv hne
      have hab : a + 1 ≤ m + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdv
      have : a + 1 ≠ m + 1 := fun h => hne (by rw [h])
      omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm] at hmem
    have hc1 : tc (T.x₁ i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have hc1' : tc (T.x₁ j) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      tc_mem (by omega) (mem_lcs_zero _) (mem_lcs_zero _)
    have h1 : tc (tc (T.x₁ i) (T.x₁ j)) (T.x₁ i ^ (3 ^ (m' + 1 + 1))) = 1 := by
      obtain ⟨q, hq⟩ := S.three_dvd_q hij.le hne
      have e : T.x₁ i ^ (3 ^ (m' + 1 + 1)) = ((T.x₁ i ^ T.d i) ^ 3) ^ q := by
        rw [← pow_mul, ← pow_mul, ← hq, S.d_mul_q hij.le, hm]
      rw [e, tc_pow_right_L1 S.h5 hc1 (pow_mem (S.Y1 i) 3), tc_pow_right_L1 S.h5 hc1 (S.Y1 i),
        S.h4 _ (tc_mem (by omega) hc1 (S.Y1 i)), one_pow]
    have h2 : tc (tc (T.x₁ j) (T.x₁ i)) (T.x₁ j ^ (3 ^ (m' + 1 + 1))) = 1 := by
      rw [← hm]; exact S.tcK_right hj hc1'
    rw [hm, delta_one S.h5 S.h4 h1 h2, one_zpow]


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

omit hτ in
theorem memB (i : Fin T.s) (k : Fin T.t) (v : ℤ) : (List.ofFn fun l => if k < l then
    tc (T.x₂ l) (T.x₂ k) ^ T.b i l else 1).prod ^ v ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  refine zpow_mem (list_prod_mem fun y hy => ?_) _
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
  split_ifs
  · exact zpow_mem (tc_mem (by omega) (S.x2mem l) (S.x2mem k)) _
  · exact one_mem _

omit hτ in
theorem genB_mem : T.genB τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  unfold Data.genB
  exact list_prod_mem fun y hy => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact list_prod_mem fun y hy => by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact S.memB i k _

omit hτ in
theorem genA_mem : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  unfold Data.genA
  exact list_prod_mem fun y hy => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact list_prod_mem fun y hy => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      split_ifs
      · exact zpow_mem (tc_mem (by omega) (S.Y1 i) (mem_lcs_zero _)) _
      · exact one_mem _

omit hτ in
/-- `[x_{2k}, x_r]^{d(r)} = [x_{2k}, x_r^{d(r)}] ∈ γ₄`. -/
theorem tc2_pow_d (r : Fin T.s) (k : Fin T.t) :
    tc (T.x₂ k) (T.x₁ r) ^ T.d r = tc (T.x₂ k) (T.x₁ r ^ T.d r) := by
  obtain ⟨m, hm⟩ := S.hd r
  rw [hm]; exact (tc_pow3_right S.h5 S.h4 (S.x2mem k) _ _).symm

/-- **The `v`-part** (wiki page 891, Lemma 2): `∑_r [R_r, x_r^{d(r)}] + 2V = 0`, i.e. for every
map `A` additive on `γ₃`, `∑_{r,k} v_{rk} d(r) A[x_{2k}, x_r] + 2 A(genB) = 0`. -/
theorem Vpart {N : Type*} [AddCommGroup N] {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    ∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) + (2 : ℤ) • A (T.genB τ) = 0 := by
  classical
  have hle34 : (⊤ : Subgroup G).lowerCentralSeries 4 ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have ht3 : ∀ r k, tc (T.x₂ k) (T.x₁ r) ^ T.d r ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro r k; rw [S.tc2_pow_d r k]; exact tc_mem (by omega) (S.x2mem k) (S.Y1 r)
  have htv : ∀ r k, (tc (T.x₂ k) (T.x₁ r) ^ T.d r) ^ τ.v r k ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun r k => zpow_mem (ht3 r k) _
  have hrow : ∀ r, (List.ofFn fun k => (tc (T.x₂ k) (T.x₁ r) ^ T.d r) ^ τ.v r k).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 3 := fun r =>
    list_prod_mem fun y hy => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact htv r k
  let P0 : G := (List.ofFn fun r => (List.ofFn fun k => (tc (T.x₂ k) (T.x₁ r) ^ T.d r) ^ τ.v r k).prod).prod
  have hP0 : P0 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    list_prod_mem fun y hy => by obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy; exact hrow r
  have hgB := S.genB_mem (τ := τ)
  let P : G := P0 * (T.genB τ * T.genB τ)
  have hP3 : P ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := mul_mem hP0 (mul_mem hgB hgB)
  -- `P = 1`, by the computation modulo `3` of the proof of Theorem 6.10
  have hP1 : P = 1 := by
    have key : P ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := by
      refine mem_of_forall_F (p := 3) ((⊤ : Subgroup G).lowerCentralSeries 3)
        ((⊤ : Subgroup G).lowerCentralSeries 4) hle34
        (fun a ha b _ => commutator_mem_lcs (i := 3) (j := 0) (by omega) ha (mem_lcs_zero b))
        (fun z hz => by rw [S.h4 z hz]; exact one_mem _) hP3 ?_
      intro F hF _
      let β' : Fin T.s → Fin T.t → ZMod 3 := fun i k => F (tc (T.x₁ i ^ T.d i) (T.x₂ k))
      have hFt : ∀ r k, F (tc (T.x₂ k) (T.x₁ r) ^ T.d r) = -β' r k := by
        intro r k
        have hz : tc (T.x₁ r ^ T.d r) (T.x₂ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
          tc_mem (by omega) (S.Y1 r) (S.x2mem k)
        simp only [β']
        rw [S.tc2_pow_d r k, ← tc_inv, addMap_inv hF hz]
      have FP0 : F P0 = ∑ r, ∑ k, (τ.v r k : ZMod 3) * -β' r k := by
        simp only [P0]
        rw [addMap_ofFn hF _ hrow]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [addMap_ofFn hF _ (htv r)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [addMap_zpow hF (ht3 r k), hFt]
      -- the `v`-part: `2 F(genB) = ∑_{i,k} v_{ik} β'_{ik}`
      let γ : Fin T.t → Fin T.t → ZMod 3 := fun l k => F (tc (T.x₂ l) (T.x₂ k))
      let N : Fin T.t → Fin T.t → ZMod 3 := fun l k => ∑ i, (τ.v i k : ZMod 3) * (T.b i l : ZMod 3)
      have FB0 : F (T.genB τ) =
          ∑ i, ∑ k, (τ.v i k : ZMod 3) * ∑ l, (if k < l then (T.b i l : ZMod 3) * γ l k else 0) := by
        unfold Data.genB
        rw [addMap_ofFn hF _ fun i => list_prod_mem fun y hy => by
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact S.memB i k _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [addMap_ofFn hF _ (fun k => S.memB i k _)]
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
          addMap_mul_mem (A := fun a => F (tc a (T.x₂ k)))
            (show (⊤ : Subgroup G).lowerCentralSeries 2 ≤ (⊤ : Subgroup G).lowerCentralSeries 1
              from (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)) hAk hA0
            (mul_mem hb1 (lcs_mem_of_le (by norm_num) hc2)) (lcs_mem_of_le (by norm_num) hv),
          hAk _ hb1 _ (lcs_mem_of_le (by norm_num) hc2), hA0 _ hc2, add_zero,
          addMap_oprod (A := fun a => F (tc a (T.x₂ k))) hAk S.x2mem]
      have FB : 2 * F (T.genB τ) = ∑ i, ∑ k, (τ.v i k : ZMod 3) * β' i k := by
        rw [FB1, ← hsk]
        simp only [true_and, ↓reduceIte]
        calc ∑ l, ∑ k, N l k * γ l k =
              ∑ l, ∑ k, ∑ i, (τ.v i k : ZMod 3) * ((T.b i l : ZMod 3) * γ l k) :=
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
      simp only [P]
      rw [hF _ hP0 _ (mul_mem hgB hgB), hF _ hgB _ hgB, FP0]
      have h2 : F (T.genB τ) + F (T.genB τ) = 2 * F (T.genB τ) := by ring
      rw [h2, FB]
      simp only [mul_neg, Finset.sum_neg_distrib, neg_add_cancel]
    rwa [S.h5, mem_bot] at key
  -- evaluate `A(P)`
  have hAP : A P = ∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) +
      (2 : ℤ) • A (T.genB τ) := by
    have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
    simp only [P, P0]
    rw [hA _ (h32 hP0) _ (h32 (mul_mem hgB hgB)), hA _ (h32 hgB) _ (h32 hgB), two_smul,
      addMapG_ofFn hA _ (fun r => h32 (hrow r))]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [addMapG_ofFn hA _ (fun k => h32 (htv r k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [addMapG_zpow hA (h32 (ht3 r k)), addMapG_pow hA (tc_mem (by omega) (S.x2mem k) (mem_lcs_zero _)),
      smul_smul]
  rw [← hAP, hP1, addMapG_one hA]

/-- **`2 g(τ) = 0`** for every map `A` additive on `γ₃` (wiki page 891, `(⋆)` and §4, in the
variant of the module docstring). -/
theorem two_smul_gen {N : Type*} [AddCommGroup N] {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) :
    (2 : ℤ) • A (T.gen τ) = 0 := by
  classical
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have hY2 : ∀ i j, tc (T.x₁ i ^ T.d i) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    fun i j => tc_mem (by omega) (S.Y1 i) (mem_lcs_zero _)
  have hfacA : ∀ i j, (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := by
    intro i j; split_ifs
    · exact zpow_mem (hY2 i j) _
    · exact one_mem _
  have hrowA : ∀ i, (List.ofFn fun j => if i < j then
      tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1).prod ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := fun i =>
    list_prod_mem fun y hy => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact hfacA i j
  have hgA := S.genA_mem (τ := τ)
  have hgB := h32 (S.genB_mem (τ := τ))
  have hAgen : A (T.gen τ) = A (T.genA τ) + A (T.genB τ) := by
    rw [Data.gen, S.genC_eq hτ, mul_one, hA _ hgA _ hgB]
  let a : Fin T.s → Fin T.s → N := fun h r => A (tc (T.x₁ h ^ T.d h) (T.x₁ r))
  have hAA : A (T.genA τ) = ∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) • a i j else 0 := by
    unfold Data.genA
    rw [addMapG_ofFn hA _ hrowA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [addMapG_ofFn hA _ (hfacA i)]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · exact addMapG_zpow hA (hY2 i j) _
    · exact addMapG_one hA
  let V : N := ∑ r, ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r))
  -- the row identities, summed
  have hrows : ∑ r, ∑ h, crow T τ r h • a h r = -V := by
    simp only [V]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact eq_neg_of_add_eq_zero_right (S.rowB hτ r hA)
  have hcrow : ∑ r, ∑ h, crow T τ r h • a h r =
      (∑ r, ∑ h, if r < h then τ.u r h • a h r else 0) - A (T.genA τ) := by
    rw [hAA, Finset.sum_comm (f := fun i j => if i < j then (τ.u i j * T.q i j) • a i j else 0),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [crow, sub_smul]
    by_cases h1 : r < h <;> by_cases h2 : h < r <;>
      simp only [h1, h2, ↓reduceIte, zero_smul, sub_zero, zero_sub, sub_self]
  have hgA' : A (T.genA τ) = (∑ r, ∑ h, if r < h then τ.u r h • a h r else 0) + V := by
    have e := hcrow.symm.trans hrows
    calc A (T.genA τ) = (∑ r, ∑ h, if r < h then τ.u r h • a h r else 0) -
          ((∑ r, ∑ h, if r < h then τ.u r h • a h r else 0) - A (T.genA τ)) := by abel
      _ = _ := by rw [e]; abel
  -- the pairs `i < j`
  have hpair : ∀ i j, i < j → (τ.u i j * T.q i j) • a i j + τ.u i j • a j i = 0 := by
    intro i j hij
    have e1 : T.x₁ i ^ T.d j = (T.x₁ i ^ T.d i) ^ (T.d j / T.d i) := by
      rw [← pow_mul, S.d_mul_q hij.le]
    have ht1 : tc (T.x₁ i ^ T.d j) (T.x₁ j) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      tc_mem (i := 1) (j := 0) (by omega) (by rw [e1]; exact pow_mem (S.Y1 i) _) (mem_lcs_zero _)
    have ht2 : tc (T.x₁ j ^ T.d j) (T.x₁ i) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hY2 j i
    have hA1 : A (tc (T.x₁ i ^ T.d j) (T.x₁ j)) = ((T.d j / T.d i : ℕ) : ℤ) • a i j := by
      rw [e1, tc_pow_left_L1 S.h5 (S.Y1 i), addMapG_pow hA (hY2 i j)]
    calc (τ.u i j * T.q i j) • a i j + τ.u i j • a j i
        = τ.u i j • (A (tc (T.x₁ i ^ T.d j) (T.x₁ j)) + A (tc (T.x₁ j ^ T.d j) (T.x₁ i))) := by
          rw [hA1, smul_add, mul_smul]; rfl
      _ = A ((tc (T.x₁ i ^ T.d j) (T.x₁ j) * tc (T.x₁ j ^ T.d j) (T.x₁ i)) ^ τ.u i j) := by
          rw [← hA _ ht1 _ ht2, addMapG_zpow hA (mul_mem ht1 ht2)]
      _ = 0 := by rw [S.delta_pow_eq_one hτ hij, addMapG_one hA]
  have hpairs : (∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) • a i j else 0) +
      (∑ r, ∑ h, if r < h then τ.u r h • a h r else 0) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · exact hpair i j hij
    · simp
  have hV := S.Vpart hτ hA
  calc (2 : ℤ) • A (T.gen τ) = A (T.genA τ) + A (T.genA τ) + (2 : ℤ) • A (T.genB τ) := by
        rw [hAgen, smul_add, two_smul]
    _ = (∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) • a i j else 0) +
          ((∑ r, ∑ h, if r < h then τ.u r h • a h r else 0) + V) + (2 : ℤ) • A (T.genB τ) := by
        rw [← hAA, ← hgA']
    _ = ((∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) • a i j else 0) +
          (∑ r, ∑ h, if r < h then τ.u r h • a h r else 0)) +
          (V + (2 : ℤ) • A (T.genB τ)) := by abel
    _ = 0 := by rw [hpairs, hV, add_zero]

/-- **Every generator of Tahara's Theorem 6.1 is trivial** in the situation `SetupB`. -/
theorem gen_eq_one : T.gen τ = 1 := by
  classical
  have h32 : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have hg2 : T.gen τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    rw [Data.gen, S.genC_eq hτ, mul_one]
    exact mul_mem (S.genA_mem (τ := τ)) (h32 (S.genB_mem (τ := τ)))
  let _ : CommGroup ↥((⊤ : Subgroup G).lowerCentralSeries 2) :=
    commGroupOfComm _ (fun a ha b hb => comm_L2 S.h5 ha hb)
  let A : G → Additive ↥((⊤ : Subgroup G).lowerCentralSeries 2) := fun g =>
    if hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2 then Additive.ofMul ⟨g, hg⟩ else 0
  have hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b := by
    intro a ha b hb
    simp only [A, ha, hb, mul_mem ha hb, ↓reduceDIte]
    rfl
  have h2 := S.two_smul_gen hτ hA
  have hsq : T.gen τ ^ 2 = 1 := by
    have e : A (T.gen τ ^ 2) = 0 := by
      rw [addMapG_pow hA hg2]; exact_mod_cast h2
    simp only [A, pow_mem hg2 2, ↓reduceDIte] at e
    have e' := congrArg Additive.toMul e
    rw [toMul_ofMul, toMul_zero] at e'
    simpa using congrArg Subtype.val e'
  obtain ⟨m, hm⟩ := S.htor _ hg2
  have hcop : Nat.gcd 2 (3 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 2 3)
  have hord : orderOf (T.gen τ) = 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hm)
    rw [hcop] at this
    exact Nat.dvd_one.mp this
  exact orderOf_eq_one_iff.mp hord

end SetupB

/-! ## The theorem for finite groups of class `≤ 4` -/

/-- **Theorem B, finite case, modulo Tahara.** Let `Q` be a finite group of class `≤ 4` such
that `Q/γ₂(Q)` is a `3`-group and `γ₄(Q)` has exponent dividing `3`. Then `D₅(Q) = 1`. -/
theorem D_five_eq_bot_of_class_four_g4_cube (hT : TaharaFiveOne) {Q : Type} [Group Q]
    [Finite Q] (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (h3grp : ∀ x : Q, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1)
    (h4 : ∀ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 3, c ^ 3 = 1) :
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
  -- a uniform exponent `3^N` of `Q/γ₂`, and then of `γ₂/γ₃` and `γ₃/γ₄`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ x : Q, x ^ (3 ^ N) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
    let _ := Fintype.ofFinite Q
    choose kf hkf using h3grp
    refine ⟨Finset.univ.sup kf, fun x => ?_⟩
    have hle : kf x ≤ Finset.univ.sup kf := Finset.le_sup (Finset.mem_univ x)
    rw [show Finset.univ.sup kf = kf x + (Finset.univ.sup kf - kf x) by omega, pow_add, pow_mul]
    exact pow_mem (hkf x) _
  have hp0 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 0,
      a ^ (3 ^ N) ∈ (⊤ : Subgroup Q).lowerCentralSeries (0 + 1) := fun a _ => hN a
  have hp1 := pow_succ_mem hp0
  have hp2 := pow_succ_mem hp1
  have hexp1 : ∀ v : Additive (Layer Q 1), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 1 v
    refine ⟨N, ?_⟩
    rw [← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _),
      show ((3 : ℤ) ^ N) = ((3 ^ N : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    exact hp1 g hg
  have hexp2 : ∀ v : Additive (Layer Q 2), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 2 v
    refine ⟨N, ?_⟩
    rw [← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _),
      show ((3 : ℤ) ^ N) = ((3 ^ N : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    exact hp2 g hg
  have htor : ∀ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1 :=
    fun c hc => ⟨N + 1, by rw [pow_succ, pow_mul]; exact h4 _ (hp2 c hc)⟩
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
  have hd : ∀ i, ∃ m : ℕ, T.d i = 3 ^ (m + 1) := fun i => ⟨ht i, rfl⟩
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
  have S : SetupB T act :=
    ⟨h5, h4, htor, hvalid, hd, fun k => dvd_pow_self 3 (Nat.succ_ne_zero _),
      fun l => dvd_pow_self 3 (Nat.succ_ne_zero _), fun i hi => not_not.mp hi, hind⟩
  have hle := hT Q h5 T hvalid
  rw [eq_bot_iff]
  refine hle.trans ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨τ, hτ, rfl⟩
  rw [SetLike.mem_coe, S.gen_eq_one hτ]
  exact one_mem _

/-- **Theorem B, modulo Tahara's Theorem 6.1** (MATH-444). Let `G/γ₂(G)` be a finite `3`-group
with `γ₄(G)³ ⊆ γ₅(G)`. Then `D₅(G) = γ₅(G)`. -/
theorem D_five_eq_gamma_five_g4_cube (hT : TaharaFiveOne) (G : Type) [Group G]
    (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (h3grp : ∀ x : G, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h4 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 3, c ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 4) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 := by
  refine le_antisymm (D_le_of_D_quotient_eq_bot _ 5 ?_) (gamma_le_D G 5 (by norm_num))
  have : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4) := finite_quotient_lcs hfin 3
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries 4)
  have hmap : ∀ (k : ℕ) (y : G), y ∈ (⊤ : Subgroup G).lowerCentralSeries k →
      π y ∈ (⊤ : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4)).lowerCentralSeries k :=
    fun k y hy => by rw [← lcs_map_mk]; exact Subgroup.mem_map_of_mem _ hy
  refine D_five_eq_bot_of_class_four_g4_cube hT (lowerCentralSeries_quotient_eq_bot 4)
    (fun x => ?_) (fun c hc => ?_)
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⊤ : Subgroup G).lowerCentralSeries 4) x
    obtain ⟨k, hk⟩ := h3grp x
    exact ⟨k, by rw [← map_pow]; exact hmap 1 _ hk⟩
  · rw [← lcs_map_mk] at hc
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (h4 y hy)
end ExpThree

end GroupDimension
