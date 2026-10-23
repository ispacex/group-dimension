module

public import GroupDimension.Tahara
public import GroupDimension.ClassFour

@[expose] public section

/-!
# `D₅ = γ₅` when `G/γ₂(G)` has exponent `3` (Theorem 6.6), given Tahara's Theorem 6.1

**Theorem 6.6** of the paper: if `G/γ₂(G)` is finite of exponent `3`, then `D₅(G) = γ₅(G)`
(`D_five_eq_gamma_five`). The proof takes Tahara's Theorem 6.1 (`TaharaFiveOne`,
`Tahara.lean`) as an explicit hypothesis, discharged in `TaharaTheorem.lean`
(`D_five_eq_gamma_five_of_exp_three`), and follows the wiki page 690 (MATH-127) and the paper:

* reduction to a finite group `Q = G/γ₅(G)` of class `≤ 4` (`finite_quotient_lcs`,
  `D_five_eq_bot_of_class_four`);
* the identities of Lemma 2 there in Tahara's convention `[y, x] = y⁻¹x⁻¹yx`:
  `[Y, x³] = [Y, x]³`, `[a³, x] = [a, x]³` and `[x³, a] = 1` when `a³ ∈ γ₄`
  (`tc_pow_three_right`, `tc_pow_three_left`, `tc_cube_eq_one`);
* a uniqueness basis adapted to the cube map `Q/γ₂ → γ₂/γ₃`, built from bases of
  `𝔽₃`-spaces adapted to a linear map (`exists_adapted_bases`, `cubeMap`,
  `isLayerBasis_of_basis`);
* the computation: for this basis every generator of Tahara's theorem is trivial
  (`Setup.gen_eq_one`, steps 1–6 of the paper). Elements of `γ₃` and `γ₄` are compared through
  `𝔽₃`-valued maps additive on a layer (`exists_F_mod`, `mem_of_forall_F`), so the
  bookkeeping becomes arithmetic in `ZMod 3`.

Indexing: Mathlib's `(⊤ : Subgroup G).lowerCentralSeries k` is `γ_{k+1}(G)`; Tahara's `H_i` is `γ_i`.
-/

namespace GroupDimension

namespace ExpThree

open Subgroup Tahara ClassFour
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Tahara's commutator -/

theorem tc_eq (y x : G) : tc y x = ⁅y⁻¹, x⁻¹⁆ := by
  simp only [tc, commutatorElement_def, inv_inv]

theorem tc_mem {i j n : ℕ} (h : i + j + 1 = n) {y x : G} (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries i)
    (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries j) : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
  rw [tc_eq]; exact commutator_mem_lcs h (inv_mem hy) (inv_mem hx)

theorem tc_inv (y x : G) : (tc y x)⁻¹ = tc x y := by simp only [tc]; group

theorem tc_of_central {z : G} (hz : ∀ g : G, g * z = z * g) (x : G) : tc z x = 1 := by
  calc z⁻¹ * x⁻¹ * z * x = z⁻¹ * (x⁻¹ * z) * x := by group
    _ = z⁻¹ * (z * x⁻¹) * x := by rw [hz x⁻¹]
    _ = 1 := by group

theorem tc_central {z : G} (hz : ∀ g : G, g * z = z * g) (x : G) : tc x z = 1 := by
  rw [← tc_inv, tc_of_central hz, inv_one]

/-- `tc y (a b) = tc y b · b⁻¹ (tc y a) b`. -/
theorem tc_mul_right (y a b : G) : tc y (a * b) = tc y b * (b⁻¹ * tc y a * b) := by
  simp only [tc]; group

/-! ## Ordered products -/

theorem oprod_mem {n : ℕ} {H : Subgroup G} {x : Fin n → G} (hx : ∀ i, x i ∈ H) (a : Fin n → ℤ) :
    oprod x a ∈ H := by
  unfold oprod
  refine list_prod_mem ?_
  intro y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  exact zpow_mem (hx i) _

/-! ## Maps additive on a subgroup -/

section AddMap

variable {p : ℕ} {S : Subgroup G} {A : G → ZMod p}

theorem addMap_list (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) (l : List G)
    (hl : ∀ y ∈ l, y ∈ S) : A l.prod = (l.map A).sum := by
  induction l with
  | nil => simp [addMap_one hA]
  | cons y l ih =>
    rw [List.prod_cons, hA _ (hl y List.mem_cons_self) _
      (list_prod_mem fun z hz => hl z (List.mem_cons_of_mem _ hz)),
      ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.sum_cons]

theorem addMap_ofFn (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {n : ℕ} (f : Fin n → G)
    (hf : ∀ i, f i ∈ S) : A (List.ofFn f).prod = ∑ i, A (f i) := by
  rw [addMap_list hA _ (fun y hy => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; exact hf i),
    List.map_ofFn, List.sum_ofFn]
  rfl

theorem addMap_oprod (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) {n : ℕ} {x : Fin n → G}
    (hx : ∀ i, x i ∈ S) (a : Fin n → ℤ) : A (oprod x a) = ∑ i, (a i : ZMod p) * A (x i) := by
  unfold oprod
  rw [addMap_ofFn hA _ fun i => zpow_mem (hx i) _]
  exact Finset.sum_congr rfl fun i _ => addMap_zpow hA (hx i) _

/-- A map additive on `S` and zero on `N ≤ S` takes the same value on `a` and `a n`. -/
theorem addMap_mul_mem {N : Subgroup G} (hNS : N ≤ S)
    (hA : ∀ a ∈ S, ∀ b ∈ S, A (a * b) = A a + A b) (hN : ∀ a ∈ N, A a = 0) {a n : G}
    (ha : a ∈ S) (hn : n ∈ N) : A (a * n) = A a := by
  rw [hA _ ha _ (hNS hn), hN _ hn, add_zero]

end AddMap

/-- On an elementary abelian section `K/N`, an element of `K \ N` is detected by an additive
`𝔽_p`-valued map on `K` vanishing on `N`. -/
theorem exists_F_mod {p : ℕ} [Fact p.Prime] (K N : Subgroup G) [N.Normal] (hNK : N ≤ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N) (hexp : ∀ a ∈ K, a ^ p ∈ N) {w : G} (hw : w ∈ K)
    (hwN : w ∉ N) :
    ∃ F : G → ZMod p, (∀ a ∈ K, ∀ b ∈ K, F (a * b) = F a + F b) ∧ (∀ a ∈ N, F a = 0) ∧
      F w ≠ 0 := by
  classical
  let M : Subgroup K := N.subgroupOf K
  have hc : ∀ x y : K ⧸ M, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have h1 := hcomm _ (inv_mem b.2) _ (inv_mem a.2)
    have h2 : (((a * b)⁻¹ * (b * a) : K) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [commutatorElement_def, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [h2]; exact h1
  letI : CommGroup (K ⧸ M) := { (inferInstance : Group (K ⧸ M)) with mul_comm := hc }
  have hp' : ∀ y : K ⧸ M, y ^ p = 1 := by
    intro y
    induction y using QuotientGroup.induction_on with | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hexp _ a.2
  have hp : ∀ x : Additive (K ⧸ M), p • x = 0 := fun x => by
    show p • Additive.ofMul (Additive.toMul x) = 0
    rw [← ofMul_pow, hp', ofMul_one]
  have hne : Additive.ofMul ((⟨w, hw⟩ : K) : K ⧸ M) ≠ 0 := by
    intro h
    apply hwN
    have h' : ((⟨w, hw⟩ : K) : K ⧸ M) = 1 := congrArg Additive.toMul h
    rw [QuotientGroup.eq_one_iff] at h'
    exact h'
  obtain ⟨f, hf⟩ := exists_addHom_ne_zero hp hne
  refine ⟨fun g => if hg : g ∈ K then f (Additive.ofMul ((⟨g, hg⟩ : K) : K ⧸ M)) else 0,
    ?_, ?_, ?_⟩
  · intro a ha b hb
    simp only [dif_pos ha, dif_pos hb, dif_pos (mul_mem ha hb)]
    rw [← map_add]
    rfl
  · intro a ha
    simp only [dif_pos (hNK ha)]
    have : ((⟨a, hNK ha⟩ : K) : K ⧸ M) = 1 := by
      rw [QuotientGroup.eq_one_iff]; exact ha
    rw [this]
    exact map_zero f
  · simpa [dif_pos hw] using hf

theorem mem_of_forall_F {p : ℕ} [Fact p.Prime] (K N : Subgroup G) [N.Normal] (hNK : N ≤ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N) (hexp : ∀ a ∈ K, a ^ p ∈ N) {w : G} (hw : w ∈ K)
    (hF : ∀ F : G → ZMod p, (∀ a ∈ K, ∀ b ∈ K, F (a * b) = F a + F b) → (∀ a ∈ N, F a = 0) →
      F w = 0) : w ∈ N := by
  by_contra hwN
  obtain ⟨F, hF1, hF2, hF3⟩ := exists_F_mod K N hNK hcomm hexp hw hwN
  exact hF3 (hF F hF1 hF2)

/-! ## Powers modulo a normal subgroup -/

theorem mk_commute {N : Subgroup G} [N.Normal] {a b : G} (h : ⁅a, b⁆ ∈ N) :
    Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) := by
  have h1 : QuotientGroup.mk' N ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

/-- If `⁅a, b⁆ ∈ N`, then `(ab)^n ≡ aⁿbⁿ` modulo `N`. -/
theorem pow_mul_mod {N : Subgroup G} [N.Normal] {a b : G} (h : ⁅a, b⁆ ∈ N) (n : ℕ) :
    (a ^ n * b ^ n)⁻¹ * (a * b) ^ n ∈ N := by
  rw [← QuotientGroup.eq]
  have := (mk_commute h).mul_pow n
  simpa [QuotientGroup.mk'_apply] using this.symm

/-- `⁅cⁿ, g⁆ ≡ ⁅c, g⁆ⁿ` modulo `γ_{k+2}`, for `c ∈ γ_{k+1}` (Mathlib index `k`). -/
theorem comm_pow_left_mod {k : ℕ} {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries k) (g : G) (n : ℕ) :
    (⁅c, g⁆ ^ n)⁻¹ * ⁅c ^ n, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 2) := by
  rw [← QuotientGroup.eq]
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (k + 2))
  have hz : ∀ y : G, Commute (π y) (π ⁅c, g⁆) := fun y =>
    mk_commute (commutator_mem_lcs (i := 0) (j := k + 1) (by omega) (mem_lcs_zero y)
      (commutator_mem_lcs (i := k) (j := 0) (by omega) hc (mem_lcs_zero g)))
  show π (⁅c, g⁆ ^ n) = π ⁅c ^ n, g⁆
  induction n with
  | zero => simp
  | succ n ih =>
    rw [map_pow] at ih ⊢
    rw [pow_succ' c n, comm_mul_left, map_mul, map_mul, map_mul, map_inv, ← ih,
      ((hz c).pow_right n).eq, mul_inv_cancel_right, pow_succ]

/-- If `γ_{k+1}/γ_{k+2}` has exponent dividing `n`, so has `γ_{k+2}/γ_{k+3}` (Mathlib index). -/
theorem pow_succ_mem {k n : ℕ}
    (hk : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries k, a ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1)) :
    ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1), a ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 2) := by
  let S : Subgroup G :=
    { carrier := {a | a ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) ∧ a ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 2)}
      one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have h := pow_mul_mod (N := (⊤ : Subgroup G).lowerCentralSeries (k + 2))
          (commutator_mem_lcs (i := k + 1) (j := 0) (by omega) ha (mem_lcs_zero b)) n
        have := mul_mem (mul_mem ha3 hb3) h
        rwa [mul_inv_cancel_left] at this
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        exact ⟨inv_mem ha, by rw [inv_pow]; exact inv_mem ha3⟩ }
  have hle : (⊤ : Subgroup G).lowerCentralSeries (k + 1) ≤ S := by
    show ⁅(⊤ : Subgroup G).lowerCentralSeries k, ⊤⁆ ≤ S
    rw [commutator_le]
    intro c hc g _
    refine ⟨commutator_mem_lcs (by omega) hc (mem_lcs_zero g), ?_⟩
    have h := comm_pow_left_mod hc g n
    have h3 : ⁅c ^ n, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 2) :=
      commutator_mem_lcs (by omega) (hk c hc) (mem_lcs_zero g)
    have := mul_mem h3 (inv_mem h)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  exact fun a ha => (hle ha).2

theorem cube_succ {k : ℕ}
    (hk : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries k, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1)) :
    ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1), a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 2) :=
  pow_succ_mem hk

/-! ## Groups of class `≤ 4` whose layers have exponent `3` -/

section Cubes

variable (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
  (h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2)

include h2 in
theorem cube_L2 : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries 2, c ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := cube_succ h2

include h5 h2 in
theorem cube_L3 : ∀ z ∈ (⊤ : Subgroup G).lowerCentralSeries 3, z ^ 3 = 1 := fun z hz => by
  have := cube_succ (cube_L2 h2) z hz
  rwa [h5, mem_bot] at this

include h5 in
theorem central_L3 {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (g : G) : g * z = z * g :=
  central3 h5 hz g

include h5 h2 in
/-- `[Y, x³] = [Y, x]³` for `Y ∈ γ₂` (Tahara's commutator). -/
theorem tc_pow_three_right {Y : G} (hY : Y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
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
    _ = c ^ 3 := by rw [cube_L3 h5 h2 e he3, mul_one]

include h5 in
/-- `[a³, x] = [a, x]³` for `a ∈ γ₂` (Tahara's commutator). -/
theorem tc_pow_three_left {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc (a ^ 3) x = tc a x ^ 3 := by
  obtain ⟨c, hc⟩ : ∃ c, c = tc a x := ⟨_, rfl⟩
  have hc2 : c ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hc ▸ tc_mem (by omega) ha (mem_lcs_zero x)
  have hac : Commute a c := by
    have := comm_eq_one h5 (by norm_num) ha hc2
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hY' : x⁻¹ * a * x = a * c := by rw [hc, tc]; group
  have hp : (x⁻¹ * a * x) ^ 3 = x⁻¹ * a ^ 3 * x := by simp only [pow_three]; group
  rw [← hc]
  calc tc (a ^ 3) x = (a ^ 3)⁻¹ * (x⁻¹ * a * x) ^ 3 := by rw [hp]; simp only [tc]; group
    _ = (a ^ 3)⁻¹ * (a * c) ^ 3 := by rw [hY']
    _ = c ^ 3 := by rw [hac.mul_pow]; group

include h5 h2 in
/-- If `a ∈ γ₂` and `a³ ∈ γ₄`, then `[x³, a] = 1`. -/
theorem tc_cube_eq_one {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (ha3 : a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (x : G) : tc (x ^ 3) a = 1 := by
  rw [← tc_inv, tc_pow_three_right h5 h2 ha, ← tc_pow_three_left h5 ha,
    tc_of_central (fun g => central_L3 h5 ha3 g), inv_one]

end Cubes

/-! ## Finite sums -/

theorem sum_col {R : Type*} [NonAssocSemiring R] {n : ℕ} (P : Fin n → Prop)
    [DecidablePred P] (f : Fin n → R) (h : Fin n) :
    (∑ x, if P x then f x * (if x = h then 1 else 0) else 0) = if P h then f h else 0 := by
  rw [Finset.sum_eq_single h]
  · simp
  · intro b _ hb; simp [hb]
  · intro hh; exact absurd (Finset.mem_univ h) hh

theorem sum_option_image {R : Type*} [AddCommMonoid R] {s t : ℕ} (σ : Fin s → Option (Fin t))
    (hinj : ∀ i j k, σ i = some k → σ j = some k → i = j) (f : Fin t → R)
    (hf : ∀ k, (∀ h, σ h ≠ some k) → f k = 0) :
    ∑ k, f k = ∑ h, ∑ k, if σ h = some k then f k else 0 := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ∃ h, σ h = some k
  · obtain ⟨h0, hh0⟩ := hk
    rw [Finset.sum_eq_single h0]
    · simp [hh0]
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (hinj _ _ _ hb' hh0)
    · intro h; exact absurd (Finset.mem_univ _) h
  · push Not at hk
    rw [hf k hk]
    simp [hk]

theorem skew_lower {s : ℕ} (P : Fin s → Prop) [DecidablePred P] (M β : Fin s → Fin s → ZMod 3)
    (hM : ∀ i j, P i → P j → M i j + M j i = 0) (hMd : ∀ i, P i → M i i = 0)
    (hβ : ∀ i j, β i j + β j i = 0)
    (hsum : ∑ i, ∑ j, (if P i ∧ P j then M i j * β i j else 0) = 0) :
    ∑ i, ∑ j, (if P i ∧ P j ∧ j < i then M i j * β i j else 0) = 0 := by
  have split : ∀ i j, (if P i ∧ P j then M i j * β i j else 0) =
      (if P i ∧ P j ∧ j < i then M i j * β i j else 0) +
      (if P i ∧ P j ∧ i < j then M i j * β i j else 0) +
      (if P i ∧ P j ∧ i = j then M i j * β i j else 0) := by
    intro i j
    by_cases hp : P i ∧ P j
    · rcases lt_trichotomy i j with h | rfl | h
      · simp [hp, h, lt_asymm h, ne_of_lt h]
      · simp [hp]
      · simp [hp, h, lt_asymm h, ne_of_gt h]
    · rw [if_neg hp, if_neg (fun h' => hp ⟨h'.1, h'.2.1⟩), if_neg (fun h' => hp ⟨h'.1, h'.2.1⟩),
        if_neg (fun h' => hp ⟨h'.1, h'.2.1⟩)]; ring
  have hdiag : ∑ i, ∑ j, (if P i ∧ P j ∧ i = j then M i j * β i j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · obtain ⟨hpi, _, rfl⟩ := hc
      rw [hMd i hpi, zero_mul]
    · rfl
  have hup : ∑ i, ∑ j, (if P i ∧ P j ∧ i < j then M i j * β i j else 0) =
      ∑ i, ∑ j, (if P i ∧ P j ∧ j < i then M i j * β i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : P j ∧ P i ∧ j < i
    · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, hc.2.2⟩]
      have e1 : M j i = -M i j := by linear_combination hM j i hc.1 hc.2.1
      have e2 : β j i = -β i j := by linear_combination hβ j i
      rw [e1, e2]; ring
    · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.2.1, h'.1, h'.2.2⟩)]
  simp_rw [split, Finset.sum_add_distrib] at hsum
  rw [hdiag, hup, add_zero] at hsum
  have h2 : (2 : ZMod 3) * ∑ i, ∑ j, (if P i ∧ P j ∧ j < i then M i j * β i j else 0) = 0 := by
    rw [two_mul]; exact hsum
  have : (2 : ZMod 3) * 2 = 1 := by decide
  calc _ = (2 : ZMod 3) * 2 * ∑ i, ∑ j, (if P i ∧ P j ∧ j < i then M i j * β i j else 0) := by
        rw [this, one_mul]
    _ = 0 := by rw [mul_assoc, h2, mul_zero]

theorem cast3_eq_zero {n : ℤ} (h : (3 : ℤ) ∣ n) : (n : ZMod 3) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mpr (by exact_mod_cast h)

theorem dvd_sum_ite {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (f : Fin n → ℤ)
    (h : ∀ x, P x → (3 : ℤ) ∣ f x) : (3 : ℤ) ∣ ∑ x, if P x then f x else 0 :=
  Finset.dvd_sum fun x _ => by split_ifs with hx; exacts [h x hx, dvd_zero _]

theorem col_sum {n t : ℕ} (b : Fin n → Fin t → ℤ) {k0 : Fin t} {h0 : Fin n}
    (hb : ∀ x, b x k0 = if x = h0 then 1 else 0) (P : Fin n → Prop) [DecidablePred P]
    (f : Fin n → ℤ) : (∑ x, if P x then f x * b x k0 else 0) = if P h0 then f h0 else 0 := by
  simp only [hb]
  exact sum_col P f h0

theorem col_sum' {n t : ℕ} (b : Fin n → Fin t → ℤ) {k0 : Fin t} {h0 : Fin n}
    (hb : ∀ x, b x k0 = if x = h0 then 1 else 0) (f : Fin n → ℤ) :
    (∑ x, f x * b x k0) = f h0 := by
  have := col_sum b hb (fun _ => True) f
  simpa using this

theorem row_zero {n t : ℕ} (b : Fin n → Fin t → ℤ) {k0 : Fin t} (hb : ∀ x, b x k0 = 0)
    (f : Fin n → ℤ) : (∑ x, f x * b x k0) = 0 := by
  simp [hb]

/-! ## The computation: every generator of Tahara is trivial -/

/-- The situation of the proof of Theorem 6.6 (and of one case of Theorem 6.8): all orders are
`3`, and the basis is adapted to the cube map. `σ i = some k` says that `x_{1i}` is *active*,
with `x_{1i}³ = x_{2k}`; inactive `x_{1i}` have `x_{1i}³ ∈ γ₃`. -/
structure Setup (T : Data G) (σ : Fin T.s → Option (Fin T.t)) : Prop where
  h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥
  h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2
  valid : T.Valid
  hd : ∀ i, T.d i = 3
  he : ∀ k, T.e k = 3
  hf : ∀ l, T.f l = 3
  inj : ∀ i j k, σ i = some k → σ j = some k → i = j
  mono : ∀ i j ki kj, σ i = some ki → σ j = some kj → ki < kj → i < j
  down : ∀ i ki k, σ i = some ki → k < ki → ∃ j, σ j = some k
  hb : ∀ i k, T.b i k = if σ i = some k then 1 else 0
  hY : ∀ i k, σ i = some k → T.x₂ k = T.x₁ i ^ 3
  hK : ∀ i, σ i = none → T.x₁ i ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2

namespace Setup

variable {T : Data G} {σ : Fin T.s → Option (Fin T.t)} (S : Setup T σ)
include S

theorem hq (i j : Fin T.s) : T.q i j = 1 := by simp [Data.q, S.hd]

theorem ch2 (i : Fin T.s) : T.ch i 2 = 3 := by
  rw [Data.ch, S.hd]; rfl

theorem ch3 (i : Fin T.s) : T.ch i 3 = 1 := by
  rw [Data.ch, S.hd]; rfl

theorem x2mem (k : Fin T.t) : T.x₂ k ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := S.valid.basis₂.mem k

theorem x3mem (l : Fin T.u) : T.x₃ l ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := S.valid.basis₃.mem l

theorem Y1 (i : Fin T.s) : T.x₁ i ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  have h := S.valid.hb i
  rw [S.hd] at h
  have hP : oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    mul_mem (oprod_mem S.x2mem _) (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (S.x3mem l)) _)
  rw [← mul_inv_cancel_left (oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i)) (T.x₁ i ^ 3)]
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

variable {τ : Coeffs T.s T.t} (hτ : T.Admissible τ)
include hτ

theorem u3 (i j : Fin T.s) (hij : i < j) : (3 : ℤ) ∣ τ.u i j := by
  have h := hτ.C₁ i j hij
  rw [S.hq, S.ch3, S.ch2, S.hd] at h
  have := Int.ModEq.dvd h
  push_cast at this
  omega

theorem w3 {h : Fin T.s} {kh : Fin T.t} (hact : σ h = some kh) {j k : Fin T.s} (hhj : h ≤ j)
    (hjk : j ≤ k) : (3 : ℤ) ∣ τ.w h j k := by
  rcases eq_or_lt_of_le hjk with rfl | hjk'
  · have hD := hτ.D₁ j kh
    rw [col_sum T.b (S.bcol hact) (fun x => x ≤ j) (fun x => τ.w x j j),
      col_sum T.b (S.bcol hact) (fun x => j < x) (fun x => τ.w'' j j x), if_pos hhj,
      if_neg (not_lt.mpr hhj), S.ch2, S.hd, S.he] at hD
    have := Int.ModEq.dvd hD
    norm_num at this
    omega
  · have hD := hτ.D₂ j k kh hjk'
    rw [col_sum T.b (S.bcol hact) (fun x => x ≤ j) (fun x => τ.w x j k),
      col_sum T.b (S.bcol hact) (fun x => j < x ∧ x ≤ k) (fun x => τ.w' j x k),
      col_sum T.b (S.bcol hact) (fun x => k < x) (fun x => τ.w'' j k x), if_pos hhj,
      if_neg (fun h' => absurd h'.1 (not_lt.mpr hhj)),
      if_neg (not_lt.mpr (hhj.trans hjk)), S.hd, S.he] at hD
    have := Int.ModEq.dvd hD
    norm_num at this
    omega

theorem w'3 {g : Fin T.s} {kg : Fin T.t} (hact : σ g = some kg) {i h : Fin T.s} (hig : i < g)
    (hgh : g ≤ h) : (3 : ℤ) ∣ τ.w' i g h := by
  have hD := hτ.D₂ i h kg (hig.trans_le hgh)
  rw [col_sum T.b (S.bcol hact) (fun x => x ≤ i) (fun x => τ.w x i h),
    col_sum T.b (S.bcol hact) (fun x => i < x ∧ x ≤ h) (fun x => τ.w' i x h),
    col_sum T.b (S.bcol hact) (fun x => h < x) (fun x => τ.w'' i h x),
    if_neg (not_le.mpr hig), if_pos ⟨hig, hgh⟩, if_neg (not_lt.mpr hgh), S.hd, S.he] at hD
  have := Int.ModEq.dvd hD
  norm_num at this
  omega

omit hτ in
theorem α3 {g : Fin T.s} (hg : σ g = none) {h : Fin T.s} (hgh : g ≤ h) (l : Fin T.u) :
    (3 : ℤ) ∣ T.α g h l := by
  have hm := S.valid.hα g h hgh
  rw [S.hd] at hm
  have ht : tc (T.x₁ g ^ 3) (T.x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (by omega) (S.hK g hg) (mem_lcs_zero _)
  have hP : oprod T.x₃ (T.α g h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    have := mul_mem ht (inv_mem hm)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this
  have := (S.valid.basis₃.indep _).mp hP l
  rw [S.hf] at this
  exact_mod_cast this

theorem E3 (i : Fin T.s) (l : Fin T.u) : (3 : ℤ) ∣ ∑ k, τ.v' i k * T.dd k l := by
  have h := hτ.E i l
  rw [S.hd i, S.hf l] at h
  have h' := Int.ModEq.dvd h
  rw [show ((Nat.gcd 3 3 : ℕ) : ℤ) = 3 by norm_num] at h'
  have s1 : (3 : ℤ) ∣ ∑ h, if h < i then τ.u h i * T.q h i * T.α h i l else 0 :=
    dvd_sum_ite _ _ fun h hh => ((S.u3 hτ h i hh).mul_right _).mul_right _
  have s2 : (3 : ℤ) ∣ ∑ h, if i < h then τ.u i h * T.c h l else 0 :=
    dvd_sum_ite _ _ fun h hh => (S.u3 hτ i h hh).mul_right _
  have s3 : (3 : ℤ) ∣ ∑ h, if h < i then τ.u h i * T.q h i * T.c h l else 0 :=
    dvd_sum_ite _ _ fun h hh => ((S.u3 hτ h i hh).mul_right _).mul_right _
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

theorem a3 (i : Fin T.s) : oprod T.x₂ (τ.v' i) ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  apply mem_of_forall_F (p := 3) ((⊤ : Subgroup G).lowerCentralSeries 2) ((⊤ : Subgroup G).lowerCentralSeries 3)
    ((Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num))
    (fun a ha b _ => commutator_mem_lcs (i := 2) (j := 0) (by omega) ha (mem_lcs_zero b))
    (cube_L2 S.h2) (S.h2 _ (oprod_mem S.x2mem _))
  intro F hF hF0
  have hle : (⊤ : Subgroup G).lowerCentralSeries 3 ≤ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  have hC : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      F ((a * b) ^ 3) = F (a ^ 3) + F (b ^ 3) := by
    intro a ha b hb
    have hn := pow_mul_mod (N := (⊤ : Subgroup G).lowerCentralSeries 3)
      (commutator_mem_lcs (i := 1) (j := 1) (by omega) ha hb) 3
    rw [← mul_inv_cancel_left (a ^ 3 * b ^ 3) ((a * b) ^ 3),
      addMap_mul_mem hle hF hF0 (mul_mem (S.h2 a ha) (S.h2 b hb)) hn,
      hF _ (S.h2 a ha) _ (S.h2 b hb)]
  have hsum := addMap_oprod (A := fun y => F (y ^ 3)) hC S.x2mem (τ.v' i)
  have hxk : ∀ k, F (T.x₂ k ^ 3) = ∑ l, (T.dd k l : ZMod 3) * F (T.x₃ l) := by
    intro k
    have h := S.valid.hdd k
    rw [S.he] at h
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.dd k)) (T.x₂ k ^ 3),
      addMap_mul_mem hle hF hF0 (oprod_mem S.x3mem _) h, addMap_oprod hF S.x3mem]
  rw [hsum]
  simp_rw [hxk, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hz := cast3_eq_zero (S.E3 hτ i l)
  push_cast at hz
  calc ∑ k, (τ.v' i k : ZMod 3) * ((T.dd k l : ZMod 3) * F (T.x₃ l))
      = (∑ k, (τ.v' i k : ZMod 3) * (T.dd k l : ZMod 3)) * F (T.x₃ l) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [hz, zero_mul]

/-- Condition (B) divided by `3`, with `u = 3u'`. -/
theorem B' (i : Fin T.s) (k : Fin T.t) :
    (∑ h, if i < h then τ.u i h / 3 * T.b h k else 0)
      - (∑ h, if h < i then τ.u h i / 3 * T.b h k else 0) + τ.v i k + τ.v' i k = 0 := by
  have h := hτ.B i k
  simp only [S.hq, mul_one, S.hd, S.he] at h
  have e1 : (∑ h, if i < h then τ.u i h * T.b h k else 0) =
      3 * ∑ h, if i < h then τ.u i h / 3 * T.b h k else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hh
    · rw [← mul_assoc, Int.mul_ediv_cancel' (S.u3 hτ i h hh)]
    · rw [mul_zero]
  have e2 : (∑ h, if h < i then τ.u h i * T.b h k else 0) =
      3 * ∑ h, if h < i then τ.u h i / 3 * T.b h k else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hh
    · rw [← mul_assoc, Int.mul_ediv_cancel' (S.u3 hτ h i hh)]
    · rw [mul_zero]
  rw [e1, e2] at h
  push_cast at h
  omega

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
  · rw [S.hd]
    rcases hσ : σ i with _ | ki
    · have : tc (tc (T.x₁ i ^ 3) (T.x₁ j)) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 4 :=
        tc_mem (i := 3) (j := 0) (by omega)
          (tc_mem (i := 2) (j := 0) (by omega) (S.hK i hσ) (mem_lcs_zero _)) (mem_lcs_zero _)
      rw [S.h5, mem_bot] at this
      rw [this, one_zpow]
    · have hz : tc (tc (T.x₁ i ^ 3) (T.x₁ j)) (T.x₁ k) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (i := 2) (j := 0) (by omega)
          (tc_mem (i := 1) (j := 0) (by omega) (S.Y1 i) (mem_lcs_zero _)) (mem_lcs_zero _)
      obtain ⟨w0, hw0⟩ := S.w3 hτ hσ hijk.1 hijk.2
      rw [hw0, zpow_mul, zpow_ofNat, cube_L3 S.h5 S.h2 _ hz, one_zpow]
  · rfl

omit hτ in
/-- `y ↦ F [Y, y]` is additive on `γ₂`, for `Y ∈ γ₂` and `F` additive on `γ₄`. -/
theorem addMap_tc_right {F : G → ZMod 3}
    (hF : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 3, F (a * b) = F a + F b)
    {Y : G} (hY : Y ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      F (tc Y (a * b)) = F (tc Y a) + F (tc Y b) := by
  intro a ha b hb
  have hta : tc Y a ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) hY ha
  have htb : tc Y b ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := tc_mem (by omega) hY hb
  rw [tc_mul_right, show b⁻¹ * tc Y a * b = tc Y a by
    rw [central_L3 S.h5 hta b⁻¹]; group, hF _ htb _ hta, add_comm]

omit hτ in
theorem factorA (i j : Fin T.s) (hu : i < j → (3 : ℤ) ∣ τ.u i j) :
    (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1) =
      if i < j ∧ σ i ≠ none ∧ σ j ≠ none then tc (T.x₁ i ^ 3) (T.x₁ j ^ 3) ^ (τ.u i j / 3)
      else 1 := by
  by_cases hij : i < j
  · rw [if_pos hij, S.hd, S.hq, mul_one, ← Int.mul_ediv_cancel' (hu hij), zpow_mul, zpow_ofNat,
      ← tc_pow_three_right S.h5 S.h2 (S.Y1 i), Int.mul_ediv_cancel' (hu hij)]
    by_cases ha : σ i ≠ none ∧ σ j ≠ none
    · rw [if_pos ⟨hij, ha⟩]
    · rw [if_neg (fun h => ha h.2)]
      have h4 : tc (T.x₁ i ^ 3) (T.x₁ j ^ 3) ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := by
        by_cases hi : σ i = none
        · exact tc_mem (i := 2) (j := 1) (by omega) (S.hK i hi) (S.Y1 j)
        · have hj : σ j = none := by
            by_contra hj; exact ha ⟨hi, hj⟩
          exact tc_mem (i := 1) (j := 2) (by omega) (S.Y1 i) (S.hK j hj)
      rw [S.h5, mem_bot] at h4
      rw [h4, one_zpow]
  · rw [if_neg hij, if_neg (fun h => hij h.1)]

/-- **Every generator of Tahara's Theorem 6.1 is trivial** in the situation `Setup`. -/
theorem gen_eq_one : T.gen τ = 1 := by
  classical
  have hle34 : (⊤ : Subgroup G).lowerCentralSeries 4 ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  -- the `u`-part, rewritten
  have hA : T.genA τ = (List.ofFn fun i => (List.ofFn fun j =>
      if i < j ∧ σ i ≠ none ∧ σ j ≠ none then tc (T.x₁ i ^ 3) (T.x₁ j ^ 3) ^ (τ.u i j / 3)
      else 1).prod).prod := by
    unfold Data.genA
    simp only [S.factorA (τ := τ) _ _ (S.u3 hτ _ _)]
  have memA : ∀ i j, (if i < j ∧ σ i ≠ none ∧ σ j ≠ none then
      tc (T.x₁ i ^ 3) (T.x₁ j ^ 3) ^ (τ.u i j / 3) else 1) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i j
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (S.Y1 i) (S.Y1 j)) _
    · exact one_mem _
  have memB : ∀ i k, (List.ofFn fun l => if k < l then tc (T.x₂ l) (T.x₂ k) ^ T.b i l
      else 1).prod ^ τ.v i k ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i k
    refine zpow_mem (list_prod_mem fun y hy => ?_) _
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hy
    split_ifs
    · exact zpow_mem (tc_mem (by omega) (S.x2mem l) (S.x2mem k)) _
    · exact one_mem _
  have memGA : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [hA]
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact memA i j
  have memGB : T.genB τ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    unfold Data.genB
    exact list_prod_mem fun y hy => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact list_prod_mem fun y hy => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy; exact memB i k
  have hgen : T.gen τ = T.genA τ * T.genB τ := by
    rw [Data.gen, S.genC_eq hτ, mul_one]
  have key : T.gen τ ∈ (⊤ : Subgroup G).lowerCentralSeries 4 := by
    rw [hgen]
    refine mem_of_forall_F (p := 3) ((⊤ : Subgroup G).lowerCentralSeries 3) ((⊤ : Subgroup G).lowerCentralSeries 4) hle34
      (fun a ha b _ => commutator_mem_lcs (i := 3) (j := 0) (by omega) ha (mem_lcs_zero b))
      (fun z hz => by rw [cube_L3 S.h5 S.h2 z hz]; exact one_mem _) (mul_mem memGA memGB) ?_
    intro F hF hF0
    rw [hF _ memGA _ memGB]
    -- notation
    let β : Fin T.s → Fin T.s → ZMod 3 := fun i j => F (tc (T.x₁ i ^ 3) (T.x₁ j ^ 3))
    let γ : Fin T.s → Fin T.t → ZMod 3 := fun i k => F (tc (T.x₁ i ^ 3) (T.x₂ k))
    let Uz : Fin T.s → Fin T.s → ℤ := fun i j =>
      if i < j then τ.u i j / 3 else if j < i then -(τ.u j i / 3) else 0
    let V : Fin T.s → Fin T.s → ZMod 3 := fun i j =>
      ∑ k, if σ j = some k then (τ.v i k : ZMod 3) else 0
    let M : Fin T.s → Fin T.s → ZMod 3 := fun i j => V i j + (Uz i j : ZMod 3)
    have hγβ : ∀ i j kj, σ j = some kj → γ i kj = β i j := by
      intro i j kj hj; simp only [γ, β, S.hY j kj hj]
    have hβskew : ∀ i j, β i j + β j i = 0 := by
      intro i j
      have ht : tc (T.x₁ i ^ 3) (T.x₁ j ^ 3) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
        tc_mem (by omega) (S.Y1 i) (S.Y1 j)
      simp only [β]
      rw [show tc (T.x₁ j ^ 3) (T.x₁ i ^ 3) = (tc (T.x₁ i ^ 3) (T.x₁ j ^ 3))⁻¹ from
        (tc_inv _ _).symm, addMap_inv hF ht, add_neg_cancel]
    have hV : ∀ i j kj, σ j = some kj → V i j = τ.v i kj := by
      intro i j kj hj
      simp only [V, hj, Option.some.injEq]
      rw [Finset.sum_ite_eq]; simp
    -- the `u`-part
    have FA : F (T.genA τ) = ∑ i, ∑ j,
        (if σ i ≠ none ∧ σ j ≠ none ∧ j < i then (Uz i j : ZMod 3) * β i j else 0) := by
      have e1 : F (T.genA τ) = ∑ i, ∑ j, (if i < j ∧ σ i ≠ none ∧ σ j ≠ none then
          ((τ.u i j / 3 : ℤ) : ZMod 3) * β i j else 0) := by
        rw [hA, addMap_ofFn hF _ fun i => list_prod_mem fun y hy => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy; exact memA i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [addMap_ofFn hF _ (memA i)]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · exact addMap_zpow hF (tc_mem (by omega) (S.Y1 i) (S.Y1 j)) _
        · exact addMap_one hF
      rw [e1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : j < i ∧ σ j ≠ none ∧ σ i ≠ none
      · rw [if_pos hc, if_pos ⟨hc.2.2, hc.2.1, hc.1⟩]
        have hU : Uz i j = -(τ.u j i / 3) := by
          simp only [Uz, if_neg (not_lt.mpr hc.1.le), if_pos hc.1]
        rw [hU]
        have := hβskew i j
        push_cast
        linear_combination (↑(τ.u j i / 3) : ZMod 3) * this
      · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.2, h.2.1, h.1⟩)]
    -- the `v`-part
    have FB : F (T.genB τ) = ∑ i, ∑ j,
        (if σ i ≠ none ∧ σ j ≠ none ∧ j < i then V i j * β i j else 0) := by
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
      rcases hσi : σ i with _ | li
      · have hb0 : ∀ l, (T.b i l : ZMod 3) = 0 := fun l => by rw [S.hb, hσi]; simp
        simp [hb0]
      · have hrow : ∀ k, (∑ l, if k < l then (T.b i l : ZMod 3) * F (tc (T.x₂ l) (T.x₂ k))
            else 0) = if k < li then γ i k else 0 := by
          intro k
          rw [Finset.sum_eq_single li]
          · simp only [S.hb, hσi, if_true, Int.cast_one, one_mul, γ, S.hY i li hσi]
          · intro l _ hl
            rw [S.hb, hσi, if_neg (fun h => hl (Option.some_inj.mp h).symm)]
            simp
          · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hrow]
        have e2 : (∑ k, (τ.v i k : ZMod 3) * (if k < li then γ i k else 0)) =
            ∑ k, if k < li then (τ.v i k : ZMod 3) * γ i k else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> simp
        rw [e2, sum_option_image σ S.inj _ (fun k hk => by
          rw [if_neg]
          intro hlt
          obtain ⟨j, hj⟩ := S.down i li k hσi hlt
          exact hk j hj)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases hσj : σ j with _ | kj
        · simp
        · rw [Finset.sum_eq_single kj]
          · have hiff : kj < li ↔ j < i := by
              constructor
              · exact S.mono j i kj li hσj hσi
              · intro hji
                rcases lt_trichotomy kj li with h | h | h
                · exact h
                · subst h; exact absurd (S.inj _ _ _ hσj hσi) (ne_of_lt hji)
                · exact absurd (S.mono i j li kj hσi hσj h) (not_lt.mpr hji.le)
            simp only [if_true, hiff]
            by_cases hji : j < i
            · simp [hji, hV i j kj hσj, hγβ i j kj hσj]
            · simp [hji]
          · intro k _ hk
            rw [if_neg (fun h => hk (Option.some_inj.mp h).symm)]
          · intro h; exact absurd (Finset.mem_univ _) h
    -- the pairing coming from condition (E)
    have pairing : ∀ i li, σ i = some li →
        ∑ j, (if σ j ≠ none then M i j * β i j else 0) = 0 := by
      intro i li hσi
      have ha1 : oprod T.x₂ (τ.v' i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := oprod_mem S.x2mem _
      have h0 := tc_cube_eq_one S.h5 S.h2 (inv_mem ha1)
        (by rw [inv_pow]; exact inv_mem (S.a3 hτ i)) (T.x₁ i)
      have hadd := S.addMap_tc_right hF (S.Y1 i)
      have hinv := addMap_inv (A := fun y => F (tc (T.x₁ i ^ 3) y)) hadd ha1
      have hsum := addMap_oprod (A := fun y => F (tc (T.x₁ i ^ 3) y)) hadd S.x2mem (τ.v' i)
      rw [h0, addMap_one hF, hsum] at hinv
      -- `v' = -v - W`
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
        have e := S.B' hτ i k
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
      have hinv' := hinv.symm
      rw [neg_neg] at hinv'
      refine (Finset.sum_congr rfl fun j _ => ?_).trans hinv'
      rw [← Finset.sum_add_distrib]
      rcases hσj : σ j with _ | kj
      · simp
      · rw [Finset.sum_eq_single kj]
        · simp only [if_true, ne_eq, reduceCtorEq, not_false_eq_true, M, hV i j kj hσj,
            hγβ i j kj hσj]
          ring
        · intro k _ hk
          rw [if_neg (fun h => hk (Option.some_inj.mp h).symm),
            if_neg (fun h => hk (Option.some_inj.mp h).symm), add_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
    -- skew-symmetry of `M` and the end
    have hM : ∀ i j, σ i ≠ none → σ j ≠ none → M i j + M j i = 0 := by
      intro i j hi hj
      obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp hi
      obtain ⟨kj, hkj⟩ := Option.ne_none_iff_exists'.mp hj
      simp only [M, hV i j kj hkj, hV j i ki hki]
      have h1 := cast3_eq_zero (S.F2 hτ hki hkj)
      have h2 : Uz i j + Uz j i = 0 := by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [Uz, h, not_lt.mpr h.le]
        · simp [Uz]
        · simp [Uz, h, not_lt.mpr h.le]
      have h2' : (Uz i j : ZMod 3) + (Uz j i : ZMod 3) = 0 := by exact_mod_cast congrArg _ h2
      push_cast at h1
      linear_combination h1 + h2'
    have hMd : ∀ i, σ i ≠ none → M i i = 0 := by
      intro i hi
      obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp hi
      simp only [M, hV i i ki hki, Uz, lt_irrefl, if_false, Int.cast_zero, add_zero]
      exact cast3_eq_zero (S.F1 hτ hki)
    have hsum : ∑ i, ∑ j, (if σ i ≠ none ∧ σ j ≠ none then M i j * β i j else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hσi : σ i with _ | li
      · simp
      · refine (Finset.sum_congr rfl fun j _ => ?_).trans (pairing i li hσi)
        simp
    have hfin := skew_lower (fun i => σ i ≠ none) M β hM hMd hβskew hsum
    rw [FA, FB, ← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hfin
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · simp only [M]; ring
    · simp
  rwa [S.h5, mem_bot] at key

end Setup

/-! ## Bases of the layers -/

/-- For a linear map `P : V → W` of finite-dimensional spaces there are bases `e` of `V` and `f`
of `W` such that `P e_i = f_i` for `i < m` and `P e_i = 0` for `i ≥ m`. -/
theorem exists_adapted_bases {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (P : V →ₗ[K] W) :
    ∃ (m a b : ℕ) (e : Module.Basis (Fin (m + a)) K V) (f : Module.Basis (Fin (m + b)) K W),
      (∀ i : Fin m, P (e (Fin.castAdd a i)) = f (Fin.castAdd b i)) ∧
      (∀ j : Fin a, P (e (Fin.natAdd m j)) = 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker P)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (LinearMap.range P)
  let bC := Module.finBasis K C
  let bK := Module.finBasis K (LinearMap.ker P)
  let bD := Module.finBasis K D
  let φ : C →ₗ[K] LinearMap.range P :=
    (P.domRestrict C).codRestrict (LinearMap.range P) (fun c => LinearMap.mem_range_self P c)
  have hφ : Function.Bijective φ := by
    constructor
    · intro c c' h
      have h' : P (c - c' : V) = 0 := by
        have h2 : P c = P c' := congrArg Subtype.val h
        rw [map_sub, h2, sub_self]
      have hk : ((c - c' : C) : V) ∈ LinearMap.ker P := by simpa using h'
      have hc : ((c - c' : C) : V) ∈ C := (c - c').2
      have := hC.disjoint.le_bot ⟨hk, hc⟩
      rw [Submodule.mem_bot] at this
      exact sub_eq_zero.mp (Subtype.ext (by simpa using this))
    · rintro ⟨w, v, rfl⟩
      have hv : v ∈ LinearMap.ker P ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨k, hk, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      show P c = P (k + c)
      rw [map_add, LinearMap.mem_ker.mp hk, zero_add]
  let bR := bC.map (LinearEquiv.ofBijective φ hφ)
  let e := ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker P) hC.symm)).reindex
    finSumFinEquiv
  let f := ((bR.prod bD).map (Submodule.prodEquivOfIsCompl (LinearMap.range P) D hD)).reindex
    finSumFinEquiv
  refine ⟨_, _, _, e, f, ?_, ?_⟩
  · intro i
    simp [e, f, bR, φ]
    all_goals rfl
  · intro j
    simp [e]

/-- `(ab)³ = a³b³z³` if `ba = abz` with `z` central. -/
theorem mul_pow_three_of_central {H : Type*} [Group H] {a b z : H} (hba : b * a = a * b * z)
    (hz : ∀ g : H, z * g = g * z) : (a * b) ^ 3 = a ^ 3 * b ^ 3 * z ^ 3 := by
  have h1 : a⁻¹ * b * a = b * z := by
    rw [mul_assoc, hba]; group
  have h2 : a⁻¹ * (a⁻¹ * b * a) * a = b * z * z := by
    rw [h1]
    calc a⁻¹ * (b * z) * a = a⁻¹ * b * (z * a) := by group
      _ = a⁻¹ * b * (a * z) := by rw [hz a]
      _ = (a⁻¹ * b * a) * z := by group
      _ = b * z * z := by rw [h1]
  have hzb : ∀ X, z * (b * X) = b * (z * X) := fun X => by rw [← mul_assoc, hz b, mul_assoc]
  calc (a * b) ^ 3 = a ^ 3 * (a⁻¹ * (a⁻¹ * b * a) * a) * (a⁻¹ * b * a) * b := by
        rw [pow_three (a * b), pow_three a]; group
    _ = a ^ 3 * (b * z * z) * (b * z) * b := by rw [h2, h1]
    _ = a ^ 3 * b ^ 3 * z ^ 3 := by
      simp only [pow_three, mul_assoc, hzb, hz b]

variable (G) in
/-- The layer `γ_{k+1}/γ_{k+2}` (Mathlib index `k`). -/
abbrev Layer (k : ℕ) : Type _ :=
  ↥((⊤ : Subgroup G).lowerCentralSeries k) ⧸ ((⊤ : Subgroup G).lowerCentralSeries (k + 1)).subgroupOf ((⊤ : Subgroup G).lowerCentralSeries k)

instance (k : ℕ) : CommGroup (Layer G k) :=
  { (inferInstance : Group (Layer G k)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with | H a =>
      induction y using QuotientGroup.induction_on with | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h : ⁅(b : G)⁻¹, (a : G)⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) :=
        lcs_mem_of_le (by omega) (commutator_lcs_le k k
          (commutator_mem_commutator (inv_mem b.2) (inv_mem a.2)))
      have e : (((a * b)⁻¹ * (b * a) : ↥((⊤ : Subgroup G).lowerCentralSeries k)) : G) =
          ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
        simp only [commutatorElement_def, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [e]; exact h }

variable (G) in
/-- The class of `g ∈ γ_{k+1}` in the layer, written additively (`0` off `γ_{k+1}`). -/
noncomputable def cl (k : ℕ) (g : G) : Additive (Layer G k) :=
  open Classical in
  if h : g ∈ (⊤ : Subgroup G).lowerCentralSeries k then Additive.ofMul (QuotientGroup.mk ⟨g, h⟩) else 0

theorem cl_of_mem {k : ℕ} {g : G} (h : g ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    cl G k g = Additive.ofMul (QuotientGroup.mk ⟨g, h⟩) := by
  rw [cl, dif_pos h]

theorem cl_mul {k : ℕ} {a b : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries k) : cl G k (a * b) = cl G k a + cl G k b := by
  rw [cl_of_mem ha, cl_of_mem hb, cl_of_mem (mul_mem ha hb), ← ofMul_mul]
  rfl

theorem cl_eq_zero_iff {k : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    cl G k a = 0 ↔ a ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  rw [cl_of_mem ha, ← ofMul_one, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

theorem cl_surj (k : ℕ) (v : Additive (Layer G k)) :
    ∃ g ∈ (⊤ : Subgroup G).lowerCentralSeries k, cl G k g = v := by
  induction v using Additive.rec with | ofMul x =>
  induction x using QuotientGroup.induction_on with | H a =>
  exact ⟨a, a.2, by rw [cl_of_mem a.2]⟩

theorem cl_one (k : ℕ) : cl G k (1 : G) = 0 := (cl_eq_zero_iff (one_mem _)).mpr (one_mem _)

theorem cl_inv {k : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    cl G k a⁻¹ = -cl G k a := by
  have := cl_mul ha (inv_mem ha)
  rw [mul_inv_cancel, cl_one] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem cl_zpow {k : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k) (n : ℤ) :
    cl G k (a ^ n) = n • cl G k a := by
  induction n using Int.induction_on with
  | zero => simp [cl_one]
  | succ n ih => rw [zpow_add_one, cl_mul (zpow_mem ha _) ha, ih, add_smul, one_smul]
  | pred n ih =>
    rw [zpow_sub_one, cl_mul (zpow_mem ha _) (inv_mem ha), ih, cl_inv ha, sub_smul, one_smul,
      sub_eq_add_neg]

theorem cl_oprod {k n : ℕ} {y : Fin n → G} (hy : ∀ i, y i ∈ (⊤ : Subgroup G).lowerCentralSeries k)
    (a : Fin n → ℤ) : cl G k (oprod y a) = ∑ i, a i • cl G k (y i) := by
  unfold oprod
  have : ∀ l : List G, (∀ x ∈ l, x ∈ (⊤ : Subgroup G).lowerCentralSeries k) →
      cl G k l.prod = (l.map (cl G k)).sum := by
    intro l
    induction l with
    | nil => intro _; simp [cl_one]
    | cons x l ih =>
      intro hl
      rw [List.prod_cons, cl_mul (hl x List.mem_cons_self)
        (list_prod_mem fun z hz => hl z (List.mem_cons_of_mem _ hz)),
        ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.sum_cons]
  rw [this _ (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact zpow_mem (hy i) _),
    List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun i _ => cl_zpow (hy i) _

theorem three_smul_cl {k : ℕ}
    (h3 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries k, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1))
    (v : Additive (Layer G k)) : (3 : ℕ) • v = 0 := by
  obtain ⟨g, hg, rfl⟩ := cl_surj k v
  rw [← natCast_zsmul, ← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _)]
  exact_mod_cast h3 g hg

/-- A basis of the `𝔽₃`-space `γ_{k+1}/γ_{k+2}` (exponent `3`), lifted to `G`, is a uniqueness
basis of the layer with all orders `3`; normal forms have exponents in `[0, 3)`. -/
theorem isLayerBasis_of_basis {k n : ℕ}
    [Module (ZMod 3) (Additive (Layer G k))] {y : Fin n → G}
    (hy : ∀ i, y i ∈ (⊤ : Subgroup G).lowerCentralSeries k) (b : Module.Basis (Fin n) (ZMod 3) (Additive (Layer G k)))
    (hb : ∀ i, b i = cl G k (y i)) :
    IsLayerBasis k y (fun _ => 3) ∧ ∀ g ∈ (⊤ : Subgroup G).lowerCentralSeries k, ∃ a : Fin n → ℤ,
      (∀ i, 0 ≤ a i ∧ a i < 3) ∧ (oprod y a)⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  have hcl : ∀ a : Fin n → ℤ, cl G k (oprod y a) = ∑ i, (a i : ZMod 3) • b i := by
    intro a
    rw [cl_oprod hy]
    exact Finset.sum_congr rfl fun i _ => by rw [hb, Int.cast_smul_eq_zsmul]
  have hnf : ∀ g ∈ (⊤ : Subgroup G).lowerCentralSeries k, ∃ a : Fin n → ℤ,
      (∀ i, 0 ≤ a i ∧ a i < 3) ∧ (oprod y a)⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
    intro g hg
    refine ⟨fun i => ((b.repr (cl G k g) i).val : ℤ), fun i => ⟨by positivity, ?_⟩, ?_⟩
    · have := (b.repr (cl G k g) i).val_lt
      show (((b.repr (cl G k g) i).val : ℕ) : ℤ) < 3
      omega
    · have hm : oprod y (fun i => ((b.repr (cl G k g) i).val : ℤ)) ∈ (⊤ : Subgroup G).lowerCentralSeries k :=
        oprod_mem hy _
      rw [← cl_eq_zero_iff (mul_mem (inv_mem hm) hg), cl_mul (inv_mem hm) hg, cl_inv hm, hcl]
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
      rw [b.sum_repr, neg_add_cancel]
  refine ⟨⟨hy, fun _ => by norm_num, fun _ _ _ => dvd_rfl, fun a => ?_, fun g hg => ?_⟩, hnf⟩
  · rw [← cl_eq_zero_iff (oprod_mem hy a), hcl]
    constructor
    · intro h i
      have := Fintype.linearIndependent_iff.mp b.linearIndependent _ h i
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this
    · intro h
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h i), zero_smul]
  · obtain ⟨a, -, ha⟩ := hnf g hg
    exact ⟨a, ha⟩

/-! ## The cube map `γ₁/γ₂ → γ₂/γ₃` -/

theorem prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact h _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact prod_ofFn_eq_single (fun j => f j.succ) i
        (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e)))

theorem oprod_zero {n : ℕ} (x : Fin n → G) : oprod x 0 = 1 := by
  unfold oprod
  exact List.prod_eq_one fun y hy => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy; simp

theorem oprod_single {n : ℕ} (x : Fin n → G) (i : Fin n) :
    oprod x (fun j => if j = i then 1 else 0) = x i := by
  unfold oprod
  rw [prod_ofFn_eq_single _ i (fun j hj => by simp [hj])]
  simp

/-- `(xy)³ ≡ x³y³` modulo `γ₃` when `γ₂/γ₃` has exponent `3`. -/
theorem cube_mul_mod (h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (x y : G) : (x ^ 3 * y ^ 3)⁻¹ * (x * y) ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  rw [← QuotientGroup.eq]
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries 2)
  have hc : tc y x ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := tc_mem (by omega) (mem_lcs_zero y) (mem_lcs_zero x)
  have hba : π y * π x = π x * π y * π (tc y x) := by
    rw [← map_mul, ← map_mul, ← map_mul]; congr 1; simp only [tc]; group
  have hz : ∀ g, π (tc y x) * π g = π g * π (tc y x) := fun g =>
    (mk_commute (commutator_mem_lcs (i := 1) (j := 0) (by omega) hc (mem_lcs_zero g))).eq
  have hπ : ∀ g, π g = (g : G ⧸ (⊤ : Subgroup G).lowerCentralSeries 2) := fun _ => rfl
  have key := mul_pow_three_of_central hba (fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ((⊤ : Subgroup G).lowerCentralSeries 2) g; exact hz g)
  have h3 : π (tc y x) ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact h2 _ hc
  rw [h3, mul_one] at key
  simp only [hπ] at key
  exact key.symm

variable (G) in
/-- The cube map `γ₁/γ₂ → γ₂/γ₃`, `x ↦ x³`, for `G/γ₂` of exponent `3`. -/
noncomputable def cubeMap (h1 : ∀ x : G, x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    Additive (Layer G 0) →+ Additive (Layer G 1) :=
  MonoidHom.toAdditive <| QuotientGroup.lift _
    { toFun := fun x => QuotientGroup.mk ⟨(x : G) ^ 3, h1 x⟩
      map_one' := by
        simp only [OneMemClass.coe_one, one_pow]; rfl
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h := inv_mem (cube_mul_mod h2 (x : G) (y : G))
        convert h using 1
        rw [mul_inv_rev, inv_inv]
        rfl }
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx
      show (QuotientGroup.mk _ : Layer G 1) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h2 _ hx)

theorem cubeMap_cl (h1 : ∀ x : G, x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h2 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (x : G) :
    cubeMap G h1 h2 (cl G 0 x) = cl G 1 (x ^ 3) := by
  rw [cl_of_mem (mem_lcs_zero x), cl_of_mem (h1 x)]
  rfl

/-! ## Theorem 6.6 for finite groups of class `≤ 4` -/

/-- **Theorem 6.6, finite case, modulo Tahara.** If `Q` is finite of class `≤ 4` and
`Q/γ₂(Q)` has exponent dividing `3`, then `D₅(Q) = 1`. -/
theorem D_five_eq_bot_of_class_four (hT : TaharaFiveOne) {Q : Type} [Group Q] [Finite Q]
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) (h1 : ∀ x : Q, x ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) :
    D 5 Q = ⊥ := by
  classical
  have h1' : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 0, a ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries (0 + 1) :=
    fun a _ => h1 a
  have h2 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 1, a ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := cube_succ h1'
  have h3 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, a ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 := cube_succ h2
  letI : Module (ZMod 3) (Additive (Layer Q 0)) := AddCommGroup.zmodModule (three_smul_cl h1')
  letI : Module (ZMod 3) (Additive (Layer Q 1)) := AddCommGroup.zmodModule (three_smul_cl h2)
  letI : Module (ZMod 3) (Additive (Layer Q 2)) := AddCommGroup.zmodModule (three_smul_cl h3)
  let P : Additive (Layer Q 0) →ₗ[ZMod 3] Additive (Layer Q 1) :=
    (cubeMap Q h1 h2).toZModLinearMap 3
  have hP : ∀ x : Q, P (cl Q 0 x) = cl Q 1 (x ^ 3) := fun x => cubeMap_cl h1 h2 x
  obtain ⟨m, a, bb, e, f, hef, hez⟩ := exists_adapted_bases P
  let e3 := Module.finBasis (ZMod 3) (Additive (Layer Q 2))
  choose L0 hL0 using fun v : Additive (Layer Q 0) => cl_surj (G := Q) 0 v
  choose L1 hL1 using fun v : Additive (Layer Q 1) => cl_surj (G := Q) 1 v
  choose L2 hL2 using fun v : Additive (Layer Q 2) => cl_surj (G := Q) 2 v
  -- the bases
  let x1 : Fin (m + a) → Q := fun i => L0 (e i)
  let x2 : Fin (m + bb) → Q := fun k =>
    if h : (k : ℕ) < m then x1 ⟨k, by omega⟩ ^ 3 else L1 (f k)
  let x3 : Fin (Module.finrank (ZMod 3) (Additive (Layer Q 2))) → Q := fun l => L2 (e3 l)
  have hx1 : ∀ i, cl Q 0 (x1 i) = e i := fun i => (hL0 (e i)).2
  have hcube : ∀ i, cl Q 1 (x1 i ^ 3) = P (e i) := fun i => by rw [← hx1, hP]
  have hx2mem : ∀ k, x2 k ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
    intro k
    by_cases h : (k : ℕ) < m
    · simp only [x2, dif_pos h]; exact h1 _
    · simp only [x2, dif_neg h]; exact (hL1 (f k)).1
  have hx2 : ∀ k, cl Q 1 (x2 k) = f k := by
    intro k
    by_cases h : (k : ℕ) < m
    · simp only [x2, dif_pos h]
      rw [hcube]
      have e1 : (⟨k, by omega⟩ : Fin (m + a)) = Fin.castAdd a ⟨k, h⟩ := rfl
      have e2 : k = Fin.castAdd bb ⟨k, h⟩ := rfl
      rw [e1, hef]
      exact congrArg f e2.symm
    · simp only [x2, dif_neg h]; exact (hL1 (f k)).2
  obtain ⟨B1, -⟩ := isLayerBasis_of_basis (fun i => mem_lcs_zero (x1 i)) e (fun i => (hx1 i).symm)
  obtain ⟨B2, -⟩ := isLayerBasis_of_basis hx2mem f (fun k => (hx2 k).symm)
  obtain ⟨B3, nf3⟩ := isLayerBasis_of_basis (fun l => (hL2 (e3 l)).1) e3
    (fun l => (hL2 (e3 l)).2.symm)
  -- the active indices
  let σ : Fin (m + a) → Option (Fin (m + bb)) := fun i =>
    if h : (i : ℕ) < m then some ⟨i, by omega⟩ else none
  have hσ : ∀ i k, σ i = some k ↔ (i : ℕ) < m ∧ (k : ℕ) = i := by
    intro i k
    simp only [σ]
    split_ifs with h
    · simp only [Option.some.injEq, h, true_and]
      constructor
      · rintro rfl; rfl
      · intro hk; exact Fin.ext hk.symm
    · simp [h]
  have hK : ∀ i, σ i = none → x1 i ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := by
    intro i hi
    have hm : ¬ (i : ℕ) < m := by
      intro h; simp [σ, h] at hi
    have e1 : i = Fin.natAdd m ⟨(i : ℕ) - m, by omega⟩ := Fin.ext (by simp; omega)
    rw [← cl_eq_zero_iff (h1 _), hcube, e1, hez]
  -- the structure constants
  let c : Fin (m + a) → Fin _ → ℤ := fun i =>
    if h : σ i = none then Classical.choose (nf3 _ (hK i h)) else 0
  let dd : Fin (m + bb) → Fin _ → ℤ := fun k => Classical.choose (nf3 _ (h2 _ (hx2mem k)))
  let α : Fin (m + a) → Fin (m + a) → Fin _ → ℤ := fun g h =>
    Classical.choose (nf3 _ (tc_mem (i := 1) (j := 0) (by omega) (h1 (x1 g)) (mem_lcs_zero (x1 h))))
  let T : Tahara.Data Q :=
    { s := m + a, t := m + bb, u := _, x₁ := x1, d := fun _ => 3, x₂ := x2, e := fun _ => 3,
      x₃ := x3, f := fun _ => 3, b := fun i k => if σ i = some k then 1 else 0, c := c, dd := dd,
      α := α }
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
      have := (Classical.choose_spec (nf3 _ (h2 _ (hx2mem k)))).1 l; exact_mod_cast this
    · intro g h l _
      have := (Classical.choose_spec (nf3 _ (tc_mem (i := 1) (j := 0) (by omega) (h1 (x1 g))
        (mem_lcs_zero (x1 h))))).1 l
      exact_mod_cast this
    · intro i
      show (oprod x2 (fun k => if σ i = some k then 1 else 0) * oprod x3 (c i))⁻¹ * x1 i ^ 3 ∈ _
      by_cases h : σ i = none
      · have hb0 : (fun k => if σ i = some k then (1 : ℤ) else 0) = 0 := by
          funext k; simp [h]
        simp only [c, dif_pos h, hb0, oprod_zero, one_mul]
        exact (Classical.choose_spec (nf3 _ (hK i h))).2
      · obtain ⟨ki, hki⟩ := Option.ne_none_iff_exists'.mp h
        have hb1 : (fun k => if σ i = some k then (1 : ℤ) else 0) =
            fun k => if k = ki then 1 else 0 := by
          funext k
          rw [hki]
          by_cases hk : k = ki
          · simp [hk]
          · simp [hk, Ne.symm hk]
        have hx : x2 ki = x1 i ^ 3 := by
          obtain ⟨hi, hk⟩ := (hσ i ki).mp hki
          simp only [x2, dif_pos (show (ki : ℕ) < m by omega)]
          congr 2
          exact Fin.ext hk
        simp only [c, dif_neg h, hb1, oprod_single, hx, oprod_zero, mul_one, inv_mul_cancel]
        exact one_mem _
    · intro k
      exact (Classical.choose_spec (nf3 _ (h2 _ (hx2mem k)))).2
    · intro g h _
      exact (Classical.choose_spec (nf3 _ (tc_mem (i := 1) (j := 0) (by omega) (h1 (x1 g))
        (mem_lcs_zero (x1 h))))).2
  have S : Setup T σ := by
    refine ⟨h5, h2, hvalid, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, fun _ _ => rfl,
      ?_, hK⟩
    · intro i j k hi hj
      obtain ⟨-, hi⟩ := (hσ i k).mp hi
      obtain ⟨-, hj⟩ := (hσ j k).mp hj
      exact Fin.ext (hi.symm.trans hj)
    · intro i j ki kj hi hj hlt
      obtain ⟨-, hi⟩ := (hσ i ki).mp hi
      obtain ⟨-, hj⟩ := (hσ j kj).mp hj
      show (i : ℕ) < j
      have : (ki : ℕ) < kj := hlt
      omega
    · intro i ki k hi hlt
      obtain ⟨him, hi⟩ := (hσ i ki).mp hi
      have : (k : ℕ) < ki := hlt
      refine ⟨⟨k, by show (k : ℕ) < m + a; omega⟩, (hσ _ k).mpr ⟨by simp; omega, rfl⟩⟩
    · intro i k hi
      obtain ⟨him, hk⟩ := (hσ i k).mp hi
      show x2 k = x1 i ^ 3
      simp only [x2, dif_pos (show (k : ℕ) < m by omega)]
      congr 2
      exact Fin.ext hk
  have hle := hT Q h5 T hvalid
  rw [eq_bot_iff]
  refine hle.trans ((Subgroup.closure_le _).mpr ?_)
  rintro z ⟨τ, hτ, rfl⟩
  rw [SetLike.mem_coe, S.gen_eq_one hτ]
  exact one_mem _

/-! ## `G/γ₂` finite ⇒ `G/γ_k` finite -/

theorem cl_eq_cl {k : ℕ} {a b : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries k)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    cl G k a = cl G k b ↔ a⁻¹ * b ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  rw [← cl_eq_zero_iff (mul_mem (inv_mem ha) hb), cl_mul (inv_mem ha) hb, cl_inv ha,
    neg_add_eq_zero]

/-- The class of `⁅c, g⁆` in `γ_{k+2}/γ_{k+3}` depends only on `c` modulo `γ_{k+2}` and on `g`
modulo `γ₂`. -/
theorem cl_comm_congr {k : ℕ} {c c' g g' : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries k)
    (hcc : c⁻¹ * c' ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1))
    (hgg : g⁻¹ * g' ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    cl G (k + 1) ⁅c, g⁆ = cl G (k + 1) ⁅c', g'⁆ := by
  have hc' : c' ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
    rw [← mul_inv_cancel_left c c']; exact mul_mem hc (lcs_mem_of_le (by omega) hcc)
  rw [cl_eq_cl (commutator_mem_lcs (by omega) hc (mem_lcs_zero g))
    (commutator_mem_lcs (by omega) hc' (mem_lcs_zero g')), ← QuotientGroup.eq]
  let π := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (k + 2))
  show π ⁅c, g⁆ = π ⁅c', g'⁆
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1), c' = c * n :=
    ⟨c⁻¹ * c', hcc, by group⟩
  obtain ⟨m, hm, rfl⟩ : ∃ m ∈ (⊤ : Subgroup G).lowerCentralSeries 1, g' = g * m :=
    ⟨g⁻¹ * g', hgg, by group⟩
  have h1 : π ⁅n, g * m⁆ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact commutator_mem_lcs (by omega) hn (mem_lcs_zero _)
  have h2 : π ⁅c, m⁆ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact commutator_mem_lcs (by omega) hc hm
  have e1 : π ⁅c * n, g * m⁆ = π ⁅c, g * m⁆ := by
    rw [comm_mul_left]; simp only [map_mul, map_inv, h1]; group
  have e2 : π ⁅c, g * m⁆ = π ⁅c, g⁆ := by
    rw [comm_mul_right]; simp only [map_mul, map_inv, h2]; group
  rw [e1, e2]

/-- If `G/γ₂(G)` is finite, so is every `G/γ_{k+1}(G)`. -/
theorem finite_quotient_lcs (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1)) :
    ∀ k, Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (k + 1)) := by
  classical
  set n := Nat.card (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1)
  have hn : 0 < n := Nat.card_pos
  have hpow0 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 0, a ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries (0 + 1) := by
    intro a _
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hpow : ∀ k, ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries k, a ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
    intro k
    induction k with
    | zero => exact hpow0
    | succ k ih => exact pow_succ_mem ih
  -- the layers are finite
  have hlay : ∀ k, Finite (Layer G k) := by
    intro k
    induction k with
    | zero =>
      let f : G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1 → Layer G 0 :=
        Quotient.lift (fun g => QuotientGroup.mk ⟨g, mem_lcs_zero g⟩) (fun a b hab => by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          exact QuotientGroup.leftRel_apply.mp hab)
      refine Finite.of_surjective f fun x => ?_
      induction x using QuotientGroup.induction_on with | H a =>
      exact ⟨(a : G), rfl⟩
    | succ k ih =>
      have htor : Monoid.IsTorsion (Layer G (k + 1)) := by
        intro x
        induction x using QuotientGroup.induction_on with | H a =>
        refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hpow (k + 1) a a.2
      -- a finite generating set
      choose rk hrk using fun v : Additive (Layer G k) => cl_surj (G := G) k v
      choose r0 hr0 using fun q : G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1 => QuotientGroup.mk_surjective q
      let T : Set (Layer G (k + 1)) := Set.range fun p : Additive (Layer G k) ×
          (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1) => Additive.toMul (cl G (k + 1) ⁅rk p.1, r0 p.2⁆)
      have hTfin : T.Finite := Set.finite_range _
      have hcl : ∀ c ∈ (⊤ : Subgroup G).lowerCentralSeries k, ∀ g : G,
          Additive.toMul (cl G (k + 1) ⁅c, g⁆) ∈ T := by
        intro c hc g
        exact ⟨(cl G k c, (g : G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1)), congrArg Additive.toMul
          (cl_comm_congr (hrk _).1 ((cl_eq_cl (hrk _).1 hc).mp (hrk _).2)
            (QuotientGroup.eq.mp (hr0 _)))⟩
      have htop : Subgroup.closure T = ⊤ := by
        rw [eq_top_iff]
        intro x _
        induction x using QuotientGroup.induction_on with | H a =>
        obtain ⟨a, ha⟩ := a
        let ι := QuotientGroup.mk' (((⊤ : Subgroup G).lowerCentralSeries (k + 2)).subgroupOf
          ((⊤ : Subgroup G).lowerCentralSeries (k + 1)))
        let H' : Subgroup G := ((Subgroup.closure T).comap ι).map ((⊤ : Subgroup G).lowerCentralSeries (k + 1)).subtype
        have hle : (⊤ : Subgroup G).lowerCentralSeries (k + 1) ≤ H' := by
          show ⁅(⊤ : Subgroup G).lowerCentralSeries k, ⊤⁆ ≤ H'
          rw [commutator_le]
          intro c hc g _
          have hm : ⁅c, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) :=
            commutator_mem_lcs (by omega) hc (mem_lcs_zero g)
          refine ⟨⟨⁅c, g⁆, hm⟩, Subgroup.subset_closure ?_, rfl⟩
          have := hcl c hc g
          rwa [cl_of_mem hm] at this
        obtain ⟨⟨b, hb⟩, hbT, hba⟩ := hle ha
        simp only [Subgroup.coe_subtype] at hba
        subst hba
        exact hbT
      haveI : Group.FG (Layer G (k + 1)) := Group.fg_iff.mpr ⟨T, htop, hTfin⟩
      exact CommGroup.finite_of_fg_torsion _ htor
  intro k
  induction k with
  | zero => exact hfin
  | succ k ih =>
    have hidx := Subgroup.relIndex_mul_index (H := (⊤ : Subgroup G).lowerCentralSeries (k + 2))
      (K := (⊤ : Subgroup G).lowerCentralSeries (k + 1)) ((Subgroup.lowerCentralSeries_antitone ⊤) (by omega))
    have h1 : ((⊤ : Subgroup G).lowerCentralSeries (k + 1)).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h2 : ((⊤ : Subgroup G).lowerCentralSeries (k + 2)).relIndex ((⊤ : Subgroup G).lowerCentralSeries (k + 1)) ≠ 0 := by
      haveI := hlay (k + 1)
      exact Subgroup.index_ne_zero_of_finite
    have h3 : ((⊤ : Subgroup G).lowerCentralSeries (k + 2)).index ≠ 0 := by
      rw [← hidx]; exact mul_ne_zero h2 h1
    haveI : ((⊤ : Subgroup G).lowerCentralSeries (k + 2)).FiniteIndex := ⟨h3⟩
    exact Subgroup.finite_quotient_of_finiteIndex

/-- **Theorem 6.6, modulo Tahara's Theorem 6.1.** If `G/γ₂(G)` is finite of exponent dividing
`3`, then `D₅(G) = γ₅(G)`. -/
theorem D_five_eq_gamma_five (hT : TaharaFiveOne) (G : Type) [Group G]
    (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1)) (h1 : ∀ x : G, x ^ 3 ∈ (⊤ : Subgroup G).lowerCentralSeries 1) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 := by
  refine le_antisymm (D_le_of_D_quotient_eq_bot _ 5 ?_) (gamma_le_D G 5 (by norm_num))
  haveI : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4) := finite_quotient_lcs hfin 3
  refine D_five_eq_bot_of_class_four hT (lowerCentralSeries_quotient_eq_bot 4) fun x => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⊤ : Subgroup G).lowerCentralSeries 4) x
  rw [← map_pow, ← lcs_map_mk]
  exact Subgroup.mem_map_of_mem _ (h1 x)

end ExpThree

end GroupDimension
