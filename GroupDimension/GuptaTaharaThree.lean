module

public import GroupDimension.TaharaTheorem
public import GroupDimension.Passi
public import GroupDimension.MinimalThree

@[expose] public section

/-!
# `D₅ = γ₅` for metabelian groups with `G/γ₂` a finite `p`-group, `p` odd (MATH-445, D5-50)

**Theorem** (`D_five_eq_gamma_five_of_metabelian`): let `p` be an odd prime, `G/γ₂(G)` a finite
`p`-group and `[γ₂(G), γ₂(G)] ⊆ γ₅(G)`. Then `D₅(G) = γ₅(G)`. For `p = 3` and `G` metabelian this
is Gupta–Tahara [GT85, Thm. 3.2(c)] (`guptaTaharaMetabelian_three`), which removes the hypothesis
`GuptaTaharaMetabelian` from Lemmas 6.1 and 6.2 at `p = 3` (the `_three` versions at the end of the
file). The proof is the one of the internal wiki page 887, through Tahara's Theorem 6.1
(`taharaFiveOne`): every admissible family gives `g = 1`.

**The module.** In a group of class `≤ 4` with `γ₂` abelian, `γ₂` is a module over the commutative
ring `ℤ[G/γ₂]`. We compute in `E = Additive (Abelianization γ₂)` (equal to `γ₂` when `γ₂` is
abelian, `eq_one_of_em_eq_zero`) through `em : G → E`, the class of an element of `γ₂`; `Cm x` is
the action of `x` (`a ↦ x⁻¹ a x`) and `Tm x = Cm x - 1` is `a ↦ [a, x]` (`Tm_em`). The `Tm x`
commute (`Tm_comm`) and any three of them kill `E` (`Tm3`).

**Identities** (wiki 887, §2):
* `em_tc_pow_left`: `[xⁿ, y] = n c + C(n,2) t_x c + C(n,3) t_x² c`, `c = [x, y]`;
* `em_tc_pow_right`: `[a, xⁿ] = n t_x a + C(n,2) t_x² a` for `a ∈ γ₂`;
* `smul_Tm_eq_zero` (Lemma 2): `xⁿ ∈ γ₂`, `n` odd `⇒ n t_x = 0` on `E`;
* `smul_Tm_tc_eq_zero` (Lemma 3): `xⁿ, yⁿ ∈ γ₂`, `n` odd `⇒ n [x, y, z] = 0`.

**Tahara's generator** (§3): `genB = 1` (`[γ₂, γ₂] = 1`); `genC = 1` by (A₃), (A₄); in `genA`,
(C₁), (C₃) pair `u_{ij} q_{ij} [Y_i, x_j]` with `-u_{ij} [Y_j, x_i]` (`swap`), so
`2 genA = -∑_i [Z_i, x_i]`, and the row `i` of (B) and (E) gives `[Z_i, x_i] = 0` (`row`).
-/

namespace GroupDimension

namespace GuptaTahara

open Subgroup Tahara ExpThree ClassFour
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## The additive group `E` and the operators `Cm x`, `Tm x` -/

/-- `γ₂(G)`. -/
abbrev L1 (G : Type*) [Group G] : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries 1

/-- The additive group in which we compute: `γ₂` abelianised. -/
abbrev E (G : Type*) [Group G] := Additive (Abelianization (L1 G))

open Classical in
/-- The class in `E` of an element of `γ₂` (and `0` off `γ₂`). -/
noncomputable def em (g : G) : E G :=
  if h : g ∈ L1 G then Additive.ofMul (Abelianization.of (⟨g, h⟩ : L1 G)) else 0

theorem em_of {g : G} (h : g ∈ L1 G) :
    em g = Additive.ofMul (Abelianization.of (⟨g, h⟩ : L1 G)) := by
  unfold em
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem em_mul {a b : G} (ha : a ∈ L1 G) (hb : b ∈ L1 G) : em (a * b) = em a + em b := by
  have e : (⟨a * b, mul_mem ha hb⟩ : L1 G) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [em_of ha, em_of hb, em_of (mul_mem ha hb), e, map_mul, ofMul_mul]

theorem em_one : em (1 : G) = 0 := by
  have e : (⟨1, one_mem _⟩ : L1 G) = 1 := rfl
  rw [em_of (one_mem _), e, map_one, ofMul_one]

theorem em_zpow {a : G} (ha : a ∈ L1 G) (n : ℤ) : em (a ^ n) = n • em a := by
  have e : (⟨a ^ n, zpow_mem ha n⟩ : L1 G) = (⟨a, ha⟩ : L1 G) ^ n :=
    Subtype.ext (by rw [SubgroupClass.coe_zpow])
  rw [em_of ha, em_of (zpow_mem ha n), e, map_zpow, ofMul_zpow]

theorem em_pow {a : G} (ha : a ∈ L1 G) (n : ℕ) : em (a ^ n) = (n : ℤ) • em a := by
  rw [← em_zpow ha, zpow_natCast]

theorem em_inv {a : G} (ha : a ∈ L1 G) : em a⁻¹ = -em a := by
  rw [← zpow_neg_one, em_zpow ha, neg_one_smul]

theorem em_surj (v : E G) : ∃ a ∈ L1 G, em a = v := by
  obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = v := ⟨Additive.toMul v, rfl⟩
  refine QuotientGroup.induction_on y fun z => ?_
  exact ⟨z.1, z.2, by rw [em_of z.2]; rfl⟩

theorem em_ofFn_prod {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ L1 G) :
    em (List.ofFn f).prod = ∑ i, em (f i) := by
  have : ∀ l : List G, (∀ x ∈ l, x ∈ L1 G) → em l.prod = (l.map em).sum := by
    intro l
    induction l with
    | nil => intro _; simp [em_one]
    | cons x l ih =>
      intro hl
      rw [List.prod_cons, em_mul (hl x List.mem_cons_self)
        (list_prod_mem fun z hz => hl z (List.mem_cons_of_mem _ hz)),
        ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.sum_cons]
  rw [this _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hf i, List.map_ofFn,
    List.sum_ofFn]
  rfl

theorem em_oprod {n : ℕ} {y : Fin n → G} (hy : ∀ i, y i ∈ L1 G) (a : Fin n → ℤ) :
    em (oprod y a) = ∑ i, a i • em (y i) := by
  unfold oprod
  rw [em_ofFn_prod _ fun i => zpow_mem (hy i) _]
  exact Finset.sum_congr rfl fun i _ => em_zpow (hy i) _

theorem conjL {a : G} (ha : a ∈ L1 G) (x : G) : x⁻¹ * a * x ∈ L1 G := by
  have := conj_mem_lcs 1 ha x⁻¹
  rwa [inv_inv] at this

theorem tcL {a : G} (ha : a ∈ L1 G) (x : G) : tc a x ∈ L1 G :=
  lcs_mem_of_le (by norm_num) (tc_mem (i := 1) (j := 0) (n := 2) (by norm_num) ha (mem_lcs_zero x))

theorem tc_mem_L1 (x y : G) : tc x y ∈ L1 G :=
  tc_mem (i := 0) (j := 0) (n := 1) (by norm_num) (mem_lcs_zero x) (mem_lcs_zero y)

/-- Conjugation `a ↦ x⁻¹ a x` on `γ₂`, into the abelianisation. -/
noncomputable def conjHom (x : G) : L1 G →* Abelianization (L1 G) where
  toFun a := Abelianization.of (⟨x⁻¹ * a.1 * x, conjL a.2 x⟩ : L1 G)
  map_one' := by
    rw [← map_one (Abelianization.of (G := L1 G))]
    congr 1
    exact Subtype.ext (by simp)
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; group)

/-- The action of `x` on `E`. -/
noncomputable def Cm (x : G) : E G →+ E G :=
  MonoidHom.toAdditive (Abelianization.lift (conjHom x))

/-- `a ↦ [a, x]` on `E`. -/
noncomputable def Tm (x : G) : E G →+ E G := Cm x - AddMonoidHom.id (E G)

theorem Cm_em {a : G} (ha : a ∈ L1 G) (x : G) : Cm x (em a) = em (x⁻¹ * a * x) := by
  rw [em_of ha, em_of (conjL ha x)]
  show Additive.ofMul (Abelianization.lift (conjHom x) (Abelianization.of ⟨a, ha⟩)) = _
  rw [Abelianization.lift_apply_of]
  rfl

theorem Cm_eq (x : G) (v : E G) : Cm x v = v + Tm x v := by
  simp [Tm]

theorem em_tc {a : G} (ha : a ∈ L1 G) (x : G) : em (tc a x) = em (x⁻¹ * a * x) - em a := by
  have e : tc a x = a⁻¹ * (x⁻¹ * a * x) := by simp only [tc]; group
  rw [e, em_mul (inv_mem ha) (conjL ha x), em_inv ha]
  abel

theorem Tm_em {a : G} (ha : a ∈ L1 G) (x : G) : Tm x (em a) = em (tc a x) := by
  rw [em_tc ha, Tm, AddMonoidHom.sub_apply, Cm_em ha, AddMonoidHom.id_apply]

theorem Cm_Cm (x y : G) (v : E G) : Cm x (Cm y v) = Cm (y * x) v := by
  obtain ⟨a, ha, rfl⟩ := em_surj v
  rw [Cm_em ha, Cm_em (conjL ha y), Cm_em ha]
  congr 1
  group

theorem Tm_lcs3 {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 3)
    (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (x : G) : Tm x (em a) = 0 := by
  have h4 : tc a x ∈ (⊤ : Subgroup G).lowerCentralSeries 4 :=
    tc_mem (i := 3) (j := 0) (by norm_num) ha (mem_lcs_zero x)
  rw [h5, mem_bot] at h4
  rw [Tm_em (lcs_mem_of_le (by norm_num) ha), h4, em_one]

theorem Tm3 (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (x y z : G) (v : E G) :
    Tm x (Tm y (Tm z v)) = 0 := by
  obtain ⟨a, ha, rfl⟩ := em_surj v
  have h2 : tc a z ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (by norm_num) ha (mem_lcs_zero z)
  have h3 : tc (tc a z) y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (by norm_num) h2 (mem_lcs_zero y)
  rw [Tm_em ha, Tm_em (tcL ha z), Tm_lcs3 h3 h5]

/-! ## Metabelian: the `Tm x` commute, and `γ₂` embeds into `E` -/

section Metabelian

variable (hmet : ∀ a ∈ L1 G, ∀ b ∈ L1 G, a * b = b * a)
include hmet

theorem conj_swap {a : G} (ha : a ∈ L1 G) (x y : G) :
    (x * y)⁻¹ * a * (x * y) = (y * x)⁻¹ * a * (y * x) := by
  set c := tc x y
  have hxy : x * y = y * x * c := by simp only [c, tc]; group
  have hm : (y * x)⁻¹ * a * (y * x) ∈ L1 G := conjL ha (y * x)
  have hc : c ∈ L1 G := tc_mem_L1 x y
  rw [hxy]
  calc (y * x * c)⁻¹ * a * (y * x * c) = c⁻¹ * ((y * x)⁻¹ * a * (y * x)) * c := by group
    _ = c⁻¹ * (c * ((y * x)⁻¹ * a * (y * x))) := by
        rw [mul_assoc c⁻¹ ((y * x)⁻¹ * a * (y * x)) c, hmet _ hm _ hc]
    _ = (y * x)⁻¹ * a * (y * x) := by group

theorem Cm_swap (x y : G) (v : E G) : Cm (x * y) v = Cm (y * x) v := by
  obtain ⟨a, ha, rfl⟩ := em_surj v
  rw [Cm_em ha, Cm_em ha, conj_swap hmet ha]

theorem Tm_comm (x y : G) (v : E G) : Tm x (Tm y v) = Tm y (Tm x v) := by
  simp only [Tm, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub, Cm_Cm]
  rw [Cm_swap hmet y x]
  abel

theorem eq_one_of_em_eq_zero {a : G} (ha : a ∈ L1 G) (h : em a = 0) : a = 1 := by
  rw [em_of ha] at h
  have h1 : Abelianization.of (⟨a, ha⟩ : L1 G) = 1 := congrArg Additive.toMul h
  have hc : commutator (L1 G) = ⊥ := by
    show ⁅(⊤ : Subgroup (L1 G)), ⊤⁆ = ⊥
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (hmet _ y.2 _ x.2)
  have h2 : (⟨a, ha⟩ : L1 G) ∈ (Abelianization.of : L1 G →* Abelianization (L1 G)).ker := h1
  rw [Abelianization.ker_of, hc, mem_bot] at h2
  exact congrArg Subtype.val h2

theorem tc_eq_one_L1 {a b : G} (ha : a ∈ L1 G) (hb : b ∈ L1 G) : tc a b = 1 :=
  tc_eq_one_iff.mpr (hmet a ha b hb)

end Metabelian

/-! ## The identities -/

section Identities

variable (hmet : ∀ a ∈ L1 G, ∀ b ∈ L1 G, a * b = b * a)
  (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
include hmet h5

omit hmet in
/-- `[xⁿ, y] = n c + C(n,2) t_x c + C(n,3) t_x² c` with `c = [x, y]`. -/
theorem em_tc_pow_left (x y : G) (n : ℕ) :
    em (tc (x ^ n) y) = (n : ℤ) • em (tc x y) + ((n.choose 2 : ℕ) : ℤ) • Tm x (em (tc x y)) +
      ((n.choose 3 : ℕ) : ℤ) • Tm x (Tm x (em (tc x y))) := by
  have hc := tc_mem_L1 x y
  induction n with
  | zero => simp [tc, em_one]
  | succ n ih =>
    have hP : tc (x ^ n) y ∈ L1 G := tc_mem_L1 _ _
    have e : tc (x ^ (n + 1)) y = x⁻¹ * tc (x ^ n) y * x * tc x y := by
      rw [pow_succ, tc_mul_left]
    rw [e, em_mul (conjL hP x) hc, ← Cm_em hP, Cm_eq, ih]
    have h2 : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
    have h3 : (n + 1).choose 3 = n.choose 3 + n.choose 2 := by
      rw [Nat.choose_succ_succ']; ring
    have h0 : Tm x (Tm x (Tm x (em (tc x y)))) = 0 := Tm3 h5 x x x _
    rw [h2, h3]
    simp only [map_add, map_zsmul, h0, smul_zero, add_zero]
    push_cast
    module

omit hmet in
/-- `[a, xⁿ] = n t_x a + C(n,2) t_x² a` for `a ∈ γ₂`. -/
theorem em_tc_pow_right {a : G} (ha : a ∈ L1 G) (x : G) (n : ℕ) :
    em (tc a (x ^ n)) = (n : ℤ) • Tm x (em a) + ((n.choose 2 : ℕ) : ℤ) • Tm x (Tm x (em a)) := by
  induction n with
  | zero => simp [tc, em_one]
  | succ n ih =>
    have hP : tc a (x ^ n) ∈ L1 G := tcL ha _
    have e : tc a (x ^ (n + 1)) = tc a x * (x⁻¹ * tc a (x ^ n) * x) := by
      rw [pow_succ, tc_mul_right]
    rw [e, em_mul (tcL ha x) (conjL hP x), ← Cm_em hP, Cm_eq, ih, ← Tm_em ha]
    have h2 : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
    have h0 : Tm x (Tm x (Tm x (em a))) = 0 := Tm3 h5 x x x _
    rw [h2]
    simp only [map_add, map_zsmul, h0, smul_zero, add_zero]
    push_cast
    module

omit hmet h5 in
theorem choose_two_of_odd {n : ℕ} (hn : Odd n) : n.choose 2 = n * (n / 2) := by
  obtain ⟨k, rfl⟩ := hn
  rw [Nat.choose_two_right, show 2 * k + 1 - 1 = 2 * k by omega,
    show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]

omit hmet h5 in
theorem smul_eq_zero_of_dvd {d a : ℤ} {v : E G} (h : d ∣ a) (hv : d • v = 0) : a • v = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [mul_comm, mul_smul, hv, smul_zero]

/-- **Lemma 2.** If `xⁿ ∈ γ₂` with `n` odd, then `n · [a, x] = 0` for all `a ∈ γ₂`. -/
theorem smul_Tm_eq_zero {x : G} {n : ℕ} (hn : Odd n) (hx : x ^ n ∈ L1 G) (v : E G) :
    (n : ℤ) • Tm x v = 0 := by
  have key : ∀ a ∈ L1 G, (n : ℤ) • Tm x (em a) + ((n.choose 2 : ℕ) : ℤ) • Tm x (Tm x (em a)) = 0 :=
    fun a ha => by rw [← em_tc_pow_right h5 ha, tc_eq_one_L1 hmet ha hx, em_one]
  obtain ⟨a, ha, rfl⟩ := em_surj v
  have k2 := key _ (tcL ha x)
  rw [← Tm_em ha, Tm3 h5 x x x, smul_zero, add_zero] at k2
  have hd2 : (n : ℤ) ∣ ((n.choose 2 : ℕ) : ℤ) := by
    rw [choose_two_of_odd hn]; push_cast; exact dvd_mul_right _ _
  have k1 := key a ha
  rw [smul_eq_zero_of_dvd hd2 k2, add_zero] at k1
  exact k1

/-- **Lemma 3.** If `xⁿ, yⁿ ∈ γ₂` with `n` odd, then `n · [x, y, z] = 0`. -/
theorem smul_Tm_tc_eq_zero {x y : G} {n : ℕ} (hn : Odd n) (hx : x ^ n ∈ L1 G) (hy : y ^ n ∈ L1 G)
    (z : G) : (n : ℤ) • Tm z (em (tc x y)) = 0 := by
  have hd2 : (n : ℤ) ∣ ((n.choose 2 : ℕ) : ℤ) := by
    rw [choose_two_of_odd hn]; push_cast; exact dvd_mul_right _ _
  have hX := Tm_comm hmet z y (em (x ^ n))
  rw [Tm_em hx, Tm_em hx, em_tc_pow_left h5, em_tc_pow_left h5] at hX
  simp only [map_add, map_zsmul] at hX
  have e1 : Tm z (Tm x (Tm x (em (tc x y)))) = 0 := by
    rw [Tm_comm hmet z x, Tm_comm hmet z x, ← Tm_comm hmet x x]; exact Tm3 h5 x x z _
  have e2 : Tm y (Tm x (Tm x (em (tc x z)))) = 0 := by
    rw [Tm_comm hmet y x, Tm_comm hmet y x]; exact Tm3 h5 x x y _
  have e3 : ((n.choose 2 : ℕ) : ℤ) • Tm z (Tm x (em (tc x y))) = 0 := by
    rw [Tm_comm hmet z x]
    exact smul_eq_zero_of_dvd hd2 (smul_Tm_eq_zero hmet h5 hn hx _)
  have e4 : ((n.choose 2 : ℕ) : ℤ) • Tm y (Tm x (em (tc x z))) = 0 := by
    rw [Tm_comm hmet y x]
    exact smul_eq_zero_of_dvd hd2 (smul_Tm_eq_zero hmet h5 hn hx _)
  have e5 : (n : ℤ) • Tm y (em (tc x z)) = 0 := smul_Tm_eq_zero hmet h5 hn hy _
  rw [e1, e2, e3, e4, e5] at hX
  simp only [smul_zero, add_zero] at hX
  exact hX

end Identities

/-! ## Tahara's generator -/

section Gen

variable (hmet : ∀ a ∈ L1 G, ∀ b ∈ L1 G, a * b = b * a)
  (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  (hodd : ∀ i, Odd (T.d i))
include hmet h5 hT hodd

omit hmet h5 hodd in
theorem Y_mem (i : Fin T.s) : T.x₁ i ^ T.d i ∈ L1 G := Passi.pow_d_mem hT i

omit hmet h5 hodd in
theorem pow_d_mem_of_le {i j : Fin T.s} (hij : i ≤ j) : T.x₁ i ^ T.d j ∈ L1 G := by
  rw [← Nat.mul_div_cancel' (hT.basis₁.dvd i j hij), pow_mul]
  exact pow_mem (Y_mem hT i) _

omit hmet h5 hodd in
theorem dq {i j : Fin T.s} (hij : i ≤ j) : (T.d i : ℤ) * T.q i j = T.d j := by
  simp only [Data.q]; exact_mod_cast Nat.mul_div_cancel' (hT.basis₁.dvd i j hij)

omit hmet h5 hT hodd in
theorem d_dvd_ch2 {i : Fin T.s} (hodd' : Odd (T.d i)) : (T.d i : ℤ) ∣ T.ch i 2 := by
  simp only [Data.ch]; rw [choose_two_of_odd hodd']; push_cast; exact dvd_mul_right _ _

/-- Lemma 2 at `x_i`. -/
theorem L2 (i : Fin T.s) (v : E G) : (T.d i : ℤ) • Tm (T.x₁ i) v = 0 :=
  smul_Tm_eq_zero hmet h5 (hodd i) (Y_mem hT i) v

/-- Lemma 3 at `(x_g, x_j)`, `g ≤ j`. -/
theorem L3 {g j : Fin T.s} (hgj : g ≤ j) (z : G) :
    (T.d j : ℤ) • Tm z (em (tc (T.x₁ g) (T.x₁ j))) = 0 :=
  smul_Tm_tc_eq_zero hmet h5 (hodd j) (pow_d_mem_of_le hT hgj) (Y_mem hT j) z

omit hmet hodd in
/-- `[Y_g, x_h] = d c + C(d,2) t_g c + C(d,3) t_g² c`. -/
theorem TY (g h : Fin T.s) : Tm (T.x₁ h) (em (T.x₁ g ^ T.d g)) =
    (T.d g : ℤ) • em (tc (T.x₁ g) (T.x₁ h)) +
      ((T.d g).choose 2 : ℤ) • Tm (T.x₁ g) (em (tc (T.x₁ g) (T.x₁ h))) +
      ((T.d g).choose 3 : ℤ) • Tm (T.x₁ g) (Tm (T.x₁ g) (em (tc (T.x₁ g) (T.x₁ h)))) := by
  rw [Tm_em (Y_mem hT g), em_tc_pow_left h5]

/-- `[Y_g, x_h, x_k] = d(g) [x_g, x_h, x_k]`. -/
theorem TTY (g h k : Fin T.s) : Tm (T.x₁ k) (Tm (T.x₁ h) (em (T.x₁ g ^ T.d g))) =
    (T.d g : ℤ) • Tm (T.x₁ k) (em (tc (T.x₁ g) (T.x₁ h))) := by
  rw [TY h5 hT]
  simp only [map_add, map_zsmul]
  have e1 : Tm (T.x₁ k) (Tm (T.x₁ g) (Tm (T.x₁ g) (em (tc (T.x₁ g) (T.x₁ h))))) = 0 := by
    rw [Tm_comm hmet _ (T.x₁ g), Tm_comm hmet _ (T.x₁ g)]; exact Tm3 h5 _ _ _ _
  have e2 : ((T.d g).choose 2 : ℤ) • Tm (T.x₁ k) (Tm (T.x₁ g) (em (tc (T.x₁ g) (T.x₁ h)))) = 0 := by
    rw [Tm_comm hmet _ (T.x₁ g)]
    exact smul_eq_zero_of_dvd (d_dvd_ch2 (hodd g)) (L2 hmet h5 hT hodd g _)
  rw [e1, e2, smul_zero, add_zero, add_zero]

omit hmet h5 hodd in
theorem TY_self (i : Fin T.s) : Tm (T.x₁ i) (em (T.x₁ i ^ T.d i)) = 0 := by
  rw [Tm_em (Y_mem hT i), tc_eq_one_iff.mpr ((Commute.refl _).pow_left _), em_one]

omit hmet h5 in
/-- (A₃), (A₄): `d(b) ∣ w_{abc} d(a)` for `a < b ≤ c`. -/
theorem w_div {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {a b c : Fin T.s} (hab : a < b)
    (hbc : b ≤ c) : ∃ r : ℤ, τ.w a b c * T.d a = T.d b * r := by
  rcases lt_or_eq_of_le hbc with hlt | rfl
  · have h := hτ.A₄ a b c hab hlt
    have hq := dq hT hbc
    exact ⟨-τ.w' a b c - τ.w'' a b c * T.q b c, by rw [← hq] at h; linear_combination h⟩
  · have h := hτ.A₃ a b hab
    obtain ⟨m, hm⟩ := d_dvd_ch2 (hodd b)
    exact ⟨τ.u a b * m - τ.w' a b b, by rw [hm] at h; linear_combination h⟩

/-- `w_{ijk} [Y_i, x_j, x_k] = 0` for `i ≤ j ≤ k`. -/
theorem w_term {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {i j k : Fin T.s} (hij : i ≤ j)
    (hjk : j ≤ k) (k' : Fin T.s) :
    τ.w i j k • Tm (T.x₁ k') (Tm (T.x₁ j) (em (T.x₁ i ^ T.d i))) = 0 := by
  rcases lt_or_eq_of_le hij with hlt | rfl
  · obtain ⟨r, hr⟩ := w_div hT hodd hτ hlt hjk
    rw [TTY h5 hT hodd, smul_smul, hr, mul_comm, mul_smul, L3 hmet h5 hT hodd hlt.le,
      smul_zero]
  · rw [TY_self hT, map_zero, smul_zero]

omit h5 hodd in
theorem genB_eq (τ : Coeffs T.s T.t) : T.genB τ = 1 := by
  have : ∀ l k, tc (T.x₂ l) (T.x₂ k) = 1 := fun l k =>
    tc_eq_one_L1 hmet (hT.basis₂.mem l) (hT.basis₂.mem k)
  simp [Data.genB, this]

theorem genC_eq {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) : T.genC τ = 1 := by
  unfold Data.genC
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  refine List.prod_eq_one fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
  split_ifs with hijk
  · have hm : tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) ∈ L1 G := tcL (tcL (Y_mem hT i) _) _
    refine eq_one_of_em_eq_zero hmet (zpow_mem hm _) ?_
    rw [em_zpow hm, ← Tm_em (tcL (Y_mem hT i) _), ← Tm_em (Y_mem hT i)]
    exact w_term hmet h5 hT hodd hτ hijk.1 hijk.2 k
  · rfl

/-- (C₁), (C₃): `u_{ij} q_{ij} [Y_i, x_j] = -u_{ij} [Y_j, x_i]`. -/
theorem swap {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {i j : Fin T.s} (hij : i < j) :
    (τ.u i j * T.q i j) • Tm (T.x₁ j) (em (T.x₁ i ^ T.d i)) =
      -(τ.u i j • Tm (T.x₁ i) (em (T.x₁ j ^ T.d j))) := by
  set c := em (tc (T.x₁ i) (T.x₁ j)) with hc
  have hc' : em (tc (T.x₁ j) (T.x₁ i)) = -c := by
    rw [← tc_inv, em_inv (tc_mem_L1 _ _)]
  have hA := TY h5 hT i j
  have hB := TY h5 hT j i
  rw [hc'] at hB
  simp only [map_neg, smul_neg] at hB
  -- vanishing pieces
  have z1 : ((T.d i).choose 2 : ℤ) • Tm (T.x₁ i) c = 0 :=
    smul_eq_zero_of_dvd (d_dvd_ch2 (hodd i)) (L2 hmet h5 hT hodd i _)
  have z2 : ((T.d j).choose 2 : ℤ) • Tm (T.x₁ j) c = 0 :=
    smul_eq_zero_of_dvd (d_dvd_ch2 (hodd j)) (L2 hmet h5 hT hodd j _)
  have hC1 : (T.d i : ℤ) ∣ τ.u i j * T.q i j * ((T.d i).choose 3 : ℤ) := by
    have h := Int.modEq_zero_iff_dvd.mp (hτ.C₁ i j hij)
    simp only [Data.ch] at h
    have h2 : (T.d i : ℤ) ∣ τ.w i i j * ((T.d i).choose 2 : ℤ) :=
      dvd_mul_of_dvd_right (by simpa [Data.ch] using d_dvd_ch2 (hodd i)) _
    simpa using dvd_sub h h2
  have hC3 : (T.d i : ℤ) ∣ τ.u i j * ((T.d j).choose 3 : ℤ) := by
    have h := Int.modEq_zero_iff_dvd.mp (hτ.C₃ i j hij)
    simp only [Data.ch] at h
    have hdj : (T.d i : ℤ) ∣ ((T.d j).choose 2 : ℤ) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (hT.basis₁.dvd i j hij.le))
        (by simpa [Data.ch] using d_dvd_ch2 (hodd j))
    have h2 : (T.d i : ℤ) ∣ τ.w' i j j * ((T.d j).choose 2 : ℤ) := dvd_mul_of_dvd_right hdj _
    have h3 := dvd_sub h2 h
    have e : τ.w' i j j * ((T.d j).choose 2 : ℤ) -
        (-τ.u i j * ((T.d j).choose 3 : ℤ) + τ.w' i j j * ((T.d j).choose 2 : ℤ)) =
        τ.u i j * ((T.d j).choose 3 : ℤ) := by ring
    rwa [e] at h3
  have hdTT : (T.d i : ℤ) • Tm (T.x₁ j) (Tm (T.x₁ j) c) = 0 := by
    have h := congrArg (fun v => Tm (T.x₁ j) (Tm (T.x₁ j) v)) hA
    simp only [Tm3 h5, map_add, map_zsmul, smul_zero, add_zero] at h
    exact h.symm
  have z3 : (τ.u i j * T.q i j * ((T.d i).choose 3 : ℤ)) • Tm (T.x₁ i) (Tm (T.x₁ i) c) = 0 :=
    smul_eq_zero_of_dvd hC1 (L2 hmet h5 hT hodd i _)
  have z4 : (τ.u i j * ((T.d j).choose 3 : ℤ)) • Tm (T.x₁ j) (Tm (T.x₁ j) c) = 0 :=
    smul_eq_zero_of_dvd hC3 hdTT
  have hq := dq hT hij.le
  rw [hA, hB]
  rw [← sub_eq_zero, sub_neg_eq_add]
  have key : (τ.u i j * T.q i j) • ((T.d i : ℤ) • c + ((T.d i).choose 2 : ℤ) • Tm (T.x₁ i) c +
      ((T.d i).choose 3 : ℤ) • Tm (T.x₁ i) (Tm (T.x₁ i) c)) +
      τ.u i j • (-((T.d j : ℤ) • c) + -(((T.d j).choose 2 : ℤ) • Tm (T.x₁ j) c) +
        -(((T.d j).choose 3 : ℤ) • Tm (T.x₁ j) (Tm (T.x₁ j) c))) =
      (τ.u i j * (T.d i * T.q i j - T.d j)) • c +
        (τ.u i j * T.q i j) • (((T.d i).choose 2 : ℤ) • Tm (T.x₁ i) c) -
        τ.u i j • (((T.d j).choose 2 : ℤ) • Tm (T.x₁ j) c) +
        (τ.u i j * T.q i j * ((T.d i).choose 3 : ℤ)) • Tm (T.x₁ i) (Tm (T.x₁ i) c) -
        (τ.u i j * ((T.d j).choose 3 : ℤ)) • Tm (T.x₁ j) (Tm (T.x₁ j) c) := by
    module
  rw [key, z1, z2, z3, z4, hq, sub_self, mul_zero, zero_smul]
  simp

omit hmet h5 hodd in
/-- `em` of the `u`-part. -/
theorem em_genA (τ : Coeffs T.s T.t) : em (T.genA τ) = ∑ i, ∑ j,
    if i < j then (τ.u i j * T.q i j) • Tm (T.x₁ j) (em (T.x₁ i ^ T.d i)) else 0 := by
  have hite : ∀ i j, (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1) ∈
      L1 G := fun i j => by
    split_ifs
    · exact zpow_mem (tcL (Y_mem hT i) _) _
    · exact one_mem _
  rw [Data.genA, em_ofFn_prod _ fun i => list_prod_mem fun z hz => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz; exact hite i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [em_ofFn_prod _ (hite i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [em_zpow (tcL (Y_mem hT i) _), Tm_em (Y_mem hT i)]
  · exact em_one

omit hmet h5 hodd in
theorem genA_mem (τ : Coeffs T.s T.t) : T.genA τ ∈ L1 G :=
  list_prod_mem fun z hz => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact list_prod_mem fun w hw => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      split_ifs
      · exact zpow_mem (tcL (Y_mem hT i) _) _
      · exact one_mem _

omit hmet hT hodd in
/-- `[g, x] = [h, x]` when `h⁻¹ g ∈ γ₄`. -/
theorem Tm_em_eq_of_mem {g h : G} (hh : h ∈ L1 G)
    (hr : h⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (x : G) :
    Tm x (em g) = Tm x (em h) := by
  have e : g = h * (h⁻¹ * g) := by group
  have hr1 : h⁻¹ * g ∈ L1 G := lcs_mem_of_le (by norm_num) hr
  rw [e, em_mul hh hr1, map_add, Tm_lcs3 hr h5, add_zero]

omit hmet h5 hodd in
theorem x2_mem (k : Fin T.t) : T.x₂ k ∈ L1 G := hT.basis₂.mem k

omit hmet h5 hodd in
theorem x3_mem (l : Fin T.u) : T.x₃ l ∈ L1 G := lcs_mem_of_le (by norm_num) (hT.basis₃.mem l)

/-- `[Y_h, x] = ∑_k b_{hk} [x_{2k}, x] + ∑_l c_{hl} [x_{3l}, x]`. -/
theorem KY (h : Fin T.s) (x : G) : Tm x (em (T.x₁ h ^ T.d h)) =
    ∑ k, T.b h k • Tm x (em (T.x₂ k)) + ∑ l, T.c h l • Tm x (em (T.x₃ l)) := by
  have hP : oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h) ∈ L1 G :=
    mul_mem (oprod_mem (x2_mem hT) _) (oprod_mem (x3_mem hT) _)
  rw [Tm_em_eq_of_mem h5 hP (hT.hb h),
    em_mul (oprod_mem (x2_mem hT) _) (oprod_mem (x3_mem hT) _),
    em_oprod (x2_mem hT), em_oprod (x3_mem hT)]
  simp only [map_add, map_sum, map_zsmul]

/-- `e(k) [x_{2k}, x] = ∑_l d_{kl} [x_{3l}, x]`. -/
theorem KE (k : Fin T.t) (x : G) : (T.e k : ℤ) • Tm x (em (T.x₂ k)) =
    ∑ l, T.dd k l • Tm x (em (T.x₃ l)) := by
  rw [← map_zsmul, ← em_pow (x2_mem hT k),
    Tm_em_eq_of_mem h5 (oprod_mem (x3_mem hT) _) (hT.hdd k),
    em_oprod (x3_mem hT)]
  simp only [map_sum, map_zsmul]

/-- `[Y_g, x_h, x] = ∑_l α^{(gh)}_l [x_{3l}, x]` for `g ≤ h`. -/
theorem KA {g h : Fin T.s} (hgh : g ≤ h) (x : G) :
    Tm x (Tm (T.x₁ h) (em (T.x₁ g ^ T.d g))) = ∑ l, T.α g h l • Tm x (em (T.x₃ l)) := by
  rw [Tm_em (Y_mem hT g),
    Tm_em_eq_of_mem h5 (oprod_mem (x3_mem hT) _)
      (hT.hα g h hgh),
    em_oprod (x3_mem hT)]
  simp only [map_sum, map_zsmul]

omit hmet h5 hT hodd in
theorem rearr2 {s u : ℕ} (P : Fin s → Fin s → Prop) [DecidableRel P] (w : Fin s → Fin s → ℤ)
    (α : Fin s → Fin s → Fin u → ℤ) (X : Fin u → E G) :
    ∑ l, (∑ g, ∑ h, if P g h then w g h * α g h l else 0) • X l =
      ∑ g, ∑ h, if P g h then w g h • ∑ l, α g h l • X l else 0 := by
  have e : ∀ g h, (if P g h then w g h • ∑ l, α g h l • X l else 0) =
      ∑ l, (if P g h then w g h * α g h l else 0) • X l := by
    intro g h; split_ifs <;> simp [Finset.smul_sum, mul_smul]
  simp only [e, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_comm

omit hmet h5 hT hodd in
theorem rearr1 {s u : ℕ} (P : Fin s → Prop) [DecidablePred P] (w : Fin s → ℤ)
    (α : Fin s → Fin u → ℤ) (X : Fin u → E G) :
    ∑ l, (∑ h, if P h then w h * α h l else 0) • X l =
      ∑ h, if P h then w h • ∑ l, α h l • X l else 0 := by
  have e : ∀ h, (if P h then w h • ∑ l, α h l • X l else 0) =
      ∑ l, (if P h then w h * α h l else 0) • X l := by
    intro h; split_ifs <;> simp [Finset.smul_sum, mul_smul]
  simp only [e, Finset.sum_smul]
  exact Finset.sum_comm

/-- **The row `i`**: (B) and (E) give `∑_{h>i} u_{ih} [Y_h, x_i] = ∑_{h<i} u_{hi} q_{hi} [Y_h, x_i]`. -/
theorem row {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) (i : Fin T.s) :
    ∑ h, (if i < h then τ.u i h else 0) • Tm (T.x₁ i) (em (T.x₁ h ^ T.d h)) =
      ∑ h, (if h < i then τ.u h i * T.q h i else 0) • Tm (T.x₁ i) (em (T.x₁ h ^ T.d h)) := by
  classical
  set X : Fin T.u → E G := fun l => Tm (T.x₁ i) (em (T.x₃ l)) with hXdef
  set X2 : Fin T.t → E G := fun k => Tm (T.x₁ i) (em (T.x₂ k)) with hX2def
  have hdX : ∀ l, (T.d i : ℤ) • X l = 0 := fun l => L2 hmet h5 hT hodd i _
  have hdX2 : ∀ k, (T.d i : ℤ) • X2 k = 0 := fun k => L2 hmet h5 hT hodd i _
  have KY' : ∀ h, Tm (T.x₁ i) (em (T.x₁ h ^ T.d h)) =
      ∑ k, T.b h k • X2 k + ∑ l, T.c h l • X l := fun h => KY hmet h5 hT hodd h _
  have KE' : ∀ k, (T.e k : ℤ) • X2 k = ∑ l, T.dd k l • X l := fun k => KE hmet h5 hT hodd k _
  have KA' : ∀ g h, g ≤ h → Tm (T.x₁ i) (Tm (T.x₁ h) (em (T.x₁ g ^ T.d g))) =
      ∑ l, T.α g h l • X l := fun g h hgh => KA hmet h5 hT hodd hgh _
  -- the vanishing of the `α`-terms
  have hZ1 : ∑ h, (if h < i then (τ.u h i * T.q h i) • ∑ l, T.α h i l • X l else 0) = 0 := by
    refine Finset.sum_eq_zero fun h _ => ?_
    split_ifs with hhi
    · rw [← KA' h i hhi.le, TTY h5 hT hodd, smul_smul,
        show τ.u h i * T.q h i * (T.d h : ℤ) = τ.u h i * ((T.d h : ℤ) * T.q h i) by ring,
        dq hT hhi.le, mul_smul, L2 hmet h5 hT hodd i, smul_zero]
    · rfl
  have hZ2 : ∑ g, ∑ h, (if g ≤ i ∧ i ≤ h then τ.w g i h • ∑ l, T.α g h l • X l else 0) = 0 := by
    refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun h _ => ?_
    split_ifs with hc
    · rw [← KA' g h (hc.1.trans hc.2), Tm_comm hmet]
      exact w_term hmet h5 hT hodd hτ hc.1 hc.2 h
    · rfl
  have hZ3 : ∑ g, ∑ h, (if g ≤ h ∧ h ≤ i then τ.w g h i • ∑ l, T.α g h l • X l else 0) = 0 := by
    refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun h _ => ?_
    split_ifs with hc
    · rw [← KA' g h hc.1]
      exact w_term hmet h5 hT hodd hτ hc.1 hc.2 i
    · rfl
  have hZ4 : ∑ g, ∑ h, (if i < g ∧ g ≤ h then τ.w' i g h • ∑ l, T.α g h l • X l else 0) = 0 := by
    refine Finset.sum_eq_zero fun g _ => Finset.sum_eq_zero fun h _ => ?_
    split_ifs with hc
    · rw [← KA' g h hc.2, Tm_comm hmet, TTY h5 hT hodd,
        show tc (T.x₁ g) (T.x₁ i) = (tc (T.x₁ i) (T.x₁ g))⁻¹ from (tc_inv _ _).symm,
        em_inv (tc_mem_L1 _ _), map_neg, smul_neg, L3 hmet h5 hT hodd hc.1.le, neg_zero,
        smul_zero]
    · rfl
  -- (E), multiplied by `X l` and summed over `l`
  have hE : ∀ l, ((-(∑ h, if h < i then τ.u h i * T.q h i * T.α h i l else 0)
      + (∑ h, if i < h then τ.u i h * T.c h l else 0)
      - (∑ h, if h < i then τ.u h i * T.q h i * T.c h l else 0)
      - (∑ k, τ.v' i k * T.dd k l)
      - (∑ g, ∑ h, if g ≤ i ∧ i ≤ h then τ.w g i h * T.α g h l else 0)
      - (∑ g, ∑ h, if g ≤ h ∧ h ≤ i then τ.w g h i * T.α g h l else 0)
      - (∑ g, ∑ h, if i < g ∧ g ≤ h then τ.w' i g h * T.α g h l else 0)) • X l) = 0 := by
    intro l
    refine smul_eq_zero_of_dvd (d := (Nat.gcd (T.d i) (T.f l) : ℤ))
      (Int.modEq_zero_iff_dvd.mp (hτ.E i l)) ?_
    have hf : (T.f l : ℤ) • X l = 0 := by
      show (T.f l : ℤ) • Tm (T.x₁ i) (em (T.x₃ l)) = 0
      rw [← map_zsmul, ← em_pow (x3_mem hT l)]
      exact Tm_lcs3 (hT.basis₃.pow_mem l) h5 _
    rw [Nat.gcd_eq_gcd_ab, add_smul, mul_comm (T.d i : ℤ), mul_smul, mul_comm (T.f l : ℤ), mul_smul,
      hdX l, hf, smul_zero, smul_zero, add_zero]
  have hEsum := Finset.sum_eq_zero (s := Finset.univ) fun l (_ : l ∈ Finset.univ) => hE l
  simp only [add_smul, sub_smul, neg_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at hEsum
  have e1 : ∑ l, (∑ h, if h < i then τ.u h i * T.q h i * T.α h i l else 0) • X l = 0 := by
    rw [rearr1 (fun h => h < i) (fun h => τ.u h i * T.q h i) (fun h l => T.α h i l) X]; exact hZ1
  have e2 : ∑ l, (∑ g, ∑ h, if g ≤ i ∧ i ≤ h then τ.w g i h * T.α g h l else 0) • X l = 0 := by
    rw [rearr2 (fun g h => g ≤ i ∧ i ≤ h) (fun g h => τ.w g i h) T.α X]; exact hZ2
  have e3 : ∑ l, (∑ g, ∑ h, if g ≤ h ∧ h ≤ i then τ.w g h i * T.α g h l else 0) • X l = 0 := by
    rw [rearr2 (fun g h => g ≤ h ∧ h ≤ i) (fun g h => τ.w g h i) T.α X]; exact hZ3
  have e4 : ∑ l, (∑ g, ∑ h, if i < g ∧ g ≤ h then τ.w' i g h * T.α g h l else 0) • X l = 0 := by
    rw [rearr2 (fun g h => i < g ∧ g ≤ h) (fun g h => τ.w' i g h) T.α X]; exact hZ4
  rw [e1, e2, e3, e4, neg_zero, zero_add, sub_zero, sub_zero, sub_zero] at hEsum
  -- (B), multiplied by `X2 k`
  have hB : ∀ k, ((∑ h, if i < h then τ.u i h * T.b h k else 0)
      - (∑ h, if h < i then τ.u h i * T.q h i * T.b h k else 0)) • X2 k =
      -(τ.v' i k • ∑ l, T.dd k l • X l) := by
    intro k
    have hb := hτ.B i k
    have e : (∑ h, if i < h then τ.u i h * T.b h k else 0)
        - (∑ h, if h < i then τ.u h i * T.q h i * T.b h k else 0) =
        -(τ.v i k * T.d i) - τ.v' i k * T.e k := by linear_combination hb
    rw [e, sub_smul, neg_smul, mul_smul, mul_smul, hdX2 k, smul_zero, neg_zero, zero_sub, KE' k]
  have hvd : ∑ k, τ.v' i k • ∑ l, T.dd k l • X l = ∑ l, (∑ k, τ.v' i k * T.dd k l) • X l := by
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  -- the two sides
  have hlhs : ∀ h, (if i < h then τ.u i h else 0) • Tm (T.x₁ i) (em (T.x₁ h ^ T.d h)) -
      (if h < i then τ.u h i * T.q h i else 0) • Tm (T.x₁ i) (em (T.x₁ h ^ T.d h)) =
      ∑ k, ((if i < h then τ.u i h * T.b h k else 0)
        - (if h < i then τ.u h i * T.q h i * T.b h k else 0)) • X2 k +
      ∑ l, ((if i < h then τ.u i h * T.c h l else 0)
        - (if h < i then τ.u h i * T.q h i * T.c h l else 0)) • X l := by
    intro h
    rw [← sub_smul, KY' h, smul_add, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul]; congr 1; split_ifs <;> ring
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul]; congr 1; split_ifs <;> ring
  have s1 : ∑ h, ∑ k, ((if i < h then τ.u i h * T.b h k else 0)
        - (if h < i then τ.u h i * T.q h i * T.b h k else 0)) • X2 k =
      ∑ k, ((∑ h, if i < h then τ.u i h * T.b h k else 0)
        - (∑ h, if h < i then τ.u h i * T.q h i * T.b h k else 0)) • X2 k := by
    simp only [← Finset.sum_sub_distrib, Finset.sum_smul]
    exact Finset.sum_comm
  have s2 : ∑ h, ∑ l, ((if i < h then τ.u i h * T.c h l else 0)
        - (if h < i then τ.u h i * T.q h i * T.c h l else 0)) • X l =
      ∑ l, (∑ h, if i < h then τ.u i h * T.c h l else 0) • X l
        - ∑ l, (∑ h, if h < i then τ.u h i * T.q h i * T.c h l else 0) • X l := by
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul, ← Finset.sum_sub_distrib, Finset.sum_smul]
    exact Finset.sum_comm
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun h _ => hlhs h,
    Finset.sum_add_distrib, s1, s2, Finset.sum_congr rfl fun k _ => hB k, Finset.sum_neg_distrib,
    hvd, ← hEsum]
  abel

/-- **Every generator of Tahara's Theorem 6.1 has order `≤ 2`** (`gen τ = genA τ` and
`2 genA = 0`). -/
theorem gen_sq {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) : T.gen τ ^ 2 = 1 := by
  classical
  rw [Data.gen, genB_eq hmet hT, genC_eq hmet h5 hT hodd hτ, mul_one, mul_one]
  set K : Fin T.s → Fin T.s → E G := fun h i => Tm (T.x₁ i) (em (T.x₁ h ^ T.d h)) with hK
  have hX := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => row hmet h5 hT hodd hτ i
  have hY : (∑ i, ∑ h, (if h < i then τ.u h i * T.q h i else 0) • K h i) =
      -∑ i, ∑ h, (if i < h then τ.u i h else 0) • K h i := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hhi
    · exact swap hmet h5 hT hodd hτ hhi
    · simp
  have hg : em (T.genA τ) = ∑ i, ∑ h, (if h < i then τ.u h i * T.q h i else 0) • K h i := by
    rw [em_genA hT, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hK]
  have h2 : (2 : ℤ) • em (T.genA τ) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hg]
    rw [hY, hX, ← hg, neg_add_cancel]
  have hmem := genA_mem hT τ
  have hsq : T.genA τ ^ (2 : ℤ) = 1 :=
    eq_one_of_em_eq_zero hmet (zpow_mem hmem _) (by rw [em_zpow hmem]; exact h2)
  exact_mod_cast hsq

end Gen

/-- In a `p`-group with `p` odd, `g² = 1` forces `g = 1`. -/
theorem eq_one_of_sq_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hG : IsPGroup p G) {g : G}
    (h : g ^ 2 = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hG) g
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [hk] at h2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at h2
    · have hdv : p ∣ 2 := h2 ▸ dvd_pow_self p hk0.ne'
      rcases (Nat.dvd_prime Nat.prime_two).mp hdv with h3 | h3
      · exact hp.out.one_lt.ne' h3
      · exact hp2 h3

/-! ## The theorem -/

/-- **`D₅ = 1` for a finite metabelian `p`-group of class `≤ 4`, `p` odd** (via `taharaFiveOne`). -/
theorem D_five_eq_bot_of_metabelian {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {Q : Type}
    [Group Q] [Finite Q] (hQ : IsPGroup p Q) (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (hmet : ∀ a ∈ L1 Q, ∀ b ∈ L1 Q, a * b = b * a) : D 5 Q = ⊥ := by
  obtain ⟨T, hT⟩ := Passi.exists_valid_data hQ
  have hodd : ∀ i, Odd (T.d i) := fun i => by
    obtain ⟨m, hm⟩ := (TaharaProof.IsLayerBasis.layerNF hT.basis₁).exists_pow hQ i
    rw [hm]
    exact (hp.out.odd_of_ne_two hp2).pow
  refine eq_bot_iff.mpr ((taharaFiveOne Q h5 T hT).trans ?_)
  rw [Subgroup.closure_le]
  rintro z ⟨τ, hτ, rfl⟩
  exact (mem_bot (G := Q)).mpr (eq_one_of_sq_eq_one hp2 hQ (gen_sq hmet h5 hT hodd hτ))

/-- **`D₅ = γ₅` when `G/γ₂` is a finite `p`-group, `p` odd, and `[γ₂, γ₂] ⊆ γ₅`** (wiki 887;
for `p = 3` Gupta–Tahara [GT85, Thm. 3.2(c)]). -/
theorem D_five_eq_gamma_five_of_metabelian {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (G : Type)
    [Group G] (hfin : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (hpg : IsPGroup p (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1))
    (hmet : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      ⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 4) :
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4 := by
  refine le_antisymm (D_le_of_D_quotient_eq_bot _ 5 ?_) (gamma_le_D G 5 (by norm_num))
  have : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 4) := finite_quotient_lcs hfin 3
  set N := (⊤ : Subgroup G).lowerCentralSeries 4
  have hmetQ : ∀ a ∈ L1 (G ⧸ N), ∀ b ∈ L1 (G ⧸ N), a * b = b * a := by
    intro a ha b hb
    rw [L1, ← lcs_map_mk] at ha hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have h1 : QuotientGroup.mk' N ⁅a', b'⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hmet a' ha' b' hb')
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  -- `G/γ₅` is a `p`-group
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  have hM : ∀ y : G, y ^ p ^ m ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := fun y => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hm]
    exact pow_card_eq_one'
  have h1 := pow_succ_mem (k := 0) (n := p ^ m) (fun a _ => hM a)
  have h2 := pow_succ_mem (k := 1) (n := p ^ m) h1
  have h3 := pow_succ_mem (k := 2) (n := p ^ m) h2
  have hQp : IsPGroup p (G ⧸ N) := fun x => by
    refine ⟨4 * m, ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have e : y ^ p ^ (4 * m) = (((y ^ p ^ m) ^ p ^ m) ^ p ^ m) ^ p ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring
    rw [e]
    exact h3 _ (h2 _ (h1 _ (hM y)))
  exact D_five_eq_bot_of_metabelian hp2 hQp (lowerCentralSeries_quotient_eq_bot 4) hmetQ

end GuptaTahara

open Subgroup ClassFour GuptaTahara
open scoped commutatorElement

/-- Gupta–Tahara at `p = 3`: `D₅ = γ₅` for finite metabelian `3`-groups ([GT85, Thm. 3.2(c)];
the instance `p = 3` of `GuptaTaharaMetabelian`). -/
def GuptaTaharaMetabelianThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 3 G → derivedSeries G 2 = ⊥ →
    D 5 G = (⊤ : Subgroup G).lowerCentralSeries 4

theorem GuptaTaharaMetabelian.three (h : GuptaTaharaMetabelian) : GuptaTaharaMetabelianThree :=
  fun G _ _ hG hd => h 3 Nat.prime_three (by norm_num) G hG hd

/-- **Gupta–Tahara at `p = 3`**, proved (MATH-445). -/
theorem guptaTaharaMetabelian_three : GuptaTaharaMetabelianThree := by
  intro G _ _ hG hd
  refine D_five_eq_gamma_five_of_metabelian (p := 3) (by norm_num) G inferInstance
    (hG.to_quotient _) fun a ha b hb => ?_
  have h : ⁅a, b⁆ ∈ derivedSeries G 2 := by
    rw [derivedSeries_succ, derivedSeries_one]
    rw [Subgroup.top_lowerCentralSeries_one] at ha hb
    exact Subgroup.commutator_mem_commutator ha hb
  rw [hd, mem_bot] at h
  rw [h]
  exact one_mem _

/-! ## Lemmas 6.1 and 6.2 at `p = 3` without the hypothesis -/

section Three

variable {Q : Type} [Group Q] [Finite Q]

/-- **Lemma 6.1, `p = 3`** (`D_le_derivedSeries_two` without `GuptaTaharaMetabelian`):
`D₅(Q) ⊆ Q''` for a finite `3`-group of class `≤ 4`. -/
theorem D_le_derivedSeries_two_three (hQ : IsPGroup 3 Q)
    (hc : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) : D 5 Q ≤ derivedSeries Q 2 := by
  set N := derivedSeries Q 2
  set π := QuotientGroup.mk' N
  have hmet : derivedSeries (Q ⧸ N) 2 = ⊥ := by
    rw [← map_derivedSeries_of_surjective (QuotientGroup.mk'_surjective N), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  have hcQ : (⊤ : Subgroup (Q ⧸ N)).lowerCentralSeries 4 = ⊥ := by
    rw [← lcs_map_mk N, hc, Subgroup.map_bot]
  have hD := guptaTaharaMetabelian_three (Q ⧸ N) (hQ.to_quotient N) hmet
  rw [hcQ] at hD
  intro g hg
  have hg' : π g ∈ D 5 (Q ⧸ N) := map_D_le π _ (mem_map_of_mem π hg)
  rw [hD, mem_bot] at hg'
  rwa [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]

/-- **Lemma 6.1, `p = 3`** (`mem_of_mem_D_add_two` without the hypothesis):
`D₅(Q) ⊆ Q'' ∩ M₅(Q)`. -/
theorem mem_of_mem_D_add_two_three (hQ : IsPGroup 3 Q)
    (hc : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) {g : Q} (hg : g ∈ D 5 Q) :
    g ∈ derivedSeries Q 2 ∧ MonoidAlgebra.of (ZMod 3) Q g - 1 ∈ Jennings.augIdealP 3 Q ^ 5 :=
  ⟨D_le_derivedSeries_two_three hQ hc hg, sub_one_mem_augIdealP_pow_of_mem_D hg⟩

/-- `rank_ge_three_of_D_five_ne_bot` without the hypothesis: `D₅(Q) ≠ 1` needs `Q'' ≠ 1`,
hence `d(Q) ≥ 3`. -/
theorem rank_ge_three_of_D_five_ne_bot_three (hQ : IsPGroup 3 Q)
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) (hD : D 5 Q ≠ ⊥) :
    derivedSeries Q 2 ≠ ⊥ ∧ 3 ≤ Group.rank Q := by
  have hm : derivedSeries Q 2 ≠ ⊥ := fun h =>
    hD (le_bot_iff.mp (h ▸ D_le_derivedSeries_two_three hQ h5))
  exact ⟨hm, (card_ge_of_not_metabelian (by norm_num) hQ h5 hm).1⟩

/-- **Lemma 6.2** with hypotheses on the quotients (`minimal_three_of_quotients`), without
`PassiDFourSquare` and `GuptaTaharaMetabelian`. -/
theorem minimal_three_of_quotients_three (hQ : IsPGroup 3 Q)
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (hmin : ∀ N : Subgroup Q, ∀ _ : N.Normal, N ≤ center Q → Nat.card N = 3 → D 5 (Q ⧸ N) = ⊥)
    (hD : D 5 Q ≠ ⊥) :
    (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ ∧ derivedSeries Q 2 ≠ ⊥ ∧ 3 ≤ Group.rank Q ∧
      IsCyclic (center Q) ∧
      ∃ z ∈ center Q, orderOf z = 3 ∧ D 5 Q = zpowers z ∧
        (∀ x ∈ center Q, x ^ 3 = 1 → x ∈ zpowers z) ∧
        z ∈ derivedSeries Q 2 ∧ MonoidAlgebra.of (ZMod 3) Q z - 1 ∈ Jennings.augIdealP 3 Q ^ 5 ∧
        ∃ _ : (zpowers z).Normal, ∃ c ≥ 4, expCentral 3 Q (c + 1) = ⊥ ∧
          expCentral 3 Q c = zpowers z ∧ expCentral 3 (Q ⧸ zpowers z) c = ⊥ ∧
          expCentral 3 (Q ⧸ zpowers z) (c - 1) ≠ ⊥ :=
  minimal_three_of_quotients_of passiDFourSquare hQ h5 hmin (D_le_derivedSeries_two_three hQ h5) hD

/-- **Lemma 6.2** (`minimal_three`, `minimal_three'`) without `PassiDFourSquare` and
`GuptaTaharaMetabelian`: the minimal counterexample to `D₅ = γ₅` among `3`-groups. -/
theorem minimal_three_three (hQ : IsPGroup 3 Q)
    (hmin : ∀ (R : Type) [Group R] [Finite R], IsPGroup 3 R → Nat.card R < Nat.card Q →
      D 5 R = (⊤ : Subgroup R).lowerCentralSeries 4)
    (hD : D 5 Q ≠ (⊤ : Subgroup Q).lowerCentralSeries 4) :
    (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥ ∧ (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ ∧
      derivedSeries Q 2 ≠ ⊥ ∧ 3 ≤ Group.rank Q ∧ IsCyclic (center Q) ∧
      ∃ z ∈ center Q, orderOf z = 3 ∧ D 5 Q = zpowers z ∧
        (∀ x ∈ center Q, x ^ 3 = 1 → x ∈ zpowers z) ∧
        z ∈ derivedSeries Q 2 ∧ MonoidAlgebra.of (ZMod 3) Q z - 1 ∈ Jennings.augIdealP 3 Q ^ 5 ∧
        ∃ _ : (zpowers z).Normal, ∃ c ≥ 4, expCentral 3 Q (c + 1) = ⊥ ∧
          expCentral 3 Q c = zpowers z ∧ expCentral 3 (Q ⧸ zpowers z) c = ⊥ ∧
          expCentral 3 (Q ⧸ zpowers z) (c - 1) ≠ ⊥ :=
  minimal_three_of passiDFourSquare hQ (fun h5 => D_le_derivedSeries_two_three hQ h5) hmin hD

end Three

end GroupDimension
