module

public import GroupDimension.TaharaProof.TFrame

@[expose] public section

/-!
# The symbol of an element of `γ₃` ([Tah81, §6])

For `z ∈ γ₃` with normal form `z = ∏ x_l^{ν_l} · h` (letters `x_l` of weight 3, `h ∈ γ₄`), its
symbol is `S z = ∑ ν_l x̄_l + h̄ ∈ W₃* ⊕ W₄` (`= nsum z 0`). Modulo the relations (I)
(`f(l) x̄_l - \\overline{x_l^{f(l)}}`), `S` is additive on `γ₃`, and an element with symbol in the
span of (I) is trivial. Moreover `ψ₃(z - 1) = S z`, so for `z ∈ D₅` (where `z - 1 ∈ Λ₅`) the symbol
lies in `R₅*`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour
open scoped commutatorElement

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable [Fintype G] {F : Frame G ι} (hF : F.Class4)
include hF

/-- `γ₃` is abelian (class `≤ 4`). -/
theorem lcs2_comm {g h : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (hh : h ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    g * h = h * g := by
  have hc : ⁅g, h⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 5 :=
    lcs_mem_of_le (by norm_num) (commutator_lcs_le 2 2 (Subgroup.commutator_mem_commutator hg hh))
  have h5 : (⊤ : Subgroup G).lowerCentralSeries 5 = ⊥ := by
    rw [eq_bot_iff, ← hF.top]; exact (Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
  rw [h5, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

omit [Fintype G] hF in
theorem A4_mul {g h : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (hh : h ∈ (⊤ : Subgroup G).lowerCentralSeries 3) :
    F.A4 (g * h) = F.A4 g + F.A4 h := by
  simp [A4, cl_mul hg hh]

omit [Fintype G] hF in
theorem A4_zpow {g : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 3) (n : ℤ) : F.A4 (g ^ n) = n • F.A4 g := by
  simp [A4, cl_zpow hg]

omit [Fintype G] hF in
theorem A4_one : F.A4 (1 : G) = 0 := by simp [A4, cl_one]

omit [Fintype G] hF in
/-- The symbol of a single letter. -/
theorem Φ3_single (m : ι) : F.Φ3 (Pi.single m 1) =
    if F.w m = 3 then F.E3' m else if F.w m = 4 then F.A4 (F.x m) else 0 := by
  rw [← cnt_single, F.Φ3_cnt (List.pairwise_singleton _ _)]; rfl

/-- On `γ₄`, `nsum z 0` is the class of `z`. -/
theorem nsum_zero_of_mem4 {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 3) : F.nsum z 0 = F.A4 z := by
  have hn : ∀ m, F.nfc z m ≠ 0 → F.w m = 4 := fun m hm => by
    have := F.nf_weight (k := 4) (by simpa using hz) (F.nfc_lt z) (F.nprod_nfc z) hm
    have := hF.w_le m; omega
  have hmem : ∀ m, F.nfc z m ≠ 0 → F.x m ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := fun m hm => by
    simpa [hn m hm] using F.mem m
  conv_rhs => rw [← F.nprod_nfc z]
  -- the class of an ordered product of letters of weight 4
  have key : ∀ l : List ι, (∀ m ∈ l, F.nfc z m ≠ 0 → F.x m ∈ (⊤ : Subgroup G).lowerCentralSeries 3) →
      F.A4 (l.map fun m => F.x m ^ F.nfc z m).prod =
        (l.map fun m => (F.nfc z m : ℤ) • F.A4 (F.x m)).sum := by
    intro l
    induction l with
    | nil => simp [A4_one]
    | cons m l ih =>
      intro hl
      have h1 : F.x m ^ F.nfc z m ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
        by_cases h : F.nfc z m = 0
        · simp [h, one_mem]
        · exact _root_.pow_mem (hl m List.mem_cons_self h) _
      have h2 : (l.map fun m => F.x m ^ F.nfc z m).prod ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
        refine list_prod_mem fun y hy => ?_
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
        by_cases h : F.nfc z i = 0
        · simp [h, one_mem]
        · exact _root_.pow_mem (hl i (List.mem_cons_of_mem _ hi) h) _
      rw [List.map_cons, List.prod_cons, A4_mul h1 h2, ih fun i hi => hl i
        (List.mem_cons_of_mem _ hi), List.map_cons, List.sum_cons]
      congr 1
      by_cases h : F.nfc z m = 0
      · simp [h, A4_one]
      · rw [← zpow_natCast, A4_zpow (hl m List.mem_cons_self h)]
  rw [nprod, lprod, key _ fun m _ hm => hmem m hm, sum_ordL, nsum]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : F.nfc z m = 0
  · simp [h]
  · rw [zero_add, Φ3_single, if_neg (by have := hn m h; omega), if_pos (hn m h)]

/-! ## Integer ordered products in `γ₃` -/

omit [Fintype G] hF in
/-- `∏ x_j^{a_j}` with integer exponents. -/
noncomputable def zprod (F : Frame G ι) (a : ι → ℤ) : G := ((ordL ι).map fun j => F.x j ^ a j).prod

omit [Fintype G] hF in
theorem zprod_natCast (b : ι → ℕ) : F.zprod (fun j => (b j : ℤ)) = F.nprod b := by
  simp [zprod, nprod, lprod]

omit [Fintype G] hF in
theorem zprod_mem {a : ι → ℤ} (ha : ∀ j, a j ≠ 0 → 3 ≤ F.w j) :
    F.zprod a ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  refine list_prod_mem fun y hy => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  by_cases h : a j = 0
  · simp [h, one_mem]
  · exact zpow_mem (lcs_mem_of_le (by have := ha j h; omega) (F.mem j)) _

theorem list_prod_mul_of_mem (L : List ι) (u v : ι → G)
    (hu : ∀ j ∈ L, u j ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (hv : ∀ j ∈ L, v j ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    (L.map fun j => u j * v j).prod = (L.map u).prod * (L.map v).prod := by
  induction L with
  | nil => simp
  | cons j L ih =>
    have hPu : (L.map u).prod ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
      refine list_prod_mem fun y hy => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact hu i (List.mem_cons_of_mem _ hi)
    simp only [List.map_cons, List.prod_cons]
    rw [ih (fun i hi => hu i (List.mem_cons_of_mem _ hi)) (fun i hi => hv i (List.mem_cons_of_mem _ hi))]
    rw [mul_assoc, ← mul_assoc (v j), lcs2_comm hF (hv j List.mem_cons_self) hPu]
    simp only [mul_assoc]

/-- In `γ₃` the ordered products are multiplicative in the exponents. -/
theorem zprod_add {a a' : ι → ℤ} (ha : ∀ j, a j ≠ 0 → 3 ≤ F.w j)
    (ha' : ∀ j, a' j ≠ 0 → 3 ≤ F.w j) : F.zprod (a + a') = F.zprod a * F.zprod a' := by
  have hm : ∀ (b : ι → ℤ), (∀ j, b j ≠ 0 → 3 ≤ F.w j) → ∀ j, F.x j ^ b j ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    fun b hb j => by
      by_cases h : b j = 0
      · simp [h, one_mem]
      · exact zpow_mem (lcs_mem_of_le (by have := hb j h; omega) (F.mem j)) _
  unfold zprod
  rw [← list_prod_mul_of_mem hF _ _ _ (fun j _ => hm a ha j) (fun j _ => hm a' ha' j)]
  simp only [Pi.add_apply, zpow_add]

omit [Fintype G] hF in
theorem A4_list_prod (L : List G) (hL : ∀ g ∈ L, g ∈ (⊤ : Subgroup G).lowerCentralSeries 3) :
    F.A4 L.prod = (L.map F.A4).sum := by
  induction L with
  | nil => simp [A4_one]
  | cons g L ih =>
    rw [List.prod_cons, A4_mul (hL g List.mem_cons_self)
      (list_prod_mem fun y hy => hL y (List.mem_cons_of_mem _ hy)),
      ih fun y hy => hL y (List.mem_cons_of_mem _ hy), List.map_cons, List.sum_cons]

omit [Fintype G] hF in
theorem pow_o_mem3 {j : ι} (hj : F.w j = 3) : F.x j ^ F.o j ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
  simpa [hj] using F.pow_mem j

/-- Exponents of a product in `γ₄` of letters of weight 3 are divisible by the orders. -/
theorem zprod_dvd {t : ι → ℤ} (ht : ∀ j, t j ≠ 0 → F.w j = 3)
    (hm : F.zprod t ∈ (⊤ : Subgroup G).lowerCentralSeries 3) : ∀ j, (F.o j : ℤ) ∣ t j := by
  have ho : ∀ j, (0 : ℤ) < F.o j := fun j => Int.natCast_pos.mpr (F.o_pos j)
  set r : ι → ℤ := fun j => t j % F.o j
  set q : ι → ℤ := fun j => (F.o j : ℤ) * (t j / F.o j)
  have hrq : t = r + q := funext fun j => by simp [r, q, Int.emod_add_mul_ediv]
  have hr0 : ∀ j, r j ≠ 0 → 3 ≤ F.w j := fun j hj => by
    have : t j ≠ 0 := fun h => hj (by simp [r, h])
    rw [ht j this]
  have hq0 : ∀ j, q j ≠ 0 → 3 ≤ F.w j := fun j hj => by
    have : t j ≠ 0 := fun h => hj (by simp [q, h])
    rw [ht j this]
  have hqm : F.zprod q ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    by_cases h : t j = 0
    · simp [q, h, one_mem]
    · simp only [q, zpow_mul]
      exact zpow_mem (by rw [zpow_natCast]; exact pow_o_mem3 (ht j h)) _
  have hrm : F.zprod r ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    have e := zprod_add hF hr0 hq0
    rw [← hrq] at e
    have : F.zprod r = F.zprod t * (F.zprod q)⁻¹ := by rw [e]; group
    rw [this]; exact mul_mem hm (inv_mem hqm)
  have hrn : F.zprod r = F.nprod fun j => (r j).toNat := by
    rw [← zprod_natCast]; congr 1; funext j
    simp [r, Int.toNat_of_nonneg (Int.emod_nonneg _ (ho j).ne')]
  rw [hrn] at hrm
  have hb : ∀ j, (r j).toNat < F.o j := fun j => by
    have := Int.emod_lt_of_pos (t j) (ho j)
    have := Int.emod_nonneg (t j) (ho j).ne'
    simp only [r]; omega
  have hz := (F.wt _ hb 3).mp hrm
  intro j
  by_cases h : t j = 0
  · simp [h]
  · have h1 : (r j).toNat = 0 := hz j (by rw [ht j h])
    have hrj : r j = 0 := by
      have h2 : 0 ≤ r j := Int.emod_nonneg (t j) (ho j).ne'
      omega
    exact Int.dvd_of_emod_eq_zero hrj

/-! ## The symbol -/

omit [Fintype G] hF in
/-- The relations (I). -/
noncomputable def RI (F : Frame G ι) : Submodule ℤ F.M3 :=
  Submodule.span ℤ (Set.range fun l : F.IdxI => F.gI l.1)

omit [Fintype G] hF in
theorem RI_le : F.RI ≤ F.R5 := by
  unfold RI R5
  refine le_trans ?_ le_sup_left
  refine le_trans ?_ le_sup_left
  refine le_trans ?_ le_sup_left
  refine le_trans ?_ le_sup_left
  refine le_trans ?_ le_sup_left
  exact le_sup_left

omit [Fintype G] hF in
/-- The symbol `S z = ∑ ν_l x̄_l + h̄` of `z ∈ γ₃`. -/
noncomputable def S (F : Frame G ι) (z : G) : F.M3 := F.nsum z 0

omit [Fintype G] hF in
theorem gI_mem_RI {l : ι} (hl : F.w l = 3) : F.gI l ∈ F.RI :=
  Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem gI_eq {l : ι} (hl : F.w l = 3) :
    F.gI l = (F.o l : ℤ) • F.Φ3 (Pi.single l 1) - F.A4 (F.x l ^ F.o l) := by
  rw [gI, ← cnt_single, show F.yy l = F.x l ^ F.o l from rfl,
    nsum_zero_of_mem4 hF (pow_o_mem3 hl)]

/-- The normal form of `z ∈ γ₃`, split into its layers 3 and 4. -/
theorem nf_split {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    ∃ (n3 n4 : ι → ℕ), (∀ j, n3 j < F.o j) ∧ (∀ j, n3 j ≠ 0 → F.w j = 3) ∧
      (∀ j, n4 j < F.o j) ∧ (∀ j, n4 j ≠ 0 → 4 ≤ F.w j) ∧
      z = F.nprod n3 * F.nprod n4 ∧ F.nprod n4 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 ∧
      F.S z = ∑ j, (n3 j : ℤ) • F.Φ3 (Pi.single j 1) + F.A4 (F.nprod n4) := by
  classical
  set n := F.nfc z
  have hn : ∀ j, n j ≠ 0 → 3 ≤ F.w j := fun j hj =>
    F.nf_weight (k := 3) (by simpa using hz) (F.nfc_lt z) (F.nprod_nfc z) hj
  set n3 : ι → ℕ := fun j => if F.w j = 3 then n j else 0
  set n4 : ι → ℕ := fun j => if F.w j = 3 then 0 else n j
  have hsplit : n = n3 + n4 := funext fun j => by
    simp only [n3, n4, Pi.add_apply]; split_ifs <;> simp
  have h3b : ∀ j, n3 j < F.o j := fun j => by
    simp only [n3]; split_ifs
    · exact F.nfc_lt z j
    · exact F.o_pos j
  have h4b : ∀ j, n4 j < F.o j := fun j => by
    simp only [n4]; split_ifs
    · exact F.o_pos j
    · exact F.nfc_lt z j
  have h3w : ∀ j, n3 j ≠ 0 → F.w j = 3 := fun j hj => by
    simp only [n3] at hj; split_ifs at hj with h
    · exact h
    · exact absurd rfl hj
  have h4w : ∀ j, n4 j ≠ 0 → 4 ≤ F.w j := fun j hj => by
    simp only [n4] at hj; split_ifs at hj with h
    · exact absurd rfl hj
    · have := hn j hj; omega
  have hmul : F.nprod n = F.nprod n3 * F.nprod n4 := by
    rw [hsplit]
    exact (lprod_mul_lprod F.x _ n4 rfl fun i j hi hj =>
      F.lt_of_w_lt (by have := h3w i hi; have := h4w j hj; omega)).symm
  have hh0 : F.nprod n4 ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    by_cases h : n4 j = 0
    · simp [h, one_mem]
    · exact _root_.pow_mem (lcs_mem_of_le (by have := h4w j h; omega) (F.mem j)) _
  refine ⟨n3, n4, h3b, h3w, h4b, h4w, by rw [← hmul, F.nprod_nfc], hh0, ?_⟩
  have hnf4 : F.nfc (F.nprod n4) = n4 := F.nfc_eq h4b rfl
  rw [← nsum_zero_of_mem4 hF hh0, S, nsum, nsum, hnf4, show F.nfc z = n3 + n4 from hsplit,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Nat.cast_add, add_smul, zero_add]

/-- **The symbol of a product**: for `z = ∏ x_j^{a_j} · h` (letters of weight 3, `h ∈ γ₄`, any
integer exponents), `S z ≡ ∑ a_j x̄_j + h̄` modulo (I). -/
theorem S_eq_of {a : ι → ℤ} (ha : ∀ j, a j ≠ 0 → F.w j = 3) {h : G}
    (hh : h ∈ (⊤ : Subgroup G).lowerCentralSeries 3) :
    F.S (F.zprod a * h) - (∑ j, a j • F.Φ3 (Pi.single j 1) + F.A4 h) ∈ F.RI := by
  have ha3 : ∀ j, a j ≠ 0 → 3 ≤ F.w j := fun j hj => by rw [ha j hj]
  have hz : F.zprod a * h ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    mul_mem (F.zprod_mem ha3) (lcs_mem_of_le (by norm_num) hh)
  obtain ⟨n3, n4, h3b, h3w, -, -, hzeq, hh0, hS⟩ := nf_split hF hz
  set n3' : ι → ℤ := fun j => (n3 j : ℤ)
  have hn3' : ∀ j, n3' j ≠ 0 → F.w j = 3 := fun j hj => h3w j (by simpa [n3'] using hj)
  set t : ι → ℤ := a - n3'
  have ht : ∀ j, t j ≠ 0 → F.w j = 3 := fun j hj => by
    by_contra hw
    have h1 : a j = 0 := by by_contra h1; exact hw (ha j h1)
    have h2 : n3' j = 0 := by by_contra h2; exact hw (hn3' j h2)
    exact hj (by simp [t, h1, h2])
  have ht3 : ∀ j, t j ≠ 0 → 3 ≤ F.w j := fun j hj => by rw [ht j hj]
  have hn33 : ∀ j, n3' j ≠ 0 → 3 ≤ F.w j := fun j hj => by rw [hn3' j hj]
  have hsplit : F.zprod a = F.zprod n3' * F.zprod t := by
    rw [← zprod_add hF hn33 ht3]; congr 1; funext j; simp [t]
  have hzn : F.zprod n3' = F.nprod n3 := zprod_natCast n3
  rw [hsplit, hzn, mul_assoc] at hzeq
  have hth : F.zprod t * h = F.nprod n4 := mul_left_cancel hzeq
  have htm : F.zprod t ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    have : F.zprod t = F.nprod n4 * h⁻¹ := by rw [← hth]; group
    rw [this]; exact mul_mem hh0 (inv_mem hh)
  have hdv := zprod_dvd hF ht htm
  -- the class of `∏ x_j^{t_j}`
  have hfac : ∀ j, F.x j ^ t j = (F.x j ^ F.o j) ^ (t j / F.o j) := fun j => by
    rw [← zpow_natCast, ← zpow_mul, Int.mul_ediv_cancel' (hdv j)]
  have hfm : ∀ j, F.x j ^ t j ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := fun j => by
    by_cases h0 : t j = 0
    · simp [h0, one_mem]
    · rw [hfac]; exact zpow_mem (pow_o_mem3 (ht j h0)) _
  have hA4t : F.A4 (F.zprod t) =
      ∑ j, (t j / F.o j) • F.A4 (F.x j ^ F.o j) := by
    rw [zprod, A4_list_prod _ (fun y hy => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy; exact hfm j), List.map_map, sum_ordL]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    by_cases h0 : t j = 0
    · simp [h0, A4_one]
    · rw [hfac, A4_zpow (pow_o_mem3 (ht j h0))]
  rw [hS, ← hth, A4_mul htm hh, hA4t]
  have e : ∑ j, (n3 j : ℤ) • F.Φ3 (Pi.single j 1) +
        (∑ j, (t j / F.o j) • F.A4 (F.x j ^ F.o j) + F.A4 h) -
      (∑ j, a j • F.Φ3 (Pi.single j 1) + F.A4 h) =
      -∑ j, (t j / F.o j) • ((F.o j : ℤ) • F.Φ3 (Pi.single j 1) - F.A4 (F.x j ^ F.o j)) := by
    have e2 : ∀ j, a j = n3 j + (t j / F.o j) * F.o j := fun j => by
      rw [Int.ediv_mul_cancel (hdv j)]; simp [t, n3']
    simp only [e2, add_smul, mul_smul, Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [e]
  refine neg_mem (Submodule.sum_mem _ fun j _ => ?_)
  by_cases h0 : t j = 0
  · simp [h0]
  · rw [← gI_eq hF (ht j h0)]
    exact Submodule.smul_mem _ _ (gI_mem_RI (ht j h0))

/-- Additivity of the symbol modulo (I). -/
theorem S_mul {z z' : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (hz' : z' ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    F.S (z * z') - (F.S z + F.S z') ∈ F.RI := by
  obtain ⟨n3, n4, -, h3w, -, -, hzeq, hh0, hS⟩ := nf_split hF hz
  obtain ⟨m3, m4, -, h3w', -, -, hzeq', hh0', hS'⟩ := nf_split hF hz'
  set a : ι → ℤ := fun j => (n3 j : ℤ)
  set a' : ι → ℤ := fun j => (m3 j : ℤ)
  have ha : ∀ j, a j ≠ 0 → F.w j = 3 := fun j hj => h3w j (by simpa [a] using hj)
  have ha' : ∀ j, a' j ≠ 0 → F.w j = 3 := fun j hj => h3w' j (by simpa [a'] using hj)
  have hp : z * z' = F.zprod (a + a') * (F.nprod n4 * F.nprod m4) := by
    rw [zprod_add hF (fun j hj => by rw [ha j hj]) (fun j hj => by rw [ha' j hj]),
      zprod_natCast, zprod_natCast, hzeq, hzeq']
    have hc : F.nprod n4 * F.nprod m3 = F.nprod m3 * F.nprod n4 :=
      lcs2_comm hF (lcs_mem_of_le (by norm_num) hh0) (by
        rw [← zprod_natCast]; exact F.zprod_mem (fun j hj => by rw [ha' j hj]))
    rw [mul_assoc, ← mul_assoc (F.nprod n4), hc]; group
  have h1 := S_eq_of hF (a := a + a') (fun j hj => by
    by_contra hw
    have h1 : a j = 0 := by by_contra h1; exact hw (ha j h1)
    have h2 : a' j = 0 := by by_contra h2; exact hw (ha' j h2)
    exact hj (by simp [h1, h2])) (mul_mem hh0 hh0')
  rw [← hp, A4_mul hh0 hh0'] at h1
  convert h1 using 1
  rw [hS, hS']
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, a, a']
  abel

end Frame

end TaharaProof

end GroupDimension
