import GroupDimension.TaharaProof.TFrame

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
theorem lcs2_comm {g h : G} (hg : g ∈ lowerCentralSeries G 2) (hh : h ∈ lowerCentralSeries G 2) :
    g * h = h * g := by
  have hc : ⁅g, h⁆ ∈ lowerCentralSeries G 5 :=
    lcs_mem_of_le (by norm_num) (commutator_lcs_le 2 2 (Subgroup.commutator_mem_commutator hg hh))
  have h5 : lowerCentralSeries G 5 = ⊥ := by
    rw [eq_bot_iff, ← hF.top]; exact lowerCentralSeries_antitone (by norm_num)
  rw [h5, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

omit [Fintype G] hF in
theorem A4_mul {g h : G} (hg : g ∈ lowerCentralSeries G 3) (hh : h ∈ lowerCentralSeries G 3) :
    F.A4 (g * h) = F.A4 g + F.A4 h := by
  simp [A4, cl_mul hg hh]

omit [Fintype G] hF in
theorem A4_zpow {g : G} (hg : g ∈ lowerCentralSeries G 3) (n : ℤ) : F.A4 (g ^ n) = n • F.A4 g := by
  simp [A4, cl_zpow hg]

omit [Fintype G] hF in
theorem A4_one : F.A4 (1 : G) = 0 := by simp [A4, cl_one]

omit [Fintype G] hF in
/-- The symbol of a single letter. -/
theorem Φ3_single (m : ι) : F.Φ3 (Pi.single m 1) =
    if F.w m = 3 then F.E3' m else if F.w m = 4 then F.A4 (F.x m) else 0 := by
  rw [← cnt_single, F.Φ3_cnt (List.pairwise_singleton _ _)]; rfl

/-- On `γ₄`, `nsum z 0` is the class of `z`. -/
theorem nsum_zero_of_mem4 {z : G} (hz : z ∈ lowerCentralSeries G 3) : F.nsum z 0 = F.A4 z := by
  have hn : ∀ m, F.nfc z m ≠ 0 → F.w m = 4 := fun m hm => by
    have := F.nf_weight (k := 4) (by simpa using hz) (F.nfc_lt z) (F.nprod_nfc z) hm
    have := hF.w_le m; omega
  have hmem : ∀ m, F.nfc z m ≠ 0 → F.x m ∈ lowerCentralSeries G 3 := fun m hm => by
    simpa [hn m hm] using F.mem m
  conv_rhs => rw [← F.nprod_nfc z]
  -- the class of an ordered product of letters of weight 4
  have key : ∀ l : List ι, (∀ m ∈ l, F.nfc z m ≠ 0 → F.x m ∈ lowerCentralSeries G 3) →
      F.A4 (l.map fun m => F.x m ^ F.nfc z m).prod =
        (l.map fun m => (F.nfc z m : ℤ) • F.A4 (F.x m)).sum := by
    intro l
    induction l with
    | nil => simp [A4_one]
    | cons m l ih =>
      intro hl
      have h1 : F.x m ^ F.nfc z m ∈ lowerCentralSeries G 3 := by
        by_cases h : F.nfc z m = 0
        · simp [h, one_mem]
        · exact _root_.pow_mem (hl m List.mem_cons_self h) _
      have h2 : (l.map fun m => F.x m ^ F.nfc z m).prod ∈ lowerCentralSeries G 3 := by
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

omit [Fintype G] in
theorem zprod_mem {a : ι → ℤ} (ha : ∀ j, a j ≠ 0 → 3 ≤ F.w j) :
    F.zprod a ∈ lowerCentralSeries G 2 := by
  refine list_prod_mem fun y hy => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  by_cases h : a j = 0
  · simp [h, one_mem]
  · exact zpow_mem (lcs_mem_of_le (by have := ha j h; omega) (F.mem j)) _

theorem list_prod_mul_of_mem (L : List ι) (u v : ι → G)
    (hu : ∀ j ∈ L, u j ∈ lowerCentralSeries G 2) (hv : ∀ j ∈ L, v j ∈ lowerCentralSeries G 2) :
    (L.map fun j => u j * v j).prod = (L.map u).prod * (L.map v).prod := by
  induction L with
  | nil => simp
  | cons j L ih =>
    have hPu : (L.map u).prod ∈ lowerCentralSeries G 2 := by
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
  have hm : ∀ (b : ι → ℤ), (∀ j, b j ≠ 0 → 3 ≤ F.w j) → ∀ j, F.x j ^ b j ∈ lowerCentralSeries G 2 :=
    fun b hb j => by
      by_cases h : b j = 0
      · simp [h, one_mem]
      · exact zpow_mem (lcs_mem_of_le (by have := hb j h; omega) (F.mem j)) _
  unfold zprod
  rw [← list_prod_mul_of_mem hF _ _ _ (fun j _ => hm a ha j) (fun j _ => hm a' ha' j)]
  simp only [Pi.add_apply, zpow_add]

omit [Fintype G] hF in
theorem A4_list_prod (L : List G) (hL : ∀ g ∈ L, g ∈ lowerCentralSeries G 3) :
    F.A4 L.prod = (L.map F.A4).sum := by
  induction L with
  | nil => simp [A4_one]
  | cons g L ih =>
    rw [List.prod_cons, A4_mul (hL g List.mem_cons_self)
      (list_prod_mem fun y hy => hL y (List.mem_cons_of_mem _ hy)),
      ih fun y hy => hL y (List.mem_cons_of_mem _ hy), List.map_cons, List.sum_cons]

omit [Fintype G] hF in
theorem pow_o_mem3 {j : ι} (hj : F.w j = 3) : F.x j ^ F.o j ∈ lowerCentralSeries G 3 := by
  simpa [hj] using F.pow_mem j

/-- Exponents of a product in `γ₄` of letters of weight 3 are divisible by the orders. -/
theorem zprod_dvd {t : ι → ℤ} (ht : ∀ j, t j ≠ 0 → F.w j = 3)
    (hm : F.zprod t ∈ lowerCentralSeries G 3) : ∀ j, (F.o j : ℤ) ∣ t j := by
  have ho : ∀ j, (0 : ℤ) < F.o j := fun j => Int.natCast_pos.mpr (F.o_pos j)
  set r : ι → ℤ := fun j => t j % F.o j
  set q : ι → ℤ := fun j => (F.o j : ℤ) * (t j / F.o j)
  have hrq : t = r + q := funext fun j => by simp [r, q, Int.emod_add_ediv]
  have hr0 : ∀ j, r j ≠ 0 → 3 ≤ F.w j := fun j hj => by
    have : t j ≠ 0 := fun h => hj (by simp [r, h])
    rw [ht j this]
  have hq0 : ∀ j, q j ≠ 0 → 3 ≤ F.w j := fun j hj => by
    have : t j ≠ 0 := fun h => hj (by simp [q, h])
    rw [ht j this]
  have hqm : F.zprod q ∈ lowerCentralSeries G 3 := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    by_cases h : t j = 0
    · simp [q, h, one_mem]
    · simp only [q, zpow_mul]
      exact zpow_mem (by rw [zpow_natCast]; exact pow_o_mem3 (ht j h)) _
  have hrm : F.zprod r ∈ lowerCentralSeries G 3 := by
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

end Frame

end TaharaProof

end GroupDimension
