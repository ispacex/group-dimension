import GroupDimension.TaharaProof.Level3Defs

/-!
# A `ℤ`-basis of `Λ₃` and the map `ψ₃` ([Tah81, Lemma 3.3, §5])

Losey's basis of `Λ₃` (Lemma 3.3): `(x_i - 1)^{d(i)}` (`d(i) ≥ 3`), `(x_k - 1)^{e(k)}`,
`d(i)(x_i - 1)(x_j - 1)` (`i ≤ j`, weight 1), and the basic products of weight `≥ 3`. We only need
that these are linearly independent (`fam_linearIndependent`): their coordinates in the basis of
basic products, at the basic products of weight `≤ 2`, form a triangular system. On their span
`L` we define `ψ₃` by Tahara's values ([Tah81, p. 151]): the symbol `Φ₃` on the first, second
and fourth kinds and `V3val` on the third. `rel3` is the set of pairs `(z, v)` with `z ∈ L` and
`ψ₃ z ≡ v (mod R₅*)`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

theorem cnt_replicate (m : ℕ) (x : ι) : cnt (List.replicate m x) = m • Pi.single x 1 := by
  funext j
  by_cases h : j = x
  · subst h; simp [cnt]
  · simp [cnt, List.count_replicate, Ne.symm h, Pi.single_eq_of_ne h]

theorem cnt_inj {l l' : List ι} (hl : l.Pairwise (· ≤ ·)) (hl' : l'.Pairwise (· ≤ ·)) :
    cnt l = cnt l' ↔ l = l' :=
  ⟨fun h => by rw [← word_cnt hl, h, word_cnt hl'], fun h => h ▸ rfl⟩

theorem sum_cnt (l : List ι) : ∑ j, cnt l j = l.length := by
  induction l with
  | nil => simp [cnt_nil]
  | cons j l ih =>
    rw [show j :: l = [j] ++ l from rfl, cnt_append, cnt_single]
    simp only [Pi.add_apply, Finset.sum_add_distrib, ih]
    rw [Finset.sum_pi_single']; simp; ring

namespace Frame

variable (F : Frame G ι)

theorem P_nsmul_single (m : ℕ) (x : ι) : F.P (m • Pi.single x 1) = F.X x ^ m := by
  induction m with
  | zero => simp [P_zero]
  | succ m ih =>
    rw [pow_succ, ← ih, F.P_mul_X, succ_nsmul]
    intro j hj; simp [Pi.single_eq_of_ne hj.ne']

/-! ## Coordinates in the basis of basic products -/

variable [Fintype G]

/-- The coordinate at a basic sequence `β` (`0` if `β` is not basic). -/
noncomputable def crd (β : ι → ℕ) : MonoidAlgebra ℤ G →ₗ[ℤ] ℤ :=
  if h : ∀ j, β j < F.o j then (Finsupp.lapply (F.toBasic β h)).comp F.basis.repr.toLinearMap
  else 0

theorem crd_P {b β : ι → ℕ} (hb : ∀ j, b j < F.o j) (hβ : ∀ j, β j < F.o j) :
    F.crd β (F.P b) = if b = β then 1 else 0 := by
  have e : F.P b = F.basis (F.toBasic b hb) := by rw [basis_apply, toBasic_val]
  rw [crd, dif_pos hβ, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Module.Basis.repr_self,
    Finsupp.lapply_apply, Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext j; exact congrArg (fun f : F.Basic => ((f j : Fin (F.o j)) : ℕ)) h
  · intro h; subst h; rfl

/-- `crd β` vanishes on the span of the basic products other than `β`. -/
theorem crd_eq_zero_of_mem {β : ι → ℕ} {S : Set (ι → ℕ)}
    (hS : ∀ b ∈ S, (∀ j, b j < F.o j) ∧ b ≠ β) {z : MonoidAlgebra ℤ G}
    (hz : z ∈ Submodule.span ℤ ((fun b => F.P b) '' S)) : F.crd β z = 0 := by
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul c u _ hu => rw [map_zsmul, hu, smul_zero]
  | mem z hz =>
  obtain ⟨b, hb, rfl⟩ := hz
  by_cases hβ : ∀ j, β j < F.o j
  · rw [F.crd_P (hS b hb).1 hβ, if_neg (hS b hb).2]
  · simp [crd, dif_neg hβ]

/-! ## Losey's basis of `Λ₃` -/

/-- `(x_i - 1)^{d(i)}`, `d(i) ≥ 3`. -/
abbrev K1 := {i : ι // F.w i = 1 ∧ 3 ≤ F.o i}
/-- `(x_k - 1)^{e(k)}`. -/
abbrev K2 := {k : ι // F.w k = 2}
/-- `d(i)(x_i - 1)(x_j - 1)`, `i ≤ j`. -/
abbrev K3 := {p : ι × ι // F.w p.1 = 1 ∧ F.w p.2 = 1 ∧ p.1 ≤ p.2}
/-- Basic products of weight `≥ 3`. -/
abbrev K4 := {b : F.Basic // 3 ≤ F.W b.val}
/-- The index set of Losey's basis of `Λ₃`. -/
abbrev Fam := F.K1 ⊕ F.K2 ⊕ F.K3 ⊕ F.K4

/-- Losey's basis of `Λ₃` ([Tah81, Lemma 3.3]). -/
noncomputable def fam : F.Fam → MonoidAlgebra ℤ G
  | .inl i => F.P (cnt (List.replicate (F.o i.1) i.1))
  | .inr (.inl k) => F.P (cnt (List.replicate (F.o k.1) k.1))
  | .inr (.inr (.inl p)) => (F.o p.1.1 : ℤ) • F.P (cnt [p.1.1, p.1.2])
  | .inr (.inr (.inr b)) => F.P b.1.val

/-- Tahara's values of `ψ₃` on Losey's basis ([Tah81, p. 151]). -/
noncomputable def famVal : F.Fam → F.M3
  | .inl i => F.Φ3 (cnt (List.replicate (F.o i.1) i.1))
  | .inr (.inl k) => F.Φ3 (cnt (List.replicate (F.o k.1) k.1))
  | .inr (.inr (.inl p)) => F.V3val p.1.1 p.1.2
  | .inr (.inr (.inr b)) => F.Φ3 b.1.val

/-- `(x - 1)^d = (x^d - 1) - ∑_{0<h<d} C(d,h) (x - 1)^h` with proper products. -/
theorem P_pow_eq (x : ι) {d : ℕ} (hd : 1 ≤ d) :
    F.P (cnt (List.replicate d x)) = (of ℤ G (F.x x ^ d) - 1) -
      ∑ h ∈ Finset.range (d - 1), (d.choose (h + 1) : ℤ) • F.P (cnt (List.replicate (h + 1) x)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [cnt_replicate, P_nsmul_single, Nat.add_sub_cancel]
  rw [X_pow_eq]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← nsmul_eq_mul, natCast_zsmul]

variable {F} (hF : F.Class4)
include hF

theorem single_basic (j : ι) : ∀ i, (Pi.single j 1 : ι → ℕ) i < F.o i := by
  intro i
  by_cases h : i = j
  · subst h; simp; exact hF.one_lt i
  · simp [Pi.single_eq_of_ne h]; exact lt_trans zero_lt_one (hF.one_lt i)

/-- The coordinates of `y - 1` at the products of weight `≤ 2`, for `y ∈ γ₂`. -/
theorem crd_of_sub_one {y : G} (hy : ∀ j, F.nfc y j ≠ 0 → 2 ≤ F.w j) {β : ι → ℕ}
    (hβ : F.W β ≤ 2) :
    F.crd β (of ℤ G y - 1) = ∑ j, (F.nfc y j : ℤ) * (if Pi.single j 1 = β then 1 else 0) := by
  by_cases hβb : ∀ i, β i < F.o i
  swap
  · rw [show F.crd β = 0 from by simp [crd, dif_neg hβb], LinearMap.zero_apply]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg (fun h => hβb (by rw [← h]; exact single_basic hF j)), mul_zero]
  obtain ⟨-, h2⟩ := F.of_nprod_sub_one (F.nfc y)
  rw [F.nprod_nfc] at h2
  have e : of ℤ G y - 1 = ∑ j, (F.nfc y j : ℤ) • F.X j +
      (of ℤ G y - 1 - ∑ j, (F.nfc y j : ℤ) • F.X j) := by abel
  rw [e, map_add, map_sum]
  have hrem : F.crd β (of ℤ G y - 1 - ∑ j, (F.nfc y j : ℤ) • F.X j) = 0 := by
    refine F.crd_eq_zero_of_mem (S := {b | b ≤ F.nfc y ∧ 2 ≤ ∑ j, b j}) ?_ ?_
    · rintro b ⟨hb, hb2⟩
      refine ⟨fun j => lt_of_le_of_lt (hb j) (F.nfc_lt y j), fun hbβ => ?_⟩
      have h4 : 2 * 2 ≤ F.W b := by
        calc 2 * 2 ≤ (∑ j, b j) * 2 := Nat.mul_le_mul_right _ hb2
          _ = ∑ j, b j * 2 := Finset.sum_mul _ _ _
          _ ≤ ∑ j, b j * F.w j := Finset.sum_le_sum fun j _ => by
              by_cases h : b j = 0
              · simp [h]
              · exact Nat.mul_le_mul_left _ (hy j (fun h0 => h (by
                  have : b j ≤ F.nfc y j := hb j; omega)))
      rw [hbβ] at h4; omega
    · have hset : (fun b => F.P b) '' {b | b ≤ F.nfc y ∧ 2 ≤ ∑ j, b j} =
          {z | ∃ β ≤ F.nfc y, 2 ≤ ∑ j, β j ∧ z = F.P β} := by
        ext z
        simp only [Set.mem_image, Set.mem_setOf_eq]
        constructor
        · rintro ⟨b, ⟨hb, hb2⟩, rfl⟩; exact ⟨b, hb, hb2, rfl⟩
        · rintro ⟨b, hb, hb2, rfl⟩; exact ⟨b, ⟨hb, hb2⟩, rfl⟩
      rw [hset]; exact h2
  rw [hrem, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, ← F.P_single, F.crd_P (single_basic hF j) hβb]
  simp [mul_comm]

omit hF in
/-- Linear independence from pivots: each member has a nonzero coordinate at its pivot, and no
other member of the same or higher rank has a coordinate there. -/
theorem li_of_pivots {κ : Type*} [Fintype κ] [DecidableEq κ] (v : κ → MonoidAlgebra ℤ G)
    (piv : κ → (ι → ℕ)) (r : κ → ℕ) (h0 : ∀ f, F.crd (piv f) (v f) ≠ 0)
    (h1 : ∀ f f', f' ≠ f → r f ≤ r f' → F.crd (piv f) (v f') = 0) : LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg f
  induction hrf : r f using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  have h := congrArg (F.crd (piv f)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single f] at h
  · rw [map_zsmul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (h0 f)
  · intro f' _ hf'
    rw [map_zsmul, smul_eq_mul]
    by_cases hr : r f ≤ r f'
    · rw [h1 f f' hf' hr, mul_zero]
    · rw [ih (r f') (by omega) f' rfl, zero_mul]
  · simp

theorem crd_P_cnt {l l' : List ι} (hl : l.Pairwise (· ≤ ·)) (hl' : l'.Pairwise (· ≤ ·))
    (hb : ∀ j, l.count j < F.o j) (hb' : ∀ j, l'.count j < F.o j) :
    F.crd (cnt l') (F.P (cnt l)) = if l = l' then 1 else 0 := by
  rw [F.crd_P (b := cnt l) (β := cnt l') hb hb']
  exact if_congr (cnt_inj hl hl') rfl rfl

theorem crd_cnt_of_sub_one {y : G} (hy : ∀ j, F.nfc y j ≠ 0 → 2 ≤ F.w j) {l : List ι}
    (hl : l.Pairwise (· ≤ ·)) (hW : F.W (cnt l) ≤ 2) :
    F.crd (cnt l) (of ℤ G y - 1) = ∑ j, (F.nfc y j : ℤ) * (if [j] = l then 1 else 0) := by
  rw [crd_of_sub_one hF hy hW]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← cnt_single]
  exact congrArg _ (if_congr (cnt_inj (List.pairwise_singleton _ _) hl) rfl rfl)

omit [Fintype G] hF in
theorem replicate_succ_eq_single {h : ℕ} {m i : ι} :
    List.replicate (h + 1) m = [i] ↔ h = 0 ∧ m = i := by
  rcases h with _ | h <;> simp [List.replicate_succ]

omit [Fintype G] hF in
theorem replicate_succ_eq_pair {h : ℕ} {m p q : ι} :
    List.replicate (h + 1) m = [p, q] ↔ h = 1 ∧ m = p ∧ m = q := by
  rcases h with _ | _ | h <;> simp [List.replicate_succ]

omit hF in
theorem pairwise_replicate (n : ℕ) (x : ι) : (List.replicate n x).Pairwise (· ≤ ·) :=
  List.pairwise_replicate.mpr (Or.inr le_rfl)

theorem count_replicate_lt {n : ℕ} {x : ι} (h : n < F.o x) (j : ι) :
    (List.replicate n x).count j < F.o j := by
  rw [List.count_replicate]
  split_ifs with hx
  · rw [beq_iff_eq] at hx; subst hx; exact h
  · exact lt_trans zero_lt_one (hF.one_lt j)

theorem count_pair_lt {p q : ι} (hpq : p < q) (j : ι) : [p, q].count j < F.o j := by
  have := hF.one_lt j
  simp only [List.count_cons, List.count_nil]
  by_cases h1 : p = j <;> by_cases h2 : q = j
  · subst h1; subst h2; exact absurd hpq (lt_irrefl _)
  all_goals simp [h1, h2]; omega

theorem count_single_lt (i j : ι) : [i].count j < F.o j := by
  have := hF.one_lt j
  simp only [List.count_cons, List.count_nil]
  split_ifs <;> omega

/-- The coordinates of a power `(x_m - 1)^{o_m}`. -/
theorem crd_pow {m : ι} {l : List ι} (hl : l.Pairwise (· ≤ ·)) (hb : ∀ j, l.count j < F.o j) :
    F.crd (cnt l) (F.P (cnt (List.replicate (F.o m) m))) =
      F.crd (cnt l) (of ℤ G (F.yy m) - 1) - ∑ h ∈ Finset.range (F.o m - 1),
        ((F.o m).choose (h + 1) : ℤ) * (if List.replicate (h + 1) m = l then 1 else 0) := by
  rw [F.P_pow_eq m (hF.one_lt m).le, _root_.map_sub, map_sum]
  change _ - _ = F.crd (cnt l) (of ℤ G (F.x m ^ F.o m) - 1) - _
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_range] at hh
  rw [map_zsmul, smul_eq_mul, F.crd_P_cnt hF (pairwise_replicate _ _) hl
    (count_replicate_lt hF (by omega)) hb]

omit [Fintype G] hF in
/-- The normal form of `y_i = x_i^{o_i}` has letters of weight `> w_i`. -/
theorem nfc_yy_weight {i j : ι} (hj : F.nfc (F.yy i) j ≠ 0) : F.w i + 1 ≤ F.w j :=
  F.nf_weight (k := F.w i + 1) (by simpa [yy] using F.pow_mem i) (F.nfc_lt _) (F.nprod_nfc _) hj

/-- Pivots of Losey's basis. -/
noncomputable def piv : F.Fam → (ι → ℕ)
  | .inl i => cnt [i.1]
  | .inr (.inl k) => cnt [k.1]
  | .inr (.inr (.inl p)) =>
    if p.1.1 = p.1.2 then (if F.o p.1.1 = 2 then cnt [p.1.1] else cnt [p.1.1, p.1.1])
    else cnt [p.1.1, p.1.2]
  | .inr (.inr (.inr b)) => b.1.val

omit hF in
/-- Ranks of the pivots. -/
def rk : F.Fam → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl p)) => if p.1.1 = p.1.2 ∧ F.o p.1.1 ≠ 2 then 1 else 0
  | .inr (.inr (.inr _)) => 2

/-- `crd_l(y_m - 1) = 0` unless `l` is a single letter of weight `> w_m`. -/
theorem crd_yy_eq_zero {m : ι} {l : List ι} (hl : l.Pairwise (· ≤ ·)) (hW : F.W (cnt l) ≤ 2)
    (h : ∀ j, [j] = l → F.w j ≤ F.w m) :
    F.crd (cnt l) (of ℤ G (F.yy m) - 1) = 0 := by
  have hm := F.w_pos m
  rw [F.crd_cnt_of_sub_one hF (fun j hj => by have := F.nfc_yy_weight hj; omega) hl hW]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : [j] = l
  · have : F.nfc (F.yy m) j = 0 := by
      by_contra h0; have := F.nfc_yy_weight h0; have := h j hj; omega
    simp [this]
  · simp [hj]

theorem crd_yy_eq_zero' {m : ι} {l : List ι} (hl : l.Pairwise (· ≤ ·)) (hW : F.W (cnt l) ≤ 2)
    (hm : F.w m = 2) : F.crd (cnt l) (of ℤ G (F.yy m) - 1) = 0 := by
  rw [F.crd_cnt_of_sub_one hF (fun j hj => by have := F.nfc_yy_weight hj; omega) hl hW]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : [j] = l
  · have : F.nfc (F.yy m) j = 0 := by
      by_contra h0
      have h1 := F.nfc_yy_weight h0
      subst hj
      rw [W_cnt] at hW; simp at hW; omega
    simp [this]
  · simp [hj]

/-- Losey's basis is linearly independent. -/
theorem fam_linearIndependent : LinearIndependent ℤ F.fam := by
  classical
  have hw : ∀ j, 1 ≤ F.w j := F.w_pos
  have ho : ∀ j, 1 < F.o j := hF.one_lt
  -- the low pivots
  have pw1 : ∀ i : ι, ([i] : List ι).Pairwise (· ≤ ·) := fun i => List.pairwise_singleton _ _
  have Wsingle : ∀ i, F.W (cnt [i]) = F.w i := fun i => by rw [W_cnt]; simp
  have Wpair : ∀ p q, F.W (cnt [p, q]) = F.w p + F.w q := fun p q => by rw [W_cnt]; simp
  -- `Σ_h C(o,h+1) [rep (h+1) m = l]`
  have hsum1 : ∀ m i, ∑ h ∈ Finset.range (F.o m - 1), ((F.o m).choose (h + 1) : ℤ) *
      (if List.replicate (h + 1) m = [i] then 1 else 0) = if m = i then (F.o m : ℤ) else 0 := by
    intro m i
    rw [Finset.sum_eq_single 0]
    · simp [replicate_succ_eq_single]
    · intro h _ hh
      rw [if_neg (by rw [replicate_succ_eq_single]; omega), mul_zero]
    · intro h0; exfalso; have := ho m; simp at h0; omega
  have hsum2 : ∀ m p q, p ≠ q → ∑ h ∈ Finset.range (F.o m - 1), ((F.o m).choose (h + 1) : ℤ) *
      (if List.replicate (h + 1) m = [p, q] then 1 else 0) = 0 := by
    intro m p q hpq
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg]; · simp
    rw [replicate_succ_eq_pair]; rintro ⟨-, rfl, rfl⟩; exact hpq rfl
  have hsum3 : ∀ m p, m ≠ p → ∑ h ∈ Finset.range (F.o m - 1), ((F.o m).choose (h + 1) : ℤ) *
      (if List.replicate (h + 1) m = [p, p] then 1 else 0) = 0 := by
    intro m p hmp
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg]; · simp
    rw [replicate_succ_eq_pair]; rintro ⟨-, rfl, -⟩; exact hmp rfl
  have hsum1' : ∀ m i, m ≠ i → ∑ h ∈ Finset.range (F.o m - 1), ((F.o m).choose (h + 1) : ℤ) *
      (if List.replicate (h + 1) m = [i] then 1 else 0) = 0 := by
    intro m i hmi; rw [hsum1, if_neg hmi]
  -- coordinates of the members of the family at a low pivot `l`
  have hK3 : ∀ (p : F.K3) (l : List ι), l.Pairwise (· ≤ ·) → (∀ j, l.count j < F.o j) →
      ¬ (p.1.1 = p.1.2 ∧ F.o p.1.1 = 2) →
      F.crd (cnt l) (F.fam (.inr (.inr (.inl p)))) =
        (F.o p.1.1 : ℤ) * (if [p.1.1, p.1.2] = l then 1 else 0) := by
    intro p l hl hb hnd
    simp only [fam]
    rw [map_zsmul, smul_eq_mul, F.crd_P_cnt hF (by simp [p.2.2.2]) hl _ hb]
    rcases eq_or_lt_of_le p.2.2.2 with h | h
    · intro j
      have h3 : 2 < F.o p.1.1 := by
        have := ho p.1.1; by_contra h'; exact hnd ⟨h, by omega⟩
      rw [← h]
      simp only [List.count_cons, List.count_nil]
      by_cases hj : p.1.1 = j
      · subst hj; simp; omega
      · simp [hj]; exact lt_trans zero_lt_one (ho j)
    · exact count_pair_lt hF h
  have hK3d : ∀ (p : F.K3) (l : List ι), l.Pairwise (· ≤ ·) → (∀ j, l.count j < F.o j) →
      F.W (cnt l) ≤ 2 → p.1.1 = p.1.2 → F.o p.1.1 = 2 →
      F.crd (cnt l) (F.fam (.inr (.inr (.inl p)))) =
        2 * (F.crd (cnt l) (of ℤ G (F.yy p.1.1) - 1) - 2 * (if [p.1.1] = l then 1 else 0)) := by
    intro p l hl hb hW hd ho2
    simp only [fam]
    have e : cnt [p.1.1, p.1.2] = cnt (List.replicate (F.o p.1.1) p.1.1) := by
      rw [ho2, ← hd]; rfl
    rw [e, map_zsmul, smul_eq_mul, F.crd_pow hF hl hb, ho2]
    simp [hsum1]
  have hK4 : ∀ (b : F.K4) (l : List ι), (∀ j, l.count j < F.o j) → F.W (cnt l) ≤ 2 →
      F.crd (cnt l) (F.fam (.inr (.inr (.inr b)))) = 0 := by
    intro b l hb hW
    simp only [fam]
    rw [F.crd_P (β := cnt l) b.1.val_lt hb, if_neg]
    intro h; have := b.2; rw [h] at this; omega
  -- coordinates of `y_m - 1` at the low pivots
  have hY1 : ∀ m i, F.w i = 1 → F.crd (cnt [i]) (of ℤ G (F.yy m) - 1) = 0 := fun m i hi =>
    crd_yy_eq_zero hF (pw1 i) (by rw [Wsingle, hi]; omega) fun j hj => by
      simp at hj; subst hj; rw [hi]; exact hw m
  have hY2 : ∀ m p q, p ≤ q → F.W (cnt [p, q]) ≤ 2 →
      F.crd (cnt [p, q]) (of ℤ G (F.yy m) - 1) = 0 :=
    fun m p q hpq hW => crd_yy_eq_zero hF (by simp [hpq]) hW fun j hj => by simp at hj
  have hYk : ∀ k k', F.w k = 2 → F.w k' = 2 → F.crd (cnt [k]) (of ℤ G (F.yy k') - 1) = 0 :=
    fun k k' hk hk' => crd_yy_eq_zero' hF (pw1 k) (by rw [Wsingle, hk]) hk'
  have hbs : ∀ i : ι, ∀ j, [i].count j < F.o j := fun i => count_single_lt hF i
  have hbd : ∀ p : ι, 2 < F.o p → ∀ j, [p, p].count j < F.o j := by
    intro p hp j
    simp only [List.count_cons, List.count_nil]
    by_cases hj : p = j
    · subst hj; simp; omega
    · simp [hj]; exact lt_trans zero_lt_one (ho j)
  have WK3 : ∀ p : F.K3, F.W (cnt [p.1.1, p.1.2]) ≤ 2 := fun p => by
    rw [Wpair, p.2.1, p.2.2.1]
  refine F.li_of_pivots F.fam F.piv F.rk ?_ ?_
  · rintro (i | k | ⟨⟨p1, p2⟩, hp1, hp2, hp12⟩ | b)
    · show F.crd (cnt [i.1]) (F.P _) ≠ 0
      rw [F.crd_pow hF (pw1 _) (hbs _), hY1 _ _ i.2.1, hsum1, if_pos rfl]
      have := ho i.1; omega
    · show F.crd (cnt [k.1]) (F.P _) ≠ 0
      rw [F.crd_pow hF (pw1 _) (hbs _), hYk _ _ k.2 k.2, hsum1, if_pos rfl]
      have := ho k.1; omega
    · simp only [piv]
      by_cases hd : p1 = p2
      · subst hd
        by_cases ho2 : F.o p1 = 2
        · rw [if_pos rfl, if_pos ho2, hK3d _ _ (pw1 _) (hbs _) (by rw [Wsingle, hp1]; omega) rfl ho2,
            hY1 _ _ hp1]
          simp
        · rw [if_pos rfl, if_neg ho2, hK3 _ _ (by simp) (hbd _ (by have := ho p1; omega))
            (fun h => ho2 h.2)]
          simp; have := ho p1; omega
      · rw [if_neg hd, hK3 _ _ (by simp [hp12]) (count_pair_lt hF (lt_of_le_of_ne hp12 hd))
          (fun h => hd h.1)]
        simp; have := ho p1; omega
    · show F.crd b.1.val (F.P b.1.val) ≠ 0
      rw [F.crd_P b.1.val_lt b.1.val_lt, if_pos rfl]; norm_num
  · rintro f f' hne hr
    rcases f with (i | k | ⟨⟨p1, p2⟩, hp1, hp2, hp12⟩ | b) <;>
      rcases f' with (i' | k' | ⟨⟨q1, q2⟩, hq1, hq2, hq12⟩ | b')
    -- f = K1 i
    · have hii : i'.1 ≠ i.1 := fun h => hne (congrArg _ (Subtype.ext h))
      show F.crd (cnt [i.1]) (F.P _) = 0
      rw [F.crd_pow hF (pw1 _) (hbs _), hY1 _ _ i.2.1, hsum1, if_neg hii, sub_zero]
    · have hki : k'.1 ≠ i.1 := fun h => by have := k'.2; rw [h, i.2.1] at this; omega
      show F.crd (cnt [i.1]) (F.P _) = 0
      rw [F.crd_pow hF (pw1 _) (hbs _), hY1 _ _ i.2.1, hsum1, if_neg hki, sub_zero]
    · by_cases hd : q1 = q2 ∧ F.o q1 = 2
      · obtain ⟨rfl, ho2⟩ := hd
        rw [show F.piv (.inl i) = cnt [i.1] from rfl, hK3d _ _ (pw1 _) (hbs _)
          (by rw [Wsingle, i.2.1]; omega) rfl ho2, hY1 _ _ i.2.1]
        have : [q1] ≠ [i.1] := by
          intro h; simp at h; subst h; have := i.2.2; omega
        simp [this]
      · rw [show F.piv (.inl i) = cnt [i.1] from rfl, hK3 _ _ (pw1 _) (hbs _) hd]
        simp
    · exact hK4 _ _ (hbs _) (by rw [Wsingle, i.2.1]; omega)
    -- f = K2 k
    · simp [rk] at hr
    · have hkk : k'.1 ≠ k.1 := fun h => hne (congrArg _ (congrArg _ (Subtype.ext h)))
      show F.crd (cnt [k.1]) (F.P _) = 0
      rw [F.crd_pow hF (pw1 _) (hbs _), hYk _ _ k.2 k'.2, hsum1, if_neg hkk, sub_zero]
    · simp only [rk] at hr
      split_ifs at hr with hd
      · rw [show F.piv (.inr (.inl k)) = cnt [k.1] from rfl, hK3 _ _ (pw1 _) (hbs _)
          (fun h => hd.2 h.2)]
        simp
      · omega
    · exact hK4 _ _ (hbs _) (by rw [Wsingle, k.2])
    -- f = K3 p
    · by_cases hd : p1 = p2
      · subst hd
        by_cases ho2 : F.o p1 = 2
        · simp only [piv, if_pos, ho2]
          have hip : i'.1 ≠ p1 := fun h => by have := i'.2.2; rw [h] at this; omega
          show F.crd (cnt [p1]) (F.P _) = 0
          rw [F.crd_pow hF (pw1 _) (hbs _), hY1 _ _ hp1, hsum1, if_neg hip, sub_zero]
        · simp [rk, ho2] at hr
      · simp only [piv, if_neg hd]
        show F.crd (cnt [p1, p2]) (F.P _) = 0
        rw [F.crd_pow hF (by simp [hp12]) (count_pair_lt hF (lt_of_le_of_ne hp12 hd)),
          hY2 _ _ _ hp12 (by rw [Wpair, hp1, hp2]), hsum2 _ _ _ hd, sub_zero]
    · by_cases hd : p1 = p2
      · subst hd
        by_cases ho2 : F.o p1 = 2
        · simp only [piv, if_pos, ho2]
          have hkp : k'.1 ≠ p1 := fun h => by have := k'.2; rw [h, hp1] at this; omega
          show F.crd (cnt [p1]) (F.P _) = 0
          rw [F.crd_pow hF (pw1 _) (hbs _), hY1 _ _ hp1, hsum1, if_neg hkp, sub_zero]
        · simp only [piv, if_pos, ho2, if_false]
          have hkp : k'.1 ≠ p1 := fun h => by have := k'.2; rw [h, hp1] at this; omega
          show F.crd (cnt [p1, p1]) (F.P _) = 0
          rw [F.crd_pow hF (by simp) (hbd _ (by have := ho p1; omega)),
            hY2 _ _ _ le_rfl (by rw [Wpair, hp1]), hsum3 _ _ hkp, sub_zero]
      · simp only [piv, if_neg hd]
        show F.crd (cnt [p1, p2]) (F.P _) = 0
        rw [F.crd_pow hF (by simp [hp12]) (count_pair_lt hF (lt_of_le_of_ne hp12 hd)),
          hY2 _ _ _ hp12 (by rw [Wpair, hp1, hp2]), hsum2 _ _ _ hd, sub_zero]
    · -- K3 against K3
      have hpq : (p1, p2) ≠ (q1, q2) := fun h => hne (by
        simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      have hlist : [q1, q2] ≠ [p1, p2] := fun h => hpq (by simp at h; rw [h.1, h.2])
      by_cases hd : p1 = p2
      · subst hd
        by_cases ho2 : F.o p1 = 2
        · simp only [piv, if_pos, ho2]
          by_cases hq : q1 = q2 ∧ F.o q1 = 2
          · obtain ⟨rfl, hqo⟩ := hq
            rw [hK3d ⟨(q1, q1), hq1, hq2, hq12⟩ _ (pw1 _) (hbs _) (by rw [Wsingle, hp1]; omega) rfl
              hqo, hY1 _ _ hp1]
            have : [q1] ≠ [p1] := fun h => hpq (by simp at h; rw [h])
            simp [this]
          · rw [hK3 _ _ (pw1 _) (hbs _) hq]; simp
        · have hrk : F.rk (.inr (.inr (.inl ⟨(q1, q2), hq1, hq2, hq12⟩))) =
              if q1 = q2 ∧ F.o q1 ≠ 2 then 1 else 0 := rfl
          have hrk0 : F.rk (.inr (.inr (.inl ⟨(p1, p1), hp1, hp2, hp12⟩))) = 1 := by
            simp [rk, ho2]
          rw [hrk0, hrk] at hr
          by_cases hq : q1 = q2 ∧ F.o q1 ≠ 2
          · have hpv : F.piv (.inr (.inr (.inl ⟨(p1, p1), hp1, hp2, hp12⟩))) = cnt [p1, p1] := by
              simp [piv, ho2]
            rw [hpv, hK3 ⟨(q1, q2), hq1, hq2, hq12⟩ _ (by simp)
              (hbd p1 (by have := ho p1; omega)) (fun h => hq.2 h.2)]
            simp [hlist]
          · rw [if_neg hq] at hr; omega
      · simp only [piv, if_neg hd]
        by_cases hq : q1 = q2 ∧ F.o q1 = 2
        · obtain ⟨rfl, hqo⟩ := hq
          rw [hK3d ⟨(q1, q1), hq1, hq2, hq12⟩ _ (by simp [hp12])
            (count_pair_lt hF (lt_of_le_of_ne hp12 hd)) (by rw [Wpair, hp1, hp2]) rfl hqo,
            hY2 _ _ _ hp12 (by rw [Wpair, hp1, hp2])]
          simp
        · rw [hK3 _ _ (by simp [hp12]) (count_pair_lt hF (lt_of_le_of_ne hp12 hd)) hq]
          simp [hlist]
    · by_cases hd : p1 = p2
      · subst hd
        by_cases ho2 : F.o p1 = 2
        · simp only [piv, if_pos, ho2]
          exact hK4 _ _ (hbs _) (by rw [Wsingle, hp1]; omega)
        · simp only [piv, if_pos, ho2, if_false]
          exact hK4 _ _ (hbd _ (by have := ho p1; omega)) (by rw [Wpair, hp1])
      · simp only [piv, if_neg hd]
        exact hK4 _ _ (count_pair_lt hF (lt_of_le_of_ne hp12 hd)) (by rw [Wpair, hp1, hp2])
    -- f = K4 b
    · simp [rk] at hr
    · simp [rk] at hr
    · simp only [rk] at hr; split_ifs at hr <;> omega
    · have hbb : b'.1.val ≠ b.1.val := fun h => hne (by
        congr 3; apply Subtype.ext; funext j; exact Fin.ext (congrFun h j))
      show F.crd b.1.val (F.P b'.1.val) = 0
      rw [F.crd_P b'.1.val_lt b.1.val_lt, if_neg hbb]

/-! ## `ψ₃` on the span of Losey's basis -/

omit hF in
/-- The span of Losey's basis (this is `Λ₃`; we only use that it contains what we need). -/
noncomputable def L3 : Submodule ℤ (MonoidAlgebra ℤ G) := Submodule.span ℤ (Set.range F.fam)

/-- Losey's basis as a basis of `L3`. -/
noncomputable def basisL3 : Module.Basis F.Fam ℤ F.L3 :=
  Module.Basis.span (fam_linearIndependent hF)

/-- Tahara's `ψ₃ : Λ₃ → W₃* ⊕ W₄`. -/
noncomputable def ψ3 : F.L3 →ₗ[ℤ] F.M3 := (basisL3 hF).constr ℤ F.famVal

omit hF in
theorem fam_mem_L3 (f : F.Fam) : F.fam f ∈ F.L3 := Submodule.subset_span ⟨f, rfl⟩

theorem ψ3_fam (f : F.Fam) : ψ3 hF ⟨F.fam f, F.fam_mem_L3 f⟩ = F.famVal f := by
  have : (⟨F.fam f, F.fam_mem_L3 f⟩ : F.L3) = basisL3 hF f := by
    show _ = Module.Basis.span (fam_linearIndependent hF) f
    simp only [Module.Basis.span_apply]
    rfl
  rw [this, ψ3, Module.Basis.constr_basis]

/-- Pairs `(z, v)` with `z ∈ L3` and `ψ₃ z ≡ v (mod R₅*)`. -/
noncomputable def rel3 : Submodule ℤ (MonoidAlgebra ℤ G × F.M3) where
  carrier := {p | ∃ h : p.1 ∈ F.L3, ψ3 hF ⟨p.1, h⟩ - p.2 ∈ F.R5}
  add_mem' := by
    rintro ⟨z, v⟩ ⟨z', v'⟩ ⟨h, hv⟩ ⟨h', hv'⟩
    refine ⟨add_mem h h', ?_⟩
    have e : (⟨(z, v).1 + (z', v').1, add_mem h h'⟩ : F.L3) = ⟨z, h⟩ + ⟨z', h'⟩ := rfl
    simp only [Prod.fst_add, Prod.snd_add] at e ⊢
    rw [e, map_add]
    convert add_mem hv hv' using 1; abel
  zero_mem' := ⟨zero_mem _, by
    have e : (⟨(0 : MonoidAlgebra ℤ G × F.M3).1, zero_mem _⟩ : F.L3) = 0 := rfl
    rw [e, map_zero]; simp⟩
  smul_mem' := by
    rintro c ⟨z, v⟩ ⟨h, hv⟩
    refine ⟨Submodule.smul_mem _ c h, ?_⟩
    have e : (⟨(c • (z, v)).1, Submodule.smul_mem _ c h⟩ : F.L3) = c • ⟨z, h⟩ := rfl
    rw [e, map_smul]
    convert Submodule.smul_mem _ c hv using 1
    simp [smul_sub]

theorem mem_rel3 {z : MonoidAlgebra ℤ G} {v : F.M3} :
    (z, v) ∈ rel3 hF ↔ ∃ h : z ∈ F.L3, ψ3 hF ⟨z, h⟩ - v ∈ F.R5 := Iff.rfl

theorem rel3_fam (f : F.Fam) : (F.fam f, F.famVal f) ∈ rel3 hF :=
  ⟨F.fam_mem_L3 f, by rw [ψ3_fam, sub_self]; exact zero_mem _⟩

theorem rel3_congr {z : MonoidAlgebra ℤ G} {v v' : F.M3} (h : (z, v) ∈ rel3 hF)
    (hv : v - v' ∈ F.R5) : (z, v') ∈ rel3 hF := by
  obtain ⟨hz, h⟩ := h
  refine ⟨hz, ?_⟩
  have := add_mem h hv
  rwa [sub_add_sub_cancel] at this

theorem rel3_add {z z' : MonoidAlgebra ℤ G} {v v' : F.M3} (h : (z, v) ∈ rel3 hF)
    (h' : (z', v') ∈ rel3 hF) : (z + z', v + v') ∈ rel3 hF := add_mem h h'

theorem rel3_sub {z z' : MonoidAlgebra ℤ G} {v v' : F.M3} (h : (z, v) ∈ rel3 hF)
    (h' : (z', v') ∈ rel3 hF) : (z - z', v - v') ∈ rel3 hF := sub_mem h h'

theorem rel3_smul {z : MonoidAlgebra ℤ G} {v : F.M3} (c : ℤ) (h : (z, v) ∈ rel3 hF) :
    (c • z, c • v) ∈ rel3 hF := Submodule.smul_mem _ c h

theorem rel3_zero : ((0 : MonoidAlgebra ℤ G), (0 : F.M3)) ∈ rel3 hF := zero_mem _

theorem rel3_sum {α : Type*} (s : Finset α) (c : α → ℤ) (z : α → MonoidAlgebra ℤ G)
    (v : α → F.M3) (h : ∀ i ∈ s, (z i, v i) ∈ rel3 hF) :
    (∑ i ∈ s, c i • z i, ∑ i ∈ s, c i • v i) ∈ rel3 hF := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel3_zero hF
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact rel3_add hF (rel3_smul hF _ (h i (Finset.mem_insert_self i s)))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Frame

end TaharaProof

end GroupDimension
