module

public import GroupDimension.TaharaProof.Layers

@[expose] public section

/-!
# Reduction of non-basic proper products ([Tah81, proof of Lemma 3.5])

Tahara orders `m`-sequences lexicographically, the first letter being the most significant
(`lexLT`). A non-basic proper product `P(a)` (some `a_x ≥ o_x = d`) reduces to smaller ones:
with `(x - 1)^d = (x^d - 1) - ∑_{0<h<d} C(d,h) (x - 1)^h`,

  `P(a) = P(a_lo) (x^d - 1) P(a_hi) - ∑_{0<h<d} C(d,h) P(a - (d - h) e_x)`,

where `a_lo` keeps the letters `< x` and `a_x - d` copies of `x`, and `a_hi` the letters `> x`
(`P_reduce`). The first term is a combination of `P(β)` with `β < a` (`T_mem`): `x^d` has weight
`> w_x`, so its letters and everything produced by sorting them past `a_hi` come after `x`.

We also record the words of `m`-sequences (`word`): the letters in order with multiplicity.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

/-! ## Tahara's order -/

/-- Tahara's order on `m`-sequences: lexicographic, the first letter most significant. -/
def lexLT (β a : ι → ℕ) : Prop := toLex β < toLex a

theorem lexLT_of {β a : ι → ℕ} (i : ι) (h1 : ∀ j < i, β j = a j) (h2 : β i < a i) :
    lexLT β a :=
  ⟨i, h1, h2⟩

theorem lexLT_wf : WellFounded (lexLT : (ι → ℕ) → (ι → ℕ) → Prop) :=
  InvImage.wf toLex wellFounded_lt

/-! ## Words -/

namespace Frame

theorem count_word [DecidableEq ι] (a : ι → ℕ) (i : ι) : (word a).count i = a i := by
  unfold word
  rw [count_flatMap_replicate ((ordL_pairwise).imp ne_of_lt), if_pos (mem_ordL i)]

theorem word_pairwise (a : ι → ℕ) : (word a).Pairwise (· ≤ ·) := by
  unfold word
  rw [List.pairwise_flatMap]
  refine ⟨fun j _ => List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
  refine ordL_pairwise.imp fun {i j} hij => ?_
  intro x hx y hy
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]; exact hij.le

/-- A sorted list is the word of its counts. -/
theorem word_eq [DecidableEq ι] {a : ι → ℕ} {l : List ι} (hl : l.Pairwise (· ≤ ·))
    (hc : ∀ i, l.count i = a i) : word a = l := by
  refine List.Perm.eq_of_pairwise' (word_pairwise a) hl ?_
  rw [List.perm_iff_count]
  intro i; rw [count_word, hc]

@[simp] theorem nsmul_single_apply [DecidableEq ι] (m : ℕ) (x j : ι) :
    (m • (Pi.single x 1 : ι → ℕ)) j = if j = x then m else 0 := by
  by_cases h : j = x
  · subst h; simp
  · simp [Pi.single_eq_of_ne h, h]

theorem single_apply' [DecidableEq ι] (x j : ι) :
    (Pi.single x 1 : ι → ℕ) j = if j = x then 1 else 0 := by
  by_cases h : j = x
  · subst h; simp
  · simp [Pi.single_eq_of_ne h, h]

theorem sum_nsmul_single (m : ℕ) (x : ι) : ∑ j, (m • (Pi.single x 1 : ι → ℕ)) j = m := by
  classical
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_pi_single']; simp

theorem length_word (a : ι → ℕ) : (word a).length = ∑ j, a j := by
  simp only [word, List.length_flatMap, List.length_replicate]
  exact sum_ordL _

theorem word_single [DecidableEq ι] (i : ι) : word (Pi.single i 1 : ι → ℕ) = [i] :=
  word_eq (List.pairwise_singleton _ _) fun j => by
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h, List.count_singleton, Ne.symm h]

theorem word_nsmul_single [DecidableEq ι] (n : ℕ) (i : ι) :
    word (n • Pi.single i 1 : ι → ℕ) = List.replicate n i :=
  word_eq (List.pairwise_replicate.mpr (Or.inr le_rfl)) fun j => by
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h, List.count_replicate, Ne.symm h]

theorem word_pair [DecidableEq ι] {i j : ι} (h : i ≤ j) :
    word ((Pi.single i 1 : ι → ℕ) + Pi.single j 1) = [i, j] :=
  word_eq (by simp [h]) fun k => by
    rw [List.count_cons, List.count_singleton]
    by_cases hi : k = i <;> by_cases hj : k = j
    · subst hi; subst hj; simp
    · subst hi; simp [Pi.single_eq_of_ne hj, Ne.symm hj]
    · subst hj; simp [Pi.single_eq_of_ne hi, Ne.symm hi]
    · simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj, Ne.symm hi, Ne.symm hj]

variable (F : Frame G ι)

theorem o_pos (j : ι) : 0 < F.o j := by
  obtain ⟨b, hb, -⟩ := F.nf 1
  exact lt_of_le_of_lt (Nat.zero_le _) (hb j)

theorem W_eq_sum_word (a : ι → ℕ) : F.W a = ((word a).map F.w).sum := F.W_eq_word a

theorem W_pos {a : ι → ℕ} (ha : a ≠ 0) : 1 ≤ F.W a := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra h; push Not at h; exact ha (funext h)
  calc 1 ≤ F.w j := F.w_pos j
    _ ≤ a j * F.w j := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj)
    _ ≤ F.W a := Finset.single_le_sum (f := fun j => a j * F.w j) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)

theorem W_ge_sum (a : ι → ℕ) : ∑ j, a j ≤ F.W a := by
  unfold W
  exact Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_right _ (F.w_pos j)

/-! ## Spans below an `m`-sequence -/

/-- The span of the proper products `P β` with `β < a` (Tahara's order) and `W β ≥ K`. -/
noncomputable def Below (a : ι → ℕ) (K : ℕ) : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ {z | ∃ β, lexLT β a ∧ K ≤ F.W β ∧ z = F.P β}

theorem Below_mono {a : ι → ℕ} {K K' : ℕ} (h : K ≤ K') : F.Below a K' ≤ F.Below a K :=
  Submodule.span_mono fun _ ⟨β, h1, h2, e⟩ => ⟨β, h1, h.trans h2, e⟩

/-! ## The reduction -/

/-- The letters `< x` of `a`, and `a_x - o_x` copies of `x`. -/
def lo (a : ι → ℕ) (x : ι) : ι → ℕ :=
  fun j => if j < x then a j else if j = x then a x - F.o x else 0

/-- The letters `> x` of `a`. -/
def hi (a : ι → ℕ) (x : ι) : ι → ℕ := fun j => if x < j then a j else 0

theorem lo_add_hi {a : ι → ℕ} {x : ι} (hx : F.o x ≤ a x) (m : ℕ) (hm : m ≤ F.o x) :
    F.lo a x + m • (Pi.single x 1 : ι → ℕ) + hi a x = a - (F.o x - m) • Pi.single x 1 := by
  classical
  funext j
  simp only [lo, hi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rcases lt_trichotomy j x with h | rfl | h
  · simp [h, h.ne, not_lt.2 h.le, Pi.single_eq_of_ne h.ne]
  · simp; omega
  · simp [h, h.ne', not_lt.2 h.le, Pi.single_eq_of_ne h.ne']

theorem P_lo_mul_pow (a : ι → ℕ) (x : ι) (m : ℕ) :
    F.P (F.lo a x) * F.X x ^ m = F.P (F.lo a x + m • (Pi.single x 1 : ι → ℕ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, F.P_mul_X]
    · congr 1; rw [succ_nsmul, add_assoc]
    · intro j hj
      simp [lo, not_lt.2 hj.le, hj.ne', Pi.single_eq_of_ne hj.ne']

theorem P_mul_hi (a : ι → ℕ) (x : ι) (m : ℕ) :
    F.P (F.lo a x + m • (Pi.single x 1 : ι → ℕ)) * F.P (hi a x) =
      F.P (F.lo a x + m • (Pi.single x 1 : ι → ℕ) + hi a x) := by
  refine F.P_mul_P fun i j hi hj => ?_
  have hj' : x < j := by
    by_contra h; exact hj (by simp [Frame.hi, h])
  have hi' : i ≤ x := by
    by_contra h; push Not at h
    exact hi (by simp [lo, not_lt.2 h.le, h.ne', Pi.single_eq_of_ne h.ne'])
  exact lt_of_le_of_lt hi' hj'

/-- `(x - 1)^(d+1) = (x^(d+1) - 1) - ∑_{0<h<d+1} C(d+1,h) (x - 1)^h`. -/
theorem X_pow_eq (x : ι) (d : ℕ) :
    F.X x ^ (d + 1) = (of ℤ G (F.x x ^ (d + 1)) - 1) -
      ∑ h ∈ Finset.range d, ((d + 1).choose (h + 1) : MonoidAlgebra ℤ G) * F.X x ^ (h + 1) := by
  have h1 : of ℤ G (F.x x ^ (d + 1)) = (F.X x + 1) ^ (d + 1) := by
    rw [map_pow]; simp [X]
  rw [h1, (Commute.one_right (F.X x)).add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, pow_zero, Nat.choose_zero_right]
  rw [Finset.sum_congr rfl fun h _ => (Nat.cast_comm _ _).symm]
  abel

/-- **Reduction** of a non-basic proper product ([Tah81, proof of Lemma 3.5]). -/
theorem P_reduce {a : ι → ℕ} {x : ι} (hx : F.o x ≤ a x) :
    F.P a = F.P (F.lo a x) * (of ℤ G (F.x x ^ F.o x) - 1) * F.P (hi a x) -
      ∑ h ∈ Finset.range (F.o x - 1), ((F.o x).choose (h + 1) : ℤ) •
        F.P (a - (F.o x - (h + 1)) • (Pi.single x 1 : ι → ℕ)) := by
  obtain ⟨d, hd⟩ : ∃ d, F.o x = d + 1 := ⟨F.o x - 1, by have := F.o_pos x; omega⟩
  have e0 : F.P a = F.P (F.lo a x) * F.X x ^ (d + 1) * F.P (hi a x) := by
    rw [F.P_lo_mul_pow, F.P_mul_hi, ← hd, F.lo_add_hi hx _ le_rfl, Nat.sub_self, zero_smul,
      tsub_zero]
  have eh : ∀ h ∈ Finset.range d, F.P (F.lo a x) * F.X x ^ (h + 1) * F.P (hi a x) =
      F.P (a - (F.o x - (h + 1)) • (Pi.single x 1 : ι → ℕ)) := by
    intro h hh
    rw [Finset.mem_range] at hh
    rw [F.P_lo_mul_pow, F.P_mul_hi, F.lo_add_hi hx _ (by omega)]
  have hc : ∀ (n : ℕ) (u v w : MonoidAlgebra ℤ G),
      u * ((n : MonoidAlgebra ℤ G) * v) * w = (n : ℤ) • (u * v * w) := by
    intro n u v w
    rw [natCast_zsmul, nsmul_eq_mul, ← mul_assoc u, ← Nat.cast_comm n u]
    simp only [mul_assoc]
  rw [hd] at eh
  rw [e0, X_pow_eq, hd, Nat.add_sub_cancel, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [← eh h hh, hc]

/-- The first term of the reduction lies below `a`. -/
theorem T_mem {a : ι → ℕ} {x : ι} (hx : F.o x ≤ a x) :
    F.P (F.lo a x) * (of ℤ G (F.x x ^ F.o x) - 1) * F.P (hi a x) ∈
      F.Below a (F.W (F.lo a x) + (F.w x + 1 + F.W (hi a x))) := by
  classical
  have hU : IsUpperSet (Set.Ioi x) := isUpperSet_Ioi x
  have hQ : ∀ i ∈ Set.Ioi x, ∀ k, ∀ z ∈ F.Sp k (Set.Ioi x), z * F.X i ∈ F.Sp (k + F.w i) (Set.Ioi x) :=
    fun i hi => F.Sp_mul_X hU i hi
  have hy : of ℤ G (F.x x ^ F.o x) - 1 ∈ F.Sp (F.w x + 1) (Set.Ioi x) :=
    F.of_sub_one_mem (by simpa using F.pow_mem x) _ fun j hj => F.lt_of_w_lt (by omega)
  have hhi : F.P (hi a x) ∈ F.Sp (F.W (hi a x)) (Set.Ioi x) :=
    F.P_mem_Sp le_rfl fun j hj => by
      by_contra h; exact hj (by simp [hi, show ¬ x < j from h])
  have hz := F.Sp_mul_Sp hQ hy hhi
  obtain ⟨z, hz, hz'⟩ : ∃ z, z ∈ F.Sp (F.w x + 1 + F.W (hi a x)) (Set.Ioi x) ∧
      z = (of ℤ G (F.x x ^ F.o x) - 1) * F.P (hi a x) := ⟨_, hz, rfl⟩
  rw [mul_assoc, ← hz']
  clear hz'
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  | mem z hz =>
  obtain ⟨β, hβ, hβU, rfl⟩ := hz
  have hsep : ∀ i j, F.lo a x i ≠ 0 → β j ≠ 0 → i < j := by
    intro i j hi hj
    have hi' : i ≤ x := by
      by_contra h; push Not at h
      exact hi (by simp [lo, not_lt.2 h.le, h.ne'])
    exact lt_of_le_of_lt hi' (hβU j hj)
  rw [F.P_mul_P hsep]
  refine Submodule.subset_span ⟨_, ?_, by rw [W_add]; omega, rfl⟩
  have hβx : β x = 0 := by
    by_contra h; exact lt_irrefl x (hβU x h)
  refine lexLT_of x (fun j hj => ?_) ?_
  · have : β j = 0 := by
      by_contra h; exact absurd (hβU j h) (not_lt.2 hj.le)
    simp [lo, hj, this]
  · simp [lo, hβx]
    have := F.o_pos x; omega

/-- Elements below `a` of large weight, when all smaller products there have value `0`. -/
theorem below_rel {M : Type*} [AddCommGroup M] (rel : Submodule ℤ (MonoidAlgebra ℤ G × M))
    {a : ι → ℕ} {K : ℕ} (IH : ∀ β, lexLT β a → K ≤ F.W β → (F.P β, (0 : M)) ∈ rel)
    {z : MonoidAlgebra ℤ G} (hz : z ∈ F.Below a K) : (z, (0 : M)) ∈ rel := by
  induction hz using Submodule.span_induction with
  | zero => exact zero_mem _
  | add u v _ _ hu hv => simpa using add_mem hu hv
  | smul c u _ hu => simpa using Submodule.smul_mem _ c hu
  | mem z hz =>
  obtain ⟨β, hβ, hK, rfl⟩ := hz
  exact IH β hβ hK

end Frame

end TaharaProof

end GroupDimension
