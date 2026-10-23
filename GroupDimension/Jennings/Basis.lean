module

public import GroupDimension.Jennings.Frame

@[expose] public section

/-!
# The Jennings basis of `𝔽_p[G]`

Stage 2 of Jennings' theorem, for a frame `F` of a restricted N-series `S` of a finite group.

**Reduction of non-basic products.** If `a_x ≥ p` for a letter `x`, then in characteristic `p`
`(x - 1)^p = x^p - 1`, so

  `P(a) = P(a_lo) (x^p - 1) P(a_hi)`

(`P_reduce`), where `a_lo` keeps the letters `< x` and `a_x - p` copies of `x`, and `a_hi` the
letters `> x`. Since `x^p ∈ S (p w_x)`, the middle factor is a combination of products of weight
`≥ p w_x` in letters `> x`; sorting them past `a_hi` gives products `P β` with `β < a`
(lexicographically, the first letter most significant) and `W β ≥ W a` (`T_mem`). Unlike over `ℤ`
(`TaharaProof/Induction.lean`), no binomial terms of lower weight appear. By well-founded
induction, `P a ∈ Bsp (W a)` (`P_mem_Bsp_W`), hence `Sp k U ⊆ Bsp k` (`Sp_le_Bsp`) and
`Δ^n ⊆ Bsp n` (`augIdealP_pow_le_Bsp`).

**Basis.** The basic products (`0 ≤ b_j < p`) span `𝔽_p[G]` (`Bsp_zero`) and there are `|G|` of
them (the normal form), so they form a basis (`basis`). The coordinates of an element of `Bsp k`
at basic products of weight `< k` vanish (`repr_eq_zero_of_mem_Bsp`).
-/

namespace GroupDimension

namespace Jennings

open MonoidAlgebra TaharaProof

variable {p : ℕ} {G : Type*} [Group G]
variable {T : RestrictedSeries p G} {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace JFrame

variable (F : JFrame T ι)

/-! ## The reduction -/

/-- The span of the products `P β` with `β < a` (lexicographic order) and `W β ≥ K`. -/
noncomputable def Below (a : ι → ℕ) (K : ℕ) : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Submodule.span (ZMod p) {z | ∃ β, lexLT β a ∧ K ≤ F.W β ∧ z = F.P β}

/-- The letters `< x` of `a`, and `a_x - p` copies of `x`. -/
def lo (p : ℕ) (a : ι → ℕ) (x : ι) : ι → ℕ :=
  fun j => if j < x then a j else if j = x then a x - p else 0

/-- The letters `> x` of `a`. -/
def hi (a : ι → ℕ) (x : ι) : ι → ℕ := fun j => if x < j then a j else 0

omit [Fintype ι] in
theorem lo_add_hi {a : ι → ℕ} {x : ι} (hx : p ≤ a x) :
    lo p a x + p • (Pi.single x 1 : ι → ℕ) + hi a x = a := by
  classical
  funext j
  simp only [lo, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases lt_trichotomy j x with h | rfl | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp; omega
  · simp [h, h.ne', not_lt.2 h.le]

theorem P_lo_mul_pow (a : ι → ℕ) (x : ι) (m : ℕ) :
    F.P (lo p a x) * F.X x ^ m = F.P (lo p a x + m • (Pi.single x 1 : ι → ℕ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, F.P_mul_X]
    · congr 1; rw [succ_nsmul, add_assoc]
    · intro j hj
      simp [lo, not_lt.2 hj.le, hj.ne']

theorem P_mul_hi (a : ι → ℕ) (x : ι) (m : ℕ) :
    F.P (lo p a x + m • (Pi.single x 1 : ι → ℕ)) * F.P (hi a x) =
      F.P (lo p a x + m • (Pi.single x 1 : ι → ℕ) + hi a x) := by
  refine F.P_mul_P fun i j hi hj => ?_
  have hj' : x < j := by
    by_contra h; exact hj (by simp [JFrame.hi, h])
  have hi' : i ≤ x := by
    by_contra h; push Not at h
    exact hi (by simp [lo, not_lt.2 h.le, h.ne'])
  exact lt_of_le_of_lt hi' hj'

/-- In characteristic `p`: `(x - 1)^p = x^p - 1`. -/
theorem X_pow_p [Fact p.Prime] (x : ι) : F.X x ^ p = of (ZMod p) G (F.x x ^ p) - 1 := by
  haveI := charP (p := p) (G := G)
  have h := add_pow_char_of_commute p (Commute.one_right (F.X x))
  rw [one_pow, X, sub_add_cancel, ← map_pow] at h
  rw [h, add_sub_cancel_right]; rfl

/-- **Reduction** of a non-basic product: `P(a) = P(a_lo) (x^p - 1) P(a_hi)`. -/
theorem P_reduce [Fact p.Prime] {a : ι → ℕ} {x : ι} (hx : p ≤ a x) :
    F.P a = F.P (lo p a x) * (of (ZMod p) G (F.x x ^ p) - 1) * F.P (hi a x) := by
  rw [← F.X_pow_p, F.P_lo_mul_pow, F.P_mul_hi, lo_add_hi hx]

theorem W_lo_add_hi {a : ι → ℕ} {x : ι} (hx : p ≤ a x) :
    F.W a = F.W (lo p a x) + p * F.w x + F.W (hi a x) := by
  conv_lhs => rw [← lo_add_hi hx]
  rw [W_add, W_add, W_nsmul_single]

/-- The reduced term lies below `a`, with weight at least `W a`. -/
theorem T_mem [Fact p.Prime] {a : ι → ℕ} {x : ι} (hx : p ≤ a x) :
    F.P (lo p a x) * (of (ZMod p) G (F.x x ^ p) - 1) * F.P (hi a x) ∈ F.Below a (F.W a) := by
  classical
  have hp2 := (Fact.out : p.Prime).two_le
  have hU : IsUpperSet (Set.Ioi x) := isUpperSet_Ioi x
  have hQ : ∀ i ∈ Set.Ioi x, ∀ k, ∀ z ∈ F.Sp k (Set.Ioi x),
      z * F.X i ∈ F.Sp (k + F.w i) (Set.Ioi x) :=
    fun i hi => F.Sp_mul_X hU i hi
  have hwx := F.w_pos x
  have hy : of (ZMod p) G (F.x x ^ p) - 1 ∈ F.Sp (p * F.w x) (Set.Ioi x) :=
    F.of_sub_one_mem (by nlinarith) (T.pow (F.w_pos x) _ (F.mem x)) _
      fun j hj => F.lt_of_w_lt (by nlinarith)
  have hhi : F.P (hi a x) ∈ F.Sp (F.W (hi a x)) (Set.Ioi x) :=
    F.P_mem_Sp le_rfl fun j hj => by
      by_contra h; exact hj (by simp [hi, show ¬ x < j from h])
  have hz := F.Sp_mul_Sp hQ hy hhi
  obtain ⟨z, hz, hz'⟩ : ∃ z, z ∈ F.Sp (p * F.w x + F.W (hi a x)) (Set.Ioi x) ∧
      z = (of (ZMod p) G (F.x x ^ p) - 1) * F.P (hi a x) := ⟨_, hz, rfl⟩
  rw [mul_assoc, ← hz']
  clear hz'
  have hWa := F.W_lo_add_hi hx
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  | mem z hz =>
  obtain ⟨β, hβ, hβU, rfl⟩ := hz
  have hsep : ∀ i j, lo p a x i ≠ 0 → β j ≠ 0 → i < j := by
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
    omega

/-- Every product `P a` is a combination of basic products of weight `≥ W a`. -/
theorem P_mem_Bsp_W [Fact p.Prime] (a : ι → ℕ) : F.P a ∈ F.Bsp (F.W a) := by
  refine lexLT_wf.induction (C := fun a => F.P a ∈ F.Bsp (F.W a)) a ?_
  intro a IH
  by_cases hb : ∀ j, a j < p
  · exact F.P_mem_Bsp hb le_rfl
  push Not at hb
  obtain ⟨x, hx⟩ := hb
  rw [F.P_reduce hx]
  refine Submodule.span_le.mpr ?_ (F.T_mem hx)
  rintro _ ⟨β, hβ, hK, rfl⟩
  exact F.Bsp_mono hK (IH β hβ)

/-- `Sp k U ⊆ Bsp k`. -/
theorem Sp_le_Bsp [Fact p.Prime] (k : ℕ) (U : Set ι) : F.Sp k U ≤ F.Bsp k :=
  Submodule.span_le.mpr fun _ ⟨a, ha, _, e⟩ => e ▸ F.Bsp_mono ha (F.P_mem_Bsp_W a)

/-- `Δ^n ⊆ Bsp n`. -/
theorem augIdealP_pow_le_Bsp [Fact p.Prime] (n : ℕ) {z : MonoidAlgebra (ZMod p) G}
    (hz : z ∈ augIdealP p G ^ n) : z ∈ F.Bsp n :=
  F.Sp_le_Bsp n Set.univ (F.augIdealP_pow_le_Sp n hz)

/-! ## The basis -/

/-- Basic sequences: `0 ≤ b_j < p`. -/
abbrev Basic (_F : JFrame T ι) := ι → Fin p

/-- A basic sequence as a sequence of naturals. -/
def bval (b : ι → Fin p) : ι → ℕ := fun j => b j

omit [LinearOrder ι] [Fintype ι] in
theorem bval_lt (b : ι → Fin p) (j : ι) : bval b j < p := (b j).isLt

/-- The basic sequence of a sequence below `p`. -/
def toFin (b : ι → ℕ) (hb : ∀ j, b j < p) : ι → Fin p := fun j => ⟨b j, hb j⟩

omit [LinearOrder ι] [Fintype ι] in
@[simp] theorem bval_toFin (b : ι → ℕ) (hb : ∀ j, b j < p) : bval (toFin b hb) = b := rfl

omit [LinearOrder ι] [Fintype ι] in
theorem bval_injective : Function.Injective (bval : (ι → Fin p) → ι → ℕ) :=
  fun _ _ h => funext fun j => Fin.ext (congrFun h j)

/-- The normal form as a bijection `F.Basic ≃ G`. -/
noncomputable def nfEquiv : F.Basic ≃ G :=
  Equiv.ofBijective (fun b => F.nprod (bval b))
    ⟨fun b c h => bval_injective (F.nf_unique _ _ (bval_lt b) (bval_lt c) h),
    fun g => by
      obtain ⟨b, hb, rfl⟩ := F.nf g
      exact ⟨toFin b hb, rfl⟩⟩

theorem P_span : ⊤ ≤ Submodule.span (ZMod p) (Set.range fun b : F.Basic => F.P (bval b)) := by
  rw [← F.Bsp_zero]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, -, rfl⟩
  exact Submodule.subset_span ⟨toFin a ha, rfl⟩

variable [Fact p.Prime] [Fintype G]

theorem P_linearIndependent :
    LinearIndependent (ZMod p) fun b : F.Basic => F.P (bval b) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank F.P_span ?_
  have h := ((MonoidAlgebra.coeffLinearEquiv (ZMod p)).trans
    (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) G)).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [Fintype.card_congr F.nfEquiv]; exact h.symm

/-- The Jennings basis of `𝔽_p[G]` by basic products. -/
noncomputable def basis : Module.Basis F.Basic (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Module.Basis.mk F.P_linearIndependent F.P_span

@[simp] theorem basis_apply (b : F.Basic) : F.basis b = F.P (bval b) := by
  simp [basis]

/-- The coordinates of an element of `Bsp k` at basic products of weight `< k` vanish. -/
theorem repr_eq_zero_of_mem_Bsp {k : ℕ} {z : MonoidAlgebra (ZMod p) G} (hz : z ∈ F.Bsp k)
    (c : F.Basic) (hc : F.W (bval c) < k) : F.basis.repr z c = 0 := by
  classical
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul r u _ hu => simp [hu]
  | mem z hz =>
  obtain ⟨a, ha, hk, rfl⟩ := hz
  have e : F.P a = F.basis (toFin a ha) := by simp
  rw [e, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
  rintro rfl
  simp at hc; omega

end JFrame

end Jennings

end GroupDimension
