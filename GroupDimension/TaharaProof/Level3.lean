import GroupDimension.TaharaProof.Level3Basis

/-!
# `ψ₃(Λ₅) ⊆ R₅*` ([Tah81, Lemmas 5.3–5.6])

We prove `ψ₃(P(a)) ≡ Φ₃(a) (mod R₅*)` for every `m`-sequence `a` of weight `≥ 3` (`U3`), by
Tahara's induction over `a` (in his order). A basic `a`, and the powers `(x - 1)^{o(x)}` of
letters of weights `1, 2`, are members of Losey's basis. Otherwise reduce `a` at a letter `x`
with `a_x ≥ d = o(x)` (`P_reduce`):

  `P(a) = P(a_lo) (y - 1) P(a_hi) - ∑_{0<h<d} C(d,h) P(r + h e_x)`, `y = x^d`, `r = a - d e_x`.

The first term `T` is evaluated to first order (`TE1`–`TE4`: commuting `y - 1` past the letters
of `a_hi` with `(u-1)(v-1) = (v-1)(u-1) + (c-1)(1 + (v-1) + (u-1) + (v-1)(u-1))`, `c = [u,v]`),
everything of weight `≥ 5` being negligible. Matching the result against the binomial terms gives
exactly one of the relations (I)–(VII) or the definition of `ψ₃` on `d(i)(x_i - 1)(x_j - 1)`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable (F : Frame G ι)

/-- `g - 1`. -/
noncomputable abbrev E (g : G) : MonoidAlgebra ℤ G := of ℤ G g - 1

omit [Fintype ι] in
/-- `(g-1)(h-1) = (h-1)(g-1) + (c-1) + (h-1)(c-1) + (g-1)(c-1) + (h-1)(g-1)(c-1)`, `c = [g, h]`. -/
theorem E_comm (g h : G) :
    E g * E h = E h * E g + E (tc g h) + E h * E (tc g h) + E g * E (tc g h) +
      E h * E g * E (tc g h) := by
  have e : of ℤ G g * of ℤ G h = of ℤ G h * of ℤ G g * of ℤ G (tc g h) := by
    rw [← _root_.map_mul, ← _root_.map_mul, ← _root_.map_mul]; congr 1; simp only [tc]; group
  simp only [E]
  rw [← sub_eq_zero]
  have e2 : ∀ a b c : MonoidAlgebra ℤ G,
      (b - 1) * (a - 1) - ((a - 1) * (b - 1) + (c - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1) +
        (a - 1) * (b - 1) * (c - 1)) = b * a - a * b * c := by
    intro a b c; noncomm_ring
  rw [e2, e, sub_self]

theorem X_eq_E (j : ι) : F.X j = E (F.x j) := rfl

/-! ## Memberships in `Sp K (Ioi x)` -/

theorem X_mem_Ioi {x m : ι} (h : x < m) : F.X m ∈ F.Sp (F.w m) (Set.Ioi x) := by
  rw [← F.P_single]
  refine F.P_mem_Sp (le_of_eq (F.W_single m).symm) fun j hj => ?_
  by_cases hjm : j = m
  · exact hjm ▸ h
  · simp [Pi.single_eq_of_ne hjm] at hj

theorem E_mem_Ioi {x : ι} {g : G} {k : ℕ} (hg : g ∈ lowerCentralSeries G (k - 1))
    (hk : F.w x < k) : E g ∈ F.Sp k (Set.Ioi x) :=
  F.of_sub_one_mem hg _ fun j hj => F.lt_of_w_lt (by omega)

theorem mul_mem_Ioi {x : ι} {K K' : ℕ} {z z' : MonoidAlgebra ℤ G} (hz : z ∈ F.Sp K (Set.Ioi x))
    (hz' : z' ∈ F.Sp K' (Set.Ioi x)) : z * z' ∈ F.Sp (K + K') (Set.Ioi x) :=
  F.Sp_mul_Sp (fun i hi => F.Sp_mul_X (isUpperSet_Ioi x) i hi) hz hz'

/-- The letters of `lo a x` are `≤ x`. -/
theorem lo_eq_zero {a : ι → ℕ} {x j : ι} (h : x < j) : F.lo a x j = 0 := by
  simp [lo, not_lt.2 h.le, h.ne']

theorem lo_lt {a : ι → ℕ} {x : ι} (hx : F.o x ≤ a x) : F.lo a x x < a x := by
  simp [lo]; have := F.o_pos x; omega

/-- `P(a_lo) · Sp K (Ioi x) ⊆ Below a (W(a_lo) + K)`. -/
theorem lo_mul_mem_Below {a : ι → ℕ} {x : ι} (hx : F.o x ≤ a x) {K : ℕ}
    {z : MonoidAlgebra ℤ G} (hz : z ∈ F.Sp K (Set.Ioi x)) :
    F.P (F.lo a x) * z ∈ F.Below a (F.W (F.lo a x) + K) := by
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  | mem z hz =>
  obtain ⟨β, hβ, hβU, rfl⟩ := hz
  have hsep : ∀ i j, F.lo a x i ≠ 0 → β j ≠ 0 → i < j := by
    intro i j hi hj
    have hi' : i ≤ x := by
      by_contra h; push Not at h; exact hi (F.lo_eq_zero h)
    exact lt_of_le_of_lt hi' (hβU j hj)
  rw [F.P_mul_P hsep]
  refine Submodule.subset_span ⟨_, ?_, by rw [W_add]; omega, rfl⟩
  have hβx : β x = 0 := by
    by_contra h; exact lt_irrefl x (hβU x h)
  refine lexLT_of x (fun j hj => ?_) ?_
  · have : β j = 0 := by
      by_contra h; exact absurd (hβU j h) (not_lt.2 hj.le)
    simp [lo, hj, this]
  · simp only [Pi.add_apply, hβx, add_zero]; exact F.lo_lt hx

variable [Fintype G] {F} (hF : F.Class4)

/-! ## The induction context -/

/-- The induction hypothesis at `a`. -/
def IHat (a : ι → ℕ) : Prop := ∀ β, lexLT β a → 3 ≤ F.W β → (F.P β, F.Φ3 β) ∈ rel3 hF

variable {hF} {a : ι → ℕ} (IH : IHat hF a) {x : ι} (hx : F.o x ≤ a x)
include IH hx

/-- Negligible terms: weight `≥ 5` below `a`. -/
theorem junk {K : ℕ} {z : MonoidAlgebra ℤ G} (hz : z ∈ F.Sp K (Set.Ioi x))
    (hK : 5 ≤ F.W (F.lo a x) + K) : (F.P (F.lo a x) * z, (0 : F.M3)) ∈ rel3 hF := by
  refine F.below_rel (rel3 hF) (a := a) (K := 5) (fun β hβ h5 => ?_)
    (F.Below_mono hK (F.lo_mul_mem_Below hx hz))
  have := IH β hβ (by omega)
  rwa [F.Φ3_eq_zero_of_five_le h5] at this

/-- A sorted product `P(a_lo) P(β)` with `β` after `x`. -/
theorem sorted {β : ι → ℕ} (hβ : ∀ j, β j ≠ 0 → x < j) (hW : 3 ≤ F.W (F.lo a x + β)) :
    (F.P (F.lo a x) * F.P β, F.Φ3 (F.lo a x + β)) ∈ rel3 hF := by
  have hsep : ∀ i j, F.lo a x i ≠ 0 → β j ≠ 0 → i < j := by
    intro i j hi hj
    have hi' : i ≤ x := by
      by_contra h; push Not at h; exact hi (F.lo_eq_zero h)
    exact lt_of_le_of_lt hi' (hβ j hj)
  rw [F.P_mul_P hsep]
  refine IH _ ?_ hW
  have hβx : β x = 0 := by
    by_contra h; exact lt_irrefl x (hβ x h)
  refine lexLT_of x (fun j hj => ?_) ?_
  · have : β j = 0 := by
      by_contra h; exact absurd (hβ j h) (not_lt.2 hj.le)
    simp [lo, hj, this]
  · simp only [Pi.add_apply, hβx, add_zero]; exact F.lo_lt hx

/-- **First order**: `P(a_lo) P(β) (g - 1) ≡ ∑_m n_g(m) Φ(a_lo + β + e_m)`, for `g ∈ γ_k` with
`k` above `w_x` and the weights of the letters of `β`. -/
theorem first_order {β : ι → ℕ} (hβ : ∀ j, β j ≠ 0 → x < j) {g : G} {k : ℕ}
    (hg : g ∈ lowerCentralSeries G (k - 1)) (hkx : F.w x < k)
    (hkβ : ∀ j, β j ≠ 0 → F.w j < k) (h3 : 3 ≤ F.W (F.lo a x) + F.W β + k)
    (h5 : 5 ≤ F.W (F.lo a x) + F.W β + 2 * k) :
    (F.P (F.lo a x) * F.P β * E g, F.nsum g (F.lo a x + β)) ∈ rel3 hF := by
  classical
  obtain ⟨-, h2⟩ := F.of_nprod_sub_one (F.nfc g)
  rw [F.nprod_nfc] at h2
  have hn : ∀ m, F.nfc g m ≠ 0 → k ≤ F.w m := fun m hm =>
    F.nf_weight hg (F.nfc_lt g) (F.nprod_nfc g) hm
  -- the remainder is negligible
  have hrem : (F.P (F.lo a x) * F.P β * (E g - ∑ m, (F.nfc g m : ℤ) • F.X m), (0 : F.M3)) ∈
      rel3 hF := by
    have hRem : E g - ∑ m, (F.nfc g m : ℤ) • F.X m ∈ F.Sp (2 * k) (Set.Ioi x) := by
      refine Submodule.span_le.mpr ?_ h2
      rintro _ ⟨γ, hγ, hγ2, rfl⟩
      have hγn : ∀ j, γ j ≠ 0 → F.nfc g j ≠ 0 := fun j hj h0 => hj (by
        have : γ j ≤ F.nfc g j := hγ j; omega)
      refine F.P_mem_Sp ?_ fun j hj => F.lt_of_w_lt (by have := hn j (hγn j hj); omega)
      calc 2 * k ≤ (∑ j, γ j) * k := Nat.mul_le_mul_right _ hγ2
        _ = ∑ j, γ j * k := Finset.sum_mul _ _ _
        _ ≤ ∑ j, γ j * F.w j := Finset.sum_le_sum fun j _ => by
            by_cases h : γ j = 0
            · simp [h]
            · exact Nat.mul_le_mul_left _ (hn j (hγn j h))
    have hPβ : F.P β ∈ F.Sp (F.W β) (Set.Ioi x) := F.P_mem_Sp le_rfl hβ
    rw [mul_assoc]
    exact junk IH hx (F.mul_mem_Ioi hPβ hRem) (by omega)
  -- the linear part
  have hlin : (F.P (F.lo a x) * F.P β * ∑ m, (F.nfc g m : ℤ) • F.X m,
      F.nsum g (F.lo a x + β)) ∈ rel3 hF := by
    rw [Finset.mul_sum, nsum]
    have key : ∀ m ∈ Finset.univ.filter fun m => F.nfc g m ≠ 0,
        (F.P (F.lo a x) * F.P (β + Pi.single m 1), F.Φ3 (F.lo a x + β + Pi.single m 1)) ∈
          rel3 hF := by
      intro m hm
      have hm0 := (Finset.mem_filter.mp hm).2
      have hwm := hn m hm0
      have hxm : x < m := F.lt_of_w_lt (by omega)
      rw [add_assoc]
      refine sorted IH hx (fun j hj => ?_) ?_
      · by_cases hjm : j = m
        · exact hjm ▸ hxm
        · exact hβ j (by simpa [Pi.single_eq_of_ne hjm] using hj)
      · rw [W_add, W_add, W_single]; omega
    have := rel3_sum hF _ (fun m => (F.nfc g m : ℤ)) _ _ key
    have e1 : ∀ m, F.nfc g m ≠ 0 →
        F.P (F.lo a x) * F.P β * ((F.nfc g m : ℤ) • F.X m) =
          (F.nfc g m : ℤ) • (F.P (F.lo a x) * F.P (β + Pi.single m 1)) := by
      intro m hm
      have hxm : x < m := F.lt_of_w_lt (by have := hn m hm; omega)
      rw [mul_smul_comm, mul_assoc, F.P_mul_X]
      intro j hj
      by_contra h
      have := hkβ j h
      have := hn m hm
      exact absurd hj (not_lt.2 (F.lt_of_w_lt (by omega) : j < m).le)
    rw [Finset.sum_filter_of_ne (p := fun m => F.nfc g m ≠ 0) (fun m _ h0 hm => h0 (by simp [hm])),
      Finset.sum_filter_of_ne (p := fun m => F.nfc g m ≠ 0) (fun m _ h0 hm => h0 (by simp [hm]))]
      at this
    have e : ∑ m, F.P (F.lo a x) * F.P β * ((F.nfc g m : ℤ) • F.X m) =
        ∑ m, (F.nfc g m : ℤ) • (F.P (F.lo a x) * F.P (β + Pi.single m 1)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : F.nfc g m = 0
      · simp [hm]
      · exact e1 m hm
    rw [e]; exact this
  have := rel3_add hF hlin hrem
  rwa [← mul_add, add_sub_cancel, add_zero] at this

end Frame

end TaharaProof

end GroupDimension
