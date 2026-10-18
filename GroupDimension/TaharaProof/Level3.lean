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

omit IH hx in
/-- The commutation rule modulo weight `2p + q`. -/
theorem comm_sub_mem {g h : G} {p q : ℕ} (hg : E g ∈ F.Sp p (Set.Ioi x))
    (hh : E h ∈ F.Sp q (Set.Ioi x)) (hc : E (tc g h) ∈ F.Sp (p + q) (Set.Ioi x)) :
    E g * E h - (E h * E g + E (tc g h) + E h * E (tc g h)) ∈ F.Sp (2 * p + q) (Set.Ioi x) := by
  have e : E g * E h - (E h * E g + E (tc g h) + E h * E (tc g h)) =
      E g * E (tc g h) + E h * E g * E (tc g h) := by
    rw [E_comm]; abel
  rw [e]
  refine add_mem (F.Sp_mono (by omega) _ (F.mul_mem_Ioi hg hc)) ?_
  exact F.Sp_mono (by omega) _ (F.mul_mem_Ioi (F.mul_mem_Ioi hh hg) hc)

/-- Replacing a factor modulo `Sp K (Ioi x)` with `W(a_lo) + K ≥ 5`. -/
theorem rel3_of_sub {u u' : MonoidAlgebra ℤ G} {v : F.M3} {K : ℕ}
    (hu : (F.P (F.lo a x) * u', v) ∈ rel3 hF) (hd : u - u' ∈ F.Sp K (Set.Ioi x))
    (hK : 5 ≤ F.W (F.lo a x) + K) : (F.P (F.lo a x) * u, v) ∈ rel3 hF := by
  have := rel3_add hF hu (junk IH hx hd hK)
  rwa [← mul_add, add_sub_cancel, add_zero] at this

omit IH hx in
/-- `y = x^{o(x)}` lies in `γ_{w(x)+1}`. -/
theorem yy_mem : F.yy x ∈ lowerCentralSeries G (F.w x + 1 - 1) := by
  simpa [yy] using F.pow_mem x

omit IH hx in
theorem E_yy_mem : E (F.yy x) ∈ F.Sp (F.w x + 1) (Set.Ioi x) :=
  F.E_mem_Ioi (yy_mem (F := F)) (by omega)

/-- **TE1**: `a_hi = 0`. -/
theorem TE1 (hhi : hi a x = 0) (h3 : 3 ≤ F.W (F.lo a x) + (F.w x + 1))
    (h5 : 5 ≤ F.W (F.lo a x) + 2 * (F.w x + 1)) :
    (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x), F.nsum (F.yy x) (F.lo a x)) ∈ rel3 hF := by
  have hW0 : F.W 0 = 0 := by simp [W]
  have := first_order IH hx (β := 0) (by simp) (yy_mem (F := F) (x := x)) (by omega) (by simp)
    (by rw [hW0]; omega) (by rw [hW0]; omega)
  rw [hhi, P_zero, mul_one]
  rwa [P_zero, mul_one, add_zero] at this

omit IH hx in
theorem W_zero : F.W 0 = 0 := by simp [W]

omit IH hx in
theorem cc_mem (hwx : F.w x = 1) (k : ι) (hk : F.w k = 1) :
    F.cc x k ∈ lowerCentralSeries G 2 :=
  ExpThree.tc_mem (i := 1) (j := 0) (by norm_num) (by simpa [hwx] using yy_mem (F := F) (x := x))
    (by simpa [hk] using F.mem k)

/-- **TE2**: `a_hi = e_k` for a letter `k > x` of weight 1 (and `w x = 1`). -/
theorem TE2 (hwx : F.w x = 1) {k : ι} (hk : F.w k = 1) (hxk : x < k)
    (hhi : hi a x = cnt [k]) :
    (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x),
      F.nsum (F.yy x) (F.lo a x + cnt [k]) + F.nsum (F.cc x k) (F.lo a x) +
        F.nsum (F.cc x k) (F.lo a x + cnt [k])) ∈ rel3 hF := by
  have hk1 : ∀ j, cnt [k] j ≠ 0 → x < j := fun j hj => by
    rw [cnt_single] at hj
    by_cases h : j = k
    · exact h ▸ hxk
    · simp [Pi.single_eq_of_ne h] at hj
  have hkw : ∀ j, cnt [k] j ≠ 0 → F.w j < 2 := fun j hj => by
    rw [cnt_single] at hj
    by_cases h : j = k
    · subst h; omega
    · simp [Pi.single_eq_of_ne h] at hj
  have hWk : F.W (cnt [k]) = 1 := by rw [W_cnt]; simp [hk]
  have hPk : F.P (cnt [k]) = F.X k := by rw [cnt_single, F.P_single]
  have hc := cc_mem (F := F) (x := x) hwx k hk
  have hEy := E_yy_mem (F := F) (x := x)
  rw [hwx] at hEy
  have hXk : E (F.x k) ∈ F.Sp 1 (Set.Ioi x) := by
    rw [← X_eq_E, ← hk]; exact F.X_mem_Ioi hxk
  have hEc : E (F.cc x k) ∈ F.Sp 3 (Set.Ioi x) := F.E_mem_Ioi hc (by omega)
  have hD := comm_sub_mem (x := x) hEy hXk hEc
  rw [hhi, hPk, mul_assoc]
  refine rel3_of_sub IH hx ?_ hD (by omega)
  have t1 := first_order IH hx hk1 (yy_mem (F := F) (x := x)) (by omega) (by rw [hwx]; exact hkw)
    (by rw [hWk, hwx]; omega) (by rw [hWk, hwx]; omega)
  have t2 := first_order IH hx (β := 0) (by simp) (k := 3) hc (by omega) (by simp)
    (by rw [W_zero (F := F)]; omega) (by rw [W_zero (F := F)]; omega)
  have t3 := first_order IH hx hk1 (k := 3) hc (by omega) (fun j hj => by
    have := hkw j hj; omega) (by rw [hWk]; omega) (by rw [hWk]; omega)
  rw [hPk] at t1 t3
  rw [P_zero, mul_one, add_zero] at t2
  have := rel3_add hF (rel3_add hF t1 t2) t3
  convert this using 2
  simp only [cc, X_eq_E]; noncomm_ring

/-- **TE3**: `a_hi = e_j + e_k` for letters `x < j ≤ k` of weight 1 (and `w x = 1`). -/
theorem TE3 (hwx : F.w x = 1) {j k : ι} (hj : F.w j = 1) (hk : F.w k = 1) (hxj : x < j)
    (hjk : j ≤ k) (hhi : hi a x = cnt [j, k]) :
    (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x),
      F.nsum (F.yy x) (F.lo a x + cnt [j, k]) + F.nsum (F.cc x k) (F.lo a x + cnt [j]) +
        F.nsum (F.cc x j) (F.lo a x + cnt [k]) + F.nsum (tc (F.cc x j) (F.x k)) (F.lo a x)) ∈
      rel3 hF := by
  have hxk : x < k := lt_of_lt_of_le hxj hjk
  have hlet : ∀ (l : List ι), (∀ i ∈ l, x < i ∧ F.w i = 1) →
      (∀ i, cnt l i ≠ 0 → x < i) ∧ (∀ i, cnt l i ≠ 0 → F.w i < 2) := by
    intro l hl
    constructor <;> intro i hi <;> have hm : i ∈ l := List.count_pos_iff.mp (Nat.pos_of_ne_zero hi)
    · exact (hl i hm).1
    · have := (hl i hm).2; omega
  obtain ⟨hjk1, hjk2⟩ := hlet [j, k] (by simp [hxj, hxk, hj, hk])
  obtain ⟨hj1, hj2⟩ := hlet [j] (by simp [hxj, hj])
  obtain ⟨hk1, hk2⟩ := hlet [k] (by simp [hxk, hk])
  have hWjk : F.W (cnt [j, k]) = 2 := by rw [W_cnt]; simp [hj, hk]
  have hWj : F.W (cnt [j]) = 1 := by rw [W_cnt]; simp [hj]
  have hWk : F.W (cnt [k]) = 1 := by rw [W_cnt]; simp [hk]
  have hPjk : F.P (cnt [j, k]) = F.X j * F.X k := by
    rw [F.P_cnt (by simp [hjk])]; simp
  have hPj : F.P (cnt [j]) = F.X j := by rw [cnt_single, F.P_single]
  have hPk : F.P (cnt [k]) = F.X k := by rw [cnt_single, F.P_single]
  have hcj := cc_mem (F := F) (x := x) hwx j hj
  have hck := cc_mem (F := F) (x := x) hwx k hk
  have hc' : tc (F.cc x j) (F.x k) ∈ lowerCentralSeries G 3 :=
    ExpThree.tc_mem (i := 2) (j := 0) (by norm_num) hcj (by simpa [hk] using F.mem k)
  have hEy := E_yy_mem (F := F) (x := x)
  rw [hwx] at hEy
  have hXj : E (F.x j) ∈ F.Sp 1 (Set.Ioi x) := by rw [← X_eq_E, ← hj]; exact F.X_mem_Ioi hxj
  have hXk : E (F.x k) ∈ F.Sp 1 (Set.Ioi x) := by rw [← X_eq_E, ← hk]; exact F.X_mem_Ioi hxk
  have hEcj : E (F.cc x j) ∈ F.Sp 3 (Set.Ioi x) := F.E_mem_Ioi hcj (by omega)
  have hEck : E (F.cc x k) ∈ F.Sp 3 (Set.Ioi x) := F.E_mem_Ioi hck (by omega)
  have hEc' : E (tc (F.cc x j) (F.x k)) ∈ F.Sp 4 (Set.Ioi x) := F.E_mem_Ioi hc' (by omega)
  have hD1 := comm_sub_mem (x := x) hEy hXj hEcj
  have hD2 := comm_sub_mem (x := x) hEy hXk hEck
  have hD3 := comm_sub_mem (x := x) hEcj hXk hEc'
  have hJ : E (F.yy x) * (E (F.x j) * E (F.x k)) - (E (F.x j) * E (F.x k) * E (F.yy x) +
      E (F.x j) * E (F.cc x k) + E (F.x k) * E (F.cc x j) + E (tc (F.cc x j) (F.x k))) ∈
      F.Sp 5 (Set.Ioi x) := by
    have key : E (F.yy x) * (E (F.x j) * E (F.x k)) - (E (F.x j) * E (F.x k) * E (F.yy x) +
        E (F.x j) * E (F.cc x k) + E (F.x k) * E (F.cc x j) + E (tc (F.cc x j) (F.x k))) =
        E (F.x j) * E (F.x k) * E (F.cc x k) +
        E (F.x j) * (E (F.yy x) * E (F.x k) - (E (F.x k) * E (F.yy x) + E (F.cc x k) +
          E (F.x k) * E (F.cc x k))) +
        E (F.x k) * E (tc (F.cc x j) (F.x k)) +
        (E (F.cc x j) * E (F.x k) - (E (F.x k) * E (F.cc x j) + E (tc (F.cc x j) (F.x k)) +
          E (F.x k) * E (tc (F.cc x j) (F.x k)))) +
        E (F.x j) * E (F.cc x j) * E (F.x k) +
        (E (F.yy x) * E (F.x j) - (E (F.x j) * E (F.yy x) + E (F.cc x j) +
          E (F.x j) * E (F.cc x j))) * E (F.x k) := by
      noncomm_ring
    rw [key]
    refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · exact F.Sp_mono (by omega) _ (F.mul_mem_Ioi (F.mul_mem_Ioi hXj hXk) hEck)
    · exact F.Sp_mono (by omega) _ (F.mul_mem_Ioi hXj hD2)
    · exact F.Sp_mono (by omega) _ (F.mul_mem_Ioi hXk hEc')
    · exact F.Sp_mono (by omega) _ hD3
    · exact F.Sp_mono (by omega) _ (F.mul_mem_Ioi (F.mul_mem_Ioi hXj hEcj) hXk)
    · exact F.Sp_mono (by omega) _ (F.mul_mem_Ioi hD1 hXk)
  rw [hhi, hPjk, mul_assoc]
  refine rel3_of_sub IH hx ?_ hJ (by omega)
  have t1 := first_order IH hx hjk1 (yy_mem (F := F) (x := x)) (by omega) (by rw [hwx]; exact hjk2)
    (by rw [hWjk, hwx]; omega) (by rw [hWjk, hwx]; omega)
  have t2 := first_order IH hx hj1 (k := 3) hck (by omega) (fun i hi => by
    have := hj2 i hi; omega) (by rw [hWj]; omega) (by rw [hWj]; omega)
  have t3 := first_order IH hx hk1 (k := 3) hcj (by omega) (fun i hi => by
    have := hk2 i hi; omega) (by rw [hWk]; omega) (by rw [hWk]; omega)
  have t4 := first_order IH hx (β := 0) (by simp) (k := 4) hc' (by omega) (by simp)
    (by rw [W_zero (F := F)]; omega) (by rw [W_zero (F := F)]; omega)
  rw [hPjk] at t1
  rw [hPj] at t2
  rw [hPk] at t3
  rw [P_zero, mul_one, add_zero] at t4
  have := rel3_add hF (rel3_add hF (rel3_add hF t1 t2) t3) t4
  convert this using 2
  simp only [cc, X_eq_E]; noncomm_ring

/-- **TE4**: `a_hi = e_k` for a letter `k > x` of weight 2 (and `w x = 1`). -/
theorem TE4 (hwx : F.w x = 1) {k : ι} (hk : F.w k = 2) (hxk : x < k)
    (hhi : hi a x = cnt [k]) :
    (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x),
      F.nsum (F.yy x) (F.lo a x + cnt [k]) + ∑ m, (F.nfc (F.yy x) m : ℤ) •
        (if k < m then F.nsum (tc (F.x m) (F.x k)) (F.lo a x) else 0)) ∈ rel3 hF := by
  classical
  have hPk : F.P (cnt [k]) = F.X k := by rw [cnt_single, F.P_single]
  have hXk : F.X k ∈ F.Sp 2 (Set.Ioi x) := by rw [← hk]; exact F.X_mem_Ioi hxk
  obtain ⟨-, h2⟩ := F.of_nprod_sub_one (F.nfc (F.yy x))
  rw [F.nprod_nfc] at h2
  have hn : ∀ m, F.nfc (F.yy x) m ≠ 0 → 2 ≤ F.w m := fun m hm => by
    have := F.nf_weight (yy_mem (F := F) (x := x)) (F.nfc_lt _) (F.nprod_nfc _) hm; omega
  have hnx : ∀ m, F.nfc (F.yy x) m ≠ 0 → x < m := fun m hm =>
    F.lt_of_w_lt (by have := hn m hm; omega)
  -- the remainder of `y - 1` is negligible
  have hRem : E (F.yy x) - ∑ m, (F.nfc (F.yy x) m : ℤ) • F.X m ∈ F.Sp 4 (Set.Ioi x) := by
    refine Submodule.span_le.mpr ?_ h2
    rintro _ ⟨γ, hγ, hγ2, rfl⟩
    have hγn : ∀ j, γ j ≠ 0 → F.nfc (F.yy x) j ≠ 0 := fun j hj h0 => hj (by
      have : γ j ≤ F.nfc (F.yy x) j := hγ j; omega)
    refine F.P_mem_Sp ?_ fun j hj => hnx j (hγn j hj)
    calc 4 = 2 * 2 := rfl
      _ ≤ (∑ j, γ j) * 2 := Nat.mul_le_mul_right _ hγ2
      _ = ∑ j, γ j * 2 := Finset.sum_mul _ _ _
      _ ≤ ∑ j, γ j * F.w j := Finset.sum_le_sum fun j _ => by
          by_cases h : γ j = 0
          · simp [h]
          · exact Nat.mul_le_mul_left _ (hn j (hγn j h))
  -- each letter of `y`
  have hm : ∀ m, F.nfc (F.yy x) m ≠ 0 →
      (F.P (F.lo a x) * (F.X m * F.X k), F.Φ3 (F.lo a x + cnt [k] + Pi.single m 1) +
        (if k < m then F.nsum (tc (F.x m) (F.x k)) (F.lo a x) else 0)) ∈ rel3 hF := by
    intro m hm0
    have hwm := hn m hm0
    have hxm := hnx m hm0
    have hsortW : 3 ≤ F.W (F.lo a x + (Pi.single m 1 + Pi.single k 1)) := by
      rw [W_add, W_add, W_single, W_single]; omega
    have hlet : ∀ j, (Pi.single m 1 + Pi.single k 1 : ι → ℕ) j ≠ 0 → x < j := by
      intro j hj
      by_cases h1 : j = m
      · exact h1 ▸ hxm
      · by_cases h2 : j = k
        · exact h2 ▸ hxk
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2] at hj
    have hval : F.lo a x + cnt [k] + Pi.single m 1 = F.lo a x + (Pi.single m 1 + Pi.single k 1) := by
      rw [cnt_single]; abel
    rw [hval]
    rcases le_or_gt m k with hmk | hkm
    · rw [if_neg (not_lt.2 hmk), add_zero]
      have := sorted IH hx hlet hsortW
      have hP : F.P (Pi.single m 1 + Pi.single k 1) = F.X m * F.X k := by
        rw [← cnt_single, ← cnt_single, ← cnt_append, F.P_cnt (by simp [hmk])]
        simp
      rwa [hP] at this
    · rw [if_pos hkm]
      set c := tc (F.x m) (F.x k)
      have hc : c ∈ lowerCentralSeries G (F.w m + 2 - 1) :=
        ExpThree.tc_mem (i := F.w m - 1) (j := 1) (by omega) (F.mem m) (by simpa [hk] using F.mem k)
      have hXm : E (F.x m) ∈ F.Sp (F.w m) (Set.Ioi x) := by rw [← X_eq_E]; exact F.X_mem_Ioi hxm
      have hEc : E c ∈ F.Sp (F.w m + 2) (Set.Ioi x) := F.E_mem_Ioi hc (by omega)
      have hD := comm_sub_mem (x := x) hXm (show E (F.x k) ∈ F.Sp 2 (Set.Ioi x) from hXk) hEc
      have hD' : F.X m * F.X k - (F.X k * F.X m + E c) ∈ F.Sp 5 (Set.Ioi x) := by
        have e : F.X m * F.X k - (F.X k * F.X m + E c) =
            (E (F.x m) * E (F.x k) - (E (F.x k) * E (F.x m) + E c + E (F.x k) * E c)) +
              E (F.x k) * E c := by
          simp only [X_eq_E]; abel
        rw [e]
        exact add_mem (F.Sp_mono (by omega) _ hD)
          (F.Sp_mono (by omega) _ (F.mul_mem_Ioi (show E (F.x k) ∈ F.Sp 2 (Set.Ioi x) from hXk) hEc))
      refine rel3_of_sub IH hx ?_ hD' (by omega)
      have t1 := sorted IH hx hlet hsortW
      have hPkm : F.P (Pi.single m 1 + Pi.single k 1) = F.X k * F.X m := by
        rw [add_comm, ← cnt_single, ← cnt_single, ← cnt_append, F.P_cnt (by simp [hkm.le])]
        simp
      rw [hPkm] at t1
      have t2 := first_order IH hx (β := 0) (by simp) hc (by omega) (by simp)
        (by rw [W_zero (F := F)]; omega) (by rw [W_zero (F := F)]; omega)
      rw [P_zero, mul_one, add_zero] at t2
      have := rel3_add hF t1 t2
      rwa [← mul_add] at this
  have key : ∀ m ∈ Finset.univ.filter fun m => F.nfc (F.yy x) m ≠ 0,
      (F.P (F.lo a x) * (F.X m * F.X k), F.Φ3 (F.lo a x + cnt [k] + Pi.single m 1) +
        (if k < m then F.nsum (tc (F.x m) (F.x k)) (F.lo a x) else 0)) ∈ rel3 hF :=
    fun m hm' => hm m (Finset.mem_filter.mp hm').2
  have hsum := rel3_sum hF _ (fun m => (F.nfc (F.yy x) m : ℤ)) _ _ key
  rw [Finset.sum_filter_of_ne (p := fun m => F.nfc (F.yy x) m ≠ 0)
      (fun m _ h0 hm => h0 (by simp [hm])),
    Finset.sum_filter_of_ne (p := fun m => F.nfc (F.yy x) m ≠ 0)
      (fun m _ h0 hm => h0 (by simp [hm]))] at hsum
  have hjunk := junk IH hx (F.mul_mem_Ioi hRem hXk) (by omega)
  have := rel3_add hF hsum hjunk
  rw [hhi, hPk]
  convert this using 2
  · have e1 : ∑ m, (F.nfc (F.yy x) m : ℤ) • (F.P (F.lo a x) * (F.X m * F.X k)) =
        F.P (F.lo a x) * ((∑ m, (F.nfc (F.yy x) m : ℤ) • F.X m) * F.X k) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_mul_assoc, mul_smul_comm]
    rw [e1, ← mul_add, ← add_mul, add_sub_cancel, mul_assoc]
  · rw [add_zero, nsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_add]

end Frame

end TaharaProof

end GroupDimension
