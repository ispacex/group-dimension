import GroupDimension.Jennings.Series

/-!
# Frames of a restricted N-series and the weight filtration of `𝔽_p[G]`

Stage 1 of Jennings' theorem: the analogue of `TaharaProof/Words.lean` (and of the first part
of `TaharaProof/Level1.lean`) over `𝔽_p = ZMod p` for an abstract restricted N-series `S`.

**Frames.** A *frame* of `S` (`JFrame T ι`): letters `x j` indexed by a finite linear order `ι`,
weights `w j ≥ 1` increasing in `j`, `x j ∈ S (w j)`, and the normal form: every `g ∈ G` is
uniquely `∏_j x_j^{b_j}` (ordered product) with `0 ≤ b_j < p`, and such a product lies in `S k`
(`k ≥ 1`) exactly when `b_j = 0` for all letters of weight `< k`. All "orders" are `p`: the
layers `S k / S (k+1)` are elementary abelian.

**Products.** For `a : ι → ℕ`, `P a = ∏_j (x_j - 1)^{a_j}` (ordered product in `𝔽_p[G]`) and
`W a = ∑_j a_j w_j` its weight. `Sp k U` is the `𝔽_p`-span of the `P a` with `W a ≥ k` and all
letters of `a` in `U`; `Bsp k` the span of the *basic* ones (`a_j < p`) with `W a ≥ k`.

**Main results of the file.**
* `of_nprod_sub_one` (to first order): for `g = ∏ x_j^{b_j}`, `g - 1 - ∑ b_j (x_j - 1)` is a
  combination of `P β` with `β ≤ b`, `|β| ≥ 2`.
* `Sp_mul_X` (sorting): `Sp k U · (x_j - 1) ⊆ Sp (k + w_j) U` for an upper set `U ∋ j`; the weight
  of a commutator is controlled by `[S a, S b] ≤ S (a + b)`.
* `Bsp_zero`: the basic products span `𝔽_p[G]`.
* `augIdealP_pow_le_Sp`: `Δ^n ⊆ Sp n univ`.
-/

namespace GroupDimension

namespace Jennings

open MonoidAlgebra TaharaProof

variable {p : ℕ} {G : Type*} [Group G]

/-- A frame of a restricted N-series: letters with weights, and normal forms with exponents
`< p` adapted to the series. -/
structure JFrame (T : RestrictedSeries p G) (ι : Type*) [LinearOrder ι] [Fintype ι] where
  x : ι → G
  w : ι → ℕ
  w_pos : ∀ j, 1 ≤ w j
  w_mono : Monotone w
  mem : ∀ j, x j ∈ T.S (w j)
  nf : ∀ g : G, ∃ b : ι → ℕ, (∀ j, b j < p) ∧ lprod (ordL ι) x b = g
  nf_unique : ∀ b c : ι → ℕ, (∀ j, b j < p) → (∀ j, c j < p) →
    lprod (ordL ι) x b = lprod (ordL ι) x c → b = c
  wt : ∀ b : ι → ℕ, (∀ j, b j < p) → ∀ k, 1 ≤ k →
    (lprod (ordL ι) x b ∈ T.S k ↔ ∀ j, w j < k → b j = 0)

variable {T : RestrictedSeries p G} {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace JFrame

variable (F : JFrame T ι)

/-- The group element `∏ x_j^{b_j}`. -/
noncomputable def nprod (b : ι → ℕ) : G := lprod (ordL ι) F.x b

/-- `x_j - 1 ∈ 𝔽_p[G]`. -/
noncomputable def X (j : ι) : MonoidAlgebra (ZMod p) G := of (ZMod p) G (F.x j) - 1

/-- The product `P(a) = ∏_j (x_j - 1)^{a_j}` (ordered). -/
noncomputable def P (a : ι → ℕ) : MonoidAlgebra (ZMod p) G := lprod (ordL ι) F.X a

/-- The weight `W(a) = ∑ a_j w_j`. -/
def W (a : ι → ℕ) : ℕ := ∑ j, a j * F.w j

/-- `Sp k U`: the span of the products of weight `≥ k` with letters in `U`. -/
noncomputable def Sp (k : ℕ) (U : Set ι) : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Submodule.span (ZMod p) {z | ∃ a : ι → ℕ, k ≤ F.W a ∧ (∀ j, a j ≠ 0 → j ∈ U) ∧ z = F.P a}

/-- `Bsp k`: the span of the basic products (`a_j < p`) of weight `≥ k`. -/
noncomputable def Bsp (k : ℕ) : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Submodule.span (ZMod p) {z | ∃ a : ι → ℕ, (∀ j, a j < p) ∧ k ≤ F.W a ∧ z = F.P a}

/-- The span of `P β` for `β ≤ b` with `|β| ≥ n`. -/
noncomputable def low (b : ι → ℕ) (n : ℕ) : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G) :=
  Submodule.span (ZMod p) {z | ∃ β : ι → ℕ, β ≤ b ∧ n ≤ ∑ j, β j ∧ z = F.P β}

theorem W_add (a b : ι → ℕ) : F.W (a + b) = F.W a + F.W b := by
  simp [W, add_mul, Finset.sum_add_distrib]

theorem W_single (j : ι) : F.W (Pi.single j 1) = F.w j := by
  classical
  simp only [W]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

theorem W_nsmul_single (m : ℕ) (j : ι) : F.W (m • Pi.single j 1) = m * F.w j := by
  classical
  simp only [W]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

theorem P_mul_X {a : ι → ℕ} {y : ι} (ha : ∀ j, y < j → a j = 0) :
    F.P a * F.X y = F.P (a + (Pi.single y 1 : ι → ℕ)) :=
  lprod_mul_single ordL_pairwise (mem_ordL y) F.X ha

theorem P_zero : F.P 0 = 1 := lprod_zero _ _

theorem P_single (j : ι) : F.P (Pi.single j 1) = F.X j := by
  rw [← zero_add (Pi.single j 1 : ι → ℕ), ← F.P_mul_X (by simp), P_zero, one_mul]

theorem P_eq_mul_last {a : ι → ℕ} {y : ι} (hy : a y ≠ 0) (ha : ∀ j, y < j → a j = 0) :
    F.P a = F.P (a - (Pi.single y 1 : ι → ℕ)) * F.X y :=
  lprod_eq_mul_last F.X hy ha

theorem P_mul_P {a b : ι → ℕ} (hab : ∀ i j, a i ≠ 0 → b j ≠ 0 → i < j) :
    F.P a * F.P b = F.P (a + b) :=
  lprod_mul_lprod F.X _ b rfl hab

theorem nprod_eq_mul_last {a : ι → ℕ} {y : ι} (hy : a y ≠ 0) (ha : ∀ j, y < j → a j = 0) :
    F.nprod a = F.nprod (a - (Pi.single y 1 : ι → ℕ)) * F.x y :=
  lprod_eq_mul_last F.x hy ha

theorem lt_of_w_lt {i j : ι} (h : F.w i < F.w j) : i < j :=
  lt_of_not_ge fun h' => absurd (F.w_mono h') (not_le.2 h)

theorem Sp_mono {k k' : ℕ} (h : k ≤ k') (U : Set ι) : F.Sp k' U ≤ F.Sp k U :=
  Submodule.span_mono fun _ ⟨a, ha, hU, e⟩ => ⟨a, h.trans ha, hU, e⟩

theorem Bsp_mono {k k' : ℕ} (h : k ≤ k') : F.Bsp k' ≤ F.Bsp k :=
  Submodule.span_mono fun _ ⟨a, hp, ha, e⟩ => ⟨a, hp, h.trans ha, e⟩

theorem Bsp_le_Sp (k : ℕ) : F.Bsp k ≤ F.Sp k Set.univ :=
  Submodule.span_mono fun _ ⟨a, _, ha, e⟩ => ⟨a, ha, fun _ _ => Set.mem_univ _, e⟩

theorem P_mem_Sp {a : ι → ℕ} {k : ℕ} {U : Set ι} (hk : k ≤ F.W a) (hU : ∀ j, a j ≠ 0 → j ∈ U) :
    F.P a ∈ F.Sp k U :=
  Submodule.subset_span ⟨a, hk, hU, rfl⟩

theorem P_mem_Bsp {a : ι → ℕ} {k : ℕ} (hp : ∀ j, a j < p) (hk : k ≤ F.W a) : F.P a ∈ F.Bsp k :=
  Submodule.subset_span ⟨a, hp, hk, rfl⟩

theorem le_W (a : ι → ℕ) (j : ι) : a j * F.w j ≤ F.W a :=
  Finset.single_le_sum (f := fun j => a j * F.w j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-! ## The normal form to first order -/

theorem low_mono {b b' : ι → ℕ} (h : b ≤ b') {n n' : ℕ} (hn : n' ≤ n) :
    F.low b n ≤ F.low b' n' :=
  Submodule.span_mono fun _ ⟨β, hβ, hβn, e⟩ => ⟨β, hβ.trans h, hn.trans hβn, e⟩

/-- `low b n · (x_y - 1) ⊆ low (b + e_y) (n + 1)` when `b` vanishes above `y`. -/
theorem low_mul_X {b : ι → ℕ} {y : ι} (hb : ∀ j, y < j → b j = 0) {n : ℕ}
    {z : MonoidAlgebra (ZMod p) G}
    (hz : z ∈ F.low b n) : z * F.X y ∈ F.low (b + (Pi.single y 1 : ι → ℕ)) (n + 1) := by
  classical
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  | mem x hx =>
  obtain ⟨β, hβ, hβn, rfl⟩ := hx
  rw [F.P_mul_X (fun j hj => by have h' : β j ≤ b j := hβ j; rw [hb j hj] at h'; omega)]
  refine Submodule.subset_span ⟨β + (Pi.single y 1 : ι → ℕ), add_le_add hβ le_rfl, ?_, rfl⟩
  rw [sum_add_single]; omega

/-- The normal form to first order: `∏ x_j^{b_j} - 1 ∈ low b 1`, and
`∏ x_j^{b_j} - 1 - ∑ b_j (x_j - 1) ∈ low b 2`. -/
theorem of_nprod_sub_one (b : ι → ℕ) :
    of (ZMod p) G (F.nprod b) - 1 ∈ F.low b 1 ∧
      of (ZMod p) G (F.nprod b) - 1 - ∑ j, (b j : ZMod p) • F.X j ∈ F.low b 2 := by
  classical
  induction h : ∑ j, b j generalizing b with
  | zero =>
    have : b = 0 := funext fun j => by
      have := (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_univ j); simpa using this
    subst this
    have h0 : F.nprod 0 = 1 := lprod_zero _ _
    simp only [h0, map_one, sub_self, Pi.zero_apply, Nat.cast_zero, zero_smul,
      Finset.sum_const_zero]
    exact ⟨zero_mem _, zero_mem _⟩
  | succ n ih =>
    have hb0 : b ≠ 0 := by rintro rfl; simp at h
    obtain ⟨y, hy, hyl⟩ := exists_last hb0
    set b' := b - (Pi.single y 1 : ι → ℕ) with hb'
    have hbb : b = b' + Pi.single y 1 := by
      funext j; by_cases hj : j = y
      · subst hj; simp [hb']; omega
      · simp [hb', Pi.single_eq_of_ne hj]
    have hsum : ∑ j, b' j = n := by
      have : ∑ j, b j = ∑ j, b' j + 1 := by rw [hbb, sum_add_single]
      omega
    obtain ⟨ih1, ih2⟩ := ih b' hsum
    have hb'l : ∀ j, y < j → b' j = 0 := fun j hj => by simp [hb', hyl j hj]
    have hle : b' ≤ b := by rw [hbb]; exact le_add_of_nonneg_right (by positivity)
    have e : of (ZMod p) G (F.nprod b) = of (ZMod p) G (F.nprod b') * (1 + F.X y) := by
      rw [F.nprod_eq_mul_last hy hyl, ← hb', _root_.map_mul, X, add_sub_cancel]
    have hX : F.X y ∈ F.low b 1 := by
      rw [← F.P_single]
      refine Submodule.subset_span ⟨(Pi.single y 1 : ι → ℕ), ?_, by simp, rfl⟩
      rw [hbb]; exact le_add_of_nonneg_left (zero_le _)
    have h1 := F.low_mul_X hb'l ih1
    rw [← hbb] at h1
    constructor
    · have : of (ZMod p) G (F.nprod b) - 1 =
          (of (ZMod p) G (F.nprod b') - 1) + (of (ZMod p) G (F.nprod b') - 1) * F.X y + F.X y := by
        rw [e]; noncomm_ring
      rw [this]
      exact add_mem (add_mem (F.low_mono hle le_rfl ih1) (F.low_mono le_rfl (by omega) h1)) hX
    · have hs : ∑ j, (b j : ZMod p) • F.X j = ∑ j, (b' j : ZMod p) • F.X j + F.X y := by
        conv_lhs => rw [hbb]
        simp only [Pi.add_apply, Nat.cast_add, add_smul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single y]
        · simp
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
      have : of (ZMod p) G (F.nprod b) - 1 - ∑ j, (b j : ZMod p) • F.X j =
          (of (ZMod p) G (F.nprod b') - 1 - ∑ j, (b' j : ZMod p) • F.X j) +
            (of (ZMod p) G (F.nprod b') - 1) * F.X y := by
        rw [e, hs]; noncomm_ring
      rw [this]
      exact add_mem (F.low_mono hle le_rfl ih2) h1

/-- The normal form of an element of `S k` has no letters of weight `< k`. -/
theorem nf_weight {g : G} {k : ℕ} (hk : 1 ≤ k) (hg : g ∈ T.S k) {b : ι → ℕ}
    (hb : ∀ j, b j < p) (hbg : F.nprod b = g) {j : ι} (hj : b j ≠ 0) : k ≤ F.w j := by
  by_contra h
  have hm : lprod (ordL ι) F.x b ∈ T.S k := by
    rw [show lprod (ordL ι) F.x b = g from hbg]; exact hg
  exact hj ((F.wt b hb k hk).mp hm j (by omega))

/-- For `g ∈ S k`, `g - 1` is a combination of products of weight `≥ k` whose letters have
weight `≥ k`. -/
theorem of_sub_one_mem {g : G} {k : ℕ} (hk : 1 ≤ k) (hg : g ∈ T.S k) (U : Set ι)
    (hU : ∀ j, k ≤ F.w j → j ∈ U) :
    of (ZMod p) G g - 1 ∈ F.Sp k U := by
  obtain ⟨b, hb, rfl⟩ := F.nf g
  refine Submodule.span_le.mpr ?_ (F.of_nprod_sub_one b).1
  rintro _ ⟨β, hβ, hβn, rfl⟩
  have hl : ∀ j, β j ≠ 0 → k ≤ F.w j := fun j hj =>
    F.nf_weight hk hg hb rfl (fun h => hj (Nat.eq_zero_of_le_zero (h ▸ hβ j)))
  refine Submodule.subset_span ⟨β, ?_, fun j hj => hU j (hl j hj), rfl⟩
  obtain ⟨j0, hj0⟩ : ∃ j, β j ≠ 0 := by
    by_contra h; push Not at h; simp [h] at hβn
  calc k ≤ F.w j0 := hl j0 hj0
    _ ≤ β j0 * F.w j0 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj0)
    _ ≤ F.W β := F.le_W β j0

/-! ## The basic products span -/

/-- The basic products span `𝔽_p[G]`. -/
theorem Bsp_zero : F.Bsp 0 = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  refine mem_of_forall_of (fun g => ?_) z
  obtain ⟨b, hb, rfl⟩ := F.nf g
  have h1 := (F.of_nprod_sub_one b).1
  have : of (ZMod p) G (F.nprod b) = (of (ZMod p) G (F.nprod b) - 1) + F.P 0 := by
    rw [P_zero]; abel
  change of (ZMod p) G (F.nprod b) ∈ _
  rw [this]
  refine add_mem (Submodule.span_le.mpr ?_ h1) (F.P_mem_Bsp ?_ (Nat.zero_le _))
  · rintro _ ⟨β, hβ, -, rfl⟩
    exact F.P_mem_Bsp (fun j => lt_of_le_of_lt (hβ j) (hb j)) (Nat.zero_le _)
  · intro j; exact lt_of_le_of_lt (zero_le _) (hb j)

theorem Sp_zero_eq_top : F.Sp 0 Set.univ = ⊤ :=
  eq_top_iff.mpr (F.Bsp_zero ▸ F.Bsp_le_Sp 0)

/-! ## Sorting -/

/-- The commutation rule `(y-1)(x-1) = (x-1)(y-1) + (c-1)(1 + (x-1) + (y-1) + (x-1)(y-1))`
with `c = tc y x`, written with `xy (c - 1) = yx - xy`. -/
theorem X_comm (i j : ι) :
    F.X j * F.X i = F.X i * F.X j + (of (ZMod p) G (Tahara.tc (F.x j) (F.x i)) - 1) +
      F.X i * (of (ZMod p) G (Tahara.tc (F.x j) (F.x i)) - 1) +
      F.X j * (of (ZMod p) G (Tahara.tc (F.x j) (F.x i)) - 1) +
      F.X i * F.X j * (of (ZMod p) G (Tahara.tc (F.x j) (F.x i)) - 1) := by
  have h : of (ZMod p) G (F.x j) * of (ZMod p) G (F.x i) =
      of (ZMod p) G (F.x i) * of (ZMod p) G (F.x j) *
        of (ZMod p) G (Tahara.tc (F.x j) (F.x i)) := by
    rw [← _root_.map_mul, ← _root_.map_mul, ← _root_.map_mul]; congr 1; simp only [Tahara.tc]
    group
  simp only [X]
  rw [← sub_eq_zero]
  have e : ∀ a b c : MonoidAlgebra (ZMod p) G,
      (b - 1) * (a - 1) - ((a - 1) * (b - 1) + (c - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1) +
        (a - 1) * (b - 1) * (c - 1)) = b * a - a * b * c := by
    intro a b c; noncomm_ring
  rw [e, h, sub_self]

/-- Multiplying `Sp k U` on the right by a word of letters, each satisfying the sorting claim. -/
theorem Sp_mul_word {U : Set ι} (Q : ι → Prop)
    (hQ : ∀ i, Q i → ∀ k, ∀ z ∈ F.Sp k U, z * F.X i ∈ F.Sp (k + F.w i) U) :
    ∀ (l : List ι), (∀ i ∈ l, Q i) → ∀ k, ∀ z ∈ F.Sp k U,
      z * (l.map F.X).prod ∈ F.Sp (k + (l.map F.w).sum) U := by
  intro l
  induction l with
  | nil => intro _ k z hz; simpa using hz
  | cons i l ih =>
    intro hl k z hz
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [← mul_assoc, ← add_assoc]
    exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ _
      (hQ i (hl i List.mem_cons_self) k z hz)

theorem P_eq_word (a : ι → ℕ) : F.P a = ((Frame.word a).map F.X).prod := by
  simp only [P, lprod, Frame.word, List.map_flatMap, prod_flatMap', List.map_replicate,
    List.prod_replicate]

theorem W_eq_word (a : ι → ℕ) : F.W a = ((Frame.word a).map F.w).sum := by
  simp only [W, Frame.word, List.map_flatMap, sum_flatMap', List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  rw [Frame.sum_ordL]

/-- Multiplying by an element of `Sp r V` for letters in `V` satisfying the sorting claim. -/
theorem Sp_mul_Sp {U V : Set ι}
    (hQ : ∀ i ∈ V, ∀ k, ∀ z ∈ F.Sp k U, z * F.X i ∈ F.Sp (k + F.w i) U)
    {k r : ℕ} {z v : MonoidAlgebra (ZMod p) G} (hz : z ∈ F.Sp k U) (hv : v ∈ F.Sp r V) :
    z * v ∈ F.Sp (k + r) U := by
  induction hv using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  | mem x hx =>
  obtain ⟨a, ha, hV, rfl⟩ := hx
  rw [F.P_eq_word]
  refine F.Sp_mono (by rw [← F.W_eq_word]; omega) U
    (F.Sp_mul_word (· ∈ V) hQ _ (fun i hi => hV i (Frame.mem_word hi)) k z hz)

/-- **Sorting** (Losey, Tahara, Jennings): `Sp k U · (x_j - 1) ⊆ Sp (k + w_j) U` for an upper set
`U` containing `j`. -/
theorem Sp_mul_X {U : Set ι} (hU : IsUpperSet U) :
    ∀ j ∈ U, ∀ k, ∀ z ∈ F.Sp k U, z * F.X j ∈ F.Sp (k + F.w j) U := by
  classical
  intro j
  induction j using WellFoundedGT.induction with
  | _ j IH =>
  intro hjU
  -- multiplying by `c - 1` for `c` of weight `> w j`
  have hc : ∀ (c : G) (r : ℕ), F.w j < r → c ∈ T.S r →
      ∀ k, ∀ z ∈ F.Sp k U, z * (of (ZMod p) G c - 1) ∈ F.Sp (k + r) U := by
    intro c r hr hcr k z hz
    have hcm : of (ZMod p) G c - 1 ∈ F.Sp r {i | j < i} :=
      F.of_sub_one_mem (by have := F.w_pos j; omega) hcr _ fun i hi => F.lt_of_w_lt (by omega)
    refine F.Sp_mul_Sp (V := {i | j < i}) (fun i hi k z hz => IH i hi (hU hi.le hjU) k z hz) hz hcm
  -- the claim for products, by induction on their length
  have hP : ∀ (n : ℕ) (a : ι → ℕ), ∑ i, a i = n → (∀ i, a i ≠ 0 → i ∈ U) →
      F.P a * F.X j ∈ F.Sp (F.W a + F.w j) U := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    intro a hn haU
    by_cases hlast : ∀ i, j < i → a i = 0
    · rw [F.P_mul_X hlast]
      refine F.P_mem_Sp (by rw [W_add, W_single]) fun i hi => ?_
      by_cases h : i = j
      · exact h ▸ hjU
      · exact haU i (by simpa [Pi.single_eq_of_ne h] using hi)
    push Not at hlast
    have ha0 : a ≠ 0 := by
      obtain ⟨i, -, hi⟩ := hlast; intro h; exact hi (by simp [h])
    obtain ⟨y, hy, hyl⟩ := exists_last ha0
    have hjy : j < y := by
      obtain ⟨i, hi, hai⟩ := hlast
      by_contra h; push Not at h
      exact hai (hyl i (lt_of_le_of_lt h hi))
    set a' := a - (Pi.single y 1 : ι → ℕ) with ha'
    have haa : a = a' + Pi.single y 1 := by
      funext i; by_cases hi : i = y
      · subst hi; simp [ha']; omega
      · simp [ha', Pi.single_eq_of_ne hi]
    have hn' : ∑ i, a' i < n := by
      have : ∑ i, a i = ∑ i, a' i + 1 := by rw [haa, sum_add_single]
      omega
    have ha'U : ∀ i, a' i ≠ 0 → i ∈ U := fun i hi => haU i (by
      intro h; apply hi; simp [ha', h])
    have hyU : y ∈ U := haU y hy
    have hWa : F.W a = F.W a' + F.w y := by rw [haa, W_add, W_single]
    set c := Tahara.tc (F.x y) (F.x j)
    have hcm : c ∈ T.S (F.w y + F.w j) := T.tc_mem (F.w_pos y) (F.w_pos j) (F.mem y) (F.mem j)
    have hwj := F.w_pos y
    have h1 : F.P a' * F.X j ∈ F.Sp (F.W a' + F.w j) U := ihn _ hn' a' rfl ha'U
    have h2 : F.P a' * F.X j * F.X y ∈ F.Sp (F.W a' + F.w j + F.w y) U :=
      IH y hjy hyU _ _ h1
    have hPa' : F.P a' ∈ F.Sp (F.W a') U := F.P_mem_Sp le_rfl ha'U
    have hPa : F.P a ∈ F.Sp (F.W a) U := F.P_mem_Sp le_rfl haU
    have h3 := hc c _ (by omega) hcm _ _ hPa'
    have h4 := hc c _ (by omega) hcm _ _ h1
    have h5 := hc c _ (by omega) hcm _ _ hPa
    have h6 := hc c _ (by omega) hcm _ _ h2
    have e : F.P a * F.X j = F.P a' * F.X j * F.X y + F.P a' * (of (ZMod p) G c - 1) +
        F.P a' * F.X j * (of (ZMod p) G c - 1) + F.P a * (of (ZMod p) G c - 1) +
        F.P a' * F.X j * F.X y * (of (ZMod p) G c - 1) := by
      rw [F.P_eq_mul_last hy hyl, ← ha', mul_assoc, F.X_comm j y]
      simp only [c, mul_add, mul_assoc]
    rw [e]
    refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_
    · exact F.Sp_mono (by omega) U h2
    · exact F.Sp_mono (by omega) U h3
    · exact F.Sp_mono (by omega) U h4
    · exact F.Sp_mono (by omega) U h5
    · exact F.Sp_mono (by omega) U h6
  intro k z hz
  induction hz using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  | mem x hx =>
  obtain ⟨a, ha, haU, rfl⟩ := hx
  exact F.Sp_mono (by omega) U (hP _ a rfl haU)

/-! ## `Δ^n ⊆ Sp n` -/

theorem Sp_mul_Sp_univ {k r : ℕ} {z v : MonoidAlgebra (ZMod p) G} (hz : z ∈ F.Sp k Set.univ)
    (hv : v ∈ F.Sp r Set.univ) : z * v ∈ F.Sp (k + r) Set.univ :=
  F.Sp_mul_Sp (fun i _ => F.Sp_mul_X isUpperSet_univ i (Set.mem_univ i)) hz hv

theorem augIdealP_le_Sp {y : MonoidAlgebra (ZMod p) G} (hy : y ∈ augIdealP p G) :
    y ∈ F.Sp 1 Set.univ := by
  -- `z ↦ z - ε(z) • 1` is linear and sends `g` to `g - 1 ∈ Sp 1`
  let M : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G) :=
    { carrier := {z | z - augmentationP p G z • (1 : MonoidAlgebra (ZMod p) G) ∈ F.Sp 1 Set.univ}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add, add_smul] at *
        have : a + b - (augmentationP p G a • (1 : MonoidAlgebra (ZMod p) G) +
            augmentationP p G b • 1) =
            (a - augmentationP p G a • 1) + (b - augmentationP p G b • 1) := by abel
        rw [this]; exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, augmentationP_smul, mul_smul] at *
        rw [← smul_sub]; exact Submodule.smul_mem _ c ha }
  have key : ∀ z, z ∈ M := mem_of_forall_of fun g => by
    show of (ZMod p) G g - augmentationP p G (of (ZMod p) G g) • (1 : MonoidAlgebra (ZMod p) G) ∈
      F.Sp 1 Set.univ
    rw [augmentationP_of, one_smul]
    exact F.of_sub_one_mem le_rfl (T.mem_one g) _ fun _ _ => Set.mem_univ _
  have : y - augmentationP p G y • (1 : MonoidAlgebra (ZMod p) G) ∈ F.Sp 1 Set.univ := key y
  rwa [mem_augIdealP.mp hy, zero_smul, sub_zero] at this

/-- `Δ^n ⊆ Sp n`. -/
theorem augIdealP_pow_le_Sp (n : ℕ) {z : MonoidAlgebra (ZMod p) G} (hz : z ∈ augIdealP p G ^ n) :
    z ∈ F.Sp n Set.univ := by
  induction n generalizing z with
  | zero => rw [F.Sp_zero_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    rw [Submodule.pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun _ _ h h' => add_mem h h')
    exact F.Sp_mul_Sp_univ (ih ha) (F.augIdealP_le_Sp hb)

end JFrame

end Jennings

end GroupDimension
