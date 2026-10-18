import GroupDimension.ExpThree

/-!
# Proper products and the weight filtration of `ℤ[G]` ([Tah81, §§2–3])

Infrastructure for the proof of Tahara's Theorem 6.1 (`TaharaFiveOne`).

**Frames.** A *frame* of a group `G` is Tahara's uniqueness basis `Φ` ([Tah81, p. 143]) together
with the weights and the orders of its letters: letters `x j` indexed by a finite linear order `ι`,
weights `w j ≥ 1` increasing in `j`, `x j ∈ γ_{w j}(G)`, and the normal form: every `g ∈ G` is
uniquely `∏_j x_j^{b_j}` (the product in the order of `ι`) with `0 ≤ b_j < o j`, and such a product
lies in `γ_{k+1}(G)` exactly when `b_j = 0` for all letters of weight `≤ k`.

**Proper products.** For `a : ι → ℕ` (Tahara's `m`-sequence), `P a = ∏_j (x_j - 1)^{a_j}`
(ordered product in `ℤ[G]`) and `W a = ∑_j a_j w_j` its weight. `Sp k U` is the `ℤ`-span of the
`P a` with `W a ≥ k` and all letters of `a` in `U`.

**Main results of the file.**
* `of_nprod_sub_one_sub` (Lemma 2.1, to first order): for `g = ∏ x_j^{b_j}`,
  `g - 1 - ∑ b_j (x_j - 1)` is a combination of `P β` with `β ≤ b`, `|β| ≥ 2`.
* `Sp_mul_X` (sorting): `Sp k U · (x_j - 1) ⊆ Sp (k + w_j) U` for an upper set `U ∋ j`. This is the
  reordering argument of Losey/Tahara: `(y-1)(x-1) = (x-1)(y-1) + ([y,x]-1) + …` with `[y,x]` of
  weight `w_x + w_y`; induction downward on the letter.
* `augIdeal_pow_le_Sp`: `Δ^n ⊆ Sp n univ`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara

/-! ## Ordered products over a sorted list -/

section Lprod

variable {ι : Type*} [LinearOrder ι] {M : Type*} [Monoid M]

/-- The ordered product `∏_{j ∈ l} f j ^ a j`. -/
def lprod (l : List ι) (f : ι → M) (a : ι → ℕ) : M := (l.map fun j => f j ^ a j).prod

@[simp] theorem lprod_zero (l : List ι) (f : ι → M) : lprod l f 0 = 1 := by
  simp [lprod]

theorem lprod_congr {l : List ι} (f : ι → M) {a b : ι → ℕ} (h : ∀ j ∈ l, a j = b j) :
    lprod l f a = lprod l f b := by
  unfold lprod; rw [List.map_congr_left (fun j hj => by rw [h j hj])]

/-- If `a` vanishes on the letters above `y`, appending `f y` adds one to the exponent of `y`. -/
theorem lprod_mul_single {l : List ι} (hl : l.Pairwise (· < ·)) {y : ι} (hy : y ∈ l) (f : ι → M)
    {a : ι → ℕ} (ha : ∀ j, y < j → a j = 0) :
    lprod l f a * f y = lprod l f (a + (Pi.single y 1 : ι → ℕ)) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hy
  rw [List.pairwise_append, List.pairwise_cons] at hl
  have h₂ : ∀ j ∈ l₂, y < j := hl.2.1.1
  have h₁ : ∀ j ∈ l₁, j < y := fun j hj => hl.2.2 j hj y List.mem_cons_self
  have e₂ : ∀ b : ι → ℕ, (∀ j ∈ l₂, b j = 0) → (l₂.map fun j => f j ^ b j).prod = 1 := by
    intro b hb
    refine List.prod_eq_one ?_
    simp only [List.mem_map]
    rintro _ ⟨j, hj, rfl⟩
    rw [hb j hj, pow_zero]
  have e₁ : (l₁.map fun j => f j ^ (a + (Pi.single y 1 : ι → ℕ)) j) = l₁.map fun j => f j ^ a j := by
    refine List.map_congr_left fun j hj => ?_
    rw [Pi.add_apply, Pi.single_eq_of_ne (h₁ j hj).ne, add_zero]
  simp only [lprod, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  rw [e₂ a (fun j hj => ha j (h₂ j hj)),
    e₂ _ (fun j hj => by
      rw [Pi.add_apply, ha j (h₂ j hj), Pi.single_eq_of_ne (h₂ j hj).ne', add_zero]), e₁,
    Pi.add_apply, Pi.single_eq_same, pow_succ]
  simp only [mul_one, mul_assoc]

end Lprod

/-! ## Sorted list of the letters -/

section Ord

variable (ι : Type*) [LinearOrder ι] [Fintype ι]

/-- The letters in increasing order. -/
noncomputable def ordL : List ι := (Finset.univ : Finset ι).sort (· ≤ ·)

variable {ι}

theorem ordL_pairwise : (ordL ι).Pairwise (· < ·) :=
  ((Finset.pairwise_sort (Finset.univ : Finset ι) (· ≤ ·)).and
    (Finset.sort_nodup (Finset.univ : Finset ι) (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2

theorem mem_ordL (j : ι) : j ∈ ordL ι := (Finset.mem_sort _).2 (Finset.mem_univ j)

end Ord

section Lprod2

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {M : Type*} [Monoid M]

/-- The largest letter of a nonzero `a`. -/
theorem exists_last {a : ι → ℕ} (ha : a ≠ 0) :
    ∃ y, a y ≠ 0 ∧ ∀ j, y < j → a j = 0 := by
  classical
  have hne : (Finset.univ.filter fun j => a j ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact ha (funext fun j => by simpa using h (Finset.mem_univ j))
  refine ⟨_, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, fun j hj => ?_⟩
  by_contra h
  exact absurd (Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)) (not_le.2 hj)

theorem sum_add_single (b : ι → ℕ) (y : ι) : ∑ j, (b + (Pi.single y 1 : ι → ℕ)) j = ∑ j, b j + 1 := by
  classical
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [Finset.sum_pi_single']; simp

theorem prod_flatMap' {α : Type*} (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem sum_flatMap' {α : Type*} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Removing the last letter. -/
theorem lprod_eq_mul_last (f : ι → M) {a : ι → ℕ} {y : ι} (hy : a y ≠ 0)
    (ha : ∀ j, y < j → a j = 0) :
    lprod (ordL ι) f a = lprod (ordL ι) f (a - (Pi.single y 1 : ι → ℕ)) * f y := by
  rw [lprod_mul_single ordL_pairwise (mem_ordL y) f]
  · congr 1; funext j
    by_cases h : j = y
    · subst h; simp; omega
    · simp [Pi.single_eq_of_ne h]
  · intro j hj; simp [ha j hj]

/-- Concatenation of ordered products with separated supports. -/
theorem lprod_mul_lprod (f : ι → M) {a : ι → ℕ} :
    ∀ (n : ℕ) (b : ι → ℕ), ∑ j, b j = n → (∀ i j, a i ≠ 0 → b j ≠ 0 → i < j) →
      lprod (ordL ι) f a * lprod (ordL ι) f b = lprod (ordL ι) f (a + b) := by
  intro n
  induction n with
  | zero =>
    intro b hb _
    have : b = 0 := funext fun j => by
      have := (Finset.sum_eq_zero_iff.mp hb) j (Finset.mem_univ j); simpa using this
    subst this; simp
  | succ n ih =>
    intro b hb hab
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    obtain ⟨y, hy, hyl⟩ := exists_last hb0
    rw [lprod_eq_mul_last f hy hyl, ← mul_assoc, ih (b - (Pi.single y 1 : ι → ℕ))]
    · rw [lprod_mul_single ordL_pairwise (mem_ordL y) f]
      · congr 1; funext j
        by_cases h : j = y
        · subst h; simp; omega
        · simp [Pi.single_eq_of_ne h]
      · intro j hj
        have h1 : a j = 0 := by
          by_contra h; exact absurd (hab j y h hy) (not_lt.2 hj.le)
        simp [h1, hyl j hj, Pi.single_eq_of_ne hj.ne']
    · have e : b = (b - (Pi.single y 1 : ι → ℕ)) + (Pi.single y 1 : ι → ℕ) := by
        funext j; by_cases h : j = y
        · subst h; simp; omega
        · simp [Pi.single_eq_of_ne h]
      have := sum_add_single (b - (Pi.single y 1 : ι → ℕ)) y
      rw [← e] at this; omega
    · intro i j hi hj
      refine hab i j hi ?_
      intro h0; apply hj; simp [h0]

/-- The product of a sorted word of letters. -/
theorem prod_map_eq_lprod (f : ι → M) (w : List ι) (hw : w.Pairwise (· ≤ ·)) :
    (w.map f).prod = lprod (ordL ι) f (fun j => w.count j) := by
  classical
  induction w using List.reverseRecOn with
  | nil => simp [lprod]
  | append_singleton w y ih =>
    rw [List.pairwise_append] at hw
    rw [List.map_append, List.prod_append, ih hw.1, List.map_singleton, List.prod_singleton,
      lprod_mul_single ordL_pairwise (mem_ordL y) f]
    · congr 1; funext j
      by_cases h : j = y
      · subst h; simp
      · simp [Pi.single_eq_of_ne h, List.count_singleton', Ne.symm h]
    · intro j hj
      refine List.count_eq_zero.mpr fun hjw => ?_
      exact absurd (hw.2.2 j hjw y List.mem_cons_self) (not_le.2 hj)

end Lprod2

/-! ## Frames -/

/-- A frame of `G`: Tahara's uniqueness basis with weights and orders ([Tah81, p. 143]). -/
structure Frame (G : Type*) [Group G] (ι : Type*) [LinearOrder ι] [Fintype ι] where
  x : ι → G
  w : ι → ℕ
  o : ι → ℕ
  w_pos : ∀ j, 1 ≤ w j
  w_mono : Monotone w
  mem : ∀ j, x j ∈ lowerCentralSeries G (w j - 1)
  pow_mem : ∀ j, x j ^ o j ∈ lowerCentralSeries G (w j)
  nf : ∀ g : G, ∃ b : ι → ℕ, (∀ j, b j < o j) ∧ lprod (ordL ι) x b = g
  nf_unique : ∀ b c : ι → ℕ, (∀ j, b j < o j) → (∀ j, c j < o j) →
    lprod (ordL ι) x b = lprod (ordL ι) x c → b = c
  wt : ∀ b : ι → ℕ, (∀ j, b j < o j) → ∀ k,
    lprod (ordL ι) x b ∈ lowerCentralSeries G k ↔ ∀ j, w j ≤ k → b j = 0

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable (F : Frame G ι)

/-- The group element `∏ x_j^{b_j}`. -/
noncomputable def nprod (b : ι → ℕ) : G := lprod (ordL ι) F.x b

/-- `x_j - 1 ∈ ℤ[G]`. -/
noncomputable def X (j : ι) : MonoidAlgebra ℤ G := of ℤ G (F.x j) - 1

/-- Tahara's proper product `P(a) = ∏_j (x_j - 1)^{a_j}`. -/
noncomputable def P (a : ι → ℕ) : MonoidAlgebra ℤ G := lprod (ordL ι) F.X a

/-- The weight `W(a) = ∑ a_j w_j`. -/
def W (a : ι → ℕ) : ℕ := ∑ j, a j * F.w j

/-- `Sp k U`: the span of the proper products of weight `≥ k` with letters in `U`. -/
noncomputable def Sp (k : ℕ) (U : Set ι) : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ {z | ∃ a : ι → ℕ, k ≤ F.W a ∧ (∀ j, a j ≠ 0 → j ∈ U) ∧ z = F.P a}

/-- The span of `P β` for `β ≤ b` with `|β| ≥ n`. -/
noncomputable def low (b : ι → ℕ) (n : ℕ) : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ {z | ∃ β : ι → ℕ, β ≤ b ∧ n ≤ ∑ j, β j ∧ z = F.P β}

theorem W_add (a b : ι → ℕ) : F.W (a + b) = F.W a + F.W b := by
  simp [W, add_mul, Finset.sum_add_distrib]

theorem W_single (j : ι) : F.W (Pi.single j 1) = F.w j := by
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

theorem P_mem_Sp {a : ι → ℕ} {k : ℕ} {U : Set ι} (hk : k ≤ F.W a) (hU : ∀ j, a j ≠ 0 → j ∈ U) :
    F.P a ∈ F.Sp k U :=
  Submodule.subset_span ⟨a, hk, hU, rfl⟩

/-! ## Lemma 2.1 to first order -/

theorem low_mono {b b' : ι → ℕ} (h : b ≤ b') {n n' : ℕ} (hn : n' ≤ n) :
    F.low b n ≤ F.low b' n' :=
  Submodule.span_mono fun _ ⟨β, hβ, hβn, e⟩ => ⟨β, hβ.trans h, hn.trans hβn, e⟩

/-- `low b n · (x_y - 1) ⊆ low (b + e_y) (n + 1)` when `b` vanishes above `y`. -/
theorem low_mul_X {b : ι → ℕ} {y : ι} (hb : ∀ j, y < j → b j = 0) {n : ℕ} {z : MonoidAlgebra ℤ G}
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

/-- **Lemma 2.1** (to first order): `∏ x_j^{b_j} - 1 - ∑ b_j (x_j - 1) ∈ low b 2`, and
`∏ x_j^{b_j} - 1 ∈ low b 1`. -/
theorem of_nprod_sub_one (b : ι → ℕ) :
    of ℤ G (F.nprod b) - 1 ∈ F.low b 1 ∧
      of ℤ G (F.nprod b) - 1 - ∑ j, (b j : ℤ) • F.X j ∈ F.low b 2 := by
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
    have e : of ℤ G (F.nprod b) = of ℤ G (F.nprod b') * (1 + F.X y) := by
      rw [F.nprod_eq_mul_last hy hyl, ← hb', _root_.map_mul, X, add_sub_cancel]
    have hX : F.X y ∈ F.low b 1 := by
      have : F.X y = F.P (Pi.single y 1) := by
        rw [← zero_add (Pi.single y 1 : ι → ℕ), ← F.P_mul_X (by simp), P_zero, one_mul]
      rw [this]
      refine Submodule.subset_span ⟨(Pi.single y 1 : ι → ℕ), ?_, by simp, rfl⟩
      rw [hbb]; exact le_add_of_nonneg_left (zero_le _)
    have h1 := F.low_mul_X hb'l ih1
    rw [← hbb] at h1
    constructor
    · have : of ℤ G (F.nprod b) - 1 =
          (of ℤ G (F.nprod b') - 1) + (of ℤ G (F.nprod b') - 1) * F.X y + F.X y := by
        rw [e]; noncomm_ring
      rw [this]
      exact add_mem (add_mem (F.low_mono hle le_rfl ih1) (F.low_mono le_rfl (by omega) h1)) hX
    · have hs : ∑ j, (b j : ℤ) • F.X j = ∑ j, (b' j : ℤ) • F.X j + F.X y := by
        conv_lhs => rw [hbb]
        simp only [Pi.add_apply, Nat.cast_add, add_smul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single y]
        · simp
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
      have : of ℤ G (F.nprod b) - 1 - ∑ j, (b j : ℤ) • F.X j =
          (of ℤ G (F.nprod b') - 1 - ∑ j, (b' j : ℤ) • F.X j) +
            (of ℤ G (F.nprod b') - 1) * F.X y := by
        rw [e, hs]; noncomm_ring
      rw [this]
      exact add_mem (F.low_mono hle le_rfl ih2) h1

/-- The normal form of an element of `γ_k` has no letters of weight `< k`. -/
theorem nf_weight {g : G} {k : ℕ} (hg : g ∈ lowerCentralSeries G (k - 1)) {b : ι → ℕ}
    (hb : ∀ j, b j < F.o j) (hbg : F.nprod b = g) {j : ι} (hj : b j ≠ 0) : k ≤ F.w j := by
  by_contra h
  have hm : lprod (ordL ι) F.x b ∈ lowerCentralSeries G (k - 1) := by
    rw [show lprod (ordL ι) F.x b = g from hbg]; exact hg
  exact hj ((F.wt b hb (k - 1)).mp hm j (by omega))

/-- For `g ∈ γ_k`, `g - 1` is a combination of proper products of weight `≥ k` whose letters have
weight `≥ k`. -/
theorem of_sub_one_mem {g : G} {k : ℕ} (hg : g ∈ lowerCentralSeries G (k - 1)) (U : Set ι)
    (hU : ∀ j, k ≤ F.w j → j ∈ U) :
    of ℤ G g - 1 ∈ F.Sp k U := by
  obtain ⟨b, hb, rfl⟩ := F.nf g
  refine Submodule.span_le.mpr ?_ (F.of_nprod_sub_one b).1
  rintro _ ⟨β, hβ, hβn, rfl⟩
  have hl : ∀ j, β j ≠ 0 → k ≤ F.w j := fun j hj =>
    F.nf_weight hg hb rfl (fun h => hj (Nat.eq_zero_of_le_zero (h ▸ hβ j)))
  refine Submodule.subset_span ⟨β, ?_, fun j hj => hU j (hl j hj), rfl⟩
  obtain ⟨j0, hj0⟩ : ∃ j, β j ≠ 0 := by
    by_contra h; push Not at h; simp [h] at hβn
  calc k ≤ F.w j0 := hl j0 hj0
    _ ≤ β j0 * F.w j0 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj0)
    _ ≤ F.W β := Finset.single_le_sum (f := fun j => β j * F.w j) (fun _ _ => zero_le _)
          (Finset.mem_univ j0)

/-! ## Sorting -/

/-- The commutation rule `(y-1)(x-1) = (x-1)(y-1) + (c-1)(1 + (x-1) + (y-1) + (x-1)(y-1))`
with `c = [y, x]`, written with `xy (c - 1) = yx - xy`. -/
theorem X_comm (i j : ι) :
    F.X j * F.X i = F.X i * F.X j + (of ℤ G (tc (F.x j) (F.x i)) - 1) +
      F.X i * (of ℤ G (tc (F.x j) (F.x i)) - 1) + F.X j * (of ℤ G (tc (F.x j) (F.x i)) - 1) +
      F.X i * F.X j * (of ℤ G (tc (F.x j) (F.x i)) - 1) := by
  have h : of ℤ G (F.x j) * of ℤ G (F.x i) =
      of ℤ G (F.x i) * of ℤ G (F.x j) * of ℤ G (tc (F.x j) (F.x i)) := by
    rw [← _root_.map_mul, ← _root_.map_mul, ← _root_.map_mul]; congr 1; simp only [tc]; group
  simp only [X]
  rw [← sub_eq_zero]
  have e : ∀ a b c : MonoidAlgebra ℤ G,
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

/-- The word of an `m`-sequence: its letters in order, with multiplicity. -/
noncomputable def word (a : ι → ℕ) : List ι := (ordL ι).flatMap fun j => List.replicate (a j) j

theorem P_eq_word (a : ι → ℕ) : F.P a = ((word a).map F.X).prod := by
  simp only [P, lprod, word, List.map_flatMap, prod_flatMap', List.map_replicate,
    List.prod_replicate]

theorem sum_ordL {N : Type*} [AddCommMonoid N] (f : ι → N) :
    ((ordL ι).map f).sum = ∑ j, f j := by
  classical
  unfold ordL
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _)]
  simp [Finset.sort_toFinset]

theorem W_eq_word (a : ι → ℕ) : F.W a = ((word a).map F.w).sum := by
  simp only [W, word, List.map_flatMap, sum_flatMap', List.map_replicate, List.sum_replicate,
    smul_eq_mul]
  rw [sum_ordL]

theorem mem_word {a : ι → ℕ} {i : ι} (h : i ∈ word a) : a i ≠ 0 := by
  simp only [word, List.mem_flatMap, List.mem_replicate] at h
  obtain ⟨j, -, hj, rfl⟩ := h
  exact hj

/-- Multiplying by an element of `Sp r V` for letters in `V` satisfying the sorting claim. -/
theorem Sp_mul_Sp {U V : Set ι}
    (hQ : ∀ i ∈ V, ∀ k, ∀ z ∈ F.Sp k U, z * F.X i ∈ F.Sp (k + F.w i) U)
    {k r : ℕ} {z v : MonoidAlgebra ℤ G} (hz : z ∈ F.Sp k U) (hv : v ∈ F.Sp r V) :
    z * v ∈ F.Sp (k + r) U := by
  induction hv using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul c u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
  | mem x hx =>
  obtain ⟨a, ha, hV, rfl⟩ := hx
  rw [F.P_eq_word]
  refine F.Sp_mono (by rw [← F.W_eq_word]; omega) U
    (F.Sp_mul_word (· ∈ V) hQ _ (fun i hi => hV i (mem_word hi)) k z hz)

/-- **Sorting** ([Tah81, §3], after Losey): `Sp k U · (x_j - 1) ⊆ Sp (k + w_j) U` for an upper
set `U` containing `j`. -/
theorem Sp_mul_X {U : Set ι} (hU : IsUpperSet U) :
    ∀ j ∈ U, ∀ k, ∀ z ∈ F.Sp k U, z * F.X j ∈ F.Sp (k + F.w j) U := by
  classical
  intro j
  induction j using WellFoundedGT.induction with
  | _ j IH =>
  intro hjU
  -- multiplying by `c - 1` for `c` of weight `> w j`
  have hc : ∀ (c : G) (r : ℕ), F.w j < r → c ∈ lowerCentralSeries G (r - 1) →
      ∀ k, ∀ z ∈ F.Sp k U, z * (of ℤ G c - 1) ∈ F.Sp (k + r) U := by
    intro c r hr hcr k z hz
    have hcm : of ℤ G c - 1 ∈ F.Sp r {i | j < i} :=
      F.of_sub_one_mem hcr _ fun i hi => F.lt_of_w_lt (by omega)
    refine F.Sp_mul_Sp (V := {i | j < i}) (fun i hi k z hz => IH i hi (hU hi.le hjU) k z hz) hz hcm
  -- the claim for proper products, by induction on their length
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
    set c := tc (F.x y) (F.x j)
    have hcm : c ∈ lowerCentralSeries G (F.w y + F.w j - 1) := by
      refine ExpThree.tc_mem ?_ (F.mem y) (F.mem j)
      have := F.w_pos y; have := F.w_pos j; omega
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
    have e : F.P a * F.X j = F.P a' * F.X j * F.X y + F.P a' * (of ℤ G c - 1) +
        F.P a' * F.X j * (of ℤ G c - 1) + F.P a * (of ℤ G c - 1) +
        F.P a' * F.X j * F.X y * (of ℤ G c - 1) := by
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

end Frame

end TaharaProof

end GroupDimension
