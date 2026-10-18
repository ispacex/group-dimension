import GroupDimension.TaharaProof.Basis

/-!
# Frames from uniqueness bases of the layers

A uniqueness basis of each layer `γ_{k+1}/γ_{k+2}` ([Tah81, p. 143]) gives a frame of `G`: the
letters of layer `k` come before those of layer `k + 1`, and every element of `G` has a unique
normal form `∏ x_j^{b_j}`, `0 ≤ b_j < o_j`. We build it layer by layer from the top
(`TailFrame k`: normal forms of the elements of `γ_{k+1}`), gluing one layer at a time
(`TailFrame.glue`, letters `Fin n ⊕ₗ ι`).
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

/-! ## Transport of ordered products -/

section Transport

variable {ι κ : Type*} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]
variable {M : Type*} [Monoid M]

theorem count_flatMap_replicate [DecidableEq ι] {L : List ι} (hnd : L.Nodup) (a : ι → ℕ)
    (i : ι) : (L.flatMap fun j => List.replicate (a j) j).count i = if i ∈ L then a i else 0 := by
  induction L with
  | nil => simp
  | cons j L ih =>
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.count_append, ih hnd.2, List.count_replicate]
    by_cases h : j = i
    · subst h; simp [hnd.1]
    · have : (j == i) = false := by simpa using h
      simp only [this, Bool.false_eq_true, ↓reduceIte, zero_add, List.mem_cons]
      by_cases hi : i ∈ L
      · simp [hi]
      · simp [hi, Ne.symm h]

/-- Ordered product over any complete strictly increasing list. -/
theorem lprod_eq_ordL {L : List ι} (hL : L.Pairwise (· < ·)) (hall : ∀ j, j ∈ L) (f : ι → M)
    (a : ι → ℕ) : lprod L f a = lprod (ordL ι) f a := by
  classical
  have hw : (L.flatMap fun j => List.replicate (a j) j).Pairwise (· ≤ ·) := by
    rw [List.pairwise_flatMap]
    refine ⟨fun j _ => List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
    refine hL.imp fun {i j} hij => ?_
    intro x hx y hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]; exact hij.le
  have hc : (fun j => (L.flatMap fun j => List.replicate (a j) j).count j) = a := by
    funext j
    rw [count_flatMap_replicate (hL.imp ne_of_lt), if_pos (hall j)]
  calc lprod L f a = (((L.flatMap fun j => List.replicate (a j) j)).map f).prod := by
        simp [lprod, List.map_flatMap, prod_flatMap', List.map_replicate, List.prod_replicate]
    _ = lprod (ordL ι) f _ := prod_map_eq_lprod f _ hw
    _ = lprod (ordL ι) f a := by rw [hc]

/-- Transport of an ordered product along a strictly monotone map. -/
theorem lprod_comp {e : κ → ι} (he : StrictMono e) (f : ι → M) (a : ι → ℕ)
    (ha : ∀ j, a j ≠ 0 → ∃ i, e i = j) :
    lprod (ordL ι) f a = lprod (ordL κ) (f ∘ e) (a ∘ e) := by
  classical
  set w := (ordL κ).flatMap fun i => List.replicate (a (e i)) i
  have hw : (w.map e).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    rw [List.pairwise_flatMap]
    refine ⟨fun j _ => List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
    refine ordL_pairwise.imp fun {i j} hij => ?_
    intro x hx y hy
    rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]; exact (he hij).le
  have hc : (fun j => (w.map e).count j) = a := by
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [List.count_map_of_injective _ _ he.injective,
        count_flatMap_replicate ((ordL_pairwise).imp ne_of_lt), if_pos (mem_ordL i)]
    · have h0 : a j = 0 := by by_contra h; exact hj (ha j h)
      rw [h0, List.count_eq_zero]
      intro hm
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hm
      exact hj ⟨i, rfl⟩
  conv_lhs => rw [← hc]
  rw [← prod_map_eq_lprod f _ hw, List.map_map]
  simp [w, lprod, List.map_flatMap, prod_flatMap', List.map_replicate, List.prod_replicate]

/-- `lprod` over `Fin n` as `oprod`. -/
theorem lprod_fin_eq_oprod {n : ℕ} (y : Fin n → G) (c : Fin n → ℕ) :
    lprod (ordL (Fin n)) y c = oprod y (fun i => (c i : ℤ)) := by
  rw [← lprod_eq_ordL (List.pairwise_lt_finRange n) (List.mem_finRange) y c]
  simp [lprod, oprod, List.ofFn_eq_map]

end Transport

/-! ## A uniqueness basis of one layer -/

/-- The normal-form part of Tahara's uniqueness basis of the layer `γ_{k+1}/γ_{k+2}`. -/
structure LayerNF (k : ℕ) {n : ℕ} (y : Fin n → G) (o : Fin n → ℕ) : Prop where
  mem : ∀ i, y i ∈ lowerCentralSeries G k
  pos : ∀ i, 0 < o i
  indep : ∀ a : Fin n → ℤ, oprod y a ∈ lowerCentralSeries G (k + 1) ↔ ∀ i, (o i : ℤ) ∣ a i
  span : ∀ g ∈ lowerCentralSeries G k, ∃ a : Fin n → ℤ,
    (oprod y a)⁻¹ * g ∈ lowerCentralSeries G (k + 1)

theorem IsLayerBasis.layerNF {k n : ℕ} {y : Fin n → G} {o : Fin n → ℕ}
    (h : IsLayerBasis k y o) : LayerNF k y o :=
  ⟨h.mem, fun i => lt_trans zero_lt_one (h.one_lt i), h.indep, h.span⟩

namespace LayerNF

variable {k n : ℕ} {y : Fin n → G} {o : Fin n → ℕ} (h : LayerNF k y o)
include h

theorem lprod_mem (c : Fin n → ℕ) : lprod (ordL (Fin n)) y c ∈ lowerCentralSeries G k := by
  rw [lprod_fin_eq_oprod]; exact ExpThree.oprod_mem h.mem _

theorem cl_lprod (c : Fin n → ℕ) :
    cl G k (lprod (ordL (Fin n)) y c) = ∑ i, (c i : ℤ) • cl G k (y i) := by
  rw [lprod_fin_eq_oprod, cl_oprod h.mem]

theorem o_smul_cl (i : Fin n) : (o i : ℤ) • cl G k (y i) = 0 := by
  classical
  have h1 := (h.indep (Pi.single i (o i : ℤ))).mpr fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [← cl_eq_zero_iff (ExpThree.oprod_mem h.mem _), cl_oprod h.mem] at h1
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at h1
  simpa using h1

theorem pow_mem (i : Fin n) : y i ^ o i ∈ lowerCentralSeries G (k + 1) := by
  rw [← cl_eq_zero_iff (_root_.pow_mem (h.mem i) _), ← zpow_natCast, cl_zpow (h.mem i)]
  exact h.o_smul_cl i

/-- Membership in `γ_{k+2}` of a product, by its coefficients. -/
theorem lprod_mem_succ_iff (c : Fin n → ℕ) :
    lprod (ordL (Fin n)) y c ∈ lowerCentralSeries G (k + 1) ↔ ∀ i, o i ∣ c i := by
  rw [lprod_fin_eq_oprod, h.indep]
  simp only [Int.natCast_dvd_natCast]

/-- Existence of the normal form in the layer. -/
theorem exists_nf {g : G} (hg : g ∈ lowerCentralSeries G k) :
    ∃ c : Fin n → ℕ, (∀ i, c i < o i) ∧
      (lprod (ordL (Fin n)) y c)⁻¹ * g ∈ lowerCentralSeries G (k + 1) := by
  obtain ⟨a, ha⟩ := h.span g hg
  refine ⟨fun i => (a i % (o i : ℤ)).toNat, fun i => ?_, ?_⟩
  · show (a i % (o i : ℤ)).toNat < o i
    have := Int.emod_lt_of_pos (a i) (Int.natCast_pos.mpr (h.pos i))
    have := Int.emod_nonneg (a i) (Int.natCast_pos.mpr (h.pos i)).ne'
    omega
  · have hm := h.lprod_mem (fun i => (a i % (o i : ℤ)).toNat)
    have hm' := ExpThree.oprod_mem h.mem a
    rw [← cl_eq_zero_iff (mul_mem (inv_mem hm') hg)] at ha
    rw [← cl_eq_zero_iff (mul_mem (inv_mem hm) hg)]
    rw [cl_mul (inv_mem hm') hg, cl_inv hm', cl_oprod h.mem] at ha
    rw [cl_mul (inv_mem hm) hg, cl_inv hm, h.cl_lprod]
    rw [← ha]
    congr 1; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (((a i % (o i : ℤ)).toNat : ℕ) : ℤ) = a i - (o i : ℤ) * (a i / (o i : ℤ)) := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_pos.mpr (h.pos i)).ne'),
        Int.emod_def]
    rw [e1, sub_smul, mul_comm, mul_smul, h.o_smul_cl i, smul_zero, sub_zero]

/-- Uniqueness of the normal form in the layer. -/
theorem nf_unique {c c' : Fin n → ℕ} (hc : ∀ i, c i < o i) (hc' : ∀ i, c' i < o i)
    (hcc : (lprod (ordL (Fin n)) y c)⁻¹ * lprod (ordL (Fin n)) y c' ∈
      lowerCentralSeries G (k + 1)) : c = c' := by
  have hm := h.lprod_mem c
  have hm' := h.lprod_mem c'
  rw [← cl_eq_zero_iff (mul_mem (inv_mem hm) hm'), cl_mul (inv_mem hm) hm', cl_inv hm,
    h.cl_lprod, h.cl_lprod, neg_add_eq_sub, ← Finset.sum_sub_distrib] at hcc
  simp_rw [← sub_smul] at hcc
  have key : oprod y (fun i => (c' i : ℤ) - c i) ∈ lowerCentralSeries G (k + 1) := by
    rw [← cl_eq_zero_iff (ExpThree.oprod_mem h.mem _), cl_oprod h.mem]; exact hcc
  have hd := (h.indep _).mp key
  funext i
  have := hd i
  have h1 := hc i; have h2 := hc' i
  obtain ⟨q, hq⟩ := this
  have : q = 0 := by
    by_contra hq0
    rcases lt_or_gt_of_ne hq0 with hq0 | hq0
    · have : (o i : ℤ) * q ≤ -(o i : ℤ) := by nlinarith
      omega
    · have : (o i : ℤ) ≤ (o i : ℤ) * q := by nlinarith
      omega
  subst this; omega

end LayerNF

/-! ## Tail frames -/

/-- Normal forms of the elements of `γ_{k+1}` (Mathlib index `k`) by the letters of the layers
`≥ k`. -/
structure TailFrame (G : Type*) [Group G] (k : ℕ) (ι : Type*) [LinearOrder ι] [Fintype ι] where
  x : ι → G
  w : ι → ℕ
  o : ι → ℕ
  w_ge : ∀ j, k + 1 ≤ w j
  w_mono : Monotone w
  mem : ∀ j, x j ∈ lowerCentralSeries G (w j - 1)
  pow_mem : ∀ j, x j ^ o j ∈ lowerCentralSeries G (w j)
  nf : ∀ g ∈ lowerCentralSeries G k, ∃ b : ι → ℕ, (∀ j, b j < o j) ∧ lprod (ordL ι) x b = g
  nf_unique : ∀ b c : ι → ℕ, (∀ j, b j < o j) → (∀ j, c j < o j) →
    lprod (ordL ι) x b = lprod (ordL ι) x c → b = c
  wt : ∀ b : ι → ℕ, (∀ j, b j < o j) → ∀ k',
    lprod (ordL ι) x b ∈ lowerCentralSeries G k' ↔ ∀ j, w j ≤ k' → b j = 0

namespace TailFrame

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- No letters: the top of the series is trivial. -/
def empty (k : ℕ) (hk : lowerCentralSeries G k = ⊥) : TailFrame G k (Fin 0) where
  x := Fin.elim0
  w := Fin.elim0
  o := Fin.elim0
  w_ge := fun j => j.elim0
  w_mono := fun j => j.elim0
  mem := fun j => j.elim0
  pow_mem := fun j => j.elim0
  nf := fun g hg => by
    rw [hk, Subgroup.mem_bot] at hg
    subst hg
    exact ⟨fun j => j.elim0, fun j => j.elim0, by simp [lprod, ordL]⟩
  nf_unique := fun b c _ _ _ => funext fun j => j.elim0
  wt := fun b _ k' => by
    have : lprod (ordL (Fin 0)) (Fin.elim0 : Fin 0 → G) b = 1 := by simp [lprod, ordL]
    simp [this, one_mem]

variable {k : ℕ} (T : TailFrame G k ι)

theorem lprod_mem (b : ι → ℕ) : lprod (ordL ι) T.x b ∈ lowerCentralSeries G k := by
  refine list_prod_mem fun z hz => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hz
  exact _root_.pow_mem (lcs_mem_of_le (i := k) (j := T.w j - 1) (by have := T.w_ge j; omega)
    (T.mem j)) _

end TailFrame

/-! ## Gluing a layer below a tail frame -/

section Glue

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {n : ℕ}

/-- The letters of the new layer. -/
def inlₗ (i : Fin n) : Fin n ⊕ₗ ι := toLex (Sum.inl i)

/-- The letters of the tail. -/
def inrₗ (j : ι) : Fin n ⊕ₗ ι := toLex (Sum.inr j)

theorem inlₗ_strictMono : StrictMono (inlₗ : Fin n → Fin n ⊕ₗ ι) :=
  fun _ _ h => Sum.Lex.inl_lt_inl_iff.mpr h

theorem inrₗ_strictMono : StrictMono (inrₗ : ι → Fin n ⊕ₗ ι) :=
  fun _ _ h => Sum.Lex.inr_lt_inr_iff.mpr h

theorem inlₗ_lt_inrₗ (i : Fin n) (j : ι) : (inlₗ i : Fin n ⊕ₗ ι) < inrₗ j := Sum.Lex.inl_lt_inr _ _

theorem cases_lex (p : Fin n ⊕ₗ ι) : (∃ i, p = inlₗ i) ∨ ∃ j, p = inrₗ j := by
  rcases p with (i | j)
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

/-- An ordered product over `Fin n ⊕ₗ ι` splits into the layer part and the tail part. -/
theorem lprod_split {M : Type*} [Monoid M] (f : Fin n ⊕ₗ ι → M) (b : Fin n ⊕ₗ ι → ℕ) :
    lprod (ordL (Fin n ⊕ₗ ι)) f b =
      lprod (ordL (Fin n)) (f ∘ inlₗ) (b ∘ inlₗ) * lprod (ordL ι) (f ∘ inrₗ) (b ∘ inrₗ) := by
  classical
  let bl : Fin n ⊕ₗ ι → ℕ := fun p => Sum.elim (fun i => b (inlₗ i)) (fun _ => 0) (ofLex p)
  let br : Fin n ⊕ₗ ι → ℕ := fun p => Sum.elim (fun _ => 0) (fun j => b (inrₗ j)) (ofLex p)
  have hb : b = bl + br := by
    funext p; rcases p with (i | j)
    · show b (toLex (Sum.inl i)) = b (inlₗ i) + 0; rfl
    · show b (toLex (Sum.inr j)) = 0 + b (inrₗ j); rw [zero_add]; rfl
  have hl : lprod (ordL (Fin n ⊕ₗ ι)) f bl = lprod (ordL (Fin n)) (f ∘ inlₗ) (b ∘ inlₗ) := by
    rw [lprod_comp inlₗ_strictMono f bl]
    · rfl
    · intro p hp
      rcases p with (i | j)
      · exact ⟨i, rfl⟩
      · exact absurd rfl hp
  have hr : lprod (ordL (Fin n ⊕ₗ ι)) f br = lprod (ordL ι) (f ∘ inrₗ) (b ∘ inrₗ) := by
    rw [lprod_comp inrₗ_strictMono f br]
    · rfl
    · intro p hp
      rcases p with (i | j)
      · exact absurd rfl hp
      · exact ⟨j, rfl⟩
  rw [← hl, ← hr, lprod_mul_lprod f _ br rfl, ← hb]
  intro p q hp hq
  rcases p with (i | j)
  · rcases q with (i' | j')
    · exact absurd rfl hq
    · exact Sum.Lex.inl_lt_inr _ _
  · exact absurd rfl hp

variable {k : ℕ} {y : Fin n → G} {o' : Fin n → ℕ}

/-- Gluing the layer `k` below a tail frame of `γ_{k+2}`. -/
def TailFrame.glue (hy : LayerNF k y o') (T : TailFrame G (k + 1) ι) :
    TailFrame G k (Fin n ⊕ₗ ι) where
  x p := Sum.elim y T.x (ofLex p)
  w p := Sum.elim (fun _ => k + 1) T.w (ofLex p)
  o p := Sum.elim o' T.o (ofLex p)
  w_ge p := by
    rcases p with (i | j)
    · exact le_rfl
    · have := T.w_ge j; show k + 1 ≤ T.w j; omega
  w_mono p q hpq := by
    rcases p with (i | j) <;> rcases q with (i' | j')
    · exact le_rfl
    · have := T.w_ge j'; show k + 1 ≤ T.w j'; omega
    · exact absurd hpq (not_le.2 (Sum.Lex.inl_lt_inr _ _))
    · exact T.w_mono (Sum.Lex.inr_le_inr_iff.mp hpq)
  mem p := by
    rcases p with (i | j)
    · simpa using hy.mem i
    · exact T.mem j
  pow_mem p := by
    rcases p with (i | j)
    · exact hy.pow_mem i
    · exact T.pow_mem j
  nf g hg := by
    obtain ⟨c, hc, hcg⟩ := hy.exists_nf hg
    obtain ⟨b', hb', hb'g⟩ := T.nf _ hcg
    refine ⟨fun p => Sum.elim c b' (ofLex p), fun p => ?_, ?_⟩
    · rcases p with (i | j)
      · exact hc i
      · exact hb' j
    · rw [lprod_split]
      change lprod (ordL (Fin n)) y c * lprod (ordL ι) T.x b' = g
      rw [hb'g, mul_inv_cancel_left]
  nf_unique b c hb hc hbc := by
    rw [lprod_split, lprod_split] at hbc
    change lprod (ordL (Fin n)) y (b ∘ inlₗ) * lprod (ordL ι) T.x (b ∘ inrₗ) =
      lprod (ordL (Fin n)) y (c ∘ inlₗ) * lprod (ordL ι) T.x (c ∘ inrₗ) at hbc
    have hl : b ∘ inlₗ = c ∘ inlₗ := by
      refine hy.nf_unique (fun i => hb (inlₗ i)) (fun i => hc (inlₗ i)) ?_
      have e : (lprod (ordL (Fin n)) y (b ∘ inlₗ))⁻¹ * lprod (ordL (Fin n)) y (c ∘ inlₗ) =
          lprod (ordL ι) T.x (b ∘ inrₗ) * (lprod (ordL ι) T.x (c ∘ inrₗ))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hbc, mul_inv_cancel_right]
      rw [e]
      exact mul_mem (T.lprod_mem _) (inv_mem (T.lprod_mem _))
    have hr : b ∘ inrₗ = c ∘ inrₗ := by
      refine T.nf_unique _ _ (fun j => hb (inrₗ j)) (fun j => hc (inrₗ j)) ?_
      rw [hl] at hbc
      exact mul_left_cancel hbc
    funext p
    rcases p with (i | j)
    · exact congrFun hl i
    · exact congrFun hr j
  wt b hb k' := by
    rw [lprod_split]
    change lprod (ordL (Fin n)) y (b ∘ inlₗ) * lprod (ordL ι) T.x (b ∘ inrₗ) ∈ _ ↔ _
    have hT := T.lprod_mem (b ∘ inrₗ)
    have hL := hy.lprod_mem (b ∘ inlₗ)
    by_cases hk' : k' ≤ k
    · constructor
      · intro _ p hp
        rcases p with (i | j)
        · change k + 1 ≤ k' at hp; omega
        · have := T.w_ge j; change T.w j ≤ k' at hp; omega
      · intro _
        exact lcs_mem_of_le hk' (mul_mem hL (lcs_mem_of_le (by omega) hT))
    · push Not at hk'
      constructor
      · intro hm
        have hl0 : b ∘ inlₗ = 0 := by
          have h1 : lprod (ordL (Fin n)) y (b ∘ inlₗ) ∈ lowerCentralSeries G (k + 1) := by
            have := lcs_mem_of_le (show k + 1 ≤ k' by omega) hm
            have e : lprod (ordL (Fin n)) y (b ∘ inlₗ) =
                lprod (ordL (Fin n)) y (b ∘ inlₗ) * lprod (ordL ι) T.x (b ∘ inrₗ) *
                  (lprod (ordL ι) T.x (b ∘ inrₗ))⁻¹ := by group
            rw [e]; exact mul_mem this (inv_mem hT)
          rw [hy.lprod_mem_succ_iff] at h1
          funext i
          obtain ⟨q, hq⟩ := h1 i
          have := hb (inlₗ i)
          change b (inlₗ i) < o' i at this
          have : q = 0 := by
            by_contra hq0
            have : o' i ≤ o' i * q := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq0)
            simp only [Function.comp_apply] at hq; omega
          simp only [Function.comp_apply] at hq; simp [hq, this]
        have e0 : lprod (ordL (Fin n)) y (b ∘ inlₗ) = 1 := by rw [hl0]; exact lprod_zero _ _
        rw [e0, one_mul] at hm
        have := (T.wt (b ∘ inrₗ) (fun j => hb (inrₗ j)) k').mp hm
        intro p hp
        rcases p with (i | j)
        · exact congrFun hl0 i
        · exact this j hp
      · intro h0
        have hl0 : b ∘ inlₗ = 0 := funext fun i => h0 (inlₗ i) (by
          change k + 1 ≤ k'; omega)
        rw [hl0, lprod_zero, one_mul]
        exact (T.wt (b ∘ inrₗ) (fun j => hb (inrₗ j)) k').mpr fun j hj => h0 (inrₗ j) hj

end Glue

/-- A tail frame of `γ₁ = G` is a frame. -/
def TailFrame.toFrame {ι : Type*} [LinearOrder ι] [Fintype ι] (T : TailFrame G 0 ι) :
    Frame G ι where
  x := T.x
  w := T.w
  o := T.o
  w_pos j := T.w_ge j
  w_mono := T.w_mono
  mem := T.mem
  pow_mem := T.pow_mem
  nf g := T.nf g (by simp)
  nf_unique := T.nf_unique
  wt := T.wt

end TaharaProof

end GroupDimension
