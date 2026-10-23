module

public import GroupDimension.Jennings.Basis

@[expose] public section

/-!
# A frame of a restricted N-series

Stage 3 of Jennings' theorem: every restricted N-series `S` of a finite group (`p` prime) has a
frame (`RestrictedSeries.exists_frame`).

**The layers.** `S k / S (k+1)` is abelian (`[S k, S k] ≤ S (2k) ≤ S (k+1)`) of exponent `p`
(`(S k)^p ≤ S (pk) ≤ S (k+1)`), so it is an `𝔽_p`-vector space; lifting a basis gives letters
`y_1, …, y_n ∈ S k` such that every `g ∈ S k` is `∏ y_i^{c_i}` modulo `S (k+1)` for unique
`0 ≤ c_i < p` (`LayerNF`, `exists_layerNF`). We work in the image of `S k` in `G ⧸ S (k+1)`.

**Gluing.** As in `TaharaProof/Layers.lean`, a *tail frame* (`TailFrame T k ι`) gives normal forms
of the elements of `S k` by letters of weight `≥ k`; it is built from the top (`S N = ⊥`) down,
gluing one layer at a time (`TailFrame.glue`, letters `Fin n ⊕ₗ ι`), and a tail frame of `S 1 = G`
is a frame.
-/

namespace GroupDimension

namespace Jennings

open MonoidAlgebra TaharaProof
open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] {T : RestrictedSeries p G}

/-- The image of a monoid hom on an ordered product. -/
theorem map_lprod {ι : Type*} {M N : Type*} [Monoid M] [Monoid N] {F' : Type*} [FunLike F' M N]
    [MonoidHomClass F' M N] (φ : F') (l : List ι) (f : ι → M) (a : ι → ℕ) :
    φ (lprod l f a) = lprod l (fun j => φ (f j)) a := by
  simp [lprod, map_list_prod, List.map_map, Function.comp_def]

theorem RestrictedSeries.lprod_mem {ι : Type*} {k : ℕ} {l : List ι} {f : ι → G}
    (hf : ∀ j ∈ l, f j ∈ T.S k) (a : ι → ℕ) : lprod l f a ∈ T.S k := by
  refine list_prod_mem fun z hz => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
  exact _root_.pow_mem (hf j hj) _

/-! ## A basis of one layer -/

/-- Normal forms of `S k` modulo `S (k+1)` with exponents `< p`. -/
structure LayerNF (T : RestrictedSeries p G) (k : ℕ) {n : ℕ} (y : Fin n → G) : Prop where
  mem : ∀ i, y i ∈ T.S k
  exists_nf : ∀ g ∈ T.S k, ∃ c : Fin n → ℕ, (∀ i, c i < p) ∧
    (lprod (ordL (Fin n)) y c)⁻¹ * g ∈ T.S (k + 1)
  nf_unique : ∀ c c' : Fin n → ℕ, (∀ i, c i < p) → (∀ i, c' i < p) →
    (lprod (ordL (Fin n)) y c)⁻¹ * lprod (ordL (Fin n)) y c' ∈ T.S (k + 1) → c = c'

namespace LayerNF

variable {k n : ℕ} {y : Fin n → G} (h : LayerNF T k y)
include h

theorem lprod_mem (c : Fin n → ℕ) : lprod (ordL (Fin n)) y c ∈ T.S k :=
  T.lprod_mem (fun i _ => h.mem i) c

theorem eq_zero_of_mem {c : Fin n → ℕ} (hc : ∀ i, c i < p)
    (hm : lprod (ordL (Fin n)) y c ∈ T.S (k + 1)) (hp : 0 < p) : c = 0 :=
  (h.nf_unique 0 c (fun _ => hp) hc (by simpa using hm)).symm

end LayerNF

/-- A finite abelian group of exponent `p` has a basis: every element is uniquely
`∑ c_i • e_i` with `0 ≤ c_i < p`. -/
theorem exists_nsmul_basis [Fact p.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    (hV : ∀ v : V, p • v = 0) :
    ∃ (n : ℕ) (e : Fin n → V), (∀ v, ∃ c : Fin n → ℕ, (∀ i, c i < p) ∧ ∑ i, c i • e i = v) ∧
      ∀ c c' : Fin n → ℕ, (∀ i, c i < p) → (∀ i, c' i < p) →
        ∑ i, c i • e i = ∑ i, c' i • e i → c = c' := by
  classical
  obtain ⟨κ, _, n, hn, ⟨E0⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' V
  let E : V ≃+ ((i : κ) → ZMod (n i)) :=
    E0.trans (DirectSum.linearEquivFunOnFintype ℤ κ fun i => ZMod (n i)).toAddEquiv
  haveI : ∀ i, NeZero (n i) := fun i => ⟨(lt_trans zero_lt_one (hn i)).ne'⟩
  -- every cyclic factor has order `p`
  have hnp : ∀ i, n i = p := by
    intro i
    have h1 := congrArg E (hV (E.symm (Pi.single i 1)))
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, Pi.single_eq_same, mul_one, Pi.zero_apply,
      nsmul_eq_mul] at h2
    have h3 : n i ∣ p := by
      have h4 := (ZMod.natCast_eq_natCast_iff' p 0 (n i)).mp (by simpa using h2)
      exact Nat.dvd_of_mod_eq_zero (by simpa using h4)
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h | h
    · exact absurd h (hn i).ne'
    · exact h
  let σ : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let e : Fin (Fintype.card κ) → V := fun q => E.symm (Pi.single (σ q) 1)
  have hE : ∀ c : Fin (Fintype.card κ) → ℕ,
      E (∑ q, c q • e q) = fun i => ((c (σ.symm i) : ℕ) : ZMod (n i)) := by
    intro c
    rw [map_sum]
    funext i
    obtain ⟨q0, rfl⟩ := σ.surjective i
    simp only [e, map_nsmul, AddEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply,
      Equiv.symm_apply_apply]
    rw [Finset.sum_eq_single q0]
    · simp
    · intro q _ hq
      have : σ q ≠ σ q0 := fun h => hq (σ.injective h)
      simp [Pi.single_eq_of_ne' this]
    · simp
  refine ⟨Fintype.card κ, e, fun v => ⟨fun q => (E v (σ q)).val, fun q => ?_, ?_⟩, ?_⟩
  · have := ZMod.val_lt (E v (σ q)); have := hnp (σ q)
    show (E v (σ q)).val < p; omega
  · apply E.injective
    rw [hE]
    funext i
    obtain ⟨q, rfl⟩ := σ.surjective i
    rw [Equiv.symm_apply_apply, ZMod.natCast_zmod_val]
  · intro c c' hc hc' h
    have h2 := congrArg E h
    rw [hE, hE] at h2
    funext q
    have h3 := congrFun h2 (σ q)
    simp only [Equiv.symm_apply_apply] at h3
    rw [ZMod.natCast_eq_natCast_iff', hnp, Nat.mod_eq_of_lt (hc q), Nat.mod_eq_of_lt (hc' q)] at h3
    exact h3

section Layer

variable [Fact p.Prime]

/-- Every layer of a restricted N-series of a finite group has a basis. -/
theorem RestrictedSeries.exists_layerNF [Finite G] (T : RestrictedSeries p G) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (n : ℕ) (y : Fin n → G), LayerNF T k y := by
  classical
  have hp2 := (Fact.out : p.Prime).two_le
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : (T.S (k + 1)).Normal := T.normal (k + 1)
  set π := QuotientGroup.mk' (T.S (k + 1))
  set A := (T.S k).map π
  set φ : T.S k →* A := π.subgroupMap (T.S k)
  have hφ : ∀ a b : T.S k, φ a = φ b ↔ (a : G)⁻¹ * b ∈ T.S (k + 1) := by
    intro a b
    rw [Subtype.ext_iff, MonoidHom.subgroupMap_apply_coe, MonoidHom.subgroupMap_apply_coe]
    exact QuotientGroup.eq
  have hφs : Function.Surjective φ := π.subgroupMap_surjective (T.S k)
  -- `A` is commutative and has exponent `p`
  have hcomm : ∀ a b : A, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := hφs a
    obtain ⟨b, rfl⟩ := hφs b
    rw [← map_mul, ← map_mul, hφ]
    have h1 : ⁅(b : G)⁻¹, (a : G)⁻¹⁆ ∈ T.S (k + 1) :=
      T.mem_of_le (by omega) (by omega) (T.comm hk hk _ (inv_mem b.2) _ (inv_mem a.2))
    have e : ((a * b : T.S k) : G)⁻¹ * ((b * a : T.S k) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [commutatorElement_def, inv_inv, Subgroup.coe_mul]; group
    rw [e]; exact h1
  have hexp : ∀ a : A, a ^ p = 1 := by
    intro a
    obtain ⟨a, rfl⟩ := hφs a
    rw [← map_pow, ← map_one φ, hφ]
    have := T.mem_of_le (m := k + 1) (n := p * k) (by omega) (by nlinarith) (T.pow hk _ a.2)
    simpa using this
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  obtain ⟨n, e, hspan, huniq⟩ := exists_nsmul_basis (V := Additive A)
    (fun x : Additive A => hexp (Additive.toMul x))
  choose y' hy' using fun i : Fin n => hφs (Additive.toMul (e i))
  -- the class of an ordered product
  have hcl : ∀ c : Fin n → ℕ,
      Additive.ofMul (φ (lprod (ordL (Fin n)) y' c)) = ∑ i, c i • e i := by
    intro c
    rw [map_lprod]
    simp only [lprod, ofMul_list_prod, List.map_map, Function.comp_def, ofMul_pow, hy',
      ofMul_toMul]
    exact Frame.sum_ordL (fun i => c i • e i)
  have hco : ∀ c : Fin n → ℕ, lprod (ordL (Fin n)) (fun i => (y' i : G)) c =
      ((lprod (ordL (Fin n)) y' c : T.S k) : G) :=
    fun c => (map_lprod (T.S k).subtype _ y' c).symm
  refine ⟨n, fun i => (y' i : G), ⟨fun i => (y' i).2, ?_, ?_⟩⟩
  · intro g hg
    obtain ⟨c, hc, hcv⟩ := hspan (Additive.ofMul (φ ⟨g, hg⟩))
    refine ⟨c, hc, ?_⟩
    have h1 : φ (lprod (ordL (Fin n)) y' c) = φ ⟨g, hg⟩ := by
      apply Additive.ofMul.injective
      rw [hcl, hcv]
    rw [hφ] at h1
    rw [hco]; exact h1
  · intro c c' hc hc' hm
    rw [hco, hco, ← hφ] at hm
    refine huniq c c' hc hc' ?_
    rw [← hcl, ← hcl, hm]

end Layer

/-! ## Tail frames -/

/-- Normal forms of the elements of `S k` by letters of weight `≥ k`. -/
structure TailFrame (T : RestrictedSeries p G) (k : ℕ) (ι : Type*) [LinearOrder ι] [Fintype ι]
    where
  x : ι → G
  w : ι → ℕ
  w_ge : ∀ j, k ≤ w j
  w_mono : Monotone w
  mem : ∀ j, x j ∈ T.S (w j)
  nf : ∀ g ∈ T.S k, ∃ b : ι → ℕ, (∀ j, b j < p) ∧ lprod (ordL ι) x b = g
  nf_unique : ∀ b c : ι → ℕ, (∀ j, b j < p) → (∀ j, c j < p) →
    lprod (ordL ι) x b = lprod (ordL ι) x c → b = c
  wt : ∀ b : ι → ℕ, (∀ j, b j < p) → ∀ k', 1 ≤ k' →
    (lprod (ordL ι) x b ∈ T.S k' ↔ ∀ j, w j < k' → b j = 0)

namespace TailFrame

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- No letters: the series is trivial from `k` on. -/
def empty (k : ℕ) (hk : T.S k = ⊥) : TailFrame T k (Fin 0) where
  x := Fin.elim0
  w := Fin.elim0
  w_ge := fun j => j.elim0
  w_mono := fun j => j.elim0
  mem := fun j => j.elim0
  nf := fun g hg => by
    rw [hk, Subgroup.mem_bot] at hg
    subst hg
    exact ⟨fun j => j.elim0, fun j => j.elim0, by simp [lprod, ordL]⟩
  nf_unique := fun b c _ _ _ => funext fun j => j.elim0
  wt := fun b _ k' _ => by
    have : lprod (ordL (Fin 0)) (Fin.elim0 : Fin 0 → G) b = 1 := by simp [lprod, ordL]
    simp [this, one_mem]

variable {k : ℕ} (Tf : TailFrame T k ι)

theorem lprod_mem (hk : 1 ≤ k) (b : ι → ℕ) : lprod (ordL ι) Tf.x b ∈ T.S k :=
  T.lprod_mem (fun j _ => T.mem_of_le hk (Tf.w_ge j) (Tf.mem j)) b

end TailFrame

/-! ## Gluing a layer below a tail frame -/

section Glue

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {n k : ℕ} {y : Fin n → G}

/-- Gluing the layer `k` below a tail frame of `S (k+1)`. -/
def TailFrame.glue (hk : 1 ≤ k) (hp : 0 < p) (hy : LayerNF T k y) (Tf : TailFrame T (k + 1) ι) :
    TailFrame T k (Fin n ⊕ₗ ι) where
  x q := Sum.elim y Tf.x (ofLex q)
  w q := Sum.elim (fun _ => k) Tf.w (ofLex q)
  w_ge q := by
    rcases q with (i | j)
    · exact le_rfl
    · have := Tf.w_ge j; show k ≤ Tf.w j; omega
  w_mono q r hqr := by
    rcases q with (i | j) <;> rcases r with (i' | j')
    · exact le_rfl
    · have := Tf.w_ge j'; show k ≤ Tf.w j'; omega
    · exact absurd hqr (not_le.2 (Sum.Lex.inl_lt_inr _ _))
    · exact Tf.w_mono (Sum.Lex.inr_le_inr_iff.mp hqr)
  mem q := by
    rcases q with (i | j)
    · exact hy.mem i
    · exact Tf.mem j
  nf g hg := by
    obtain ⟨c, hc, hcg⟩ := hy.exists_nf g hg
    obtain ⟨b', hb', hb'g⟩ := Tf.nf _ hcg
    refine ⟨fun q => Sum.elim c b' (ofLex q), fun q => ?_, ?_⟩
    · rcases q with (i | j)
      · exact hc i
      · exact hb' j
    · rw [lprod_split]
      change lprod (ordL (Fin n)) y c * lprod (ordL ι) Tf.x b' = g
      rw [hb'g, mul_inv_cancel_left]
  nf_unique b c hb hc hbc := by
    rw [lprod_split, lprod_split] at hbc
    change lprod (ordL (Fin n)) y (b ∘ inlₗ) * lprod (ordL ι) Tf.x (b ∘ inrₗ) =
      lprod (ordL (Fin n)) y (c ∘ inlₗ) * lprod (ordL ι) Tf.x (c ∘ inrₗ) at hbc
    have hl : b ∘ inlₗ = c ∘ inlₗ := by
      refine hy.nf_unique _ _ (fun i => hb (inlₗ i)) (fun i => hc (inlₗ i)) ?_
      have e : (lprod (ordL (Fin n)) y (b ∘ inlₗ))⁻¹ * lprod (ordL (Fin n)) y (c ∘ inlₗ) =
          lprod (ordL ι) Tf.x (b ∘ inrₗ) * (lprod (ordL ι) Tf.x (c ∘ inrₗ))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hbc, mul_inv_cancel_right]
      rw [e]
      exact mul_mem (Tf.lprod_mem (by omega) _) (inv_mem (Tf.lprod_mem (by omega) _))
    have hr : b ∘ inrₗ = c ∘ inrₗ := by
      refine Tf.nf_unique _ _ (fun j => hb (inrₗ j)) (fun j => hc (inrₗ j)) ?_
      rw [hl] at hbc
      exact mul_left_cancel hbc
    funext q
    rcases q with (i | j)
    · exact congrFun hl i
    · exact congrFun hr j
  wt b hb k' hk' := by
    rw [lprod_split]
    change lprod (ordL (Fin n)) y (b ∘ inlₗ) * lprod (ordL ι) Tf.x (b ∘ inrₗ) ∈ _ ↔ _
    have hT := Tf.lprod_mem (by omega) (b ∘ inrₗ)
    have hL := hy.lprod_mem (b ∘ inlₗ)
    by_cases hkk : k' ≤ k
    · constructor
      · intro _ q hq
        rcases q with (i | j)
        · change k < k' at hq; omega
        · have := Tf.w_ge j; change Tf.w j < k' at hq; omega
      · intro _
        exact T.mem_of_le hk' hkk (mul_mem hL (T.mem_of_le hk (by omega) hT))
    · push Not at hkk
      constructor
      · intro hm
        have hl0 : b ∘ inlₗ = 0 := by
          have h1 : lprod (ordL (Fin n)) y (b ∘ inlₗ) ∈ T.S (k + 1) := by
            have := T.mem_of_le (by omega) (show k + 1 ≤ k' by omega) hm
            have e : lprod (ordL (Fin n)) y (b ∘ inlₗ) =
                lprod (ordL (Fin n)) y (b ∘ inlₗ) * lprod (ordL ι) Tf.x (b ∘ inrₗ) *
                  (lprod (ordL ι) Tf.x (b ∘ inrₗ))⁻¹ := by group
            rw [e]; exact mul_mem this (inv_mem hT)
          exact hy.eq_zero_of_mem (fun i => hb (inlₗ i)) h1 hp
        have e0 : lprod (ordL (Fin n)) y (b ∘ inlₗ) = 1 := by rw [hl0]; exact lprod_zero _ _
        rw [e0, one_mul] at hm
        have := (Tf.wt (b ∘ inrₗ) (fun j => hb (inrₗ j)) k' hk').mp hm
        intro q hq
        rcases q with (i | j)
        · exact congrFun hl0 i
        · exact this j hq
      · intro h0
        have hl0 : b ∘ inlₗ = 0 := funext fun i => h0 (inlₗ i) (by
          change k < k'; omega)
        rw [hl0, lprod_zero, one_mul]
        exact (Tf.wt (b ∘ inrₗ) (fun j => hb (inrₗ j)) k' hk').mpr fun j hj => h0 (inrₗ j) hj

end Glue

/-- A tail frame of `S 1 = G` is a frame. -/
def TailFrame.toFrame {ι : Type*} [LinearOrder ι] [Fintype ι] (Tf : TailFrame T 1 ι) :
    JFrame T ι where
  x := Tf.x
  w := Tf.w
  w_pos := Tf.w_ge
  w_mono := Tf.w_mono
  mem := Tf.mem
  nf g := Tf.nf g (T.mem_one g)
  nf_unique := Tf.nf_unique
  wt := Tf.wt

/-! ## Existence of a frame -/

variable [Fact p.Prime] [Finite G]

theorem RestrictedSeries.exists_tailFrame (T : RestrictedSeries p G) {N : ℕ} (hN : 1 ≤ N)
    (hbot : T.S N = ⊥) : ∀ d k, 1 ≤ k → N ≤ k + d →
      ∃ (ι : Type) (_ : LinearOrder ι) (_ : Fintype ι), Nonempty (TailFrame T k ι) := by
  intro d
  induction d with
  | zero =>
    intro k _ hk
    have : T.S k = ⊥ := eq_bot_iff.mpr (hbot ▸ T.antitone hN (by omega))
    exact ⟨Fin 0, inferInstance, inferInstance, ⟨TailFrame.empty k this⟩⟩
  | succ d ih =>
    intro k hk hkd
    obtain ⟨ι, _, _, ⟨Tf⟩⟩ := ih (k + 1) (by omega) (by omega)
    obtain ⟨n, y, hy⟩ := T.exists_layerNF hk
    exact ⟨Fin n ⊕ₗ ι, inferInstance, inferInstance,
      ⟨Tf.glue hk (Fact.out : p.Prime).pos hy⟩⟩

/-- **Every restricted N-series of a finite group has a frame.** -/
theorem RestrictedSeries.exists_frame (T : RestrictedSeries p G) :
    ∃ (ι : Type) (_ : LinearOrder ι) (_ : Fintype ι), Nonempty (JFrame T ι) := by
  obtain ⟨N, hN, hbot⟩ := T.eventually
  obtain ⟨ι, _, _, ⟨Tf⟩⟩ := T.exists_tailFrame hN hbot N 1 le_rfl (by omega)
  exact ⟨ι, inferInstance, inferInstance, ⟨Tf.toFrame⟩⟩

end Jennings

end GroupDimension
