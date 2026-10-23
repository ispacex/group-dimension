import GroupDimension.Basic

/-!
# A representation that kills `Δ^k`

Let `f : G →* A` be a multiplicative map of a group into a ring and `s : ι → G` a generating
family. If every product `(f(s i₁) - 1) ⋯ (f(s i_k) - 1)` of `k` factors vanishes, then `f`
extends to a ring map `ℤ[G] → A` that kills `Δ(G)^k`, so `f g = 1` for every `g ∈ D_k(G)`
(`map_eq_one_of_mem_D`).

The proof: let `𝔐_j ⊆ A` be the `ℤ`-span of the products of at least `j` factors `f(s i) - 1`.
Then `𝔐_a 𝔐_b ⊆ 𝔐_{a+b}`, `𝔐_k = 0`, and `f g - 1 ∈ 𝔐_1` for all `g` (the set of such `g`
contains the generators and is closed under products and, since `𝔐_1` is nilpotent, under
inverses). Hence `Δ^j` maps into `𝔐_j`.
-/

namespace GroupDimension.Cert1024

open MonoidAlgebra

variable {A : Type*} [Ring A] {ι : Type*}

/-- `𝔐_j`: the `ℤ`-span of the products of at least `j` elements of `N`. -/
def prodSpan (N : ι → A) (j : ℕ) : Submodule ℤ A :=
  Submodule.span ℤ {x | ∃ l : List ι, j ≤ l.length ∧ x = (l.map N).prod}

variable (N : ι → A)

theorem prod_mem_prodSpan {j : ℕ} (l : List ι) (hl : j ≤ l.length) :
    (l.map N).prod ∈ prodSpan N j :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem prodSpan_anti {i j : ℕ} (h : i ≤ j) : prodSpan N j ≤ prodSpan N i :=
  Submodule.span_mono fun _ ⟨l, hl, e⟩ => ⟨l, h.trans hl, e⟩

theorem one_mem_prodSpan_zero : (1 : A) ∈ prodSpan N 0 := by
  simpa using prod_mem_prodSpan N (j := 0) [] le_rfl

theorem mul_mem_prodSpan {a b : ℕ} {x y : A} (hx : x ∈ prodSpan N a) (hy : y ∈ prodSpan N b) :
    x * y ∈ prodSpan N (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l', hl', rfl⟩ := hy
      rw [← List.prod_append, ← List.map_append]
      exact prod_mem_prodSpan N _ (by simp; omega)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- If all products of `k` factors vanish, `𝔐_k = 0`. -/
theorem prodSpan_eq_bot {k : ℕ} (h : ∀ l : List ι, l.length = k → (l.map N).prod = 0) :
    prodSpan N k = ⊥ := by
  rw [eq_bot_iff, prodSpan, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot, ← List.take_append_drop k l, List.map_append,
    List.prod_append, h _ (by simp; omega), zero_mul]

variable {G : Type*} [Group G]

/-- `f g - 1 ∈ 𝔐_1` for every `g`, when `f(s i) - 1 = N i` and `𝔐_k = 0`. -/
theorem sub_one_mem_prodSpan (f : G →* A) (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (hN : ∀ i, f (s i) - 1 = N i) {k : ℕ} (hk : prodSpan N k = ⊥) (g : G) :
    f g - 1 ∈ prodSpan N 1 := by
  -- powers of an element of `𝔐_1`
  have hpow : ∀ {a : A}, a ∈ prodSpan N 1 → ∀ j, a ^ (j + 1) ∈ prodSpan N (j + 1) := by
    intro a ha j
    induction j with
    | zero => simpa using ha
    | succ j ih => rw [pow_succ]; exact mul_mem_prodSpan N ih ha
  have hnil : ∀ {a : A}, a ∈ prodSpan N 1 → ∃ n, a ^ n = 0 := fun ha =>
    ⟨k + 1, by
      have := prodSpan_anti N (Nat.le_succ k) (hpow ha k)
      rwa [hk, Submodule.mem_bot] at this⟩
  let H : Subgroup G :=
    { carrier := {g | f g - 1 ∈ prodSpan N 1}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul] at *
        have e : f a * f b - 1 = (f a - 1) * (f b - 1) + (f a - 1) + (f b - 1) := by noncomm_ring
        rw [e]
        exact add_mem (add_mem (prodSpan_anti N (by norm_num) (mul_mem_prodSpan N ha hb)) ha) hb
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        set t := f a - 1 with ht
        obtain ⟨n0, hn0⟩ := hnil (neg_mem ha)
        have hn : (-t) ^ (n0 + 1) = 0 := by rw [pow_succ, hn0, zero_mul]
        have geom : ∀ n, (1 + t) * ∑ j ∈ Finset.range n, (-t) ^ j = 1 - (-t) ^ n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
            have hc : t * (-t) ^ n = (-t) ^ n * t := ((Commute.refl t).neg_right.pow_right n).eq
            rw [add_mul, one_mul, hc]
            simp only [mul_neg]
            abel
        set q : A := ∑ j ∈ Finset.range (n0 + 1), (-t) ^ j with hq
        have hgeom : (1 + t) * q = 1 := by rw [hq, geom, hn, sub_zero]
        have hfa : f a = 1 + t := by rw [ht]; abel
        have hinv : f a⁻¹ = q := by
          have : f a⁻¹ * f a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
          calc f a⁻¹ = f a⁻¹ * ((1 + t) * q) := by rw [hgeom, mul_one]
            _ = q := by rw [← mul_assoc, ← hfa, this, one_mul]
        rw [hinv, hq]
        have hs : ∀ n, (∑ j ∈ Finset.range (n + 1), (-t) ^ j) - 1 ∈ prodSpan N 1 := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            rw [Finset.sum_range_succ]
            have e : (∑ j ∈ Finset.range (n + 1), (-t) ^ j) + (-t) ^ (n + 1) - 1 =
              ((∑ j ∈ Finset.range (n + 1), (-t) ^ j) - 1) + (-t) ^ (n + 1) := by abel
            rw [e]
            exact add_mem ih (prodSpan_anti N (by omega) (hpow (neg_mem ha) n))
        exact hs n0 }
  have hle : Subgroup.closure (Set.range s) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show f (s i) - 1 ∈ prodSpan N 1
    rw [hN i]
    simpa using prod_mem_prodSpan N [i] le_rfl
  exact hle (hs ▸ Subgroup.mem_top g)

/-- **The extension kills `Δ^k`.** With `f(s i) - 1 = N i`, generators `s`, and all products of
`k` of the `N i` zero, the ring map `ℤ[G] → A` induced by `f` maps `Δ(G)^k` to `0`; hence
`f g = 1` for `g ∈ D_k(G)`. -/
theorem map_eq_one_of_mem_D (f : G →* A) (s : ι → G) (hs : Subgroup.closure (Set.range s) = ⊤)
    (hN : ∀ i, f (s i) - 1 = N i) {k : ℕ} (h : ∀ l : List ι, l.length = k → (l.map N).prod = 0)
    {g : G} (hg : g ∈ D k G) : f g = 1 := by
  have hk := prodSpan_eq_bot N h
  have h1 := sub_one_mem_prodSpan N f s hs hN hk
  let φ := (MonoidAlgebra.lift ℤ A G f).toRingHom
  have hφof : ∀ x : G, φ (of ℤ G x) = f x := fun x => by simp [φ]
  -- `φ(y) z ∈ 𝔐_j` for `z ∈ 𝔐_j`
  have hleft : ∀ (y : MonoidAlgebra ℤ G) {j} {z : A}, z ∈ prodSpan N j → φ y * z ∈ prodSpan N j := by
    intro y j z hz
    induction y using MonoidAlgebra.induction_on with
    | hM x =>
      rw [hφof]
      have e : f x * z = (f x - 1) * z + z := by noncomm_ring
      rw [e]
      exact add_mem (prodSpan_anti N (by omega) (mul_mem_prodSpan N (h1 x) hz)) hz
    | hadd a b ha hb => rw [map_add, add_mul]; exact add_mem ha hb
    | hsmul c a ha =>
      have key : ∀ (c : ℤ) (a : MonoidAlgebra ℤ G), φ a * z ∈ prodSpan N j →
          φ (c • a) * z ∈ prodSpan N j := by
        intro c a ha
        rw [map_zsmul, smul_mul_assoc]
        exact Submodule.smul_of_tower_mem _ c ha
      exact key c a ha
  -- the left ideals `P_j = φ⁻¹(𝔐_j)`
  let P : ℕ → Ideal (MonoidAlgebra ℤ G) := fun j =>
    { carrier := {x | φ x ∈ prodSpan N j}
      add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq, map_add] at *; exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        exact hleft c hx }
  -- `Δ ≤ P_1`
  have hΔ : augIdeal G ≤ P 1 := by
    intro x hx
    have key : ∀ y : MonoidAlgebra ℤ G, φ y - (augmentation G y : A) ∈ prodSpan N 1 := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | hM x => rw [hφof, augmentation_of, Int.cast_one]; exact h1 x
      | hadd a b ha hb =>
        rw [map_add, map_add, Int.cast_add]
        have e : φ a + φ b - ((augmentation G a : A) + augmentation G b) =
          (φ a - augmentation G a) + (φ b - augmentation G b) := by abel
        rw [e]; exact add_mem ha hb
      | hsmul c a ha =>
        have key : ∀ (c : ℤ) (a : MonoidAlgebra ℤ G),
            φ a - ((augmentation G a : ℤ) : A) ∈ prodSpan N 1 →
            φ (c • a) - ((augmentation G (c • a) : ℤ) : A) ∈ prodSpan N 1 := by
          intro c a ha
          have e : φ (c • a) - ((augmentation G (c • a) : ℤ) : A) =
              c • (φ a - (augmentation G a : A)) := by
            rw [map_zsmul, map_zsmul, smul_eq_mul, Int.cast_mul, smul_sub, zsmul_eq_mul,
              zsmul_eq_mul]
          rw [e]
          exact Submodule.smul_of_tower_mem _ c ha
        exact key c a ha
    have := key x
    rwa [(mem_augIdeal).mp hx, Int.cast_zero, sub_zero] at this
  -- `Δ^j ≤ P_j`
  have hpow : ∀ j, augIdeal G ^ j ≤ P j := by
    intro j
    induction j with
    | zero =>
      intro x _
      show φ x ∈ prodSpan N 0
      simpa using hleft x (one_mem_prodSpan_zero N)
    | succ j ih =>
      rw [Submodule.pow_succ, Ideal.mul_le]
      intro r hr t ht
      show φ (r * t) ∈ prodSpan N (j + 1)
      rw [map_mul]
      exact mul_mem_prodSpan N (ih hr) (hΔ ht)
  have hmem : φ (of ℤ G g - 1) ∈ prodSpan N k := hpow k ((mem_D).mp hg)
  rw [hk, Submodule.mem_bot, _root_.map_sub, _root_.map_one, hφof] at hmem
  exact sub_eq_zero.mp hmem

end GroupDimension.Cert1024
