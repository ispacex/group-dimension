module

public import Mathlib

@[expose] public section

/-!
# Normal words of a polycyclic presentation with relative orders `2`

Let `g_0, …, g_{m-1}` generate a group `G`, and suppose that for all `k < l`

  `g_k² ∈ ⟨g_{k+1}, …, g_{m-1}⟩`  and  `g_k⁻¹ g_l g_k ∈ ⟨g_{k+1}, …, g_{m-1}⟩`.

Then every element of `G` is a normal word `g_0^{e_0} g_1^{e_1} ⋯ g_{m-1}^{e_{m-1}}`,
`e_k ∈ {0, 1}` (`exists_nwFrom_zero`); in particular `|G| ≤ 2^m`. This is the standard bound for a
pc presentation, and it is all that is used about the presentations of the candidates: the
certificate then shows that the `2^m` normal words act by distinct operators.
-/

namespace GroupDimension.Cert1024

section Monoid

variable {M : Type*} [Monoid M] {m : ℕ}

/-- The normal word `g_i^{e_i} g_{i+1}^{e_{i+1}} ⋯ g_{m-1}^{e_{m-1}}`. -/
def nwFrom (g : Fin m → M) (e : Fin m → Bool) (i : ℕ) : M :=
  if h : i < m then (if e ⟨i, h⟩ then g ⟨i, h⟩ else 1) * nwFrom g e (i + 1) else 1
termination_by m - i

theorem nwFrom_of_lt (g : Fin m → M) (e : Fin m → Bool) {i : ℕ} (h : i < m) :
    nwFrom g e i = (if e ⟨i, h⟩ then g ⟨i, h⟩ else 1) * nwFrom g e (i + 1) := by
  rw [nwFrom, dif_pos h]

theorem nwFrom_of_le (g : Fin m → M) (e : Fin m → Bool) {i : ℕ} (h : m ≤ i) :
    nwFrom g e i = 1 := by
  rw [nwFrom, dif_neg (by omega)]

/-- Induction from `m` down to `i`. -/
theorem nwFrom_induction {P : ℕ → Prop} (htop : ∀ i, m ≤ i → P i)
    (hstep : ∀ i, i < m → P (i + 1) → P i) : ∀ i, P i := by
  intro i
  induction h : m - i using Nat.strong_induction_on generalizing i with
  | _ t ih =>
    by_cases hi : i < m
    · exact hstep i hi (ih (m - (i + 1)) (by omega) (i + 1) rfl)
    · exact htop i (by omega)

theorem map_nwFrom {N : Type*} [Monoid N] (f : M →* N) (g : Fin m → M) (e : Fin m → Bool)
    (i : ℕ) : f (nwFrom g e i) = nwFrom (fun k => f (g k)) e i := by
  induction i using nwFrom_induction (m := m) with
  | htop i h => rw [nwFrom_of_le _ _ h, nwFrom_of_le _ _ h, map_one]
  | hstep i h ih =>
    rw [nwFrom_of_lt _ _ h, nwFrom_of_lt _ _ h, map_mul, ih]
    split_ifs <;> simp

/-- A normal word from `i` on only depends on `e_i, …, e_{m-1}`. -/
theorem nwFrom_congr (g : Fin m → M) {e e' : Fin m → Bool} {i : ℕ}
    (h : ∀ k : Fin m, i ≤ k.val → e k = e' k) : nwFrom g e i = nwFrom g e' i := by
  induction i using nwFrom_induction (m := m) with
  | htop i hi => rw [nwFrom_of_le _ _ hi, nwFrom_of_le _ _ hi]
  | hstep i hi ih =>
    rw [nwFrom_of_lt _ _ hi, nwFrom_of_lt _ _ hi, h ⟨i, hi⟩ le_rfl,
      ih fun k hk => h k (by omega)]

/-- Leading zero exponents can be skipped. -/
theorem nwFrom_skip (g : Fin m → M) (e : Fin m → Bool) {i j : ℕ} (hij : i ≤ j)
    (h : ∀ k : Fin m, k.val < j → e k = false) : nwFrom g e i = nwFrom g e j := by
  induction hd : j - i generalizing i with
  | zero => rw [show i = j by omega]
  | succ t ih =>
    have hi : i < m ∨ m ≤ i := lt_or_ge i m
    rcases hi with hi | hi
    · rw [nwFrom_of_lt _ _ hi, h ⟨i, hi⟩ (show i < j by omega), if_neg (by simp), one_mul]
      exact ih (by omega) (by omega)
    · rw [nwFrom_of_le _ _ hi, nwFrom_of_le _ _ (by omega)]

end Monoid

section Group

variable {G : Type*} [Group G] {m : ℕ}

/-- `⟨g_i, g_{i+1}, …, g_{m-1}⟩`. -/
def tail (g : Fin m → G) (i : ℕ) : Subgroup G :=
  Subgroup.closure (g '' {k | i ≤ k.val})

theorem tail_anti (g : Fin m → G) {i j : ℕ} (h : i ≤ j) : tail g j ≤ tail g i :=
  Subgroup.closure_mono (Set.image_mono fun k (hk : j ≤ k.val) => (h.trans hk : i ≤ k.val))

theorem mem_tail (g : Fin m → G) {i : ℕ} (k : Fin m) (hk : i ≤ k.val) : g k ∈ tail g i :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem nwFrom_mem_tail (g : Fin m → G) (e : Fin m → Bool) (i : ℕ) : nwFrom g e i ∈ tail g i := by
  induction i using nwFrom_induction (m := m) with
  | htop i hi => rw [nwFrom_of_le _ _ hi]; exact one_mem _
  | hstep i hi ih =>
    rw [nwFrom_of_lt _ _ hi]
    refine mul_mem ?_ (tail_anti g (Nat.le_succ i) ih)
    split_ifs
    · exact mem_tail g ⟨i, hi⟩ le_rfl
    · exact one_mem _

/-- **Normal words.** Under the pc conditions every element of `⟨g_i, …, g_{m-1}⟩` is a normal
word from `i` on. -/
theorem exists_nwFrom (g : Fin m → G)
    (hpow : ∀ k : Fin m, g k ^ 2 ∈ tail g (k.val + 1))
    (hconj : ∀ k l : Fin m, k < l → (g k)⁻¹ * g l * g k ∈ tail g (k.val + 1)) :
    ∀ i, ∀ x ∈ tail g i, ∃ e, x = nwFrom g e i := by
  intro i
  induction i using nwFrom_induction (m := m) with
  | htop i hi =>
    intro x hx
    have : tail g i = ⊥ := by
      rw [tail, Subgroup.closure_eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      exact absurd (k.isLt) (by simp only [Set.mem_ofPred_eq] at hk; omega)
    rw [this, Subgroup.mem_bot] at hx
    exact ⟨fun _ => false, by rw [hx, nwFrom_of_le _ _ hi]⟩
  | hstep i hi ih =>
    set K := tail g (i + 1)
    set a := g ⟨i, hi⟩
    have ha2 : a ^ 2 ∈ K := hpow ⟨i, hi⟩
    -- `a⁻¹ K a ⊆ K`
    have hn : ∀ y ∈ K, a⁻¹ * y * a ∈ K := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hy
        exact hconj ⟨i, hi⟩ l (by simp only [Set.mem_ofPred_eq] at hl; exact Fin.mk_lt_of_lt_val (by omega))
      | one => simp
      | mul x y _ _ hx hy =>
        have : a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
        rw [this]; exact mul_mem hx hy
      | inv x _ hx =>
        have : a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by group
        rw [this]; exact inv_mem hx
    let S : Subgroup G :=
      { carrier := {x | x ∈ K ∨ a⁻¹ * x ∈ K}
        one_mem' := Or.inl (one_mem K)
        mul_mem' := by
          rintro x y (hx | hx) (hy | hy)
          · exact Or.inl (mul_mem hx hy)
          · refine Or.inr ?_
            have : a⁻¹ * (x * y) = (a⁻¹ * x * a) * (a⁻¹ * y) := by group
            rw [this]; exact mul_mem (hn x hx) hy
          · refine Or.inr ?_
            have : a⁻¹ * (x * y) = (a⁻¹ * x) * y := by group
            rw [this]; exact mul_mem hx hy
          · refine Or.inl ?_
            have : x * y = a ^ 2 * (a⁻¹ * (a⁻¹ * x) * a) * (a⁻¹ * y) := by group
            rw [this]; exact mul_mem (mul_mem ha2 (hn _ hx)) hy
        inv_mem' := by
          rintro x (hx | hx)
          · exact Or.inl (inv_mem hx)
          · refine Or.inr ?_
            have : a⁻¹ * x⁻¹ = (a⁻¹ * (a⁻¹ * x)⁻¹ * a) * (a ^ 2)⁻¹ := by group
            rw [this]; exact mul_mem (hn _ (inv_mem hx)) (inv_mem ha2) }
    have hle : tail g i ≤ S := by
      rw [tail, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      simp only [Set.mem_ofPred_eq] at hk
      rcases Nat.eq_or_lt_of_le hk with h | h
      · have : k = ⟨i, hi⟩ := Fin.ext h.symm
        subst this
        exact Or.inr (by rw [inv_mul_cancel]; exact one_mem K)
      · exact Or.inl (mem_tail g k h)
    intro x hx
    have hc : ∀ (e : Fin m → Bool) (bb : Bool),
        nwFrom g (Function.update e ⟨i, hi⟩ bb) (i + 1) = nwFrom g e (i + 1) := fun e bb =>
      nwFrom_congr g fun k hk => Function.update_of_ne (fun h => by rw [h] at hk; simp at hk) _ _
    rcases hle hx with hx | hx
    · obtain ⟨e, he⟩ := ih x hx
      refine ⟨Function.update e ⟨i, hi⟩ false, ?_⟩
      rw [nwFrom_of_lt _ _ hi, Function.update_self, if_neg (by simp), one_mul, hc, he]
    · obtain ⟨e, he⟩ := ih _ hx
      refine ⟨Function.update e ⟨i, hi⟩ true, ?_⟩
      rw [nwFrom_of_lt _ _ hi, Function.update_self, if_pos rfl, hc, ← he, mul_inv_cancel_left]

/-- Every element of a group generated by `g` (with the pc conditions) is a normal word. -/
theorem exists_nwFrom_zero (g : Fin m → G) (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hpow : ∀ k : Fin m, g k ^ 2 ∈ tail g (k.val + 1))
    (hconj : ∀ k l : Fin m, k < l → (g k)⁻¹ * g l * g k ∈ tail g (k.val + 1)) (x : G) :
    ∃ e, x = nwFrom g e 0 := by
  refine exists_nwFrom g hpow hconj 0 x ?_
  have : tail g 0 = ⊤ := by
    rw [tail, ← hgen]
    congr 1
    ext y; simp
  rw [this]; exact Subgroup.mem_top x

end Group

end GroupDimension.Cert1024
