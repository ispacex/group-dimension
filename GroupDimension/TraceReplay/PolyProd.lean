module

public import GroupDimension.Basic
public import GroupDimension.CentralRoot

@[expose] public section

/-!
# Products of polynomial maps (MATH-314; Passi, docs §3.2(e), point 2)

A function `φ : G → ℤ` is a *polynomial map of degree `≤ p`* when its linear extension
`lin φ : ℤ[G] → ℤ` vanishes on `Δ^{p+1}`. The pointwise product of polynomial maps of degrees
`≤ p` and `≤ q` is a polynomial map of degree `≤ p + q` (`lin_mul_eq_zero`).

The proof is a covering formula. For `l = [g_1, …, g_N]` let `E l = Π (g_k − 1)`. Then
`lin (φ·χ) (E l) = Σ lin φ (E T) · lin χ (E U)`, over the pairs of sublists `T, U` of `l` with
`T ∪ U = l` (`lin_mul_E`; the sum is `cov`, a recursion over `l`: each letter goes to `T`, to `U`, or
to both). As `|T| + |U| ≥ N`, one factor vanishes when `N ≥ p + q + 1`, and `Δ^N` is spanned by the
`E l` with `|l| = N` (`pow_le_spanE`). The same formula, with letters for group elements
(`covW`), is how the trace replay computes a product map on a monomial.
-/

namespace GroupDimension.TraceReplay

open MonoidAlgebra

section PolyProd

variable {G : Type*} [Group G]

/-- The linear extension of `φ : G → ℤ` to `ℤ[G]`. -/
noncomputable def lin (φ : G → ℤ) : MonoidAlgebra ℤ G →+ ℤ :=
  (Finsupp.linearCombination ℤ φ).toAddMonoidHom.comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

omit [Group G] in
theorem lin_single (φ : G → ℤ) (g : G) (a : ℤ) : lin φ (single g a) = a * φ g := by
  show Finsupp.linearCombination ℤ φ (Finsupp.single g a) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem lin_of (φ : G → ℤ) (g : G) : lin φ (of ℤ G g) = φ g := by
  rw [show of ℤ G g = single g 1 from rfl, lin_single, one_mul]

theorem lin_one (φ : G → ℤ) : lin φ (1 : MonoidAlgebra ℤ G) = φ 1 := by
  rw [← map_one (of ℤ G), lin_of]

/-- Left translation: `lin φ (g x) = lin φ_g x`, `φ_g h = φ (g h)`. -/
theorem lin_of_mul (φ : G → ℤ) (g : G) (x : MonoidAlgebra ℤ G) :
    lin φ (of ℤ G g * x) = lin (fun h => φ (g * h)) x := by
  induction x using MonoidAlgebra.induction_on with
  | of h => rw [← map_mul, lin_of, lin_of]
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy]
  | smul r x hx => rw [mul_smul_comm, map_zsmul, map_zsmul, hx]

/-- `E l = Π (g − 1)` over `g ∈ l`, in order. -/
noncomputable def E (l : List G) : MonoidAlgebra ℤ G := (l.map fun g => of ℤ G g - 1).prod

theorem E_nil : E ([] : List G) = 1 := rfl

theorem E_cons (g : G) (l : List G) : E (g :: l) = (of ℤ G g - 1) * E l := by
  simp [E]

theorem E_append (a b : List G) : E (a ++ b) = E a * E b := by
  simp [E, List.map_append, List.prod_append]

theorem E_mem (l : List G) : E l ∈ augIdeal G ^ l.length := by
  induction l with
  | nil => rw [E_nil, List.length_nil, Submodule.pow_zero]; exact Submodule.one_le.mp le_rfl
  | cons g l ih =>
    rw [E_cons, List.length_cons, add_comm]
    have h1 : of ℤ G g - 1 ∈ augIdeal G ^ 1 := by rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal g
    exact mul_mem_augIdeal_pow h1 ih

variable (φ χ : G → ℤ)

/-- The covering sum `Σ_{T ∪ U = l} lin φ (a · E T) · lin χ (b · E U)`, by recursion over `l`. -/
noncomputable def cov : MonoidAlgebra ℤ G → MonoidAlgebra ℤ G → List G → ℤ
  | a, b, [] => lin φ a * lin χ b
  | a, b, g :: l => cov (a * (of ℤ G g - 1)) b l + cov a (b * (of ℤ G g - 1)) l +
      cov (a * (of ℤ G g - 1)) (b * (of ℤ G g - 1)) l

theorem cov_add_left (l : List G) : ∀ a a' b : MonoidAlgebra ℤ G,
    cov φ χ (a + a') b l = cov φ χ a b l + cov φ χ a' b l := by
  induction l with
  | nil => intro a a' b; simp only [cov, map_add, add_mul]
  | cons g l ih => intro a a' b; simp only [cov, add_mul, ih]; ring

theorem cov_add_right (l : List G) : ∀ a b b' : MonoidAlgebra ℤ G,
    cov φ χ a (b + b') l = cov φ χ a b l + cov φ χ a b' l := by
  induction l with
  | nil => intro a b b'; simp only [cov, map_add, mul_add]
  | cons g l ih => intro a b b'; simp only [cov, add_mul, ih]; ring

/-- Translating both maps by `g` is multiplying both prefixes by `g` on the left. -/
theorem cov_translate (g : G) (l : List G) : ∀ a b : MonoidAlgebra ℤ G,
    cov (fun h => φ (g * h)) (fun h => χ (g * h)) a b l = cov φ χ (of ℤ G g * a) (of ℤ G g * b) l := by
  induction l with
  | nil => intro a b; simp only [cov, lin_of_mul]
  | cons h l ih => intro a b; simp only [cov, ih, mul_assoc]

/-- **The covering formula.** `lin (φ·χ) (E l) = cov φ χ 1 1 l`. -/
theorem lin_mul_E (l : List G) :
    ∀ φ χ : G → ℤ, lin (fun g => φ g * χ g) (E l) = cov φ χ 1 1 l := by
  induction l with
  | nil => intro φ χ; simp only [E_nil, cov, lin_one]
  | cons g l ih =>
    intro φ χ
    have e1 : lin (fun h => φ h * χ h) (E (g :: l)) =
        lin (fun h => φ (g * h) * χ (g * h)) (E l) - lin (fun h => φ h * χ h) (E l) := by
      rw [E_cons, sub_mul, one_mul, map_sub, lin_of_mul]
    rw [e1, ih (fun h => φ (g * h)) (fun h => χ (g * h)), ih φ χ, cov_translate, mul_one]
    have e2 : of ℤ G g = (of ℤ G g - 1) + 1 := by abel
    rw [e2, cov_add_left, cov_add_right, cov_add_right]
    simp only [cov, one_mul]
    ring

/-- One factor vanishes on every leaf when the prefixes and the list are long enough. -/
theorem cov_eq_zero {p q : ℕ} (hφ : ∀ x ∈ augIdeal G ^ (p + 1), lin φ x = 0)
    (hχ : ∀ x ∈ augIdeal G ^ (q + 1), lin χ x = 0) (l : List G) :
    ∀ (i j : ℕ) (a b : MonoidAlgebra ℤ G), a ∈ augIdeal G ^ i → b ∈ augIdeal G ^ j →
      p + q + 1 ≤ i + j + l.length → cov φ χ a b l = 0 := by
  induction l with
  | nil =>
    intro i j a b ha hb h
    simp only [List.length_nil, add_zero] at h
    simp only [cov]
    rcases Nat.lt_or_ge p i with hi | hi
    · rw [hφ a (Ideal.pow_le_pow_right (by omega) ha), zero_mul]
    · rw [hχ b (Ideal.pow_le_pow_right (by omega) hb), mul_zero]
  | cons g l ih =>
    intro i j a b ha hb h
    simp only [List.length_cons] at h
    have hg : of ℤ G g - 1 ∈ augIdeal G ^ 1 := by rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal g
    have ha' := mul_mem_augIdeal_pow ha hg
    have hb' := mul_mem_augIdeal_pow hb hg
    simp only [cov]
    rw [ih (i + 1) j _ _ ha' hb (by omega), ih i (j + 1) _ _ ha hb' (by omega),
      ih (i + 1) (j + 1) _ _ ha' hb' (by omega)]
    ring

/-- `Δ^{N+1}` is spanned over `ℤ` by the `E l`, `|l| = N + 1`. -/
theorem pow_le_spanE (N : ℕ) :
    ((augIdeal G ^ (N + 1)).restrictScalars ℤ : Submodule ℤ (MonoidAlgebra ℤ G)) ≤
      Submodule.span ℤ {x | ∃ l : List G, l.length = N + 1 ∧ x = E l} := by
  induction N with
  | zero =>
    intro x hx
    rw [Submodule.restrictScalars_mem, zero_add, Submodule.pow_one] at hx
    refine CentralRoot.augIdeal_induction
      (p := fun x => x ∈ Submodule.span ℤ {x | ∃ l : List G, l.length = 0 + 1 ∧ x = E l}) hx
      (zero_mem _) (fun g => Submodule.subset_span ⟨[g], rfl, by simp [E]⟩)
      (fun y h => neg_mem h) (fun y z h h' => add_mem h h')
  | succ N ih =>
    intro x hx
    rw [Submodule.restrictScalars_mem, Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun _ _ h h' => add_mem h h')
    have ha' : a ∈ Submodule.span ℤ {x | ∃ l : List G, l.length = N + 1 ∧ x = E l} := ih ha
    refine CentralRoot.augIdeal_induction
      (p := fun b => a * b ∈ Submodule.span ℤ {x | ∃ l : List G, l.length = N + 1 + 1 ∧ x = E l}) hb
      (by rw [mul_zero]; exact zero_mem _) ?_ (fun y h => by rw [mul_neg]; exact neg_mem h)
      (fun y z h h' => by rw [mul_add]; exact add_mem h h')
    intro g
    clear ha
    induction ha' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ [g], by simp [hl], ?_⟩
      rw [E_append]; simp [E]
    | zero => rw [zero_mul]; exact zero_mem _
    | add y z _ _ hy hz => rw [add_mul]; exact add_mem hy hz
    | smul c y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hy

/-- **Passi's product rule.** If `lin φ` vanishes on `Δ^{p+1}` and `lin χ` on `Δ^{q+1}`, then
`lin (φ·χ)` vanishes on `Δ^{p+q+1}`. -/
theorem lin_mul_eq_zero {p q : ℕ} (hφ : ∀ x ∈ augIdeal G ^ (p + 1), lin φ x = 0)
    (hχ : ∀ x ∈ augIdeal G ^ (q + 1), lin χ x = 0) :
    ∀ x ∈ augIdeal G ^ (p + q + 1), lin (fun g => φ g * χ g) x = 0 := by
  intro x hx
  have hx' := pow_le_spanE (G := G) (p + q) (by rwa [Submodule.restrictScalars_mem])
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    rw [lin_mul_E]
    have h1 : (1 : MonoidAlgebra ℤ G) ∈ augIdeal G ^ 0 := by
      rw [Submodule.pow_zero]; exact Submodule.one_le.mp le_rfl
    exact cov_eq_zero φ χ hφ hχ l 0 0 1 1 h1 h1 (by omega)
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_zsmul, hy, smul_zero]

/-! ## The covering sum on words -/

/-- `cov` with words for the prefixes: `F a · H b` at the leaves, `a, b` the letters chosen so far. -/
def covW (F H : List ℕ → ℤ) : List ℕ → List ℕ → List ℕ → ℤ
  | a, b, [] => F a * H b
  | a, b, j :: l => covW F H (a ++ [j]) b l + covW F H a (b ++ [j]) l + covW F H (a ++ [j]) (b ++ [j]) l

theorem cov_eq_covW (g : ℕ → G) (P : ℕ → Prop) (F H : List ℕ → ℤ)
    (hF : ∀ w, (∀ j ∈ w, P j) → lin φ (E (w.map g)) = F w)
    (hH : ∀ w, (∀ j ∈ w, P j) → lin χ (E (w.map g)) = H w) (l : List ℕ) (hl : ∀ j ∈ l, P j) :
    ∀ a b : List ℕ, (∀ j ∈ a, P j) → (∀ j ∈ b, P j) →
      cov φ χ (E (a.map g)) (E (b.map g)) (l.map g) = covW F H a b l := by
  induction l with
  | nil => intro a b ha hb; simp only [List.map_nil, cov, covW, hF a ha, hH b hb]
  | cons j l ih =>
    intro a b ha hb
    have hj : P j := hl j List.mem_cons_self
    have hl' : ∀ i ∈ l, P i := fun i hi => hl i (List.mem_cons_of_mem _ hi)
    have ej : ∀ c : List ℕ, E (c.map g) * (of ℤ G (g j) - 1) = E ((c ++ [j]).map g) := by
      intro c; rw [List.map_append, E_append]; simp [E]
    have hc : ∀ c : List ℕ, (∀ i ∈ c, P i) → ∀ i ∈ c ++ [j], P i := by
      intro c hc i hi
      rcases List.mem_append.mp hi with h | h
      · exact hc i h
      · rw [List.mem_singleton.mp h]; exact hj
    simp only [List.map_cons, cov, covW, ej]
    rw [ih hl' _ _ (hc a ha) hb, ih hl' _ _ ha (hc b hb), ih hl' _ _ (hc a ha) (hc b hb)]

/-- The value of `φ·χ` on `E (w.map g)` from the values of `φ` and `χ` on sub-words. -/
theorem lin_mul_E_map (g : ℕ → G) (P : ℕ → Prop) (F H : List ℕ → ℤ)
    (hF : ∀ w, (∀ j ∈ w, P j) → lin φ (E (w.map g)) = F w)
    (hH : ∀ w, (∀ j ∈ w, P j) → lin χ (E (w.map g)) = H w) (w : List ℕ) (hw : ∀ j ∈ w, P j) :
    lin (fun x => φ x * χ x) (E (w.map g)) = covW F H [] [] w := by
  rw [lin_mul_E, ← cov_eq_covW φ χ g P F H hF hH w hw [] [] (by simp) (by simp)]; rfl

/-- The constant map `1` is `1` on `E []` and `0` on every other `E l`. -/
theorem lin_one_E (l : List G) : lin (fun _ => (1 : ℤ)) (E l) = if l = [] then 1 else 0 := by
  cases l with
  | nil => rw [E_nil, lin_one, if_pos rfl]
  | cons g l => rw [E_cons, sub_mul, one_mul, map_sub, lin_of_mul, sub_self, if_neg (List.cons_ne_nil _ _)]

/-- `lin 1` vanishes on `Δ`: the constant map is a polynomial map of degree `0`. -/
theorem lin_one_eq_zero : ∀ x ∈ augIdeal G ^ (0 + 1), lin (fun _ : G => (1 : ℤ)) x = 0 := by
  intro x hx
  have hx' := pow_le_spanE (G := G) 0 (by rwa [Submodule.restrictScalars_mem])
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    rw [lin_one_E, if_neg (by rintro rfl; simp at hl)]
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_zsmul, hy, smul_zero]

end PolyProd

end GroupDimension.TraceReplay
