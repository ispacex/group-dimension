module

public import GroupDimension.TraceReplay.Magnus
public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Powers of a homomorphism `G → ℤ` as functionals on `ℤ[G]/Δ^n` (MATH-314)

The trace checker's rank bound uses *polynomial maps*: functions `G → ℤ` whose linear extension
vanishes on a power of the augmentation ideal `Δ`. When all maps have weight 1 (as for `c4a`), they
are homomorphisms `φ : G → ℤ`, and the functionals are the powers `φ^K`.

* `nu φ K : ℤ[G] →+ ℚ` is the linear extension of `g ↦ φ(g)^K`. It is defined as `K!·[t^K] Φ(x)`,
  where `Φ : ℤ[G] → ℚ⟦t⟧` is the ring map `g ↦ exp(φ(g)·t)`.
* `nu_eq_zero`: `nu φ K` vanishes on `Δ^n` for `K < n`. The map `Φ` sends `Δ` into `t·ℚ⟦t⟧`, so
  it sends `Δ^n` into `t^n·ℚ⟦t⟧`.
* `nu_psi`: the value of `nu φ K` on `ψ(X_w) = Π (g_{w_i} − 1)` is `hval a K 0 w`. Here `hval` is a
  recursion on the word that the kernel can evaluate:
  `hval s [] = s^K` and `hval s (j :: w) = hval (s + a_j) w − hval s w`.
-/

namespace GroupDimension.TraceReplay

open MonoidAlgebra PowerSeries

/-- `hval a K s w = Σ_{σ ⊆ w} (−1)^{|w|−|σ|} (s + Σ_{j ∈ σ} a_j)^K`, `σ` over the subwords. -/
def hval (a : List Int) (K : Nat) : Int → List Nat → Int
  | s, [] => s ^ K
  | s, j :: w => hval a K (s + a.getD j 0) w - hval a K s w

section HomPow

variable {G : Type*} [Group G] (φ : G →* Multiplicative ℤ)

/-- `g ↦ exp(φ(g)·t)` in `ℚ⟦t⟧`. -/
noncomputable def expHom : G →* PowerSeries ℚ where
  toFun g := rescale ((Multiplicative.toAdd (φ g) : ℤ) : ℚ) (exp ℚ)
  map_one' := by
    rw [map_one, toAdd_one, Int.cast_zero, rescale_zero_apply, constantCoeff_exp, map_one]
  map_mul' a b := by
    rw [map_mul, toAdd_mul, Int.cast_add, exp_mul_exp_eq_exp_add]

/-- `Φ : ℤ[G] → ℚ⟦t⟧`, `g ↦ exp(φ(g)·t)`. -/
noncomputable def Phi : MonoidAlgebra ℤ G →ₐ[ℤ] PowerSeries ℚ :=
  MonoidAlgebra.lift ℤ (PowerSeries ℚ) G (expHom φ)

theorem Phi_of (g : G) :
    Phi φ (of ℤ G g) = rescale ((Multiplicative.toAdd (φ g) : ℤ) : ℚ) (exp ℚ) := by
  rw [Phi, MonoidAlgebra.lift_of]; rfl

theorem coeff_rescale_exp (a : ℚ) (K : ℕ) :
    (K.factorial : ℚ) * coeff K (rescale a (exp ℚ)) = a ^ K := by
  rw [coeff_rescale, coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
  have : (K.factorial : ℚ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
  field_simp

theorem X_dvd_Phi {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G) :
    (PowerSeries.X : PowerSeries ℚ) ∣ Phi φ x := by
  refine CentralRoot.augIdeal_induction (p := fun x => (PowerSeries.X : PowerSeries ℚ) ∣ Phi φ x) hx
    (by rw [map_zero]; exact dvd_zero _) ?_
    (fun y h => by rw [map_neg]; exact (dvd_neg).2 h)
    (fun y z h h' => by rw [map_add]; exact dvd_add h h')
  intro g
  rw [X_dvd_iff, map_sub, map_one, Phi_of, map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply,
    coeff_rescale]
  simp

theorem X_pow_dvd_Phi (k : ℕ) {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G ^ k) :
    (PowerSeries.X : PowerSeries ℚ) ^ k ∣ Phi φ x := by
  induction k generalizing x with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    rw [Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun _ _ h h' => ?_)
    · rw [map_mul, pow_succ]; exact mul_dvd_mul (ih ha) (X_dvd_Phi φ hb)
    · rw [map_add]; exact dvd_add h h'

/-- `ν_K = K!·[t^K] Φ`: the linear extension of `g ↦ φ(g)^K`. -/
noncomputable def nu (K : ℕ) : MonoidAlgebra ℤ G →+ ℚ :=
  (AddMonoidHom.mulLeft (K.factorial : ℚ)).comp
    ((coeff K : PowerSeries ℚ →ₗ[ℚ] ℚ).toAddMonoidHom.comp (Phi φ).toAddMonoidHom)

theorem nu_apply (K : ℕ) (x : MonoidAlgebra ℤ G) :
    nu φ K x = (K.factorial : ℚ) * coeff K (Phi φ x) := rfl

theorem nu_of (K : ℕ) (g : G) : nu φ K (of ℤ G g) = ((Multiplicative.toAdd (φ g) : ℤ) : ℚ) ^ K := by
  rw [nu_apply, Phi_of, coeff_rescale_exp]

/-- `ν_K` vanishes on `Δ^n` for `K < n`: a power of a homomorphism `G → ℤ` is a polynomial map. -/
theorem nu_eq_zero {n K : ℕ} (hK : K < n) {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G ^ n) :
    nu φ K x = 0 := by
  rw [nu_apply, X_pow_dvd_iff.mp (X_pow_dvd_Phi φ n hx) K hK, mul_zero]

variable {d : ℕ} [NeZero d] (g : Fin d → G) (a : List ℤ)

omit [NeZero d] in
theorem nu_prod_aux (ha : ∀ j : Fin d, Multiplicative.toAdd (φ (g j)) = a.getD j.val 0) (K : ℕ)
    (l : List (Fin d)) : ∀ s : ℤ,
      (K.factorial : ℚ) * coeff K (rescale (s : ℚ) (exp ℚ) *
        Phi φ (l.map fun j => of ℤ G (g j) - 1).prod) = (hval a K s (l.map (·.val)) : ℚ) := by
  induction l with
  | nil =>
    intro s
    rw [List.map_nil, List.prod_nil, map_one, mul_one, coeff_rescale_exp, List.map_nil, hval,
      Int.cast_pow]
  | cons j l ih =>
    intro s
    have e : rescale (s : ℚ) (exp ℚ) * Phi φ ((j :: l).map fun j => of ℤ G (g j) - 1).prod =
        rescale ((s + a.getD j.val 0 : ℤ) : ℚ) (exp ℚ) *
          Phi φ (l.map fun j => of ℤ G (g j) - 1).prod -
        rescale (s : ℚ) (exp ℚ) * Phi φ (l.map fun j => of ℤ G (g j) - 1).prod := by
      rw [List.map_cons, List.prod_cons, map_mul, map_sub, map_one, Phi_of, ha, Int.cast_add,
        ← exp_mul_exp_eq_exp_add]
      ring
    rw [e, map_sub, mul_sub, ih, ih, List.map_cons, hval, Int.cast_sub]

/-- The value of `ν_K` on `ψ(X_w)`, computable: `hval a K 0 w`. -/
theorem nu_psi (ha : ∀ j : Fin d, Multiplicative.toAdd (φ (g j)) = a.getD j.val 0) (K : ℕ)
    (w : FreeMonoid (Fin d)) :
    nu φ K (psi g (single w 1)) = (hval a K 0 (w.toList.map (·.val)) : ℚ) := by
  rw [psi_single, one_smul, nu_apply, ← nu_prod_aux φ g a ha K w.toList 0, Int.cast_zero,
    rescale_zero_apply, constantCoeff_exp, map_one, one_mul]

end HomPow

end GroupDimension.TraceReplay
