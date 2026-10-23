module

public import GroupDimension.Basic

@[expose] public section

/-!
# `γₙ(G) ⊆ Dₙ(G)` and functoriality

Mathlib's commutator is `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹`
(`commutatorElement_def`). In `ℤ[G]`,

  `⁅a, b⁆ - 1 = ((a - 1)(b - 1) - (b - 1)(a - 1)) · a⁻¹ b⁻¹`,

because `ab - ba = (a - 1)(b - 1) - (b - 1)(a - 1)` and `ba · a⁻¹b⁻¹ = 1`.
For the other common convention `[a, b] = a⁻¹ b⁻¹ a b` the same computation gives
`[a, b] - 1 = a⁻¹ b⁻¹ ((a - 1)(b - 1) - (b - 1)(a - 1))`; both identities are proved below.

Consequently `⁅D_i, D_j⁆ ⊆ D_{i+j}`, and induction gives `γ_n ⊆ D_n`.
-/

namespace GroupDimension

open MonoidAlgebra
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- `ab - ba = (a - 1)(b - 1) - (b - 1)(a - 1)` in any ring. -/
theorem mul_sub_mul_eq_commutator_aug {R : Type*} [Ring R] (x y : R) :
    x * y - y * x = (x - 1) * (y - 1) - (y - 1) * (x - 1) := by
  noncomm_ring

/-- The commutator identity for Mathlib's convention `⁅a, b⁆ = a b a⁻¹ b⁻¹`. -/
theorem of_commutator_sub_one (a b : G) :
    of ℤ G ⁅a, b⁆ - 1 =
      ((of ℤ G a - 1) * (of ℤ G b - 1) - (of ℤ G b - 1) * (of ℤ G a - 1)) *
        (of ℤ G a⁻¹ * of ℤ G b⁻¹) := by
  rw [← mul_sub_mul_eq_commutator_aug, commutatorElement_def]
  have hb : of ℤ G b * of ℤ G b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, _root_.map_one]
  have ha : of ℤ G a * of ℤ G a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, _root_.map_one]
  have hba : of ℤ G b * of ℤ G a * (of ℤ G a⁻¹ * of ℤ G b⁻¹) = 1 := by
    rw [mul_assoc, ← mul_assoc (of ℤ G a), ha, one_mul, hb]
  rw [sub_mul, hba]
  simp only [map_mul, mul_assoc]

/-- The commutator identity for the convention `[a, b] = a⁻¹ b⁻¹ a b`. -/
theorem of_inv_mul_inv_mul_mul_sub_one (a b : G) :
    of ℤ G (a⁻¹ * b⁻¹ * a * b) - 1 =
      (of ℤ G a⁻¹ * of ℤ G b⁻¹) *
        ((of ℤ G a - 1) * (of ℤ G b - 1) - (of ℤ G b - 1) * (of ℤ G a - 1)) := by
  rw [← mul_sub_mul_eq_commutator_aug]
  have hb : of ℤ G b⁻¹ * of ℤ G b = 1 := by rw [← map_mul, inv_mul_cancel, _root_.map_one]
  have ha : of ℤ G a⁻¹ * of ℤ G a = 1 := by rw [← map_mul, inv_mul_cancel, _root_.map_one]
  have hab : of ℤ G a⁻¹ * of ℤ G b⁻¹ * (of ℤ G b * of ℤ G a) = 1 := by
    rw [mul_assoc, ← mul_assoc (of ℤ G b⁻¹), hb, one_mul, ha]
  rw [mul_sub, hab]
  simp only [map_mul, mul_assoc]

/-- If `p ∈ D_i` and `q ∈ D_j` then `⁅p, q⁆ ∈ D_{i+j}`. -/
theorem commutator_mem_D {i j : ℕ} {p q : G} (hp : p ∈ D i G) (hq : q ∈ D j G) :
    ⁅p, q⁆ ∈ D (i + j) G := by
  rw [mem_D] at *
  rw [of_commutator_sub_one]
  refine Ideal.mul_mem_right _ _ (Ideal.sub_mem _ (mul_mem_augIdeal_pow hp hq) ?_)
  rw [add_comm]
  exact mul_mem_augIdeal_pow hq hp

/-- `⁅D_i(G), D_j(G)⁆ ⊆ D_{i+j}(G)`. -/
theorem commutator_D_le (i j : ℕ) : ⁅D i G, D j G⁆ ≤ D (i + j) G :=
  (Subgroup.commutator_le).mpr fun _ hp _ hq => commutator_mem_D hp hq

variable (G) in
/-- **`γ_{n+1}(G) ⊆ D_{n+1}(G)`** in Mathlib's zero-based indexing of the lower central
series: `(⊤ : Subgroup G).lowerCentralSeries n = γ_{n+1}(G)`. -/
theorem lowerCentralSeries_le_D (n : ℕ) : (⊤ : Subgroup G).lowerCentralSeries n ≤ D (n + 1) G := by
  induction n with
  | zero => simp
  | succ n ih =>
    change ⁅(⊤ : Subgroup G).lowerCentralSeries n, ⊤⁆ ≤ D (n + 1 + 1) G
    calc ⁅(⊤ : Subgroup G).lowerCentralSeries n, ⊤⁆ ≤ ⁅D (n + 1) G, D 1 G⁆ :=
          Subgroup.commutator_mono ih (by simp)
      _ ≤ D (n + 1 + 1) G := commutator_D_le _ _

variable (G) in
/-- **`γ_n(G) ⊆ D_n(G)` for every `n ≥ 1`**, in the literature's indexing:
`γ_n(G) = (⊤ : Subgroup G).lowerCentralSeries (n - 1)`. -/
theorem gamma_le_D (n : ℕ) (hn : 1 ≤ n) : (⊤ : Subgroup G).lowerCentralSeries (n - 1) ≤ D n G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa using lowerCentralSeries_le_D G k

/-! ## Functoriality -/

variable {H : Type*} [Group H]

/-- The ring map `ℤ[G] → ℤ[H]` induced by `f : G →* H` respects augmentations. -/
theorem augmentation_mapDomain (f : G →* H) (x : MonoidAlgebra ℤ G) :
    augmentation H (mapDomainRingHom ℤ f x) = augmentation G x := by
  have : (augmentation H).comp (mapDomainRingHom ℤ f) = augmentation G := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [augmentation]
    · intro g
      simp [augmentation]
  exact congrArg (fun φ => φ x) this

theorem mapDomain_mem_augIdeal_pow (f : G →* H) (n : ℕ) {x : MonoidAlgebra ℤ G}
    (hx : x ∈ augIdeal G ^ n) : mapDomainRingHom ℤ f x ∈ augIdeal H ^ n := by
  induction n generalizing x with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ] at hx ⊢
    have key : augIdeal G ^ n * augIdeal G ≤
        Ideal.comap (mapDomainRingHom ℤ f) (augIdeal H ^ n * augIdeal H) := by
      rw [Ideal.mul_le]
      intro r hr s hs
      rw [Ideal.mem_comap, map_mul]
      refine Ideal.mul_mem_mul (ih hr) ?_
      rw [mem_augIdeal, augmentation_mapDomain, ← mem_augIdeal]
      exact hs
    exact key hx

/-- **Functoriality**: a homomorphism `f : G → H` maps `D_n(G)` into `D_n(H)`. -/
theorem mapDomainRingHom_of (f : G →* H) (g : G) :
    mapDomainRingHom ℤ f (of ℤ G g) = of ℤ H (f g) := by
  simp [MonoidAlgebra.of_apply]

theorem map_mem_D (f : G →* H) {n : ℕ} {g : G} (hg : g ∈ D n G) : f g ∈ D n H := by
  rw [mem_D] at *
  have h := mapDomain_mem_augIdeal_pow f n hg
  rwa [_root_.map_sub, _root_.map_one, mapDomainRingHom_of] at h

theorem map_D_le (f : G →* H) (n : ℕ) : (D n G).map f ≤ D n H := by
  rintro _ ⟨g, hg, rfl⟩
  exact map_mem_D f hg

theorem D_le_comap (f : G →* H) (n : ℕ) : D n G ≤ (D n H).comap f :=
  fun _ hg => map_mem_D f hg

end GroupDimension
