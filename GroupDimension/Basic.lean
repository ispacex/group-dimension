module

public import Mathlib

@[expose] public section

/-!
# Integral dimension subgroups

For a group `G` let `ℤ[G] = MonoidAlgebra ℤ G` be its integral group ring,
`ε : ℤ[G] → ℤ` the augmentation (`g ↦ 1`), and `Δ(G) = ker ε` the augmentation ideal.
The `n`-th dimension subgroup is

  `D n G = G ∩ (1 + Δ(G)^n) = {g | g - 1 ∈ Δ(G)^n}`.

Indexing follows the literature: `D 1 G = G`, `D 2 G = [G, G]`, … (and `D 0 G = G`
because `Δ^0 = ℤ[G]`).

Mathlib's `(⊤ : Subgroup G).lowerCentralSeries k` is numbered from zero:
`(⊤ : Subgroup G).lowerCentralSeries 0 = ⊤` and `(⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⁅(⊤ : Subgroup G).lowerCentralSeries k, ⊤⁆`
(see `Mathlib/GroupTheory/Nilpotent.lean`), so **`(⊤ : Subgroup G).lowerCentralSeries k = γ_{k+1}(G)`**.
For example `γ₄(G)` is `(⊤ : Subgroup G).lowerCentralSeries 3`.

`Δ(G)` is a left ideal in Mathlib's sense (`Ideal = Submodule ℤ[G] ℤ[G]`) and carries the
instance `IsTwoSided`, being the kernel of a ring homomorphism; its powers are two-sided too.
-/

namespace GroupDimension

open MonoidAlgebra

variable (G : Type*) [Group G]

/-- The augmentation `ε : ℤ[G] → ℤ`, `g ↦ 1`. -/
noncomputable def augmentation : MonoidAlgebra ℤ G →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ G (1 : G →* ℤ)).toRingHom

/-- The augmentation ideal `Δ(G) = ker ε`. -/
noncomputable def augIdeal : Ideal (MonoidAlgebra ℤ G) :=
  RingHom.ker (augmentation G)

instance augIdeal_isTwoSided : (augIdeal G).IsTwoSided :=
  inferInstanceAs (RingHom.ker (augmentation G)).IsTwoSided

variable {G}

@[simp]
theorem augmentation_of (g : G) : augmentation G (of ℤ G g) = 1 := by
  simp [augmentation]

theorem mem_augIdeal {x : MonoidAlgebra ℤ G} : x ∈ augIdeal G ↔ augmentation G x = 0 :=
  RingHom.mem_ker

theorem of_sub_one_mem_augIdeal (g : G) : of ℤ G g - 1 ∈ augIdeal G := by
  rw [mem_augIdeal, _root_.map_sub, augmentation_of, _root_.map_one, sub_self]

/-- `Δ^i · Δ^j ⊆ Δ^(i+j)`. -/
theorem mul_mem_augIdeal_pow {x y : MonoidAlgebra ℤ G} {i j : ℕ}
    (hx : x ∈ augIdeal G ^ i) (hy : y ∈ augIdeal G ^ j) :
    x * y ∈ augIdeal G ^ (i + j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using Ideal.mul_mem_right y _ hx
  · rw [Submodule.pow_add _ hj.ne']
    exact Ideal.mul_mem_mul hx hy

/-- The `n`-th integral dimension subgroup `D_n(G) = {g ∈ G | g - 1 ∈ Δ(G)^n}`. -/
noncomputable def D (n : ℕ) (G : Type*) [Group G] : Subgroup G where
  carrier := {g | of ℤ G g - 1 ∈ augIdeal G ^ n}
  one_mem' := by
    show of ℤ G 1 - 1 ∈ augIdeal G ^ n
    rw [map_one, sub_self]; exact zero_mem _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    -- `ab - 1 = (a - 1) b + (b - 1)`
    have h : of ℤ G (a * b) - 1 = (of ℤ G a - 1) * of ℤ G b + (of ℤ G b - 1) := by
      rw [map_mul]; noncomm_ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    -- `a⁻¹ - 1 = -((a - 1) a⁻¹)`
    have h : of ℤ G a⁻¹ - 1 = -((of ℤ G a - 1) * of ℤ G a⁻¹) := by
      have hh : of ℤ G a * of ℤ G a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [sub_mul, hh]; noncomm_ring
    rw [h]
    exact neg_mem (Ideal.mul_mem_right _ _ ha)

theorem mem_D {n : ℕ} {g : G} : g ∈ D n G ↔ of ℤ G g - 1 ∈ augIdeal G ^ n := Iff.rfl

/-- `D_n(G)` is a normal subgroup: `h g h⁻¹ - 1 = h (g - 1) h⁻¹`. -/
instance D_normal (n : ℕ) : (D n G).Normal where
  conj_mem g hg h := by
    rw [mem_D] at *
    have e : of ℤ G (h * g * h⁻¹) - 1 = of ℤ G h * (of ℤ G g - 1) * of ℤ G h⁻¹ := by
      have hh : of ℤ G h * of ℤ G h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hh]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hg)

@[simp]
theorem D_zero : D 0 G = ⊤ := by
  ext g; simp [mem_D, Submodule.pow_zero, Ideal.one_eq_top]

/-- `D_1(G) = G`. -/
@[simp]
theorem D_one : D 1 G = ⊤ := by
  ext g; simp only [mem_D, Submodule.pow_one, Subgroup.mem_top, iff_true]
  exact of_sub_one_mem_augIdeal g

/-- The dimension series is decreasing. -/
theorem D_antitone : Antitone (fun n => D n G) := by
  intro m n hmn g hg
  exact Ideal.pow_le_pow_right hmn hg

end GroupDimension
