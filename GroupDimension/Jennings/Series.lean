module

public import GroupDimension.TaharaProof.Induction

@[expose] public section

/-!
# Restricted N-series and the augmentation ideal over `𝔽_p`

Infrastructure for Jennings' theorem ([Jen41], [Laz54]; Passi, LNM 715, Ch. III).

**Restricted N-series** (Lazard). A series `S 1 = G ≥ S 2 ≥ ⋯` of normal subgroups with
`[S a, S b] ≤ S (a + b)` and `(S a)^p ≤ S (p a)`, ending at `1`. The index `0` plays no role:
`S 0` is unconstrained, and every field speaks about indices `≥ 1`. Its layers `S k / S (k+1)`
are elementary abelian `p`-groups (`[S k, S k] ≤ S (2k)`, `(S k)^p ≤ S (pk)`).

**The augmentation ideal over `𝔽_p`.** `augIdealP p G = ker (ε : 𝔽_p[G] → 𝔽_p)`, the analogue of
`augIdeal` (`GroupDimension/Basic.lean`) with coefficients `ZMod p`.

The main theorem (`GroupDimension/Jennings/Main.lean`) is `G ∩ (1 + Δ_{𝔽_p}^n) ≤ S n` for every
restricted N-series `S` of a finite `p`-group.
-/

namespace GroupDimension

namespace Jennings

open MonoidAlgebra
open scoped commutatorElement

/-- A restricted N-series of `G` (Lazard): `S 1 = ⊤`, decreasing, normal, `[S a, S b] ≤ S (a+b)`,
`(S a)^p ≤ S (p a)`, and `S N = ⊥` for some `N ≥ 1`. (Only indices `≥ 1` matter; `S 0` is
unconstrained, which is why `N ≥ 1` is required in `eventually`.) -/
structure RestrictedSeries (p : ℕ) (G : Type*) [Group G] where
  S : ℕ → Subgroup G
  normal : ∀ n, (S n).Normal
  one : S 1 = ⊤
  antitone : ∀ {m n}, 1 ≤ m → m ≤ n → S n ≤ S m
  comm : ∀ {a b}, 1 ≤ a → 1 ≤ b → ∀ x ∈ S a, ∀ y ∈ S b, ⁅x, y⁆ ∈ S (a + b)
  pow : ∀ {a}, 1 ≤ a → ∀ x ∈ S a, x ^ p ∈ S (p * a)
  eventually : ∃ N, 1 ≤ N ∧ S N = ⊥

namespace RestrictedSeries

variable {p : ℕ} {G : Type*} [Group G] (T : RestrictedSeries p G)

theorem mem_of_le {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) {g : G} (hg : g ∈ T.S n) : g ∈ T.S m :=
  T.antitone hm h hg

theorem mem_one (g : G) : g ∈ T.S 1 := by rw [T.one]; trivial

/-- Tahara's commutator `tc y x = y⁻¹ x⁻¹ y x` of elements of `S a`, `S b` lies in `S (a + b)`. -/
theorem tc_mem {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {y x : G} (hy : y ∈ T.S a) (hx : x ∈ T.S b) :
    Tahara.tc y x ∈ T.S (a + b) := by
  have := T.comm ha hb _ (inv_mem hy) _ (inv_mem hx)
  simpa [commutatorElement_def, Tahara.tc] using this

end RestrictedSeries

/-! ## The augmentation ideal over `𝔽_p` -/

variable (p : ℕ) (G : Type*) [Group G]

/-- The augmentation `ε : 𝔽_p[G] → 𝔽_p`, `g ↦ 1`, as an algebra map. -/
noncomputable def augAlgHomP : MonoidAlgebra (ZMod p) G →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) G (1 : G →* ZMod p)

/-- The augmentation `ε : 𝔽_p[G] → 𝔽_p`, `g ↦ 1`. -/
noncomputable def augmentationP : MonoidAlgebra (ZMod p) G →+* ZMod p :=
  (augAlgHomP p G).toRingHom

/-- The augmentation ideal `Δ_{𝔽_p}(G) = ker ε`. -/
noncomputable def augIdealP : Ideal (MonoidAlgebra (ZMod p) G) :=
  RingHom.ker (augmentationP p G)

instance augIdealP_isTwoSided : (augIdealP p G).IsTwoSided :=
  inferInstanceAs (RingHom.ker (augmentationP p G)).IsTwoSided

variable {p G}

@[simp]
theorem augmentationP_of (g : G) : augmentationP p G (of (ZMod p) G g) = 1 := by
  simp [augmentationP, augAlgHomP]

theorem augmentationP_smul (c : ZMod p) (z : MonoidAlgebra (ZMod p) G) :
    augmentationP p G (c • z) = c * augmentationP p G z := by
  show augAlgHomP p G (c • z) = c * augAlgHomP p G z
  rw [map_smul, smul_eq_mul]

theorem mem_augIdealP {x : MonoidAlgebra (ZMod p) G} :
    x ∈ augIdealP p G ↔ augmentationP p G x = 0 :=
  RingHom.mem_ker

theorem of_sub_one_mem_augIdealP (g : G) : of (ZMod p) G g - 1 ∈ augIdealP p G := by
  rw [mem_augIdealP, _root_.map_sub, augmentationP_of, _root_.map_one, sub_self]

/-- Induction over `𝔽_p[G]`: a submodule containing every `g` is everything. -/
theorem mem_of_forall_of {M : Submodule (ZMod p) (MonoidAlgebra (ZMod p) G)}
    (h : ∀ g, of (ZMod p) G g ∈ M) (z : MonoidAlgebra (ZMod p) G) : z ∈ M := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add y z hy hz => exact add_mem hy hz
  | single g c =>
    have e : (MonoidAlgebra.single g c : MonoidAlgebra (ZMod p) G) = c • of (ZMod p) G g := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    rw [e]; exact Submodule.smul_mem _ _ (h g)

/-- `𝔽_p[G]` has characteristic `p`. -/
theorem charP [Fact p.Prime] : CharP (MonoidAlgebra (ZMod p) G) p := by
  refine charP_of_injective_algebraMap (R := ZMod p) ?_ p
  intro a b h
  have := congrArg (fun z : MonoidAlgebra (ZMod p) G => z.coeff 1) h
  simpa [MonoidAlgebra.coe_algebraMap] using this

end Jennings

end GroupDimension
