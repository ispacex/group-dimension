module

public import GroupDimension.Kernel.ClassThree

@[expose] public section

/-!
# All `K ⊆ γ_c(M)` at once: Lemmas 3 and 5, Propositions 4 and 6, the reduction to cocyclic
quotients, removing `∩ γ_c` (fast-core paper, §6.6–6.10; MATH-310)

`cflint-fast-core`, `docs/analysis.md`:

> **§6.6, Reduction used.** Let `M = Γ/γ₅(Γ)Γ''` and `K ⊆ γ₄(M)`. If `1 ≠ v ∈ D₇(M/K) ∩ γ₄`, take
> `K' ⊇ K` maximal with `v ∉ K'`: then `v ∈ D₇(M/K')` by functoriality and `γ₄(M)/K'` is a finite
> cyclic 2-group (finitely generated abelian with a unique minimal subgroup). So it suffices to
> test the *cocyclic* quotients `G_φ = M/ker φ`, `φ : γ₄(M) ↠ C_{2^m}`, and in each the single
> element `A^{2^{m-1}}` of order 2 of `γ₄(G_φ) = ⟨A⟩`.
>
> **§6.8(b), Lemma 3.** (i) `ψ : A₄ → Δ⁴/Δⁿ`, `k ↦ k − 1`, is a homomorphism. (ii) For `K ⊆ A₄`
> and `v ∈ M`: `v ∈ D_n(M/K) ⟺ v − 1 ∈ Δⁿ + (K − 1)A`, and
> `(K − 1)A + Δⁿ = Δⁿ + Σ_k ψ(k)·R`, `R = span{1} ∪ {(x_{j₁} − 1)⋯(x_{j_l} − 1) : 1 ≤ l ≤ n − 5}`,
> `k` over generators of `K`.
>
> **Proposition 4.** Let `U_n = J_n + Λ(A₄ ⊗ R₊)`, `R₊` the monomials of degree `1..n−5`, and
> `ψ̄ : A₄ → A/U_n`. If `ψ̄` is injective, then `D_n(M/K) ∩ γ₄(M)/K = 1` for **every** `K ⊆ A₄`.
> Conversely, `ker ψ̄` contains `D_n(M) ∩ A₄`, and every `v ∈ D_n(M/K) ∩ A₄`, `v ∉ K`, gives
> `1 ≠ vk⁻¹ ∈ ker ψ̄` for some `k ∈ K`. `ker ψ̄` is torsion (Jennings), so it is enough to test the
> elements of order 2; `ker ψ̄_{n+1} ⊆ ker ψ̄_n`.
>
> **§6.10, Lemma 5 and Proposition 6**: the same for `c = 5`, `A₅ = γ₅(M)`, `n ≤ 10`.
> **Removing `∩ γ₅`.** For `K ⊆ γ₅(M)`, `(M/K)/γ₅(M/K) = M/γ₅(M) = Q`, and the image of `D_n(M/K)`
> in `Q` lies in `D_n(Q)`. So `D_n(Q) = 1` and `ψ̄_n` injective imply `D_n(M/K) = 1` for every
> `K ⊆ γ₅(M)`.

Indexing as in `Statements.lean`: `γ_c = (⊤ : Subgroup M).lowerCentralSeries (c − 1)`, so
`γ₄ = … 3`, `γ₅ = … 4`. `A = ℤ[M]`, `Δ = augIdeal M`.

## Setting

Everything is proved for an arbitrary group `M`, a subgroup `C` with `C ⊆ D_c(M)` (for the paper,
`C = γ_c(M)`: `lowerCentralSeries_le_D`), and `n ≤ 2c`; Propositions 4 and 6 need `K` normal, not
central, and no finite generation. The paper's objects:

* `psiHom C hC hn : C →* ℤ[M]/Δⁿ`, `k ↦ k − 1` — the map `ψ` of Lemmas 3(i) and 5(i) (its values
  lie in `Δ^c/Δⁿ`, since `C ⊆ D_c`).
* `KA K = span_ℤ{(k − 1)g : k ∈ K, g ∈ M}` — the right ideal `(K − 1)A`.
* `U C n = Δⁿ + span_ℤ{(k − 1)d : k ∈ C, d ∈ Δ}` — the paper's `U_n = J_n + Λ(A_c ⊗ R₊)`, written
  intrinsically in `ℤ[M]` (the paper's `U_n ⊆ A_n` is the image of `U C n` under
  `ℤ[M]/Δⁿ ≅ A_n/J_n`, `Kernel/Magnus.lean`). `U_eq_span_Rplus` shows that it equals the paper's
  `Δⁿ + span{ψ(b_t)·m : b_t generators of C, m ∈ R₊}`.
* `psiBar C hC hn : C →* ℤ[M]/U_n`, `k ↦ k − 1` — the map `ψ̄`.
* `monom l = (x₁ − 1)⋯(x_l − 1)`, `Rplus X m` the monomials in the generators `X` of length
  `1 ≤ l < m` (the paper's `R₊` is `Rplus X (n − c)`), `insert 1 (Rplus X m)` the paper's `R`.

## What is proved

* **Lemmas 3(i), 5(i)** (`psiHom`, `ker_psiHom`): `ψ` is a homomorphism for `C ⊆ D_c`, `n ≤ 2c`
  (`c = 4`, `n ≤ 8`; `c = 5`, `n ≤ 10`), with kernel `D_n ∩ C`; `zpow_sub_one_sub_mem`:
  `k^a − 1 ≡ a(k − 1) (mod Δⁿ)`.
* **Lemmas 3(ii), 5(ii)**: for `K` normal, `ker(ℤ[M] → ℤ[M/K]) = (K − 1)A` (`ker_eq_KA`) and
  `v ∈ D_n(M/K) ⟺ v − 1 ∈ Δⁿ + (K − 1)A` (`mem_D_quotient_iff`); and, for `K = ⟨S⟩ ⊆ D_c`,
  `c ≤ n ≤ 2c` and any `R` with `ℤ[M] = span R + Δ^{n−c}`,
  `Δⁿ + (K − 1)A = Δⁿ + span{(s − 1)r : s ∈ S, r ∈ R}` (`pow_sup_KA_eq`). With `X` generating `M`,
  the paper's `R = span{1} ∪ {monomials of length 1..n−c−1}` satisfies the hypothesis
  (`top_le_span_R`, from `augIdeal_le_span_Rplus`: `Δ = span R₊ + Δ^m`), so the identity holds as
  in the paper (`lemma_ii`).
* **Propositions 4, 6** (`D_quotient_inf_map_eq_bot`; `prop4`, `prop6` for `C = γ₄`, `γ₅`): if
  `ψ̄` is injective, then `D_n(M/K) ∩ C/K = 1` for every normal `K ⊆ C` at once.
  The converses: `D_inf_le_ker` (`D_n(M) ∩ C ⊆ ker ψ̄`) and `exists_ne_one_mem_ker` (every
  `v ∈ D_n(M/K) ∩ C`, `v ∉ K`, gives `1 ≠ vk⁻¹ ∈ ker ψ̄`, `k ∈ K`); the key step is
  `exists_sub_mem_U`. Also `U_eq_span_Rplus` (the paper's `U_n` from generators of `C` and `R₊`),
  `ker_psiBar_mono` (`ker ψ̄_{n'} ⊆ ker ψ̄_n` for `n ≤ n' ≤ 2c`), `ker_le_D` (`ker ψ̄ ⊆ D_{c+1}`
  for `c + 1 ≤ n`), `U_succ_eq` and `ker_psiBar_of_eq` (for `n = c + 1`, `U = Δ^{c+1}` and
  `ker ψ̄ = D_{c+1} ∩ C`: "for `n = 6`, `U₆ = J₆`").
* **Torsion of `ker ψ̄`**, with Jennings' theorem as the explicit hypothesis `JenningsIsolator`
  (`M` finitely generated of class `≤ c`, `c + 1 ≤ n`): `isOfFinOrder_of_mem_ker`; and the test on
  the elements of order 2: if every element of finite order of `C` has `2`-power order,
  `ker ψ̄ = 1 ⟺` no `z ≠ 1` with `z² = 1` lies in it (`ker_eq_bot_iff_two`).
* **Reduction used (§6.6)** (`reduction_cocyclic`, `reduction_cocyclic_two`): for `C` central and
  finitely generated, `K ⊆ C` normal, `v ∈ C ∖ K` with `v ∈ D_n(M/K)`, there is a normal `K'`,
  `K ⊆ K' ⊆ C`, `v ∉ K'`, `v ∈ D_n(M/K')`, such that every subgroup strictly between `K'` and `C`
  contains `v`, and `C/K'` is a finite cyclic `p`-group, `p` the (prime) order of `v` there;
  if `v^{2^j} ∈ K` for some `j`, then `p = 2`, `v² ∈ K'` and there is `φ : C ↠ C_{2^m}` with
  `ker φ = K'`. The group theory: `exists_maximal_avoiding` (Zorn) and
  `cocyclic_prime`, `cocyclic_isPGroup`, `cocyclic_finite`, `cocyclic_isCyclic` (an abelian group
  in which every nontrivial subgroup contains a fixed `b ≠ 1`).
* **Removing `∩ γ_c` (§6.10)** (`D_quotient_eq_bot`, `D_quotient_eq_bot_of_le`): if
  `D_n(M/C) = 1` (e.g. `D_m(M/C) = 1` for some `m ≤ n`) and `ψ̄_n` is injective, then
  `D_n(M/K) = 1` for every normal `K ⊆ C`. `D_five_eq_bot`: §6.10's
  "`D₅(Q) = 1` from `D₅(Q₃) = 1` and `D₅(Q) ∩ γ₄(Q) = 1`, the latter by `ψ̄₅` for `c = 4`".
* `normal_of_le_lcs`, `lcs_le_center`: in a group of class `≤ c` every subgroup of `γ_c` is central,
  hence normal (the paper's `K ⊆ γ_c(M)` need no normality hypothesis there).

## What is not formalized here

* Jennings' theorem itself (`JenningsIsolator` is a hypothesis of the torsion statements only;
  Propositions 4 and 6, Lemmas 3 and 5, the reduction and the removal of `∩ γ_c` do not use it).
* In the reduction, `γ_c(M/K') = γ_c(M)/K'` is not stated: the paper's "the single element
  `A^{2^{m-1}}` of order 2 of `γ₄(G_φ) = ⟨A⟩`" is formalized as "`v` is the unique element of
  order 2 of `C/K'`" (`v ∉ K'`, `v² ∈ K'`, `C/K'` cyclic, every nontrivial subgroup contains `v`).
* The identification of `U C n` with the paper's matrix `J_n + Λ(A_c ⊗ R₊)` in `A_n` beyond the
  statement in `ℤ[M]` (`U_eq_span_Rplus`; the transfer to `A_n/J_n` is `Kernel/Magnus.lean`'s
  `quotEquiv`, not restated here), and "injective modulo `2^{32}` is exact" (a relation in `U_n` is one
  in `U_n + 2^{32}A`, not stated).
* That `γ_c(M)` is finitely generated (`M` finitely generated nilpotent) is a hypothesis of the
  reduction (`Group.FG C`), and `(M/K)/γ_c(M/K) = M/γ_c(M)` is not stated (the removal uses only the
  map `M/K → M/C`).
* Everything computational in §6.6–6.10: the records, `c4_q3.py`, `howell_gpu.py --kfree`, the
  `socle_bits` counts, the certificates and the tables.
-/

namespace GroupDimension.Kernel.KFree

noncomputable section

open MonoidAlgebra
open scoped commutatorElement

variable {M : Type*} [Group M]

/-! ## Elementary identities in `ℤ[M]` -/

theorem mul_sub_one_eq (k k' : M) :
    of ℤ M (k * k') - 1 =
      (of ℤ M k - 1) + (of ℤ M k' - 1) + (of ℤ M k - 1) * (of ℤ M k' - 1) := by
  rw [map_mul]; noncomm_ring

theorem inv_sub_one_eq (k : M) :
    of ℤ M k⁻¹ - 1 = -(of ℤ M k - 1) - (of ℤ M k - 1) * (of ℤ M k⁻¹ - 1) := by
  have h : of ℤ M k⁻¹ - 1 = -((of ℤ M k - 1) * of ℤ M k⁻¹) := by
    have hh : of ℤ M k * of ℤ M k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [sub_mul, hh]; noncomm_ring
  have e : -(of ℤ M k - 1) - (of ℤ M k - 1) * (of ℤ M k⁻¹ - 1) =
      -((of ℤ M k - 1) * of ℤ M k⁻¹) := by noncomm_ring
  rw [e]; exact h

theorem single_eq_smul_of (g : M) (c : ℤ) :
    (single g c : MonoidAlgebra ℤ M) = c • of ℤ M g := by
  rw [of_apply, smul_single', mul_one]

theorem augmentation_single (g : M) (c : ℤ) : augmentation M (single g c) = c := by
  rw [single_eq_smul_of, map_zsmul, augmentation_of, smul_eq_mul, mul_one]

/-- Membership in an ideal viewed as a `ℤ`-submodule. -/
theorem mem_rs {I : Ideal (MonoidAlgebra ℤ M)} {x : MonoidAlgebra ℤ M} :
    x ∈ I.restrictScalars ℤ ↔ x ∈ I :=
  Iff.rfl

/-- `x · y ∈ span{s t}` for `x ∈ span S`, `y ∈ span T`. -/
theorem mul_mem_span_mul {S T : Set (MonoidAlgebra ℤ M)} {x y : MonoidAlgebra ℤ M}
    (hx : x ∈ Submodule.span ℤ S) (hy : y ∈ Submodule.span ℤ T) :
    x * y ∈ Submodule.span ℤ {z | ∃ s ∈ S, ∃ t ∈ T, z = s * t} := by
  induction hx using Submodule.span_induction with
  | mem s hs =>
    induction hy using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span ⟨s, hs, t, ht, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

/-- `x − ε(x) ∈ span_ℤ{g − 1}`. -/
theorem sub_aug_mem_span (x : MonoidAlgebra ℤ M) :
    x - augmentation M x • (1 : MonoidAlgebra ℤ M) ∈
      Submodule.span ℤ {y | ∃ g : M, y = of ℤ M g - 1} := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, zero_smul, sub_zero]; exact zero_mem _
  | add a b ha hb =>
    rw [map_add, add_smul]
    convert add_mem ha hb using 1; abel
  | single g c =>
    rw [augmentation_single, single_eq_smul_of, ← smul_sub]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨g, rfl⟩)

/-- `Δ = span_ℤ{g − 1 : g ∈ M}`. -/
theorem mem_span_of_mem_augIdeal {x : MonoidAlgebra ℤ M} (hx : x ∈ augIdeal M) :
    x ∈ Submodule.span ℤ {y | ∃ g : M, y = of ℤ M g - 1} := by
  have := sub_aug_mem_span x
  rwa [mem_augIdeal.mp hx, zero_smul, sub_zero] at this

/-! ## Lemmas 3(i) and 5(i): the map `ψ` -/

variable {c n : ℕ}

/-- `(k − 1)(k' − 1) ∈ Δⁿ` for `k, k' ∈ D_c`, `n ≤ 2c`. -/
theorem sub_one_mul_sub_one_mem (hn : n ≤ 2 * c) {k k' : M} (hk : k ∈ D c M)
    (hk' : k' ∈ D c M) : (of ℤ M k - 1) * (of ℤ M k' - 1) ∈ augIdeal M ^ n :=
  Ideal.pow_le_pow_right (by omega) (mul_mem_augIdeal_pow hk hk')

/-- `kk' − 1 ≡ (k − 1) + (k' − 1) (mod Δⁿ)` for `k, k' ∈ D_c`, `n ≤ 2c`. -/
theorem mk_mul_sub_one (hn : n ≤ 2 * c) {k k' : M} (hk : k ∈ D c M) (hk' : k' ∈ D c M) :
    Ideal.Quotient.mk (augIdeal M ^ n) (of ℤ M (k * k') - 1) =
      Ideal.Quotient.mk (augIdeal M ^ n) (of ℤ M k - 1) +
        Ideal.Quotient.mk (augIdeal M ^ n) (of ℤ M k' - 1) := by
  rw [← map_add, Ideal.Quotient.eq, mul_sub_one_eq]
  convert sub_one_mul_sub_one_mem hn hk hk' using 1
  abel

variable (C : Subgroup M)

/-- **Lemmas 3(i), 5(i)**: `ψ : C → ℤ[M]/Δⁿ`, `k ↦ (k − 1) mod Δⁿ`, is a homomorphism for
`C ⊆ D_c` and `n ≤ 2c` (to the additive group, written multiplicatively). For the paper,
`C = γ₄(M)`, `n ≤ 8` (Lemma 3) and `C = γ₅(M)`, `n ≤ 10` (Lemma 5). -/
def psiHom (hC : C ≤ D c M) (hn : n ≤ 2 * c) :
    C →* Multiplicative (MonoidAlgebra ℤ M ⧸ augIdeal M ^ n) where
  toFun k := Multiplicative.ofAdd (Ideal.Quotient.mk _ (of ℤ M (k : M) - 1))
  map_one' := by
    show Multiplicative.ofAdd _ = 1
    rw [OneMemClass.coe_one, map_one, sub_self, map_zero, ofAdd_zero]
  map_mul' k k' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, Subgroup.coe_mul, mk_mul_sub_one hn (hC k.2) (hC k'.2)]

theorem psiHom_apply (hC : C ≤ D c M) (hn : n ≤ 2 * c) (k : C) :
    psiHom C hC hn k = Multiplicative.ofAdd (Ideal.Quotient.mk _ (of ℤ M (k : M) - 1)) := rfl

/-- The kernel of `ψ` is `D_n ∩ C`. -/
theorem ker_psiHom (hC : C ≤ D c M) (hn : n ≤ 2 * c) :
    (psiHom C hC hn).ker = (D n M).subgroupOf C := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, psiHom_apply, ofAdd_eq_one,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Iff.rfl

variable {C}

/-- `k^a − 1 ≡ a (k − 1) (mod Δⁿ)` for `k ∈ D_c`, `n ≤ 2c`. -/
theorem zpow_sub_one_sub_mem (hn : n ≤ 2 * c) {k : M} (hk : k ∈ D c M) (a : ℤ) :
    (of ℤ M (k ^ a) - 1) - a • (of ℤ M k - 1) ∈ augIdeal M ^ n := by
  have h := map_zpow (psiHom (D c M) le_rfl hn) ⟨k, hk⟩ a
  rw [psiHom_apply, psiHom_apply, ← ofAdd_zsmul] at h
  have h' := Multiplicative.ofAdd.injective h
  rw [← map_zsmul, Ideal.Quotient.eq, SubgroupClass.coe_zpow] at h'
  exact h'

/-! ## The submodule `U_n` and the map `ψ̄` -/

variable (C) in
/-- `span_ℤ{(k − 1) d : k ∈ C, d ∈ Δ}`, the paper's `Λ(A_c ⊗ R₊)` written in `ℤ[M]`. -/
def Wspan : Submodule ℤ (MonoidAlgebra ℤ M) :=
  Submodule.span ℤ {x | ∃ k ∈ C, ∃ d ∈ augIdeal M, x = (of ℤ M k - 1) * d}

variable (C) in
/-- `U_n = Δⁿ + span_ℤ{(k − 1) d : k ∈ C, d ∈ Δ}` (the paper's `U_n = J_n + Λ(A_c ⊗ R₊)`;
`U_eq_span_Rplus`). -/
def U (n : ℕ) : Submodule ℤ (MonoidAlgebra ℤ M) :=
  (augIdeal M ^ n).restrictScalars ℤ ⊔ Wspan C

theorem mem_U_of_mem_pow {x : MonoidAlgebra ℤ M} (hx : x ∈ augIdeal M ^ n) : x ∈ U C n :=
  Submodule.mem_sup_left (mem_rs.mpr hx)

theorem mem_U_of_mem_Wspan {x : MonoidAlgebra ℤ M} (hx : x ∈ Wspan C) : x ∈ U C n :=
  Submodule.mem_sup_right hx

variable (C) in
/-- **The map `ψ̄`** of Propositions 4 and 6: `C → ℤ[M]/U_n`, `k ↦ (k − 1) mod U_n`, a
homomorphism for `C ⊆ D_c`, `n ≤ 2c`. -/
def psiBar (hC : C ≤ D c M) (hn : n ≤ 2 * c) :
    C →* Multiplicative (MonoidAlgebra ℤ M ⧸ U C n) where
  toFun k := Multiplicative.ofAdd (Submodule.Quotient.mk (of ℤ M (k : M) - 1))
  map_one' := by
    show Multiplicative.ofAdd _ = 1
    rw [OneMemClass.coe_one, map_one, sub_self, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' k k' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add, Subgroup.coe_mul,
      Multiplicative.ofAdd.injective.eq_iff, Submodule.Quotient.eq, mul_sub_one_eq]
    convert mem_U_of_mem_pow (C := C) (sub_one_mul_sub_one_mem hn (hC k.2) (hC k'.2)) using 1
    abel

theorem psiBar_apply (hC : C ≤ D c M) (hn : n ≤ 2 * c) (k : C) :
    psiBar C hC hn k = Multiplicative.ofAdd (Submodule.Quotient.mk (of ℤ M (k : M) - 1)) := rfl

theorem mem_ker_psiBar (hC : C ≤ D c M) (hn : n ≤ 2 * c) (k : C) :
    k ∈ (psiBar C hC hn).ker ↔ of ℤ M (k : M) - 1 ∈ U C n := by
  rw [MonoidHom.mem_ker, psiBar_apply, ofAdd_eq_one, Submodule.Quotient.mk_eq_zero]

/-! ## Lemmas 3(ii) and 5(ii): the kernel of `ℤ[M] → ℤ[M/K]` -/

/-- The right ideal `(K − 1)A = span_ℤ{(k − 1) g : k ∈ K, g ∈ M}`. -/
def KA (K : Subgroup M) : Submodule ℤ (MonoidAlgebra ℤ M) :=
  Submodule.span ℤ {x | ∃ k ∈ K, ∃ g : M, x = (of ℤ M k - 1) * of ℤ M g}

theorem sub_one_mul_mem_KA {K : Subgroup M} {k : M} (hk : k ∈ K) (a : MonoidAlgebra ℤ M) :
    (of ℤ M k - 1) * a ∈ KA K := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b ha hb => rw [mul_add]; exact add_mem ha hb
  | single g c' =>
    rw [single_eq_smul_of, mul_smul_comm]
    exact Submodule.smul_mem _ c' (Submodule.subset_span ⟨k, hk, g, rfl⟩)

theorem mapDomain_eq_zero_of_mem_KA (K : Subgroup M) [K.Normal] {x : MonoidAlgebra ℤ M}
    (hx : x ∈ KA K) : mapDomainRingHom ℤ (QuotientGroup.mk' K) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, g, rfl⟩ := hx
    have h1 : QuotientGroup.mk' K k = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hk
    rw [map_mul, _root_.map_sub, _root_.map_one, mapDomainRingHom_of, h1, map_one, sub_self,
      zero_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_zsmul, hx, smul_zero]

/-- The kernel of `ℤ[M] → ℤ[M/K]` lies in `(K − 1)A` (`K` normal). -/
theorem mem_KA_of_mem_ker (K : Subgroup M) [hK : K.Normal] {x : MonoidAlgebra ℤ M}
    (hx : mapDomainRingHom ℤ (QuotientGroup.mk' K) x = 0) : x ∈ KA K := by
  obtain ⟨s, hs⟩ : ∃ s : M ⧸ K → M, ∀ q, QuotientGroup.mk' K (s q) = q :=
    ⟨_, Function.surjInv_eq (QuotientGroup.mk'_surjective K)⟩
  have key : ∀ y : MonoidAlgebra ℤ M,
      y - mapDomain s (mapDomainRingHom ℤ (QuotientGroup.mk' K) y) ∈ KA K := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero, mapDomain_zero, sub_zero]; exact zero_mem _
    | add a b ha hb =>
      rw [map_add, mapDomain_add]
      convert add_mem ha hb using 1; abel
    | single g c =>
      rw [mapDomainRingHom_apply, mapDomain_single, mapDomain_single]
      have ht : g * (s (QuotientGroup.mk' K g))⁻¹ ∈ K := by
        have h1 : (s (QuotientGroup.mk' K g))⁻¹ * g ∈ K :=
          QuotientGroup.eq.mp (hs (QuotientGroup.mk' K g))
        have := hK.conj_mem _ h1 (s (QuotientGroup.mk' K g))
        rwa [mul_inv_cancel_left] at this
      have e : (single g c : MonoidAlgebra ℤ M) - single (s (QuotientGroup.mk' K g)) c =
          c • ((of ℤ M (g * (s (QuotientGroup.mk' K g))⁻¹) - 1) *
            of ℤ M (s (QuotientGroup.mk' K g))) := by
        rw [sub_mul, ← map_mul (of ℤ M), inv_mul_cancel_right, one_mul, smul_sub,
          single_eq_smul_of g c, single_eq_smul_of _ c]
      rw [e]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨_, ht, _, rfl⟩)
  have := key x
  rwa [hx, mapDomain_zero, sub_zero] at this

/-- **Lemmas 3(ii), 5(ii)**, the kernel: `ker(ℤ[M] → ℤ[M/K]) = (K − 1)A` for `K` normal. -/
theorem ker_eq_KA (K : Subgroup M) [K.Normal] :
    (RingHom.ker (mapDomainRingHom ℤ (QuotientGroup.mk' K))).restrictScalars ℤ = KA K :=
  le_antisymm (fun _ hx => mem_KA_of_mem_ker K (RingHom.mem_ker.mp (mem_rs.mp hx)))
    (fun _ hx => mem_rs.mpr (RingHom.mem_ker.mpr (mapDomain_eq_zero_of_mem_KA K hx)))

section Lift

variable {H : Type*} [Group H] (f : M →* H)

theorem mapDomain_surjective (hf : Function.Surjective f) :
    Function.Surjective (mapDomainRingHom ℤ f) := by
  intro z
  induction z using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | single g c =>
    obtain ⟨w, hw⟩ := hf g
    exact ⟨single w c, by rw [mapDomainRingHom_apply, mapDomain_single, hw]⟩

/-- `Δ(H)ᵏ` is the image of `Δ(M)ᵏ` under a surjection `M → H`. -/
theorem exists_lift_augIdeal_pow (hf : Function.Surjective f) : ∀ k : ℕ, ∀ z ∈ augIdeal H ^ k,
    ∃ y ∈ augIdeal M ^ k, mapDomainRingHom ℤ f y = z
  | 0, z, _ => by
    obtain ⟨y, hy⟩ := mapDomain_surjective f hf z
    exact ⟨y, by rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, hy⟩
  | k + 1, z, hz => by
    rw [Submodule.pow_succ] at hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨y1, hy1, e1⟩ := exists_lift_augIdeal_pow hf k a ha
      obtain ⟨y2, e2⟩ := mapDomain_surjective f hf b
      have hy2 : y2 ∈ augIdeal M := by
        rw [mem_augIdeal, ← augmentation_mapDomain f, e2]; exact mem_augIdeal.mp hb
      refine ⟨y1 * y2, ?_, by rw [map_mul, e1, e2]⟩
      rw [Submodule.pow_succ]; exact Submodule.mul_mem_mul hy1 hy2
    · obtain ⟨y1, hy1, e1⟩ := ha
      obtain ⟨y2, hy2, e2⟩ := hb
      exact ⟨y1 + y2, add_mem hy1 hy2, by rw [map_add, e1, e2]⟩

end Lift

/-- **Lemmas 3(ii), 5(ii)**, first sentence: for `K` normal and `v ∈ M`,
`v ∈ D_n(M/K) ⟺ v − 1 ∈ Δⁿ + (K − 1)A`. -/
theorem mem_D_quotient_iff (K : Subgroup M) [K.Normal] (n : ℕ) (v : M) :
    QuotientGroup.mk' K v ∈ D n (M ⧸ K) ↔
      of ℤ M v - 1 ∈ (augIdeal M ^ n).restrictScalars ℤ ⊔ KA K := by
  have e : of ℤ (M ⧸ K) (QuotientGroup.mk' K v) - 1 =
      mapDomainRingHom ℤ (QuotientGroup.mk' K) (of ℤ M v - 1) := by
    rw [_root_.map_sub, _root_.map_one, mapDomainRingHom_of]
  rw [mem_D, e]
  constructor
  · intro hv
    obtain ⟨y, hy, hyx⟩ :=
      exists_lift_augIdeal_pow _ (QuotientGroup.mk'_surjective K) n _ hv
    refine Submodule.mem_sup.mpr ⟨y, mem_rs.mpr hy, of ℤ M v - 1 - y, ?_, by abel⟩
    exact mem_KA_of_mem_ker K (by rw [_root_.map_sub, hyx, sub_self])
  · intro hv
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
    rw [← hyz, map_add, mapDomain_eq_zero_of_mem_KA K hz, add_zero]
    exact mapDomain_mem_augIdeal_pow _ n (mem_rs.mp hy)

/-- `k − 1 ∈ span_ℤ{s − 1 : s ∈ S} + Δⁿ` for `k ∈ ⟨S⟩ ⊆ D_c`, `n ≤ 2c`. -/
theorem sub_one_mem_span_sup {S : Set M} (hS : Subgroup.closure S ≤ D c M) (hn : n ≤ 2 * c)
    {h : M} (hh : h ∈ Subgroup.closure S) :
    of ℤ M h - 1 ∈ Submodule.span ℤ {x | ∃ s ∈ S, x = of ℤ M s - 1} ⊔
      (augIdeal M ^ n).restrictScalars ℤ := by
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, rfl⟩)
  | one => rw [map_one, sub_self]; exact zero_mem _
  | mul x y hx hy ihx ihy =>
    rw [mul_sub_one_eq]
    exact add_mem (add_mem ihx ihy)
      (Submodule.mem_sup_right (mem_rs.mpr (sub_one_mul_sub_one_mem hn (hS hx) (hS hy))))
  | inv x hx ih =>
    rw [inv_sub_one_eq]
    exact sub_mem (neg_mem ih) (Submodule.mem_sup_right
      (mem_rs.mpr (sub_one_mul_sub_one_mem hn (hS hx) (hS (inv_mem hx)))))

/-- The common step of Lemmas 3(ii), 5(ii) and of `U_eq_span_Rplus`: for `h ∈ ⟨S⟩ ⊆ D_c`,
`c ≤ n ≤ 2c` and `v ∈ span R + Δ^{n−c}`, `(h − 1) v ∈ Δⁿ + span{(s − 1) r : s ∈ S, r ∈ R}`. -/
theorem sub_one_mul_mem_sup {S : Set M} {R : Set (MonoidAlgebra ℤ M)}
    (hS : Subgroup.closure S ≤ D c M) (hcn : c ≤ n) (hn : n ≤ 2 * c) {h : M}
    (hh : h ∈ Subgroup.closure S) {v : MonoidAlgebra ℤ M}
    (hv : v ∈ Submodule.span ℤ R ⊔ (augIdeal M ^ (n - c)).restrictScalars ℤ) :
    (of ℤ M h - 1) * v ∈ (augIdeal M ^ n).restrictScalars ℤ ⊔
      Submodule.span ℤ {x | ∃ s ∈ S, ∃ r ∈ R, x = (of ℤ M s - 1) * r} := by
  obtain ⟨r, hr, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
  have hcn' : c + (n - c) = n := by omega
  have hd' : (of ℤ M h - 1) * d ∈ augIdeal M ^ n := by
    have := mul_mem_augIdeal_pow (hS hh) (mem_rs.mp hd)
    rwa [hcn'] at this
  obtain ⟨t, ht, e, he, hte⟩ := Submodule.mem_sup.mp (sub_one_mem_span_sup hS hn hh)
  rw [mul_add]
  refine add_mem ?_ (Submodule.mem_sup_left (mem_rs.mpr hd'))
  rw [← hte, add_mul]
  refine add_mem (Submodule.mem_sup_right ?_)
    (Submodule.mem_sup_left (mem_rs.mpr (Ideal.mul_mem_right _ _ (mem_rs.mp he))))
  refine Submodule.span_mono ?_ (mul_mem_span_mul ht hr)
  rintro _ ⟨_, ⟨s, hs, rfl⟩, r', hr', rfl⟩
  exact ⟨s, hs, r', hr', rfl⟩

/-- **Lemmas 3(ii), 5(ii)**, the identity with an arbitrary `R`: for `K = ⟨S⟩ ⊆ D_c`,
`c ≤ n ≤ 2c` and `ℤ[M] = span R + Δ^{n−c}`,
`Δⁿ + (K − 1)A = Δⁿ + span_ℤ{(s − 1) r : s ∈ S, r ∈ R}`. -/
theorem pow_sup_KA_eq (K : Subgroup M) {S : Set M} (hS : Subgroup.closure S = K)
    (hK : K ≤ D c M) {R : Set (MonoidAlgebra ℤ M)}
    (hR : ∀ a, a ∈ Submodule.span ℤ R ⊔ (augIdeal M ^ (n - c)).restrictScalars ℤ)
    (hcn : c ≤ n) (hn : n ≤ 2 * c) :
    (augIdeal M ^ n).restrictScalars ℤ ⊔ KA K =
      (augIdeal M ^ n).restrictScalars ℤ ⊔
        Submodule.span ℤ {x | ∃ s ∈ S, ∃ r ∈ R, x = (of ℤ M s - 1) * r} := by
  have hS' : Subgroup.closure S ≤ D c M := by rw [hS]; exact hK
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, hk, g, rfl⟩
    exact sub_one_mul_mem_sup hS' hcn hn (by rw [hS]; exact hk) (hR _)
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro _ ⟨s, hs, r, _, rfl⟩
    exact Submodule.mem_sup_right
      (sub_one_mul_mem_KA (by rw [← hS]; exact Subgroup.subset_closure hs) r)

/-! ## Monomials in the generators: the paper's `R` and `R₊` -/

/-- `(x₁ − 1)(x₂ − 1)⋯(x_l − 1)`. -/
def monom (l : List M) : MonoidAlgebra ℤ M := (l.map fun x => of ℤ M x - 1).prod

theorem monom_cons (x : M) (l : List M) : monom (x :: l) = (of ℤ M x - 1) * monom l := by
  rw [monom, List.map_cons, List.prod_cons]; rfl

theorem monom_singleton (x : M) : monom [x] = of ℤ M x - 1 := by
  rw [monom, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem monom_append (l l' : List M) : monom (l ++ l') = monom l * monom l' := by
  rw [monom, List.map_append, List.prod_append]; rfl

theorem monom_mem_pow (l : List M) : monom l ∈ augIdeal M ^ l.length := by
  induction l with
  | nil => rw [List.length_nil, Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | cons x l ih =>
    rw [monom_cons, List.length_cons, add_comm]
    exact mul_mem_augIdeal_pow (by rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal x) ih

/-- The monomials `(x_{j₁} − 1)⋯(x_{j_l} − 1)` in elements of `X`, of length `1 ≤ l < m`. The paper's
`R₊` (for `U_n`) is `Rplus X (n − c)`; its `R` (Lemmas 3(ii), 5(ii)) is `insert 1 (Rplus X (n − c))`. -/
def Rplus (X : Set M) (m : ℕ) : Set (MonoidAlgebra ℤ M) :=
  {y | ∃ l : List M, (∀ x ∈ l, x ∈ X) ∧ 1 ≤ l.length ∧ l.length < m ∧ y = monom l}

theorem mem_augIdeal_of_mem_Rplus {X : Set M} {m : ℕ} {y : MonoidAlgebra ℤ M}
    (hy : y ∈ Rplus X m) : y ∈ augIdeal M := by
  obtain ⟨l, -, h1, -, rfl⟩ := hy
  have := Ideal.pow_le_pow_right h1 (monom_mem_pow l)
  rwa [Submodule.pow_one] at this

/-- If `w = −u + (−u) w` and `u ∈ P`, `P` closed under multiplication, then
`w ∈ P + (−u)^{j+1} w` for every `j`. -/
theorem exists_eq_add_pow_mul {P : Submodule ℤ (MonoidAlgebra ℤ M)}
    (hmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) {u w : MonoidAlgebra ℤ M} (hu : u ∈ P)
    (hw : w = -u + (-u) * w) : ∀ j : ℕ, ∃ s ∈ P, w = s + (-u) ^ (j + 1) * w
  | 0 => ⟨-u, neg_mem hu, by rw [zero_add, pow_one]; exact hw⟩
  | j + 1 => by
    obtain ⟨s, hs, hsw⟩ := exists_eq_add_pow_mul hmul hu hw j
    have hp : ∀ i : ℕ, (-u) ^ (i + 1) ∈ P := by
      intro i
      induction i with
      | zero => rw [zero_add, pow_one]; exact neg_mem hu
      | succ i ih => rw [pow_succ]; exact hmul _ ih _ (neg_mem hu)
    refine ⟨s + (-u) ^ (j + 1 + 1), add_mem hs (hp (j + 1)), ?_⟩
    calc w = s + (-u) ^ (j + 1) * w := hsw
      _ = s + (-u) ^ (j + 1) * (-u + (-u) * w) := by rw [← hw]
      _ = s + (-u) ^ (j + 1 + 1) + (-u) ^ (j + 1 + 1) * w := by
        rw [mul_add, ← mul_assoc, ← pow_succ]; abel

/-- **`Δ = span R₊ + Δ^m`**: if `X` generates `M`, every `g − 1` lies in the `ℤ`-span of the
monomials in `X` of length `1 ≤ l < m`, plus `Δ^m`. -/
theorem sub_one_mem_span_Rplus {X : Set M} (hX : Subgroup.closure X = ⊤) (m : ℕ) (g : M) :
    of ℤ M g - 1 ∈ Submodule.span ℤ (Rplus X m) ⊔ (augIdeal M ^ m).restrictScalars ℤ := by
  set P := Submodule.span ℤ (Rplus X m) ⊔ (augIdeal M ^ m).restrictScalars ℤ with hP
  have hmon : ∀ l : List M, (∀ x ∈ l, x ∈ X) → 1 ≤ l.length → monom l ∈ P := by
    intro l hl h1
    by_cases hlm : l.length < m
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, hl, h1, hlm, rfl⟩)
    · exact Submodule.mem_sup_right
        (mem_rs.mpr (Ideal.pow_le_pow_right (by omega) (monom_mem_pow l)))
  have hspan : ∀ a ∈ Submodule.span ℤ (Rplus X m), a ∈ augIdeal M := fun a ha =>
    mem_rs.mp ((Submodule.span_le (p := (augIdeal M).restrictScalars ℤ)).mpr
      (fun y hy => mem_rs.mpr (mem_augIdeal_of_mem_Rplus hy)) ha)
  have hmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P := by
    intro a ha b hb
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Submodule.mem_sup.mp hb
    rw [add_mul, mul_add]
    refine add_mem (add_mem ?_ ?_) (Submodule.mem_sup_right
      (mem_rs.mpr (Ideal.mul_mem_right _ _ (mem_rs.mp ha2))))
    · refine (Submodule.span_le (p := P)).mpr ?_ (mul_mem_span_mul ha1 hb1)
      rintro _ ⟨_, ⟨l, hl, hl1, -, rfl⟩, _, ⟨l', hl', -, -, rfl⟩, rfl⟩
      rw [← monom_append]
      refine hmon _ ?_ ?_
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        exacts [hl x h, hl' x h]
      · rw [List.length_append]; omega
    · exact Submodule.mem_sup_right
        (mem_rs.mpr (Ideal.mul_mem_left _ _ (mem_rs.mp hb2)))
  have hg : g ∈ Subgroup.closure X := by rw [hX]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rw [← monom_singleton]
    exact hmon [x] (by simpa using hx) (by simp)
  | one => rw [map_one, sub_self]; exact zero_mem _
  | mul x y _ _ hx hy =>
    rw [mul_sub_one_eq]
    exact add_mem (add_mem hx hy) (hmul _ hx _ hy)
  | inv x _ hx =>
    have hw : of ℤ M x⁻¹ - 1 = -(of ℤ M x - 1) + (-(of ℤ M x - 1)) * (of ℤ M x⁻¹ - 1) := by
      rw [neg_mul, ← sub_eq_add_neg]; exact inv_sub_one_eq x
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Submodule.mem_sup_right
        (mem_rs.mpr (by rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top))
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    obtain ⟨s, hs, hsw⟩ := exists_eq_add_pow_mul hmul hx hw j
    rw [hsw]
    refine add_mem hs (Submodule.mem_sup_right (mem_rs.mpr (Ideal.mul_mem_right _ _ ?_)))
    exact Ideal.pow_mem_pow (neg_mem (of_sub_one_mem_augIdeal x)) _

/-- **`Δ = span R₊ + Δ^m`** for a generating set `X` of `M`. -/
theorem augIdeal_le_span_Rplus {X : Set M} (hX : Subgroup.closure X = ⊤) (m : ℕ)
    {x : MonoidAlgebra ℤ M} (hx : x ∈ augIdeal M) :
    x ∈ Submodule.span ℤ (Rplus X m) ⊔ (augIdeal M ^ m).restrictScalars ℤ := by
  have hsub : Submodule.span ℤ {y | ∃ g : M, y = of ℤ M g - 1} ≤
      Submodule.span ℤ (Rplus X m) ⊔ (augIdeal M ^ m).restrictScalars ℤ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact sub_one_mem_span_Rplus hX m g
  exact hsub (mem_span_of_mem_augIdeal hx)

/-- **`ℤ[M] = span R + Δ^m`**, `R = {1} ∪ R₊`, for a generating set `X` of `M`. -/
theorem top_le_span_R {X : Set M} (hX : Subgroup.closure X = ⊤) (m : ℕ)
    (a : MonoidAlgebra ℤ M) :
    a ∈ Submodule.span ℤ (insert 1 (Rplus X m)) ⊔ (augIdeal M ^ m).restrictScalars ℤ := by
  have e : a = (a - augmentation M a • (1 : MonoidAlgebra ℤ M)) +
      augmentation M a • (1 : MonoidAlgebra ℤ M) := by abel
  have hsub : Submodule.span ℤ {y | ∃ g : M, y = of ℤ M g - 1} ≤
      Submodule.span ℤ (insert 1 (Rplus X m)) ⊔ (augIdeal M ^ m).restrictScalars ℤ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (sub_one_mem_span_Rplus hX m g)
    rw [← hyz]
    exact add_mem (Submodule.mem_sup_left (Submodule.span_mono (Set.subset_insert _ _) hy))
      (Submodule.mem_sup_right hz)
  rw [e]
  exact add_mem (hsub (sub_aug_mem_span a)) (Submodule.mem_sup_left (Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_insert _ _))))

/-- **Lemmas 3(ii), 5(ii)** in the paper's form: `X` generates `M`, `K = ⟨S⟩ ⊆ D_c`
(e.g. `K ⊆ γ_c(M)`), `c ≤ n ≤ 2c`, `R = span{1} ∪ {(x_{j₁} − 1)⋯(x_{j_l} − 1) : 1 ≤ l ≤ n − c − 1}`:
`(K − 1)A + Δⁿ = Δⁿ + Σ_{s ∈ S} ψ(s)·R`. -/
theorem lemma_ii {X : Set M} (hX : Subgroup.closure X = ⊤) (K : Subgroup M) {S : Set M}
    (hS : Subgroup.closure S = K) (hK : K ≤ D c M) (hcn : c ≤ n) (hn : n ≤ 2 * c) :
    (augIdeal M ^ n).restrictScalars ℤ ⊔ KA K =
      (augIdeal M ^ n).restrictScalars ℤ ⊔ Submodule.span ℤ
        {x | ∃ s ∈ S, ∃ r ∈ insert 1 (Rplus X (n - c)), x = (of ℤ M s - 1) * r} :=
  pow_sup_KA_eq K hS hK (top_le_span_R hX (n - c)) hcn hn

/-- **The paper's `U_n`**: for `C = ⟨B⟩ ⊆ D_c` (`B` the generators `b_t` of `A_c`), `X`
generating `M` and `c ≤ n ≤ 2c`, `U_n = Δⁿ + span{(b − 1) r : b ∈ B, r ∈ R₊}`,
`R₊ = Rplus X (n − c)` the monomials of degree `1..n − c − 1`. -/
theorem U_eq_span_Rplus {X : Set M} (hX : Subgroup.closure X = ⊤) {B : Set M}
    (hB : Subgroup.closure B = C) (hC : C ≤ D c M) (hcn : c ≤ n) (hn : n ≤ 2 * c) :
    U C n = (augIdeal M ^ n).restrictScalars ℤ ⊔
      Submodule.span ℤ {x | ∃ b ∈ B, ∃ r ∈ Rplus X (n - c), x = (of ℤ M b - 1) * r} := by
  have hB' : Subgroup.closure B ≤ D c M := by rw [hB]; exact hC
  unfold U
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, hk, d, hd, rfl⟩
    exact sub_one_mul_mem_sup hB' hcn hn (by rw [hB]; exact hk)
      (augIdeal_le_span_Rplus hX (n - c) hd)
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro _ ⟨b, hb, r, hr, rfl⟩
    exact Submodule.mem_sup_right (Submodule.subset_span
      ⟨b, by rw [← hB]; exact Subgroup.subset_closure hb, r, mem_augIdeal_of_mem_Rplus hr, rfl⟩)

/-! ## Propositions 4 and 6 -/

/-- Every element of `(K − 1)A` is `(k − 1)` modulo `U_n`, for some `k ∈ K` (`K ⊆ C ⊆ D_c`,
`n ≤ 2c`). -/
theorem exists_of_mem_KA {K : Subgroup M} (hKC : K ≤ C) (hC : C ≤ D c M) (hn : n ≤ 2 * c)
    {x : MonoidAlgebra ℤ M} (hx : x ∈ KA K) : ∃ k ∈ K, x - (of ℤ M k - 1) ∈ U C n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, g, rfl⟩ := hx
    refine ⟨k, hk, ?_⟩
    have e : (of ℤ M k - 1) * of ℤ M g - (of ℤ M k - 1) =
        (of ℤ M k - 1) * (of ℤ M g - 1) := by noncomm_ring
    rw [e]
    exact mem_U_of_mem_Wspan
      (Submodule.subset_span ⟨k, hKC hk, _, of_sub_one_mem_augIdeal g, rfl⟩)
  | zero => exact ⟨1, one_mem _, by rw [map_one, sub_self, sub_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk, hxk⟩ := hx
    obtain ⟨k', hk', hyk⟩ := hy
    refine ⟨k * k', mul_mem hk hk', ?_⟩
    have e : x + y - (of ℤ M (k * k') - 1) = (x - (of ℤ M k - 1)) + (y - (of ℤ M k' - 1)) -
        (of ℤ M k - 1) * (of ℤ M k' - 1) := by rw [mul_sub_one_eq]; abel
    rw [e]
    exact sub_mem (add_mem hxk hyk)
      (mem_U_of_mem_pow (sub_one_mul_sub_one_mem hn (hC (hKC hk)) (hC (hKC hk'))))
  | smul a x _ hx =>
    obtain ⟨k, hk, hxk⟩ := hx
    refine ⟨k ^ a, zpow_mem hk a, ?_⟩
    have e : a • x - (of ℤ M (k ^ a) - 1) = a • (x - (of ℤ M k - 1)) -
        ((of ℤ M (k ^ a) - 1) - a • (of ℤ M k - 1)) := by rw [smul_sub]; abel
    rw [e]
    exact sub_mem (Submodule.smul_mem _ a hxk)
      (mem_U_of_mem_pow (zpow_sub_one_sub_mem hn (hC (hKC hk)) a))

/-- **The key step of Propositions 4 and 6**: if `v ∈ C` and `v ∈ D_n(M/K)` (`K ⊆ C ⊆ D_c` normal,
`n ≤ 2c`), then `ψ(v) ≡ ψ(k) (mod U_n)` for some `k ∈ K`. -/
theorem exists_sub_mem_U (K : Subgroup M) [K.Normal] (hKC : K ≤ C) (hC : C ≤ D c M)
    (hn : n ≤ 2 * c) {v : M} (hv : QuotientGroup.mk' K v ∈ D n (M ⧸ K)) :
    ∃ k ∈ K, (of ℤ M v - 1) - (of ℤ M k - 1) ∈ U C n := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp ((mem_D_quotient_iff K n v).mp hv)
  obtain ⟨k, hk, hzk⟩ := exists_of_mem_KA hKC hC hn hz
  refine ⟨k, hk, ?_⟩
  rw [← hyz, add_sub_assoc]
  exact add_mem (mem_U_of_mem_pow (mem_rs.mp hy)) hzk

/-- **Propositions 4 and 6, converse**: every `v ∈ D_n(M/K) ∩ C` gives `vk⁻¹ ∈ ker ψ̄` for some
`k ∈ K`. -/
theorem exists_mem_ker (K : Subgroup M) [K.Normal] (hKC : K ≤ C) (hC : C ≤ D c M)
    (hn : n ≤ 2 * c) {v : M} (hvC : v ∈ C) (hv : QuotientGroup.mk' K v ∈ D n (M ⧸ K)) :
    ∃ (k : M) (hk : k ∈ K),
      (⟨v, hvC⟩ * (⟨k, hKC hk⟩ : C)⁻¹ : C) ∈ (psiBar C hC hn).ker := by
  obtain ⟨k, hk, hvk⟩ := exists_sub_mem_U K hKC hC hn hv
  refine ⟨k, hk, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, psiBar_apply, psiBar_apply,
    Multiplicative.ofAdd.injective.eq_iff, Submodule.Quotient.eq]
  exact hvk

/-- **Propositions 4 and 6, converse**: every `v ∈ D_n(M/K) ∩ C` with `v ∉ K` gives
`1 ≠ vk⁻¹ ∈ ker ψ̄` for some `k ∈ K`: the test is a filter. -/
theorem exists_ne_one_mem_ker (K : Subgroup M) [K.Normal] (hKC : K ≤ C) (hC : C ≤ D c M)
    (hn : n ≤ 2 * c) {v : M} (hvC : v ∈ C) (hvK : v ∉ K)
    (hv : QuotientGroup.mk' K v ∈ D n (M ⧸ K)) :
    ∃ z ∈ (psiBar C hC hn).ker, z ≠ 1 ∧ ∃ k ∈ K, (z : M) = v * k⁻¹ := by
  obtain ⟨k, hk, hz⟩ := exists_mem_ker K hKC hC hn hvC hv
  refine ⟨_, hz, fun h1 => hvK ?_, k, hk, rfl⟩
  rw [mul_inv_eq_one] at h1
  have : v = k := congrArg Subtype.val h1
  rw [this]; exact hk

/-- **Propositions 4 and 6, converse**: `D_n(M) ∩ C ⊆ ker ψ̄` (the case `K = 1`). -/
theorem D_inf_le_ker (hC : C ≤ D c M) (hn : n ≤ 2 * c) :
    (D n M).subgroupOf C ≤ (psiBar C hC hn).ker := by
  intro k hk
  rw [mem_ker_psiBar]
  exact mem_U_of_mem_pow (Subgroup.mem_subgroupOf.mp hk)

/-- If `ψ̄` is injective, `v ∈ C` and `v ∈ D_n(M/K)`, then `v ∈ K`. -/
theorem mem_of_mem_D_quotient (K : Subgroup M) [K.Normal] (hKC : K ≤ C) (hC : C ≤ D c M)
    (hn : n ≤ 2 * c) (hinj : (psiBar C hC hn).ker = ⊥) {v : M} (hvC : v ∈ C)
    (hv : QuotientGroup.mk' K v ∈ D n (M ⧸ K)) : v ∈ K := by
  obtain ⟨k, hk, hz⟩ := exists_mem_ker K hKC hC hn hvC hv
  rw [hinj, Subgroup.mem_bot, mul_inv_eq_one] at hz
  have : v = k := congrArg Subtype.val hz
  rw [this]; exact hk

/-- **Propositions 4 and 6**: if `ψ̄ : C → ℤ[M]/U_n` is injective (`C ⊆ D_c`, `n ≤ 2c`), then
`D_n(M/K) ∩ C/K = 1` for **every** normal `K ⊆ C` at once. -/
theorem D_quotient_inf_map_eq_bot (K : Subgroup M) [K.Normal] (hKC : K ≤ C) (hC : C ≤ D c M)
    (hn : n ≤ 2 * c) (hinj : (psiBar C hC hn).ker = ⊥) :
    D n (M ⧸ K) ⊓ C.map (QuotientGroup.mk' K) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hD, v, hvC, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact mem_of_mem_D_quotient K hKC hC hn hinj hvC hD

/-! ## The kernel of `ψ̄`: monotonicity, `D_{c+1}`, torsion, the elements of order `2` -/

theorem U_mono {n n' : ℕ} (h : n ≤ n') : U C n' ≤ U C n :=
  sup_le_sup_right (fun _ hx => mem_rs.mpr (Ideal.pow_le_pow_right h (mem_rs.mp hx))) _

/-- `ker ψ̄_{n'} ⊆ ker ψ̄_n` for `n ≤ n' ≤ 2c`: injectivity at `n` gives it at every larger `n'`. -/
theorem ker_psiBar_mono (hC : C ≤ D c M) {n n' : ℕ} (h : n ≤ n') (hn : n ≤ 2 * c)
    (hn' : n' ≤ 2 * c) : (psiBar C hC hn').ker ≤ (psiBar C hC hn).ker := by
  intro k hk
  rw [mem_ker_psiBar] at hk ⊢
  exact U_mono h hk

/-- `U_n ⊆ Δ^{c+1}` for `c + 1 ≤ n`. -/
theorem U_le (hC : C ≤ D c M) (hcn : c + 1 ≤ n) {x : MonoidAlgebra ℤ M} (hx : x ∈ U C n) :
    x ∈ augIdeal M ^ (c + 1) := by
  have hle : U C n ≤ (augIdeal M ^ (c + 1)).restrictScalars ℤ := by
    refine sup_le (fun y hy => mem_rs.mpr (Ideal.pow_le_pow_right hcn (mem_rs.mp hy)))
      (Submodule.span_le.mpr ?_)
    rintro _ ⟨k, hk, d, hd, rfl⟩
    exact mem_rs.mpr (mul_mem_augIdeal_pow (hC hk) (by rwa [Submodule.pow_one]))
  exact mem_rs.mp (hle hx)

/-- `ker ψ̄ ⊆ D_{c+1}(M)` for `c + 1 ≤ n`. -/
theorem ker_le_D (hC : C ≤ D c M) (hn : n ≤ 2 * c) (hcn : c + 1 ≤ n) {z : C}
    (hz : z ∈ (psiBar C hC hn).ker) : (z : M) ∈ D (c + 1) M :=
  U_le hC hcn ((mem_ker_psiBar hC hn z).mp hz)

/-- For `n = c + 1` the paper's `R₊` is empty: `U_{c+1} = Δ^{c+1}` ("`U₆ = J₆`"). -/
theorem U_succ_eq (hC : C ≤ D c M) : U C (c + 1) = (augIdeal M ^ (c + 1)).restrictScalars ℤ :=
  le_antisymm (fun _ h => mem_rs.mpr (U_le hC le_rfl h)) (fun _ h => mem_U_of_mem_pow (mem_rs.mp h))

/-- For `n = c + 1`: `ker ψ̄ = D_{c+1} ∩ C`
("for `n = 6`, `U₆ = J₆`: the test is just `D₆(M) ∩ γ₅`"). -/
theorem ker_psiBar_of_eq (hC : C ≤ D c M) (hn : n ≤ 2 * c) (hcn : n = c + 1) :
    (psiBar C hC hn).ker = (D n M).subgroupOf C := by
  subst hcn
  ext k
  rw [mem_ker_psiBar, Subgroup.mem_subgroupOf]
  exact ⟨fun h => U_le hC le_rfl h, fun h => mem_U_of_mem_pow h⟩

/-- If no `g ≠ 1` of a subgroup `H` has `g² = 1`, then no `g ≠ 1` of `H` has `g^{2^k} = 1`. -/
theorem eq_one_of_pow_two_pow_eq_one {G : Type*} [Group G] (H : Subgroup G)
    (h : ∀ g ∈ H, g ^ 2 = 1 → g = 1) : ∀ (k : ℕ) (g : G), g ∈ H → g ^ 2 ^ k = 1 → g = 1
  | 0, g, _, hk => by rwa [pow_zero, pow_one] at hk
  | k + 1, g, hg, hk => by
    refine eq_one_of_pow_two_pow_eq_one H h k g hg ?_
    refine h _ (pow_mem hg _) ?_
    rw [← pow_mul, ← pow_succ, hk]

end

/-- **Propositions 4 and 6, torsion of `ker ψ̄`**: given Jennings' theorem (`JenningsIsolator`, a
hypothesis), for `M` finitely generated of class `≤ c` and `c + 1 ≤ n ≤ 2c`, every element of
`ker ψ̄` has finite order (`ker ψ̄ ⊆ D_{c+1}(M) ⊆ √γ_{c+1}(M) = τ(M)`). -/
theorem isOfFinOrder_of_mem_ker (hJ : JenningsIsolator) {G : Type} [Group G] (hfg : Group.FG G)
    {c n : ℕ} (hG : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) (C : Subgroup G)
    (hC : C ≤ D c G) (hn : n ≤ 2 * c) (hcn : c + 1 ≤ n) {z : C}
    (hz : z ∈ (psiBar C hC hn).ker) : IsOfFinOrder (z : G) := by
  obtain ⟨m, hm, hzm⟩ := hJ G hfg (Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c, hG⟩) (c + 1)
    (by omega) (z : G) (ker_le_D hC hn hcn hz)
  rw [Nat.add_sub_cancel, hG, Subgroup.mem_bot] at hzm
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hzm⟩

/-- **Propositions 4 and 6: it is enough to test the elements of order 2.** Given Jennings'
theorem (hypothesis), for `M` finitely generated of class `≤ c`, `c + 1 ≤ n ≤ 2c`, and `C` whose
elements of finite order have `2`-power order (in the paper: `τ(A_c)` a `2`-group): `ψ̄` is
injective iff no `z ≠ 1` of `C` with `z² = 1` lies in `ker ψ̄`. -/
theorem ker_eq_bot_iff_two (hJ : JenningsIsolator) {G : Type} [Group G] (hfg : Group.FG G)
    {c n : ℕ} (hG : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) (C : Subgroup G)
    (hC : C ≤ D c G) (hn : n ≤ 2 * c) (hcn : c + 1 ≤ n)
    (h2 : ∀ g ∈ C, IsOfFinOrder g → ∃ k : ℕ, g ^ 2 ^ k = 1) :
    (psiBar C hC hn).ker = ⊥ ↔
      ∀ z : C, (z : G) ^ 2 = 1 → psiBar C hC hn z = 1 → z = 1 := by
  constructor
  · intro h z _ hz
    have : z ∈ (psiBar C hC hn).ker := MonoidHom.mem_ker.mpr hz
    rwa [h, Subgroup.mem_bot] at this
  · intro h
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := h2 z z.2 (isOfFinOrder_of_mem_ker hJ hfg hG C hC hn hcn hz)
    refine eq_one_of_pow_two_pow_eq_one _ (fun g hg hg2 => h g ?_ (MonoidHom.mem_ker.mp hg)) k z hz ?_
    · rw [← Subgroup.coe_pow, hg2, Subgroup.coe_one]
    · exact Subtype.ext (by rw [Subgroup.coe_pow, hk, Subgroup.coe_one])

/-! ## Removing `∩ γ_c` (§6.10) -/

section Removing

variable {M : Type*} [Group M] {c n : ℕ}

/-- **Removing `∩ γ_c`** (§6.10): if `ψ̄_n` is injective (`C ⊆ D_c` normal, `n ≤ 2c`) and
`D_n(M/C) = 1`, then `D_n(M/K) = 1` for every normal `K ⊆ C`: the image of `D_n(M/K)` in `M/C`
lies in `D_n(M/C)`. For the paper, `C = γ_c(M)` and `M/C = Q`. -/
theorem D_quotient_eq_bot (C K : Subgroup M) [C.Normal] [K.Normal] (hKC : K ≤ C)
    (hC : C ≤ D c M) (hn : n ≤ 2 * c) (hinj : (psiBar C hC hn).ker = ⊥)
    (hQ : D n (M ⧸ C) = ⊥) : D n (M ⧸ K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K x
  have h1 : QuotientGroup.mk' C v ∈ D n (M ⧸ C) :=
    map_mem_D (QuotientGroup.map K C (MonoidHom.id M) (fun y hy => hKC hy)) hx
  rw [hQ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact mem_of_mem_D_quotient K hKC hC hn hinj h1 hx

/-- **Removing `∩ γ_c`**, with `D_m(M/C) = 1` for some `m ≤ n` (§6.8(b): `D₄(M/γ₄) = 1` from (a);
§6.10: `D₅(Q) = 1`, so `D₈(Q) = 1`). -/
theorem D_quotient_eq_bot_of_le (C K : Subgroup M) [C.Normal] [K.Normal] (hKC : K ≤ C)
    (hC : C ≤ D c M) (hn : n ≤ 2 * c) (hinj : (psiBar C hC hn).ker = ⊥) {m : ℕ} (hmn : m ≤ n)
    (hQ : D m (M ⧸ C) = ⊥) : D n (M ⧸ K) = ⊥ := by
  have h : D n (M ⧸ C) ≤ D m (M ⧸ C) := D_antitone hmn
  rw [hQ] at h
  exact D_quotient_eq_bot C K hKC hC hn hinj (le_bot_iff.mp h)

/-- §6.10: `D₅(Q) = 1` from `D₅(Q/γ₄(Q)) = 1` (Lemma 1) and the injectivity of
`ψ̄₅ : γ₄(Q) → Δ⁴/Δ⁵` (i.e. `D₅(Q) ∩ γ₄(Q) = 1`), by Corollary 2. -/
theorem D_five_eq_bot (G : Type*) [Group G]
    (hQ3 : D 5 (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 3) = ⊥)
    (hinj : (psiBar ((⊤ : Subgroup G).lowerCentralSeries 3) (c := 4) (n := 5)
      (lowerCentralSeries_le_D G 3) (by norm_num)).ker = ⊥) : D 5 G = ⊥ := by
  have hk := ker_psiBar_of_eq (C := (⊤ : Subgroup G).lowerCentralSeries 3) (c := 4) (n := 5)
    (lowerCentralSeries_le_D G 3) (by norm_num) rfl
  have hk' : (D 5 G).subgroupOf ((⊤ : Subgroup G).lowerCentralSeries 3) = ⊥ := hk.symm.trans hinj
  have hd : Disjoint (D 5 G) ((⊤ : Subgroup G).lowerCentralSeries 3) :=
    Subgroup.subgroupOf_eq_bot.mp hk'
  exact ClassThree.D_eq_bot_of_inf_gammaFour_eq_bot hQ3 le_rfl (disjoint_iff.mp hd)

end Removing

/-! ## The paper's instances: `c = 4` (Lemma 3, Proposition 4) and `c = 5` (Lemma 5, Proposition 6) -/

section Paper

open scoped commutatorElement

variable {M : Type*} [Group M]

/-- In a group of class `≤ j + 1` (`γ_{j+2} = 1`), `γ_{j+1}` is central. -/
theorem lcs_le_center {j : ℕ} (hM : (⊤ : Subgroup M).lowerCentralSeries (j + 1) = ⊥) :
    (⊤ : Subgroup M).lowerCentralSeries j ≤ Subgroup.center M := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have h : ⁅k, g⁆ ∈ (⊤ : Subgroup M).lowerCentralSeries (j + 1) :=
    Subgroup.commutator_mem_commutator hk (Subgroup.mem_top g)
  rw [hM, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at h
  exact h.eq.symm

/-- A subgroup of the center is normal. -/
theorem normal_of_le_center {K : Subgroup M} (hK : K ≤ Subgroup.center M) : K.Normal :=
  ⟨fun k hk g => by
    rw [Subgroup.mem_center_iff.mp (hK hk) g, mul_inv_cancel_right]; exact hk⟩

/-- In a group of class `≤ j + 1`, every subgroup of `γ_{j+1}` is normal (the paper's
`K ⊆ γ_c(M)`, `M` of class `c`). -/
theorem normal_of_le_lcs {j : ℕ} (hM : (⊤ : Subgroup M).lowerCentralSeries (j + 1) = ⊥)
    {K : Subgroup M} (hK : K ≤ (⊤ : Subgroup M).lowerCentralSeries j) : K.Normal :=
  normal_of_le_center (hK.trans (lcs_le_center hM))

/-- **Proposition 4** (`c = 4`, `n ≤ 8`): if `ψ̄ : γ₄(M) → ℤ[M]/U_n` is injective, then
`D_n(M/K) ∩ γ₄(M)/K = 1` for every normal `K ⊆ γ₄(M)` (every `K ⊆ γ₄(M)` when `γ₅(M) = 1`,
`normal_of_le_lcs`). -/
theorem prop4 {n : ℕ} (hn : n ≤ 2 * 4)
    (hinj : (psiBar ((⊤ : Subgroup M).lowerCentralSeries 3) (c := 4)
      (lowerCentralSeries_le_D M 3) hn).ker = ⊥)
    (K : Subgroup M) [K.Normal] (hK : K ≤ (⊤ : Subgroup M).lowerCentralSeries 3) :
    D n (M ⧸ K) ⊓ ((⊤ : Subgroup M).lowerCentralSeries 3).map (QuotientGroup.mk' K) = ⊥ :=
  D_quotient_inf_map_eq_bot K hK _ hn hinj

/-- **Proposition 6** (`c = 5`, `n ≤ 10`): if `ψ̄ : γ₅(M) → ℤ[M]/U_n` is injective, then
`D_n(M/K) ∩ γ₅(M)/K = 1` for every normal `K ⊆ γ₅(M)`. -/
theorem prop6 {n : ℕ} (hn : n ≤ 2 * 5)
    (hinj : (psiBar ((⊤ : Subgroup M).lowerCentralSeries 4) (c := 5)
      (lowerCentralSeries_le_D M 4) hn).ker = ⊥)
    (K : Subgroup M) [K.Normal] (hK : K ≤ (⊤ : Subgroup M).lowerCentralSeries 4) :
    D n (M ⧸ K) ⊓ ((⊤ : Subgroup M).lowerCentralSeries 4).map (QuotientGroup.mk' K) = ⊥ :=
  D_quotient_inf_map_eq_bot K hK _ hn hinj

/-- **Removing `∩ γ₅`** (§6.10), the paper's form: `D_n(M/γ₅(M)) = 1` and `ψ̄_n` injective
(`n ≤ 10`) give `D_n(M/K) = 1` for every normal `K ⊆ γ₅(M)`. -/
theorem removing_gammaFive {n : ℕ} (hn : n ≤ 2 * 5)
    (hinj : (psiBar ((⊤ : Subgroup M).lowerCentralSeries 4) (c := 5)
      (lowerCentralSeries_le_D M 4) hn).ker = ⊥)
    (hQ : D n (M ⧸ (⊤ : Subgroup M).lowerCentralSeries 4) = ⊥)
    (K : Subgroup M) [K.Normal] (hK : K ≤ (⊤ : Subgroup M).lowerCentralSeries 4) :
    D n (M ⧸ K) = ⊥ :=
  D_quotient_eq_bot _ K hK _ hn hinj hQ

end Paper

/-! ## Reduction used (§6.6): cocyclic quotients -/

section Cocyclic

variable {B : Type*} [Group B]

theorem pow_div_prime {x : B} (hx : orderOf x ≠ 0) {q : ℕ} (hq : q.Prime) (hqd : q ∣ orderOf x) :
    (x ^ (orderOf x / q)) ^ q = 1 ∧ x ^ (orderOf x / q) ≠ 1 := by
  refine ⟨by rw [← pow_mul, Nat.div_mul_cancel hqd, pow_orderOf_eq_one], fun h => ?_⟩
  have h1 := orderOf_dvd_of_pow_eq_one h
  have hpos : 0 < orderOf x / q :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hx) hqd) hq.pos
  have hlt : orderOf x / q < orderOf x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) hq.one_lt
  exact absurd (Nat.le_of_dvd hpos h1) (not_le.mpr hlt)

variable {b : B} (hb : b ≠ 1) (h : ∀ H : Subgroup B, H ≠ ⊥ → b ∈ H)
include hb h

/-- In a group where every nontrivial subgroup contains a fixed `b ≠ 1`, every element has
finite order. -/
theorem cocyclic_isOfFinOrder (a : B) : IsOfFinOrder a := by
  by_cases ha : a = 1
  · rw [ha]; exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow 1⟩
  by_contra hfin
  have hinj := injective_zpow_iff_not_isOfFinOrder.mpr hfin
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (h _ (Subgroup.zpowers_ne_bot.mpr ha))
  have hj0 : j ≠ 0 := by
    rintro rfl; rw [zpow_zero] at hj; exact hb hj.symm
  have ha2 : a ^ (2 * j) ≠ 1 := fun h2 => by
    have := hinj (h2.trans (zpow_zero a).symm)
    omega
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h _ (Subgroup.zpowers_ne_bot.mpr ha2))
  rw [← hj, ← zpow_mul] at hk
  have h3 : 2 * j * k = j := hinj hk
  have h4 : j * (2 * k - 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact hj0 h5
  · omega

/-- … `b` has prime order. -/
theorem cocyclic_prime : (orderOf b).Prime := by
  have h0 : orderOf b ≠ 0 := (orderOf_pos_iff.mpr (cocyclic_isOfFinOrder hb h b)).ne'
  have h1 : orderOf b ≠ 1 := fun h1 => hb (orderOf_eq_one_iff.mp h1)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨hcq, hc1⟩ := pow_div_prime h0 hq hqd
  have hdq : orderOf b ∣ q := (orderOf_dvd_of_mem_zpowers (h _ (Subgroup.zpowers_ne_bot.mpr hc1))).trans
    (orderOf_dvd_of_pow_eq_one hcq)
  rwa [Nat.dvd_antisymm hdq hqd]

/-- … `B` is a `p`-group, `p` the order of `b`. -/
theorem cocyclic_isPGroup : IsPGroup (orderOf b) B := by
  have hp := cocyclic_prime hb h
  intro a
  by_cases ha : a = 1
  · exact ⟨0, by rw [ha, one_pow]⟩
  have h0 : orderOf a ≠ 0 := (orderOf_pos_iff.mpr (cocyclic_isOfFinOrder hb h a)).ne'
  have e := Nat.eq_prime_pow_of_unique_prime_dvd h0 (p := orderOf b) (by
    intro q hq hqd
    obtain ⟨hcq, hc1⟩ := pow_div_prime h0 hq hqd
    have hdq : orderOf b ∣ q :=
      (orderOf_dvd_of_mem_zpowers (h _ (Subgroup.zpowers_ne_bot.mpr hc1))).trans
        (orderOf_dvd_of_pow_eq_one hcq)
    exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdq).symm)
  exact ⟨_, by rw [← e, pow_orderOf_eq_one]⟩

omit hb h in
/-- If `z^p = 1` (`p` prime) and `1 ≠ b ∈ ⟨z⟩`, then `z ∈ ⟨b⟩`. -/
theorem mem_zpowers_of_pow_prime {p : ℕ} (hp : p.Prime) {z : B} (hb : b ≠ 1)
    (hbz : b ∈ Subgroup.zpowers z) (hz : z ^ p = 1) : z ∈ Subgroup.zpowers b := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbz
  have hpi : ¬ (p : ℤ) ∣ i := by
    rintro ⟨j, rfl⟩
    apply hb
    rw [zpow_mul, zpow_natCast, hz, one_zpow]
  obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hpi
  refine Subgroup.mem_zpowers_iff.mpr ⟨v, ?_⟩
  calc (z ^ i) ^ v = (z ^ (p : ℤ)) ^ u * (z ^ i) ^ v := by
        rw [zpow_natCast, hz, one_zpow, one_mul]
    _ = z ^ (u * p + v * i) := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (p : ℤ) u, mul_comm i v]
    _ = z := by rw [huv, zpow_one]

/-- … if `B` is abelian and finitely generated, it is finite. -/
theorem cocyclic_finite (hcomm : ∀ x y : B, x * y = y * x) [hfg : Group.FG B] : Finite B := by
  let inst : CommGroup B := { (inferInstance : Group B) with mul_comm := hcomm }
  have hfg' : @Group.FG B inst.toGroup := by exact hfg
  exact CommGroup.finite_of_fg_isMulTorsion B (fun a => by exact cocyclic_isOfFinOrder hb h a)

/-- … if `B` is abelian and finite, it is cyclic. -/
theorem cocyclic_isCyclic (hcomm : ∀ x y : B, x * y = y * x) [Finite B] : IsCyclic B := by
  have hp := cocyclic_prime hb h
  have hpg := cocyclic_isPGroup hb h
  set p := orderOf b with hp_def
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := Finite.exists_max (orderOf : B → ℕ)
  have hexp : ∀ x : B, x ^ orderOf a = 1 := by
    intro x
    obtain ⟨f, hf⟩ := (IsPGroup.iff_orderOf.mp hpg) x
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hpg) a
    have hle := ha x
    rw [hf, he] at hle
    have hfe : f ≤ e := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    rw [← orderOf_dvd_iff_pow_eq_one, hf, he]
    exact Nat.pow_dvd_pow p hfe
  have ha1 : a ≠ 1 := by
    intro ha1
    have := ha b
    rw [ha1, orderOf_one] at this
    have := hp.two_le
    omega
  have hba : Subgroup.zpowers b ≤ Subgroup.zpowers a :=
    Subgroup.zpowers_le.mpr (h _ (Subgroup.zpowers_ne_bot.mpr ha1))
  have key : ∀ N : ℕ, ∀ x : B, orderOf x = N → x ∈ Subgroup.zpowers a := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro x hxN
      by_cases hx1 : x = 1
      · rw [hx1]; exact one_mem _
      have hx0 : orderOf x ≠ 0 := (orderOf_pos_iff.mpr (cocyclic_isOfFinOrder hb h x)).ne'
      have hpx : p ∣ orderOf x :=
        orderOf_dvd_of_mem_zpowers (h _ (Subgroup.zpowers_ne_bot.mpr hx1))
      have hylt : orderOf (x ^ p) < N := by
        rw [← hxN]
        have hd : orderOf (x ^ p) ∣ orderOf x / p := by
          apply orderOf_dvd_of_pow_eq_one
          rw [← pow_mul, Nat.mul_div_cancel' hpx, pow_orderOf_eq_one]
        exact lt_of_le_of_lt
          (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hpx) hp.pos) hd)
          (Nat.div_lt_self (Nat.pos_of_ne_zero hx0) hp.one_lt)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (ih _ hylt (x ^ p) rfl)
      obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hpg) a
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := by
        refine ⟨e - 1, ?_⟩
        rcases Nat.eq_zero_or_pos e with rfl | he0
        · rw [pow_zero, orderOf_eq_one_iff] at he; exact absurd he ha1
        · omega
      have hpj : (p : ℤ) ∣ j := by
        have h1 : a ^ (j * (p : ℤ) ^ e') = 1 := by
          rw [zpow_mul, hj, ← Nat.cast_pow, zpow_natCast, ← pow_mul, ← pow_succ', ← he, hexp]
        have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
        rw [he, Nat.cast_pow, pow_succ'] at h2
        exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))).mp h2
      obtain ⟨j', rfl⟩ := hpj
      have hz : (x * (a ^ j')⁻¹) ^ p = 1 := by
        rw [Commute.mul_pow (hcomm x (a ^ j')⁻¹) p, inv_pow, ← zpow_natCast (a ^ j') p,
          ← zpow_mul, mul_comm j' (p : ℤ), hj, mul_inv_cancel]
      have hzb : x * (a ^ j')⁻¹ ∈ Subgroup.zpowers b := by
        by_cases hz1 : x * (a ^ j')⁻¹ = 1
        · rw [hz1]; exact one_mem _
        exact mem_zpowers_of_pow_prime hp hb (h _ (Subgroup.zpowers_ne_bot.mpr hz1)) hz
      have := mul_mem (hba hzb) (zpow_mem (Subgroup.mem_zpowers a) j')
      rwa [inv_mul_cancel_right] at this
  exact isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨a, eq_top_iff.mpr fun x _ => key _ x rfl⟩

end Cocyclic

section Reduction

variable {M : Type*} [Group M]

/-- **Zorn**: for `K ⊆ C` and `v ∉ K` there is `K' ⊇ K` inside `C`, maximal with `v ∉ K'`. -/
theorem exists_maximal_avoiding (C K : Subgroup M) (hKC : K ≤ C) {v : M} (hvK : v ∉ K) :
    ∃ K' : Subgroup M, K ≤ K' ∧ K' ≤ C ∧ v ∉ K' ∧
      ∀ H : Subgroup M, K' ≤ H → H ≤ C → v ∉ H → H ≤ K' := by
  have hz := zorn_le_nonempty₀ {H : Subgroup M | H ≤ C ∧ v ∉ H} (by
    intro c hcs hc y hy
    refine ⟨sSup c, ⟨sSup_le fun H hH => (hcs hH).1, ?_⟩, fun z hz => le_sSup hz⟩
    rw [Subgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hc.directedOn]
    rintro ⟨H, hH, hvH⟩
    exact (hcs hH).2 hvH) K ⟨hKC, hvK⟩
  obtain ⟨K', hKK', hmax⟩ := hz
  exact ⟨K', hKK', hmax.prop.1, hmax.prop.2, fun H h1 h2 h3 => hmax.2 ⟨h2, h3⟩ h1⟩

/-- **Reduction used (§6.6)**: let `C` be central and finitely generated (the paper's
`C = γ₄(M)`, `M` of class `4`, finitely generated), `K ⊆ C` normal and `v ∈ C ∖ K` with
`v ∈ D_n(M/K)`. Then there is a normal `K'` with `K ⊆ K' ⊆ C`, `v ∉ K'`, `v ∈ D_n(M/K')`, such that
every subgroup `H` with `K' ⊊ H ⊆ C` contains `v` (so `v` generates the unique minimal subgroup of
`C/K'`), and `C/K'` is a finite cyclic `p`-group, `p` the order of `v` in `C/K'`, a prime. -/
theorem reduction_cocyclic (C K : Subgroup M) (hCc : C ≤ Subgroup.center M) [Group.FG C]
    [K.Normal] (hKC : K ≤ C) {n : ℕ} {v : M} (hvC : v ∈ C) (hvK : v ∉ K)
    (hv : QuotientGroup.mk' K v ∈ D n (M ⧸ K)) :
    ∃ (K' : Subgroup M) (_ : K'.Normal), K ≤ K' ∧ K' ≤ C ∧ v ∉ K' ∧
      QuotientGroup.mk' K' v ∈ D n (M ⧸ K') ∧
      (∀ H : Subgroup M, K' ≤ H → H ≤ C → H ≠ K' → v ∈ H) ∧
      (orderOf ((⟨v, hvC⟩ : C) : C ⧸ K'.subgroupOf C)).Prime ∧
      IsPGroup (orderOf ((⟨v, hvC⟩ : C) : C ⧸ K'.subgroupOf C)) (C ⧸ K'.subgroupOf C) ∧
      Finite (C ⧸ K'.subgroupOf C) ∧ IsCyclic (C ⧸ K'.subgroupOf C) := by
  obtain ⟨K', hKK', hK'C, hvK', hmax⟩ := exists_maximal_avoiding C K hKC hvK
  have hK'n : K'.Normal := normal_of_le_center (hK'C.trans hCc)
  have hD : QuotientGroup.mk' K' v ∈ D n (M ⧸ K') :=
    map_mem_D (QuotientGroup.map K K' (MonoidHom.id M) (fun y hy => hKK' hy)) hv
  have hmax' : ∀ H : Subgroup M, K' ≤ H → H ≤ C → H ≠ K' → v ∈ H := by
    intro H h1 h2 h3
    by_contra hvH
    exact h3 (le_antisymm (hmax H h1 h2 hvH) h1)
  set Q := C ⧸ K'.subgroupOf C
  set b : Q := ((⟨v, hvC⟩ : C) : Q) with hb_def
  have hb : b ≠ 1 := by
    rw [hb_def, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hvK'
  have hcomm : ∀ x y : Q, x * y = y * x := by
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hCc x.2) y).symm
  have hsub : ∀ H' : Subgroup Q, H' ≠ ⊥ → b ∈ H' := by
    intro H' hH'
    obtain ⟨q, hqH, hq1⟩ : ∃ q ∈ H', q ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hH' ((Subgroup.eq_bot_iff_forall H').mpr hcon)
    set L : Subgroup M := (H'.comap (QuotientGroup.mk' (K'.subgroupOf C))).map C.subtype
    have hK'L : K' ≤ L := by
      intro k hk
      refine ⟨⟨k, hK'C hk⟩, ?_, rfl⟩
      show QuotientGroup.mk' (K'.subgroupOf C) ⟨k, hK'C hk⟩ ∈ H'
      rw [QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)]
      exact one_mem _
    have hLC : L ≤ C := Subgroup.map_subtype_le _
    have hLK' : L ≠ K' := by
      intro hLK
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
      have hcL : (c : M) ∈ L := ⟨c, hqH, rfl⟩
      rw [hLK] at hcL
      exact hq1 ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcL))
    obtain ⟨c, hc, hcv⟩ := hmax' L hK'L hLC hLK'
    have : c = ⟨v, hvC⟩ := Subtype.ext hcv
    rw [this] at hc
    exact hc
  have hfin : Finite Q := cocyclic_finite hb hsub hcomm
  refine ⟨K', hK'n, hKK', hK'C, hvK', hD, hmax', cocyclic_prime hb hsub,
    cocyclic_isPGroup hb hsub, hfin, cocyclic_isCyclic hb hsub hcomm⟩

/-- **Reduction used (§6.6), with `C_{2^m}`**: as `reduction_cocyclic`, and if moreover
`v^{2^j} ∈ K` for some `j` (in the paper `τ(γ₄)` is a `2`-group), then `v² ∈ K'` and there is a
surjection `φ : C ↠ C_{2^m}` (`Multiplicative (ZMod (2^m))`) with kernel `K'`: it suffices to test
the cocyclic quotients `M/ker φ`, and in each the element `v` of order `2` of `C/ker φ`. -/
theorem reduction_cocyclic_two (C K : Subgroup M) (hCc : C ≤ Subgroup.center M) [Group.FG C]
    [K.Normal] (hKC : K ≤ C) {n : ℕ} {v : M} (hvC : v ∈ C) (hvK : v ∉ K)
    (hv : QuotientGroup.mk' K v ∈ D n (M ⧸ K)) (hv2 : ∃ j : ℕ, v ^ 2 ^ j ∈ K) :
    ∃ (K' : Subgroup M) (_ : K'.Normal), K ≤ K' ∧ K' ≤ C ∧ v ∉ K' ∧ v ^ 2 ∈ K' ∧
      QuotientGroup.mk' K' v ∈ D n (M ⧸ K') ∧
      (∀ H : Subgroup M, K' ≤ H → H ≤ C → H ≠ K' → v ∈ H) ∧
      ∃ (m : ℕ) (φ : C →* Multiplicative (ZMod (2 ^ m))),
        Function.Surjective φ ∧ φ.ker = K'.subgroupOf C := by
  obtain ⟨K', hK'n, hKK', hK'C, hvK', hD, hmax', hp, hpg, hfin, hcyc⟩ :=
    reduction_cocyclic C K hCc hKC hvC hvK hv
  have := hK'n
  have := hfin
  set b : C ⧸ K'.subgroupOf C := ((⟨v, hvC⟩ : C) : C ⧸ K'.subgroupOf C) with hb_def
  obtain ⟨j, hj⟩ := hv2
  have hbj : b ^ 2 ^ j = 1 := by
    rw [hb_def, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hKK' hj
  have h2 : orderOf b = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (orderOf_dvd_of_pow_eq_one hbj))
  have hv2' : v ^ 2 ∈ K' := by
    have hb2 : b ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one b
    rw [hb_def, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow] at hb2
    exact hb2
  rw [h2] at hpg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hpg)
  obtain ⟨e⟩ : Nonempty (Multiplicative (ZMod (Nat.card (C ⧸ K'.subgroupOf C))) ≃*
      (C ⧸ K'.subgroupOf C)) := ⟨zmodCyclicMulEquiv hcyc⟩
  rw [hm] at e
  refine ⟨K', hK'n, hKK', hK'C, hvK', hv2', hD, hmax', m,
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (K'.subgroupOf C)), ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Reduction

end GroupDimension.Kernel.KFree
