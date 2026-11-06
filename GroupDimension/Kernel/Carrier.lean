module

public import GroupDimension.Kernel.Decomposition

@[expose] public section

/-!
# The carrier identity: Lemma 13, Theorem 14, Lemma 15, Proposition 16
(fast-core paper, §6.12; MATH-312)

`cflint-fast-core`, `docs/analysis.md`, §6.12. Notation of §6.11: `d_l = [t, x_l] ∈ γ_k`, `X_i = x_i − 1`,
`E_i = 2^{e_i}` with `P_i = x_i^{E_i} ∈ γ_k`; `[a, b] = a⁻¹b⁻¹ab` (`pc`).

> **Lemma 13** (quadratic pairing). Let `k ∈ {3, 4}`, `G` of class `≤ k + 1`, `x^E = P = ∏_l d_l^{e_l}` with
> `d_l ∈ γ_k`, `E = 2^e ≥ 4`, `s ∈ {0, 1}`, `2 + s ≤ k`. Suppose that for every `l` either `E ∣ 8e_l`, or
> `d_l^{2^{s+3}e_l} ∈ γ_{k+1+s}`. Then `2^{s+3} E X² ∈ Δ^{k+2+s}`.
>
> **Theorem 14.** Let `G` have class `≤ 4`, `t ∈ γ₂`, `d_l = [t, x_l]`, and `x₁⁸ = d₂⁻¹d₃⁻⁴`,
> `x₂⁶⁴ = d₁d₃¹⁶d₅⁻¹⁶`, `x₅¹⁰²⁴ = d₂⁻¹⁶`. Then `128 X₂² X₁ ∈ Δ⁶`. As an identity,
> `128X₂²X₁ ≡ X₂²(x₅¹⁰²⁴ − 1) − 64X₂²D₃ − Σ_{m≥2} C(128, m) X₂²X₁^m (mod Δ⁶)`.
>
> Where the second case comes from: if `t ∈ γ_{k−1}`, `d₁ = [t, x₁]` and `x₁^{E₁} ∈ γ_k`, then
> `1 = [t, x₁^{E₁}] = d₁^{E₁}[d₁, x₁]^{C(E₁, 2)}`, so `d₁^{E₁} ∈ γ_{k+1}` and `d₁^{2E₁} = 1`.
>
> **Lemma 15** (where `w` lives). Let `G` have class `c = k + 1`, `x_i^{E_i} = P_i ∈ γ_k`, `E_j ∣ A_ij`,
> and `g₁ ∈ (γ_k)^{E₁}γ_c`, `g₂ ∈ (γ_k)^{E₂}γ_c`. Then
> `w = [x₂, x₁^{A₁₂}] = ∏_l [x₂, d_l]^{−a_l A₁₂/E₁}` (`P₁ = ∏_l d_l^{−a_l}`). Since `[x₂, d_l]^{E₂} = 1`, a
> part with `E₂ ∣ a_l A₁₂/E₁` contributes nothing.
>
> **Proposition 16.** Let `k ∈ {3, 4}`, `G` of class `k + 1`, `P₁ = ∏_l d_l^{−a_l}`, `N = A₁₂/2 = 2^ν`.
> Suppose (i) Lemma 13 holds for `x₂` with `s = k − 3`; (ii) `(N/2) X₁² ∈ Δ^{2k−2}` (for `k = 3`:
> `N ≥ 2E₁²`; for `k = 4`: Lemma 13 for `x₁` with `s = 0` and `N ≥ 16E₁`); (iii) for every `l` either
> (pairing) `v₂(a_l N/E₁) ≥ e₂ + k − 3`, or (carrier) `d_l^{−a_l N/E₁} = x_κ^F` for a generator `x_κ`
> and `2^k E₂ ∣ F`. Then `N X₂² X₁ ∈ Δ^{2k}`.

Here (paper's indices `1, 2, 3` are `0, 1, 2` of `Fin 3` in Lemma 15) `D_k` replaces `γ_k` wherever only
`γ_k ⊆ D_k` is used; then no class hypothesis is needed for Lemma 13 and Proposition 16.

## What is proved

* **Lemma 13** (`lemma13`, from `lemma13_zero` for `s = 0` and `lemma13_one` for `s = 1`;
  `lemma13_gamma` with the paper's `γ`-hypotheses): for any group, `2 ≤ 2 + s ≤ k ≤ 4`, `s ≤ 1`,
  `x^{2^e} = ∏_l d_l^{e_l}` (a list, any order), `d_l ∈ D_k`, and for every `l` either `2^e ∣ 8e_l` or
  `d_l^{8e_l} ∈ D_{k+1}` and `d_l^{2^{s+3}e_l} ∈ D_{k+1+s}`: `2^{s+3}2^e X² ∈ Δ^{k+2+s}`. No class
  hypothesis; `E ≥ 4` is not needed.
* **Where the second case comes from** (`second_case`): if `[d, x]` is central (`d = [t, x] ∈ γ_k`, class
  `≤ k + 1`) and `t` commutes with `x^E`, then `d^E ∈ γ_{k+1}` and `d^{2E} = 1`; the identity behind it is
  `pc_pow_eq` (`[t, x^n] = d^n [d, x]^{C(n, 2)}`). `second_case_three`: for class `≤ 4` and `t ∈ γ₂`,
  `x^E ∈ γ₃` the commutation is automatic (`[γ₂, γ₃] = 1`, `comm_lcs_one`, from the three subgroup lemma).
* **Theorem 14** (`theorem14`), exactly as stated, for any `x₃` and any `t ∈ γ₂`; it is Proposition 16
  with `k = 3`, `(e₁, e₂, ν) = (3, 6, 7)` and Lemma 13 for `x₂` (`d₁⁸ ∈ γ₄` by `second_case_three`).
  The identity of the proof, `theorem14_identity`: in any group with `x₁⁸ = d₂⁻¹d₃⁻⁴`,
  `x₅¹⁰²⁴ = d₂⁻¹⁶`, `d_l ∈ γ₃` and `γ₃` abelian,
  `128X₂²X₁ − (X₂²(x₅¹⁰²⁴ − 1) − 64X₂²D₃ − Σ_{m=2}^{5} C(128, m) X₂²X₁^m) ∈ Δ⁸`.
* **§6.12(b), the paper part** (`theorem14_mod7`): in the setting of Theorem 14,
  `128X₂²X₁ + 64X₂²D₃ ∈ Δ⁷` — the binomials of `x₁` and the carried part lie in `Δ⁷` (Lemma 13 for `x₁`,
  `s = 0`, and for `x₂`, `s = 1`, with `d₁⁸ ∈ γ₄`, `d₁¹⁶ = 1`), so the uncarried `d₃`-part is the only
  possible obstruction at `Δ⁷`.
* **Lemma 15** (`lemma15`: `w = [x₂, x₁^{A₁₂}]`; `lemma15_prod`: `[x₂, x₁^{A₁₂}] =
  ∏_l [x₂, d_l]^{−a_l A₁₂/E₁}`; `lemma15_w`: both; `part_trivial`: `[x₂, d]^m = 1` when `E₂ ∣ m`),
  for `k ≥ 2`, class `≤ k + 1`. The paper's `(γ_k)^{E_i}γ_c` is read as `{y^{E_i} z : y ∈ γ_k, z ∈ γ_c}`.
* **Proposition 16** (`prop16`), for any group: `3 ≤ k ≤ 4`, `x₁^{2^{e₁}} = ∏_l d_l^{−a_l}`, `d_l ∈ D_k`,
  `x₂^{2^{e₂}} ∈ D_k`, (i) as the two conclusions `8E₂X₂² ∈ Δ^{k+2}` and `2^kE₂X₂² ∈ Δ^{2k−1}` of
  Lemma 13 for `x₂` (`s = 0` and `s = k − 3`), (ii) `2^{ν−1}X₁² ∈ Δ^{2k−2}` and, for `k = 4`,
  `e₁ + 3 ≤ ν`, (iii) for every `l` pairing (`2^{k−3}E₂ ∣ a_l 2^{ν−e₁}`) or carrier
  (`d_l^{−a_l 2^{ν−e₁}} = y^F` for some `y ∈ G`, `2^kE₂ ∣ F`): `2^ν X₂²X₁ ∈ Δ^{2k}`. The carrier need not
  be a generator. `prop16_ii_three`, `prop16_ii_four`: the paper's sufficient forms of (ii). The pieces:
  `carrier_mem` (a carried part), `pairing_part_mem` (a pairing part), `tail_mem` (the binomials of
  `x₁`), `pow_list_mem`.

## Corrections to the paper

* Lemma 13 for `s = 1`: the proof bounds the term `m = 2` by the case `s = 0`, so for every `l` of the
  second kind it needs `d_l^{8e_l} ∈ γ_{k+1}` as well as `d_l^{16e_l} ∈ γ_{k+2}` (the second does not
  imply the first). Both hold in c4a (`d₁⁸ ∈ γ₄`, `d₁¹⁶ = 1`).
* Proposition 16 (i) is used in its proof through both conclusions of Lemma 13 for `x₂`, `s = 0` and
  `s = k − 3`: for `k = 4` the second binomial term of a carried part needs `8E₂X₂² ∈ Δ⁶`, which
  `16E₂X₂² ∈ Δ⁷` does not give. With the corrected Lemma 13 both come together.
* Proposition 16 (ii): for `k = 4` the binomial term `m = 4` of `x₁^N` needs `N ≥ 8E₁` beyond
  `(N/2)X₁² ∈ Δ⁶`; the paper's concrete form (`N ≥ 16E₁`) has it.

## Not formalized

* The computer part of §6.12(b) (`64X₂²D₃ ∉ Δ⁷` in c4a), the tables, the presentations of (d),
  conjecture H and its refinement, and all computation (measured memberships, non-memberships, the
  explicit `n = 5` form of Lemma 13 over `ℤ`).
* That the carried part is "forced" (`w ≠ 1` needs a carried part): only its ingredients are stated —
  `lemma15_w` and `part_trivial`.
-/

namespace GroupDimension.Kernel.Carrier

noncomputable section

open MonoidAlgebra
open GroupDimension.Kernel.Decomposition (δ δ_mem δ_mem_pow_one δ_one δ_mul pow_mono pc
  pc_zpow_right pc_pow_left binom_trunc binomSum lvl lvl_sound two_mul_choose_two choose_two_succ
  w_three)
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Levels -/

theorem mm {a b : MonoidAlgebra ℤ G} {i j n : ℕ} (ha : a ∈ augIdeal G ^ i)
    (hb : b ∈ augIdeal G ^ j) (h : n ≤ i + j) : a * b ∈ augIdeal G ^ n :=
  pow_mono h (mul_mem_augIdeal_pow ha hb)

theorem δpow_mem (x : G) (n : ℕ) : δ x ^ n ∈ augIdeal G ^ n := Ideal.pow_mem_pow (δ_mem x) n

theorem δ_mem_of_D {k : ℕ} {d : G} (h : d ∈ D k G) : δ d ∈ augIdeal G ^ k := h

/-- The pairing lemma as used here: `x^{2^e} ∈ D_k`, `k ≤ 4` `⟹ 2^j 2^e (x − 1) ∈ Δ^{min(2+j, k)}`. -/
theorem pw {x : G} {e k : ℕ} (hk : k ≤ 4) (hx : x ^ 2 ^ e ∈ D k G) (j : ℕ) :
    ((2 : ℤ) ^ j * 2 ^ e) • δ x ∈ augIdeal G ^ min (2 + j) k := by
  have h := lvl_sound hk hx (e + j)
  have hl : lvl k e (e + j) = min (2 + j) k := by
    unfold lvl
    simp only [show ¬ e + j < e by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  rwa [hl, pow_add, mul_comm ((2 : ℤ) ^ e)] at h

theorem pw_le {x : G} {e k j m : ℕ} (hk : k ≤ 4) (hx : x ^ 2 ^ e ∈ D k G) (hj : m ≤ 2 + j)
    (hmk : m ≤ k) : ((2 : ℤ) ^ j * 2 ^ e) • δ x ∈ augIdeal G ^ m :=
  pow_mono (le_min hj hmk) (pw hk hx j)

theorem pw0 {x : G} {e k : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ 4) (hx : x ^ 2 ^ e ∈ D k G) :
    ((2 : ℤ) ^ e) • δ x ∈ augIdeal G ^ 2 := by
  have h := pw_le (j := 0) (m := 2) hk hx (by omega) hk2
  rwa [pow_zero, one_mul] at h

/-! ## Binomial coefficients -/

theorem mul_choose_eq (F m : ℕ) : (m + 1) * F.choose (m + 1) = F * (F - 1).choose m := by
  rcases F with _ | n
  · simp
  · rw [Nat.add_sub_cancel, Nat.add_one_mul_choose_eq n m, mul_comm]

theorem two_mul_choose_two_nat (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have h := mul_choose_eq n 1
  rwa [Nat.choose_one_right] at h

/-- `2^a ∣ F` and `m + 1` odd `⟹ 2^a ∣ C(F, m + 1)` (from `(m+1) C(F, m+1) = F C(F−1, m)`). -/
theorem two_pow_dvd_choose {a F m : ℕ} (hF : 2 ^ a ∣ F) (hm : Nat.Coprime 2 (m + 1)) :
    2 ^ a ∣ F.choose (m + 1) := by
  have h : 2 ^ a ∣ (m + 1) * F.choose (m + 1) := by
    rw [mul_choose_eq]; exact Dvd.dvd.mul_right hF _
  exact (Nat.Coprime.pow_left a hm).dvd_of_dvd_mul_left h

/-- `2^a ∣ F`, `a ≥ 2` `⟹ 2^{a−2} ∣ C(F, 4)`. -/
theorem choose_four_dvd {a F : ℕ} (hF : 2 ^ a ∣ F) (ha : 2 ≤ a) : 2 ^ (a - 2) ∣ F.choose 4 := by
  have h : 4 * F.choose 4 = F * (F - 1).choose 3 := mul_choose_eq F 3
  have e : 2 ^ a = 4 * 2 ^ (a - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_sub_of_le ha]
  have h2 : 4 * 2 ^ (a - 2) ∣ 4 * F.choose 4 := by
    rw [← e, h]; exact Dvd.dvd.mul_right hF _
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2

/-- The remainder of `x^E − 1 = Σ_{m=1}^{5} C(E, m) X^m + r`, `r ∈ Δ⁶`. -/
def rem5 (x : G) (E : ℕ) : MonoidAlgebra ℤ G :=
  δ (x ^ E) - ((E : ℤ) • δ x + (E.choose 2 : ℤ) • δ x ^ 2 + (E.choose 3 : ℤ) • δ x ^ 3 +
    (E.choose 4 : ℤ) • δ x ^ 4 + (E.choose 5 : ℤ) • δ x ^ 5)

theorem δ_pow_eq5 (x : G) (E : ℕ) :
    δ (x ^ E) = (E : ℤ) • δ x + (E.choose 2 : ℤ) • δ x ^ 2 + (E.choose 3 : ℤ) • δ x ^ 3 +
      (E.choose 4 : ℤ) • δ x ^ 4 + (E.choose 5 : ℤ) • δ x ^ 5 + rem5 x E := by
  rw [rem5]; abel

theorem rem5_mem (x : G) (E : ℕ) : rem5 x E ∈ augIdeal G ^ 6 := by
  have h := binom_trunc x (E : ℤ) 6
  rw [zpow_natCast] at h
  have hs : binomSum x (E : ℤ) 6 =
      1 + ((E : ℤ) • δ x + (E.choose 2 : ℤ) • δ x ^ 2 + (E.choose 3 : ℤ) • δ x ^ 3 +
        (E.choose 4 : ℤ) • δ x ^ 4 + (E.choose 5 : ℤ) • δ x ^ 5) := by
    simp only [binomSum, Finset.sum_range_succ, Finset.sum_range_zero, Ring.choose_natCast,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, pow_one, one_smul,
      zero_add, add_assoc]
  have e : rem5 x E = of ℤ G (x ^ E) - binomSum x (E : ℤ) 6 := by
    rw [hs, rem5]; simp only [δ]; abel
  rw [e]; exact h

/-! ## Products of elements of `D_k` -/

theorem prod_mem_D {k : ℕ} (l : List (G × ℤ)) (f : ℤ → ℤ) (hd : ∀ p ∈ l, p.1 ∈ D k G) :
    (l.map fun p => p.1 ^ f p.2).prod ∈ D k G := by
  refine list_prod_mem fun a ha => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact zpow_mem (hd p hp) _

/-- `c Y (∏ a − 1) Z ∈ Δ^T` from `c Y (a − 1) Z ∈ Δ^T` for each factor `a ∈ D_k`, `T ≤ 2k`. -/
theorem list_smul_mem {k T : ℕ} (hT : T ≤ 2 * k) (Y Z : MonoidAlgebra ℤ G) (c : ℤ) (l : List G)
    (hl : ∀ a ∈ l, a ∈ D k G) (h : ∀ a ∈ l, c • (Y * δ a * Z) ∈ augIdeal G ^ T) :
    c • (Y * δ l.prod * Z) ∈ augIdeal G ^ T := by
  induction l with
  | nil => rw [List.prod_nil, δ_one, mul_zero, zero_mul, smul_zero]; exact zero_mem _
  | cons a l ih =>
    have ha : δ a ∈ augIdeal G ^ k := hl a (by simp)
    have hl' : ∀ b ∈ l, b ∈ D k G := fun b hb => hl b (by simp [hb])
    have hp : δ l.prod ∈ augIdeal G ^ k := list_prod_mem hl'
    have e : c • (Y * δ (a * l.prod) * Z) = c • (Y * δ a * Z) + c • (Y * δ l.prod * Z) +
        c • (Y * (δ a * δ l.prod) * Z) := by
      rw [δ_mul]; simp only [mul_add, add_mul, smul_add]
    rw [List.prod_cons, e]
    refine add_mem (add_mem (h a (by simp)) (ih hl' fun b hb => h b (by simp [hb]))) ?_
    refine zsmul_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_)) _
    exact pow_mono hT (by rw [two_mul]; exact mul_mem_augIdeal_pow ha hp)

/-- `c (d^a − 1) ≡ d^{ca} − 1 (mod Δ^{2k})` for `d ∈ D_k`. -/
theorem zpow_smul_sub_mem {k : ℕ} {d : G} (hd : d ∈ D k G) (a c : ℤ) :
    c • δ (d ^ a) - δ (d ^ (c * a)) ∈ augIdeal G ^ (2 * k) := by
  have h1 := KFree.zpow_sub_one_sub_mem (n := 2 * k) (c := k) le_rfl hd a
  have h2 := KFree.zpow_sub_one_sub_mem (n := 2 * k) (c := k) le_rfl hd (c * a)
  have e : c • δ (d ^ a) - δ (d ^ (c * a)) =
      c • ((of ℤ G (d ^ a) - 1) - a • (of ℤ G d - 1)) -
        ((of ℤ G (d ^ (c * a)) - 1) - (c * a) • (of ℤ G d - 1)) := by
    simp only [δ, smul_sub, mul_smul]; abel
  rw [e]; exact sub_mem (zsmul_mem h1 _) h2

/-- A part read through pairing: `c Y (d^a − 1) Z ∈ Δ^T` if `ca = qF` and `F Y (d − 1) Z ∈ Δ^T`. -/
theorem partA {k T : ℕ} (hT : T ≤ 2 * k) {d : G} (hd : d ∈ D k G) (Y Z : MonoidAlgebra ℤ G)
    {a c q F : ℤ} (hq : c * a = q * F) (hF : F • (Y * δ d * Z) ∈ augIdeal G ^ T) :
    c • (Y * δ (d ^ a) * Z) ∈ augIdeal G ^ T := by
  have h1 := KFree.zpow_sub_one_sub_mem (n := 2 * k) (c := k) le_rfl hd a
  have e : c • (Y * δ (d ^ a) * Z) =
      c • (Y * ((of ℤ G (d ^ a) - 1) - a • (of ℤ G d - 1)) * Z) + q • (F • (Y * δ d * Z)) := by
    rw [smul_smul, ← hq]
    simp only [δ, mul_sub, sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc, mul_smul]
    abel
  rw [e]
  exact add_mem (zsmul_mem (pow_mono hT (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h1))) _)
    (zsmul_mem hF _)

/-- A part read through a relation: `c Y (d^a − 1) Z ∈ Δ^T` if `Y (d^{ca} − 1) Z ∈ Δ^T`. -/
theorem partB {k T : ℕ} (hT : T ≤ 2 * k) {d : G} (hd : d ∈ D k G) (Y Z : MonoidAlgebra ℤ G)
    (a c : ℤ) (h : Y * δ (d ^ (c * a)) * Z ∈ augIdeal G ^ T) :
    c • (Y * δ (d ^ a) * Z) ∈ augIdeal G ^ T := by
  have h1 := zpow_smul_sub_mem hd a c
  have e : c • (Y * δ (d ^ a) * Z) =
      Y * (c • δ (d ^ a) - δ (d ^ (c * a))) * Z + Y * δ (d ^ (c * a)) * Z := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]; abel
  rw [e]
  exact add_mem (pow_mono hT (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h1))) h

/-! ## Lemma 13: the quadratic pairing -/

/-- **Lemma 13**, `s = 0`: `x^{2^e} = ∏ d_l^{e_l}`, `d_l ∈ D_k`, `2 ≤ k ≤ 4`, and for every `l` either
`2^e ∣ 8e_l` or `d_l^{8e_l} ∈ D_{k+1}` `⟹ 8 · 2^e X² ∈ Δ^{k+2}`. -/
theorem lemma13_zero {x : G} {e k : ℕ} (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (l : List (G × ℤ))
    (hP : x ^ 2 ^ e = (l.map fun p => p.1 ^ p.2).prod) (hd : ∀ p ∈ l, p.1 ∈ D k G)
    (hcase : ∀ p ∈ l, (2 : ℤ) ^ e ∣ 8 * p.2 ∨ p.1 ^ (8 * p.2) ∈ D (k + 1) G) :
    ((8 : ℤ) * 2 ^ e) • (δ x * δ x) ∈ augIdeal G ^ (k + 2) := by
  have hx : x ^ 2 ^ e ∈ D k G := by rw [hP]; exact prod_mem_D l (fun a => a) hd
  have hX1 := δ_mem_pow_one x
  have hl : ∀ a ∈ l.map (fun p => p.1 ^ p.2), a ∈ D k G := fun a ha => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha; exact zpow_mem (hd p hp) _
  -- the relator part `8 X (P − 1)`
  have hmain : (8 : ℤ) • (δ x * δ (x ^ 2 ^ e)) ∈ augIdeal G ^ (k + 2) := by
    have h := list_smul_mem (T := k + 2) (by omega) (δ x) 1 (8 : ℤ) _ hl (fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      rcases hcase p hp with ⟨q, hq⟩ | h8
      · refine partA (k := k) (by omega) (hd p hp) (δ x) 1 (q := q) (F := (2 : ℤ) ^ e)
          (by rw [hq, mul_comm]) ?_
        rw [mul_one, ← smul_mul_assoc]
        exact mm (pw0 hk2 hk4 hx) (δ_mem_of_D (hd p hp)) (by omega)
      · exact partB (k := k) (by omega) (hd p hp) (δ x) 1 _ _
          (by rw [mul_one]; exact mm hX1 (δ_mem_of_D h8) (by omega)))
    rw [hP]; simpa only [mul_one] using h
  have hE : ((2 ^ e : ℕ) : ℤ) = (2 : ℤ) ^ e := by norm_num
  have hc2 : (2 : ℤ) * ((2 ^ e).choose 2 : ℕ) = 2 ^ e * (2 ^ e - 1) := by
    have := two_mul_choose_two (2 ^ e); rwa [hE] at this
  obtain ⟨q3, hq3⟩ : 2 ^ e ∣ (2 ^ e).choose 3 := two_pow_dvd_choose (m := 2) dvd_rfl (by decide)
  have h4 : (4 : ℤ) * ((2 ^ e).choose 4 : ℕ) = 2 ^ e * ((2 ^ e - 1).choose 3 : ℕ) := by
    exact_mod_cast mul_choose_eq (2 ^ e) 3
  have key : ((8 : ℤ) * 2 ^ e) • (δ x * δ x) = (8 : ℤ) • (δ x * δ (x ^ 2 ^ e)) -
      (((8 : ℤ) * ((2 ^ e).choose 2 : ℕ)) • (δ x * δ x ^ 2) +
        ((8 : ℤ) * ((2 ^ e).choose 3 : ℕ)) • (δ x * δ x ^ 3) +
        ((8 : ℤ) * ((2 ^ e).choose 4 : ℕ)) • (δ x * δ x ^ 4) +
        ((8 : ℤ) * ((2 ^ e).choose 5 : ℕ)) • (δ x * δ x ^ 5) +
        (8 : ℤ) • (δ x * rem5 x (2 ^ e))) := by
    rw [δ_pow_eq5 x (2 ^ e)]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul, hE]
    abel
  rw [key]
  refine sub_mem hmain (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · -- `m = 2`: `8 C(E, 2) = (E − 1) · 4E`
    have e2 : ((8 : ℤ) * ((2 ^ e).choose 2 : ℕ)) • (δ x * δ x ^ 2) =
        ((2 : ℤ) ^ e - 1) • ((((2 : ℤ) ^ 2 * 2 ^ e) • δ x) * δ x ^ 2) := by
      rw [smul_mul_assoc, smul_smul]; congr 1; linear_combination 4 * hc2
    rw [e2]
    exact zsmul_mem (mm (pw_le (j := 2) (m := k) hk4 hx (by omega) le_rfl) (δpow_mem x 2)
      (by omega)) _
  · -- `m = 3`: `E ∣ C(E, 3)`
    have e3 : ((8 : ℤ) * ((2 ^ e).choose 3 : ℕ)) • (δ x * δ x ^ 3) =
        (q3 : ℤ) • ((((2 : ℤ) ^ 3 * 2 ^ e) • δ x) * δ x ^ 3) := by
      rw [smul_mul_assoc, smul_smul, hq3]; congr 1; push_cast; ring
    rw [e3]
    exact zsmul_mem (mm (pw_le (j := 3) (m := k) hk4 hx (by omega) le_rfl) (δpow_mem x 3)
      (by omega)) _
  · -- `m = 4`: `4 C(E, 4) = E C(E − 1, 3)`
    have e4 : ((8 : ℤ) * ((2 ^ e).choose 4 : ℕ)) • (δ x * δ x ^ 4) =
        ((2 : ℤ) * ((2 ^ e - 1).choose 3 : ℕ)) • ((((2 : ℤ) ^ 0 * 2 ^ e) • δ x) * δ x ^ 4) := by
      rw [smul_mul_assoc, smul_smul]; congr 1; linear_combination 2 * h4
    rw [e4]
    exact zsmul_mem (mm (pw_le (j := 0) (m := 2) hk4 hx (by omega) (by omega)) (δpow_mem x 4)
      (by omega)) _
  · exact zsmul_mem (mm hX1 (δpow_mem x 5) (by omega)) _
  · exact zsmul_mem (mm hX1 (rem5_mem x _) (by omega)) _

/-- **Lemma 13**, `s = 1`: as `lemma13_zero` with `3 ≤ k`, and for every `l` either `2^e ∣ 8e_l` or
both `d_l^{8e_l} ∈ D_{k+1}` and `d_l^{16e_l} ∈ D_{k+2}` `⟹ 16 · 2^e X² ∈ Δ^{k+3}`. The first of the
two is needed: the term `m = 2` is bounded by the case `s = 0`. -/
theorem lemma13_one {x : G} {e k : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4) (l : List (G × ℤ))
    (hP : x ^ 2 ^ e = (l.map fun p => p.1 ^ p.2).prod) (hd : ∀ p ∈ l, p.1 ∈ D k G)
    (hcase : ∀ p ∈ l, (2 : ℤ) ^ e ∣ 8 * p.2 ∨
      (p.1 ^ (8 * p.2) ∈ D (k + 1) G ∧ p.1 ^ (16 * p.2) ∈ D (k + 2) G)) :
    ((16 : ℤ) * 2 ^ e) • (δ x * δ x) ∈ augIdeal G ^ (k + 3) := by
  have h0 := lemma13_zero (by omega) hk4 l hP hd fun p hp => (hcase p hp).imp id And.left
  have hx : x ^ 2 ^ e ∈ D k G := by rw [hP]; exact prod_mem_D l (fun a => a) hd
  have hX1 := δ_mem_pow_one x
  have hl : ∀ a ∈ l.map (fun p => p.1 ^ p.2), a ∈ D k G := fun a ha => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha; exact zpow_mem (hd p hp) _
  have hmain : (16 : ℤ) • (δ x * δ (x ^ 2 ^ e)) ∈ augIdeal G ^ (k + 3) := by
    have h := list_smul_mem (T := k + 3) (by omega) (δ x) 1 (16 : ℤ) _ hl (fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      rcases hcase p hp with ⟨q, hq⟩ | ⟨_, h16⟩
      · refine partA (k := k) (by omega) (hd p hp) (δ x) 1 (q := q)
          (F := (2 : ℤ) ^ 1 * 2 ^ e) (by linear_combination 2 * hq) ?_
        rw [mul_one, ← smul_mul_assoc]
        exact mm (pw_le (j := 1) (m := 3) hk4 hx (by omega) (by omega)) (δ_mem_of_D (hd p hp))
          (by omega)
      · exact partB (k := k) (by omega) (hd p hp) (δ x) 1 _ _
          (by rw [mul_one]; exact mm hX1 (δ_mem_of_D h16) (by omega)))
    rw [hP]; simpa only [mul_one] using h
  have hE : ((2 ^ e : ℕ) : ℤ) = (2 : ℤ) ^ e := by norm_num
  have hc2 : (2 : ℤ) * ((2 ^ e).choose 2 : ℕ) = 2 ^ e * (2 ^ e - 1) := by
    have := two_mul_choose_two (2 ^ e); rwa [hE] at this
  obtain ⟨q3, hq3⟩ : 2 ^ e ∣ (2 ^ e).choose 3 := two_pow_dvd_choose (m := 2) dvd_rfl (by decide)
  obtain ⟨q5, hq5⟩ : 2 ^ e ∣ (2 ^ e).choose 5 := two_pow_dvd_choose (m := 4) dvd_rfl (by decide)
  have h4 : (4 : ℤ) * ((2 ^ e).choose 4 : ℕ) = 2 ^ e * ((2 ^ e - 1).choose 3 : ℕ) := by
    exact_mod_cast mul_choose_eq (2 ^ e) 3
  have key : ((16 : ℤ) * 2 ^ e) • (δ x * δ x) = (16 : ℤ) • (δ x * δ (x ^ 2 ^ e)) -
      (((16 : ℤ) * ((2 ^ e).choose 2 : ℕ)) • (δ x * δ x ^ 2) +
        ((16 : ℤ) * ((2 ^ e).choose 3 : ℕ)) • (δ x * δ x ^ 3) +
        ((16 : ℤ) * ((2 ^ e).choose 4 : ℕ)) • (δ x * δ x ^ 4) +
        ((16 : ℤ) * ((2 ^ e).choose 5 : ℕ)) • (δ x * δ x ^ 5) +
        (16 : ℤ) • (δ x * rem5 x (2 ^ e))) := by
    rw [δ_pow_eq5 x (2 ^ e)]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul, hE]
    abel
  rw [key]
  refine sub_mem hmain (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_)
  · -- `m = 2`: `16 C(E, 2) X³ = (E − 1) X (8E X²)`, by the case `s = 0`
    have e2 : ((16 : ℤ) * ((2 ^ e).choose 2 : ℕ)) • (δ x * δ x ^ 2) =
        ((2 : ℤ) ^ e - 1) • (δ x * (((8 : ℤ) * 2 ^ e) • (δ x * δ x))) := by
      rw [pow_two, mul_smul_comm, smul_smul]; congr 1; linear_combination 8 * hc2
    rw [e2]
    exact zsmul_mem (mm hX1 h0 (by omega)) _
  · have e3 : ((16 : ℤ) * ((2 ^ e).choose 3 : ℕ)) • (δ x * δ x ^ 3) =
        ((2 : ℤ) * q3) • ((((2 : ℤ) ^ 3 * 2 ^ e) • δ x) * δ x ^ 3) := by
      rw [smul_mul_assoc, smul_smul, hq3]; congr 1; push_cast; ring
    rw [e3]
    exact zsmul_mem (mm (pw_le (j := 3) (m := k) hk4 hx (by omega) le_rfl) (δpow_mem x 3)
      (by omega)) _
  · have e4 : ((16 : ℤ) * ((2 ^ e).choose 4 : ℕ)) • (δ x * δ x ^ 4) =
        (((2 ^ e - 1).choose 3 : ℕ) : ℤ) • ((((2 : ℤ) ^ 2 * 2 ^ e) • δ x) * δ x ^ 4) := by
      rw [smul_mul_assoc, smul_smul]; congr 1; linear_combination 4 * h4
    rw [e4]
    exact zsmul_mem (mm (pw_le (j := 2) (m := k) hk4 hx (by omega) le_rfl) (δpow_mem x 4)
      (by omega)) _
  · have e5 : ((16 : ℤ) * ((2 ^ e).choose 5 : ℕ)) • (δ x * δ x ^ 5) =
        ((16 : ℤ) * q5) • ((((2 : ℤ) ^ 0 * 2 ^ e) • δ x) * δ x ^ 5) := by
      rw [smul_mul_assoc, smul_smul, hq5]; congr 1; push_cast; ring
    rw [e5]
    exact zsmul_mem (mm (pw_le (j := 0) (m := 2) hk4 hx (by omega) (by omega)) (δpow_mem x 5)
      (by omega)) _
  · exact zsmul_mem (mm hX1 (rem5_mem x _) (by omega)) _

/-- **Lemma 13** (§6.12(a)), corrected: for `s ≤ 1`, `2 + s ≤ k ≤ 4`, `x^{2^e} = ∏_l d_l^{e_l}` with
`d_l ∈ D_k`, and for every `l` either `2^e ∣ 8e_l`, or `d_l^{8e_l} ∈ D_{k+1}` and
`d_l^{2^{s+3}e_l} ∈ D_{k+1+s}`: `2^{s+3} 2^e X² ∈ Δ^{k+2+s}`. (For `s = 0` the two conditions of the
second case coincide; for `s = 1` the paper states only the second.) -/
theorem lemma13 {x : G} {e k s : ℕ} (hs : s ≤ 1) (hsk : s + 2 ≤ k) (hk4 : k ≤ 4)
    (l : List (G × ℤ)) (hP : x ^ 2 ^ e = (l.map fun p => p.1 ^ p.2).prod)
    (hd : ∀ p ∈ l, p.1 ∈ D k G)
    (hcase : ∀ p ∈ l, (2 : ℤ) ^ e ∣ 8 * p.2 ∨
      (p.1 ^ (8 * p.2) ∈ D (k + 1) G ∧ p.1 ^ (2 ^ (s + 3) * p.2) ∈ D (k + 1 + s) G)) :
    ((2 : ℤ) ^ (s + 3) * 2 ^ e) • (δ x * δ x) ∈ augIdeal G ^ (k + 2 + s) := by
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
  · have := lemma13_zero (by omega) hk4 l hP hd fun p hp => (hcase p hp).imp id And.left
    rw [show ((2 : ℤ) ^ (0 + 3) * 2 ^ e) = 8 * 2 ^ e by norm_num]
    exact pow_mono (by omega) this
  · have := lemma13_one (by omega) hk4 l hP hd fun p hp => (hcase p hp).imp id fun h =>
      ⟨h.1, by rw [show (16 : ℤ) * p.2 = 2 ^ (1 + 3) * p.2 by norm_num]
               exact D_antitone (by omega) h.2⟩
    rw [show ((2 : ℤ) ^ (1 + 3) * 2 ^ e) = 16 * 2 ^ e by norm_num]
    exact pow_mono (by omega) this

/-- **Lemma 13** with the paper's hypotheses: `d_l ∈ γ_k`, `d_l^{8e_l} ∈ γ_{k+1}`,
`d_l^{2^{s+3}e_l} ∈ γ_{k+1+s}` (`γ_n = lowerCentralSeries (n − 1)`). No class hypothesis is needed. -/
theorem lemma13_gamma {x : G} {e k s : ℕ} (hs : s ≤ 1) (hsk : s + 2 ≤ k) (hk4 : k ≤ 4)
    (l : List (G × ℤ)) (hP : x ^ 2 ^ e = (l.map fun p => p.1 ^ p.2).prod)
    (hd : ∀ p ∈ l, p.1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hcase : ∀ p ∈ l, (2 : ℤ) ^ e ∣ 8 * p.2 ∨
      (p.1 ^ (8 * p.2) ∈ (⊤ : Subgroup G).lowerCentralSeries k ∧
        p.1 ^ (2 ^ (s + 3) * p.2) ∈ (⊤ : Subgroup G).lowerCentralSeries (k + s))) :
    ((2 : ℤ) ^ (s + 3) * 2 ^ e) • (δ x * δ x) ∈ augIdeal G ^ (k + 2 + s) :=
  lemma13 hs hsk hk4 l hP (fun p hp => gamma_le_D G k (by omega) (hd p hp)) fun p hp =>
    (hcase p hp).imp id fun h => ⟨lowerCentralSeries_le_D G k h.1, by
      have := lowerCentralSeries_le_D G (k + s) h.2
      rwa [show k + s + 1 = k + 1 + s by omega] at this⟩

/-! ## Proposition 16 -/

/-- A carried part: `X₂² (y^F − 1) ∈ Δ^{2k}` when `2^k E₂ ∣ F`, given both conclusions of Lemma 13
for `x₂` (`s = 0` and `s = k − 3`). `y` is any element. -/
theorem carrier_mem {x2 : G} (y : G) {k e2 F : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4)
    (hx2 : x2 ^ 2 ^ e2 ∈ D k G)
    (hi0 : ((8 : ℤ) * 2 ^ e2) • (δ x2 * δ x2) ∈ augIdeal G ^ (k + 2))
    (hi : ((2 : ℤ) ^ k * 2 ^ e2) • (δ x2 * δ x2) ∈ augIdeal G ^ (2 * k - 1))
    (hF : 2 ^ k * 2 ^ e2 ∣ F) :
    δ x2 * δ x2 * δ (y ^ F) ∈ augIdeal G ^ (2 * k) := by
  have hW : δ x2 * δ x2 ∈ augIdeal G ^ 2 :=
    mm (δ_mem_pow_one x2) (δ_mem_pow_one x2) (by norm_num)
  have hW2 : ((2 : ℤ) ^ (k - 1) * 2 ^ e2) • (δ x2 * δ x2) ∈ augIdeal G ^ (2 * k - 2) := by
    rcases (show k = 3 ∨ k = 4 by omega) with rfl | rfl
    · rw [← smul_mul_assoc]
      exact mm (pw_le (m := 3) hk4 hx2 (by omega) (by omega)) (δ_mem_pow_one x2) (by omega)
    · have e : ((2 : ℤ) ^ (4 - 1) * 2 ^ e2) = 8 * 2 ^ e2 := by norm_num
      rw [e]; exact pow_mono (by omega) hi0
  have hke : 2 ^ (k + e2) ∣ F := by rw [pow_add]; exact hF
  obtain ⟨f, rfl⟩ := hF
  have hc2 : (2 : ℤ) * ((2 ^ k * 2 ^ e2 * f).choose 2 : ℕ) =
      (2 ^ k * 2 ^ e2 * f) * (2 ^ k * 2 ^ e2 * f - 1) := by
    have := two_mul_choose_two (2 ^ k * 2 ^ e2 * f); push_cast at this; exact this
  have hk2 : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨q3, hq3⟩ := two_pow_dvd_choose (m := 2) hke (by decide)
  obtain ⟨q4, hq4⟩ := choose_four_dvd hke (by omega)
  obtain ⟨q5, hq5⟩ := two_pow_dvd_choose (m := 4) hke (by decide)
  have key : δ x2 * δ x2 * δ (y ^ (2 ^ k * 2 ^ e2 * f)) =
      ((2 ^ k * 2 ^ e2 * f : ℕ) : ℤ) • (δ x2 * δ x2 * δ y) +
      ((2 ^ k * 2 ^ e2 * f).choose 2 : ℤ) • (δ x2 * δ x2 * δ y ^ 2) +
      ((2 ^ k * 2 ^ e2 * f).choose 3 : ℤ) • (δ x2 * δ x2 * δ y ^ 3) +
      ((2 ^ k * 2 ^ e2 * f).choose 4 : ℤ) • (δ x2 * δ x2 * δ y ^ 4) +
      ((2 ^ k * 2 ^ e2 * f).choose 5 : ℤ) • (δ x2 * δ x2 * δ y ^ 5) +
      δ x2 * δ x2 * rem5 y (2 ^ k * 2 ^ e2 * f) := by
    rw [δ_pow_eq5 y]; simp only [mul_add, mul_smul_comm]
  rw [key]
  refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_
  · -- `m = 1`: `F X₂² X_κ = f (2^k E₂ X₂²) X_κ`
    have e1 : ((2 ^ k * 2 ^ e2 * f : ℕ) : ℤ) • (δ x2 * δ x2 * δ y) =
        (f : ℤ) • ((((2 : ℤ) ^ k * 2 ^ e2) • (δ x2 * δ x2)) * δ y) := by
      rw [smul_mul_assoc, smul_smul]; congr 1; push_cast; ring
    rw [e1]
    exact zsmul_mem (mm hi (δ_mem_pow_one y) (by omega)) _
  · -- `m = 2`: `C(F, 2) = 2^{k−1}E₂ f (F − 1)`
    have hc2' : (((2 ^ k * 2 ^ e2 * f).choose 2 : ℕ) : ℤ) =
        2 ^ (k - 1) * 2 ^ e2 * (f * (2 ^ k * 2 ^ e2 * f - 1)) := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      rw [hc2, hk2]; ring
    have e2 : (((2 ^ k * 2 ^ e2 * f).choose 2 : ℕ) : ℤ) • (δ x2 * δ x2 * δ y ^ 2) =
        ((f : ℤ) * (2 ^ k * 2 ^ e2 * f - 1)) •
          ((((2 : ℤ) ^ (k - 1) * 2 ^ e2) • (δ x2 * δ x2)) * δ y ^ 2) := by
      rw [smul_mul_assoc, smul_smul, hc2']; congr 1; ring
    rw [e2]
    exact zsmul_mem (mm hW2 (δpow_mem y 2) (by omega)) _
  · have e3 : (((2 ^ k * 2 ^ e2 * f).choose 3 : ℕ) : ℤ) • (δ x2 * δ x2 * δ y ^ 3) =
        (q3 : ℤ) • ((((2 : ℤ) ^ k * 2 ^ e2) • (δ x2 * δ x2)) * δ y ^ 3) := by
      rw [smul_mul_assoc, smul_smul, hq3]; congr 1; push_cast; ring
    rw [e3]
    exact zsmul_mem (mm hi (δpow_mem y 3) (by omega)) _
  · have hp : (2 : ℤ) ^ (k + e2 - 2) = 2 ^ (k - 2) * 2 ^ e2 := by
      rw [← pow_add]; congr 1; omega
    have e4 : (((2 ^ k * 2 ^ e2 * f).choose 4 : ℕ) : ℤ) • (δ x2 * δ x2 * δ y ^ 4) =
        (q4 : ℤ) • ((((2 : ℤ) ^ (k - 2) * 2 ^ e2) • δ x2) * δ x2 * δ y ^ 4) := by
      rw [smul_mul_assoc, smul_mul_assoc, smul_smul, hq4]; congr 1; push_cast; rw [hp]; ring
    rw [e4]
    exact zsmul_mem (mm (mm (n := k + 1) (pw_le (m := k) hk4 hx2 (by omega) le_rfl)
      (δ_mem_pow_one x2) le_rfl) (δpow_mem y 4) (by omega)) _
  · have e5 : (((2 ^ k * 2 ^ e2 * f).choose 5 : ℕ) : ℤ) • (δ x2 * δ x2 * δ y ^ 5) =
        (q5 : ℤ) • ((((2 : ℤ) ^ k * 2 ^ e2) • (δ x2 * δ x2)) * δ y ^ 5) := by
      rw [smul_mul_assoc, smul_smul, hq5]; congr 1; push_cast; ring
    rw [e5]
    exact zsmul_mem (mm hi (δpow_mem y 5) (by omega)) _
  · exact mm hW (rem5_mem y _) (by omega)

/-- A part read through pairing: `X₂² (d^c − 1) ∈ Δ^{2k}` when `d ∈ D_k` and `2^{k−3}E₂ ∣ c`. -/
theorem pairing_part_mem {x2 d : G} {k e2 : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4)
    (hx2 : x2 ^ 2 ^ e2 ∈ D k G) (hd : d ∈ D k G) {c : ℤ}
    (hc : (2 : ℤ) ^ (k - 3) * 2 ^ e2 ∣ c) :
    δ x2 * δ x2 * δ (d ^ c) ∈ augIdeal G ^ (2 * k) := by
  obtain ⟨q, hq⟩ := hc
  have hF : ((2 : ℤ) ^ (k - 3) * 2 ^ e2) • (δ x2 * δ x2 * δ d * 1) ∈ augIdeal G ^ (2 * k) := by
    rw [mul_one, ← smul_mul_assoc, ← smul_mul_assoc]
    exact mm (mm (n := k) (pw_le (m := k - 1) hk4 hx2 (by omega) (by omega)) (δ_mem_pow_one x2)
      (by omega)) (δ_mem_of_D hd) (by omega)
  have h := partA (k := k) (T := 2 * k) le_rfl hd (δ x2 * δ x2) 1 (a := c) (c := 1) (q := q)
    (by rw [one_mul, hq, mul_comm]) hF
  simpa only [one_smul, mul_one] using h

/-- `Y (P^M − 1) ∈ Δ^T` for `P = ∏ a`, `a ∈ D_k`, from `M Y (a − 1) ∈ Δ^T` for each factor. -/
theorem pow_list_mem {k T : ℕ} (hT : T ≤ 2 * k) (Y : MonoidAlgebra ℤ G) (M : ℤ) (l : List G)
    (hl : ∀ a ∈ l, a ∈ D k G) (h : ∀ a ∈ l, M • (Y * δ a * 1) ∈ augIdeal G ^ T) :
    Y * δ (l.prod ^ M) ∈ augIdeal G ^ T := by
  have hP : l.prod ∈ D k G := list_prod_mem hl
  have h1 := KFree.zpow_sub_one_sub_mem (n := 2 * k) (c := k) le_rfl hP M
  have h2 := list_smul_mem hT Y 1 M l hl h
  have e : Y * δ (l.prod ^ M) =
      Y * ((of ℤ G (l.prod ^ M) - 1) - M • (of ℤ G l.prod - 1)) + M • (Y * δ l.prod * 1) := by
    simp only [δ, mul_sub, mul_one, mul_smul_comm]; abel
  rw [e]
  exact add_mem (pow_mono hT (Ideal.mul_mem_left _ _ h1)) h2

/-- The binomials of `x₁`: `Σ_{m=2}^{5} C(N, m) X₂²X₁^m + X₂² r ∈ Δ^{2k}` for `N = 2^ν`, under (ii). -/
theorem tail_mem {x1 : G} (x2 : G) {k e1 ν : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4) (hν : e1 ≤ ν)
    (hν1 : 1 ≤ ν) (hx1 : x1 ^ 2 ^ e1 ∈ D k G)
    (hii : ((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1) ∈ augIdeal G ^ (2 * k - 2))
    (htail : k = 4 → e1 + 3 ≤ ν) :
    ((2 ^ ν).choose 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
      ((2 ^ ν).choose 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
      ((2 ^ ν).choose 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
      ((2 ^ ν).choose 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5) +
      δ x2 * δ x2 * rem5 x1 (2 ^ ν) ∈ augIdeal G ^ (2 * k) := by
  have hW : δ x2 * δ x2 ∈ augIdeal G ^ 2 :=
    mm (δ_mem_pow_one x2) (δ_mem_pow_one x2) (by norm_num)
  have hN : (2 : ℤ) ^ ν = 2 * 2 ^ (ν - 1) := by rw [← pow_succ']; congr 1; omega
  refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) (mm hW (rem5_mem x1 _) (by omega))
  · -- `m = 2`: `C(N, 2) = (N − 1) N/2`
    have h2 := two_mul_choose_two (2 ^ ν); push_cast at h2
    have hc : (((2 ^ ν).choose 2 : ℕ) : ℤ) = (2 ^ ν - 1) * 2 ^ (ν - 1) := by
      apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
      linear_combination h2 + ((2 : ℤ) ^ ν - 1) * hN
    have e2 : (((2 ^ ν).choose 2 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) =
        ((2 : ℤ) ^ ν - 1) • (δ x2 * δ x2 * (((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1))) := by
      rw [pow_two (δ x1), mul_smul_comm, smul_smul, hc]
    rw [e2]
    exact zsmul_mem (mm hW hii (by omega)) _
  · -- `m = 3`: `N ∣ C(N, 3)`
    obtain ⟨q3, hq3⟩ := two_pow_dvd_choose (a := ν) (m := 2) dvd_rfl (by decide)
    have e3 : (((2 ^ ν).choose 3 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) =
        ((2 : ℤ) * q3) • (δ x2 * δ x2 * (((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1)) * δ x1) := by
      rw [pow_three' (δ x1), mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc (δ x2 * δ x2),
        hq3]
      congr 1; push_cast; linear_combination (q3 : ℤ) * hN
    rw [e3]
    exact zsmul_mem (mm (mm (n := 2 * k) hW hii (by omega)) (δ_mem_pow_one x1) (by omega)) _
  · -- `m = 4`: degree `6` for `k = 3`; for `k = 4`, `2^{ν−2} X₁ ∈ Δ³`
    rcases (show k = 3 ∨ k = 4 by omega) with rfl | rfl
    · exact zsmul_mem (mm hW (δpow_mem x1 4) (by omega)) _
    · have ht := htail rfl
      obtain ⟨q4, hq4⟩ := choose_four_dvd (a := ν) (F := 2 ^ ν) dvd_rfl (by omega)
      have hp : (2 : ℤ) ^ (ν - 2) = 2 ^ (ν - 2 - e1) * 2 ^ e1 := by
        rw [← pow_add]; congr 1; omega
      have e4 : (((2 ^ ν).choose 4 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) =
          (q4 : ℤ) • (δ x2 * δ x2 * ((((2 : ℤ) ^ (ν - 2 - e1) * 2 ^ e1) • δ x1) * δ x1 ^ 3)) := by
        rw [pow_succ' (δ x1) 3, smul_mul_assoc, mul_smul_comm, smul_smul, hq4]
        congr 1; push_cast; rw [hp]; ring
      rw [e4]
      exact zsmul_mem (mm hW (mm (n := 6) (pw_le (m := 3) hk4 hx1 (by omega) (by omega))
        (δpow_mem x1 3) (by omega)) (by omega)) _
  · -- `m = 5`: `E₁ ∣ C(N, 5)`
    obtain ⟨q5, hq5⟩ := two_pow_dvd_choose (a := e1) (F := 2 ^ ν) (m := 4)
      (pow_dvd_pow 2 hν) (by decide)
    have e5 : (((2 ^ ν).choose 5 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5) =
        (q5 : ℤ) • (δ x2 * δ x2 * ((((2 : ℤ) ^ 0 * 2 ^ e1) • δ x1) * δ x1 ^ 4)) := by
      rw [pow_succ' (δ x1) 4, smul_mul_assoc, mul_smul_comm, smul_smul, hq5]
      congr 1; push_cast; ring
    rw [e5]
    exact zsmul_mem (mm hW (mm (n := 6) (pw_le (m := 2) hk4 hx1 (by omega) (by omega))
      (δpow_mem x1 4) (by omega)) (by omega)) _

/-- **Proposition 16** (§6.12(c)), for any group (`D_k` in place of `γ_k`, no class hypothesis). Let
`3 ≤ k ≤ 4`, `x₁^{2^{e₁}} = ∏_l d_l^{−a_l}` with `d_l ∈ D_k`, `x₂^{2^{e₂}} ∈ D_k`, `N = 2^ν`,
`e₁ ≤ ν`, and
(i) `8E₂X₂² ∈ Δ^{k+2}` and `2^kE₂X₂² ∈ Δ^{2k−1}` (Lemma 13 for `x₂`, `s = 0` and `s = k − 3`);
(ii) `(N/2)X₁² ∈ Δ^{2k−2}`, and `N ≥ 8E₁` if `k = 4`;
(iii) for every `l` either `2^{k−3}E₂ ∣ a_l N/E₁` (pairing) or `d_l^{−a_l N/E₁} = y^F` with
`2^kE₂ ∣ F` (carrier).
Then `N X₂² X₁ ∈ Δ^{2k}`. -/
theorem prop16 {x1 x2 : G} {k e1 e2 ν : ℕ} (hk3 : 3 ≤ k) (hk4 : k ≤ 4)
    (l : List (G × ℤ)) (hd : ∀ p ∈ l, p.1 ∈ D k G)
    (hP1 : x1 ^ 2 ^ e1 = (l.map fun p => p.1 ^ (-p.2)).prod)
    (hx2 : x2 ^ 2 ^ e2 ∈ D k G)
    (hi0 : ((8 : ℤ) * 2 ^ e2) • (δ x2 * δ x2) ∈ augIdeal G ^ (k + 2))
    (hi : ((2 : ℤ) ^ k * 2 ^ e2) • (δ x2 * δ x2) ∈ augIdeal G ^ (2 * k - 1))
    (hν : e1 ≤ ν) (hν1 : 1 ≤ ν)
    (hii : ((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1) ∈ augIdeal G ^ (2 * k - 2))
    (htail : k = 4 → e1 + 3 ≤ ν)
    (hiii : ∀ p ∈ l, (2 : ℤ) ^ (k - 3) * 2 ^ e2 ∣ p.2 * 2 ^ (ν - e1) ∨
      ∃ y : G, ∃ F : ℕ, 2 ^ k * 2 ^ e2 ∣ F ∧ p.1 ^ (-p.2 * 2 ^ (ν - e1)) = y ^ F) :
    ((2 : ℤ) ^ ν) • (δ x2 * δ x2 * δ x1) ∈ augIdeal G ^ (2 * k) := by
  have hx1 : x1 ^ 2 ^ e1 ∈ D k G := by rw [hP1]; exact prod_mem_D l (fun a => -a) hd
  have hl : ∀ a ∈ l.map (fun p => p.1 ^ (-p.2)), a ∈ D k G := fun a ha => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha; exact zpow_mem (hd p hp) _
  have hxN : x1 ^ 2 ^ ν = (l.map fun p => p.1 ^ (-p.2)).prod ^ ((2 : ℤ) ^ (ν - e1)) := by
    rw [show (2 : ℤ) ^ (ν - e1) = ((2 ^ (ν - e1) : ℕ) : ℤ) by norm_num, zpow_natCast, ← hP1,
      ← pow_mul, ← pow_add, Nat.add_sub_of_le hν]
  -- `X₂² (x₁^N − 1) ∈ Δ^{2k}`, part by part
  have hmain : δ x2 * δ x2 * δ (x1 ^ 2 ^ ν) ∈ augIdeal G ^ (2 * k) := by
    rw [hxN]
    refine pow_list_mem le_rfl _ _ _ hl fun a ha => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine partB (k := k) le_rfl (hd p hp) (δ x2 * δ x2) 1 (-p.2) ((2 : ℤ) ^ (ν - e1)) ?_
    rw [mul_one]
    rcases hiii p hp with hpair | ⟨y, F, hF, hyF⟩
    · refine pairing_part_mem hk3 hk4 hx2 (hd p hp) ?_
      rw [show (2 : ℤ) ^ (ν - e1) * -p.2 = -(p.2 * 2 ^ (ν - e1)) by ring]
      exact (dvd_neg).mpr hpair
    · rw [show (2 : ℤ) ^ (ν - e1) * -p.2 = -p.2 * 2 ^ (ν - e1) by ring, hyF]
      exact carrier_mem y hk3 hk4 hx2 hi0 hi hF
  have htl := tail_mem x2 hk3 hk4 hν hν1 hx1 hii htail
  have key : ((2 ^ ν : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1) = δ x2 * δ x2 * δ (x1 ^ 2 ^ ν) -
      (((2 ^ ν).choose 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
        ((2 ^ ν).choose 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
        ((2 ^ ν).choose 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
        ((2 ^ ν).choose 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5) +
        δ x2 * δ x2 * rem5 x1 (2 ^ ν)) := by
    rw [δ_pow_eq5 x1 (2 ^ ν)]; simp only [mul_add, mul_smul_comm]; abel
  have hcast : ((2 ^ ν : ℕ) : ℤ) = (2 : ℤ) ^ ν := by norm_num
  rw [← hcast, key]
  exact sub_mem hmain htl

/-- The paper's sufficient form of (ii) for `k = 3`: `N ≥ 2E₁²`. -/
theorem prop16_ii_three {x1 : G} {e1 ν : ℕ} (hx1 : x1 ^ 2 ^ e1 ∈ D 3 G) (h : 2 * e1 + 1 ≤ ν) :
    ((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1) ∈ augIdeal G ^ (2 * 3 - 2) := by
  have hp : (2 : ℤ) ^ (ν - 1) = 2 ^ (ν - 1 - 2 * e1) * 2 ^ e1 * 2 ^ e1 := by
    rw [mul_assoc, ← pow_add, ← pow_add]; congr 1; omega
  have e : ((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1) =
      ((2 : ℤ) ^ (ν - 1 - 2 * e1)) • ((((2 : ℤ) ^ e1) • δ x1) * (((2 : ℤ) ^ e1) • δ x1)) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, hp, mul_assoc]
  rw [e]
  exact zsmul_mem (mm (pw0 (by norm_num) (by norm_num) hx1)
    (pw0 (by norm_num) (by norm_num) hx1) (by norm_num)) _

/-- The paper's sufficient form of (ii) for `k = 4`: Lemma 13 for `x₁` (`s = 0`) and `N ≥ 16E₁`
(which also gives `N ≥ 8E₁`). -/
theorem prop16_ii_four {x1 : G} {e1 ν : ℕ}
    (h8 : ((8 : ℤ) * 2 ^ e1) • (δ x1 * δ x1) ∈ augIdeal G ^ (4 + 2)) (h : e1 + 4 ≤ ν) :
    ((2 : ℤ) ^ (ν - 1)) • (δ x1 * δ x1) ∈ augIdeal G ^ (2 * 4 - 2) := by
  have hp : (2 : ℤ) ^ (ν - 1) = 2 ^ (ν - 4 - e1) * (8 * 2 ^ e1) := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]; congr 1; omega
  rw [hp, mul_smul]
  exact zsmul_mem (pow_mono (by norm_num) h8) _

/-! ## Group theory: commutators in the lower central series -/

theorem pc_eq_commutator (a b : G) : pc a b = ⁅a⁻¹, b⁻¹⁆ := by
  rw [pc, commutatorElement_def, inv_inv, inv_inv]

theorem pc_mem_lcs_left {n : ℕ} {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries n)
    (b : G) : pc a b ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
  rw [pc_eq_commutator]
  exact Subgroup.commutator_mem_commutator (inv_mem ha) (Subgroup.mem_top b⁻¹)

theorem pc_mem_lcs_right {n : ℕ} (a : G) {b : G} (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries n) :
    pc a b ∈ (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
  have e : pc a b = (pc b a)⁻¹ := by simp only [pc]; group
  rw [e]; exact inv_mem (pc_mem_lcs_left hb a)

/-- `[γ_{i+1}, γ₂] = 1` if `γ_{i+3} = 1` (the three subgroup lemma). -/
theorem comm_lcs_one {i : ℕ} (h : (⊤ : Subgroup G).lowerCentralSeries (i + 2) = ⊥) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries 1⁆ = ⊥ := by
  have h1 : (⊤ : Subgroup G).lowerCentralSeries 1 = ⁅(⊤ : Subgroup G), ⊤⁆ := rfl
  have h2 : (⊤ : Subgroup G).lowerCentralSeries (i + 2) =
      ⁅⁅(⊤ : Subgroup G).lowerCentralSeries i, ⊤⁆, ⊤⁆ := rfl
  rw [h2] at h
  rw [h1, Subgroup.commutator_comm ((⊤ : Subgroup G).lowerCentralSeries i)]
  apply Subgroup.commutator_commutator_eq_bot_of_rotate
  · rw [Subgroup.commutator_comm (⊤ : Subgroup G) ((⊤ : Subgroup G).lowerCentralSeries i)]
    exact h
  · exact h

theorem commute_of_lcs {i : ℕ} (h : (⊤ : Subgroup G).lowerCentralSeries (i + 2) = ⊥) {p q : G}
    (hp : p ∈ (⊤ : Subgroup G).lowerCentralSeries i)
    (hq : q ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : Commute p q := by
  have hpq : ⁅p, q⁆ ∈ ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries 1⁆ :=
    Subgroup.commutator_mem_commutator hp hq
  rwa [comm_lcs_one h, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hpq

theorem commute_of_central {j : ℕ} (h : (⊤ : Subgroup G).lowerCentralSeries (j + 1) = ⊥) {z : G}
    (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries j) (y : G) : Commute z y :=
  ((Subgroup.mem_center_iff.mp (KFree.lcs_le_center (M := G) h hz)) y).symm

theorem pc_mul_right {a y z : G} (h : ∀ g : G, Commute (pc a y) g) :
    pc a (y * z) = pc a y * pc a z := by
  have h1 : y⁻¹ * a * y = a * pc a y := by simp only [pc]; group
  calc pc a (y * z) = a⁻¹ * z⁻¹ * (y⁻¹ * a * y) * z := by simp only [pc]; group
    _ = a⁻¹ * z⁻¹ * a * (pc a y * z) := by rw [h1]; group
    _ = a⁻¹ * z⁻¹ * a * (z * pc a y) := by rw [(h z).eq]
    _ = pc a z * pc a y := by simp only [pc]; group
    _ = pc a y * pc a z := ((h (pc a z)).eq).symm

theorem pc_eq_one_of_commute {a b : G} (h : Commute a b) : pc a b = 1 := by
  simp only [pc]; rw [mul_assoc (a⁻¹ * b⁻¹), h.eq]; group

theorem conj_eq_mul_pc (x a : G) : x⁻¹ * a * x = a * pc a x := by simp only [pc]; group

/-- `x^{−n} t x^n = t d^n e^{C(n, 2)}` when `x⁻¹tx = td`, `x⁻¹dx = de` and `e` is central. -/
theorem conj_pow_eq {t x d e : G} (hd : x⁻¹ * t * x = t * d) (hde : x⁻¹ * d * x = d * e)
    (he : ∀ y : G, Commute e y) (n : ℕ) :
    (x ^ n)⁻¹ * t * x ^ n = t * (d ^ n * e ^ n.choose 2) := by
  have hconj : ∀ g : G, x⁻¹ * g * x = MulAut.conj x⁻¹ g := fun g => by
    rw [MulAut.conj_apply, inv_inv]
  have hex : x⁻¹ * e * x = e := by rw [mul_assoc, (he x).eq, inv_mul_cancel_left]
  induction n with
  | zero => simp
  | succ n ih =>
    calc (x ^ (n + 1))⁻¹ * t * x ^ (n + 1) = x⁻¹ * ((x ^ n)⁻¹ * t * x ^ n) * x := by
          rw [pow_succ, mul_inv_rev]; simp only [mul_assoc]
      _ = x⁻¹ * (t * (d ^ n * e ^ n.choose 2)) * x := by rw [ih]
      _ = (x⁻¹ * t * x) * ((x⁻¹ * d * x) ^ n * (x⁻¹ * e * x) ^ n.choose 2) := by
          simp only [hconj, map_mul, map_pow]
      _ = (t * d) * ((d * e) ^ n * e ^ n.choose 2) := by rw [hd, hde, hex]
      _ = t * (d ^ (n + 1) * e ^ (n + 1).choose 2) := by
          rw [(he d).symm.mul_pow, choose_two_succ, add_comm (n.choose 2) n,
            pow_add e n (n.choose 2), pow_succ' d n]
          simp only [mul_assoc]

/-- `[t, x^n] = d^n [d, x]^{C(n, 2)}` for `d = [t, x]` when `[d, x]` is central. -/
theorem pc_pow_eq {t x : G} (he : ∀ y : G, Commute (pc (pc t x) x) y) (n : ℕ) :
    pc t (x ^ n) = pc t x ^ n * pc (pc t x) x ^ n.choose 2 := by
  have h : pc t (x ^ n) = t⁻¹ * ((x ^ n)⁻¹ * t * x ^ n) := by simp only [pc, mul_assoc]
  rw [h, conj_pow_eq (conj_eq_mul_pc x t) (conj_eq_mul_pc x (pc t x)) he n, inv_mul_cancel_left]

/-- **Where the second case of Lemma 13 comes from** (§6.12(a)): in a group of class `≤ k + 1`, if
`d = [t, x] ∈ γ_k` and `t` commutes with `x^E`, then `d^E ∈ γ_{k+1}` and `d^{2E} = 1`. -/
theorem second_case {k : ℕ} {t x : G} {E : ℕ} (hk : 1 ≤ k)
    (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥)
    (hd : pc t x ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1)) (htx : Commute t (x ^ E)) :
    pc t x ^ E ∈ (⊤ : Subgroup G).lowerCentralSeries k ∧ pc t x ^ (2 * E) = 1 := by
  have he_mem : pc (pc t x) x ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
    have := pc_mem_lcs_left hd x; rwa [Nat.sub_add_cancel hk] at this
  have he : ∀ y, Commute (pc (pc t x) x) y := commute_of_central hclass he_mem
  have h1 := pc_pow_eq he E
  rw [pc_eq_one_of_commute htx] at h1
  have hdE : pc t x ^ E = (pc (pc t x) x ^ E.choose 2)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
  have hdE_mem : pc t x ^ E ∈ (⊤ : Subgroup G).lowerCentralSeries k := by
    rw [hdE]; exact inv_mem (pow_mem he_mem _)
  refine ⟨hdE_mem, ?_⟩
  have heE : pc (pc t x) x ^ E = 1 := by
    rw [← pc_pow_left he E]
    exact pc_eq_one_of_commute (commute_of_central hclass hdE_mem x)
  have h2 : E.choose 2 * 2 = E * (E - 1) := by rw [mul_comm]; exact two_mul_choose_two_nat E
  calc pc t x ^ (2 * E) = (pc t x ^ E) ^ 2 := by rw [← pow_mul, mul_comm]
    _ = ((pc (pc t x) x ^ E.choose 2)⁻¹) ^ 2 := by rw [hdE]
    _ = ((pc (pc t x) x ^ E) ^ (E - 1))⁻¹ := by rw [inv_pow, ← pow_mul, ← pow_mul, h2]
    _ = 1 := by rw [heE, one_pow, inv_one]

/-- `second_case` for class `≤ 4`, `t ∈ γ₂`, `x^E ∈ γ₃`: then `[t, x^E] = 1` holds automatically
(`[γ₂, γ₃] = 1`), so `d^E ∈ γ₄` and `d^{2E} = 1`. -/
theorem second_case_three {t x : G} {E : ℕ}
    (hclass : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (ht : t ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hx : x ^ E ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    pc t x ^ E ∈ (⊤ : Subgroup G).lowerCentralSeries 3 ∧ pc t x ^ (2 * E) = 1 :=
  second_case (k := 3) (by norm_num) hclass (pc_mem_lcs_left ht x)
    (commute_of_lcs (i := 2) hclass hx ht).symm

/-! ## Theorem 14 -/

/-- **Theorem 14** (§6.12(a)). Let `G` have class `≤ 4`, `t ∈ γ₂`, `d_l = [t, x_l]`, and
`x₁⁸ = d₂⁻¹d₃⁻⁴`, `x₂⁶⁴ = d₁d₃¹⁶d₅⁻¹⁶`, `x₅¹⁰²⁴ = d₂⁻¹⁶`. Then `128 X₂² X₁ ∈ Δ⁶`. -/
theorem theorem14 {t x1 x2 x3 x5 : G}
    (hclass : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (ht : t ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h1 : x1 ^ 8 = (pc t x2)⁻¹ * pc t x3 ^ (-4 : ℤ))
    (h2 : x2 ^ 64 = pc t x1 * pc t x3 ^ (16 : ℤ) * pc t x5 ^ (-16 : ℤ))
    (h5 : x5 ^ 1024 = pc t x2 ^ (-16 : ℤ)) :
    (128 : ℤ) • (δ x2 * δ x2 * δ x1) ∈ augIdeal G ^ 6 := by
  have hd : ∀ y, pc t y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := fun y => pc_mem_lcs_left ht y
  have hD : ∀ y, pc t y ∈ D 3 G := fun y => lowerCentralSeries_le_D G 2 (hd y)
  have hx1γ : x1 ^ 8 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    rw [h1]; exact mul_mem (inv_mem (hd x2)) (zpow_mem (hd x3) _)
  obtain ⟨hd1, -⟩ := second_case_three hclass ht hx1γ
  -- Lemma 13 for `x₂`, `s = 0`: `512 X₂² ∈ Δ⁵`
  have hL2 : ((8 : ℤ) * 2 ^ 6) • (δ x2 * δ x2) ∈ augIdeal G ^ (3 + 2) := by
    refine lemma13_zero (k := 3) (by norm_num) (by norm_num)
      [(pc t x1, 1), (pc t x3, 16), (pc t x5, -16)] ?_ ?_ ?_
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, zpow_one]
      rw [show (2 : ℕ) ^ 6 = 64 by norm_num, h2, mul_assoc]
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact hD _
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · right
        have e : pc t x1 ^ ((8 : ℤ) * (pc t x1, (1 : ℤ)).2) = pc t x1 ^ 8 := by norm_num
        rw [e]; exact lowerCentralSeries_le_D G 3 hd1
      · left; norm_num
      · left; norm_num
  have hx1D : x1 ^ 2 ^ 3 ∈ D 3 G := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, h1]
    exact mul_mem (inv_mem (hD _)) (zpow_mem (hD _) _)
  have hii := prop16_ii_three (ν := 7) hx1D (by norm_num)
  -- Proposition 16 with `k = 3`, `(e₁, e₂, ν) = (3, 6, 7)`
  have h := prop16 (x1 := x1) (x2 := x2) (k := 3) (e1 := 3) (e2 := 6) (ν := 7)
    (by norm_num) (by norm_num) [(pc t x2, 1), (pc t x3, 4)]
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact hD _)
    (by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num, h1, zpow_neg_one])
    (by rw [show (2 : ℕ) ^ 6 = 64 by norm_num, h2]
        exact mul_mem (mul_mem (hD _) (zpow_mem (hD _) _)) (zpow_mem (hD _) _))
    hL2 (by rw [show ((2 : ℤ) ^ 3 * 2 ^ 6) = 8 * 2 ^ 6 by norm_num]; exact hL2)
    (by norm_num) (by norm_num)
    hii
    (by norm_num)
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · right; refine ⟨x5, 1024, by norm_num, ?_⟩
          rw [h5]; norm_num
        · left; norm_num)
  rw [show (128 : ℤ) = 2 ^ 7 by norm_num]; exact h

/-- The identity of the proof of Theorem 14: with `x₁⁸ = d₂⁻¹d₃⁻⁴`, `x₅¹⁰²⁴ = d₂⁻¹⁶`, `d_l ∈ γ₃` and
`γ₃` abelian (here: class `≤ 4`, `t ∈ γ₂`),
`128X₂²X₁ − (X₂²(x₅¹⁰²⁴ − 1) − 64X₂²D₃ − Σ_{m=2}^{5} C(128, m) X₂²X₁^m) ∈ Δ⁸`. -/
theorem theorem14_identity {t x1 x2 x3 x5 : G}
    (hclass : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (ht : t ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h1 : x1 ^ 8 = (pc t x2)⁻¹ * pc t x3 ^ (-4 : ℤ))
    (h5 : x5 ^ 1024 = pc t x2 ^ (-16 : ℤ)) :
    (128 : ℤ) • (δ x2 * δ x2 * δ x1) -
      (δ x2 * δ x2 * δ (x5 ^ 1024) - (64 : ℤ) • (δ x2 * δ x2 * δ (pc t x3)) -
        ((Nat.choose 128 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
          (Nat.choose 128 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
          (Nat.choose 128 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
          (Nat.choose 128 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5))) ∈ augIdeal G ^ 8 := by
  have hd : ∀ y, pc t y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := fun y => pc_mem_lcs_left ht y
  have hD : ∀ y, pc t y ∈ D 3 G := fun y => lowerCentralSeries_le_D G 2 (hd y)
  -- `x₁¹²⁸ = x₅¹⁰²⁴ d₃⁻⁶⁴` (`γ₃` is abelian)
  have hc : Commute (pc t x2)⁻¹ (pc t x3 ^ (-4 : ℤ)) :=
    commute_of_lcs (i := 2) hclass (inv_mem (hd x2))
      (Subgroup.lowerCentralSeries_antitone (S := (⊤ : Subgroup G)) (by norm_num)
        (zpow_mem (hd x3) _))
  have hx1 : x1 ^ 128 = x5 ^ 1024 * pc t x3 ^ (-64 : ℤ) := by
    calc x1 ^ 128 = (x1 ^ 8) ^ 16 := by rw [show (128 : ℕ) = 8 * 16 by norm_num, pow_mul]
      _ = ((pc t x2)⁻¹ * pc t x3 ^ (-4 : ℤ)) ^ 16 := by rw [h1]
      _ = ((pc t x2)⁻¹) ^ 16 * (pc t x3 ^ (-4 : ℤ)) ^ 16 := hc.mul_pow 16
      _ = x5 ^ 1024 * pc t x3 ^ (-64 : ℤ) := by
          rw [h5]; congr 1
          · rw [inv_pow, zpow_neg, zpow_ofNat]
          · rw [← zpow_natCast, ← zpow_mul]; norm_num
  have hx5 : x5 ^ 1024 ∈ D 3 G := by rw [h5]; exact zpow_mem (hD _) _
  have hd3 : pc t x3 ^ (-64 : ℤ) ∈ D 3 G := zpow_mem (hD _) _
  have hW : δ x2 * δ x2 ∈ augIdeal G ^ 2 :=
    mm (δ_mem_pow_one x2) (δ_mem_pow_one x2) (by norm_num)
  have hZ : δ (pc t x3 ^ (-64 : ℤ)) - (-64 : ℤ) • δ (pc t x3) ∈ augIdeal G ^ 6 :=
    KFree.zpow_sub_one_sub_mem (n := 6) (c := 3) (by norm_num) (hD x3) (-64)
  have hexp := δ_pow_eq5 x1 128
  have hmul : δ (x1 ^ 128) = δ (x5 ^ 1024) + δ (pc t x3 ^ (-64 : ℤ)) +
      δ (x5 ^ 1024) * δ (pc t x3 ^ (-64 : ℤ)) := by rw [hx1, δ_mul]
  have e : (128 : ℤ) • (δ x2 * δ x2 * δ x1) -
      (δ x2 * δ x2 * δ (x5 ^ 1024) - (64 : ℤ) • (δ x2 * δ x2 * δ (pc t x3)) -
        ((Nat.choose 128 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
          (Nat.choose 128 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
          (Nat.choose 128 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
          (Nat.choose 128 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5))) =
      δ x2 * δ x2 * (δ (pc t x3 ^ (-64 : ℤ)) - (-64 : ℤ) • δ (pc t x3)) +
        δ x2 * δ x2 * (δ (x5 ^ 1024) * δ (pc t x3 ^ (-64 : ℤ))) -
        δ x2 * δ x2 * rem5 x1 128 := by
    have h128 : (128 : ℤ) • (δ x2 * δ x2 * δ x1) =
        δ x2 * δ x2 * (((128 : ℕ) : ℤ) • δ x1) := by rw [mul_smul_comm]; norm_num
    have hX : ((128 : ℕ) : ℤ) • δ x1 = δ (x1 ^ 128) -
        ((Nat.choose 128 2 : ℤ) • δ x1 ^ 2 + (Nat.choose 128 3 : ℤ) • δ x1 ^ 3 +
          (Nat.choose 128 4 : ℤ) • δ x1 ^ 4 + (Nat.choose 128 5 : ℤ) • δ x1 ^ 5 + rem5 x1 128) := by
      rw [hexp]; abel
    rw [h128, hX, hmul]
    simp only [mul_add, mul_sub, mul_smul_comm]
    abel
  rw [e]
  refine sub_mem (add_mem (mm hW hZ (by norm_num)) ?_) (mm hW (rem5_mem x1 _) (by norm_num))
  exact mm hW (mm (n := 6) (δ_mem_of_D hx5) (δ_mem_of_D hd3) (by norm_num)) (by norm_num)

/-- **§6.12(b), on paper: one level only.** In the setting of Theorem 14, steps (1) and (4) of its
proof go one level further — the binomials of `x₁` (by Lemma 13 for `x₁`, `s = 0`) and the carried
part `X₂²(x₅¹⁰²⁴ − 1)` (by Lemma 13 for `x₂`, `s = 1`, using `d₁⁸ ∈ γ₄`, `d₁¹⁶ = 1`) lie in `Δ⁷` — so
`128X₂²X₁ ≡ −64X₂²D₃ (mod Δ⁷)`: the uncarried `d₃`-part is the only possible obstruction at `Δ⁷`.
(That it is one, `64X₂²D₃ ∉ Δ⁷` in c4a, is the computation.) -/
theorem theorem14_mod7 {t x1 x2 x3 x5 : G}
    (hclass : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥)
    (ht : t ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (h1 : x1 ^ 8 = (pc t x2)⁻¹ * pc t x3 ^ (-4 : ℤ))
    (h2 : x2 ^ 64 = pc t x1 * pc t x3 ^ (16 : ℤ) * pc t x5 ^ (-16 : ℤ))
    (h5 : x5 ^ 1024 = pc t x2 ^ (-16 : ℤ)) :
    (128 : ℤ) • (δ x2 * δ x2 * δ x1) + (64 : ℤ) • (δ x2 * δ x2 * δ (pc t x3)) ∈
      augIdeal G ^ 7 := by
  have hd : ∀ y, pc t y ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := fun y => pc_mem_lcs_left ht y
  have hD : ∀ y, pc t y ∈ D 3 G := fun y => lowerCentralSeries_le_D G 2 (hd y)
  have hx1γ : x1 ^ 8 ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    rw [h1]; exact mul_mem (inv_mem (hd x2)) (zpow_mem (hd x3) _)
  obtain ⟨hd1, hd16⟩ := second_case_three hclass ht hx1γ
  have hW : δ x2 * δ x2 ∈ augIdeal G ^ 2 :=
    mm (δ_mem_pow_one x2) (δ_mem_pow_one x2) (by norm_num)
  have hx2D : x2 ^ 2 ^ 6 ∈ D 3 G := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, h2]
    exact mul_mem (mul_mem (hD _) (zpow_mem (hD _) _)) (zpow_mem (hD _) _)
  have hx1D : x1 ^ 2 ^ 3 ∈ D 3 G := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, h1]
    exact mul_mem (inv_mem (hD _)) (zpow_mem (hD _) _)
  have hP2 : x2 ^ 2 ^ 6 = ([(pc t x1, (1 : ℤ)), (pc t x3, 16), (pc t x5, -16)].map
      fun p => p.1 ^ p.2).prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, zpow_one]
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, h2, mul_assoc]
  have hd2 : ∀ p ∈ [(pc t x1, (1 : ℤ)), (pc t x3, 16), (pc t x5, -16)], p.1 ∈ D 3 G := by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact hD _
  -- Lemma 13 for `x₂`: `512 X₂² ∈ Δ⁵`, `1024 X₂² ∈ Δ⁶`
  have hL1 : ((16 : ℤ) * 2 ^ 6) • (δ x2 * δ x2) ∈ augIdeal G ^ (3 + 3) := by
    refine lemma13_one (k := 3) (by norm_num) (by norm_num) _ hP2 hd2 ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · right
      refine ⟨?_, ?_⟩
      · have e : pc t x1 ^ ((8 : ℤ) * (pc t x1, (1 : ℤ)).2) = pc t x1 ^ 8 := by norm_num
        rw [e]; exact lowerCentralSeries_le_D G 3 hd1
      · have e : pc t x1 ^ ((16 : ℤ) * (pc t x1, (1 : ℤ)).2) = pc t x1 ^ (2 * 8) := by norm_num
        rw [e, hd16]; exact one_mem _
    · left; norm_num
    · left; norm_num
  have hL0 : ((8 : ℤ) * 2 ^ 6) • (δ x2 * δ x2) ∈ augIdeal G ^ (3 + 2) :=
    lemma13_zero (k := 3) (by norm_num) (by norm_num) _ hP2 hd2 fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · right
        have e : pc t x1 ^ ((8 : ℤ) * (pc t x1, (1 : ℤ)).2) = pc t x1 ^ 8 := by norm_num
        rw [e]; exact lowerCentralSeries_le_D G 3 hd1
      · left; norm_num
      · left; norm_num
  -- Lemma 13 for `x₁`, `s = 0`: `64 X₁² ∈ Δ⁵`
  have hX1 : ((8 : ℤ) * 2 ^ 3) • (δ x1 * δ x1) ∈ augIdeal G ^ (3 + 2) := by
    refine lemma13_zero (k := 3) (by norm_num) (by norm_num)
      [(pc t x2, (-1 : ℤ)), (pc t x3, -4)] ?_ ?_ ?_
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, h1, zpow_neg_one]
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hD _
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> (left; norm_num)
  -- the carried part in `Δ⁷`
  have hcar : δ x2 * δ x2 * δ (x5 ^ 1024) ∈ augIdeal G ^ 7 := by
    obtain ⟨q3, hq3⟩ : 2 ^ 10 ∣ Nat.choose 1024 3 :=
      two_pow_dvd_choose (m := 2) (by norm_num) (by decide)
    obtain ⟨q4, hq4⟩ : 2 ^ 8 ∣ Nat.choose 1024 4 := choose_four_dvd (a := 10) (by norm_num) (by norm_num)
    have hc2 : Nat.choose 1024 2 = 512 * 1023 := by
      have := two_mul_choose_two_nat 1024; omega
    have key : δ x2 * δ x2 * δ (x5 ^ 1024) =
        ((1024 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x5) +
        ((1024 : ℕ).choose 2 : ℤ) • (δ x2 * δ x2 * δ x5 ^ 2) +
        ((1024 : ℕ).choose 3 : ℤ) • (δ x2 * δ x2 * δ x5 ^ 3) +
        ((1024 : ℕ).choose 4 : ℤ) • (δ x2 * δ x2 * δ x5 ^ 4) +
        ((1024 : ℕ).choose 5 : ℤ) • (δ x2 * δ x2 * δ x5 ^ 5) +
        δ x2 * δ x2 * rem5 x5 1024 := by
      rw [δ_pow_eq5 x5]; simp only [mul_add, mul_smul_comm]
    rw [key]
    generalize Nat.choose 1024 2 = c2 at hc2 ⊢
    generalize Nat.choose 1024 3 = c3 at hq3 ⊢
    generalize Nat.choose 1024 4 = c4 at hq4 ⊢
    generalize Nat.choose 1024 5 = c5
    subst hc2 hq3 hq4
    refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_)
      (mm hW (rem5_mem x5 _) (by norm_num))
    · have e : ((1024 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x5) =
          (1 : ℤ) • ((((16 : ℤ) * 2 ^ 6) • (δ x2 * δ x2)) * δ x5) := by
        rw [smul_mul_assoc, smul_smul] <;> norm_num
      rw [e]; exact zsmul_mem (mm hL1 (δ_mem_pow_one x5) (by norm_num)) _
    · have e : (((512 * 1023 : ℕ) : ℤ)) • (δ x2 * δ x2 * δ x5 ^ 2) =
          (1023 : ℤ) • ((((8 : ℤ) * 2 ^ 6) • (δ x2 * δ x2)) * δ x5 ^ 2) := by
        rw [smul_mul_assoc, smul_smul] <;> norm_num
      rw [e]; exact zsmul_mem (mm hL0 (δpow_mem x5 2) (by norm_num)) _
    · have e : (((2 ^ 10 * q3 : ℕ) : ℤ)) • (δ x2 * δ x2 * δ x5 ^ 3) =
          (q3 : ℤ) • ((((16 : ℤ) * 2 ^ 6) • (δ x2 * δ x2)) * δ x5 ^ 3) := by
        rw [smul_mul_assoc, smul_smul]; congr 1; push_cast; ring
      rw [e]; exact zsmul_mem (mm hL1 (δpow_mem x5 3) (by norm_num)) _
    · have e : (((2 ^ 8 * q4 : ℕ) : ℤ)) • (δ x2 * δ x2 * δ x5 ^ 4) =
          (q4 : ℤ) • ((((2 : ℤ) ^ 2 * 2 ^ 6) • δ x2) * δ x2 * δ x5 ^ 4) := by
        rw [smul_mul_assoc, smul_mul_assoc, smul_smul]; congr 1; push_cast; ring
      rw [e]
      exact zsmul_mem (mm (mm (n := 4) (pw_le (m := 3) (by norm_num) hx2D (by norm_num) le_rfl)
        (δ_mem_pow_one x2) (by norm_num)) (δpow_mem x5 4) (by norm_num)) _
    · exact zsmul_mem (mm hW (δpow_mem x5 5) (by norm_num)) _
  -- the binomials of `x₁` in `Δ⁷`
  have htail : (Nat.choose 128 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
      (Nat.choose 128 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
      (Nat.choose 128 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
      (Nat.choose 128 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5) ∈ augIdeal G ^ 7 := by
    obtain ⟨q3, hq3⟩ : 2 ^ 7 ∣ Nat.choose 128 3 :=
      two_pow_dvd_choose (m := 2) (by norm_num) (by decide)
    obtain ⟨q4, hq4⟩ : 2 ^ 5 ∣ Nat.choose 128 4 := choose_four_dvd (a := 7) (by norm_num) (by norm_num)
    obtain ⟨q5, hq5⟩ : 2 ^ 7 ∣ Nat.choose 128 5 :=
      two_pow_dvd_choose (m := 4) (by norm_num) (by decide)
    have hc2 : Nat.choose 128 2 = 64 * 127 := by
      have := two_mul_choose_two_nat 128; omega
    generalize Nat.choose 128 2 = c2 at hc2 ⊢
    generalize Nat.choose 128 3 = c3 at hq3 ⊢
    generalize Nat.choose 128 4 = c4 at hq4 ⊢
    generalize Nat.choose 128 5 = c5 at hq5 ⊢
    subst hc2 hq3 hq4 hq5
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · have e : ((64 * 127 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) =
          (127 : ℤ) • (δ x2 * δ x2 * (((8 : ℤ) * 2 ^ 3) • (δ x1 * δ x1))) := by
        rw [pow_two (δ x1), mul_smul_comm, smul_smul] <;> norm_num
      rw [e]; exact zsmul_mem (mm hW hX1 (by norm_num)) _
    · have e : ((2 ^ 7 * q3 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) =
          ((2 : ℤ) * q3) • (δ x2 * δ x2 * (((8 : ℤ) * 2 ^ 3) • (δ x1 * δ x1)) * δ x1) := by
        rw [pow_three' (δ x1), mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc (δ x2 * δ x2)]
        congr 1; push_cast; ring
      rw [e]
      exact zsmul_mem (mm (mm (n := 7) hW hX1 (by norm_num)) (δ_mem_pow_one x1) (by norm_num)) _
    · have e : ((2 ^ 5 * q4 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) =
          (q4 : ℤ) • (δ x2 * δ x2 * ((((2 : ℤ) ^ 2 * 2 ^ 3) • δ x1) * δ x1 ^ 3)) := by
        rw [pow_succ' (δ x1) 3, smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1; push_cast; ring
      rw [e]
      exact zsmul_mem (mm hW (mm (n := 6) (pw_le (m := 3) (by norm_num) hx1D (by norm_num) le_rfl)
        (δpow_mem x1 3) (by norm_num)) (by norm_num)) _
    · have e : ((2 ^ 7 * q5 : ℕ) : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5) =
          ((2 : ℤ) ^ 4 * q5) • (δ x2 * δ x2 * ((((2 : ℤ) ^ 0 * 2 ^ 3) • δ x1) * δ x1 ^ 4)) := by
        rw [pow_succ' (δ x1) 4, smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1; push_cast; ring
      rw [e]
      exact zsmul_mem (mm hW (mm (n := 6) (pw_le (m := 2) (by norm_num) hx1D (by norm_num)
        (by norm_num)) (δpow_mem x1 4) (by norm_num)) (by norm_num)) _
  have hid := pow_mono (by norm_num : 7 ≤ 8) (theorem14_identity hclass ht h1 h5)
  have e : (128 : ℤ) • (δ x2 * δ x2 * δ x1) + (64 : ℤ) • (δ x2 * δ x2 * δ (pc t x3)) =
      ((128 : ℤ) • (δ x2 * δ x2 * δ x1) -
        (δ x2 * δ x2 * δ (x5 ^ 1024) - (64 : ℤ) • (δ x2 * δ x2 * δ (pc t x3)) -
          ((Nat.choose 128 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
            (Nat.choose 128 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
            (Nat.choose 128 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
            (Nat.choose 128 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5)))) +
        δ x2 * δ x2 * δ (x5 ^ 1024) -
        ((Nat.choose 128 2 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 2) +
          (Nat.choose 128 3 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 3) +
          (Nat.choose 128 4 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 4) +
          (Nat.choose 128 5 : ℤ) • (δ x2 * δ x2 * δ x1 ^ 5)) := by abel
  rw [e]
  exact sub_mem (add_mem hid hcar) htail

/-! ## Lemma 15: where `w` lives -/

theorem pc_central {k : ℕ} (hk : 1 ≤ k) (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥)
    (a : G) {y : G} (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1)) :
    ∀ g, Commute (pc a y) g :=
  commute_of_central hclass (by have := pc_mem_lcs_right a hy; rwa [Nat.sub_add_cancel hk] at this)

theorem abel_lcs {k : ℕ} (hk : 2 ≤ k) (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥)
    {p q : G} (hp : p ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hq : q ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1)) : Commute p q :=
  commute_of_lcs (i := k - 1) (by rwa [show k - 1 + 2 = k + 1 by omega]) hp
    (Subgroup.lowerCentralSeries_antitone (S := (⊤ : Subgroup G)) (by omega) hq)

/-- **Lemma 15** (§6.12(a)), with the paper's `x₁, x₂, x₃` as `x 0, x 1, x 2`. Let `G` have class
`≤ k + 1`, `k ≥ 2`, `x_i^{E_i} ∈ γ_k`, `E_j ∣ A_ij` (`i ≠ j`), `A` antisymmetric, and
`g_i = y_i^{E_i} z_i` with `y_i ∈ γ_k`, `z_i ∈ γ_{k+1}` for `i = 0, 1` (the pairing with multiplier 1).
Then `w = [x₂, x₁^{A₁₂}]`. -/
theorem lemma15 {k : ℕ} (hk : 2 ≤ k) (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥)
    (x : Fin 3 → G) (A : Fin 3 → Fin 3 → ℤ) (E : Fin 3 → ℕ) (hA : ∀ i j, A j i = -A i j)
    (hP : ∀ i, x i ^ E i ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hdvd : ∀ i j, i ≠ j → (E j : ℤ) ∣ A i j)
    (hg0 : ∃ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1),
      ∃ z ∈ (⊤ : Subgroup G).lowerCentralSeries k, Decomposition.g x A 0 = y ^ E 0 * z)
    (hg1 : ∃ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1),
      ∃ z ∈ (⊤ : Subgroup G).lowerCentralSeries k, Decomposition.g x A 1 = y ^ E 1 * z) :
    Decomposition.w x A = pc (x 1) (x 0 ^ A 0 1) := by
  have hcen : ∀ a, ∀ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1), ∀ g, Commute (pc a y) g :=
    fun a y hy => pc_central (by omega) hclass a hy
  have hzc : ∀ z ∈ (⊤ : Subgroup G).lowerCentralSeries k, ∀ a, pc a z = 1 :=
    fun z hz a => pc_eq_one_of_commute (commute_of_central hclass hz a).symm
  have hpow : ∀ i, ∀ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1), pc (x i) (y ^ E i) = 1 := by
    intro i y hy
    rw [← zpow_natCast y (E i), pc_zpow_right (hcen _ y hy), zpow_natCast,
      ← pc_pow_left (hcen _ y hy)]
    exact pc_eq_one_of_commute (abel_lcs hk hclass (hP i) hy)
  have hgi : ∀ i, (∃ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1),
      ∃ z ∈ (⊤ : Subgroup G).lowerCentralSeries k, Decomposition.g x A i = y ^ E i * z) →
      pc (x i) (Decomposition.g x A i) = 1 := by
    rintro i ⟨y, hy, z, hz, he⟩
    rw [he, pc_mul_right (hcen _ _ (pow_mem hy _)), hpow i y hy, hzc z hz, one_mul]
  have hh : ∀ i j, i ≠ j → Decomposition.hPow x A i j ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1) := by
    intro i j hij
    obtain ⟨q, hq⟩ := hdvd i j hij
    rw [Decomposition.hPow, hq, zpow_mul, zpow_natCast]
    exact zpow_mem (hP j) q
  have hfin : List.finRange 3 = [0, 1, 2] := by decide
  have hg0' : Decomposition.g x A 0 = Decomposition.hPow x A 0 1 * Decomposition.hPow x A 0 2 := by
    simp [Decomposition.g, hfin, List.filter]
  have hg1' : Decomposition.g x A 1 = Decomposition.hPow x A 1 0 * Decomposition.hPow x A 1 2 := by
    simp [Decomposition.g, hfin, List.filter]
  have e0 : Decomposition.u x A 0 1 * Decomposition.u x A 0 2 = 1 := by
    have := hgi 0 hg0
    rw [hg0', pc_mul_right (hcen _ _ (hh 0 1 (by decide)))] at this
    exact this
  have hQ : x 0 ^ A 0 1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1) := by
    obtain ⟨q, hq⟩ := hdvd 1 0 (by decide)
    rw [show A 0 1 = (E 0 : ℤ) * -q by linear_combination hA 0 1 - hq, zpow_mul, zpow_natCast]
    exact zpow_mem (hP 0) _
  have e1 : Decomposition.u x A 1 2 = pc (x 1) (x 0 ^ A 0 1) := by
    have := hgi 1 hg1
    rw [hg1', pc_mul_right (hcen _ _ (hh 1 0 (by decide)))] at this
    have h10 : pc (x 1) (Decomposition.hPow x A 1 0) = (pc (x 1) (x 0 ^ A 0 1))⁻¹ := by
      rw [Decomposition.hPow, hA 0 1,
        show x 0 ^ (-A 0 1) = (x 0 ^ A 0 1) ^ (-1 : ℤ) by rw [← zpow_mul, mul_neg_one],
        pc_zpow_right (hcen _ _ hQ), zpow_neg_one]
    rw [h10] at this
    exact (inv_mul_eq_one.mp this).symm
  rw [w_three, e0, one_mul, e1]

/-- `([x₂, ∏_l d_l^{−a_l}])^q = ∏_l [x₂, d_l]^{−a_l q}` for `d_l ∈ γ_k`, class `≤ k + 1`. -/
theorem pc_list_prod {k : ℕ} (hk : 1 ≤ k) (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥)
    (x2 : G) (q : ℤ) : ∀ l : List (G × ℤ),
      (∀ p ∈ l, p.1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1)) →
      pc x2 (l.map fun p => p.1 ^ (-p.2)).prod ^ q =
        (l.map fun p => pc x2 p.1 ^ (-p.2 * q)).prod
  | [], _ => by simp [pc]
  | p :: l, hl => by
    have hp : p.1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1) := hl p (by simp)
    have hl' : ∀ r ∈ l, r.1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1) :=
      fun r hr => hl r (by simp [hr])
    have hcen1 : ∀ g, Commute (pc x2 (p.1 ^ (-p.2))) g :=
      pc_central hk hclass x2 (zpow_mem hp _)
    simp only [List.map_cons, List.prod_cons]
    rw [pc_mul_right hcen1, (hcen1 _).mul_zpow, pc_zpow_right (pc_central hk hclass x2 hp),
      ← zpow_mul, pc_list_prod hk hclass x2 q l hl']

/-- **Lemma 15**, the product: if `x₁^{E₁} = ∏_l d_l^{−a_l}` with `d_l ∈ γ_k` (class `≤ k + 1`) and
`A = E₁ q`, then `[x₂, x₁^A] = ∏_l [x₂, d_l]^{−a_l q}`. -/
theorem lemma15_prod {k : ℕ} (hk : 1 ≤ k)
    (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥) {x1 x2 : G} {E1 : ℕ} {A q : ℤ}
    (l : List (G × ℤ)) (hd : ∀ p ∈ l, p.1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hP : x1 ^ E1 = (l.map fun p => p.1 ^ (-p.2)).prod) (hq : A = E1 * q) :
    pc x2 (x1 ^ A) = (l.map fun p => pc x2 p.1 ^ (-p.2 * q)).prod := by
  have hPm : (l.map fun p => p.1 ^ (-p.2)).prod ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1) :=
    list_prod_mem fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha; exact zpow_mem (hd p hp) _
  rw [hq, zpow_mul, zpow_natCast, hP, pc_zpow_right (pc_central hk hclass x2 hPm)]
  exact pc_list_prod hk hclass x2 q l hd

/-- **Lemma 15**, both parts: `w = ∏_l [x₂, d_l]^{−a_l A₁₂/E₁}`. -/
theorem lemma15_w {k : ℕ} (hk : 2 ≤ k) (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥)
    (x : Fin 3 → G) (A : Fin 3 → Fin 3 → ℤ) (E : Fin 3 → ℕ) (hA : ∀ i j, A j i = -A i j)
    (hP : ∀ i, x i ^ E i ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hdvd : ∀ i j, i ≠ j → (E j : ℤ) ∣ A i j)
    (hg0 : ∃ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1),
      ∃ z ∈ (⊤ : Subgroup G).lowerCentralSeries k, Decomposition.g x A 0 = y ^ E 0 * z)
    (hg1 : ∃ y ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1),
      ∃ z ∈ (⊤ : Subgroup G).lowerCentralSeries k, Decomposition.g x A 1 = y ^ E 1 * z)
    (l : List (G × ℤ)) (hd : ∀ p ∈ l, p.1 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hP0 : x 0 ^ E 0 = (l.map fun p => p.1 ^ (-p.2)).prod) {q : ℤ} (hq : A 0 1 = E 0 * q) :
    Decomposition.w x A = (l.map fun p => pc (x 1) p.1 ^ (-p.2 * q)).prod := by
  rw [lemma15 hk hclass x A E hA hP hdvd hg0 hg1]
  exact lemma15_prod (by omega) hclass l hd hP0 hq

/-- "Since `[x₂, d_l]^{E₂} = 1`, a part with `E₂ ∣ m` contributes nothing": `[x₂, d]^m = 1` for
`x₂^{E₂}, d ∈ γ_k` (class `≤ k + 1`, `k ≥ 2`) and `E₂ ∣ m`. -/
theorem part_trivial {k : ℕ} (hk : 2 ≤ k)
    (hclass : (⊤ : Subgroup G).lowerCentralSeries (k + 1) = ⊥) {x2 d : G} {E2 : ℕ}
    (hx2 : x2 ^ E2 ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1))
    (hd : d ∈ (⊤ : Subgroup G).lowerCentralSeries (k - 1)) {m : ℤ} (hm : (E2 : ℤ) ∣ m) :
    pc x2 d ^ m = 1 := by
  obtain ⟨r, rfl⟩ := hm
  rw [zpow_mul, zpow_natCast, ← pc_pow_left (pc_central (by omega) hclass x2 hd),
    pc_eq_one_of_commute (abel_lcs hk hclass hx2 hd), one_zpow]

end

end GroupDimension.Kernel.Carrier
