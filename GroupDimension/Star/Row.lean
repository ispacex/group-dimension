module

public import GroupDimension.Star.Defs
public import GroupDimension.Passi

@[expose] public section

/-!
# `(⋆)`, Lemma 1: the exact row identity (MATH-448)

Wiki page 891, §3, Lemma 1, in the form of `ExpThree.SetupB.rowB` (`G4Cube.lean`) but exact:
condition (E) is used with its true modulus `gcd(d(r), f(l))`, which kills `[x_{3l}, x_r]`
(its order divides `f(l)`, since `x_{3l}^{f(l)} ∈ γ₄`, and `d(r)`, since `[x_{3l}, x_r^{d(r)}] = 1`),
so no condition on the exponent of `γ₄` is needed.
-/

namespace GroupDimension

namespace Star

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

variable {G : Type*} [Group G] {N : Type*} [AddCommGroup N]

/-- (K4), the right-hand power rule for an element of `γ₃`: its commutators lie in the centre. -/
theorem tc_pow_right_L2 {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (x : G) (n : ℕ) :
    tc c (x ^ n) = tc c x ^ n := by
  induction n with
  | zero => simp [tc]
  | succ n ih =>
    have hz : tc c (x ^ n) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (by omega) hc (mem_lcs_zero _)
    have hconj : x⁻¹ * tc c (x ^ n) * x = tc c (x ^ n) := by
      rw [mul_assoc, ← central_L3 h5 hz x]
      group
    rw [pow_succ, tc_mul_right, hconj, ih, ← pow_succ']

/-- **Lemma 1 (row `r`), exact.** For every map `A` additive on `γ₃`:
`∑_k v_{rk} d(r) A[x_{2k}, x_r] + ∑_h crow_{rh} A[Y_h, x_r]
  = ∑_{h<r} u_{hr} q_{hr} A[Y_h, x_r, x_r] + ∑_l Ew_{rl} A[x_{3l}, x_r]`. -/
theorem row_exact {T : Data G} (h5 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) (hv : T.Valid)
    {τ : Coeffs T.s T.t} (hτ : T.Admissible τ) {A : G → N}
    (hA : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 2, ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 2,
      A (a * b) = A a + A b) (r : Fin T.s) :
    ∑ k, (τ.v r k * (T.d r : ℤ)) • A (tc (T.x₂ k) (T.x₁ r)) +
      ∑ h, crow T τ r h • A (tc (T.x₁ h ^ T.d h) (T.x₁ r)) =
    (∑ h, if h < r then
      (τ.u h r * T.q h r) • A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ r)) (T.x₁ r)) else 0) +
      ∑ l, Ew T τ r l • A (tc (T.x₃ l) (T.x₁ r)) := by
  classical
  have x2mem : ∀ k, T.x₂ k ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := hv.basis₂.mem
  have x3mem : ∀ l, T.x₃ l ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := hv.basis₃.mem
  have Y1 : ∀ h, T.x₁ h ^ T.d h ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
    intro h
    have hm := hv.hb h
    have hP : oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h) ∈
        (⊤ : Subgroup G).lowerCentralSeries 1 :=
      mul_mem (oprod_mem x2mem _) (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _)
    rw [← mul_inv_cancel_left (oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h)) (T.x₁ h ^ T.d h)]
    exact mul_mem hP (lcs_mem_of_le (by norm_num) hm)
  have x2e : ∀ k, T.x₂ k ^ T.e k ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    intro k
    have hm := hv.hdd k
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.dd k)) (T.x₂ k ^ T.e k)]
    exact mul_mem (oprod_mem x3mem _) (lcs_mem_of_le (by norm_num) hm)
  -- The map `Φ = A [·, x_r]`, additive on `γ₂`, zero on `γ₄`.
  let Φ : G → N := fun g => A (tc g (T.x₁ r))
  have hΦadd : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1,
      ∀ b ∈ (⊤ : Subgroup G).lowerCentralSeries 1, Φ (a * b) = Φ a + Φ b := by
    intro a ha b hb
    simp only [Φ]
    rw [tc_mul_left_L1 h5 ha hb, hA _ (tc_mem (by omega) ha (mem_lcs_zero _)) _
      (tc_mem (by omega) hb (mem_lcs_zero _))]
  have hΦ3 : ∀ a ∈ (⊤ : Subgroup G).lowerCentralSeries 3, Φ a = 0 := by
    intro a ha
    simp only [Φ]
    rw [tc_L3 h5 ha]
    exact addMapG_one hA
  have hΦrem : ∀ {y : G} {a : Fin T.u → ℤ},
      (oprod T.x₃ a)⁻¹ * y ∈ (⊤ : Subgroup G).lowerCentralSeries 3 →
      y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 → Φ y = ∑ l, a l • Φ (T.x₃ l) := by
    intro y a hy hy1
    have ho : oprod T.x₃ a ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      oprod_mem (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _
    rw [← mul_inv_cancel_left (oprod T.x₃ a) y, hΦadd _ ho _
      (lcs_mem_of_le (by norm_num) hy), hΦ3 _ hy, add_zero,
      addMapG_oprod hΦadd (fun l => lcs_mem_of_le (by norm_num) (x3mem l))]
  -- Both `d(r)` and `f(l)`, hence their gcd, kill `Φ(x_{3l})`.
  have hdl : ∀ l, (T.d r : ℤ) • Φ (T.x₃ l) = 0 := by
    intro l
    have hz : tc (T.x₃ l) (T.x₁ r) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (by omega) (x3mem l) (mem_lcs_zero _)
    have hm := addMapG_pow hA (lcs_mem_of_le (by norm_num) hz) (T.d r)
    rw [← tc_pow_right_L2 (x3mem l) h5, tc_L2_L1 h5 (x3mem l) (Y1 r),
      addMapG_one hA] at hm
    simpa only [Φ] using hm.symm
  have hfl : ∀ l, (T.f l : ℤ) • Φ (T.x₃ l) = 0 := by
    intro l
    have hz : tc (T.x₃ l) (T.x₁ r) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
      tc_mem (by omega) (x3mem l) (mem_lcs_zero _)
    have hm := addMapG_pow hA (lcs_mem_of_le (by norm_num) hz) (T.f l)
    rw [← tc_pow_left_L1 h5 (lcs_mem_of_le (by norm_num) (x3mem l)),
      tc_L3 h5 (hv.basis₃.pow_mem l), addMapG_one hA] at hm
    simpa only [Φ] using hm.symm
  have hgcd : ∀ l, (Nat.gcd (T.d r) (T.f l) : ℤ) • Φ (T.x₃ l) = 0 := by
    intro l
    rw [Nat.gcd_eq_gcd_ab, add_smul, mul_comm (T.d r : ℤ), mul_smul,
      mul_comm (T.f l : ℤ), mul_smul, hdl, hfl, smul_zero, smul_zero, add_zero]
  -- Expansion of `Y_h` in the second- and third-layer bases.
  have hY : ∀ h, ∑ k, T.b h k • Φ (T.x₂ k) =
      Φ (T.x₁ h ^ T.d h) - Φ (oprod T.x₃ (T.c h)) := by
    intro h
    have hm := hv.hb h
    have hb1 : oprod T.x₂ (T.b h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := oprod_mem x2mem _
    have hc1 : oprod T.x₃ (T.c h) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
      oprod_mem (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _
    have hn1 := lcs_mem_of_le (show 1 ≤ 3 by norm_num) hm
    rw [← addMapG_oprod (A := Φ) hΦadd x2mem (T.b h),
      ← mul_inv_cancel_left (oprod T.x₂ (T.b h) * oprod T.x₃ (T.c h)) (T.x₁ h ^ T.d h),
      hΦadd _ (mul_mem hb1 hc1) _ hn1, hΦ3 _ hm, add_zero, hΦadd _ hb1 _ hc1]
    abel
  have hBrow : ∀ k, τ.v' r k * (T.e k : ℤ) =
      -(∑ h, crow T τ r h * T.b h k) - τ.v r k * (T.d r : ℤ) := by
    intro k
    have hm := hτ.B r k
    have ec : ∑ h, crow T τ r h * T.b h k =
        (∑ h, if r < h then τ.u r h * T.b h k else 0) -
        ∑ h, if h < r then τ.u h r * T.q h r * T.b h k else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [crow]
      split_ifs <;> ring
    rw [ec]
    linarith
  -- The element `A_r = ∏_k (x_{2k}^{e(k)})^{v'_{rk}}` of `γ₃`.
  have hM : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) +
      ∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) +
      ∑ h, crow T τ r h • Φ (T.x₁ h ^ T.d h) =
      ∑ h, crow T τ r h • Φ (oprod T.x₃ (T.c h)) := by
    have hAk : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) =
        ∑ k, (τ.v' r k * (T.e k : ℤ)) • Φ (T.x₂ k) := by
      rw [addMapG_oprod hΦadd (fun k => lcs_mem_of_le (by norm_num) (x2e k))]
      exact Finset.sum_congr rfl fun k _ => by rw [addMapG_pow hΦadd (x2mem k), smul_smul]
    have hsum : ∑ k, (τ.v' r k * (T.e k : ℤ)) • Φ (T.x₂ k) +
        ∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) =
        -∑ h, crow T τ r h • ∑ k, T.b h k • Φ (T.x₂ k) := by
      calc
        _ = ∑ k, (τ.v' r k * (T.e k : ℤ) + τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => (add_smul _ _ _).symm
        _ = ∑ k, (-(∑ h, crow T τ r h * T.b h k)) • Φ (T.x₂ k) :=
          Finset.sum_congr rfl fun k _ => by rw [hBrow k]; congr 1; ring
        _ = -∑ h, crow T τ r h • ∑ k, T.b h k • Φ (T.x₂ k) := by
          simp only [neg_smul, Finset.sum_smul, Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
    rw [hAk, hsum]
    simp_rw [hY, smul_sub, Finset.sum_sub_distrib]
    abel
  -- Pairing `hα` once more gives the triple commutators in the `α`-part.
  have hαtriple : ∀ h, h ≤ r →
      A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ r)) (T.x₁ r)) =
        ∑ l, T.α h r l • Φ (T.x₃ l) := by
    intro h hhr
    have hm := hv.hα h r hhr
    have ho : oprod T.x₃ (T.α h r) ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
      oprod_mem x3mem _
    rw [← mul_inv_cancel_left (oprod T.x₃ (T.α h r)) (tc (T.x₁ h ^ T.d h) (T.x₁ r)),
      tc_mul_left_L1 h5 (lcs_mem_of_le (by norm_num) ho) (lcs_mem_of_le (by norm_num) hm),
      tc_L3 h5 hm, mul_one]
    change Φ (oprod T.x₃ (T.α h r)) = _
    exact addMapG_oprod hΦadd (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _
  -- Condition (E), with its true modulus.
  let αrow : Fin T.u → ℤ := fun l =>
    ∑ h, if h < r then τ.u h r * T.q h r * T.α h r l else 0
  have hE : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) +
      (∑ l, αrow l • Φ (T.x₃ l)) + (∑ l, Ew T τ r l • Φ (T.x₃ l)) =
      ∑ h, crow T τ r h • Φ (oprod T.x₃ (T.c h)) := by
    have hAk : Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)) =
        ∑ l, (∑ k, τ.v' r k * T.dd k l) • Φ (T.x₃ l) := by
      have hd' : ∀ k, Φ (T.x₂ k ^ T.e k) = ∑ l, T.dd k l • Φ (T.x₃ l) := fun k =>
        hΦrem (hv.hdd k) (lcs_mem_of_le (by norm_num) (x2e k))
      rw [addMapG_oprod hΦadd (fun k => lcs_mem_of_le (by norm_num) (x2e k))]
      simp_rw [hd', Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have hc : ∀ h, Φ (oprod T.x₃ (T.c h)) = ∑ l, T.c h l • Φ (T.x₃ l) := fun h =>
      hΦrem (by rw [inv_mul_cancel]; exact one_mem _)
        (oprod_mem (fun l => lcs_mem_of_le (by norm_num) (x3mem l)) _)
    simp_rw [hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, hAk, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, ← add_smul, ← add_smul]
    obtain ⟨q, hq⟩ := Int.modEq_zero_iff_dvd.mp (hτ.E r l)
    have e : (∑ k, τ.v' r k * T.dd k l) + αrow l + Ew T τ r l =
        (∑ h, crow T τ r h * T.c h l) - (Nat.gcd (T.d r) (T.f l) : ℤ) * q := by
      rw [← hq]
      have ec : ∑ h, crow T τ r h * T.c h l =
          (∑ h, if r < h then τ.u r h * T.c h l else 0) -
          ∑ h, if h < r then τ.u h r * T.q h r * T.c h l else 0 := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [crow]
        split_ifs <;> ring
      rw [ec]
      simp only [αrow, Ew]
      ring
    rw [e, sub_smul,
      show ((Nat.gcd (T.d r) (T.f l) : ℤ) * q) • Φ (T.x₃ l) =
        q • ((Nat.gcd (T.d r) (T.f l) : ℤ) • Φ (T.x₃ l)) by rw [smul_smul, mul_comm],
      hgcd, smul_zero, sub_zero]
  have hmain : (∑ k, (τ.v r k * (T.d r : ℤ)) • Φ (T.x₂ k)) +
      (∑ h, crow T τ r h • Φ (T.x₁ h ^ T.d h)) =
      (∑ l, αrow l • Φ (T.x₃ l)) + (∑ l, Ew T τ r l • Φ (T.x₃ l)) := by
    apply add_left_cancel (a := Φ (oprod (fun k => T.x₂ k ^ T.e k) (τ.v' r)))
    simpa only [add_assoc] using hM.trans hE.symm
  have hαsum : (∑ l, αrow l • Φ (T.x₃ l)) =
      ∑ h, if h < r then (τ.u h r * T.q h r) •
        A (tc (tc (T.x₁ h ^ T.d h) (T.x₁ r)) (T.x₁ r)) else 0 := by
    calc
      _ = ∑ l, ∑ h, if h < r then
          (τ.u h r * T.q h r * T.α h r l) • Φ (T.x₃ l) else 0 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [αrow, Finset.sum_smul]
        refine Finset.sum_congr rfl fun h _ => ?_
        split_ifs <;> simp
      _ = ∑ h, ∑ l, if h < r then
          (τ.u h r * T.q h r * T.α h r l) • Φ (T.x₃ l) else 0 := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun h _ => ?_
        by_cases hhr : h < r
        · simp only [hhr, ↓reduceIte]
          rw [hαtriple h hhr.le, Finset.smul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_smul]
        · simp only [hhr, ↓reduceIte, Finset.sum_const_zero]
  rw [← hαsum]
  exact hmain

end Star

end GroupDimension
