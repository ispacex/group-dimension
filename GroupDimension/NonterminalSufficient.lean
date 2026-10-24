module

public import GroupDimension.IterExt
public import GroupDimension.Nonterminal

@[expose] public section

/-!
# Theorem 6.12, sufficiency: a solution of (E)+(J) gives a nonterminal `P`

(Appendix, Step 5.) The paper defines `Q` by a pc-presentation and checks its consistency. Here
`Q` is constructed without presentations:

* `A = ℤ⁴/L` is the abelian group `⟨u, v, w, z⟩` with `u^p = z^{μ_u}`, `v^p = z^{μ_v}`,
  `w^p = z^p = 1`; `D_k : A → A` is `u ↦ w^{f_k} z^{σ_k}`, `v ↦ z^{η_k}`, `w ↦ z^{f_k}`,
  `z ↦ 1` (written additively), and `T_k = 1 + D_k`;
* `G̃` is the iterated extension of `A` by `x_0, …, x_{d-1}` of infinite order with
  `x_k⁻¹ a x_k = T_k a` and `[x_j, x_i] = u^{ω₁(j,i)} v^{ω₂(j,i)} w^{ω₃(j,i)}` for `j < i`
  (`IterExt.stage`); the condition for it to exist is the Jacobi identity, whose `z`-component is
  (J) and whose `w`-component holds in `P`;
* the elements `y_i = x_i^p (v^{α_i} w^{β_i})⁻¹` are central in `G̃`: this is (E);
* `Q = G̃/⟨y_0, …, y_{d-1}⟩`, with `Q → P` from the universal property of `G̃`; its kernel is
  `⟨z⟩` of order `p` (`z ∉ N` via `G̃ → ℤ^d`; the `x_i` are independent in `P/γ₂(P)`, since
  `|P/γ₂(P)| = p^d`), and `[[u, x_k], x_k] = z^{f_k²} ≠ 1` lies in `γ₄(Q)`.

`nonterminal_sufficient` is the statement for the data of `nonterminal_necessary`, with `x_i`
generating `P`, `|P/γ₂(P)| = p^d` and (N2); `nonterminal_iff` combines both directions. Here `P`
(and `Q`) live in `Type`, since the universal property of `G̃` is stated for targets in `Type`.
-/

namespace GroupDimension
namespace NonterminalSuff

open Subgroup Nonterminal Multiplicative
open scoped commutatorElement

/-- `ℤ⁴`, the coordinates `(u, v, w, z)`. -/
abbrev V4 := ℤ × ℤ × ℤ × ℤ

/-- The exponents of a normal form of `P` and a solution of (E)+(J), indexed by `ℕ`. -/
structure Data (p : ℕ) where
  μu : ZMod p
  μv : ZMod p
  f : ℕ → ZMod p
  σ : ℕ → ZMod p
  η : ℕ → ZMod p
  α : ℕ → ZMod p
  β : ℕ → ZMod p
  ω₁ : ℕ → ℕ → ZMod p
  ω₂ : ℕ → ℕ → ZMod p
  ω₃ : ℕ → ℕ → ZMod p

/-- The representative in `[0, p)` of an element of `𝔽_p`. -/
def Z {p : ℕ} (a : ZMod p) : ℤ := (a.val : ℤ)

theorem Z_cast {p : ℕ} [NeZero p] (a : ZMod p) : ((Z a : ℤ) : ZMod p) = a := by
  simp [Z]

theorem dvd_of_cast {p : ℕ} {x : ℤ} (h : (x : ZMod p) = 0) : (p : ℤ) ∣ x :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h

namespace Data

variable {p : ℕ} [Fact p.Prime] (𝔇 : Data p)

/-- The relations of `A`: `u^p = z^{μ_u}`, `v^p = z^{μ_v}`, `w^p = 1`, `z^p = 1`. -/
def L : AddSubgroup V4 :=
  AddSubgroup.closure {((p : ℤ), 0, 0, -Z 𝔇.μu), (0, (p : ℤ), 0, -Z 𝔇.μv), (0, 0, (p : ℤ), 0),
    (0, 0, 0, (p : ℤ))}

omit [Fact p.Prime] in
theorem mem_L {n : V4} (h1 : (p : ℤ) ∣ n.1) (h2 : (p : ℤ) ∣ n.2.1) (h3 : (p : ℤ) ∣ n.2.2.1)
    (h4 : (p : ℤ) ∣ n.2.2.2 + Z 𝔇.μu * (n.1 / p) + Z 𝔇.μv * (n.2.1 / p)) : n ∈ 𝔇.L := by
  obtain ⟨n1, n2, n3, n4⟩ := n
  obtain ⟨k1, rfl⟩ := h1
  obtain ⟨k2, rfl⟩ := h2
  obtain ⟨k3, rfl⟩ := h3
  rcases eq_or_ne (p : ℤ) 0 with hp0 | hp0
  · simp only [hp0, zero_mul, Int.ediv_zero, mul_zero, add_zero, zero_dvd_iff] at h4 ⊢
    have : ((0 : ℤ), (0 : ℤ), (0 : ℤ), n4) = 0 := by simp [h4]
    rw [this]; exact zero_mem _
  obtain ⟨k4, hk4⟩ := h4
  simp only [Int.mul_ediv_cancel_left _ hp0] at hk4
  have e : ((p : ℤ) * k1, (p : ℤ) * k2, (p : ℤ) * k3, n4) =
      k1 • ((p : ℤ), (0 : ℤ), (0 : ℤ), -Z 𝔇.μu) + k2 • ((0 : ℤ), (p : ℤ), (0 : ℤ), -Z 𝔇.μv) +
        k3 • ((0 : ℤ), (0 : ℤ), (p : ℤ), (0 : ℤ)) + k4 • ((0 : ℤ), (0 : ℤ), (0 : ℤ), (p : ℤ)) := by
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero, add_zero, zero_add,
      Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring, by linarith⟩
  rw [e]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
    exact zsmul_mem (AddSubgroup.subset_closure (by simp)) _

/-- `z`-type element of `L`: `(0, 0, m₃, m₄)` with `p ∣ m₃, m₄`. -/
theorem mem_L_zz (n : V4) (m3 m4 : ℤ) (h3 : (m3 : ZMod p) = 0) (h4 : (m4 : ZMod p) = 0)
    (hn : n = ((0 : ℤ), (0 : ℤ), m3, m4)) : n ∈ 𝔇.L := by
  subst hn
  apply 𝔇.mem_L <;> simp [dvd_of_cast h3, dvd_of_cast h4]

/-- `z` is not in `L`: the invariant `μ_u n₁ + μ_v n₂ + p n₄ (mod p²)`. -/
theorem z_notMem_L : ((0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ)) ∉ 𝔇.L := by
  let S : AddSubgroup V4 :=
    { carrier := {n | ((p : ℤ) ^ 2) ∣ Z 𝔇.μu * n.1 + Z 𝔇.μv * n.2.1 + p * n.2.2.2}
      add_mem' := fun {a c} ha hc => by
        have := dvd_add ha hc
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at this ⊢
        convert this using 1; ring
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        have := dvd_neg.mpr ha
        simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg] at this ⊢
        convert this using 1; ring }
  have hle : 𝔇.L ≤ S := by
    rw [L, AddSubgroup.closure_le]
    intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    show ((p : ℤ) ^ 2) ∣ _
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨0, by ring⟩
    · exact ⟨0, by ring⟩
    · exact ⟨0, by ring⟩
    · exact ⟨1, by ring⟩
  intro h
  obtain ⟨c, hc⟩ := hle h
  have hp1 : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℤ) ≠ 0 := by omega
  simp only [mul_zero, add_zero, zero_add, mul_one] at hc
  have h1 : (p : ℤ) * (p * c - 1) = 0 := by linear_combination (-1 : ℤ) * hc
  rcases mul_eq_zero.mp h1 with h | h
  · exact hp0 h
  · have := Int.le_of_dvd one_pos (⟨c, by linarith⟩ : (p : ℤ) ∣ 1)
    omega

/-- The abelian group `A = ⟨u, v, w, z⟩`. -/
abbrev A : Type := V4 ⧸ 𝔇.L

/-- `D_k` on `ℤ⁴`. -/
def Dt (k : ℕ) : V4 →+ V4 where
  toFun n := (0, 0, Z (𝔇.f k) * n.1, Z (𝔇.σ k) * n.1 + Z (𝔇.η k) * n.2.1 + Z (𝔇.f k) * n.2.2.1)
  map_zero' := by simp
  map_add' a c := by
    obtain ⟨a1, a2, a3, a4⟩ := a
    obtain ⟨c1, c2, c3, c4⟩ := c
    simp only [Prod.mk_add_mk, add_zero, Prod.mk.injEq, true_and]
    constructor <;> ring

omit [Fact p.Prime] in
theorem Dt_apply (k : ℕ) (n : V4) : 𝔇.Dt k n =
    (0, 0, Z (𝔇.f k) * n.1, Z (𝔇.σ k) * n.1 + Z (𝔇.η k) * n.2.1 + Z (𝔇.f k) * n.2.2.1) := rfl

omit [Fact p.Prime] in
theorem Dt_Dt (i j : ℕ) (n : V4) : 𝔇.Dt i (𝔇.Dt j n) = (0, 0, 0, Z (𝔇.f i) * (Z (𝔇.f j) * n.1)) := by
  simp only [Dt_apply, mul_zero, zero_add]

theorem Dt_comm (i j : ℕ) (n : V4) : 𝔇.Dt i (𝔇.Dt j n) = 𝔇.Dt j (𝔇.Dt i n) := by
  rw [Dt_Dt, Dt_Dt]; simp only [Prod.mk.injEq, true_and]; ring

theorem Dt_Dt_Dt (i j l : ℕ) (n : V4) : 𝔇.Dt i (𝔇.Dt j (𝔇.Dt l n)) = 0 := by
  rw [Dt_Dt]; simp [Dt_apply]

theorem L_le_comap_Dt (k : ℕ) : 𝔇.L ≤ 𝔇.L.comap (𝔇.Dt k) := by
  rw [L, AddSubgroup.closure_le]
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  show 𝔇.Dt k n ∈ 𝔇.L
  apply 𝔇.mem_L <;>
    rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [Dt_apply, mul_zero, zero_add, add_zero, Int.zero_ediv, dvd_zero, dvd_mul_left,
]

/-- `D_k` on `A`. -/
def D (k : ℕ) : 𝔇.A →+ 𝔇.A := QuotientAddGroup.map _ _ (𝔇.Dt k) (𝔇.L_le_comap_Dt k)

theorem D_mk (k : ℕ) (n : V4) : 𝔇.D k (n : 𝔇.A) = ((𝔇.Dt k n : V4) : 𝔇.A) := rfl

theorem D_D_D (i j l : ℕ) (a : 𝔇.A) : 𝔇.D i (𝔇.D j (𝔇.D l a)) = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H n => rw [D_mk, D_mk, D_mk, Dt_Dt_Dt]; rfl

theorem D_comm (i j : ℕ) (a : 𝔇.A) : 𝔇.D i (𝔇.D j a) = 𝔇.D j (𝔇.D i a) := by
  induction a using QuotientAddGroup.induction_on with
  | H n => rw [D_mk, D_mk, D_mk, D_mk, Dt_comm]

/-- `T_k = 1 + D_k`, conjugation by `x_k` on `A`. -/
def T (k : ℕ) : 𝔇.A ≃+ 𝔇.A where
  toFun a := a + 𝔇.D k a
  invFun a := a - 𝔇.D k a + 𝔇.D k (𝔇.D k a)
  left_inv a := by
    simp only [map_add, map_sub, 𝔇.D_D_D]; abel
  right_inv a := by
    simp only [map_add, map_sub, 𝔇.D_D_D]; abel
  map_add' a c := by simp only [map_add]; abel

theorem T_apply (k : ℕ) (a : 𝔇.A) : 𝔇.T k a = a + 𝔇.D k a := rfl

theorem T_mk (k : ℕ) (n : V4) : 𝔇.T k (n : 𝔇.A) = ((n + 𝔇.Dt k n : V4) : 𝔇.A) := by
  rw [T_apply, D_mk, QuotientAddGroup.mk_add]

theorem T_comm (i j : ℕ) (a : 𝔇.A) : 𝔇.T i (𝔇.T j a) = 𝔇.T j (𝔇.T i a) := by
  simp only [T_apply, map_add, 𝔇.D_comm i j]; abel

/-- `[x_j, x_i] = u^{ω₁(j,i)} v^{ω₂(j,i)} w^{ω₃(j,i)}`. -/
def b (j i : ℕ) : 𝔇.A :=
  ((Z (𝔇.ω₁ j i), Z (𝔇.ω₂ j i), Z (𝔇.ω₃ j i), (0 : ℤ)) : V4)

/-- The Jacobi identity in `A` (for `j < i < k`) from its `w`- and `z`-components. -/
theorem jacobi {j i k : ℕ}
    (hw : 𝔇.f i * 𝔇.ω₁ j k - 𝔇.f j * 𝔇.ω₁ i k - 𝔇.f k * 𝔇.ω₁ j i = 0)
    (hz : (𝔇.σ i * 𝔇.ω₁ j k + 𝔇.η i * 𝔇.ω₂ j k + 𝔇.f i * 𝔇.ω₃ j k) -
      (𝔇.σ j * 𝔇.ω₁ i k + 𝔇.η j * 𝔇.ω₂ i k + 𝔇.f j * 𝔇.ω₃ i k) -
      (𝔇.σ k * 𝔇.ω₁ j i + 𝔇.η k * 𝔇.ω₂ j i + 𝔇.f k * 𝔇.ω₃ j i) = 0) :
    -𝔇.T j (𝔇.b i k) + 𝔇.b j i + 𝔇.T i (𝔇.b j k) + 𝔇.b i k = 𝔇.b j k + 𝔇.T k (𝔇.b j i) := by
  simp only [b, T_mk, ← QuotientAddGroup.mk_neg, ← QuotientAddGroup.mk_add]
  rw [QuotientAddGroup.eq]
  refine 𝔇.mem_L_zz _ (Z (𝔇.f k) * Z (𝔇.ω₁ j i) + Z (𝔇.f j) * Z (𝔇.ω₁ i k) -
      Z (𝔇.f i) * Z (𝔇.ω₁ j k))
    ((Z (𝔇.σ k) * Z (𝔇.ω₁ j i) + Z (𝔇.η k) * Z (𝔇.ω₂ j i) + Z (𝔇.f k) * Z (𝔇.ω₃ j i)) +
      (Z (𝔇.σ j) * Z (𝔇.ω₁ i k) + Z (𝔇.η j) * Z (𝔇.ω₂ i k) + Z (𝔇.f j) * Z (𝔇.ω₃ i k)) -
      (Z (𝔇.σ i) * Z (𝔇.ω₁ j k) + Z (𝔇.η i) * Z (𝔇.ω₂ j k) + Z (𝔇.f i) * Z (𝔇.ω₃ j k)))
    (by push_cast [Z_cast]; linear_combination (-1 : ZMod p) * hw)
    (by push_cast [Z_cast]; linear_combination (-1 : ZMod p) * hz) ?_
  simp only [Dt_apply, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  refine ⟨by ring, by ring, by ring, by ring⟩


/-- `x_i^p = v^{α_i} w^{β_i}` in `A`. -/
def πA (i : ℕ) : 𝔇.A := (((0 : ℤ), Z (𝔇.α i), Z (𝔇.β i), (0 : ℤ)) : V4)

/-- The central element `z`. -/
def zA : 𝔇.A := (((0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ)) : V4)

theorem zA_ne : 𝔇.zA ≠ 0 := by
  intro h
  rw [zA, QuotientAddGroup.eq_zero_iff] at h
  exact 𝔇.z_notMem_L h

theorem D_zA (k : ℕ) : 𝔇.D k 𝔇.zA = 0 := by
  rw [zA, D_mk, QuotientAddGroup.eq_zero_iff, Dt_apply]
  simp only [mul_zero, add_zero]
  exact zero_mem _

theorem T_zA (k : ℕ) : 𝔇.T k 𝔇.zA = 𝔇.zA := by
  rw [T_apply, D_zA, add_zero]

theorem T_iterate (k n : ℕ) (m : V4) : (⇑(𝔇.T k))^[n] (m : 𝔇.A) =
    ((m + n • 𝔇.Dt k m + n.choose 2 • 𝔇.Dt k (𝔇.Dt k m) : V4) : 𝔇.A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, T_mk]
    congr 1
    rw [map_add, map_add, map_nsmul, map_nsmul, Dt_Dt_Dt, nsmul_zero, add_zero, choose_two_succ,
      add_nsmul, add_nsmul, one_nsmul]
    abel

theorem cast_choose_two (hp2 : p ≠ 2) : ((p.choose 2 : ℕ) : ZMod p) = 0 := by
  have h2 : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)
  obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) h2
  rw [hc, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem cast_choose_three (hp2 : p ≠ 2) :
    ((p.choose 3 : ℕ) : ZMod p) = if p = 3 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have h3 : 3 < p := by have := (Fact.out : p.Prime).two_le; omega
    obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) h3
    rw [hc, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- `x_k^p` acts trivially on `A`: `T_k^p = 1`. -/
theorem T_pow_p (hp2 : p ≠ 2) (k : ℕ) (a : 𝔇.A) : (⇑(𝔇.T k))^[p] a = a := by
  induction a using QuotientAddGroup.induction_on with
  | H m =>
    rw [T_iterate, QuotientAddGroup.eq]
    obtain ⟨n1, n2, n3, n4⟩ := m
    refine 𝔇.mem_L_zz _ (-((p : ℤ) * (Z (𝔇.f k) * n1)))
      (-((p : ℤ) * (Z (𝔇.σ k) * n1 + Z (𝔇.η k) * n2 + Z (𝔇.f k) * n3)) -
        (p.choose 2 : ℤ) * (Z (𝔇.f k) * (Z (𝔇.f k) * n1)))
      (by push_cast; simp) (by push_cast [cast_choose_two hp2]; simp) ?_
    simp only [Dt_apply, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
      Prod.smul_fst, Prod.smul_snd]
    simp only [nsmul_eq_mul]
    refine ⟨by ring, by ring, by ring, by ring⟩

/-- **(E) in `A`**: for `β = u^{B₁} v^{B₂} w^{B₃}` with `B_r ≡ ω_r(i,j)`,
`p β + \binom p2 D_i β + \binom p3 D_i² β = D_j π_i`. This is what makes `y_i` commute with
`x_j`. -/
theorem E_mem (hp2 : p ≠ 2) (i j : ℕ) (B1 B2 B3 : ℤ)
    (hE : 𝔇.μu * (B1 : ZMod p) + 𝔇.μv * (B2 : ZMod p) +
      (if p = 3 then 1 else 0) * 𝔇.f i ^ 2 * (B1 : ZMod p) - 𝔇.η j * 𝔇.α i - 𝔇.f j * 𝔇.β i = 0) :
    p • (((B1, B2, B3, (0 : ℤ)) : V4) : 𝔇.A) +
      p.choose 2 • 𝔇.D i (((B1, B2, B3, (0 : ℤ)) : V4) : 𝔇.A) +
      p.choose 3 • 𝔇.D i (𝔇.D i (((B1, B2, B3, (0 : ℤ)) : V4) : 𝔇.A)) - 𝔇.D j (𝔇.πA i) = 0 := by
  simp only [πA, D_mk]
  rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul,
    ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add,
    ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : p • ((B1, B2, B3, (0 : ℤ)) : V4) + p.choose 2 • 𝔇.Dt i (B1, B2, B3, 0) +
      p.choose 3 • 𝔇.Dt i (𝔇.Dt i (B1, B2, B3, 0)) - 𝔇.Dt j (0, Z (𝔇.α i), Z (𝔇.β i), 0) =
      ((p : ℤ) * B1, (p : ℤ) * B2, (p : ℤ) * B3 + (p.choose 2 : ℤ) * (Z (𝔇.f i) * B1),
        (p.choose 2 : ℤ) * (Z (𝔇.σ i) * B1 + Z (𝔇.η i) * B2 + Z (𝔇.f i) * B3) +
        (p.choose 3 : ℤ) * (Z (𝔇.f i) * (Z (𝔇.f i) * B1)) -
        (Z (𝔇.η j) * Z (𝔇.α i) + Z (𝔇.f j) * Z (𝔇.β i))) := by
    simp only [Dt_apply, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd]
    simp only [nsmul_eq_mul]
    refine ⟨by ring, by ring, by ring, by ring⟩
  rw [e]
  apply 𝔇.mem_L
  · exact dvd_mul_right _ _
  · exact dvd_mul_right _ _
  · exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_of_cast (by
      push_cast [cast_choose_two hp2]; rfl)) _)
  · simp only [Int.mul_ediv_cancel_left _ hp0]
    apply dvd_of_cast
    push_cast [cast_choose_two hp2, cast_choose_three hp2, Z_cast]
    linear_combination hE


omit [Fact p.Prime] in
theorem p_zA : p • 𝔇.zA = 0 := by
  rw [zA, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  apply AddSubgroup.subset_closure
  simp

/-- An element of `A` killed by `u, v, w ↦ ·` is a power of `z`. -/
theorem eq_zsmul_zA {n : V4} (h1 : (p : ℤ) ∣ n.1) (h2 : (p : ℤ) ∣ n.2.1) (h3 : (p : ℤ) ∣ n.2.2.1) :
    (n : 𝔇.A) = (n.2.2.2 + Z 𝔇.μu * (n.1 / p) + Z 𝔇.μv * (n.2.1 / p)) • 𝔇.zA := by
  rw [zA, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq]
  obtain ⟨n1, n2, n3, n4⟩ := n
  apply 𝔇.mem_L <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_zero, add_zero, mul_one] at h1 h2 h3 ⊢
  · exact dvd_neg.mpr h1
  · exact dvd_neg.mpr h2
  · exact dvd_neg.mpr h3
  · rw [Int.neg_ediv_of_dvd h1, Int.neg_ediv_of_dvd h2]
    exact ⟨0, by ring⟩

end Data

/-! ### The group `G̃` and the quotient `Q` -/

section Group

variable {P : Type} [Group P] {p : ℕ} [Fact p.Prime]

/-- Hypotheses on `P` and on the data (indices `< d`): the relations of the normal form, `u, v, w`
of exponent `p`, `v, w` central, the Jacobi identity in `A` (`hJw`, `hJz`), (E) (`hE`) and the
alternation of the `ω_r`. -/
structure Hyp (𝔇 : Data p) (d : ℕ) (x : ℕ → P) (u v w : P) : Prop where
  hp2 : p ≠ 2
  hvc : v ∈ center P
  hwc : w ∈ center P
  hu : u ^ p = 1
  hv : v ^ p = 1
  hw : w ^ p = 1
  hf : ∀ k < d, u⁻¹ * (x k)⁻¹ * u * x k = w ^ (𝔇.f k).val
  hω : ∀ j i, j < d → i < d →
    (x j)⁻¹ * (x i)⁻¹ * x j * x i = u ^ (𝔇.ω₁ j i).val * v ^ (𝔇.ω₂ j i).val * w ^ (𝔇.ω₃ j i).val
  hpow : ∀ i < d, x i ^ p = v ^ (𝔇.α i).val * w ^ (𝔇.β i).val
  hJw : ∀ j i k, j < i → i < k → k < d →
    𝔇.f i * 𝔇.ω₁ j k - 𝔇.f j * 𝔇.ω₁ i k - 𝔇.f k * 𝔇.ω₁ j i = 0
  hJz : ∀ j i k, j < i → i < k → k < d →
    (𝔇.σ i * 𝔇.ω₁ j k + 𝔇.η i * 𝔇.ω₂ j k + 𝔇.f i * 𝔇.ω₃ j k) -
      (𝔇.σ j * 𝔇.ω₁ i k + 𝔇.η j * 𝔇.ω₂ i k + 𝔇.f j * 𝔇.ω₃ i k) -
      (𝔇.σ k * 𝔇.ω₁ j i + 𝔇.η k * 𝔇.ω₂ j i + 𝔇.f k * 𝔇.ω₃ j i) = 0
  hE : ∀ i j, i < d → j < d → 𝔇.μu * 𝔇.ω₁ i j + 𝔇.μv * 𝔇.ω₂ i j +
    (if p = 3 then 1 else 0) * 𝔇.f i ^ 2 * 𝔇.ω₁ i j - 𝔇.η j * 𝔇.α i - 𝔇.f j * 𝔇.β i = 0
  hanti : ∀ i j, i < d → j < d →
    𝔇.ω₁ j i = -𝔇.ω₁ i j ∧ 𝔇.ω₂ j i = -𝔇.ω₂ i j ∧ 𝔇.ω₃ j i = -𝔇.ω₃ i j

namespace Hyp

variable {𝔇 : Data p} {d : ℕ} {x : ℕ → P} {u v w : P} (H : Hyp 𝔇 d x u v w)

include H in
theorem central_comm {c : P} (hc : c ∈ center P) (g : P) : Commute g c :=
  mem_center_iff.mp hc g

/-- `n ↦ u^{n₁} v^{n₂} w^{n₃}` on `ℤ⁴`. -/
def ψt : V4 →+ Additive P where
  toFun n := Additive.ofMul (u ^ n.1 * (v ^ n.2.1 * w ^ n.2.2.1))
  map_zero' := by simp
  map_add' a c := by
    rw [← ofMul_mul]
    congr 1
    obtain ⟨a1, a2, a3, a4⟩ := a
    obtain ⟨c1, c2, c3, c4⟩ := c
    simp only [Prod.mk_add_mk, zpow_add]
    have hX : Commute (v ^ a2 * w ^ a3) (u ^ c1) :=
      (H.central_comm (mul_mem (zpow_mem H.hvc _) (zpow_mem H.hwc _)) _).symm
    have hW : Commute (w ^ a3) (v ^ c2) := (H.central_comm (zpow_mem H.hwc _) _).symm
    rw [hX.mul_mul_mul_comm, hW.mul_mul_mul_comm]

theorem ψt_L : 𝔇.L ≤ H.ψt.ker := by
  rw [Data.L, AddSubgroup.closure_le]
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
  show Additive.ofMul _ = 0
  rw [ofMul_eq_zero]
  rcases hn with rfl | rfl | rfl | rfl <;>
    simp only [zpow_natCast, zpow_zero, H.hu, H.hv, H.hw, mul_one]

/-- `A → P`, `u ↦ u`, `v ↦ v`, `w ↦ w`, `z ↦ 1`. -/
def ψA : Multiplicative 𝔇.A →* P where
  toFun a := Additive.toMul (QuotientAddGroup.lift 𝔇.L H.ψt H.ψt_L (toAdd a))
  map_one' := by simp
  map_mul' a c := by simp [toAdd_mul]

theorem ψA_mk (n : V4) : H.ψA (ofAdd (n : 𝔇.A)) = u ^ n.1 * (v ^ n.2.1 * w ^ n.2.2.1) := rfl

theorem ψA_mem (a : Multiplicative 𝔇.A) (hu1 : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1)
    (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hw1 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 1) :
    H.ψA a ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
  obtain ⟨a, rfl⟩ := ofAdd.surjective a
  induction a using QuotientAddGroup.induction_on with
  | H n => rw [ψA_mk]; exact mul_mem (zpow_mem hu1 _) (mul_mem (zpow_mem hv1 _) (zpow_mem hw1 _))

include H in
theorem conj_u {k : ℕ} (hk : k < d) : (x k)⁻¹ * u * x k = u * w ^ Z (𝔇.f k) := by
  rw [Z, zpow_natCast, ← H.hf k hk]; group

/-- The iterated extension `G̃`. -/
def S : IterExt.Stage 𝔇.T 𝔇.b d :=
  IterExt.stage 𝔇.T 𝔇.b 𝔇.T_comm d
    (fun i j k hji hik hkd => 𝔇.jacobi (H.hJw j i k hji hik hkd) (H.hJz j i k hji hik hkd)) d le_rfl

theorem lift_h1 : ∀ j < d, ∀ a : 𝔇.A,
    (x j)⁻¹ * H.ψA (ofAdd a) * x j = H.ψA (ofAdd (𝔇.T j a)) := by
  intro j hj a
  induction a using QuotientAddGroup.induction_on with
  | H n =>
    rw [Data.T_mk, ψA_mk, ψA_mk]
    obtain ⟨n1, n2, n3, n4⟩ := n
    simp only [Data.Dt_apply, Prod.mk_add_mk, add_zero]
    have hC : v ^ n2 * w ^ n3 ∈ center P := mul_mem (zpow_mem H.hvc _) (zpow_mem H.hwc _)
    have hconj : (x j)⁻¹ * u ^ n1 * x j = (u * w ^ Z (𝔇.f j)) ^ n1 := by
      have := conj_zpow (a := (x j)⁻¹) (b := u) (i := n1)
      rw [inv_inv] at this
      rw [← this, H.conj_u hj]
    have hW : Commute u (w ^ Z (𝔇.f j)) := H.central_comm (zpow_mem H.hwc _) u
    calc (x j)⁻¹ * (u ^ n1 * (v ^ n2 * w ^ n3)) * x j
        = ((x j)⁻¹ * u ^ n1 * x j) * ((x j)⁻¹ * (v ^ n2 * w ^ n3) * x j) := by group
      _ = u ^ n1 * w ^ (Z (𝔇.f j) * n1) * (v ^ n2 * w ^ n3) := by
          rw [hconj, conj_eq_mul_pc, pc_of_mem_center hC, mul_one, hW.mul_zpow, ← zpow_mul]
      _ = u ^ n1 * (v ^ n2 * w ^ (n3 + Z (𝔇.f j) * n1)) := by
          rw [mul_assoc, ← (H.central_comm (zpow_mem H.hwc (Z (𝔇.f j) * n1)) (v ^ n2 * w ^ n3)).eq,
            zpow_add]
          simp only [mul_assoc]

theorem lift_h2 : ∀ i j, j < i → i < d →
    (x i)⁻¹ * x j * x i = x j * H.ψA (ofAdd (𝔇.b j i)) := by
  intro i j hji hid
  rw [Data.b, ψA_mk, conj_eq_mul_pc]
  simp only [Z, zpow_natCast]
  rw [show pc (x j) (x i) = _ from H.hω j i (hji.trans hid) hid, mul_assoc]

/-- `G̃ → P`. -/
def πt : H.S.G →* P := (H.S.lift H.ψA x H.lift_h1 H.lift_h2).1

theorem πt_ι (a : Multiplicative 𝔇.A) : H.πt (H.S.ι a) = H.ψA a :=
  (H.S.lift H.ψA x H.lift_h1 H.lift_h2).2.1 a

theorem πt_X {j : ℕ} (hj : j < d) : H.πt (H.S.X j) = x j :=
  (H.S.lift H.ψA x H.lift_h1 H.lift_h2).2.2 j hj

/-- The generators of `ℤ^d`. -/
def e (j : ℕ) : Multiplicative (Fin d → ℤ) :=
  if h : j < d then ofAdd (Pi.single ⟨j, h⟩ 1) else 1

/-- `G̃ → ℤ^d`, killing `A`. -/
def τ : H.S.G →* Multiplicative (Fin d → ℤ) :=
  (H.S.lift 1 e (fun j _ a => by simp)
    (fun i j _ _ => by rw [MonoidHom.one_apply, mul_one, mul_comm, mul_inv_cancel_left])).1

theorem τ_ι (a : Multiplicative 𝔇.A) : H.τ (H.S.ι a) = 1 :=
  (H.S.lift 1 e (fun j _ a => by simp)
    (fun i j _ _ => by rw [MonoidHom.one_apply, mul_one, mul_comm, mul_inv_cancel_left])).2.1 a

theorem τ_X {j : ℕ} (hj : j < d) : H.τ (H.S.X j) = e j :=
  (H.S.lift 1 e (fun j _ a => by simp)
    (fun i j _ _ => by rw [MonoidHom.one_apply, mul_one, mul_comm, mul_inv_cancel_left])).2.2 j hj

/-- `y_i = x_i^p (v^{α_i} w^{β_i})⁻¹`. -/
def y (i : ℕ) : H.S.G := H.S.X i ^ p * (H.S.ι (ofAdd (𝔇.πA i)))⁻¹

theorem πt_y {i : ℕ} (hi : i < d) : H.πt (H.y i) = 1 := by
  rw [y, map_mul, map_pow, map_inv, πt_X H hi, πt_ι, Data.πA, ψA_mk, H.hpow i hi]
  simp only [zpow_zero, one_mul, Z, zpow_natCast, mul_inv_cancel]

theorem τ_y {i : ℕ} (hi : i < d) : H.τ (H.y i) = ofAdd (p • Pi.single ⟨i, hi⟩ (1 : ℤ)) := by
  rw [y, map_mul, map_pow, map_inv, τ_X H hi, τ_ι, inv_one, mul_one, e, dif_pos hi, ← ofAdd_nsmul]

theorem pc_ι {i : ℕ} (hi : i < d) (c : 𝔇.A) :
    pc (H.S.ι (ofAdd c)) (H.S.X i) = H.S.ι (ofAdd (𝔇.D i c)) := by
  have h := H.S.conj_ι i hi c
  calc pc (H.S.ι (ofAdd c)) (H.S.X i)
      = (H.S.ι (ofAdd c))⁻¹ * ((H.S.X i)⁻¹ * H.S.ι (ofAdd c) * H.S.X i) := by simp only [pc]; group
    _ = H.S.ι (ofAdd (𝔇.D i c)) := by
        rw [h, ← H.S.ι_neg, ← H.S.ι_add, Data.T_apply, neg_add_cancel_left]

theorem ι_pow (c : 𝔇.A) (n : ℕ) : H.S.ι (ofAdd c) ^ n = H.S.ι (ofAdd (n • c)) := by
  rw [ofAdd_nsmul, map_pow]

theorem comm_Xp_ι {i : ℕ} (hi : i < d) (a : 𝔇.A) : Commute (H.S.X i ^ p) (H.S.ι (ofAdd a)) := by
  have h := H.S.conj_pow hi a p
  rw [𝔇.T_pow_p H.hp2] at h
  show H.S.X i ^ p * H.S.ι (ofAdd a) = H.S.ι (ofAdd a) * H.S.X i ^ p
  conv_lhs => rw [← h]
  group

theorem comm_y_ι {i : ℕ} (hi : i < d) (a : 𝔇.A) : Commute (H.y i) (H.S.ι (ofAdd a)) :=
  (H.comm_Xp_ι hi a).mul_left (Commute.inv_left (H.S.ι_comm _ _))

/-- `x_j⁻¹ x_i x_j = x_i β` with `β = u^{B₁} v^{B₂} w^{B₃}`, `B_r ≡ ω_r(i,j)`. -/
theorem conj_X_lift {i j : ℕ} (hi : i < d) (hj : j < d) :
    ∃ B1 B2 B3 : ℤ, (H.S.X j)⁻¹ * H.S.X i * H.S.X j =
      H.S.X i * H.S.ι (ofAdd ((((B1, B2, B3, (0 : ℤ)) : V4) : 𝔇.A))) ∧
      (B1 : ZMod p) = 𝔇.ω₁ i j ∧ (B2 : ZMod p) = 𝔇.ω₂ i j := by
  rw [H.S.conj_X' hi hj]
  rcases lt_trichotomy i j with h | rfl | h
  · refine ⟨Z (𝔇.ω₁ i j), Z (𝔇.ω₂ i j), Z (𝔇.ω₃ i j), ?_, Z_cast _, Z_cast _⟩
    rw [if_pos h, Data.b]
  · have h0 : ∀ a : ZMod p, a = -a → a = 0 := by
      intro a ha
      have h2 : (2 : ZMod p) * a = 0 := by linear_combination ha
      rcases mul_eq_zero.mp h2 with h2 | h2
      · exfalso
        have : (p : ℤ) ∣ 2 := dvd_of_cast (by exact_mod_cast h2)
        have hp2 := Int.le_of_dvd (by norm_num) this
        have := (Fact.out : p.Prime).two_le
        have := H.hp2
        omega
      · exact h2
    refine ⟨0, 0, 0, ?_, ?_, ?_⟩
    · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      rfl
    · rw [h0 _ (H.hanti i i hi hi).1]; simp
    · rw [h0 _ (H.hanti i i hi hi).2.1]; simp
  · refine ⟨-Z (𝔇.ω₁ j i), -Z (𝔇.ω₂ j i), -Z (𝔇.ω₃ j i), ?_, ?_, ?_⟩
    · rw [if_neg (lt_asymm h), if_pos h, Data.b, ← QuotientAddGroup.mk_neg, Prod.neg_mk,
        Prod.neg_mk, Prod.neg_mk, neg_zero]
    · push_cast [Z_cast]; rw [(H.hanti j i hj hi).1]
    · push_cast [Z_cast]; rw [(H.hanti j i hj hi).2.1]

theorem comm_y_X {i j : ℕ} (hi : i < d) (hj : j < d) : Commute (H.y i) (H.S.X j) := by
  obtain ⟨B1, B2, B3, hB, h1, h2⟩ := H.conj_X_lift hi hj
  set β : 𝔇.A := (((B1, B2, B3, (0 : ℤ)) : V4) : 𝔇.A)
  have hβ1 := H.pc_ι hi β
  have hβ2 := H.pc_ι hi (𝔇.D i β)
  have hβ3 : pc (H.S.ι (ofAdd (𝔇.D i (𝔇.D i β)))) (H.S.X i) = 1 := by
    rw [H.pc_ι hi, 𝔇.D_D_D, H.S.ι_zero]
  have hpow := mul_pow_formula (a := H.S.ι (ofAdd β)) (x := H.S.X i) hβ1 hβ2 hβ3
    (H.S.ι_comm _ _) (H.S.ι_comm _ _) (H.S.ι_comm _ _) p
  have hE := 𝔇.E_mem H.hp2 i j B1 B2 B3 (by rw [h1, h2]; exact H.hE i j hi hj)
  have key : (H.S.X j)⁻¹ * H.y i * H.S.X j = H.y i := by
    calc (H.S.X j)⁻¹ * H.y i * H.S.X j
        = ((H.S.X j)⁻¹ * H.S.X i * H.S.X j) ^ p *
          ((H.S.X j)⁻¹ * H.S.ι (ofAdd (𝔇.πA i)) * H.S.X j)⁻¹ := by
          rw [y, conj_pow']; group
      _ = H.S.X i ^ p * H.S.ι (ofAdd (p • β + p.choose 2 • 𝔇.D i β +
            p.choose 3 • 𝔇.D i (𝔇.D i β) - 𝔇.T j (𝔇.πA i))) := by
          rw [hB, hpow, H.S.conj_ι j hj, H.ι_pow, H.ι_pow, H.ι_pow, sub_eq_add_neg, H.S.ι_add,
            H.S.ι_add, H.S.ι_add, H.S.ι_neg]
          simp only [mul_assoc]
      _ = H.y i := by
          rw [y, Data.T_apply, show p • β + p.choose 2 • 𝔇.D i β + p.choose 3 • 𝔇.D i (𝔇.D i β) -
            (𝔇.πA i + 𝔇.D j (𝔇.πA i)) = -𝔇.πA i by rw [← sub_eq_zero] at hE ⊢; rw [← hE]; abel,
            H.S.ι_neg]
  calc H.y i * H.S.X j = H.S.X j * ((H.S.X j)⁻¹ * H.y i * H.S.X j) := by group
    _ = H.S.X j * H.y i := by rw [key]

theorem y_mem_center {i : ℕ} (hi : i < d) : H.y i ∈ center H.S.G :=
  H.S.mem_center (H.comm_y_ι hi) (fun j hj => H.comm_y_X hi hj)

theorem ιz_mem_center : H.S.ι (ofAdd 𝔇.zA) ∈ center H.S.G :=
  H.S.mem_center (fun a => H.S.ι_comm _ _) (fun j hj => by
    show H.S.ι (ofAdd 𝔇.zA) * H.S.X j = H.S.X j * H.S.ι (ofAdd 𝔇.zA)
    rw [H.S.ι_mul_X hj, 𝔇.T_zA])

/-- `ℤ^d → G̃`, `k ↦ ∏ y_i^{k_i}` (the `y_i` are central). -/
theorem y_comm : Pairwise fun i j : Fin d => ∀ a c : Multiplicative ℤ,
    Commute (zpowersHom H.S.G (H.y i) a) (zpowersHom H.S.G (H.y j) c) := by
  intro _ j _ a c
  simp only [zpowersHom_apply]
  exact mem_center_iff.mp (zpow_mem (H.y_mem_center j.2) _) _

def ν : (Fin d → Multiplicative ℤ) →* H.S.G :=
  MonoidHom.noncommPiCoprod (fun i => zpowersHom H.S.G (H.y i)) H.y_comm

theorem ν_single (i : Fin d) (g : Multiplicative ℤ) :
    H.ν (Pi.mulSingle i g) = H.y i ^ toAdd g := by
  rw [ν, MonoidHom.noncommPiCoprod_mulSingle, zpowersHom_apply]

/-- `N = ⟨y_0, …, y_{d-1}⟩`, central. -/
def N : Subgroup H.S.G := H.ν.range

theorem N_le_center : H.N ≤ center H.S.G := by
  rw [N, ν, MonoidHom.noncommPiCoprod_range, iSup_le_iff]
  rintro i _ ⟨m, rfl⟩
  rw [zpowersHom_apply]
  exact zpow_mem (H.y_mem_center i.2) _

instance N_normal : H.N.Normal :=
  ⟨fun n hn g => by rw [mem_center_iff.mp (H.N_le_center hn) g, mul_inv_cancel_right]; exact hn⟩

theorem y_mem_N {i : ℕ} (hi : i < d) : H.y i ∈ H.N :=
  ⟨Pi.mulSingle ⟨i, hi⟩ (ofAdd 1), by rw [ν_single, toAdd_ofAdd, zpow_one]⟩

/-- `k ↦ p k` on `ℤ^d`. -/
def χ (p d : ℕ) : (Fin d → Multiplicative ℤ) →* Multiplicative (Fin d → ℤ) where
  toFun k := ofAdd (fun i => (p : ℤ) * toAdd (k i))
  map_one' := by ext i; simp
  map_mul' a c := by ext i; simp [mul_add]

theorem τ_ν (k : Fin d → Multiplicative ℤ) : H.τ (H.ν k) = χ p d k := by
  have := MonoidHom.functions_ext (Multiplicative (Fin d → ℤ)) (H.τ.comp H.ν) (χ p d)
    (fun i g => by
      rw [MonoidHom.comp_apply, ν_single, map_zpow, H.τ_y i.2]
      apply toAdd.injective
      ext l
      by_cases hl : l = i
      · subst hl; simp [χ]; ring
      · simp [χ, Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl])
  exact DFunLike.congr_fun this k

theorem ιz_notMem_N : H.S.ι (ofAdd 𝔇.zA) ∉ H.N := by
  rintro ⟨k, hk⟩
  have h1 : χ p d k = 1 := by rw [← H.τ_ν, hk, τ_ι]
  have hk1 : k = 1 := by
    funext i
    have := congrArg (fun m : Multiplicative (Fin d → ℤ) => toAdd m i) h1
    simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one, Pi.zero_apply,
      mul_eq_zero, Nat.cast_eq_zero, (Fact.out : p.Prime).ne_zero, false_or] at this
    rw [Pi.one_apply, ← ofAdd_toAdd (k i), this, ofAdd_zero]
  subst hk1
  rw [map_one] at hk
  have := H.S.ι_injective (hk.symm.trans (map_one _).symm)
  exact 𝔇.zA_ne (by simpa using this)


/-! ### `Q = G̃/N` -/

theorem N_le_ker : H.N ≤ H.πt.ker := by
  rw [N, ν, MonoidHom.noncommPiCoprod_range, iSup_le_iff]
  rintro i _ ⟨m, rfl⟩
  rw [zpowersHom_apply, MonoidHom.mem_ker, map_zpow, H.πt_y i.2, one_zpow]

/-- `Q`. -/
abbrev Q : Type := H.S.G ⧸ H.N

/-- `G̃ → Q`. -/
abbrev mkQ : H.S.G →* H.Q := QuotientGroup.mk' H.N

/-- `Q → P`. -/
def πQ : H.Q →* P := QuotientGroup.lift H.N H.πt H.N_le_ker

theorem πQ_mk (g : H.S.G) : H.πQ (H.mkQ g) = H.πt g := rfl

/-- The central element `z ∈ Q`. -/
def zQ : H.Q := H.mkQ (H.S.ι (ofAdd 𝔇.zA))

theorem zQ_mem_center : H.zQ ∈ center H.Q := by
  rw [mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H.N q
  rw [zQ, ← map_mul, ← map_mul, mem_center_iff.mp H.ιz_mem_center g]

theorem zQ_pow : H.zQ ^ p = 1 := by
  rw [zQ, ← map_pow, H.ι_pow, 𝔇.p_zA, H.S.ι_zero, map_one]

theorem zQ_ne_one : H.zQ ≠ 1 := by
  rw [zQ, Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact H.ιz_notMem_N

theorem orderOf_zQ : orderOf H.zQ = p := orderOf_eq_prime H.zQ_pow H.zQ_ne_one

theorem zQ_zpow (m : ℤ) : H.mkQ (H.S.ι (ofAdd (m • 𝔇.zA))) = H.zQ ^ m := by
  rw [zQ, ← map_zpow, ← map_zpow, ofAdd_zsmul]

theorem πt_surjective (hgen : closure (x '' Set.Iio d) = ⊤) : Function.Surjective H.πt := by
  have hr : H.πt.range = ⊤ := by
    rw [eq_top_iff, ← hgen, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨_, H.πt_X hj⟩
  intro g
  have hg : g ∈ H.πt.range := by rw [hr]; exact mem_top g
  exact hg

theorem πQ_surjective (hgen : closure (x '' Set.Iio d) = ⊤) : Function.Surjective H.πQ := by
  intro g
  obtain ⟨g', rfl⟩ := H.πt_surjective hgen g
  exact ⟨H.mkQ g', rfl⟩

theorem zpow_eq_pow_val {g : P} (hg : g ^ p = 1) (n : ℤ) : g ^ n = g ^ ((n : ZMod p).val) := by
  rw [← zpow_natCast, ZMod.val_intCast, Int.emod_def, zpow_sub, zpow_mul, zpow_natCast, hg,
    one_zpow, inv_one, mul_one]

theorem list_prod_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

/-- `x_0, …, x_{d-1}` are independent in `P/γ₂(P)`. -/
theorem dvd_of_mem_lcs1 (hgen : closure (x '' Set.Iio d) = ⊤)
    (hcard : Nat.card (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 1) = p ^ d)
    (hxp : ∀ i < d, x i ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (s : ℕ → ℤ)
    (h : ((List.range d).map fun j => x j ^ s j).prod ∈ (⊤ : Subgroup P).lowerCentralSeries 1) :
    ∀ j < d, (p : ℤ) ∣ s j := by
  have hof : ∀ g ∈ (⊤ : Subgroup P).lowerCentralSeries 1, Abelianization.of g = 1 := fun g hg =>
    (QuotientGroup.eq_one_iff g).mpr hg
  have hp1 : ∀ i < d, Abelianization.of (x i) ^ p = 1 := fun i hi => by
    rw [← map_pow]; exact hof _ (hxp i hi)
  let Θ : Multiplicative (Fin d → ZMod p) →* Abelianization P :=
    { toFun := fun k => ∏ i : Fin d, Abelianization.of (x i) ^ (toAdd k i).val
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [toAdd_mul, Pi.add_apply, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => (pow_val_add (hp1 i i.2) _ _).symm }
  have hΘ_single : ∀ i : Fin d, Θ (ofAdd (Pi.single i 1)) = Abelianization.of (x i) := fun i => by
    show ∏ l : Fin d, _ = _
    rw [Finset.prod_eq_single i]
    · simp [ZMod.val_one]
    · intro l _ hl; simp [Pi.single_eq_of_ne hl]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsurj : Function.Surjective Θ := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ a
    have hle : closure (x '' Set.Iio d) ≤ Θ.range.comap Abelianization.of := by
      rw [closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨_, hΘ_single ⟨j, hj⟩⟩
    rw [hgen] at hle
    exact hle (mem_top g)
  have hcardA : Nat.card (Abelianization P) = p ^ d := hcard
  have hinj : Function.Injective Θ := by
    refine ((Nat.bijective_iff_surjective_and_card Θ).mpr ⟨hsurj, ?_⟩).1
    rw [hcardA, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have h1 : Θ (ofAdd fun i => ((s i : ℤ) : ZMod p)) = 1 := by
    show ∏ i : Fin d, _ = _
    have e := hof _ h
    rw [map_list_prod, List.map_map] at e
    rw [← e, Function.comp_def]
    simp only [map_zpow]
    rw [list_prod_range, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := hp1 i i.2
    rw [toAdd_ofAdd]
    exact (zpow_eq_pow_val this (s i)).symm
  intro j hj
  have := congrArg (fun k : Multiplicative (Fin d → ZMod p) => toAdd k ⟨j, hj⟩)
    (hinj (h1.trans (map_one Θ).symm))
  exact dvd_of_cast (by simpa using this)

/-- **The kernel of `Q → P` is `⟨z⟩`.** -/
theorem ker_πQ (hgen : closure (x '' Set.Iio d) = ⊤)
    (hcard : Nat.card (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 1) = p ^ d)
    (hu1 : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1)
    (hw1 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (huc : u ∉ center P)
    (hv2 : v ∉ (⊤ : Subgroup P).lowerCentralSeries 2) (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2)
    (hwo : orderOf w = p) : H.πQ.ker = zpowers H.zQ := by
  have hxp : ∀ i < d, x i ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := fun i hi => by
    rw [H.hpow i hi]; exact mul_mem (pow_mem hv1 _) (pow_mem hw1 _)
  apply le_antisymm
  · intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H.N q
    rw [MonoidHom.mem_ker] at hq
    change H.πt g = 1 at hq
    obtain ⟨a, s, hg⟩ := H.S.nf g
    -- the `x`-exponents are divisible by `p`
    have hLP : H.πt ((List.range d).map fun j => H.S.X j ^ s j).prod =
        ((List.range d).map fun j => x j ^ s j).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      refine List.map_congr_left fun j hj => ?_
      simp [H.πt_X (List.mem_range.mp hj)]
    have hdvd : ∀ j < d, (p : ℤ) ∣ s j := by
      apply dvd_of_mem_lcs1 (x := x) hgen hcard hxp s
      rw [hg, map_mul, hLP, πt_ι] at hq
      rw [eq_inv_of_mul_eq_one_right hq]
      exact inv_mem (H.ψA_mem _ hu1 hv1 hw1)
    -- so `g ∈ ι(A) N`
    have hX : ∀ l : List ℕ, (∀ j ∈ l, j < d) →
        H.mkQ ((l.map fun j => H.S.X j ^ s j).prod) ∈ (H.mkQ.comp H.S.ι).range := by
      intro l hl
      induction l with
      | nil => simp
      | cons j l ih =>
        simp only [List.map_cons, List.prod_cons, map_mul]
        refine mul_mem ?_ (ih fun i hi => hl i (List.mem_cons_of_mem _ hi))
        have hj := hl j List.mem_cons_self
        obtain ⟨c, hc⟩ := hdvd j hj
        have hXp : H.S.X j ^ (p : ℤ) = H.y j * H.S.ι (ofAdd (𝔇.πA j)) := by
          rw [y, zpow_natCast, inv_mul_cancel_right]
        have hcomm : Commute (H.y j) (H.S.ι (ofAdd (𝔇.πA j))) :=
          (mem_center_iff.mp (H.y_mem_center hj) _).symm
        have hy1 : H.mkQ (H.y j) = 1 := (QuotientGroup.eq_one_iff _).mpr (H.y_mem_N hj)
        refine ⟨ofAdd (c • 𝔇.πA j), ?_⟩
        show H.mkQ (H.S.ι (ofAdd (c • 𝔇.πA j))) = H.mkQ (H.S.X j ^ s j)
        rw [hc, zpow_mul, hXp, hcomm.mul_zpow, map_mul, map_zpow H.mkQ (H.y j), hy1, one_zpow,
          one_mul, ofAdd_zsmul, map_zpow, map_zpow]
    obtain ⟨a', ha'⟩ : H.mkQ g ∈ (H.mkQ.comp H.S.ι).range := by
      rw [hg, map_mul]
      exact mul_mem ⟨_, rfl⟩ (hX _ fun j hj => List.mem_range.mp hj)
    have hψ : H.ψA a' = 1 := by
      have : H.πQ (H.mkQ (H.S.ι a')) = 1 := by
        rw [show H.mkQ (H.S.ι a') = H.mkQ g from ha']; exact hq
      rw [← H.πt_ι]; exact this
    obtain ⟨a', rfl⟩ := ofAdd.surjective a'
    induction a' using QuotientAddGroup.induction_on with
    | H n =>
      rw [ψA_mk, ← mul_assoc, zpow_eq_pow_val H.hu, zpow_eq_pow_val H.hv,
        zpow_eq_pow_val H.hw] at hψ
      obtain ⟨h1, h2, h3⟩ := indep H.hu huc H.hvc hv2 hw2 H.hwc hwo H.hv hψ
      rw [← ha', MonoidHom.comp_apply,
        𝔇.eq_zsmul_zA (dvd_of_cast h1) (dvd_of_cast h2) (dvd_of_cast h3), zQ_zpow]
      exact zpow_mem (mem_zpowers _) _
  · rw [zpowers_le, MonoidHom.mem_ker, zQ, πQ_mk, πt_ι, Data.zA, ψA_mk]
    simp

/-- **`γ₄(Q) ≠ 1`**: `[[u, x_k], x_k] = z^{f_k²}` with `f_k ≠ 0`. -/
theorem lcs3_ne_bot (hgen : closure (x '' Set.Iio d) = ⊤)
    (hcard : Nat.card (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 1) = p ^ d)
    (hu1 : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1)
    (hw1 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (huc : u ∉ center P)
    (hv2 : v ∉ (⊤ : Subgroup P).lowerCentralSeries 2) (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2)
    (hwo : orderOf w = p) : (⊤ : Subgroup H.Q).lowerCentralSeries 3 ≠ ⊥ := by
  have hker := H.ker_πQ hgen hcard hu1 hv1 hw1 huc hv2 hw2 hwo
  -- some `f_k ≠ 0`
  obtain ⟨k, hk, hfk⟩ : ∃ k < d, 𝔇.f k ≠ 0 := by
    by_contra h
    push Not at h
    apply huc
    rw [mem_center_iff]
    intro g
    have hle : closure (x '' Set.Iio d) ≤ Subgroup.centralizer {u} := by
      rw [closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have := H.hf j hj
      rw [h j hj, ZMod.val_zero, pow_zero] at this
      exact (pc_eq_one_iff.mp this).symm
    rw [hgen] at hle
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (mem_top g)))
  set uA : 𝔇.A := ((((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) : V4) : 𝔇.A)
  set Xk := H.mkQ (H.S.X k)
  have hu : H.πQ (H.mkQ (H.S.ι (ofAdd uA))) = u := by
    rw [πQ_mk, πt_ι, ψA_mk]; simp
  obtain ⟨g, hg, hgu⟩ : ∃ g ∈ (⊤ : Subgroup H.Q).lowerCentralSeries 1, H.πQ g = u := by
    rw [← lcs_map_of_surjective (H.πQ_surjective hgen) 1] at hu1
    exact Subgroup.mem_map.mp hu1
  obtain ⟨m, hm⟩ : g⁻¹ * H.mkQ (H.S.ι (ofAdd uA)) ∈ zpowers H.zQ := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hgu, hu, inv_mul_cancel]
  have hm' : H.zQ ^ m = g⁻¹ * H.mkQ (H.S.ι (ofAdd uA)) := hm
  have hu' : H.mkQ (H.S.ι (ofAdd uA)) = g * H.zQ ^ m := by
    rw [hm', mul_inv_cancel_left]
  have hpc : ∀ c : 𝔇.A, pc (H.mkQ (H.S.ι (ofAdd c))) Xk = H.mkQ (H.S.ι (ofAdd (𝔇.D k c))) := by
    intro c
    rw [← H.pc_ι hk]
    simp only [pc, map_mul, map_inv]
    rfl
  have h3 : pc (H.mkQ (H.S.ι (ofAdd uA))) Xk ∈ (⊤ : Subgroup H.Q).lowerCentralSeries 2 := by
    rw [hu', pc_mul_central (zpow_mem H.zQ_mem_center _)]
    exact pc_mem (by norm_num) hg (mem_lcs_zero _)
  have h4 : pc (pc (H.mkQ (H.S.ι (ofAdd uA))) Xk) Xk ∈ (⊤ : Subgroup H.Q).lowerCentralSeries 3 :=
    pc_mem (by norm_num) h3 (mem_lcs_zero _)
  rw [hpc, hpc] at h4
  have hDD : 𝔇.D k (𝔇.D k uA) = (Z (𝔇.f k) * Z (𝔇.f k)) • 𝔇.zA := by
    rw [Data.D_mk, Data.D_mk, Data.zA, ← QuotientAddGroup.mk_zsmul]
    congr 1
    simp [Data.Dt_apply]
  rw [hDD, zQ_zpow] at h4
  intro hbot
  rw [hbot, mem_bot] at h4
  have hdvd : ((p : ℤ)) ∣ Z (𝔇.f k) * Z (𝔇.f k) := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rwa [H.orderOf_zQ] at this
  rcases (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_or_dvd hdvd with h | h <;>
    exact hfk (by rw [← Z_cast (𝔇.f k)]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)

include H in
/-- **The extension.** -/
theorem exists_extension (hgen : closure (x '' Set.Iio d) = ⊤)
    (hcard : Nat.card (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 1) = p ^ d)
    (hu1 : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1)
    (hw1 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (huc : u ∉ center P)
    (hv2 : v ∉ (⊤ : Subgroup P).lowerCentralSeries 2) (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2)
    (hwo : orderOf w = p) :
    ∃ (Q : Type) (_ : Group Q) (π : Q →* P) (z : Q), Function.Surjective π ∧ π.ker = zpowers z ∧
      z ∈ center Q ∧ orderOf z = p ∧ (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ :=
  ⟨H.Q, inferInstance, H.πQ, H.zQ, H.πQ_surjective hgen,
    H.ker_πQ hgen hcard hu1 hv1 hw1 huc hv2 hw2 hwo, H.zQ_mem_center, H.orderOf_zQ,
    H.lcs3_ne_bot hgen hcard hu1 hv1 hw1 huc hv2 hw2 hwo⟩

end Hyp

end Group

end NonterminalSuff

section

open Subgroup Nonterminal NonterminalSuff
open scoped commutatorElement

/-- **Theorem 6.12, "⇐"** (Appendix, Step 5). Let `p` be an odd prime and `P` a group with
`γ₄(P) = 1`, `|γ₃(P)| = p`, `γ₂(P)` of exponent `p` (N2), generated by `x_1, …, x_d` with
`|P/γ₂(P)| = p^d`. Let `w` generate `γ₃(P)`, `v ∈ Z(P) ∩ γ₂(P) \ γ₃(P)`, `u ∈ γ₂(P) \ Z(P)`, with
`[x_i,x_j] = u^{ω₁(i,j)} v^{ω₂(i,j)} w^{ω₃(i,j)}`, `x_i^p = v^{α_i} w^{β_i}` and `[u,x_i] = w^{f_i}`
(`[a,b] = a⁻¹b⁻¹ab`). If the system (E)+(J) has a solution with `c = 1`, then `P` is nonterminal in
the sense of Lemma C.1: there are a group `Q` and `π : Q →* P` onto with `ker π = ⟨z⟩`, `z`
central of order `p`, and `γ₄(Q) ≠ 1`. (`P` is taken in `Type`, and so is `Q`.) -/
theorem nonterminal_sufficient {P : Type} [Group P] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h4 : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥)
    (h3 : Nat.card ((⊤ : Subgroup P).lowerCentralSeries 2) = p)
    (hN2 : ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, a ^ p = 1)
    {d : ℕ} (x : Fin d → P) (hgen : closure (Set.range x) = ⊤)
    (hcard : Nat.card (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 1) = p ^ d)
    {u v w : P} {ω₁ ω₂ ω₃ : Fin d → Fin d → ZMod p} {α β f : Fin d → ZMod p}
    (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hvc : v ∈ center P)
    (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hv2 : v ∉ (⊤ : Subgroup P).lowerCentralSeries 2)
    (hu1 : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (huc : u ∉ center P)
    (hω : ∀ i j, (x i)⁻¹ * (x j)⁻¹ * x i * x j =
      u ^ (ω₁ i j).val * v ^ (ω₂ i j).val * w ^ (ω₃ i j).val)
    (hpow : ∀ i, x i ^ p = v ^ (α i).val * w ^ (β i).val)
    (hf : ∀ i, u⁻¹ * (x i)⁻¹ * u * x i = w ^ (f i).val)
    {μu μv : ZMod p} {η σ : Fin d → ZMod p} (hsol : SystemEJ ω₁ ω₂ ω₃ α β f 1 μu μv η σ) :
    ∃ (Q : Type) (_ : Group Q) (π : Q →* P) (z : Q), Function.Surjective π ∧ π.ker = zpowers z ∧
      z ∈ center Q ∧ orderOf z = p ∧ (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥ := by
  have hwc : w ∈ center P := by
    rw [mem_center_iff]; intro g
    have h : ⁅w, g⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 3 :=
      commutator_mem_lcs (by norm_num) hw2 (mem_lcs_zero g)
    rw [h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  have hwo : orderOf w = p := (orderOf_eq_of_card h3 hw2 hw1).1
  have hw1' : w ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := lcs_mem_of_le (by norm_num) hw2
  have hu := hN2 u hu1
  have hv := hN2 v hv1
  have hw := hN2 w hw1'
  have huv : Commute u v := mem_center_iff.mp hvc u
  have huw : Commute u w := mem_center_iff.mp hwc u
  have hvw : Commute v w := mem_center_iff.mp hwc v
  -- the `ω_r` are alternating
  have hanti : ∀ i j, ω₁ j i = -ω₁ i j ∧ ω₂ j i = -ω₂ i j ∧ ω₃ j i = -ω₃ i j := by
    intro i j
    have e : (x j)⁻¹ * (x i)⁻¹ * x j * x i = ((x i)⁻¹ * (x j)⁻¹ * x i * x j)⁻¹ := by group
    rw [hω j i, hω i j] at e
    have h1 := mul_eq_one_iff_eq_inv.mpr e
    rw [mul3_pow_val hu hv hw huv huw hvw] at h1
    obtain ⟨h₁, h₂, h₃⟩ := indep hu huc hvc hv2 hw2 hwc hwo hv h1
    exact ⟨eq_neg_of_add_eq_zero_left h₁, eq_neg_of_add_eq_zero_left h₂,
      eq_neg_of_add_eq_zero_left h₃⟩
  -- the `w`-component of the Jacobi identity in `P`
  have hcomm1 : ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
      ∀ b ∈ (⊤ : Subgroup P).lowerCentralSeries 1, a * b = b * a := by
    intro a ha b hb
    have h : ⁅a, b⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 3 := commutator_mem_lcs (by norm_num) ha hb
    rw [h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hpcw : ∀ a b c : Fin d,
      pc (pc (x a) (x b)) (x c) = w ^ (f c * ω₁ a b).val := by
    intro a b c
    have hpc : pc (x a) (x b) = u ^ (ω₁ a b).val * v ^ (ω₂ a b).val * w ^ (ω₃ a b).val := hω a b
    have hux : pc u (x c) = w ^ (f c).val := hf c
    rw [hpc, pc_mul_central (pow_mem hwc _), pc_mul_central (pow_mem hvc _),
      pc_pow (by rw [hux]; exact mem_center_iff.mp (pow_mem hwc _) u), hux, pow_val_pow hw,
      ZMod.natCast_zmod_val]
  have hjw : ∀ a b c : Fin d, f c * ω₁ a b + f a * ω₁ b c + f b * ω₁ c a = 0 := by
    intro a b c
    have h := pc_jacobi (A := (⊤ : Subgroup P).lowerCentralSeries 1) hcomm1 pc_mem_one (x a) (x b) (x c)
    rw [hpcw, hpcw, hpcw, pow_val_add hw, pow_val_add hw] at h
    have := pow_val_eq_one hwo h
    linear_combination this
  -- the data, indexed by `ℕ`
  let e1 : (Fin d → ZMod p) → ℕ → ZMod p := fun g j => if h : j < d then g ⟨j, h⟩ else 0
  let e2 : (Fin d → Fin d → ZMod p) → ℕ → ℕ → ZMod p := fun g i j =>
    if h : i < d ∧ j < d then g ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  let xN : ℕ → P := fun j => if h : j < d then x ⟨j, h⟩ else 1
  let 𝔇 : Data p := ⟨μu, μv, e1 f, e1 σ, e1 η, e1 α, e1 β, e2 ω₁, e2 ω₂, e2 ω₃⟩
  have he1 : ∀ (g : Fin d → ZMod p) (j : ℕ) (hj : j < d), e1 g j = g ⟨j, hj⟩ :=
    fun g j hj => dif_pos hj
  have he2 : ∀ (g : Fin d → Fin d → ZMod p) (i j : ℕ) (hi : i < d) (hj : j < d),
      e2 g i j = g ⟨i, hi⟩ ⟨j, hj⟩ := fun g i j hi hj => dif_pos ⟨hi, hj⟩
  have hxN : ∀ (j : ℕ) (hj : j < d), xN j = x ⟨j, hj⟩ := fun j hj => dif_pos hj
  have H : Hyp 𝔇 d xN u v w :=
    { hp2 := hp2, hvc := hvc, hwc := hwc, hu := hu, hv := hv, hw := hw
      hf := fun k hk => by
        show u⁻¹ * (xN k)⁻¹ * u * xN k = w ^ (e1 f k).val
        rw [hxN k hk, he1 f k hk]; exact hf _
      hω := fun j i hj hi => by
        show (xN j)⁻¹ * (xN i)⁻¹ * xN j * xN i =
          u ^ (e2 ω₁ j i).val * v ^ (e2 ω₂ j i).val * w ^ (e2 ω₃ j i).val
        rw [hxN j hj, hxN i hi, he2 _ j i hj hi, he2 _ j i hj hi, he2 _ j i hj hi]; exact hω _ _
      hpow := fun i hi => by
        show xN i ^ p = v ^ (e1 α i).val * w ^ (e1 β i).val
        rw [hxN i hi, he1 α i hi, he1 β i hi]; exact hpow _
      hJw := fun j i k hji hik hkd => by
        show e1 f i * e2 ω₁ j k - e1 f j * e2 ω₁ i k - e1 f k * e2 ω₁ j i = 0
        have hid := hik.trans hkd
        have hjd := hji.trans hid
        rw [he1 f i hid, he1 f j hjd, he1 f k hkd, he2 _ j k hjd hkd, he2 _ i k hid hkd,
          he2 _ j i hjd hid]
        have := hjw ⟨j, hjd⟩ ⟨i, hid⟩ ⟨k, hkd⟩
        rw [(hanti ⟨j, hjd⟩ ⟨k, hkd⟩).1] at this
        linear_combination -this
      hJz := fun j i k hji hik hkd => by
        show (e1 σ i * e2 ω₁ j k + e1 η i * e2 ω₂ j k + e1 f i * e2 ω₃ j k) -
          (e1 σ j * e2 ω₁ i k + e1 η j * e2 ω₂ i k + e1 f j * e2 ω₃ i k) -
          (e1 σ k * e2 ω₁ j i + e1 η k * e2 ω₂ j i + e1 f k * e2 ω₃ j i) = 0
        have hid := hik.trans hkd
        have hjd := hji.trans hid
        simp only [he1 _ i hid, he1 _ j hjd, he1 _ k hkd, he2 _ j k hjd hkd, he2 _ i k hid hkd,
          he2 _ j i hjd hid]
        have := hsol.2 ⟨j, hjd⟩ ⟨i, hid⟩ ⟨k, hkd⟩ hji hik
        obtain ⟨a1, a2, a3⟩ := hanti ⟨j, hjd⟩ ⟨k, hkd⟩
        rw [a1, a2, a3] at this
        linear_combination -this
      hE := fun i j hi hj => by
        show μu * e2 ω₁ i j + μv * e2 ω₂ i j + (if p = 3 then 1 else 0) * e1 f i ^ 2 * e2 ω₁ i j -
          e1 η j * e1 α i - e1 f j * e1 β i = 0
        simp only [he1 _ i hi, he1 _ j hj, he2 _ i j hi hj]
        have := hsol.1 ⟨j, hj⟩ ⟨i, hi⟩
        obtain ⟨a1, a2, -⟩ := hanti ⟨i, hi⟩ ⟨j, hj⟩
        rw [a1, a2] at this
        linear_combination -this
      hanti := fun i j hi hj => by
        show e2 ω₁ j i = -e2 ω₁ i j ∧ e2 ω₂ j i = -e2 ω₂ i j ∧ e2 ω₃ j i = -e2 ω₃ i j
        simp only [he2 _ j i hj hi, he2 _ i j hi hj]
        exact hanti _ _ }
  have hgen' : closure (xN '' Set.Iio d) = ⊤ := by
    rw [← hgen]
    congr 1
    ext g
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, (hxN j hj).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, i.2, hxN i i.2⟩
  exact H.exists_extension hgen' hcard hu1 hv1 hw1' huc hv2 hw2 hwo

/-- **Theorem 6.12** (both directions, for a normal form of `P`). Let `p` be an odd prime, `P` of
type `(d, 2, 1)` with `P/γ₂(P)` elementary abelian, generated by `x_1, …, x_d`, with `γ₂(P)` of
exponent `p` (N2), and let `u, v, w` and the exponents be a normal form as in the theorem. Then `P`
is nonterminal (in the sense of Lemma C.1) if and only if (E)+(J) has a solution with `c = 1`.
(N1) and (N3) are part of the normal form here (`v, w` central, `x_i^p ∈ ⟨v, w⟩`); that they are
necessary is `nonterminal_necessary`. -/
theorem nonterminal_iff {P : Type} [Group P] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h4 : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥)
    (h2 : ((⊤ : Subgroup P).lowerCentralSeries 2).relIndex ((⊤ : Subgroup P).lowerCentralSeries 1) = p ^ 2)
    (h3 : Nat.card ((⊤ : Subgroup P).lowerCentralSeries 2) = p)
    (hel : ∀ x : P, x ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 1)
    (hN2 : ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, a ^ p = 1)
    {d : ℕ} (x : Fin d → P) (hgen : closure (Set.range x) = ⊤)
    (hcard : Nat.card (P ⧸ (⊤ : Subgroup P).lowerCentralSeries 1) = p ^ d)
    {u v w : P} {ω₁ ω₂ ω₃ : Fin d → Fin d → ZMod p} {α β f : Fin d → ZMod p}
    (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hvc : v ∈ center P)
    (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hv2 : v ∉ (⊤ : Subgroup P).lowerCentralSeries 2)
    (hu1 : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (huc : u ∉ center P)
    (hω : ∀ i j, (x i)⁻¹ * (x j)⁻¹ * x i * x j =
      u ^ (ω₁ i j).val * v ^ (ω₂ i j).val * w ^ (ω₃ i j).val)
    (hpow : ∀ i, x i ^ p = v ^ (α i).val * w ^ (β i).val)
    (hf : ∀ i, u⁻¹ * (x i)⁻¹ * u * x i = w ^ (f i).val) :
    (∃ (Q : Type) (_ : Group Q) (π : Q →* P) (z : Q), Function.Surjective π ∧ π.ker = zpowers z ∧
      z ∈ center Q ∧ orderOf z = p ∧ (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥) ↔
    ∃ μu μv : ZMod p, ∃ η σ : Fin d → ZMod p, SystemEJ ω₁ ω₂ ω₃ α β f 1 μu μv η σ := by
  constructor
  · rintro ⟨Q, _, π, z, hπ, hker, hz, hzo, hQ⟩
    exact (nonterminal_necessary hp2 h4 h2 h3 hel π hπ z hz hzo hker hQ).2.2.2 d x u v w ω₁ ω₂ ω₃
      α β f hw2 hw1 hvc hv1 hv2 hu1 huc hω hpow hf
  · rintro ⟨μu, μv, η, σ, hsol⟩
    exact nonterminal_sufficient hp2 h4 h3 hN2 x hgen hcard hw2 hw1 hvc hv1 hv2 hu1 huc hω hpow hf
      hsol

end

end GroupDimension
