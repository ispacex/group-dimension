import GroupDimension.CentralD8

/-!
# Adjoining a central square root (the core of Proposition 5.8(2) of the D5 paper)

Let `K` be a group, `H ≤ K`, and `r ∈ K` central with `K = H ⊔ Hr`, so `s = r² ∈ H`. Let
`g ∈ H` (not necessarily central) and `c = g⁻² s`. If `c^(2^j) - 1 ∈ Δ(H)^(j+2)` for all
`j ≥ 0`, then

  `ℤ[H] ∩ Δ(K)^n = Δ(H)^n` for all `n`, and `D_n(K) = D_n(H)` for `n ≥ 2`.

The paper projects `u₀ + u₁ r ↦ u₀ + u₁ g` and checks `q((r - 1)^i) ∈ Δ(H)^i` through the
recurrence `e_{b+2} = τ e_b - 2 e_{b+1}`, `τ = c - 1`. Here the same projection is handled as in
`CentralD8`: in the coordinates `X(u₀ + u₁ r) = u₀ + u₁ g`, `Y(u₀ + u₁ r) = u₁`, left
multiplication by `r` is `(x, y) ↦ (x g + y g² τ, x - y g)`, and
`{u | X u ∈ Δ(H)^n, Y u ∈ B_n}` is a left ideal containing `Δ(K)^n`. The input is
`2^m τ ∈ Δ(H)^(m+2)`, which follows from the hypothesis and
`2(c^(2^j) - 1) = (c^(2^(j+1)) - 1) - (c^(2^j) - 1)²`.

MATH-206; the statement is `D_n_eq_of_sqrt`.
-/

namespace GroupDimension

open MonoidAlgebra

/-- The data: `K = H ⊔ Hr` with `r` central and `g ∈ H`. -/
structure SqrtData (K : Type*) [Group K] where
  H : Subgroup K
  r : K
  g : H
  central : ∀ x : K, r * x = x * r
  sq_mem : r * r ∈ H
  r_nmem : r ∉ H
  gen : ∀ k : K, ∃ h ∈ H, k = h ∨ k = h * r

namespace SqrtData

variable {K : Type*} [Group K] (S : SqrtData K)

/-- `s = r²`. -/
def s : S.H := ⟨S.r * S.r, S.sq_mem⟩

/-- `c = g⁻² s`. -/
def c : S.H := S.g⁻¹ * S.g⁻¹ * S.s

/-- `τ = c - 1`. -/
noncomputable abbrev τ : MonoidAlgebra ℤ S.H := of ℤ S.H S.c - 1

/-! ## The retraction on elements -/

open Classical in
/-- `ρ(h) = h`, `ρ(h r) = h`. -/
noncomputable def rho (k : K) : K := if k ∈ S.H then k else k * S.r⁻¹

variable {S}

theorem rho_h {h : K} (hh : h ∈ S.H) : S.rho h = h := by simp [rho, hh]

theorem hr_nmem {h : K} (hh : h ∈ S.H) : h * S.r ∉ S.H := by
  rw [Subgroup.mul_mem_cancel_left _ hh]; exact S.r_nmem

theorem rho_hr {h : K} (hh : h ∈ S.H) : S.rho (h * S.r) = h := by
  simp [rho, hr_nmem hh]

theorem rho_mem (k : K) : S.rho k ∈ S.H := by
  obtain ⟨h, hh, hk | hk⟩ := S.gen k <;> subst k
  · rw [rho_h hh]; exact hh
  · rw [rho_hr hh]; exact hh

variable (S) in
/-- The retraction `K → H`. -/
noncomputable def ret (k : K) : S.H := ⟨S.rho k, rho_mem k⟩

theorem ret_h {h : K} (hh : h ∈ S.H) : S.ret h = ⟨h, hh⟩ := Subtype.ext (rho_h hh)
theorem ret_hr {h : K} (hh : h ∈ S.H) : S.ret (h * S.r) = ⟨h, hh⟩ := Subtype.ext (rho_hr hh)

open Classical in
variable (S) in
/-- `X(h) = h`, `X(h r) = h g`. -/
noncomputable def xv (k : K) : MonoidAlgebra ℤ S.H :=
  if k ∈ S.H then of ℤ S.H (S.ret k) else of ℤ S.H (S.ret k) * of ℤ S.H S.g

open Classical in
variable (S) in
/-- `Y(h) = 0`, `Y(h r) = h`. -/
noncomputable def yv (k : K) : MonoidAlgebra ℤ S.H := if k ∈ S.H then 0 else of ℤ S.H (S.ret k)

theorem xv_h {h : K} (hh : h ∈ S.H) : S.xv h = of ℤ S.H ⟨h, hh⟩ := by simp [xv, hh, ret_h hh]
theorem xv_hr {h : K} (hh : h ∈ S.H) :
    S.xv (h * S.r) = of ℤ S.H ⟨h, hh⟩ * of ℤ S.H S.g := by simp [xv, hr_nmem hh, ret_hr hh]
theorem yv_h {h : K} (hh : h ∈ S.H) : S.yv h = 0 := by simp [yv, hh]
theorem yv_hr {h : K} (hh : h ∈ S.H) : S.yv (h * S.r) = of ℤ S.H ⟨h, hh⟩ := by
  simp [yv, hr_nmem hh, ret_hr hh]

theorem of_mk_mul {h k : K} (hh : h ∈ S.H) (hk : k ∈ S.H) :
    of ℤ S.H ⟨k, hk⟩ * of ℤ S.H ⟨h, hh⟩ = of ℤ S.H ⟨k * h, S.H.mul_mem hk hh⟩ := by
  rw [← _root_.map_mul]; rfl

theorem mul_h {k : K} (hk : k ∈ S.H) (x : K) :
    S.xv (k * x) = of ℤ S.H ⟨k, hk⟩ * S.xv x ∧ S.yv (k * x) = of ℤ S.H ⟨k, hk⟩ * S.yv x := by
  have hkh : ∀ {h}, h ∈ S.H → k * h ∈ S.H := fun hh => S.H.mul_mem hk hh
  obtain ⟨h, hh, hx | hx⟩ := S.gen x <;> subst x
  · rw [xv_h (hkh hh), xv_h hh, yv_h (hkh hh), yv_h hh, of_mk_mul hh hk, mul_zero]
    exact ⟨rfl, rfl⟩
  · rw [← mul_assoc, xv_hr (hkh hh), xv_hr hh, yv_hr (hkh hh), yv_hr hh, ← mul_assoc,
      of_mk_mul hh hk]
    exact ⟨rfl, rfl⟩

/-- `g² τ = s - g²` in `ℤ[H]`. -/
theorem gg_tau : of ℤ S.H S.g * of ℤ S.H S.g * S.τ =
    of ℤ S.H S.s - of ℤ S.H S.g * of ℤ S.H S.g := by
  have e : S.g * S.g * S.c = S.s := by simp only [c]; group
  rw [τ, mul_sub, mul_one, ← _root_.map_mul, ← _root_.map_mul, e]

theorem mul_r (x : K) :
    S.xv (S.r * x) = S.xv x * of ℤ S.H S.g + S.yv x * (of ℤ S.H S.g * of ℤ S.H S.g * S.τ) ∧
      S.yv (S.r * x) = S.xv x - S.yv x * of ℤ S.H S.g := by
  obtain ⟨h, hh, hx | hx⟩ := S.gen x <;> subst x
  · rw [S.central h, xv_hr hh, xv_h hh, yv_hr hh, yv_h hh]
    constructor <;> simp
  · have hs : h * (S.r * S.r) ∈ S.H := S.H.mul_mem hh S.sq_mem
    have e : S.r * (h * S.r) = h * (S.r * S.r) := by rw [← mul_assoc, S.central h, mul_assoc]
    have e' : of ℤ S.H ⟨h * (S.r * S.r), hs⟩ = of ℤ S.H ⟨h, hh⟩ * of ℤ S.H S.s := by
      rw [← _root_.map_mul]; rfl
    rw [e, xv_h hs, yv_h hs, xv_hr hh, yv_hr hh, gg_tau, e', sub_self]
    refine ⟨?_, rfl⟩
    noncomm_ring

/-! ## The coordinates `X, Y : ℤ[K] → ℤ[H]` -/

variable (S)

noncomputable def X : MonoidAlgebra ℤ K →+ MonoidAlgebra ℤ S.H :=
  MonoidAlgebra.liftNC (Int.castAddHom _) S.xv

noncomputable def Y : MonoidAlgebra ℤ K →+ MonoidAlgebra ℤ S.H :=
  MonoidAlgebra.liftNC (Int.castAddHom _) S.yv

theorem X_of (k : K) : S.X (of ℤ K k) = S.xv k := by
  simp [X, MonoidAlgebra.of_apply, MonoidAlgebra.liftNC_single]

theorem Y_of (k : K) : S.Y (of ℤ K k) = S.yv k := by
  simp [Y, MonoidAlgebra.of_apply, MonoidAlgebra.liftNC_single]

theorem X_mul_h {k : K} (hk : k ∈ S.H) (y : MonoidAlgebra ℤ K) :
    S.X (of ℤ K k * y) = of ℤ S.H ⟨k, hk⟩ * S.X y := by
  refine DihedralData.ext_of (f₁ := (S.X).comp (AddMonoidHom.mulLeft (of ℤ K k)))
    (f₂ := (AddMonoidHom.mulLeft (of ℤ S.H ⟨k, hk⟩)).comp S.X) (fun x => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← _root_.map_mul, X_of]
  exact (mul_h hk x).1

theorem Y_mul_h {k : K} (hk : k ∈ S.H) (y : MonoidAlgebra ℤ K) :
    S.Y (of ℤ K k * y) = of ℤ S.H ⟨k, hk⟩ * S.Y y := by
  refine DihedralData.ext_of (f₁ := (S.Y).comp (AddMonoidHom.mulLeft (of ℤ K k)))
    (f₂ := (AddMonoidHom.mulLeft (of ℤ S.H ⟨k, hk⟩)).comp S.Y) (fun x => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← _root_.map_mul, Y_of]
  exact (mul_h hk x).2

theorem X_mul_r (y : MonoidAlgebra ℤ K) :
    S.X (of ℤ K S.r * y) =
      S.X y * of ℤ S.H S.g + S.Y y * (of ℤ S.H S.g * of ℤ S.H S.g * S.τ) := by
  refine DihedralData.ext_of (f₁ := (S.X).comp (AddMonoidHom.mulLeft (of ℤ K S.r)))
    (f₂ := (AddMonoidHom.mulRight (of ℤ S.H S.g)).comp S.X +
      (AddMonoidHom.mulRight (of ℤ S.H S.g * of ℤ S.H S.g * S.τ)).comp S.Y) (fun x => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
    AddMonoidHom.add_apply, ← map_mul (of ℤ K), X_of, Y_of]
  exact (mul_r x).1

theorem Y_mul_r (y : MonoidAlgebra ℤ K) :
    S.Y (of ℤ K S.r * y) = S.X y - S.Y y * of ℤ S.H S.g := by
  refine DihedralData.ext_of (f₁ := (S.Y).comp (AddMonoidHom.mulLeft (of ℤ K S.r)))
    (f₂ := S.X - (AddMonoidHom.mulRight (of ℤ S.H S.g)).comp S.Y) (fun x => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
    AddMonoidHom.sub_apply, ← map_mul (of ℤ K), X_of, Y_of]
  exact (mul_r x).2

theorem X_iota (x : MonoidAlgebra ℤ S.H) : S.X (mapDomainRingHom ℤ S.H.subtype x) = x := by
  induction x using CentralRoot.induction_of with
  | h0 => rw [_root_.map_zero, _root_.map_zero]
  | hof h =>
    rw [mapDomainRingHom_of, X_of, Subgroup.coe_subtype, xv_h h.2]
  | hneg y hy => rw [_root_.map_neg, _root_.map_neg, hy]
  | hadd y z hy hz => rw [_root_.map_add, _root_.map_add, hy, hz]

/-! ## `2^m τ ∈ Δ(H)^(m+2)` -/

variable {S}

theorem two_pow_smul_c
    (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) (m : ℕ) :
    ∀ j : ℕ, (2 ^ m : ℕ) • (of ℤ S.H (S.c ^ 2 ^ j) - 1) ∈ augIdeal S.H ^ (m + j + 2) := by
  induction m with
  | zero => intro j; rw [pow_zero, one_smul, zero_add]; exact hc j
  | succ m ih =>
    intro j
    -- `2 (x - 1) = (x² - 1) - (x - 1)²` with `x = c^(2^j)`
    have hsq : of ℤ S.H (S.c ^ 2 ^ (j + 1)) =
        of ℤ S.H (S.c ^ 2 ^ j) * of ℤ S.H (S.c ^ 2 ^ j) := by
      rw [← _root_.map_mul, ← pow_add, ← two_mul, pow_succ, mul_comm]
    have e : (2 ^ (m + 1) : ℕ) • (of ℤ S.H (S.c ^ 2 ^ j) - 1) =
        (2 ^ m : ℕ) • (of ℤ S.H (S.c ^ 2 ^ (j + 1)) - 1) -
          ((2 ^ m : ℕ) • (of ℤ S.H (S.c ^ 2 ^ j) - 1)) * (of ℤ S.H (S.c ^ 2 ^ j) - 1) := by
      rw [hsq, smul_mul_assoc, ← smul_sub, pow_succ, mul_smul]
      congr 1
      rw [two_smul]; noncomm_ring
    rw [e]
    refine sub_mem ?_ ?_
    · have := ih (j + 1)
      rwa [show m + (j + 1) + 2 = m + 1 + j + 2 by omega] at this
    · exact Ideal.pow_le_pow_right (by omega) (mul_mem_augIdeal_pow (ih j) (hc j))

theorem two_pow_smul_tau
    (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) (m : ℕ) :
    (2 ^ m : ℕ) • S.τ ∈ augIdeal S.H ^ (m + 2) := by
  have := two_pow_smul_c hc m 0
  rwa [pow_zero, pow_one, add_zero] at this

/-! ## The left ideal `{u | X u ∈ Δ(H)^n, Y u ∈ B_n}` -/

variable (S)

/-- The left ideal `{u | X u ∈ Δ(H)^n, Y u ∈ B_n}` of `ℤ[K]`. -/
noncomputable def P (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2))
    (n : ℕ) : Ideal (MonoidAlgebra ℤ K) where
  carrier := {u | S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    simp only [Set.mem_setOf_eq, _root_.map_add] at *
    exact ⟨add_mem hy.1 hz.1, add_mem hy.2 hz.2⟩
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have hh : ∀ k (hk : k ∈ S.H) (u : MonoidAlgebra ℤ K),
        S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n →
        S.X (of ℤ K k * u) ∈ augIdeal S.H ^ n ∧ S.Y (of ℤ K k * u) ∈ Bfilt S.H n := by
      intro k hk u hu
      rw [S.X_mul_h hk, S.Y_mul_h hk]
      exact ⟨Ideal.mul_mem_left _ _ hu.1, Ideal.mul_mem_left _ _ hu.2⟩
    have hr : ∀ u : MonoidAlgebra ℤ K,
        S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n →
        S.X (of ℤ K S.r * u) ∈ augIdeal S.H ^ n ∧ S.Y (of ℤ K S.r * u) ∈ Bfilt S.H n := by
      intro u hu
      rw [S.X_mul_r, S.Y_mul_r]
      refine ⟨add_mem (Ideal.mul_mem_right _ _ hu.1) ?_,
        sub_mem (pow_le_Bfilt hu.1) (Bfilt_mul_right hu.2 _)⟩
      rw [← mul_assoc]
      exact Ideal.pow_le_pow_right (Nat.le_succ n)
        (Bfilt_mul_tau (two_pow_smul_tau hc) (Bfilt_mul_right hu.2 _))
    induction c using CentralRoot.induction_of with
    | h0 => simp
    | hof k =>
      obtain ⟨h, hh', hk | hk⟩ := S.gen k <;> subst k
      · exact hh h hh' u hu
      · rw [map_mul (of ℤ K) h S.r, mul_assoc]; exact hh h hh' _ (hr u hu)
    | hneg c hc =>
      simp only [neg_mul, _root_.map_neg]; exact ⟨neg_mem hc.1, neg_mem hc.2⟩
    | hadd c d hc hd =>
      simp only [add_mul, _root_.map_add]; exact ⟨add_mem hc.1 hd.1, add_mem hc.2 hd.2⟩

variable {S}

theorem sub_one_mul_mem_P
    (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) {n : ℕ}
    {u : MonoidAlgebra ℤ K} (hu : u ∈ S.P hc n) (k : K) :
    (of ℤ K k - 1) * u ∈ S.P hc (n + 1) := by
  have hu' : S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n := hu
  have hk : ∀ k (hk : k ∈ S.H), (of ℤ K k - 1) * u ∈ S.P hc (n + 1) := by
    intro k hk
    show S.X _ ∈ _ ∧ S.Y _ ∈ _
    rw [sub_mul, one_mul, _root_.map_sub, _root_.map_sub, S.X_mul_h hk, S.Y_mul_h hk,
      ← sub_one_mul, ← sub_one_mul]
    refine ⟨?_, Bfilt_mul_left hu'.2 _ (of_sub_one_mem_augIdeal _)⟩
    have := mul_mem_augIdeal_pow (i := 1)
      (by rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal (⟨k, hk⟩ : S.H)) hu'.1
    rwa [add_comm] at this
  have hr : (of ℤ K S.r - 1) * u ∈ S.P hc (n + 1) := by
    show S.X _ ∈ _ ∧ S.Y _ ∈ _
    rw [sub_mul, one_mul, _root_.map_sub, _root_.map_sub, S.X_mul_r, S.Y_mul_r]
    constructor
    · have e : S.X u * of ℤ S.H S.g + S.Y u * (of ℤ S.H S.g * of ℤ S.H S.g * S.τ) - S.X u =
          S.X u * (of ℤ S.H S.g - 1) + S.Y u * (of ℤ S.H S.g * of ℤ S.H S.g) * S.τ := by
        noncomm_ring
      rw [e]
      refine add_mem ?_ (Bfilt_mul_tau (two_pow_smul_tau hc) (Bfilt_mul_right hu'.2 _))
      exact mul_mem_augIdeal_pow hu'.1 (by rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal _)
    · have e : S.X u - S.Y u * of ℤ S.H S.g - S.Y u =
          S.X u - (S.Y u + S.Y u) - S.Y u * (of ℤ S.H S.g - 1) := by noncomm_ring
      rw [e]
      exact sub_mem (sub_mem (pow_le_Bfilt_succ hu'.1) (Bfilt_add_self hu'.2))
        (Bfilt_mul_aug hu'.2 (of_sub_one_mem_augIdeal _))
  obtain ⟨h, hh, hk' | hk'⟩ := S.gen k <;> subst k
  · exact hk h hh
  · have e : (of ℤ K (h * S.r) - 1) * u =
        of ℤ K h * ((of ℤ K S.r - 1) * u) + (of ℤ K h - 1) * u := by
      rw [_root_.map_mul]; noncomm_ring
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ hr) (hk h hh)

theorem augIdeal_pow_le_P
    (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) (n : ℕ) :
    augIdeal K ^ n ≤ S.P hc n := by
  induction n with
  | zero =>
    intro u _
    show S.X u ∈ _ ∧ S.Y u ∈ _
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact ⟨Submodule.mem_top,
      pow_le_Bfilt (by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial)⟩
  | succ n ih =>
    rw [augIdeal_pow_succ', Ideal.mul_le]
    intro x hx u hu
    refine CentralRoot.augIdeal_induction (p := fun x => x * u ∈ S.P hc (n + 1)) hx
      (by simp) (fun k => sub_one_mul_mem_P hc (ih hu) k)
      (fun y hy => by show (-y) * u ∈ _; rw [neg_mul]; exact neg_mem hy)
      (fun y z hy hz => by show (y + z) * u ∈ _; rw [add_mul]; exact add_mem hy hz)

theorem iota_mem_augIdeal_pow_iff
    (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) (n : ℕ)
    (x : MonoidAlgebra ℤ S.H) :
    mapDomainRingHom ℤ S.H.subtype x ∈ augIdeal K ^ n ↔ x ∈ augIdeal S.H ^ n := by
  constructor
  · intro hx
    have := (S.augIdeal_pow_le_P hc n hx).1
    rwa [S.X_iota] at this
  · exact mapDomain_mem_augIdeal_pow S.H.subtype n

theorem commutator_le : commutator K ≤ S.H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hone : ∀ z : K, 1 * z = z * 1 := fun z => by rw [one_mul, mul_one]
  have hform : ∀ k : K, ∃ h ∈ S.H, ∃ e : K, (∀ z, e * z = z * e) ∧ k = h * e := by
    intro k
    obtain ⟨h, hh, hk | hk⟩ := S.gen k
    · exact ⟨h, hh, 1, hone, by rw [hk, mul_one]⟩
    · exact ⟨h, hh, S.r, S.central, hk⟩
  obtain ⟨h1, hh1, e1, he1, rfl⟩ := hform x
  obtain ⟨h2, hh2, e2, he2, rfl⟩ := hform y
  rw [commutatorElement_def, comm_central h1 h2 e1 e2 he1 he2]
  exact S.H.mul_mem (S.H.mul_mem (S.H.mul_mem hh1 hh2) (S.H.inv_mem hh1)) (S.H.inv_mem hh2)

theorem D_eq (hc : ∀ j : ℕ, of ℤ S.H (S.c ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) (n : ℕ)
    (hn : 2 ≤ n) : D n K = (D n S.H).map S.H.subtype :=
  D_eq_of_mem_pow S.H S.commutator_le (fun n x => (S.iota_mem_augIdeal_pow_iff hc n x).mp) n hn

end SqrtData

/-- **Adjoining a central square root.** `K = H ⊔ Hr` with `r` central (so `r² ∈ H`), `g ∈ H`
not necessarily central, and `c = g⁻² r²` with `c^(2^j) - 1 ∈ Δ(H)^(j+2)` for all `j ≥ 0`.
Then `ℤ[H] ∩ Δ(K)^n = Δ(H)^n` for all `n` and `D_n(K) = D_n(H)` for `n ≥ 2`. For `c = 1` this
is Lemma 5.9 with `m = 2`. -/
theorem D_n_eq_of_sqrt {K : Type*} [Group K] (H : Subgroup K) (r : K) (g : H)
    (central : ∀ x : K, r * x = x * r) (sq_mem : r * r ∈ H) (r_nmem : r ∉ H)
    (gen : ∀ k : K, ∃ h ∈ H, k = h ∨ k = h * r)
    (hc : ∀ j : ℕ, of ℤ H ((g⁻¹ * g⁻¹ * ⟨r * r, sq_mem⟩) ^ 2 ^ j) - 1 ∈ augIdeal H ^ (j + 2)) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal K ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n K = (D n H).map H.subtype :=
  let S : SqrtData K := ⟨H, r, g, central, sq_mem, r_nmem, gen⟩
  ⟨S.iota_mem_augIdeal_pow_iff hc, S.D_eq hc⟩

end GroupDimension
