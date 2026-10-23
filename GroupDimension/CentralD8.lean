module

public import GroupDimension.CentralRoot

@[expose] public section

/-!
# Central products with `D₈` (Proposition 5.8(1) of the D5 paper)

Let `Q` be a group, `H ≤ Q`, and `a, b ∈ Q` involutions commuting with every element of `H`,
with `t = [a, b] ∈ H`, `Q = H ⊔ Ha ⊔ Hb ⊔ Hab` (that is, `Q = H·⟨a, b⟩` and `a, b, ab ∉ H`).
This is `Q = H ∘ D₈`, glued along `Z(D₈) = ⟨t⟩` (for `t = 1` it is `H × C₂²`, also
covered). If `t ∈ γ₂(H)`, then

  `ℤ[H] ∩ Δ(Q)^n = Δ(H)^n` for all `n`, and `D_n(Q) = D_n(H)` for `n ≥ 2`.

The proof is the paper's. The module `N = ℤ[Q/⟨b⟩]` is free over `ℤ[H]` on `e₀ = ⟨b⟩` and
`f = a e₀ - e₀`; in these coordinates `u e₀ = X(u) e₀ + Y(u) f`, where on group elements
`X(h e) = h` and `Y(h e) = h` or `0` according as `e ∈ {a, ab}` or `e ∈ {1, b}`. Left
multiplication acts by `a : (x, y) ↦ (x, x - y)` and `b : (x, y) ↦ (x + yτ, yt)`,
`τ = t - 1`. With `B_n` the left ideal spanned by the `2^(n-1-i) x`, `x ∈ Δ(H)^i`, the set
`{u | X u ∈ Δ(H)^n, Y u ∈ B_n}` is a left ideal containing `Δ(Q)^n`; the input is
`2^k τ ∈ Δ(H)^(k+2)`, which holds with room to spare (`2^k τ ∈ Δ(H)^(2k+2)`, from `τ² = -2τ` and
`τ ∈ Δ(H)^2`).

MATH-206; the paper's statement is `D_n_eq_of_dihedral`.
-/

namespace GroupDimension

open MonoidAlgebra

/-! ## A projection that respects the filtration -/

/-- If `ℤ[H] ∩ Δ(Q)^n ⊆ Δ(H)^n` for all `n` and `[Q, Q] ≤ H`, then `D_n(Q) = D_n(H)` for
`n ≥ 2`. -/
theorem D_eq_of_mem_pow {Q : Type*} [Group Q] (H : Subgroup Q) (hcomm : commutator Q ≤ H)
    (hring : ∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
      mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n → x ∈ augIdeal H ^ n)
    (n : ℕ) (hn : 2 ≤ n) : D n Q = (D n H).map H.subtype := by
  refine le_antisymm ?_ (map_D_le _ n)
  intro k hk
  have hk2 : k ∈ H := by
    have : k ∈ D 2 Q := D_antitone hn hk
    rw [D_two, Subgroup.top_lowerCentralSeries_one] at this
    exact hcomm this
  refine ⟨⟨k, hk2⟩, ?_, rfl⟩
  show (⟨k, hk2⟩ : H) ∈ D n H
  rw [mem_D]
  apply hring
  rw [_root_.map_sub, _root_.map_one, mapDomainRingHom_of]
  exact hk

/-! ## The filtration `B_n` -/

section Filtration

variable {G : Type*} [Group G]

variable (G) in
/-- The left ideal `B_n` of `ℤ[G]` spanned by the `2^(n-1-i) x` with `x ∈ Δ(G)^i`, `i ≤ n`.
It contains `Δ(G)^(n-1)` (the terms `i = n - 1, n` both have coefficient `1`) and
`2^(n-1) ℤ[G]`. -/
noncomputable def Bfilt (n : ℕ) : Ideal (MonoidAlgebra ℤ G) :=
  Ideal.span {y | ∃ i ≤ n, ∃ x ∈ augIdeal G ^ i, y = (2 ^ (n - 1 - i) : ℕ) • x}

theorem gen_mem_Bfilt {n i : ℕ} (hi : i ≤ n) {x : MonoidAlgebra ℤ G}
    (hx : x ∈ augIdeal G ^ i) : (2 ^ (n - 1 - i) : ℕ) • x ∈ Bfilt G n :=
  Ideal.subset_span ⟨i, hi, x, hx, rfl⟩

theorem pow_le_Bfilt {n : ℕ} {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G ^ n) :
    x ∈ Bfilt G n := by
  have := gen_mem_Bfilt (le_refl n) hx
  rwa [show n - 1 - n = 0 by omega, pow_zero, one_smul] at this

theorem pow_le_Bfilt_succ {n : ℕ} {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G ^ n) :
    x ∈ Bfilt G (n + 1) := by
  have := gen_mem_Bfilt (n := n + 1) (by omega) hx
  rwa [show n + 1 - 1 - n = 0 by omega, pow_zero, one_smul] at this

/-- Induction over `B_n` for a property closed under left multiplication. -/
theorem Bfilt_induction {n : ℕ} {p : MonoidAlgebra ℤ G → Prop} {y : MonoidAlgebra ℤ G}
    (hy : y ∈ Bfilt G n)
    (hgen : ∀ i ≤ n, ∀ x ∈ augIdeal G ^ i, p ((2 ^ (n - 1 - i) : ℕ) • x))
    (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) (hmul : ∀ c y, p y → p (c * y)) : p y := by
  refine Submodule.span_induction ?_ h0 (fun y z _ _ => hadd y z) (fun c y _ => hmul c y) hy
  rintro _ ⟨i, hi, x, hx, rfl⟩
  exact hgen i hi x hx

/-- `Δ · B_n ⊆ B_{n+1}`. -/
theorem Bfilt_mul_left {n : ℕ} {y : MonoidAlgebra ℤ G} (hy : y ∈ Bfilt G n) :
    ∀ δ ∈ augIdeal G, δ * y ∈ Bfilt G (n + 1) := by
  refine Bfilt_induction (p := fun y => ∀ δ ∈ augIdeal G, δ * y ∈ Bfilt G (n + 1)) hy ?_
    (fun δ _ => by rw [mul_zero]; exact zero_mem _) ?_ ?_
  · intro i hi x hx δ hδ
    rw [mul_smul_comm]
    have hδx : δ * x ∈ augIdeal G ^ (i + 1) := by
      have := mul_mem_augIdeal_pow (i := 1) (by rwa [Submodule.pow_one]) hx
      rwa [add_comm] at this
    have := gen_mem_Bfilt (n := n + 1) (by omega) hδx
    rwa [show n + 1 - 1 - (i + 1) = n - 1 - i by omega] at this
  · intro y z hy hz δ hδ
    rw [mul_add]; exact add_mem (hy δ hδ) (hz δ hδ)
  · intro c y hy δ hδ
    rw [← mul_assoc]
    exact hy _ (Ideal.mul_mem_right _ _ hδ)

/-- `B_n · ℤ[G] ⊆ B_n`. -/
theorem Bfilt_mul_right {n : ℕ} {y : MonoidAlgebra ℤ G} (hy : y ∈ Bfilt G n)
    (z : MonoidAlgebra ℤ G) : y * z ∈ Bfilt G n := by
  refine Bfilt_induction (p := fun y => y * z ∈ Bfilt G n) hy ?_
    (by simp) ?_ ?_
  · intro i hi x hx
    rw [smul_mul_assoc]
    exact gen_mem_Bfilt hi (Ideal.mul_mem_right _ _ hx)
  · intro y w hy hw
    rw [add_mul]; exact add_mem hy hw
  · intro c y hy
    rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hy

/-- `B_n · Δ ⊆ B_{n+1}`. -/
theorem Bfilt_mul_aug {n : ℕ} {y : MonoidAlgebra ℤ G} (hy : y ∈ Bfilt G n)
    {δ : MonoidAlgebra ℤ G} (hδ : δ ∈ augIdeal G) : y * δ ∈ Bfilt G (n + 1) := by
  refine Bfilt_induction (p := fun y => y * δ ∈ Bfilt G (n + 1)) hy ?_
    (by simp) ?_ ?_
  · intro i hi x hx
    rw [smul_mul_assoc]
    have := gen_mem_Bfilt (n := n + 1) (by omega)
      (mul_mem_augIdeal_pow (j := 1) hx (by rwa [Submodule.pow_one]))
    rwa [show n + 1 - 1 - (i + 1) = n - 1 - i by omega] at this
  · intro y w hy hw
    rw [add_mul]; exact add_mem hy hw
  · intro c y hy
    rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hy

/-- `y ∈ B_n → 2y ∈ B_{n+1}`. -/
theorem Bfilt_add_self {n : ℕ} {y : MonoidAlgebra ℤ G} (hy : y ∈ Bfilt G n) :
    y + y ∈ Bfilt G (n + 1) := by
  refine Bfilt_induction (p := fun y => y + y ∈ Bfilt G (n + 1)) hy ?_
    (by simp) ?_ ?_
  · intro i hi x hx
    rcases Nat.lt_or_ge i n with h | h
    · have := gen_mem_Bfilt (n := n + 1) (by omega) hx
      rwa [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, pow_succ, mul_smul, two_smul,
        smul_add] at this
    · have hi' : i = n := le_antisymm hi h
      subst hi'
      rw [show i - 1 - i = 0 by omega, pow_zero, one_smul]
      exact pow_le_Bfilt_succ (add_mem hx hx)
  · intro y z hy hz
    rw [add_add_add_comm]; exact add_mem hy hz
  · intro c y hy
    rw [← mul_add]; exact Ideal.mul_mem_left _ _ hy

/-- If `2^k τ ∈ Δ^(k+2)` for all `k`, then `B_n τ ⊆ Δ^(n+1)`. -/
theorem Bfilt_mul_tau {τ : MonoidAlgebra ℤ G}
    (hτ : ∀ k : ℕ, (2 ^ k : ℕ) • τ ∈ augIdeal G ^ (k + 2)) {n : ℕ} {y : MonoidAlgebra ℤ G}
    (hy : y ∈ Bfilt G n) : y * τ ∈ augIdeal G ^ (n + 1) := by
  refine Bfilt_induction (p := fun y => y * τ ∈ augIdeal G ^ (n + 1)) hy ?_
    (by simp) ?_ ?_
  · intro i hi x hx
    rw [smul_mul_assoc, ← mul_smul_comm]
    exact Ideal.pow_le_pow_right (by omega) (mul_mem_augIdeal_pow hx (hτ (n - 1 - i)))
  · intro y z hy hz
    rw [add_mul]; exact add_mem hy hz
  · intro c y hy
    rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hy

/-- `Δ^(n+1) = Δ · Δ^n`. -/
theorem augIdeal_pow_succ' (n : ℕ) : augIdeal G ^ (n + 1) = augIdeal G * augIdeal G ^ n := by
  rcases n with _ | n
  · rw [Submodule.pow_zero, Ideal.one_eq_top, zero_add, Submodule.pow_one, Ideal.mul_top]
  · exact Submodule.pow_succ' _ (Nat.succ_ne_zero n)

end Filtration

/-- The data of Proposition 5.8(1): `Q = H ∘ D₈`. -/
structure DihedralData (Q : Type*) [Group Q] where
  H : Subgroup Q
  a : Q
  b : Q
  t : H
  ha : a * a = 1
  hb : b * b = 1
  comm_a : ∀ h ∈ H, a * h = h * a
  comm_b : ∀ h ∈ H, b * h = h * b
  ht : (t : Q) = a * b * a⁻¹ * b⁻¹
  gen : ∀ g : Q, ∃ h ∈ H, g = h ∨ g = h * a ∨ g = h * b ∨ g = h * (a * b)
  a_nmem : a ∉ H
  b_nmem : b ∉ H
  ab_nmem : a * b ∉ H

namespace DihedralData

variable {Q : Type*} [Group Q] (S : DihedralData Q)

/-! ## Relations -/

theorem a_inv : S.a⁻¹ = S.a := inv_eq_of_mul_eq_one_right S.ha

theorem b_inv : S.b⁻¹ = S.b := inv_eq_of_mul_eq_one_right S.hb

theorem ht' : (S.t : Q) = S.a * S.b * S.a * S.b := by
  rw [S.ht, S.a_inv, S.b_inv]

theorem t_comm_a : S.a * S.t = S.t * S.a := S.comm_a _ S.t.2

/-- `ba = t ab`. -/
theorem ba : S.b * S.a = S.t * (S.a * S.b) := by
  calc S.b * S.a = (S.a * S.a) * S.b * S.a * (S.b * S.b) := by rw [S.ha, S.hb]; group
    _ = S.a * (S.a * S.b * S.a * S.b) * S.b := by group
    _ = S.a * S.t * S.b := by rw [S.ht']
    _ = S.t * S.a * S.b := by rw [S.t_comm_a]
    _ = S.t * (S.a * S.b) := by group

/-- `b ab = t a`. -/
theorem bab : S.b * (S.a * S.b) = S.t * S.a := by
  rw [← mul_assoc, S.ba, mul_assoc, mul_assoc, S.hb, mul_one]

/-- `aba = t b`. -/
theorem aba : S.a * S.b * S.a = S.t * S.b := by
  rw [mul_assoc, S.ba, ← mul_assoc, ← mul_assoc, S.t_comm_a, mul_assoc (S.t : Q) S.a S.a, S.ha,
    mul_one]

/-- `τ = t - 1 ∈ ℤ[H]`. -/
noncomputable abbrev τ : MonoidAlgebra ℤ S.H := of ℤ S.H S.t - 1

theorem tt : (S.t : Q) * S.t = 1 := by
  have h1 : S.a * S.t * S.a = S.t := by rw [S.t_comm_a, mul_assoc, S.ha, mul_one]
  have h2 : S.a * S.t * S.a = (S.t : Q)⁻¹ := by
    rw [S.ht']
    simp only [mul_inv_rev, S.a_inv, S.b_inv]
    have : S.a * (S.a * S.b * S.a * S.b) * S.a = (S.a * S.a) * (S.b * (S.a * (S.b * S.a))) := by
      group
    rw [this, S.ha, one_mul]
  rw [mul_eq_one_iff_eq_inv]
  exact h1.symm.trans h2

/-! ## The retraction on elements -/

open Classical in
/-- `ρ(h e) = h` for `e ∈ {1, a, b, ab}`. -/
noncomputable def rho (g : Q) : Q :=
  if g ∈ S.H then g else if g * S.b ∈ S.H then g * S.b
  else if g * S.a ∈ S.H then g * S.a else g * S.b * S.a

/-- `g ∈ Ha ∪ Hab`. -/
def IsA (g : Q) : Prop := g ∉ S.H ∧ g * S.b ∉ S.H

variable {S}

theorem mul_mem_iff {h : Q} (hh : h ∈ S.H) (x : Q) : h * x ∈ S.H ↔ x ∈ S.H :=
  Subgroup.mul_mem_cancel_left _ hh

theorem rho_h {h : Q} (hh : h ∈ S.H) : S.rho h = h := by
  simp [rho, hh]

theorem rho_ha {h : Q} (hh : h ∈ S.H) : S.rho (h * S.a) = h := by
  have h1 : h * S.a ∉ S.H := by rw [mul_mem_iff hh]; exact S.a_nmem
  have h2 : h * S.a * S.b ∉ S.H := by rw [mul_assoc, mul_mem_iff hh]; exact S.ab_nmem
  have h3 : h * S.a * S.a = h := by rw [mul_assoc, S.ha, mul_one]
  simp [rho, h1, h2, h3, hh]

theorem rho_hb {h : Q} (hh : h ∈ S.H) : S.rho (h * S.b) = h := by
  have h1 : h * S.b ∉ S.H := by rw [mul_mem_iff hh]; exact S.b_nmem
  have h3 : h * S.b * S.b = h := by rw [mul_assoc, S.hb, mul_one]
  simp [rho, h1, h3, hh]

theorem rho_hab {h : Q} (hh : h ∈ S.H) : S.rho (h * (S.a * S.b)) = h := by
  have h1 : h * (S.a * S.b) ∉ S.H := by rw [mul_mem_iff hh]; exact S.ab_nmem
  have h2 : h * (S.a * S.b) * S.b ∉ S.H := by
    rw [mul_assoc, mul_assoc, S.hb, mul_one, mul_mem_iff hh]; exact S.a_nmem
  have h3 : h * (S.a * S.b) * S.a ∉ S.H := by
    rw [mul_assoc, S.aba, ← mul_assoc, mul_mem_iff (S.H.mul_mem hh S.t.2)]
    exact S.b_nmem
  have h4 : h * (S.a * S.b) * S.b * S.a = h := by
    rw [mul_assoc h, mul_assoc S.a, S.hb, mul_one, mul_assoc, S.ha, mul_one]
  simp [rho, h1, h2, h3, h4]

theorem isA_h {h : Q} (hh : h ∈ S.H) : ¬S.IsA h := fun h' => h'.1 hh

theorem isA_ha {h : Q} (hh : h ∈ S.H) : S.IsA (h * S.a) :=
  ⟨by rw [mul_mem_iff hh]; exact S.a_nmem,
   by rw [mul_assoc, mul_mem_iff hh]; exact S.ab_nmem⟩

theorem isA_hb {h : Q} (hh : h ∈ S.H) : ¬S.IsA (h * S.b) :=
  fun h' => h'.2 (by rw [mul_assoc, S.hb, mul_one]; exact hh)

theorem isA_hab {h : Q} (hh : h ∈ S.H) : S.IsA (h * (S.a * S.b)) :=
  ⟨by rw [mul_mem_iff hh]; exact S.ab_nmem,
   by rw [mul_assoc, mul_assoc, S.hb, mul_one, mul_mem_iff hh]; exact S.a_nmem⟩

theorem rho_mem (g : Q) : S.rho g ∈ S.H := by
  obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g
  · rw [rho_h hh]; exact hh
  · rw [rho_ha hh]; exact hh
  · rw [rho_hb hh]; exact hh
  · rw [rho_hab hh]; exact hh

variable (S) in
/-- The retraction `Q → H`. -/
noncomputable def ret (g : Q) : S.H := ⟨S.rho g, rho_mem g⟩

open Classical in
variable (S) in
/-- The second coordinate of `g e₀`: `h` for `g = ha, hab`, and `0` for `g = h, hb`. -/
noncomputable def yv (g : Q) : MonoidAlgebra ℤ S.H := if S.IsA g then of ℤ S.H (S.ret g) else 0

theorem ret_h {h : Q} (hh : h ∈ S.H) : S.ret h = ⟨h, hh⟩ := Subtype.ext (rho_h hh)
theorem ret_ha {h : Q} (hh : h ∈ S.H) : S.ret (h * S.a) = ⟨h, hh⟩ := Subtype.ext (rho_ha hh)
theorem ret_hb {h : Q} (hh : h ∈ S.H) : S.ret (h * S.b) = ⟨h, hh⟩ := Subtype.ext (rho_hb hh)
theorem ret_hab {h : Q} (hh : h ∈ S.H) : S.ret (h * (S.a * S.b)) = ⟨h, hh⟩ :=
  Subtype.ext (rho_hab hh)

theorem yv_h {h : Q} (hh : h ∈ S.H) : S.yv h = 0 := by simp [yv, isA_h hh]
theorem yv_ha {h : Q} (hh : h ∈ S.H) : S.yv (h * S.a) = of ℤ S.H ⟨h, hh⟩ := by
  simp [yv, isA_ha hh, ret_ha hh]
theorem yv_hb {h : Q} (hh : h ∈ S.H) : S.yv (h * S.b) = 0 := by simp [yv, isA_hb hh]
theorem yv_hab {h : Q} (hh : h ∈ S.H) : S.yv (h * (S.a * S.b)) = of ℤ S.H ⟨h, hh⟩ := by
  simp [yv, isA_hab hh, ret_hab hh]

/-! ## How left multiplication by `h`, `a`, `b` acts on `(r, yv)` -/

theorem of_mk_mul {h k : Q} (hh : h ∈ S.H) (hk : k ∈ S.H) :
    of ℤ S.H ⟨k, hk⟩ * of ℤ S.H ⟨h, hh⟩ = of ℤ S.H ⟨k * h, S.H.mul_mem hk hh⟩ := by
  rw [← _root_.map_mul]; rfl

theorem ret_mul_h {k : Q} (hk : k ∈ S.H) (g : Q) :
    of ℤ S.H (S.ret (k * g)) = of ℤ S.H ⟨k, hk⟩ * of ℤ S.H (S.ret g) ∧
      S.yv (k * g) = of ℤ S.H ⟨k, hk⟩ * S.yv g := by
  have hkh : ∀ {h}, h ∈ S.H → k * h ∈ S.H := fun hh => S.H.mul_mem hk hh
  obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g
  · rw [ret_h (hkh hh), ret_h hh, yv_h (hkh hh), yv_h hh, of_mk_mul hh hk, mul_zero]
    exact ⟨rfl, rfl⟩
  · rw [← mul_assoc, ret_ha (hkh hh), ret_ha hh, yv_ha (hkh hh), yv_ha hh, of_mk_mul hh hk]
    exact ⟨rfl, rfl⟩
  · rw [← mul_assoc, ret_hb (hkh hh), ret_hb hh, yv_hb (hkh hh), yv_hb hh, of_mk_mul hh hk,
      mul_zero]
    exact ⟨rfl, rfl⟩
  · rw [← mul_assoc, ret_hab (hkh hh), ret_hab hh, yv_hab (hkh hh), yv_hab hh, of_mk_mul hh hk]
    exact ⟨rfl, rfl⟩

theorem ret_mul_a (g : Q) :
    S.ret (S.a * g) = S.ret g ∧ S.yv (S.a * g) = of ℤ S.H (S.ret g) - S.yv g := by
  obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g
  · rw [S.comm_a h hh, ret_ha hh, ret_h hh, yv_ha hh, yv_h hh, sub_zero]
    exact ⟨rfl, rfl⟩
  · have e : S.a * (h * S.a) = h := by
      rw [← mul_assoc, S.comm_a h hh, mul_assoc, S.ha, mul_one]
    rw [e, ret_h hh, ret_ha hh, yv_h hh, yv_ha hh, sub_self]
    exact ⟨rfl, rfl⟩
  · have e : S.a * (h * S.b) = h * (S.a * S.b) := by rw [← mul_assoc, S.comm_a h hh, mul_assoc]
    rw [e, ret_hab hh, ret_hb hh, yv_hab hh, yv_hb hh, sub_zero]
    exact ⟨rfl, rfl⟩
  · have e : S.a * (h * (S.a * S.b)) = h * S.b := by
      rw [← mul_assoc, S.comm_a h hh, mul_assoc, ← mul_assoc S.a, S.ha, one_mul]
    rw [e, ret_hb hh, ret_hab hh, yv_hb hh, yv_hab hh, sub_self]
    exact ⟨rfl, rfl⟩

theorem ret_mul_b (g : Q) :
    of ℤ S.H (S.ret (S.b * g)) = of ℤ S.H (S.ret g) + S.yv g * S.τ ∧
      S.yv (S.b * g) = S.yv g * of ℤ S.H S.t := by
  have ht : ∀ {h}, (hh : h ∈ S.H) → of ℤ S.H ⟨h, hh⟩ * of ℤ S.H S.t =
      of ℤ S.H ⟨h * S.t, S.H.mul_mem hh S.t.2⟩ := fun hh => by rw [← _root_.map_mul]; rfl
  obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g
  · rw [S.comm_b h hh, ret_hb hh, ret_h hh, yv_hb hh, yv_h hh, zero_mul, zero_mul, add_zero]
    exact ⟨rfl, rfl⟩
  · have hht : h * S.t ∈ S.H := S.H.mul_mem hh S.t.2
    have e : S.b * (h * S.a) = (h * S.t) * (S.a * S.b) := by
      rw [← mul_assoc, S.comm_b h hh, mul_assoc, S.ba, ← mul_assoc]
    rw [e, ret_hab hht, ret_ha hh, yv_hab hht, yv_ha hh, ht hh, τ, mul_sub, mul_one, ht hh]
    exact ⟨by abel, rfl⟩
  · have e : S.b * (h * S.b) = h := by
      rw [← mul_assoc, S.comm_b h hh, mul_assoc, S.hb, mul_one]
    rw [e, ret_h hh, ret_hb hh, yv_h hh, yv_hb hh, zero_mul, zero_mul, add_zero]
    exact ⟨rfl, rfl⟩
  · have hht : h * S.t ∈ S.H := S.H.mul_mem hh S.t.2
    have e : S.b * (h * (S.a * S.b)) = (h * S.t) * S.a := by
      rw [← mul_assoc, S.comm_b h hh, mul_assoc, S.bab, ← mul_assoc]
    rw [e, ret_ha hht, ret_hab hh, yv_ha hht, yv_hab hh, ht hh, τ, mul_sub, mul_one, ht hh]
    exact ⟨by abel, rfl⟩

/-! ## The coordinates `X, Y : ℤ[Q] → ℤ[H]` -/

variable (S)

/-- `X(h e) = h`. -/
noncomputable def X : MonoidAlgebra ℤ Q →+ MonoidAlgebra ℤ S.H :=
  MonoidAlgebra.liftNC (Int.castAddHom _) (fun g => of ℤ S.H (S.ret g))

/-- `Y(h e) = h` for `e ∈ {a, ab}`, `0` for `e ∈ {1, b}`. -/
noncomputable def Y : MonoidAlgebra ℤ Q →+ MonoidAlgebra ℤ S.H :=
  MonoidAlgebra.liftNC (Int.castAddHom _) S.yv

theorem X_of (g : Q) : S.X (of ℤ Q g) = of ℤ S.H (S.ret g) := by
  simp [X, MonoidAlgebra.of_apply, MonoidAlgebra.liftNC_single]

theorem Y_of (g : Q) : S.Y (of ℤ Q g) = S.yv g := by
  simp [Y, MonoidAlgebra.of_apply, MonoidAlgebra.liftNC_single]

/-- Two additive maps out of `ℤ[Q]` that agree on group elements agree. -/
theorem ext_of {M : Type*} [AddCommGroup M] {f₁ f₂ : MonoidAlgebra ℤ Q →+ M}
    (h : ∀ g, f₁ (of ℤ Q g) = f₂ (of ℤ Q g)) (y : MonoidAlgebra ℤ Q) : f₁ y = f₂ y := by
  induction y using CentralRoot.induction_of with
  | h0 => simp
  | hof g => exact h g
  | hneg y hy => rw [_root_.map_neg, hy, _root_.map_neg]
  | hadd y z hy hz => rw [_root_.map_add, hy, hz, _root_.map_add]

theorem X_mul_h {k : Q} (hk : k ∈ S.H) (y : MonoidAlgebra ℤ Q) :
    S.X (of ℤ Q k * y) = of ℤ S.H ⟨k, hk⟩ * S.X y := by
  refine ext_of (f₁ := (S.X).comp (AddMonoidHom.mulLeft (of ℤ Q k)))
    (f₂ := (AddMonoidHom.mulLeft (of ℤ S.H ⟨k, hk⟩)).comp S.X) (fun g => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← _root_.map_mul, X_of]
  exact (ret_mul_h hk g).1.trans (_root_.map_mul _ _ _).symm

theorem Y_mul_h {k : Q} (hk : k ∈ S.H) (y : MonoidAlgebra ℤ Q) :
    S.Y (of ℤ Q k * y) = of ℤ S.H ⟨k, hk⟩ * S.Y y := by
  refine ext_of (f₁ := (S.Y).comp (AddMonoidHom.mulLeft (of ℤ Q k)))
    (f₂ := (AddMonoidHom.mulLeft (of ℤ S.H ⟨k, hk⟩)).comp S.Y) (fun g => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← _root_.map_mul, Y_of]
  exact (ret_mul_h hk g).2

theorem X_mul_a (y : MonoidAlgebra ℤ Q) : S.X (of ℤ Q S.a * y) = S.X y := by
  refine ext_of (f₁ := (S.X).comp (AddMonoidHom.mulLeft (of ℤ Q S.a))) (f₂ := S.X)
    (fun g => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← _root_.map_mul, X_of,
    (ret_mul_a g).1]

theorem Y_mul_a (y : MonoidAlgebra ℤ Q) : S.Y (of ℤ Q S.a * y) = S.X y - S.Y y := by
  refine ext_of (f₁ := (S.Y).comp (AddMonoidHom.mulLeft (of ℤ Q S.a))) (f₂ := S.X - S.Y)
    (fun g => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, ← _root_.map_mul, Y_of, X_of,
    AddMonoidHom.sub_apply]
  exact (ret_mul_a g).2

theorem X_mul_b (y : MonoidAlgebra ℤ Q) :
    S.X (of ℤ Q S.b * y) = S.X y + S.Y y * S.τ := by
  refine ext_of (f₁ := (S.X).comp (AddMonoidHom.mulLeft (of ℤ Q S.b)))
    (f₂ := S.X + (AddMonoidHom.mulRight S.τ).comp S.Y) (fun g => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
    AddMonoidHom.add_apply, ← _root_.map_mul, Y_of, X_of]
  exact (ret_mul_b g).1

theorem Y_mul_b (y : MonoidAlgebra ℤ Q) :
    S.Y (of ℤ Q S.b * y) = S.Y y * of ℤ S.H S.t := by
  refine ext_of (f₁ := (S.Y).comp (AddMonoidHom.mulLeft (of ℤ Q S.b)))
    (f₂ := (AddMonoidHom.mulRight (of ℤ S.H S.t)).comp S.Y) (fun g => ?_) y
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
    ← _root_.map_mul, Y_of]
  exact (ret_mul_b g).2

theorem X_iota (x : MonoidAlgebra ℤ S.H) : S.X (mapDomainRingHom ℤ S.H.subtype x) = x := by
  induction x using CentralRoot.induction_of with
  | h0 => rw [_root_.map_zero, _root_.map_zero]
  | hof h =>
    rw [mapDomainRingHom_of, X_of]
    congr 1
    exact Subtype.ext (rho_h h.2)
  | hneg y hy => rw [_root_.map_neg, _root_.map_neg, hy]
  | hadd y z hy hz => rw [_root_.map_add, _root_.map_add, hy, hz]

/-! ## `2^k τ ∈ Δ(H)^(2k+2)` -/

variable {S}

theorem tau_mem (htc : S.t ∈ commutator S.H) : S.τ ∈ augIdeal S.H ^ 2 := by
  have : S.t ∈ D 2 S.H := by rw [D_two, Subgroup.top_lowerCentralSeries_one]; exact htc
  exact mem_D.mp this

theorem two_pow_smul_tau (htc : S.t ∈ commutator S.H) (k : ℕ) :
    (2 ^ k : ℕ) • S.τ ∈ augIdeal S.H ^ (2 * k + 2) := by
  induction k with
  | zero => rw [pow_zero, one_smul]; exact tau_mem htc
  | succ k ih =>
    have htt : of ℤ S.H S.t * of ℤ S.H S.t = 1 := by
      rw [← _root_.map_mul, show S.t * S.t = 1 from Subtype.ext S.tt, _root_.map_one]
    have hsq : S.τ * S.τ = -((2 : ℕ) • S.τ) := by
      have e : S.τ * S.τ = of ℤ S.H S.t * of ℤ S.H S.t - of ℤ S.H S.t - of ℤ S.H S.t + 1 := by
        simp only [τ]; noncomm_ring
      rw [e, htt, two_smul]; simp only [τ]; abel
    have e : (2 ^ (k + 1) : ℕ) • S.τ = -(((2 ^ k : ℕ) • S.τ) * S.τ) := by
      rw [smul_mul_assoc, hsq, smul_neg, neg_neg, smul_smul, pow_succ]
    rw [e]
    refine neg_mem ?_
    have := mul_mem_augIdeal_pow ih (tau_mem htc)
    rwa [show 2 * k + 2 + 2 = 2 * (k + 1) + 2 by ring] at this

theorem two_pow_smul_tau' (htc : S.t ∈ commutator S.H) (k : ℕ) :
    (2 ^ k : ℕ) • S.τ ∈ augIdeal S.H ^ (k + 2) :=
  Ideal.pow_le_pow_right (by omega) (two_pow_smul_tau htc k)

theorem B_mul_t (htc : S.t ∈ commutator S.H) {n : ℕ} {y : MonoidAlgebra ℤ S.H}
    (hy : y ∈ Bfilt S.H n) : y * of ℤ S.H S.t ∈ Bfilt S.H n := by
  have e : y * of ℤ S.H S.t = y + y * S.τ := by simp only [τ]; noncomm_ring
  rw [e]
  exact add_mem hy (pow_le_Bfilt (Ideal.pow_le_pow_right (Nat.le_succ n)
    (Bfilt_mul_tau (two_pow_smul_tau' htc) hy)))

/-! ## The left ideal `P_n = {u | X u ∈ Δ(H)^n, Y u ∈ B_n}` -/

variable (S)

/-- The left ideal `{u | X u ∈ Δ(H)^n, Y u ∈ B_n}` of `ℤ[Q]`. -/
noncomputable def P (htc : S.t ∈ commutator S.H) (n : ℕ) : Ideal (MonoidAlgebra ℤ Q) where
  carrier := {u | S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    simp only [Set.mem_setOf_eq, _root_.map_add] at *
    exact ⟨add_mem hy.1 hz.1, add_mem hy.2 hz.2⟩
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    -- closure under `h ·`, `a ·`, `b ·`
    have hh : ∀ k (hk : k ∈ S.H) (u : MonoidAlgebra ℤ Q),
        S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n →
        S.X (of ℤ Q k * u) ∈ augIdeal S.H ^ n ∧ S.Y (of ℤ Q k * u) ∈ Bfilt S.H n := by
      intro k hk u hu
      rw [S.X_mul_h hk, S.Y_mul_h hk]
      exact ⟨Ideal.mul_mem_left _ _ hu.1, Ideal.mul_mem_left _ _ hu.2⟩
    have ha : ∀ u : MonoidAlgebra ℤ Q,
        S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n →
        S.X (of ℤ Q S.a * u) ∈ augIdeal S.H ^ n ∧ S.Y (of ℤ Q S.a * u) ∈ Bfilt S.H n := by
      intro u hu
      rw [S.X_mul_a, S.Y_mul_a]
      exact ⟨hu.1, sub_mem (pow_le_Bfilt hu.1) hu.2⟩
    have hb : ∀ u : MonoidAlgebra ℤ Q,
        S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n →
        S.X (of ℤ Q S.b * u) ∈ augIdeal S.H ^ n ∧ S.Y (of ℤ Q S.b * u) ∈ Bfilt S.H n := by
      intro u hu
      rw [S.X_mul_b, S.Y_mul_b]
      exact ⟨add_mem hu.1 (Ideal.pow_le_pow_right (Nat.le_succ n)
        (Bfilt_mul_tau (two_pow_smul_tau' htc) hu.2)),
        B_mul_t htc hu.2⟩
    induction c using CentralRoot.induction_of with
    | h0 => simp
    | hof g =>
      obtain ⟨h, hh', hg | hg | hg | hg⟩ := S.gen g <;> subst g
      · exact hh h hh' u hu
      · rw [map_mul (of ℤ Q) h S.a, mul_assoc]; exact hh h hh' _ (ha u hu)
      · rw [map_mul (of ℤ Q) h S.b, mul_assoc]; exact hh h hh' _ (hb u hu)
      · rw [map_mul (of ℤ Q) h, map_mul (of ℤ Q) S.a S.b, mul_assoc, mul_assoc]
        exact hh h hh' _ (ha _ (hb u hu))
    | hneg c hc =>
      simp only [neg_mul, _root_.map_neg]; exact ⟨neg_mem hc.1, neg_mem hc.2⟩
    | hadd c d hc hd =>
      simp only [add_mul, _root_.map_add]; exact ⟨add_mem hc.1 hd.1, add_mem hc.2 hd.2⟩

variable {S}

theorem mem_P {htc : S.t ∈ commutator S.H} {n : ℕ} {u : MonoidAlgebra ℤ Q} :
    u ∈ S.P htc n ↔ S.X u ∈ augIdeal S.H ^ n ∧ S.Y u ∈ Bfilt S.H n := Iff.rfl

theorem sub_one_mul_mem_P (htc : S.t ∈ commutator S.H) {n : ℕ} {u : MonoidAlgebra ℤ Q}
    (hu : u ∈ S.P htc n) (g : Q) : (of ℤ Q g - 1) * u ∈ S.P htc (n + 1) := by
  rw [mem_P] at hu
  have hk : ∀ k (hk : k ∈ S.H), (of ℤ Q k - 1) * u ∈ S.P htc (n + 1) := by
    intro k hk
    rw [mem_P, sub_mul, one_mul, _root_.map_sub, _root_.map_sub, S.X_mul_h hk, S.Y_mul_h hk,
      ← sub_one_mul, ← sub_one_mul]
    refine ⟨?_, Bfilt_mul_left hu.2 _ (of_sub_one_mem_augIdeal _)⟩
    have := mul_mem_augIdeal_pow (i := 1)
      (by rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal (⟨k, hk⟩ : S.H)) hu.1
    rwa [add_comm] at this
  have ha : (of ℤ Q S.a - 1) * u ∈ S.P htc (n + 1) := by
    rw [mem_P, sub_mul, one_mul, _root_.map_sub, _root_.map_sub, S.X_mul_a, S.Y_mul_a, sub_self,
      sub_sub, ← sub_sub, sub_sub (S.X u)]
    exact ⟨zero_mem _, sub_mem (pow_le_Bfilt_succ hu.1) (Bfilt_add_self hu.2)⟩
  have hb : (of ℤ Q S.b - 1) * u ∈ S.P htc (n + 1) := by
    rw [mem_P, sub_mul, one_mul, _root_.map_sub, _root_.map_sub, S.X_mul_b, S.Y_mul_b,
      add_sub_cancel_left]
    refine ⟨Bfilt_mul_tau (two_pow_smul_tau' htc) hu.2, ?_⟩
    have e : S.Y u * of ℤ S.H S.t - S.Y u = S.Y u * S.τ := by simp only [τ]; noncomm_ring
    rw [e]
    exact pow_le_Bfilt (Bfilt_mul_tau (two_pow_smul_tau' htc) hu.2)
  -- `x y - 1 = x (y - 1) + (x - 1)`
  have hmul : ∀ x y : Q, (of ℤ Q x - 1) * u ∈ S.P htc (n + 1) →
      (of ℤ Q y - 1) * u ∈ S.P htc (n + 1) → (of ℤ Q (x * y) - 1) * u ∈ S.P htc (n + 1) := by
    intro x y hx hy
    have e : (of ℤ Q (x * y) - 1) * u = of ℤ Q x * ((of ℤ Q y - 1) * u) + (of ℤ Q x - 1) * u := by
      rw [_root_.map_mul]; noncomm_ring
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ hy) hx
  obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g
  · exact hk h hh
  · exact hmul _ _ (hk h hh) ha
  · exact hmul _ _ (hk h hh) hb
  · exact hmul _ _ (hk h hh) (hmul _ _ ha hb)

theorem augIdeal_pow_le_P (htc : S.t ∈ commutator S.H) (n : ℕ) :
    augIdeal Q ^ n ≤ S.P htc n := by
  induction n with
  | zero =>
    intro u _
    rw [mem_P, Submodule.pow_zero, Ideal.one_eq_top]
    exact ⟨Submodule.mem_top, pow_le_Bfilt (by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial)⟩
  | succ n ih =>
    rw [augIdeal_pow_succ', Ideal.mul_le]
    intro x hx u hu
    refine CentralRoot.augIdeal_induction (p := fun x => x * u ∈ S.P htc (n + 1)) hx
      (by simp) (fun g => sub_one_mul_mem_P htc (ih hu) g)
      (fun y hy => by show (-y) * u ∈ _; rw [neg_mul]; exact neg_mem hy)
      (fun y z hy hz => by show (y + z) * u ∈ _; rw [add_mul]; exact add_mem hy hz)

/-! ## The proposition -/

/-- `ℤ[H] ∩ Δ(Q)^n = Δ(H)^n`. -/
theorem iota_mem_augIdeal_pow_iff (htc : S.t ∈ commutator S.H) (n : ℕ)
    (x : MonoidAlgebra ℤ S.H) :
    mapDomainRingHom ℤ S.H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal S.H ^ n := by
  constructor
  · intro hx
    have := (S.augIdeal_pow_le_P htc n hx).1
    rwa [S.X_iota] at this
  · exact mapDomain_mem_augIdeal_pow S.H.subtype n

theorem conj_of_comm {h e k : Q} (hk : e * k = k * e) : h * e * k * (h * e)⁻¹ = h * k * h⁻¹ := by
  calc h * e * k * (h * e)⁻¹ = h * (e * k) * e⁻¹ * h⁻¹ := by group
    _ = h * k * h⁻¹ := by rw [hk]; group

instance normal : S.H.Normal where
  conj_mem k hk g := by
    have hconj : ∀ {h e : Q}, h ∈ S.H → e * k = k * e → h * e * k * (h * e)⁻¹ ∈ S.H :=
      fun hh he => by
        rw [conj_of_comm he]; exact S.H.mul_mem (S.H.mul_mem hh hk) (S.H.inv_mem hh)
    obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g
    · exact S.H.mul_mem (S.H.mul_mem hh hk) (S.H.inv_mem hh)
    · exact hconj hh (S.comm_a k hk)
    · exact hconj hh (S.comm_b k hk)
    · exact hconj hh (by rw [mul_assoc, S.comm_b k hk, ← mul_assoc, S.comm_a k hk, mul_assoc])

theorem commutator_le : commutator Q ≤ S.H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  let π := QuotientGroup.mk' S.H
  have hπh : ∀ h ∈ S.H, π h = 1 := fun h hh => (QuotientGroup.eq_one_iff h).mpr hh
  have hab : Commute (π S.a) (π S.b) := by
    have : π (S.a * S.b * S.a⁻¹ * S.b⁻¹) = 1 := by rw [← S.ht]; exact hπh _ S.t.2
    simp only [_root_.map_mul, _root_.map_inv] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this)
  -- `π x` is a product of `π a`, `π b`
  have hform : ∀ g : Q, Commute (π g) (π S.a) ∧ Commute (π g) (π S.b) := by
    intro g
    obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen g <;> subst g <;>
      simp only [_root_.map_mul, hπh h hh, one_mul]
    · exact ⟨Commute.one_left _, Commute.one_left _⟩
    · exact ⟨Commute.refl _, hab⟩
    · exact ⟨hab.symm, Commute.refl _⟩
    · exact ⟨(Commute.refl _).mul_left hab.symm, hab.mul_left (Commute.refl _)⟩
  have hxy : Commute (π x) (π y) := by
    obtain ⟨h, hh, hg | hg | hg | hg⟩ := S.gen y <;> subst y <;>
      simp only [_root_.map_mul, hπh h hh, one_mul]
    · exact Commute.one_right _
    · exact (hform x).1
    · exact (hform x).2
    · exact (hform x).1.mul_right (hform x).2
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  show π (x * y * x⁻¹ * y⁻¹) = 1
  simp only [_root_.map_mul, _root_.map_inv]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hxy.eq

/-- **Proposition 5.8(1)**: `D_n(H ∘ D₈) = D_n(H)` for `n ≥ 2`. -/
theorem D_eq (htc : S.t ∈ commutator S.H) (n : ℕ) (hn : 2 ≤ n) :
    D n Q = (D n S.H).map S.H.subtype :=
  D_eq_of_mem_pow S.H S.commutator_le (fun n x => (S.iota_mem_augIdeal_pow_iff htc n x).mp) n hn

end DihedralData

/-- **Proposition 5.8(1), `E = D₈`, as stated in the paper.** Let `H ≤ Q` and let `a, b ∈ Q` be
involutions commuting with `H`, with `t = [a, b] ∈ γ₂(H)`, `Q = H⟨a, b⟩` (every element is
`h`, `ha`, `hb` or `hab` with `h ∈ H`) and `a, b, ab ∉ H`; so `Q = H ∘ D₈`. Then
`ℤ[H] ∩ Δ(Q)^n = Δ(H)^n` for all `n` and `D_n(Q) = D_n(H)` for `n ≥ 2`. -/
theorem D_n_eq_of_dihedral {Q : Type*} [Group Q] (H : Subgroup Q) (a b : Q) (t : H)
    (ha : a * a = 1) (hb : b * b = 1) (comm_a : ∀ h ∈ H, a * h = h * a)
    (comm_b : ∀ h ∈ H, b * h = h * b) (ht : (t : Q) = a * b * a⁻¹ * b⁻¹)
    (htc : t ∈ commutator H)
    (gen : ∀ g : Q, ∃ h ∈ H, g = h ∨ g = h * a ∨ g = h * b ∨ g = h * (a * b))
    (a_nmem : a ∉ H) (b_nmem : b ∉ H) (ab_nmem : a * b ∉ H) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n Q = (D n H).map H.subtype :=
  let S : DihedralData Q := ⟨H, a, b, t, ha, hb, comm_a, comm_b, ht, gen, a_nmem, b_nmem, ab_nmem⟩
  ⟨S.iota_mem_augIdeal_pow_iff htc, S.D_eq htc⟩

end GroupDimension
