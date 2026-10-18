import GroupDimension.CentralSqrt

/-!
# Central products `H ∘ E` with `E/Z(E) ≅ (ℤ/2)²` (Proposition 5.8 of the D5 paper)

Let `Q` be a group, `H ≤ Q`, and `α, β ∈ Q` commuting with every element of `H`, with
`Q = H ⊔ Hα ⊔ Hβ ⊔ Hαβ`, `s = α² ∈ H`, `β² = s^e` and `t = [α, β] ∈ γ₂(H)`. This covers
`H ∘ D₈` (`s = 1`), `H ∘ Q₈` (`s = t`, `e = 1`) and `H ∘ M_{2^{k+2}}` (`α = a`, `β = b`,
`s = a²`, `e = 0`). If for some `g ∈ H` the element `c = g⁻² s` has
`c^(2^j) - 1 ∈ Δ(H)^(j+2)` for all `j`, then `ℤ[H] ∩ Δ(Q)^n = Δ(H)^n` for all `n` and
`D_n(Q) = D_n(H)` for `n ≥ 2`. (Getting from `(H × E)/{(φ(z), z⁻¹)}` to this normal form uses
`H ∩ E = Z(E)` and is not formalized.)

The proof is the paper's, with one overgroup for all cases. In
`G = (Q × ℤ) / ⟨(s, -2)⟩` let `ζ` be the image of `(1, 1)`, so `ζ² = s` and `ζ` is central.
Then `a' = α ζ⁻¹` and `b' = β ζ^(-e)` are involutions commuting with `H'' = H⟨ζ⟩`, with
`[a', b'] = t`, and `G = H'' ∘ D₈`. So `ℤ[H''] ∩ Δ(G)^n = Δ(H'')^n` (`CentralD8`), and
`ℤ[H] ∩ Δ(H'')^n = Δ(H)^n` (`CentralSqrt`, with `r = ζ`). As `Q ↪ G`, `Δ(Q)^n` maps into
`Δ(G)^n`, which gives `ℤ[H] ∩ Δ(Q)^n = Δ(H)^n`; and `[Q, Q]` maps into `[G, G] ≤ H''`, so
`[Q, Q] ≤ H`.

MATH-206; the statements are `D_n_eq_of_central_product` and its corollaries.
-/

namespace GroupDimension

open MonoidAlgebra

/-- The data of Proposition 5.8: `Q = H ∘ E` with `E = ⟨α, β⟩`, `E/Z(E) ≅ (ℤ/2)²`. -/
structure CentralProductData (Q : Type*) [Group Q] where
  H : Subgroup Q
  α : Q
  β : Q
  s : H
  t : H
  e : ℤ
  comm_α : ∀ h ∈ H, α * h = h * α
  comm_β : ∀ h ∈ H, β * h = h * β
  hα : α * α = s
  hβ : β * β = (s : Q) ^ e
  ht : (t : Q) = α * β * α⁻¹ * β⁻¹
  gen : ∀ q : Q, ∃ h ∈ H, q = h ∨ q = h * α ∨ q = h * β ∨ q = h * (α * β)
  α_nmem : α ∉ H
  β_nmem : β ∉ H
  αβ_nmem : α * β ∉ H

namespace CentralProductData

variable {Q : Type*} [Group Q] (S : CentralProductData Q)

/-- The generator of `ℤ`, written multiplicatively. -/
def z : Multiplicative ℤ := Multiplicative.ofAdd 1

theorem zz_zpow (k : ℤ) : (z⁻¹ * z⁻¹) ^ k = Multiplicative.ofAdd (-2 * k) := by
  apply Multiplicative.toAdd.injective
  simp only [z, toAdd_zpow, toAdd_mul, toAdd_inv, toAdd_ofAdd, smul_eq_mul]
  ring

theorem s_comm (q : Q) : Commute (S.s : Q) q := by
  have ch : ∀ h ∈ S.H, Commute (S.s : Q) h := by
    intro h hh
    show (S.s : Q) * h = h * S.s
    rw [← S.hα, mul_assoc, S.comm_α h hh, ← mul_assoc, S.comm_α h hh, mul_assoc]
  have cα : Commute (S.s : Q) S.α := (S.comm_α _ S.s.2).symm
  have cβ : Commute (S.s : Q) S.β := (S.comm_β _ S.s.2).symm
  obtain ⟨h, hh, hq | hq | hq | hq⟩ := S.gen q <;> subst q
  · exact ch h hh
  · exact (ch h hh).mul_right cα
  · exact (ch h hh).mul_right cβ
  · exact (ch h hh).mul_right (cα.mul_right cβ)

/-! ## The overgroup `G = (Q × ℤ) / ⟨(s, -2)⟩` -/

/-- `w = (s, -2)`. -/
def w : Q × Multiplicative ℤ := ((S.s : Q), z⁻¹ * z⁻¹)

theorem w_comm (p : Q × Multiplicative ℤ) : Commute S.w p :=
  Prod.ext (S.s_comm p.1) (mul_comm _ _)

/-- `N = ⟨w⟩`, central. -/
def N : Subgroup (Q × Multiplicative ℤ) := Subgroup.zpowers S.w

instance N_normal : S.N.Normal where
  conj_mem n hn p := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [((S.w_comm p).zpow_left k).symm.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k

/-- The overgroup. -/
abbrev G := (Q × Multiplicative ℤ) ⧸ S.N

/-- The quotient map. -/
def π : Q × Multiplicative ℤ →* S.G := QuotientGroup.mk' S.N

theorem π_eq {p p' : Q × Multiplicative ℤ} :
    S.π p = S.π p' ↔ ∃ k : ℤ, S.w ^ k = p⁻¹ * p' := by
  rw [π, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, N,
    Subgroup.mem_zpowers_iff]

theorem π_w_zpow (k : ℤ) : S.π (S.w ^ k) = 1 := by
  rw [π, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.zpow_mem_zpowers _ k

theorem w_zpow_fst (k : ℤ) : (S.w ^ k).1 = (S.s : Q) ^ k :=
  map_zpow (MonoidHom.fst Q (Multiplicative ℤ)) S.w k

theorem w_zpow_snd' (k : ℤ) : (S.w ^ k).2 = (z⁻¹ * z⁻¹) ^ k :=
  map_zpow (MonoidHom.snd Q (Multiplicative ℤ)) S.w k

theorem w_zpow_snd (k : ℤ) : (S.w ^ k).2 = Multiplicative.ofAdd (-2 * k) := by
  rw [w_zpow_snd']; exact zz_zpow k

/-- If `π(q, m) = π(h, m')` with `h ∈ H`, then `q ∈ H`. -/
theorem mem_of_π_eq {q h : Q} {m m' : Multiplicative ℤ} (hh : h ∈ S.H)
    (he : S.π (h, m') = S.π (q, m)) : q ∈ S.H := by
  obtain ⟨k, hk⟩ := S.π_eq.mp he
  have h1 := congrArg Prod.fst hk
  rw [w_zpow_fst, Prod.fst_mul, Prod.fst_inv] at h1
  have : q = h * (S.s : Q) ^ k := by rw [h1, mul_inv_cancel_left]
  rw [this]
  exact S.H.mul_mem hh (S.H.zpow_mem S.s.2 k)

/-- `H'' = H⟨ζ⟩`, the image of `H × ℤ`. -/
def H2 : Subgroup S.G := (S.H.prod ⊤).map S.π

theorem mem_H2 {x : S.G} : x ∈ S.H2 ↔ ∃ h ∈ S.H, ∃ m, S.π (h, m) = x := by
  constructor
  · rintro ⟨⟨h, m⟩, hp, rfl⟩
    exact ⟨h, (Subgroup.mem_prod.mp hp).1, m, rfl⟩
  · rintro ⟨h, hh, m, rfl⟩
    exact ⟨(h, m), Subgroup.mem_prod.mpr ⟨hh, Subgroup.mem_top _⟩, rfl⟩

theorem π_mem_H2 {h : Q} (hh : h ∈ S.H) (m : Multiplicative ℤ) : S.π (h, m) ∈ S.H2 :=
  S.mem_H2.mpr ⟨h, hh, m, rfl⟩

theorem nmem_H2 {q : Q} (hq : q ∉ S.H) (m : Multiplicative ℤ) : S.π (q, m) ∉ S.H2 := by
  intro hm
  obtain ⟨h, hh, m', he⟩ := S.mem_H2.mp hm
  exact hq (S.mem_of_π_eq hh he)

theorem π_comm_H2 {q : Q} (hq : ∀ h ∈ S.H, q * h = h * q) (m : Multiplicative ℤ) :
    ∀ x ∈ S.H2, S.π (q, m) * x = x * S.π (q, m) := by
  intro x hx
  obtain ⟨h, hh, m', rfl⟩ := S.mem_H2.mp hx
  rw [← _root_.map_mul, ← _root_.map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, hq h hh, mul_comm m]

/-! ## `G = H'' ∘ D₈` -/

/-- `a' = α ζ⁻¹`. -/
def a' : S.G := S.π (S.α, z⁻¹)

/-- `b' = β ζ^(-e)`. -/
def b' : S.G := S.π (S.β, z⁻¹ ^ S.e)

/-- `ζ`, the image of `(1, 1)`. -/
def ζ : S.G := S.π (1, z)

/-- The data for `CentralD8`. -/
def dihedral : DihedralData S.G where
  H := S.H2
  a := S.a'
  b := S.b'
  t := ⟨S.π (S.t, 1), S.π_mem_H2 S.t.2 1⟩
  ha := by
    rw [a', ← _root_.map_mul, Prod.mk_mul_mk, S.hα]
    have := S.π_w_zpow 1
    rw [zpow_one] at this
    exact this
  hb := by
    rw [b', ← _root_.map_mul, Prod.mk_mul_mk, S.hβ, ← mul_zpow]
    have : (((S.s : Q) ^ S.e, (z⁻¹ * z⁻¹) ^ S.e) : Q × Multiplicative ℤ) = S.w ^ S.e :=
      Prod.ext (S.w_zpow_fst _).symm (S.w_zpow_snd' _).symm
    rw [this, S.π_w_zpow]
  comm_a := S.π_comm_H2 S.comm_α _
  comm_b := S.π_comm_H2 S.comm_β _
  ht := by
    simp only [a', b', ← _root_.map_inv, ← _root_.map_mul, Prod.inv_mk, Prod.mk_mul_mk, ← S.ht]
    congr 2
    group
  gen := by
    intro x
    obtain ⟨⟨q, m⟩, rfl⟩ := QuotientGroup.mk'_surjective S.N x
    change ∃ h ∈ S.H2, S.π (q, m) = h ∨ S.π (q, m) = h * S.a' ∨ S.π (q, m) = h * S.b' ∨
      S.π (q, m) = h * (S.a' * S.b')
    obtain ⟨h, hh, hq | hq | hq | hq⟩ := S.gen q <;> subst q
    · exact ⟨_, S.π_mem_H2 hh m, Or.inl rfl⟩
    · refine ⟨_, S.π_mem_H2 hh (m * z), Or.inr (Or.inl ?_)⟩
      rw [a', ← _root_.map_mul, Prod.mk_mul_mk, mul_inv_cancel_right]
    · refine ⟨_, S.π_mem_H2 hh (m * z ^ S.e), Or.inr (Or.inr (Or.inl ?_))⟩
      rw [b', ← _root_.map_mul, Prod.mk_mul_mk, inv_zpow', mul_assoc, ← zpow_add, add_neg_cancel,
        zpow_zero, mul_one]
    · refine ⟨_, S.π_mem_H2 hh (m * z * z ^ S.e), Or.inr (Or.inr (Or.inr ?_))⟩
      rw [a', b', ← _root_.map_mul, ← _root_.map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk]
      congr 2
      rw [inv_zpow']
      group
  a_nmem := S.nmem_H2 S.α_nmem _
  b_nmem := S.nmem_H2 S.β_nmem _
  ab_nmem := by
    rw [a', b', ← _root_.map_mul, Prod.mk_mul_mk]
    exact S.nmem_H2 S.αβ_nmem _

/-- `H → H''`, `h ↦ π(h, 1)`. -/
def fK : S.H →* S.H2 :=
  (S.π.comp ((MonoidHom.inl Q (Multiplicative ℤ)).comp S.H.subtype)).codRestrict S.H2
    (fun h => S.π_mem_H2 h.2 1)

theorem dihedral_htc (htc : S.t ∈ commutator S.H) :
    S.dihedral.t ∈ commutator S.dihedral.H := by
  have h1 : S.fK S.t ∈ (commutator S.H).map S.fK := Subgroup.mem_map_of_mem S.fK htc
  rw [commutator_def, Subgroup.map_commutator] at h1
  have h2 := Subgroup.commutator_mono le_top le_top h1
  rw [← commutator_def] at h2
  exact h2

/-! ## `H'' = H⟨ζ⟩` with `ζ² = s` -/

theorem fK_injective : Function.Injective S.fK := by
  intro h h' he
  have he' : S.π ((h : Q), 1) = S.π ((h' : Q), 1) := congrArg Subtype.val he
  obtain ⟨k, hk⟩ := S.π_eq.mp he'
  have h2 := congrArg Prod.snd hk
  rw [w_zpow_snd, Prod.snd_mul, Prod.snd_inv, inv_one, one_mul] at h2
  have hk0 : k = 0 := by
    have := congrArg Multiplicative.toAdd h2
    simp only [toAdd_ofAdd, toAdd_one] at this
    omega
  subst hk0
  have h1 := congrArg Prod.fst hk
  rw [zpow_zero, Prod.fst_one, Prod.fst_mul, Prod.fst_inv] at h1
  exact Subtype.ext (inv_mul_eq_one.mp h1.symm)

theorem ζ_mem : S.ζ ∈ S.H2 := S.π_mem_H2 S.H.one_mem z

theorem ζ_central (x : S.G) : S.ζ * x = x * S.ζ := by
  obtain ⟨⟨q, m⟩, rfl⟩ := QuotientGroup.mk'_surjective S.N x
  change S.π (1, z) * S.π (q, m) = S.π (q, m) * S.π (1, z)
  rw [← _root_.map_mul, ← _root_.map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one,
    mul_comm z]

theorem ζζ : S.ζ * S.ζ = S.π ((S.s : Q), 1) := by
  rw [ζ, ← _root_.map_mul, Prod.mk_mul_mk, one_mul, S.π_eq]
  refine ⟨1, Prod.ext ?_ ?_⟩
  · rw [zpow_one, Prod.fst_mul, Prod.fst_inv, inv_one, one_mul]; rfl
  · rw [zpow_one, Prod.snd_mul, Prod.snd_inv, mul_one, mul_inv]; rfl

/-- `H → H_K`, an isomorphism (`φ`). -/
noncomputable def φ : S.H ≃* S.fK.range := MonoidHom.ofInjective S.fK_injective

/-- The data for `CentralSqrt`: `K = H''`, base `H`, `r = ζ`, and `g`. -/
noncomputable def sqrt (g : S.H) : SqrtData S.H2 where
  H := S.fK.range
  r := ⟨S.ζ, S.ζ_mem⟩
  g := S.φ g
  central x := Subtype.ext (S.ζ_central x)
  sq_mem := ⟨S.s, Subtype.ext S.ζζ.symm⟩
  r_nmem := by
    rintro ⟨h, hh⟩
    have he : S.π ((h : Q), 1) = S.π (1, z) := congrArg Subtype.val hh
    obtain ⟨k, hk⟩ := S.π_eq.mp he
    have h2 := congrArg Prod.snd hk
    rw [w_zpow_snd, Prod.snd_mul, Prod.snd_inv, inv_one, one_mul] at h2
    have := congrArg Multiplicative.toAdd h2
    simp only [z, toAdd_ofAdd] at this
    omega
  gen := by
    rintro ⟨x, hx⟩
    obtain ⟨h, hh, m, rfl⟩ := S.mem_H2.mp hx
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (Multiplicative.toAdd m)
    · refine ⟨S.fK ⟨h * (S.s : Q) ^ j, S.H.mul_mem hh (S.H.zpow_mem S.s.2 j)⟩,
        ⟨_, rfl⟩, Or.inl (Subtype.ext ?_)⟩
      show S.π (h, m) = S.π (h * (S.s : Q) ^ j, 1)
      rw [S.π_eq]
      refine ⟨j, Prod.ext ?_ ?_⟩
      · rw [w_zpow_fst, Prod.fst_mul, Prod.fst_inv, inv_mul_cancel_left]
      · rw [w_zpow_snd, Prod.snd_mul, Prod.snd_inv, mul_one]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd, toAdd_inv, hj]
        ring
    · refine ⟨S.fK ⟨h * (S.s : Q) ^ j, S.H.mul_mem hh (S.H.zpow_mem S.s.2 j)⟩,
        ⟨_, rfl⟩, Or.inr (Subtype.ext ?_)⟩
      show S.π (h, m) = S.π (h * (S.s : Q) ^ j, 1) * S.π (1, z)
      rw [← _root_.map_mul, Prod.mk_mul_mk, mul_one, one_mul, S.π_eq]
      refine ⟨j, Prod.ext ?_ ?_⟩
      · rw [w_zpow_fst, Prod.fst_mul, Prod.fst_inv, inv_mul_cancel_left]
      · rw [w_zpow_snd, Prod.snd_mul, Prod.snd_inv]
        apply Multiplicative.toAdd.injective
        simp only [z, toAdd_ofAdd, toAdd_inv, toAdd_mul, hj]
        ring

theorem sqrt_c (g : S.H) : (S.sqrt g).c = S.φ (g⁻¹ * g⁻¹ * S.s) := by
  have hs : (S.sqrt g).s = S.φ S.s := Subtype.ext (Subtype.ext S.ζζ)
  rw [SqrtData.c, hs, _root_.map_mul, _root_.map_mul, _root_.map_inv]
  rfl

-- `ℤ[H_K]` for a subgroup of a subgroup of a quotient: instance search needs more room.
set_option synthInstance.maxHeartbeats 200000 in
theorem sqrt_hc (g : S.H)
    (hc : ∀ j : ℕ, of ℤ S.H ((g⁻¹ * g⁻¹ * S.s) ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2)) (j : ℕ) :
    of ℤ S.fK.range ((S.sqrt g).c ^ 2 ^ j) - 1 ∈ augIdeal S.fK.range ^ (j + 2) := by
  have := mapDomain_mem_augIdeal_pow S.φ.toMonoidHom (j + 2) (hc j)
  rw [_root_.map_sub, _root_.map_one, mapDomainRingHom_of] at this
  rw [sqrt_c]
  convert this using 3

/-- `Q → G`, `q ↦ π(q, 0)`; injective by `mem_of_π_eq`. -/
def ιQ : Q →* S.G := S.π.comp (MonoidHom.inl Q _)

/-- `[Q, Q] ≤ H`: the image of `[Q, Q]` lies in `[G, G] ≤ H''`, whose preimage is `H`. -/
theorem commutator_le : commutator Q ≤ S.H := by
  intro q hq
  have h1 : S.ιQ q ∈ (commutator Q).map S.ιQ := Subgroup.mem_map_of_mem S.ιQ hq
  rw [commutator_def, Subgroup.map_commutator] at h1
  have h2 := S.dihedral.commutator_le
    (by rw [commutator_def]; exact Subgroup.commutator_mono le_top le_top h1)
  obtain ⟨h, hh, m, he⟩ := S.mem_H2.mp h2
  exact S.mem_of_π_eq (q := q) (m := 1) hh he

-- `ℤ[H_K]` for a subgroup of a subgroup of a quotient: instance search needs more room, and the
-- elaboration of the three `mapDomain`s below more time.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
/-- `ℤ[H] ∩ Δ(Q)^n ⊆ Δ(H)^n`, through `ℤ[H] → ℤ[H''] → ℤ[G]`. -/
theorem mem_pow_of_iota (htc : S.t ∈ commutator S.H) (g : S.H)
    (hc : ∀ j : ℕ, of ℤ S.H ((g⁻¹ * g⁻¹ * S.s) ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2))
    (n : ℕ) (x : MonoidAlgebra ℤ S.H)
    (hx : mapDomainRingHom ℤ S.H.subtype x ∈ augIdeal Q ^ n) : x ∈ augIdeal S.H ^ n := by
  have key : ∀ x : MonoidAlgebra ℤ S.H, mapDomainRingHom ℤ S.H2.subtype
      (mapDomainRingHom ℤ S.fK.range.subtype (mapDomainRingHom ℤ S.φ.toMonoidHom x)) =
        mapDomainRingHom ℤ S.ιQ (mapDomainRingHom ℤ S.H.subtype x) := by
    intro x
    induction x using CentralRoot.induction_of with
    | h0 => simp only [_root_.map_zero]
    | hof h => simp only [mapDomainRingHom_of]; rfl
    | hneg y hy => simp only [_root_.map_neg, hy]
    | hadd y z hy hz => simp only [_root_.map_add, hy, hz]
  have back : ∀ x : MonoidAlgebra ℤ S.H,
      mapDomainRingHom ℤ S.φ.symm.toMonoidHom (mapDomainRingHom ℤ S.φ.toMonoidHom x) = x := by
    intro x
    induction x using CentralRoot.induction_of with
    | h0 => simp only [_root_.map_zero]
    | hof h => simp [mapDomainRingHom_of]
    | hneg y hy => simp only [_root_.map_neg, hy]
    | hadd y z hy hz => simp only [_root_.map_add, hy, hz]
  have hx1 : mapDomainRingHom ℤ S.H2.subtype (mapDomainRingHom ℤ S.fK.range.subtype
      (mapDomainRingHom ℤ S.φ.toMonoidHom x)) ∈ augIdeal S.G ^ n := by
    rw [key]
    exact mapDomain_mem_augIdeal_pow S.ιQ n hx
  have hx2 := (S.dihedral.iota_mem_augIdeal_pow_iff (S.dihedral_htc htc) n _).mp hx1
  have hx3 := ((S.sqrt g).iota_mem_augIdeal_pow_iff (S.sqrt_hc g hc) n _).mp hx2
  rw [← back x]
  exact mapDomain_mem_augIdeal_pow S.φ.symm.toMonoidHom n hx3

/-- **Proposition 5.8**, general form, ring statement: `ℤ[H] ∩ Δ(Q)^n = Δ(H)^n`. -/
theorem iota_mem_augIdeal_pow_iff (htc : S.t ∈ commutator S.H) (g : S.H)
    (hc : ∀ j : ℕ, of ℤ S.H ((g⁻¹ * g⁻¹ * S.s) ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2))
    (n : ℕ) (x : MonoidAlgebra ℤ S.H) :
    mapDomainRingHom ℤ S.H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal S.H ^ n :=
  ⟨S.mem_pow_of_iota htc g hc n x, mapDomain_mem_augIdeal_pow S.H.subtype n⟩

/-- **Proposition 5.8**, general form: `D_n(Q) = D_n(H)` for `n ≥ 2`. -/
theorem D_eq (htc : S.t ∈ commutator S.H) (g : S.H)
    (hc : ∀ j : ℕ, of ℤ S.H ((g⁻¹ * g⁻¹ * S.s) ^ 2 ^ j) - 1 ∈ augIdeal S.H ^ (j + 2))
    (n : ℕ) (hn : 2 ≤ n) : D n Q = (D n S.H).map S.H.subtype :=
  D_eq_of_mem_pow S.H S.commutator_le (S.mem_pow_of_iota htc g hc) n hn

end CentralProductData

/-! ## The statements of the paper -/

theorem augIdeal_of_commutator {H : Type*} [Group H] {t : H} (htc : t ∈ commutator H) :
    of ℤ H t - 1 ∈ augIdeal H ^ 2 := by
  have : t ∈ D 2 H := by rw [D_two, lowerCentralSeries_one]; exact htc
  exact mem_D.mp this

/-- **Proposition 5.8, general form.** `H ≤ Q`, `α, β ∈ Q` commuting with `H`,
`Q = H ⊔ Hα ⊔ Hβ ⊔ Hαβ`, `s = α² ∈ H`, `β² = s^e`, `t = [α, β] ∈ γ₂(H)`, and for some `g ∈ H`
the element `c = g⁻² s` has `c^(2^j) - 1 ∈ Δ(H)^(j+2)` for all `j ≥ 0`. Then
`ℤ[H] ∩ Δ(Q)^n = Δ(H)^n` for all `n` and `D_n(Q) = D_n(H)` for `n ≥ 2`. -/
theorem D_n_eq_of_central_product {Q : Type*} [Group Q] (H : Subgroup Q) (α β : Q)
    (s t g : H) (e : ℤ) (comm_α : ∀ h ∈ H, α * h = h * α) (comm_β : ∀ h ∈ H, β * h = h * β)
    (hα : α * α = s) (hβ : β * β = (s : Q) ^ e) (ht : (t : Q) = α * β * α⁻¹ * β⁻¹)
    (htc : t ∈ commutator H)
    (gen : ∀ q : Q, ∃ h ∈ H, q = h ∨ q = h * α ∨ q = h * β ∨ q = h * (α * β))
    (α_nmem : α ∉ H) (β_nmem : β ∉ H) (αβ_nmem : α * β ∉ H)
    (hc : ∀ j : ℕ, of ℤ H ((g⁻¹ * g⁻¹ * s) ^ 2 ^ j) - 1 ∈ augIdeal H ^ (j + 2)) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n Q = (D n H).map H.subtype :=
  let S : CentralProductData Q :=
    ⟨H, α, β, s, t, e, comm_α, comm_β, hα, hβ, ht, gen, α_nmem, β_nmem, αβ_nmem⟩
  ⟨S.iota_mem_augIdeal_pow_iff htc g hc, S.D_eq htc g hc⟩

/-- **Proposition 5.8(1), `E = Q₈`.** `α² = β² = [α, β] = t ∈ γ₂(H)`. -/
theorem D_n_eq_of_quaternion {Q : Type*} [Group Q] (H : Subgroup Q) (α β : Q) (t : H)
    (comm_α : ∀ h ∈ H, α * h = h * α) (comm_β : ∀ h ∈ H, β * h = h * β)
    (hα : α * α = t) (hβ : β * β = t) (ht : (t : Q) = α * β * α⁻¹ * β⁻¹)
    (htc : t ∈ commutator H)
    (gen : ∀ q : Q, ∃ h ∈ H, q = h ∨ q = h * α ∨ q = h * β ∨ q = h * (α * β))
    (α_nmem : α ∉ H) (β_nmem : β ∉ H) (αβ_nmem : α * β ∉ H) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n Q = (D n H).map H.subtype := by
  -- `t² = 1`: `β t β⁻¹ = (β α β⁻¹)² = (t⁻¹ α)² = t⁻¹`
  have h1 : β * α * β⁻¹ = (t : Q)⁻¹ * α := by rw [ht]; group
  have hct : α * (t : Q)⁻¹ = (t : Q)⁻¹ * α := comm_α _ (H.inv_mem t.2)
  have htt : (t : Q) = (t : Q)⁻¹ := by
    calc (t : Q) = β * t * β⁻¹ := by rw [comm_β _ t.2, mul_inv_cancel_right]
      _ = (β * α * β⁻¹) * (β * α * β⁻¹) := by rw [← hα]; group
      _ = (t : Q)⁻¹ * (α * (t : Q)⁻¹) * α := by rw [h1]; group
      _ = (t : Q)⁻¹ * (t : Q)⁻¹ * (α * α) := by rw [hct]; group
      _ = (t : Q)⁻¹ := by rw [hα]; group
  have ht2 : t ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one, mul_eq_one_iff_eq_inv]; exact htt)
  refine D_n_eq_of_central_product H α β t t 1 1 comm_α comm_β hα (by rw [zpow_one]; exact hβ)
    ht htc gen α_nmem β_nmem αβ_nmem ?_
  intro j
  rw [inv_one, one_mul, one_mul]
  rcases j with _ | j
  · rw [pow_zero, pow_one]; exact augIdeal_of_commutator htc
  · rw [pow_succ', pow_mul, ht2, one_pow, _root_.map_one, sub_self]; exact zero_mem _

/-- **Proposition 5.8(2), `s = g²`.** `E = M_{2^{k+2}}` (or any `E` with `β² = 1`) and
`s = g²` for some `g ∈ H`, central or not. -/
theorem D_n_eq_of_modular_sq {Q : Type*} [Group Q] (H : Subgroup Q) (α β : Q) (t g : H)
    (comm_α : ∀ h ∈ H, α * h = h * α) (comm_β : ∀ h ∈ H, β * h = h * β)
    (hα : α * α = ((g * g : H) : Q)) (hβ : β * β = 1) (ht : (t : Q) = α * β * α⁻¹ * β⁻¹)
    (htc : t ∈ commutator H)
    (gen : ∀ q : Q, ∃ h ∈ H, q = h ∨ q = h * α ∨ q = h * β ∨ q = h * (α * β))
    (α_nmem : α ∉ H) (β_nmem : β ∉ H) (αβ_nmem : α * β ∉ H) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n Q = (D n H).map H.subtype := by
  refine D_n_eq_of_central_product H α β (g * g) t g 0 comm_α comm_β hα
    (by rw [zpow_zero]; exact hβ) ht htc gen α_nmem β_nmem αβ_nmem ?_
  intro j
  rw [show g⁻¹ * g⁻¹ * (g * g) = 1 by group, one_pow, _root_.map_one, sub_self]
  exact zero_mem _

/-- **Proposition 5.8(2), `s ∈ γ₂(H)`, `s² ∈ γ₃(H)`, `s⁴ = 1`** (`g = 1`; the case `k = 2`,
`E = M₁₆`). -/
theorem D_n_eq_of_modular_comm {Q : Type*} [Group Q] (H : Subgroup Q) (α β : Q) (s t : H)
    (comm_α : ∀ h ∈ H, α * h = h * α) (comm_β : ∀ h ∈ H, β * h = h * β)
    (hα : α * α = s) (hβ : β * β = 1) (ht : (t : Q) = α * β * α⁻¹ * β⁻¹)
    (htc : t ∈ commutator H) (hs : s ∈ commutator H) (hs2 : s * s ∈ lowerCentralSeries H 2)
    (hs4 : s ^ 4 = 1)
    (gen : ∀ q : Q, ∃ h ∈ H, q = h ∨ q = h * α ∨ q = h * β ∨ q = h * (α * β))
    (α_nmem : α ∉ H) (β_nmem : β ∉ H) (αβ_nmem : α * β ∉ H) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n Q = (D n H).map H.subtype := by
  refine D_n_eq_of_central_product H α β s t 1 0 comm_α comm_β hα
    (by rw [zpow_zero]; exact hβ) ht htc gen α_nmem β_nmem αβ_nmem ?_
  intro j
  rw [inv_one, one_mul, one_mul]
  rcases j with _ | _ | j
  · rw [pow_zero, pow_one]; exact augIdeal_of_commutator hs
  · rw [zero_add, pow_one, pow_two]
    exact mem_D.mp (lowerCentralSeries_le_D H 2 hs2)
  · rw [show 2 ^ (j + 2) = 4 * 2 ^ j by ring, pow_mul, hs4, one_pow, _root_.map_one, sub_self]
    exact zero_mem _

/-- **Proposition 5.8(2), "for instance"**: `c = g⁻² s` with `c^(2^j) ∈ γ_{j+2}(H)` for all `j`
(`lowerCentralSeries H (j + 1) = γ_{j+2}(H)`). -/
theorem D_n_eq_of_central_product_of_gamma {Q : Type*} [Group Q] (H : Subgroup Q) (α β : Q)
    (s t g : H) (e : ℤ) (comm_α : ∀ h ∈ H, α * h = h * α) (comm_β : ∀ h ∈ H, β * h = h * β)
    (hα : α * α = s) (hβ : β * β = (s : Q) ^ e) (ht : (t : Q) = α * β * α⁻¹ * β⁻¹)
    (htc : t ∈ commutator H)
    (gen : ∀ q : Q, ∃ h ∈ H, q = h ∨ q = h * α ∨ q = h * β ∨ q = h * (α * β))
    (α_nmem : α ∉ H) (β_nmem : β ∉ H) (αβ_nmem : α * β ∉ H)
    (hγ : ∀ j : ℕ, (g⁻¹ * g⁻¹ * s) ^ 2 ^ j ∈ lowerCentralSeries H (j + 1)) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal Q ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n Q = (D n H).map H.subtype :=
  D_n_eq_of_central_product H α β s t g e comm_α comm_β hα hβ ht htc gen α_nmem β_nmem αβ_nmem
    (fun j => mem_D.mp (lowerCentralSeries_le_D H (j + 1) (hγ j)))

end GroupDimension
