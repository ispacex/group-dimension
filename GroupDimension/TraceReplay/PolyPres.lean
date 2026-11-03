module

public import GroupDimension.TraceReplay.PolyExact
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

/-!
# Polynomial maps of a presented group from a finite check (MATH-314, docs §3.2(e), point 1)

`check_mem_D_poly_lin` takes as a hypothesis (`IsBase`) that each base map `(w, λ)` is a polynomial
map of `G` of degree `≤ w` with the values `λ` on the monomials. Here that hypothesis is derived,
for a presented group `G = F/⟨⟨rels⟩⟩`, from identities in the truncated free algebra
`A = ℤ⟨X⟩ / (degree ≥ w + 1)`:

  `λ(u · (μ(r) − 1) · v) = 0` for every relator `r` and all monomials `u`, `v`  (`hvan`),

where `μ : F → Aˣ`, `x_j ↦ 1 + X_j`, is the Magnus map. This is check 1 of §3.2(e), which
`check_trace --polymaps` performs. Then `φ(g) = λ(μ(ĝ))` (`ĝ` any preimage) is well defined on `G`,
`φ(ψ X_u) = λ(X_u)`, and `φ` vanishes on `Δ^{w+1}` because `μ(ĝ) − 1` has no constant term
(`isBase_of_vanish`). No direction of §3.1 beyond this one is used.
-/

namespace GroupDimension.TraceReplay

open MonoidAlgebra

section Trunc

variable {d : ℕ} [NeZero d]

/-- `I_k` as a two-sided ideal. -/
def IkI (k : ℕ) : Ideal (R d) where
  carrier := Ik d k
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c _ hx := mem_Ik_mul hx c

instance IkI_isTwoSided (k : ℕ) : (IkI (d := d) k).IsTwoSided := ⟨fun b ha => mul_mem_Ik ha b⟩

theorem mem_IkI {k : ℕ} {x : R d} : x ∈ IkI k ↔ x ∈ Ik d k := Iff.rfl

/-- `A_k = ℤ⟨X⟩ / I_k`. -/
abbrev Ak (d k : ℕ) [NeZero d] := R d ⧸ IkI (d := d) k

/-- `I_i · I_j ⊆ I_{i+j}`. -/
theorem mul_mem_Ik_add {i j : ℕ} {x y : R d} (hx : x ∈ Ik d i) (hy : y ∈ Ik d j) :
    x * y ∈ Ik d (i + j) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨v, hv, rfl⟩ := hb
      rw [single_mul_single, one_mul]
      exact single_mem_Ik (by rw [FreeMonoid.length_mul]; omega) _
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

theorem X_pow_mem_Ik (k j : ℕ) : (X (d := d) j) ^ k ∈ Ik d k := by
  rw [X, single_pow, one_pow]
  exact single_mem_Ik (by rw [length_pow_of]) _

theorem isNilpotent_X (k j : ℕ) : IsNilpotent (Ideal.Quotient.mk (IkI (d := d) k) (X j)) :=
  ⟨k, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact X_pow_mem_Ik k j⟩

/-- `1 + X_j` as a unit of `A_k`. -/
noncomputable def unitX (k j : ℕ) : (Ak d k)ˣ := (isNilpotent_X k j).isUnit_one_add.unit

/-- The Magnus map `F → A_kˣ`, `x_j ↦ 1 + X_j`. -/
noncomputable def muA (k : ℕ) : FreeGroup (Fin d) →* (Ak d k)ˣ := FreeGroup.lift fun j => unitX k j

theorem muA_of (k : ℕ) (j : Fin d) :
    ((muA k (FreeGroup.of j) : (Ak d k)ˣ) : Ak d k) = Ideal.Quotient.mk _ (1 + X j) := by
  rw [muA, FreeGroup.lift_apply_of, unitX, IsUnit.unit_spec, map_add, map_one]

/-- The image of `I_1` (no constant term). -/
def Pos (k : ℕ) : Set (Ak d k) := {a | ∃ y ∈ Ik d 1, Ideal.Quotient.mk _ y = a}

theorem muA_sub_one_mem (k : ℕ) (x : FreeGroup (Fin d)) :
    ((muA k x : (Ak d k)ˣ) : Ak d k) - 1 ∈ Pos k := by
  let T : Subgroup (FreeGroup (Fin d)) :=
    { carrier := {x | ((muA k x : (Ak d k)ˣ) : Ak d k) - 1 ∈ Pos k}
      mul_mem' := by
        intro x y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩
        refine ⟨a * b + a + b, add_mem (add_mem (mul_mem_Ik ha b) ha) hb, ?_⟩
        rw [map_add, map_add, map_mul, ea, eb, map_mul, Units.val_mul]; noncomm_ring
      one_mem' := ⟨0, zero_mem _, by rw [map_zero, map_one, Units.val_one, sub_self]⟩
      inv_mem' := by
        intro x ⟨a, ha, ea⟩
        obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (((muA k x⁻¹ : (Ak d k)ˣ) : Ak d k))
        refine ⟨-(c * a), neg_mem (mem_Ik_mul ha c), ?_⟩
        show _ = ((muA k x⁻¹ : (Ak d k)ˣ) : Ak d k) - 1
        rw [map_neg, map_mul, hc, ea, map_inv, mul_sub, Units.inv_mul, mul_one]; abel }
  have hgen : ∀ j, FreeGroup.of j ∈ T := fun j =>
    ⟨X j, single_mem_Ik (by simp) _, by rw [muA_of, map_add, map_one, add_sub_cancel_left]⟩
  have : T = ⊤ := by
    rw [eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩; exact hgen j
  exact (this ▸ Subgroup.mem_top x : x ∈ T)

theorem prod_Pos_eq_zero (k : ℕ) (l : List (Ak d k)) (hl : ∀ a ∈ l, a ∈ Pos k) :
    ∃ y ∈ Ik d l.length, Ideal.Quotient.mk _ y = l.prod := by
  induction l with
  | nil => exact ⟨1, by rw [List.length_nil]; exact single_mem_Ik (by simp) _, by rw [map_one]; rfl⟩
  | cons a l ih =>
    obtain ⟨y, hy, ey⟩ := hl a List.mem_cons_self
    obtain ⟨z, hz, ez⟩ := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨y * z, ?_, by rw [map_mul, ey, ez, List.prod_cons]⟩
    have := mul_mem_Ik_add hy hz
    rwa [List.length_cons, add_comm] at this ⊢

end Trunc

section Lam

variable {d : ℕ} [NeZero d]

/-- The value of a base map `(w, λ)` on a monomial. -/
def lamW (m : ℕ × List ℤ) (u : FreeMonoid (Fin d)) : ℤ :=
  if 1 ≤ u.length ∧ u.length ≤ m.1 then m.2.getD (posN d (u.toList.map (·.val)) - 1) 0 else 0

/-- `λ` on `ℤ⟨X⟩`. -/
noncomputable def lamR (m : ℕ × List ℤ) : R d →+ ℤ :=
  (Finsupp.linearCombination ℤ (lamW m)).toAddMonoidHom.comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem lamR_single (m : ℕ × List ℤ) (u : FreeMonoid (Fin d)) (a : ℤ) :
    lamR m (single u a) = a * lamW m u := by
  show Finsupp.linearCombination ℤ (lamW m) (Finsupp.single u a) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem lamR_Ik (m : ℕ × List ℤ) {x : R d} (hx : x ∈ Ik d (m.1 + 1)) : lamR m x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    rw [lamR_single, lamW, if_neg (by omega), mul_zero]
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_zsmul, hy, smul_zero]

/-- `λ` on `A_{w+1}`. -/
noncomputable def lamA (m : ℕ × List ℤ) : Ak d (m.1 + 1) →+ ℤ :=
  QuotientAddGroup.lift (IkI (d := d) (m.1 + 1)).toAddSubgroup (lamR m) fun _ hx => lamR_Ik m hx

theorem lamA_mk (m : ℕ × List ℤ) (x : R d) : lamA m (Ideal.Quotient.mk _ x) = lamR m x := rfl

end Lam

section Pres

variable {d : ℕ} [NeZero d] (rels : Set (FreeGroup (Fin d))) (m : ℕ × List ℤ)

local notation "A" => Ak d (m.1 + 1)

/-- The elements of `F` that `λ` cannot see inside a product. -/
def invisible : Subgroup (FreeGroup (Fin d)) where
  carrier := {x | ∀ a b : A, lamA m (a * (muA _ x : A) * b) = lamA m (a * b)}
  mul_mem' := by
    intro x y hx hy a b
    rw [map_mul, Units.val_mul, ← mul_assoc, hy, hx]
  one_mem' := by intro a b; rw [map_one, Units.val_one, mul_one]
  inv_mem' := by
    intro x hx a b
    have := hx (a * (muA _ x⁻¹ : A)) b
    rw [mul_assoc a, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one] at this
    exact this.symm

instance invisible_normal : (invisible m).Normal where
  conj_mem x hx c a b := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    have := hx (a * (muA _ c : A)) ((muA _ c⁻¹ : A) * b)
    simp only [mul_assoc] at this ⊢
    rw [this, ← mul_assoc ((muA _ c : A)), ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, one_mul]

/-- Check 1 of §3.2(e) for `(w, λ)`: `λ(X_u · (μ(r) − 1) · X_v) = 0` in `A_{w+1}` for every relator
`r` and all monomials `u`, `v`. -/
def Vanish : Prop :=
  ∀ r ∈ rels, ∀ u v : FreeMonoid (Fin d),
    lamA m (Ideal.Quotient.mk _ (single u 1) * ((muA _ r : A) - 1) * Ideal.Quotient.mk _ (single v 1)) = 0

variable {rels m}

theorem vanish_all (hvan : Vanish rels m)
    {r : FreeGroup (Fin d)} (hr : r ∈ rels) (a b : A) : lamA m (a * ((muA _ r : A) - 1) * b) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction a using MonoidAlgebra.induction_on with
  | of u =>
    induction b using MonoidAlgebra.induction_on with
    | of v => exact hvan r hr u v
    | add x y hx hy => rw [map_add, mul_add, map_add, hx, hy, add_zero]
    | smul c x hx => rw [map_zsmul, mul_smul_comm, map_zsmul, hx, smul_zero]
  | add x y hx hy => rw [map_add, add_mul, add_mul, map_add, hx, hy, add_zero]
  | smul c x hx => rw [map_zsmul, smul_mul_assoc, smul_mul_assoc, map_zsmul, hx, smul_zero]

theorem normalClosure_le_invisible (hvan : Vanish rels m) :
    Subgroup.normalClosure rels ≤ invisible m := by
  refine Subgroup.normalClosure_le_normal fun r hr a b => ?_
  have := vanish_all hvan hr a b
  rw [mul_sub, sub_mul, mul_one, map_sub, sub_eq_zero] at this
  exact this

/-- `φ_a(ĝ) = λ(a · μ(ĝ))` on `G = F/⟨⟨rels⟩⟩`. -/
noncomputable def phiA (hvan : Vanish rels m)
    (a : A) : PresentedGroup rels → ℤ :=
  fun q => Quotient.liftOn' q (fun x => lamA m (a * (muA _ x : A))) fun x y hxy => by
    have hn : x⁻¹ * y ∈ invisible m :=
      normalClosure_le_invisible hvan (QuotientGroup.leftRel_apply.mp hxy)
    have e : y = x * (x⁻¹ * y) := by group
    show lamA m (a * (muA _ x : A)) = lamA m (a * (muA _ y : A))
    rw [e, map_mul, Units.val_mul, ← mul_assoc]
    have := hn (a * (muA _ x : A)) 1
    rw [mul_one, mul_one] at this
    exact this.symm

theorem phiA_mk (hvan : Vanish rels m) (a : A) (x : FreeGroup (Fin d)) :
    phiA hvan a (PresentedGroup.mk rels x) = lamA m (a * (muA _ x : A)) := rfl

/-- Translation: `φ_a(x̂ q) = φ_{a μ(x)}(q)`. -/
theorem phiA_mul (hvan : Vanish rels m) (a : A) (x : FreeGroup (Fin d)) (q : PresentedGroup rels) :
    phiA hvan a (PresentedGroup.mk rels x * q) = phiA hvan (a * (muA _ x : A)) q := by
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [show (QuotientGroup.mk y : PresentedGroup rels) = PresentedGroup.mk rels y from rfl, ← map_mul,
      phiA_mk, phiA_mk, map_mul, Units.val_mul, mul_assoc]

/-- `lin φ_a (E (l̂)) = λ(a · Π (μ(x) − 1))`. -/
theorem lin_phiA_E (hvan : Vanish rels m) (l : List (FreeGroup (Fin d))) (a : A) :
    lin (phiA hvan a) (E (l.map (PresentedGroup.mk rels))) =
      lamA m (a * (l.map fun x => (muA _ x : A) - 1).prod) := by
  induction l generalizing a with
  | nil =>
    rw [List.map_nil, E_nil, lin_one, List.map_nil, List.prod_nil, mul_one, ← map_one (PresentedGroup.mk rels),
      phiA_mk, map_one, Units.val_one, mul_one]
  | cons x l ih =>
    rw [List.map_cons, E_cons, sub_mul, one_mul, map_sub, lin_of_mul,
      show (fun h => phiA hvan a (PresentedGroup.mk rels x * h)) = phiA hvan (a * (muA _ x : A)) from
        funext (phiA_mul hvan a x),
      ih, ih, List.map_cons, List.prod_cons, ← map_sub]
    congr 1; noncomm_ring

theorem exists_lift (l : List (PresentedGroup rels)) :
    ∃ l' : List (FreeGroup (Fin d)), l'.map (PresentedGroup.mk rels) = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons q l ih =>
    obtain ⟨l', rfl⟩ := ih
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x :: l', rfl⟩

theorem prod_muA_letters (u : List ℕ) :
    (u.map fun j => ((muA (m.1 + 1) (FreeGroup.of (letter d j)) : A) - 1)).prod =
      Ideal.Quotient.mk _ (single (FreeMonoid.ofList (u.map (letter d))) 1) := by
  induction u with
  | nil => rw [List.map_nil, List.prod_nil, List.map_nil, FreeMonoid.ofList_nil, ← one_def, map_one]
  | cons j u ih =>
    rw [List.map_cons, List.prod_cons, ih, muA_of, map_add, map_one, add_sub_cancel_left, X, letter_val,
      ← map_mul, single_mul_single, one_mul, List.map_cons, FreeMonoid.ofList_cons]

/-- **The base maps of a presented group.** If `λ` passes check 1 (`Vanish`), then
`φ(ĝ) = λ(μ(ĝ))` is a polynomial map of `G = F/⟨⟨rels⟩⟩` of degree `≤ w` with the values `λ`. -/
theorem isBase_of_vanish (hvan : Vanish rels m) :
    IsBase (fun j : Fin d => (PresentedGroup.of j : PresentedGroup rels)) m (phiA hvan 1) := by
  refine ⟨?_, fun x hx => ?_, fun u hu h1 hw => ?_⟩
  · rw [← map_one (PresentedGroup.mk rels), phiA_mk, map_one, Units.val_one, mul_one, ← map_one
      (Ideal.Quotient.mk _), lamA_mk, one_def, lamR_single, lamW, if_neg (by simp), mul_zero]
  · have hs := pow_le_spanE (G := PresentedGroup rels) m.1 (show x ∈ (augIdeal _ ^ (m.1 + 1)).restrictScalars ℤ from hx)
    clear hx
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨l', rfl⟩ := exists_lift l
      rw [lin_phiA_E, one_mul]
      obtain ⟨z, hz, ez⟩ := prod_Pos_eq_zero (m.1 + 1) (l'.map fun x => (muA _ x : A) - 1)
        (fun b hb => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb; exact muA_sub_one_mem _ x)
      rw [← ez, lamA_mk]
      refine lamR_Ik m ?_
      rw [List.length_map] at hz hl
      rwa [hl] at hz
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_zsmul, hy, smul_zero]
  · have e : u.map (gN (fun j : Fin d => (PresentedGroup.of j : PresentedGroup rels))) =
        (u.map fun j => FreeGroup.of (letter d j)).map (PresentedGroup.mk rels) := by
      rw [List.map_map]; rfl
    rw [e, lin_phiA_E, List.map_map, one_mul]
    rw [show ((fun x => ((muA (m.1 + 1) x : A) - 1)) ∘ fun j => FreeGroup.of (letter d j)) =
      fun j => ((muA (m.1 + 1) (FreeGroup.of (letter d j)) : A) - 1) from rfl, prod_muA_letters, lamA_mk,
      lamR_single, one_mul, lamW]
    have hl : (FreeMonoid.ofList (u.map (letter d))).length = u.length := by simp
    have hv : (FreeMonoid.ofList (u.map (letter d))).toList.map (·.val) = u := by
      rw [FreeMonoid.toList_ofList, List.map_map]
      conv_rhs => rw [← List.map_id u]
      exact List.map_congr_left fun j hj => letter_of_lt (hu j hj)
    rw [if_pos (by rw [hl]; exact ⟨h1, hw⟩), hv]

end Pres

/-- **Exact membership in a presented group, polynomial maps of any weight.** If `check` accepts the
trace, `checkPoly` the certificate, every relator of the trace is one of `allRels`, and every base map
passes check 1 against `allRels` (`hvan`), then in `G = ⟨x_1, …, x_d | allRels⟩` every word test
claimed whose element has `p`-power order in `Δ/Δ^n` (`hord`) lies in `D_n(G)`. -/
theorem check_mem_D_poly_pres (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (P : PolyCert) (hP : checkPoly T P = true) (allRels : List (List (ℕ × ℤ)))
    (hsub : T.rels.all (fun r => allRels.any (fun r' => r' == r.2)) = true)
    (hvan : ∀ i < P.maps.length, Vanish (relSet T.d allRels) (P.maps.getD i (0, [])))
    (t : ℕ) (ht : t ∈ members) (hw : T.tests.any (fun y => y.1 == t) = true)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) •
      (of ℤ (PresentedGroup (relSet T.d allRels))
        (gword (PresentedGroup.of (rels := relSet T.d allRels)) (findWord t T.tests)) - 1) ∈
      augIdeal (PresentedGroup (relSet T.d allRels)) ^ T.n) :
    gword (PresentedGroup.of (rels := relSet T.d allRels)) (findWord t T.tests) ∈
      GroupDimension.D T.n (PresentedGroup (relSet T.d allRels)) := by
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hsub
  refine check_mem_D_poly T members hc P hP (PresentedGroup.of (rels := relSet T.d allRels)) ?_
    (PresentedGroup.closure_range_of _) (fun i hi => ⟨_, isBase_of_vanish (hvan i hi)⟩) t ht hw hord
  intro r hr
  obtain ⟨r', hr', hrr⟩ := hsub r hr
  have e : (PresentedGroup.of : Fin T.d → PresentedGroup (relSet T.d allRels)) =
      PresentedGroup.mk _ ∘ FreeGroup.of := rfl
  rw [e, ← map_gword]
  exact PresentedGroup.one_of_mem ⟨r', hr', by rw [hrr]⟩

end GroupDimension.TraceReplay
