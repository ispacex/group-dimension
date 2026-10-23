module

public import GroupDimension.Cert1024.Nilpotent
public import GroupDimension.Cert1024.PcBound
public import Cert1024Comp

@[expose] public section

/-!
# Certificates for `D₄(Q) = 1`, `Q` given by a pc presentation

**The group.** A `PcPres` is a polycyclic presentation on generators `g_0, …, g_{m-1}`, all of
relative order `2`: for each `k` the relation `g_k² = w_k`, and for `k < l` the relation
`g_k⁻¹ g_l g_k = w_{kl}`, where `w_k`, `w_{kl}` are normal words given by bit masks
(`bits n k = n.testBit k`). `PcGroup m P` is the group defined by these relations
(`PresentedGroup`); nothing else is assumed about it.

**The certificate.** A finite abelian group `V = ⊕_{i<r} ℤ/2^{a_i}`, realised as `(Fin r → ℤ) ⧸ L`
with `L = {v | 2^{a_i} ∣ v_i}`, and integer matrices `C_k` (`k < m`), acting on `V`.

**The check** (`checkAux`, a `Bool`): the masks are of pc shape (`w_k`, `w_{kl}` only involve
generators after `g_k`); every matrix is well defined on `V` (`2^{a_i} ∣ C_{ij} 2^{a_j}`); `C_k` is
invertible on `V` with the computed inverse `C_k' = 1 - N + N² - N³`, `N = C_k - 1`; the `C_k` satisfy the relations on `V`; `Δ⁴ V = 0`, checked on spanning sets of `Δ^d V`
(`nilSpan`: the images `(C_k - 1) b` of a spanning set `B_d` of `Δ^d V`, reduced against each
other, span `Δ^{d+1} V`; the check is that `B_4` is empty), so that every product of four
operators `C_k - 1` is `0` on `V` (`nilSpan_sound`); and the `2^m` normal words in the `C_k` are
pairwise distinct on `V`.
All matrices are kept reduced (row `i` modulo `2^{a_i}`), so "equal on `V`" is equality.

**Soundness** (`D_four_eq_bot_of_checkAux`): if the check passes, `g_k ↦ C_k` is a homomorphism
`ρ : PcGroup m P → Aut V`; it is injective (every element is a normal word, `PcBound.lean`, and the
normal words act differently); and `ρ` kills `D₄` (`Nilpotent.lean`). So `D₄ = 1`, hence `D₅ = 1`.
-/

namespace GroupDimension.Cert1024

open Matrix

/-! ## Presentations -/


/-- The relators `g_k² w_k⁻¹` and `g_k⁻¹ g_l g_k w_{kl}⁻¹`. -/
def pcRels (m : ℕ) (P : PcPres) : Set (FreeGroup (Fin m)) :=
  {r | (∃ k : Fin m, r = FreeGroup.of k ^ 2 * (nwFrom FreeGroup.of (bits (P.powMask k)) 0)⁻¹) ∨
    ∃ k l : Fin m, k < l ∧ r = (FreeGroup.of k)⁻¹ * FreeGroup.of l * FreeGroup.of k *
      (nwFrom FreeGroup.of (bits (P.conjMask k l)) 0)⁻¹}

/-- The group of a pc presentation. -/
abbrev PcGroup (m : ℕ) (P : PcPres) : Type := PresentedGroup (pcRels m P)


theorem bits_eq_false_of_all {m n K : ℕ} (h : (List.range (K + 1)).all (fun j => !n.testBit j) = true)
    (j : Fin m) (hj : j.val < K + 1) : bits n j = false := by
  rw [List.all_eq_true] at h
  have := h j.val (List.mem_range.mpr hj)
  simpa [bits] using this

/-! ## The module `V` and integer matrices on it -/

section Module

variable {r : ℕ} (a : Fin r → ℕ)

/-- `L = ⊕ 2^{a_i} ℤ`. -/
def latt : AddSubgroup (Fin r → ℤ) where
  carrier := {v | ∀ i, (2 : ℤ) ^ a i ∣ v i}
  add_mem' := fun hx hy i => dvd_add (hx i) (hy i)
  zero_mem' := fun _ => dvd_zero _
  neg_mem' := fun hx i => (dvd_neg).mpr (hx i)

/-- `V = ⊕ ℤ/2^{a_i}`. -/
abbrev Mod := (Fin r → ℤ) ⧸ latt a

/-- `A` is well defined on `V`: `2^{a_i} ∣ A_{ij} 2^{a_j}`. -/
def WD (A : Matrix (Fin r) (Fin r) ℤ) : Prop := ∀ i j, (2 : ℤ) ^ a i ∣ A i j * 2 ^ a j

variable {a}

theorem WD.mulVec_mem {A : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) {v : Fin r → ℤ}
    (hv : v ∈ latt a) : A *ᵥ v ∈ latt a := by
  intro i
  simp only [mulVec, dotProduct]
  refine Finset.dvd_sum fun j _ => ?_
  obtain ⟨t, ht⟩ := hv j
  rw [ht, ← mul_assoc]
  exact Dvd.dvd.mul_right (hA i j) t

theorem WD.mul {A B : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (hB : WD a B) : WD a (A * B) := by
  intro i k
  simp only [mul_apply, Finset.sum_mul]
  refine Finset.dvd_sum fun j _ => ?_
  obtain ⟨t, ht⟩ := hB j k
  rw [mul_assoc, ht, ← mul_assoc]
  exact Dvd.dvd.mul_right (hA i j) t

theorem WD.one : WD a (1 : Matrix (Fin r) (Fin r) ℤ) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [one_apply_ne h]

theorem WD.sub {A B : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (hB : WD a B) : WD a (A - B) :=
  fun i j => by rw [Matrix.sub_apply, sub_mul]; exact dvd_sub (hA i j) (hB i j)

theorem WD.zero : WD a (0 : Matrix (Fin r) (Fin r) ℤ) := fun i j => by simp

variable (a)

/-- The operator of a well-defined `A` on `V`. -/
noncomputable def opWD (A : Matrix (Fin r) (Fin r) ℤ) (h : WD a A) : AddMonoid.End (Mod a) :=
  QuotientAddGroup.map (latt a) (latt a) (mulVecLin A).toAddMonoidHom
    (fun _ hv => WD.mulVec_mem h hv)

/-- The operator of `A` on `V` (`0` if `A` is not well defined). -/
noncomputable def op (A : Matrix (Fin r) (Fin r) ℤ) : AddMonoid.End (Mod a) := by
  classical
  exact if h : WD a A then opWD a A h else 0

variable {a}

theorem op_mk {A : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (v : Fin r → ℤ) :
    op a A (QuotientAddGroup.mk v) = QuotientAddGroup.mk (A *ᵥ v) := by
  rw [op, dif_pos hA, opWD]; rfl

theorem op_ext {f g : AddMonoid.End (Mod a)}
    (h : ∀ v : Fin r → ℤ, f (QuotientAddGroup.mk v) = g (QuotientAddGroup.mk v)) : f = g :=
  AddMonoidHom.ext fun x => QuotientAddGroup.induction_on x h

theorem op_mul {A B : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (hB : WD a B) :
    op a (A * B) = op a A * op a B :=
  op_ext fun v => by
    rw [op_mk (hA.mul hB)]
    change _ = op a A (op a B (QuotientAddGroup.mk v))
    rw [op_mk hB, op_mk hA, mulVec_mulVec]

theorem op_one : op a (1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
  op_ext fun v => by rw [op_mk WD.one, one_mulVec]; rfl

theorem op_sub {A B : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (hB : WD a B) :
    op a (A - B) = op a A - op a B :=
  op_ext fun v => by
    rw [op_mk (hA.sub hB)]
    change _ = op a A (QuotientAddGroup.mk v) - op a B (QuotientAddGroup.mk v)
    rw [op_mk hA, op_mk hB, sub_mulVec, QuotientAddGroup.mk_sub]

/-- Matrices congruent row by row act equally. -/
theorem op_eq_of_dvd {A B : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (hB : WD a B)
    (h : ∀ i j, (2 : ℤ) ^ a i ∣ A i j - B i j) : op a A = op a B :=
  op_ext fun v => by
    rw [op_mk hA, op_mk hB, QuotientAddGroup.eq_iff_sub_mem]
    intro i
    rw [← sub_mulVec]
    simp only [mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (by rw [Matrix.sub_apply]; exact h i j) _

/-- Conversely, matrices that act equally are congruent row by row. -/
theorem dvd_of_op_eq {A B : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (hB : WD a B)
    (h : op a A = op a B) (i j : Fin r) : (2 : ℤ) ^ a i ∣ A i j - B i j := by
  have := congrArg (fun f => f (QuotientAddGroup.mk (Pi.single j 1))) h
  simp only [op_mk hA, op_mk hB] at this
  have hm := (QuotientAddGroup.eq_iff_sub_mem).mp this.symm i
  exact dvd_sub_comm.mp (by simpa [mulVec_single, Pi.sub_apply] using hm)

/-- Row `i` reduced modulo `2^{a_i}`. -/
def red (a : Fin r → ℕ) (A : Matrix (Fin r) (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => A i j % 2 ^ a i

theorem dvd_red_sub (A : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) :
    (2 : ℤ) ^ a i ∣ red a A i j - A i j := by
  simp only [red, of_apply, Int.emod_def, sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right _ _

theorem WD.reduce {A : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) : WD a (red a A) := fun i j => by
  have h1 := dvd_red_sub (a := a) A i j
  have : red a A i j * 2 ^ a j = (red a A i j - A i j) * 2 ^ a j + A i j * 2 ^ a j := by ring
  rw [this]
  exact dvd_add (Dvd.dvd.mul_right h1 _) (hA i j)

theorem op_red {A : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) : op a (red a A) = op a A :=
  op_eq_of_dvd hA.reduce hA (dvd_red_sub A)

theorem red_red (A : Matrix (Fin r) (Fin r) ℤ) : red a (red a A) = red a A := by
  ext i j; simp [red, Int.emod_emod_of_dvd]

/-- Congruent matrices have the same reduction. -/
theorem red_eq_of_dvd {A B : Matrix (Fin r) (Fin r) ℤ}
    (h : ∀ i j, (2 : ℤ) ^ a i ∣ A i j - B i j) : red a A = red a B := by
  ext i j
  exact ((Int.modEq_iff_dvd).mpr (h i j)).symm

end Module

/-! ## The computational matrices as matrices -/

section Comp

variable {r : ℕ}

/-- The matrix of a materialised one. -/
def toM (x : Mat r) : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => x[i][j]

theorem toM_injective {x y : Mat r} (h : toM x = toM y) : x = y := by
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  simpa [toM] using this

theorem toM_mmul (a : Fin r → ℕ) (x y : Mat r) : toM (mmul a x y) = red a (toM x * toM y) := by
  ext i j
  simp [toM, mmul, red, Matrix.mul_apply, Fin.sum_univ_def]

theorem delta_eq (i j : Fin r) : delta i j = (1 : Matrix (Fin r) (Fin r) ℤ) i j := by
  simp [delta, Matrix.one_apply]

theorem toM_idM (a : Fin r → ℕ) : toM (idM a) = red a 1 := by
  ext i j; simp [toM, idM, red, delta_eq]

theorem toM_subOne (a : Fin r → ℕ) (x : Mat r) : toM (subOne a x) = red a (toM x - 1) := by
  ext i j; simp [toM, subOne, red, delta_eq]

theorem toM_zeroM : toM (zeroM : Mat r) = 0 := by
  ext i j; simp [toM, zeroM]

theorem mem_allFns : ∀ {m : ℕ} (e : Fin m → Bool), e ∈ allFns m
  | 0, e => by
    simp only [allFns, List.mem_singleton]; funext i; exact i.elim0
  | m + 1, e => by
    simp only [allFns, List.mem_flatMap]
    refine ⟨fun i => e ⟨i.val + 1, by omega⟩, mem_allFns _, ?_⟩
    have : e = consB (e 0) fun i => e ⟨i.val + 1, by omega⟩ := by
      funext i
      simp only [consB]
      split_ifs with h
      · exact congrArg e (Fin.ext h)
      · exact congrArg e (Fin.ext (by simp; omega))
    rw [this]
    cases e 0 <;> simp [consB]

theorem WD_of_wdB {a : Fin r → ℕ} {x : Mat r} (h : wdB a x = true) : WD a (toM x) := by
  intro i j
  simp only [wdB, List.all_eq_true, List.mem_finRange, beq_iff_eq, forall_const] at h
  exact Int.dvd_of_emod_eq_zero (h i j)

end Comp

/-! ## The check -/

section Check

variable {m r : ℕ}

theorem genOK_spec {m : ℕ} {P : PcPres} {a : Fin r → ℕ} {C : Fin m → Mat r} {k : Fin m}
    (h : genOK m P a C k = true) :
    wdB a (C k) = true ∧ wdB a (invM a (C k)) = true ∧ mmul a (C k) (invM a (C k)) = idM a ∧
      mmul a (invM a (C k)) (C k) = idM a ∧
      mmul a (C k) (C k) = nwMat a C (bits (P.powMask k)) 0 ∧
      ∀ l, k < l → mmul a (C l) (C k) = mmul a (C k) (nwMat a C (bits (P.conjMask k l)) 0) := by
  simp only [genOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    forall_const, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun l hl => (h6 l).resolve_left (not_le.mpr hl)⟩

theorem formatOK_spec {m : ℕ} {P : PcPres} (h : formatOK m P = true) :
    (∀ k j : Fin m, j.val < k.val + 1 → bits (P.powMask k) j = false) ∧
    (∀ k l : Fin m, k < l → ∀ j : Fin m, j.val < k.val + 1 → bits (P.conjMask k l) j = false) := by
  simp only [formatOK, List.all_eq_true, List.mem_finRange, forall_const, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at h
  refine ⟨fun k j hj => bits_eq_false_of_all ?_ j hj, fun k l hkl j hj => bits_eq_false_of_all ?_ j hj⟩
  · simp only [List.all_eq_true, Bool.not_eq_true']; exact (h k).1
  · rcases (h k).2 l with h' | h'
    · exact absurd hkl (not_lt.mpr h')
    · simp only [List.all_eq_true, Bool.not_eq_true']; exact h'

/-! ### The nilpotency check -/

section Span

variable {a : Fin r → ℕ}

/-- A materialised vector as a vector. -/
def toV (v : Vec r) : Fin r → ℤ := fun i => v[i]

/-- Its class in `V`. -/
def mkV (a : Fin r → ℕ) (v : Vec r) : Mod a := QuotientAddGroup.mk (toV v)

/-- The subgroup of `V` generated by a list of vectors. -/
def spanV (a : Fin r → ℕ) (B : List (Vec r)) : AddSubgroup (Mod a) :=
  AddSubgroup.closure {x | ∃ b ∈ B, x = mkV a b}

theorem mkV_mem_spanV {B : List (Vec r)} {b : Vec r} (hb : b ∈ B) : mkV a b ∈ spanV a B :=
  AddSubgroup.subset_closure ⟨b, hb, rfl⟩

theorem spanV_mono {B B' : List (Vec r)} (h : ∀ b ∈ B, b ∈ B') : spanV a B ≤ spanV a B' :=
  AddSubgroup.closure_le _ |>.mpr fun _ ⟨b, hb, he⟩ => he ▸ mkV_mem_spanV (h b hb)

theorem spanV_nil : spanV a ([] : List (Vec r)) = ⊥ := by
  simp [spanV]

theorem mkV_eq_of_dvd {v w : Vec r} (h : ∀ i : Fin r, (2 : ℤ) ^ a i ∣ v[i] - w[i]) :
    mkV a v = mkV a w := by
  rw [mkV, mkV, QuotientAddGroup.eq_iff_sub_mem]
  intro i
  simpa [toV] using h i

theorem mkV_mvec {x : Mat r} (hx : WD a (toM x)) (v : Vec r) :
    mkV a (mvec a x v) = op a (toM x) (mkV a v) := by
  rw [mkV, mkV, op_mk hx, QuotientAddGroup.eq_iff_sub_mem]
  intro i
  have h := (Int.mod_modEq (((List.finRange r).map fun k => x[i][k] * v[k]).sum) (2 ^ a i)).symm.dvd
  simpa [toV, mvec, toM, mulVec, dotProduct, Fin.sum_univ_def] using h

theorem mkV_axpy (c : ℤ) (b u : Vec r) : mkV a (axpy a c b u) = mkV a u - c • mkV a b := by
  have : mkV a u - c • mkV a b = mkV a (Vector.ofFn fun i => u[i] - c * b[i]) := by
    rw [mkV, mkV, mkV, ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_sub]
    congr 1
    funext i
    simp [toV]
  rw [this]
  refine mkV_eq_of_dvd fun i => ?_
  simpa [axpy] using (Int.mod_modEq (u[i] - c * b[i]) (2 ^ a i)).symm.dvd

theorem mkV_zeroV : mkV a (zeroV : Vec r) = 0 := by
  rw [mkV]
  convert QuotientAddGroup.mk_zero (latt a)
  funext i
  simp [toV, zeroV]

theorem mkV_sub_reduceV_mem (B : List (Vec r)) (u : Vec r) :
    mkV a u - mkV a (reduceV a B u) ∈ spanV a B := by
  induction B generalizing u with
  | nil => simp [reduceV]
  | cons b B ih =>
    have h1 := ih (axpy a (coefV a b u) b u)
    simp only [reduceV, List.foldl_cons] at h1 ⊢
    have h2 : mkV a u - mkV a (axpy a (coefV a b u) b u) ∈ spanV a (b :: B) := by
      rw [mkV_axpy, sub_sub_cancel]
      exact AddSubgroup.zsmul_mem _ (mkV_mem_spanV List.mem_cons_self) _
    have h3 := spanV_mono (a := a) (fun x hx => List.mem_cons_of_mem b hx) h1
    have := AddSubgroup.add_mem _ h2 h3
    rwa [sub_add_sub_cancel] at this

theorem mem_insV {w x : Vec r} {B : List (Vec r)} : x ∈ insV a w B ↔ x = w ∨ x ∈ B := by
  induction B with
  | nil => simp [insV]
  | cons b B ih =>
    simp only [insV]
    split_ifs
    · simp
    · simp only [List.mem_cons, ih]; tauto

theorem addV_spec (B : List (Vec r)) (u : Vec r) :
    mkV a u ∈ spanV a (addV a B u) ∧ spanV a B ≤ spanV a (addV a B u) := by
  have hr := mkV_sub_reduceV_mem (a := a) B u
  simp only [addV]
  split_ifs with hz
  · rw [beq_iff_eq] at hz
    rw [hz, mkV_zeroV, sub_zero] at hr
    exact ⟨hr, le_rfl⟩
  · have hle : spanV a B ≤ spanV a (insV a (reduceV a B u) B) :=
      spanV_mono fun x hx => mem_insV.mpr (Or.inr hx)
    have hw : mkV a (reduceV a B u) ∈ spanV a (insV a (reduceV a B u) B) :=
      mkV_mem_spanV (mem_insV.mpr (Or.inl rfl))
    refine ⟨?_, hle⟩
    have := AddSubgroup.add_mem _ (hle hr) hw
    rwa [sub_add_cancel] at this

theorem foldl_addV_spec (U B : List (Vec r)) :
    (∀ u ∈ U, mkV a u ∈ spanV a (U.foldl (addV a) B)) ∧
      spanV a B ≤ spanV a (U.foldl (addV a) B) := by
  induction U generalizing B with
  | nil => simp
  | cons u U ih =>
    obtain ⟨h1, h2⟩ := addV_spec (a := a) B u
    obtain ⟨h3, h4⟩ := ih (addV a B u)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨h4 h1, h3⟩, h2.trans h4⟩

/-- Each `N ∈ Ns` maps the span of `B` into the span of the next set. -/
theorem op_mem_spanStep {Ns : List (Mat r)} {B : List (Vec r)} {n : Mat r} (hn : n ∈ Ns)
    (hW : WD a (toM n)) {x : Mod a} (hx : x ∈ spanV a B) :
    op a (toM n) x ∈ spanV a (spanStep a Ns B) := by
  have hgen : spanV a B ≤ (spanV a (spanStep a Ns B)).comap (op a (toM n)) := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    show op a (toM n) (mkV a b) ∈ spanV a (spanStep a Ns B)
    rw [← mkV_mvec hW]
    exact (foldl_addV_spec (a := a) _ []).1 _ (List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨n, hn, rfl⟩⟩)
  exact hgen hx

theorem mem_spanV_basisV (x : Mod a) : x ∈ spanV a (basisV r) := by
  induction x using QuotientAddGroup.induction_on with
  | H v =>
    rw [pi_eq_sum_univ v, QuotientAddGroup.mk_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [QuotientAddGroup.mk_zsmul]
    refine AddSubgroup.zsmul_mem _ ?_ _
    have hb : (Vector.ofFn fun j => if i = j then (1 : ℤ) else 0) ∈ basisV r :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have e : mkV a (Vector.ofFn fun j => if i = j then (1 : ℤ) else 0) =
        QuotientAddGroup.mk (fun j => if i = j then (1 : ℤ) else 0) := by
      rw [mkV]; congr 1; funext j; simp [toV]
    exact e ▸ mkV_mem_spanV hb

/-- **Soundness of the nilpotency check**: if `nilSpan` passes, every product of `c` operators
`C_k - 1` is `0` on `V`. -/
theorem nilSpan_sound {m c : ℕ} {C : Fin m → Mat r} (h : nilSpan m a C c = true)
    (hC : ∀ k, WD a (toM (C k))) :
    ∀ l : List (Fin m), l.length = c → (l.map fun k => op a (toM (C k)) - 1).prod = 0 := by
  let Ns := (List.finRange m).map fun k => subOne a (C k)
  have hWN : ∀ k, WD a (toM (subOne a (C k))) := fun k => by
    rw [toM_subOne]; exact ((hC k).sub WD.one).reduce
  have hN : ∀ k, op a (toM (subOne a (C k))) = op a (toM (C k)) - 1 := fun k => by
    rw [toM_subOne, op_red ((hC k).sub WD.one), op_sub (hC k) WD.one, op_one]
  have key : ∀ (l : List (Fin m)) (x : Mod a),
      (l.map fun k => op a (toM (C k)) - 1).prod x ∈ spanV a (spanIter a Ns l.length (basisV r)) := by
    intro l
    induction l with
    | nil => intro x; exact mem_spanV_basisV _
    | cons k l ih =>
      intro x
      simp only [List.map_cons, List.prod_cons, List.length_cons, spanIter]
      have e : ((op a (toM (C k)) - 1) * (l.map fun k => op a (toM (C k)) - 1).prod) x =
          (op a (toM (C k)) - 1) ((l.map fun k => op a (toM (C k)) - 1).prod x) := rfl
      rw [e, ← hN]
      exact op_mem_spanStep (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) (hWN k) (ih x)
  intro l hl
  have hnil : spanIter a Ns c (basisV r) = [] := by
    simpa [nilSpan, Ns] using h
  ext x
  have := key l x
  rw [hl, hnil, spanV_nil, AddSubgroup.mem_bot] at this
  simpa using this

end Span

/-! ### Soundness -/

variable {P : PcPres} {a : Fin r → ℕ} {C : Fin m → Mat r}

theorem WD_toM_mmul {x y : Mat r} (hx : WD a (toM x)) (hy : WD a (toM y)) :
    WD a (toM (mmul a x y)) := by
  rw [toM_mmul]; exact (hx.mul hy).reduce

theorem op_mmul {x y : Mat r} (hx : WD a (toM x)) (hy : WD a (toM y)) :
    op a (toM (mmul a x y)) = op a (toM x) * op a (toM y) := by
  rw [toM_mmul, op_red (hx.mul hy), op_mul hx hy]

theorem WD_idM : WD a (toM (idM a)) := by rw [toM_idM]; exact WD.one.reduce

theorem op_idM : op a (toM (idM a)) = 1 := by rw [toM_idM, op_red WD.one, op_one]

theorem nwMat_spec (hC : ∀ k, WD a (toM (C k))) (e : Fin m → Bool) (i : ℕ) :
    WD a (toM (nwMat a C e i)) ∧
      op a (toM (nwMat a C e i)) = nwFrom (fun k => op a (toM (C k))) e i ∧
      ∃ X, toM (nwMat a C e i) = red a X := by
  induction i using nwFrom_induction (m := m) with
  | htop i hi =>
    rw [nwMat, dif_neg (by omega), nwFrom_of_le _ _ hi]
    exact ⟨WD_idM, op_idM, 1, toM_idM a⟩
  | hstep i hi ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [nwMat, dif_pos hi, nwFrom_of_lt _ _ hi]
    split_ifs
    · exact ⟨WD_toM_mmul (hC _) h1, by rw [op_mmul (hC _) h1, h2], _, toM_mmul _ _ _⟩
    · exact ⟨h1, by rw [h2, one_mul], h3⟩

/-- A reduced matrix is determined by its operator. -/
theorem eq_of_op_eq {x y : Mat r} (hx : WD a (toM x)) (hy : WD a (toM y))
    (hx' : ∃ X, toM x = red a X) (hy' : ∃ Y, toM y = red a Y)
    (h : op a (toM x) = op a (toM y)) : x = y := by
  obtain ⟨X, hX⟩ := hx'
  obtain ⟨Y, hY⟩ := hy'
  have := red_eq_of_dvd (dvd_of_op_eq hx hy h)
  rw [hX, hY, red_red, red_red] at this
  exact toM_injective (by rw [hX, hY, this])

/-- What a passing check gives: a representation `f` of the group of the presentation that kills
`D₄`, distinct normal words have distinct images, and every element is a normal word. -/
theorem rep_of_checkAux (h : checkAux m P a C = true) :
    ∃ f : PcGroup m P →* AddMonoid.End (Mod a), (∀ g ∈ D 4 (PcGroup m P), f g = 1) ∧
      (∀ e e', f (nwFrom PresentedGroup.of e 0) = f (nwFrom PresentedGroup.of e' 0) → e = e') ∧
      ∀ x : PcGroup m P, ∃ e, x = nwFrom PresentedGroup.of e 0 := by
  simp only [checkAux, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨hfmt0, hgen0, hnil0, hnodup0⟩ := h
  have hfmt := formatOK_spec hfmt0
  have hgen := fun k => genOK_spec (hgen0 k)
  have hnodup : ((allFns m).map fun e => nwMat a C e 0).Nodup :=
    of_decide_eq_true (by simpa [faithOK] using hnodup0)
  have hconj : ∀ k l : Fin m, k < l →
      mmul a (C l) (C k) = mmul a (C k) (nwMat a C (bits (P.conjMask k l)) 0) :=
    fun k l hkl => (hgen k).2.2.2.2.2 l hkl
  have hC : ∀ k, WD a (toM (C k)) := fun k => WD_of_wdB (hgen k).1
  have hCi : ∀ k, WD a (toM (invM a (C k))) := fun k => WD_of_wdB (hgen k).2.1
  -- the units `C_k`
  let U : Fin m → (AddMonoid.End (Mod a))ˣ := fun k =>
    { val := op a (toM (C k))
      inv := op a (toM (invM a (C k)))
      val_inv := by rw [← op_mmul (hC k) (hCi k), (hgen k).2.2.1, op_idM]
      inv_val := by rw [← op_mmul (hCi k) (hC k), (hgen k).2.2.2.1, op_idM] }
  have hU : ∀ e (i : ℕ), ((nwFrom U e i : (AddMonoid.End (Mod a))ˣ) : AddMonoid.End (Mod a)) =
      op a (toM (nwMat a C e i)) := fun e i => by
    rw [← Units.coeHom_apply, map_nwFrom, (nwMat_spec hC e i).2.1]; rfl
  -- the relations hold
  have hrel : ∀ x ∈ pcRels m P, FreeGroup.lift U x = 1 := by
    rintro x (⟨k, rfl⟩ | ⟨k, l, hkl, rfl⟩)
    · rw [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, map_nwFrom, mul_inv_eq_one]
      simp only [FreeGroup.lift_apply_of]
      apply Units.ext
      rw [hU, pow_two, Units.val_mul, ← (hgen k).2.2.2.2.1]
      exact (op_mmul (hC k) (hC k)).symm
    · rw [map_mul, map_mul, map_mul, map_inv, map_inv, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, map_nwFrom, mul_inv_eq_one]
      simp only [FreeGroup.lift_apply_of]
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      apply Units.ext
      have h2 := hconj k l hkl
      rw [Units.val_mul, Units.val_mul, hU]
      have := congrArg (op a ∘ toM) h2
      simp only [Function.comp] at this
      rw [op_mmul (hC l) (hC k), op_mmul (hC k) (nwMat_spec hC _ 0).1] at this
      exact this
  let ρ := PresentedGroup.toGroup hrel
  let f : PcGroup m P →* AddMonoid.End (Mod a) := (Units.coeHom _).comp ρ
  have hf : ∀ k, f (PresentedGroup.of k) = op a (toM (C k)) := fun k => by
    simp [f, ρ, PresentedGroup.toGroup.of, U]
  -- `f` kills `D₄`
  have hD : ∀ g ∈ D 4 (PcGroup m P), f g = 1 := by
    intro g hg
    refine map_eq_one_of_mem_D (fun k => op a (toM (C k)) - 1) f PresentedGroup.of
      (PresentedGroup.closure_range_of _) (fun k => by rw [hf]) ?_ hg
    exact nilSpan_sound hnil0 hC
  -- `f` is injective: every element is a normal word, and normal words act differently
  have hpc := exists_nwFrom_zero (PresentedGroup.of (rels := pcRels m P))
    (PresentedGroup.closure_range_of _)
    (fun k => by
      have h1 := PresentedGroup.one_of_mem (rels := pcRels m P) (Or.inl ⟨k, rfl⟩)
      rw [map_mul, map_inv, mul_inv_eq_one, map_pow, map_nwFrom] at h1
      have h1' : PresentedGroup.of k ^ 2 =
          nwFrom (fun j => PresentedGroup.of (rels := pcRels m P) j) (bits (P.powMask k)) 0 := h1
      rw [h1', nwFrom_skip _ _ (Nat.zero_le (k.val + 1))
        (fun j hj => hfmt.1 k j hj)]
      exact nwFrom_mem_tail _ _ _)
    (fun k l hkl => by
      have h1 := PresentedGroup.one_of_mem (rels := pcRels m P) (Or.inr ⟨k, l, hkl, rfl⟩)
      rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, map_inv, map_nwFrom] at h1
      have h1' : (PresentedGroup.of k)⁻¹ * PresentedGroup.of l * PresentedGroup.of k =
          nwFrom (fun j => PresentedGroup.of (rels := pcRels m P) j) (bits (P.conjMask k l)) 0 := h1
      rw [h1', nwFrom_skip _ _ (Nat.zero_le (k.val + 1))
        (fun j hj => hfmt.2 k l hkl j hj)]
      exact nwFrom_mem_tail _ _ _)
  have hnw : ∀ e, f (nwFrom PresentedGroup.of e 0) = op a (toM (nwMat a C e 0)) := fun e => by
    rw [map_nwFrom]
    simp only [hf]
    exact (nwMat_spec hC e 0).2.1.symm
  refine ⟨f, hD, fun e e' hee => ?_, hpc⟩
  rw [hnw, hnw] at hee
  have heq : nwMat a C e 0 = nwMat a C e' 0 :=
    eq_of_op_eq (nwMat_spec hC e 0).1 (nwMat_spec hC _ 0).1 (nwMat_spec hC e 0).2.2
      (nwMat_spec hC _ 0).2.2 hee
  exact List.inj_on_of_nodup_map hnodup (mem_allFns e) (mem_allFns _) heq

theorem nwFrom_false {G : Type*} [Monoid G] (g : Fin m → G) : nwFrom g (fun _ => false) 0 = 1 :=
  (nwFrom_skip _ _ (Nat.zero_le m) (fun _ _ => rfl)).trans (nwFrom_of_le _ _ le_rfl)

/-- **Soundness of the check**: the group of the presentation has `D₄ = 1`. -/
theorem D_four_eq_bot_of_checkAux (h : checkAux m P a C = true) : D 4 (PcGroup m P) = ⊥ := by
  obtain ⟨f, hD, hinj, hpc⟩ := rep_of_checkAux h
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨e, rfl⟩ := hpc g
  have h1 := hD _ hg
  have h0 : f (nwFrom PresentedGroup.of (fun _ => false) 0) = 1 := by rw [nwFrom_false, map_one]
  rw [hinj e _ (h1.trans h0.symm), Subgroup.mem_bot, nwFrom_false]

/-- The group of the presentation has order `2^m`: the normal words are a bijection. -/
theorem card_eq_of_checkAux (h : checkAux m P a C = true) : Nat.card (PcGroup m P) = 2 ^ m := by
  obtain ⟨f, -, hinj, hpc⟩ := rep_of_checkAux h
  have hbij : Function.Bijective
      (fun e : Fin m → Bool => nwFrom (PresentedGroup.of (rels := pcRels m P)) e 0) :=
    ⟨fun e e' hee => hinj e e' (by simp only at hee; rw [hee]),
      fun x => (hpc x).imp fun e he => he.symm⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

theorem D_five_eq_bot_of_checkAux (h : checkAux m P a C = true) : D 5 (PcGroup m P) = ⊥ :=
  eq_bot_iff.mpr ((D_antitone (by norm_num : 4 ≤ 5)).trans (D_four_eq_bot_of_checkAux h).le)

end Check

end GroupDimension.Cert1024
