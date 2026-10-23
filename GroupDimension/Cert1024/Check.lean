import GroupDimension.Cert1024.Nilpotent
import GroupDimension.Cert1024.PcBound
import Cert1024Comp

/-!
# Certificates for `D₄(Q) = 1`, `Q` given by a pc presentation

**The group.** A `PcPres` is a polycyclic presentation on generators `g_0, …, g_{m-1}`, all of
relative order `2`: for each `k` the relation `g_k² = w_k`, and for `k < l` the relation
`g_k⁻¹ g_l g_k = w_{kl}`, where `w_k`, `w_{kl}` are normal words given by bit masks
(`bits n k = n.testBit k`). `PcGroup m P` is the group defined by these relations
(`PresentedGroup`); nothing else is assumed about it.

**The certificate.** A finite abelian group `V = ⊕_{i<r} ℤ/2^{a_i}`, realised as `(Fin r → ℤ) ⧸ L`
with `L = {v | 2^{a_i} ∣ v_i}`, and integer matrices `C_k`, `C_k'` (`k < m`), acting on `V`.

**The check** (`checkAux`, a `Bool`): the masks are of pc shape (`w_k`, `w_{kl}` only involve
generators after `g_k`); every matrix is well defined on `V` (`2^{a_i} ∣ C_{ij} 2^{a_j}`); `C_k C_k'
= C_k' C_k = 1` on `V`; the `C_k` satisfy the relations on `V`; every product of four matrices
`C_k - 1` is `0` on `V`; and the `2^m` normal words in the `C_k` are pairwise distinct on `V`.
All matrices are kept reduced (row `i` modulo `2^{a_i}`), so "equal on `V`" is equality.

**Soundness** (`D_four_eq_bot_of_check`): if the check passes, `g_k ↦ C_k` is a homomorphism
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
  fun i j => by rw [sub_apply, sub_mul]; exact dvd_sub (hA i j) (hB i j)

theorem WD.zero : WD a (0 : Matrix (Fin r) (Fin r) ℤ) := fun i j => by simp

variable (a)

/-- The operator of `A` on `V` (`0` if `A` is not well defined). -/
noncomputable def op (A : Matrix (Fin r) (Fin r) ℤ) : AddMonoid.End (Mod a) := by
  classical
  exact if h : WD a A then
    QuotientAddGroup.map (latt a) (latt a) (mulVecLin A).toAddMonoidHom
      (fun _ hv => WD.mulVec_mem h hv)
  else 0

variable {a}

theorem op_mk {A : Matrix (Fin r) (Fin r) ℤ} (hA : WD a A) (v : Fin r → ℤ) :
    op a A (QuotientAddGroup.mk v) = QuotientAddGroup.mk (A *ᵥ v) := by
  rw [op, dif_pos hA]; rfl

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
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (by rw [sub_apply]; exact h i j) _

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

/-- **Soundness of the check**: the group of the presentation has `D₄ = 1`. -/
theorem D_four_eq_bot_of_checkAux (h : checkAux m P a C = true) : D 4 (PcGroup m P) = ⊥ := by
  simp only [checkAux, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨hfmt0, hgen0, hnil0, hnodup0⟩ := h
  have hfmt := formatOK_spec hfmt0
  have hgen := fun k => genOK_spec (hgen0 k)
  have hnil : ∀ k1 k2 k3 k4 : Fin m, mmul a (subOne a (C k1)) (mmul a (subOne a (C k2))
      (mmul a (subOne a (C k3)) (mmul a (subOne a (C k4)) (idM a)))) = zeroM := by
    simpa [nilOK, List.all_eq_true] using hnil0
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
    intro l hl
    match l, hl with
    | [k1, k2, k3, k4], _ =>
      have hN : ∀ k, op a (toM (subOne a (C k))) = op a (toM (C k)) - 1 := fun k => by
        rw [toM_subOne, op_red ((hC k).sub WD.one), op_sub (hC k) WD.one, op_one]
      have hWN : ∀ k, WD a (toM (subOne a (C k))) := fun k => by
        rw [toM_subOne]; exact ((hC k).sub WD.one).reduce
      have := congrArg (op a ∘ toM) (hnil k1 k2 k3 k4)
      simp only [Function.comp, toM_zeroM] at this
      rw [op_mmul (hWN k1) (WD_toM_mmul (hWN k2) (WD_toM_mmul (hWN k3) (WD_toM_mmul (hWN k4) WD_idM))),
        op_mmul (hWN k2) (WD_toM_mmul (hWN k3) (WD_toM_mmul (hWN k4) WD_idM)),
        op_mmul (hWN k3) (WD_toM_mmul (hWN k4) WD_idM), op_mmul (hWN k4) WD_idM, op_idM,
        hN, hN, hN, hN] at this
      have h0 : op a (0 : Matrix (Fin r) (Fin r) ℤ) = 0 :=
        op_ext fun v => by rw [op_mk WD.zero, zero_mulVec]; rfl
      rw [h0] at this
      simpa [mul_assoc] using this
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
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨e, rfl⟩ := hpc g
  have h1 := hD _ hg
  rw [hnw] at h1
  have e0 := hnw (fun _ => false)
  rw [show nwFrom (PresentedGroup.of (rels := pcRels m P)) (fun _ => false) 0 = 1 from
    (nwFrom_skip _ _ (Nat.zero_le m) (fun _ _ => rfl)).trans (nwFrom_of_le _ _ le_rfl), map_one] at e0
  have heq : nwMat a C e 0 = nwMat a C (fun _ => false) 0 :=
    eq_of_op_eq (nwMat_spec hC e 0).1 (nwMat_spec hC _ 0).1 (nwMat_spec hC e 0).2.2
      (nwMat_spec hC _ 0).2.2 (h1.trans e0)
  have := List.inj_on_of_nodup_map hnodup (mem_allFns e) (mem_allFns _) heq
  rw [this, Subgroup.mem_bot]
  exact (nwFrom_skip _ _ (Nat.zero_le m) (fun _ _ => rfl)).trans (nwFrom_of_le _ _ le_rfl)

theorem D_five_eq_bot_of_checkAux (h : checkAux m P a C = true) : D 5 (PcGroup m P) = ⊥ :=
  eq_bot_iff.mpr ((D_antitone (by norm_num : 4 ≤ 5)).trans (D_four_eq_bot_of_checkAux h).le)

end Check

end GroupDimension.Cert1024
