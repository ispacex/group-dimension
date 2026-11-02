module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.NoncommRing
public import GroupDimension.TraceReplay.Check

@[expose] public section

/-!
# Soundness of the trace replay (MATH-314, item 7)

The semantics of `TraceReplay.check`: `R = ℤ[FreeMonoid (Fin d)] = ℤ⟨X_1..X_d⟩`. A sparse vector
`v` means `eval v = Σ a_c X_{w(c)}`, where `w(c)` is the word at position `c`.

For a list of relators `rels` (flat words) and a modulus `D`, the level-`k` target is the
`ℤ`-submodule `Lt k` of `R` spanned by
* `X_u (mt k r − 1) X_v` for `r ∈ rels` and words `u, v`, where `mt k r` is the Magnus image of `r`
  with every factor `(1 + X_j)^e` cut to `Σ_{m<k} C(e, m) X_j^m`;
* the monomials `X_w` with `|w| ≥ k`;
* `D • R`.
So `Lt k` is the preimage of `J_k + D·A_k` under `R → A_k = R / (degree ≥ k)`.

Main results: every vector a trace defines at level `k` lies in `Lt k`; if `check` passes, then
`mt n w_t − 1 ∈ Lt n` for every test claimed in, and `p^{E−1} X_w ∈ Lt n` for every word `w ≠ 1`
(exactness (X) with no free columns).
-/

namespace GroupDimension.TraceReplay

noncomputable section

open MonoidAlgebra

section Words

variable (d : ℕ) [NeZero d]

/-- `ℤ⟨X_1..X_d⟩`. -/
abbrev R := MonoidAlgebra ℤ (FreeMonoid (Fin d))

/-- A letter `j < d` (reduced modulo `d`, so that it is always a letter). -/
def letter (j : ℕ) : Fin d := ⟨j % d, Nat.mod_lt _ (NeZero.pos d)⟩

/-- The word of length `g` with index `idx`: base `d`, the first letter most significant. -/
def wordOf : ℕ → ℕ → FreeMonoid (Fin d)
  | 0, _ => 1
  | g + 1, idx => wordOf g (idx / d) * FreeMonoid.of (letter d idx)

/-- The word at position `c`. -/
def wordAt (c : ℕ) : FreeMonoid (Fin d) := wordOf d (degOf d c) (c - off d (degOf d c))

/-- The monomial at position `c`. -/
def e (c : ℕ) : R d := single (wordAt d c) 1

/-- The element a sparse vector stands for. -/
def eval (v : Vec) : R d := (v.map fun t => ((t.2 : ℕ) : ℤ) • e d t.1).sum

@[simp] theorem eval_nil : eval d [] = 0 := rfl

@[simp] theorem eval_cons (c a : ℕ) (v : Vec) :
    eval d ((c, a) :: v) = ((a : ℕ) : ℤ) • e d c + eval d v := by
  simp [eval]

end Words

/-! ## Positions -/

section Positions

variable {d : ℕ}

theorem off_succ (d g : ℕ) : off d (g + 1) = off d g + d ^ g := rfl

theorem off_mono (hd : 0 < d) {g h : ℕ} (hgh : g ≤ h) : off d g ≤ off d h := by
  induction hgh with
  | refl => exact le_rfl
  | step _ ih => rw [off_succ]; omega

theorem off_lt_off (hd : 0 < d) {g h : ℕ} (hgh : g < h) : off d g < off d h := by
  induction hgh with
  | refl => rw [off_succ]; have : 0 < d ^ g := Nat.pow_pos hd; omega
  | step _ ih => rw [off_succ]; omega

theorem le_off (hd : 0 < d) (g : ℕ) : g ≤ off d g := by
  induction g with
  | zero => exact le_rfl
  | succ g ih => rw [off_succ]; have : 0 < d ^ g := Nat.pow_pos hd; omega

/-- The degree is determined by `off g ≤ c < off (g + 1)`. -/
theorem deg_unique (hd : 0 < d) {c g h : ℕ} (hg : off d g ≤ c ∧ c < off d (g + 1))
    (hh : off d h ≤ c ∧ c < off d (h + 1)) : g = h := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := off_mono hd (show g + 1 ≤ h by omega); omega
  · have := off_mono hd (show h + 1 ≤ g by omega); omega

/-- `degAux` finds the degree when there is enough fuel. -/
theorem degAux_spec (hd : 0 < d) (c : ℕ) :
    ∀ fuel g, off d g ≤ c → c < off d (g + fuel) →
      off d (degAux d c fuel g) ≤ c ∧ c < off d (degAux d c fuel g + 1) := by
  intro fuel
  induction fuel with
  | zero => intro g h1 h2; simp at h2; omega
  | succ fuel ih =>
    intro g h1 h2
    simp only [degAux]
    by_cases hc : c < off d (g + 1)
    · simp [Nat.blt_eq.mpr hc, h1, hc]
    · have hb : Nat.blt c (off d (g + 1)) = false :=
        Bool.eq_false_iff.mpr fun h => hc (Nat.blt_eq.mp h)
      simp only [hb, Bool.cond_false]
      exact ih (g + 1) (by omega) (by rw [show g + 1 + fuel = g + (fuel + 1) by omega]; exact h2)

theorem deg_spec (hd : 0 < d) (c : ℕ) : off d (degOf d c) ≤ c ∧ c < off d (degOf d c + 1) :=
  degAux_spec hd c (c + 1) 0 (by simp [off]) (by
    simp only [Nat.zero_add]; have := le_off hd (c + 1)
    have := off_lt_off hd (Nat.lt_succ_self (c + 1)); omega)

/-- `degAux` with fuel `k` computes `deg` below `off k`. -/
theorem degAux_eq_deg (hd : 0 < d) {c k : ℕ} (hc : c < off d k) : degAux d c k 0 = degOf d c :=
  deg_unique hd (degAux_spec hd c k 0 (by simp [off]) (by simpa using hc)) (deg_spec hd c)

theorem deg_eq (hd : 0 < d) {c g : ℕ} (h1 : off d g ≤ c) (h2 : c < off d (g + 1)) : degOf d c = g :=
  deg_unique hd (deg_spec hd c) ⟨h1, h2⟩

theorem idx_lt (hd : 0 < d) (c : ℕ) : c - off d (degOf d c) < d ^ degOf d c := by
  have := deg_spec hd c; rw [off_succ] at this; omega

end Positions

section Decode

variable {d : ℕ} [NeZero d]

theorem letter_of_lt {j : ℕ} (hj : j < d) : (letter d j : ℕ) = j := Nat.mod_eq_of_lt hj

theorem wordOf_succ (g idx : ℕ) :
    wordOf d (g + 1) idx = wordOf d g (idx / d) * FreeMonoid.of (letter d idx) := rfl

/-- Appending a letter: `w(g + 1, idx·d + j) = w(g, idx) X_j`. -/
theorem wordOf_append (g idx j : ℕ) (hj : j < d) :
    wordOf d (g + 1) (idx * d + j) = wordOf d g idx * FreeMonoid.of (letter d j) := by
  have hd := NeZero.pos d
  rw [wordOf_succ]
  congr 2
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  · ext; simp [letter, Nat.add_mod, Nat.mod_eq_of_lt hj]

/-- Prepending a letter: `w(g + 1, j·d^g + idx) = X_j w(g, idx)`. -/
theorem wordOf_prepend (j : ℕ) (hj : j < d) :
    ∀ g idx, idx < d ^ g → wordOf d (g + 1) (j * d ^ g + idx) = FreeMonoid.of (letter d j) * wordOf d g idx := by
  have hd := NeZero.pos d
  intro g
  induction g with
  | zero =>
    intro idx hidx
    simp at hidx; subst hidx
    simp [wordOf]
  | succ g ih =>
    intro idx hidx
    rw [wordOf_succ (d := d) (g + 1) (j * d ^ (g + 1) + idx), wordOf_succ (d := d) g idx]
    have h1 : (j * d ^ (g + 1) + idx) / d = j * d ^ g + idx / d := by
      rw [pow_succ, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.add_comm]
    have h2 : letter d (j * d ^ (g + 1) + idx) = letter d idx := by
      ext; simp [letter, pow_succ, ← Nat.mul_assoc, Nat.add_mod]
    rw [h1, h2, ih _ (Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hidx; exact hidx)), mul_assoc]

/-- The length of `wordOf g idx` is `g`. -/
theorem length_wordOf (g idx : ℕ) : (wordOf d g idx).length = g := by
  induction g generalizing idx with
  | zero => rfl
  | succ g ih => simp [wordOf_succ, ih]

end Decode

/-! ## Arithmetic modulo `D` -/

section Modulo

variable (d : ℕ) [NeZero d]

/-- `D • R`. -/
def DR (D : ℕ) : Submodule ℤ (R d) := LinearMap.range (((D : ℕ) : ℤ) • LinearMap.id)

theorem smul_mem_DR (D : ℕ) (x : R d) : ((D : ℕ) : ℤ) • x ∈ DR d D := ⟨x, by simp⟩

variable {d}

theorem natCast_smul_mod (D a : ℕ) (x : R d) :
    ((a : ℕ) : ℤ) • x - ((a % D : ℕ) : ℤ) • x ∈ DR d D := by
  have h : ((a : ℕ) : ℤ) = ((a % D : ℕ) : ℤ) + ((D : ℕ) : ℤ) * ((a / D : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div a D).symm
  have : ((a : ℕ) : ℤ) • x - ((a % D : ℕ) : ℤ) • x = ((D : ℕ) : ℤ) • (((a / D : ℕ) : ℤ) • x) := by
    rw [smul_smul, ← sub_smul]; congr 1; linarith
  rw [this]; exact smul_mem_DR d D _

/-- `ins` adds `a · e_k`, modulo `D`. -/
theorem eval_ins (D k a : ℕ) (v : Vec) :
    eval d (ins D k a v) - (eval d v + ((a : ℕ) : ℤ) • e d k) ∈ DR d D := by
  induction v with
  | nil =>
    simp only [ins, eval_nil, zero_add]
    cases h : (a % D == 0)
    · simp only [Bool.cond_false, eval_cons, eval_nil, add_zero]
      rw [← neg_sub, Submodule.neg_mem_iff]; exact natCast_smul_mod D a _
    · simp only [Bool.cond_true, eval_nil, zero_sub, Submodule.neg_mem_iff]
      have h0 : a % D = 0 := by simpa using h
      simpa [h0] using natCast_smul_mod D a (e d k)
  | cons t v ih =>
    obtain ⟨k', b⟩ := t
    simp only [ins]
    cases hlt : Nat.blt k k'
    · cases heq : (k == k')
      · simp only [Bool.cond_false, eval_cons]
        have : ((b : ℕ) : ℤ) • e d k' + eval d (ins D k a v) - (((b : ℕ) : ℤ) • e d k' + eval d v + ((a : ℕ) : ℤ) • e d k) =
            eval d (ins D k a v) - (eval d v + ((a : ℕ) : ℤ) • e d k) := by abel
        rw [this]; exact ih
      · have hk : k = k' := by simpa using heq
        subst hk
        simp only [Bool.cond_false, Bool.cond_true]
        have hs := natCast_smul_mod D (a + b) (e d k)
        cases h : ((a + b) % D == 0)
        · simp only [Bool.cond_false, eval_cons]
          have : ((((a + b) % D : ℕ) : ℤ)) • e d k + eval d v - (((b : ℕ) : ℤ) • e d k + eval d v + ((a : ℕ) : ℤ) • e d k) =
              -(((a + b : ℕ) : ℤ) • e d k - (((a + b) % D : ℕ) : ℤ) • e d k) := by
            push_cast; rw [add_smul]; abel
          rw [this, Submodule.neg_mem_iff]; exact hs
        · have h0 : (a + b) % D = 0 := by simpa using h
          simp only [Bool.cond_true, eval_cons]
          have : eval d v - (((b : ℕ) : ℤ) • e d k + eval d v + ((a : ℕ) : ℤ) • e d k) =
              -(((a + b : ℕ) : ℤ) • e d k - (((a + b) % D : ℕ) : ℤ) • e d k) := by
            rw [h0]; push_cast; rw [add_smul]; simp; abel
          rw [this, Submodule.neg_mem_iff]; exact hs
    · simp only [Bool.cond_true]
      cases h : (a % D == 0)
      · simp only [Bool.cond_false, eval_cons]
        have : ((a % D : ℕ) : ℤ) • e d k + (((b : ℕ) : ℤ) • e d k' + eval d v) -
            (((b : ℕ) : ℤ) • e d k' + eval d v + ((a : ℕ) : ℤ) • e d k) =
            -(((a : ℕ) : ℤ) • e d k - ((a % D : ℕ) : ℤ) • e d k) := by abel
        rw [this, Submodule.neg_mem_iff]; exact natCast_smul_mod D a _
      · have h0 : a % D = 0 := by simpa using h
        simp only [Bool.cond_true, eval_cons]
        have : ((b : ℕ) : ℤ) • e d k' + eval d v - (((b : ℕ) : ℤ) • e d k' + eval d v + ((a : ℕ) : ℤ) • e d k) =
            -(((a : ℕ) : ℤ) • e d k - ((a % D : ℕ) : ℤ) • e d k) := by rw [h0]; simp
        rw [this, Submodule.neg_mem_iff]; exact natCast_smul_mod D a _

/-- `addSmul` is `w + a·v`, modulo `D`. -/
theorem eval_addSmul (D a : ℕ) (v : Vec) :
    ∀ w, eval d (addSmul D a v w) - (eval d w + ((a : ℕ) : ℤ) • eval d v) ∈ DR d D := by
  induction v with
  | nil => intro w; simp [addSmul]
  | cons t v ih =>
    intro w
    obtain ⟨c, b⟩ := t
    have h1 := ih (ins D c (a * b) w)
    have h2 := eval_ins (d := d) D c (a * b) w
    simp only [addSmul, List.foldl_cons] at h1 ⊢
    have : eval d (List.foldl (fun acc e => ins D e.1 (a * e.2) acc) (ins D c (a * b) w) v) -
        (eval d w + ((a : ℕ) : ℤ) • eval d ((c, b) :: v)) =
        (eval d (List.foldl (fun acc e => ins D e.1 (a * e.2) acc) (ins D c (a * b) w) v) -
          (eval d (ins D c (a * b) w) + ((a : ℕ) : ℤ) • eval d v)) +
        (eval d (ins D c (a * b) w) - (eval d w + ((a * b : ℕ) : ℤ) • e d c)) := by
      rw [eval_cons, smul_add, smul_smul]; push_cast; abel
    rw [this]; exact add_mem h1 h2

theorem eval_smul (D a : ℕ) (v : Vec) :
    eval d (smul D a v) - ((a : ℕ) : ℤ) • eval d v ∈ DR d D := by
  simpa [smul] using eval_addSmul (d := d) D a v []

/-- `red D a ≡ a` modulo `D`, for `D > 0`. -/
theorem red_smul (D : ℕ) (hD : 0 < D) (a : ℤ) (x : R d) :
    ((red D a : ℕ) : ℤ) • x - a • x ∈ DR d D := by
  have h1 : ((red D a : ℕ) : ℤ) = a % (D : ℤ) := by
    simp only [red]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have : ((red D a : ℕ) : ℤ) • x - a • x = ((D : ℕ) : ℤ) • ((-(a / (D : ℤ))) • x) := by
    rw [smul_smul, ← sub_smul, h1]; congr 1
    have := Int.emod_def a (D : ℤ); linarith
  rw [this]; exact smul_mem_DR d D _


theorem mem_DR {D : ℕ} {x : R d} : x ∈ DR d D ↔ ∃ y, ((D : ℕ) : ℤ) • y = x := by
  simp [DR]

/-! ## Monomials at positions, shifts -/

/-- `X_j`. -/
def X (j : ℕ) : R d := single (FreeMonoid.of (letter d j)) 1

theorem e_of_pos {g idx : ℕ} (hidx : idx < d ^ g) :
    e d (off d g + idx) = single (wordOf d g idx) 1 := by
  have hd := NeZero.pos d
  have hdeg : degOf d (off d g + idx) = g := deg_eq hd (by omega) (by rw [off_succ]; omega)
  simp only [e, wordAt, hdeg, Nat.add_sub_cancel_left]

theorem e_lshift (c : ℕ) {j : ℕ} (hj : j < d) :
    e d (off d (degOf d c + 1) + j * d ^ degOf d c + (c - off d (degOf d c))) = X j * e d c := by
  have hd := NeZero.pos d
  have hidx := idx_lt hd c
  have hlt : j * d ^ degOf d c + (c - off d (degOf d c)) < d ^ (degOf d c + 1) := by
    calc j * d ^ degOf d c + (c - off d (degOf d c)) < j * d ^ degOf d c + d ^ degOf d c :=
          Nat.add_lt_add_left hidx _
      _ = (j + 1) * d ^ degOf d c := by ring
      _ ≤ d * d ^ degOf d c := Nat.mul_le_mul_right _ hj
      _ = d ^ (degOf d c + 1) := by ring
  rw [Nat.add_assoc, e_of_pos hlt, wordOf_prepend j hj _ _ hidx]
  simp [X, e, wordAt, single_mul_single]

theorem e_rshift (c : ℕ) {j : ℕ} (hj : j < d) :
    e d (off d (degOf d c + 1) + (c - off d (degOf d c)) * d + j) = e d c * X j := by
  have hd := NeZero.pos d
  have hidx := idx_lt hd c
  have hlt : (c - off d (degOf d c)) * d + j < d ^ (degOf d c + 1) := by
    calc (c - off d (degOf d c)) * d + j < (c - off d (degOf d c)) * d + d := Nat.add_lt_add_left hj _
      _ = (c - off d (degOf d c) + 1) * d := by ring
      _ ≤ d ^ degOf d c * d := Nat.mul_le_mul_right _ hidx
      _ = d ^ (degOf d c + 1) := (pow_succ _ _).symm
  rw [Nat.add_assoc, e_of_pos hlt, wordOf_append _ _ _ hj]
  simp [X, e, wordAt, single_mul_single]

/-- A fold of `ins` over a vector, with positions moved by `f`, computes `φ (eval v)`. -/
theorem eval_foldl_ins (D : ℕ) (f : ℕ × ℕ → ℕ) (φ : R d →+ R d) (v : Vec)
    (hf : ∀ t ∈ v, e d (f t) = φ (e d t.1)) (acc : Vec) :
    eval d (v.foldl (fun acc t => ins D (f t) t.2 acc) acc) - (eval d acc + φ (eval d v)) ∈ DR d D := by
  induction v generalizing acc with
  | nil => simp
  | cons t v ih =>
    obtain ⟨c, a⟩ := t
    have h1 := ih (fun t ht => hf t (List.mem_cons_of_mem _ ht)) (ins D (f (c, a)) a acc)
    have h2 := eval_ins (d := d) D (f (c, a)) a acc
    rw [hf (c, a) List.mem_cons_self] at h2
    simp only [List.foldl_cons]
    have : eval d (List.foldl (fun acc t => ins D (f t) t.2 acc) (ins D (f (c, a)) a acc) v) -
          (eval d acc + φ (eval d ((c, a) :: v))) =
        (eval d (List.foldl (fun acc t => ins D (f t) t.2 acc) (ins D (f (c, a)) a acc) v) -
          (eval d (ins D (f (c, a)) a acc) + φ (eval d v))) +
        (eval d (ins D (f (c, a)) a acc) - (eval d acc + ((a : ℕ) : ℤ) • φ (e d c))) := by
      rw [eval_cons, map_add, map_zsmul]; abel
    rw [this]; exact add_mem h1 h2

theorem eval_lshift (D : ℕ) {j : ℕ} (hj : j < d) (v : Vec) :
    eval d (lshift d D j v) - X j * eval d v ∈ DR d D := by
  have h := eval_foldl_ins (d := d) D
    (fun t => off d (degOf d t.1 + 1) + j * d ^ degOf d t.1 + (t.1 - off d (degOf d t.1)))
    (AddMonoidHom.mulLeft (X j)) v (fun t _ => e_lshift t.1 hj) []
  simp only [eval_nil, zero_add, AddMonoidHom.coe_mulLeft] at h
  exact h

theorem eval_rshift (D : ℕ) {j : ℕ} (hj : j < d) (v : Vec) :
    eval d (rshift d D j v) - eval d v * X j ∈ DR d D := by
  have h := eval_foldl_ins (d := d) D
    (fun t => off d (degOf d t.1 + 1) + (t.1 - off d (degOf d t.1)) * d + j)
    (AddMonoidHom.mulRight (X j)) v (fun t _ => e_rshift t.1 hj) []
  simp only [eval_nil, zero_add, AddMonoidHom.coe_mulRight] at h
  exact h

/-! ## The degree ideal `I_k` -/

variable (d) in
/-- The monomials of length `≥ k`. -/
def Ik (k : ℕ) : Submodule ℤ (R d) :=
  Submodule.span ℤ {x | ∃ w : FreeMonoid (Fin d), k ≤ w.length ∧ x = single w 1}

theorem single_mem_Ik {k : ℕ} {w : FreeMonoid (Fin d)} (hw : k ≤ w.length) (a : ℤ) :
    single w a ∈ Ik d k := by
  have : single w a = a • single w (1 : ℤ) := by rw [smul_single', mul_one]
  rw [this]; exact Submodule.smul_mem _ a (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem Ik_mono {k k' : ℕ} (h : k ≤ k') : Ik d k' ≤ Ik d k :=
  Submodule.span_mono fun _ ⟨w, hw, hx⟩ => ⟨w, by omega, hx⟩

/-- `u · I_k · v ⊆ I_{k + |u| + |v|}`. -/
theorem single_mul_mem_Ik {k : ℕ} {x : R d} (hx : x ∈ Ik d k) (u v : FreeMonoid (Fin d)) :
    single u 1 * x * single v 1 ∈ Ik d (k + u.length + v.length) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [single_mul_single, single_mul_single]
    exact single_mem_Ik (by simp only [FreeMonoid.length_mul]; omega) _
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem single_eq_smul (m : FreeMonoid (Fin d)) (r : ℤ) : (single m r : R d) = r • single m 1 := by
  rw [smul_single', mul_one]

theorem mul_mem_Ik {k : ℕ} {x : R d} (hx : x ∈ Ik d k) (y : R d) : x * y ∈ Ik d k := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add]; exact add_mem hf hg
  | single m r =>
    rw [single_eq_smul, mul_smul_comm]
    refine Submodule.smul_mem _ r ?_
    have h := single_mul_mem_Ik hx 1 m
    rw [← one_def, one_mul] at h
    exact Ik_mono (by omega) h

theorem mem_Ik_mul {k : ℕ} {x : R d} (hx : x ∈ Ik d k) (y : R d) : y * x ∈ Ik d k := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul]; exact add_mem hf hg
  | single m r =>
    rw [single_eq_smul, smul_mul_assoc]
    refine Submodule.smul_mem _ r ?_
    have h := single_mul_mem_Ik hx m 1
    rw [← one_def, mul_one] at h
    exact Ik_mono (by omega) h

theorem sup_mul_mem {D k : ℕ} {x : R d} (hx : x ∈ DR d D ⊔ Ik d k) (y : R d) :
    x * y ∈ DR d D ⊔ Ik d k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [add_mul]
  refine Submodule.add_mem_sup ?_ (mul_mem_Ik hb y)
  obtain ⟨z, rfl⟩ := mem_DR.mp ha
  rw [smul_mul_assoc]; exact smul_mem_DR d D _

/-! ## Magnus terms -/

/-- `Σ_{m<k} C(e, m) X_j^m`. -/
def S (k j : ℕ) (ex : ℤ) : R d :=
  ∑ m ∈ Finset.range k, binom ex m • single (FreeMonoid.of (letter d j) ^ m) 1

variable (d) in
/-- The Magnus image of a flat word, every factor `(1 + X_j)^e` cut below degree `k`. -/
def mt (k : ℕ) (w : List (ℕ × ℤ)) : R d := (w.map fun f => S k (f.1 - 1) f.2).prod

theorem binom_zero (ex : ℤ) : binom ex 0 = 1 := by simp [binom, descProd, fact]

theorem length_pow_of (l : Fin d) (m : ℕ) : (FreeMonoid.of l ^ m).length = m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, FreeMonoid.length_mul, ih, FreeMonoid.length_of]

/-- The terms `genPowTerms` adds, from step `m` on. -/
theorem eval_genPowTerms (D k j : ℕ) (hj : j < d) (hD : 0 < D) (ex : ℤ) (c a : ℕ) :
    ∀ fuel m idx acc, 1 ≤ m → idx < d ^ (degOf d c + m - 1) →
      wordOf d (degOf d c + m - 1) idx = wordAt d c * FreeMonoid.of (letter d j) ^ (m - 1) →
      k ≤ degOf d c + m + fuel →
      eval d (genPowTerms d D k j ex (degOf d c) a fuel m idx acc) -
        (eval d acc + ((a : ℕ) : ℤ) • ∑ m' ∈ Finset.Ico m k,
          binom ex m' • single (wordAt d c * FreeMonoid.of (letter d j) ^ m') 1) ∈ DR d D ⊔ Ik d k := by
  have hd := NeZero.pos d
  set g := degOf d c with hg
  have hlen : (wordAt d c).length = g := length_wordOf _ _
  -- the terms of degree `≥ k`
  have high : ∀ m, k ≤ g + m → ((a : ℕ) : ℤ) • ∑ m' ∈ Finset.Ico m k,
      binom ex m' • single (wordAt d c * FreeMonoid.of (letter d j) ^ m') (1 : ℤ) ∈ Ik d k := by
    intro m hm
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m' hm' => Submodule.smul_mem _ _ ?_)
    rw [Finset.mem_Ico] at hm'
    exact single_mem_Ik (by rw [FreeMonoid.length_mul, hlen, length_pow_of]; omega) _
  intro fuel
  induction fuel with
  | zero =>
    intro m idx acc _ _ _ hk
    simp only [genPowTerms, sub_add_cancel_left, Submodule.neg_mem_iff]
    exact Submodule.mem_sup_right (high m (by omega))
  | succ fuel ih =>
    intro m idx acc hm hidx hw hk
    simp only [genPowTerms]
    by_cases hgm : g + m < k
    · have hb : Nat.blt (g + m) k = true := Nat.blt_eq.mpr hgm
      simp only [hb, Bool.cond_true]
      have hgm1 : g + m - 1 + 1 = g + m := by omega
      have hidx' : idx * d + j < d ^ (g + (m + 1) - 1) := by
        rw [show g + (m + 1) - 1 = g + m - 1 + 1 by omega]
        calc idx * d + j < idx * d + d := Nat.add_lt_add_left hj _
          _ = (idx + 1) * d := by ring
          _ ≤ d ^ (g + m - 1) * d := Nat.mul_le_mul_right _ hidx
          _ = d ^ (g + m - 1 + 1) := (pow_succ _ _).symm
      have hw' : wordOf d (g + (m + 1) - 1) (idx * d + j) =
          wordAt d c * FreeMonoid.of (letter d j) ^ (m + 1 - 1) := by
        rw [show g + (m + 1) - 1 = g + m - 1 + 1 by omega, wordOf_append _ _ _ hj, hw, mul_assoc,
          ← pow_succ, show m - 1 + 1 = m + 1 - 1 by omega]
      have h1 := ih (m + 1) (idx * d + j)
        (ins D (off d (g + m) + (idx * d + j)) (a * red D (binom ex m)) acc) (by omega) hidx' hw'
        (by omega)
      have hpos : e d (off d (g + m) + (idx * d + j)) =
          single (wordAt d c * FreeMonoid.of (letter d j) ^ m) 1 := by
        have hlt : idx * d + j < d ^ (g + m) := by
          have := hidx'; rwa [show g + (m + 1) - 1 = g + m by omega] at this
        rw [e_of_pos hlt, ← hgm1, wordOf_append _ _ _ hj, hw, mul_assoc, ← pow_succ,
          show m - 1 + 1 = m by omega]
      have h2 := eval_ins (d := d) D (off d (g + m) + (idx * d + j)) (a * red D (binom ex m)) acc
      rw [hpos] at h2
      have h3 := red_smul (d := d) D hD (binom ex m)
        (((a : ℕ) : ℤ) • single (wordAt d c * FreeMonoid.of (letter d j) ^ m) 1)
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m < k)]
      have : eval d (genPowTerms d D k j ex g a fuel (m + 1) (idx * d + j)
            (ins D (off d (g + m) + (idx * d + j)) (a * red D (binom ex m)) acc)) -
          (eval d acc + ((a : ℕ) : ℤ) • (binom ex m • single (wordAt d c * FreeMonoid.of (letter d j) ^ m) 1 +
            ∑ m' ∈ Finset.Ico (m + 1) k,
              binom ex m' • single (wordAt d c * FreeMonoid.of (letter d j) ^ m') 1)) =
          (eval d (genPowTerms d D k j ex g a fuel (m + 1) (idx * d + j)
            (ins D (off d (g + m) + (idx * d + j)) (a * red D (binom ex m)) acc)) -
            (eval d (ins D (off d (g + m) + (idx * d + j)) (a * red D (binom ex m)) acc) +
              ((a : ℕ) : ℤ) • ∑ m' ∈ Finset.Ico (m + 1) k,
                binom ex m' • single (wordAt d c * FreeMonoid.of (letter d j) ^ m') 1)) +
          (eval d (ins D (off d (g + m) + (idx * d + j)) (a * red D (binom ex m)) acc) -
            (eval d acc + ((a * red D (binom ex m) : ℕ) : ℤ) •
              single (wordAt d c * FreeMonoid.of (letter d j) ^ m) 1)) +
          (((red D (binom ex m) : ℕ) : ℤ) • (((a : ℕ) : ℤ) •
              single (wordAt d c * FreeMonoid.of (letter d j) ^ m) 1) -
            binom ex m • (((a : ℕ) : ℤ) • single (wordAt d c * FreeMonoid.of (letter d j) ^ m) 1)) := by
        push_cast
        simp only [smul_add, smul_smul]
        rw [mul_comm (binom ex m), mul_comm ((red D (binom ex m) : ℕ) : ℤ)]
        abel
      rw [this]
      exact add_mem (add_mem h1 (Submodule.mem_sup_left h2)) (Submodule.mem_sup_left h3)
    · have hb : Nat.blt (g + m) k = false := Bool.eq_false_iff.mpr fun h => hgm (Nat.blt_eq.mp h)
      simp only [hb, Bool.cond_false, sub_add_cancel_left, Submodule.neg_mem_iff]
      exact Submodule.mem_sup_right (high m (by omega))

theorem e_mul_S (c k j : ℕ) (hk : 0 < k) (ex : ℤ) :
    e d c * S k j ex = e d c + ∑ m' ∈ Finset.Ico 1 k,
      binom ex m' • single (wordAt d c * FreeMonoid.of (letter d j) ^ m') 1 := by
  rw [S, Finset.mul_sum, Finset.sum_range_eq_add_Ico _ hk]
  simp only [mul_smul_comm, e, single_mul_single, mul_one, pow_zero, binom_zero, one_smul]

/-- `mulGenPow` multiplies by `S k j e`, modulo `D` and degree `k`. -/
theorem eval_mulGenPow (D k j : ℕ) (hj : j < d) (hD : 0 < D) (hk : 0 < k) (ex : ℤ) (x : Vec) :
    eval d (mulGenPow d D k j ex x) - eval d x * S k j ex ∈ DR d D ⊔ Ik d k := by
  have hd := NeZero.pos d
  suffices h : ∀ v acc, eval d (v.foldl (fun acc t => let g := degOf d t.1
      genPowTerms d D k j ex g t.2 k 1 (t.1 - off d g) acc) acc) -
      (eval d acc + (eval d v * S k j ex - eval d v)) ∈ DR d D ⊔ Ik d k by
    have := h x x; rw [add_sub_cancel] at this; exact this
  intro v
  induction v with
  | nil => intro acc; simp
  | cons t v ih =>
    intro acc
    obtain ⟨c, a⟩ := t
    simp only [List.foldl_cons]
    have h1 := ih (genPowTerms d D k j ex (degOf d c) a k 1 (c - off d (degOf d c)) acc)
    have h2 := eval_genPowTerms (d := d) D k j hj hD ex c a k 1 (c - off d (degOf d c)) acc le_rfl
      (by simpa using idx_lt hd c) (by simp [wordAt]) (by omega)
    have hsum : ∑ m' ∈ Finset.Ico 1 k, binom ex m' • single (wordAt d c * FreeMonoid.of (letter d j) ^ m') (1 : ℤ) =
        e d c * S k j ex - e d c := by rw [e_mul_S c k j hk ex]; abel
    rw [hsum] at h2
    have : eval d (List.foldl (fun acc t => let g := degOf d t.1
          genPowTerms d D k j ex g t.2 k 1 (t.1 - off d g) acc)
          (genPowTerms d D k j ex (degOf d c) a k 1 (c - off d (degOf d c)) acc) v) -
        (eval d acc + (eval d ((c, a) :: v) * S k j ex - eval d ((c, a) :: v))) =
        (eval d (List.foldl (fun acc t => let g := degOf d t.1
          genPowTerms d D k j ex g t.2 k 1 (t.1 - off d g) acc)
          (genPowTerms d D k j ex (degOf d c) a k 1 (c - off d (degOf d c)) acc) v) -
          (eval d (genPowTerms d D k j ex (degOf d c) a k 1 (c - off d (degOf d c)) acc) +
            (eval d v * S k j ex - eval d v))) +
        (eval d (genPowTerms d D k j ex (degOf d c) a k 1 (c - off d (degOf d c)) acc) -
          (eval d acc + ((a : ℕ) : ℤ) • (e d c * S k j ex - e d c))) := by
      rw [eval_cons, add_mul, smul_mul_assoc]; simp only [smul_sub]; abel
    rw [this]; exact add_mem h1 h2

/-- A word with letters `1..d`. -/
def okWord (d : ℕ) (w : List (ℕ × ℤ)) : Prop := ∀ f ∈ w, 0 < f.1 ∧ f.1 ≤ d

theorem eval_unit : eval d [(0, 1)] = 1 := by
  have h0 : wordAt d 0 = 1 := by
    have : degOf d 0 = 0 := by
      simp [degOf, degAux, off]
    simp [wordAt, this, wordOf]
  simp [eval, e, h0, one_def]

theorem eval_magnus (D k : ℕ) (hD : 0 < D) (hk : 0 < k) (w : List (ℕ × ℤ)) (hw : okWord d w) :
    eval d (magnus d D k w) - mt d k w ∈ DR d D ⊔ Ik d k := by
  suffices h : ∀ w : List (ℕ × ℤ), okWord d w → ∀ x : Vec,
      eval d (w.foldl (fun x f => mulGenPow d D k (f.1 - 1) f.2 x) x) - eval d x * mt d k w ∈
        DR d D ⊔ Ik d k by
    have := h w hw [(0, 1)]; rwa [eval_unit, one_mul] at this
  intro w
  induction w with
  | nil => intro _ x; simp [mt]
  | cons f w ih =>
    intro hw x
    have hf := hw f List.mem_cons_self
    have h1 := ih (fun f' hf' => hw f' (List.mem_cons_of_mem _ hf')) (mulGenPow d D k (f.1 - 1) f.2 x)
    have h2 := sup_mul_mem (eval_mulGenPow (d := d) D k (f.1 - 1) (by omega) hD hk f.2 x) (mt d k w)
    simp only [List.foldl_cons]
    have : eval d (List.foldl (fun x f => mulGenPow d D k (f.1 - 1) f.2 x) (mulGenPow d D k (f.1 - 1) f.2 x) w) -
        eval d x * mt d k (f :: w) =
        (eval d (List.foldl (fun x f => mulGenPow d D k (f.1 - 1) f.2 x) (mulGenPow d D k (f.1 - 1) f.2 x) w) -
          eval d (mulGenPow d D k (f.1 - 1) f.2 x) * mt d k w) +
        (eval d (mulGenPow d D k (f.1 - 1) f.2 x) - eval d x * S k (f.1 - 1) f.2) * mt d k w := by
      simp only [mt, List.map_cons, List.prod_cons]; noncomm_ring
    rw [this]; exact add_mem h1 h2

theorem eval_magnus1 (D k : ℕ) (hD : 0 < D) (hk : 0 < k) (w : List (ℕ × ℤ)) (hw : okWord d w) :
    eval d (magnus1 d D k w) - (mt d k w - 1) ∈ DR d D ⊔ Ik d k := by
  have h1 := eval_magnus (d := d) D k hD hk w hw
  have h2 := eval_ins (d := d) D 0 (D - 1) (magnus d D k w)
  have he0 : e d 0 = 1 := by have := eval_unit (d := d); simpa [eval] using this
  rw [he0] at h2
  have : eval d (magnus1 d D k w) - (mt d k w - 1) =
      (eval d (ins D 0 (D - 1) (magnus d D k w)) - (eval d (magnus d D k w) + ((D - 1 : ℕ) : ℤ) • 1)) +
      (eval d (magnus d D k w) - mt d k w) + ((D : ℕ) : ℤ) • 1 := by
    rw [magnus1, Nat.cast_sub (by omega : 1 ≤ D)]; simp only [sub_smul, one_smul, Nat.cast_one]; abel
  rw [this]
  exact add_mem (add_mem (Submodule.mem_sup_left h2) h1) (Submodule.mem_sup_left (smul_mem_DR d D _))

/-! ## The targets `Lt k` -/

variable (d) in
/-- The relator part: `X_u (mt k r − 1) X_v`. -/
def Jt (rels : List (ℕ × List (ℕ × ℤ))) (k : ℕ) : Submodule ℤ (R d) :=
  Submodule.span ℤ {x | ∃ r ∈ rels, ∃ u v : FreeMonoid (Fin d), x = single u 1 * (mt d k r.2 - 1) * single v 1}

variable (d) in
/-- `J_k + D·A_k`, pulled back to `R`. -/
def Lt (rels : List (ℕ × List (ℕ × ℤ))) (D k : ℕ) : Submodule ℤ (R d) := Jt d rels k ⊔ Ik d k ⊔ DR d D

variable {rels : List (ℕ × List (ℕ × ℤ))}

theorem DR_le_Lt (D k : ℕ) : DR d D ≤ Lt d rels D k := le_sup_right
theorem Ik_le_Lt (D k : ℕ) : Ik d k ≤ Lt d rels D k :=
  (le_sup_right : Ik d k ≤ Jt d rels k ⊔ Ik d k).trans le_sup_left
theorem Jt_le_Lt (D k : ℕ) : Jt d rels k ≤ Lt d rels D k :=
  (le_sup_left : Jt d rels k ≤ Jt d rels k ⊔ Ik d k).trans le_sup_left
theorem M_le_Lt (D k : ℕ) : DR d D ⊔ Ik d k ≤ Lt d rels D k := sup_le (DR_le_Lt D k) (Ik_le_Lt D k)

theorem prod_sub_mem_Ik {k : ℕ} (l : List (R d × R d)) (h : ∀ q ∈ l, q.1 - q.2 ∈ Ik d k) :
    (l.map Prod.fst).prod - (l.map Prod.snd).prod ∈ Ik d k := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq := h q List.mem_cons_self
    have hl := ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      show q.1 * (l.map Prod.fst).prod - q.2 * (l.map Prod.snd).prod =
        (q.1 - q.2) * (l.map Prod.fst).prod + q.2 * ((l.map Prod.fst).prod - (l.map Prod.snd).prod) by
      noncomm_ring]
    exact add_mem (mul_mem_Ik hq _) (mem_Ik_mul hl _)

theorem S_sub_mem (k j : ℕ) (ex : ℤ) : (S k j ex : R d) - S (k + 1) j ex ∈ Ik d k := by
  rw [S, S, Finset.sum_range_succ, sub_add_cancel_left, Submodule.neg_mem_iff]
  exact Submodule.smul_mem _ _ (single_mem_Ik (by rw [length_pow_of]) 1)

theorem mt_sub_mem (k : ℕ) (w : List (ℕ × ℤ)) : mt d k w - mt d (k + 1) w ∈ Ik d k := by
  have := prod_sub_mem_Ik (d := d) (k := k) (w.map fun f => (S k (f.1 - 1) f.2, S (k + 1) (f.1 - 1) f.2))
    (by intro q hq; obtain ⟨f, -, rfl⟩ := List.mem_map.mp hq; exact S_sub_mem k _ _)
  simpa [mt, List.map_map, Function.comp_def] using this

/-- `X_j · L_k ⊆ L_{k+1}` (Lemma N1, easy direction). -/
theorem X_mul_mem {D k j : ℕ} {x : R d} (hx : x ∈ Lt d rels D k) : X j * x ∈ Lt d rels D (k + 1) := by
  obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
  clear hab hx
  rw [mul_add, mul_add]
  refine add_mem (add_mem ?_ ?_) ?_
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, u, v, rfl⟩ := hy
      have hsplit : X j * (single u 1 * (mt d k r.2 - 1) * single v 1) =
          single (FreeMonoid.of (letter d j) * u) 1 * (mt d (k + 1) r.2 - 1) * single v 1 +
          single (FreeMonoid.of (letter d j) * u) 1 * (mt d k r.2 - mt d (k + 1) r.2) * single v 1 := by
        rw [X, ← mul_assoc, ← mul_assoc, single_mul_single, one_mul]; noncomm_ring
      rw [hsplit]
      refine add_mem (Jt_le_Lt D (k + 1) (Submodule.subset_span ⟨r, hr, _, v, rfl⟩)) (Ik_le_Lt D (k + 1) ?_)
      have := single_mul_mem_Ik (mt_sub_mem (d := d) k r.2) (FreeMonoid.of (letter d j) * u) v
      exact Ik_mono (by simp only [FreeMonoid.length_mul, FreeMonoid.length_of]; omega) this
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul n y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hy
  · refine Ik_le_Lt D (k + 1) ?_
    have := single_mul_mem_Ik hb (FreeMonoid.of (letter d j)) 1
    rw [← one_def, mul_one] at this
    exact Ik_mono (by simp only [FreeMonoid.length_of, FreeMonoid.length_one]; omega) this
  · obtain ⟨z, rfl⟩ := mem_DR.mp hc
    rw [mul_smul_comm]; exact DR_le_Lt D (k + 1) (smul_mem_DR d D _)

/-- `L_k · X_j ⊆ L_{k+1}`. -/
theorem mul_X_mem {D k j : ℕ} {x : R d} (hx : x ∈ Lt d rels D k) : x * X j ∈ Lt d rels D (k + 1) := by
  obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
  clear hab hx
  rw [add_mul, add_mul]
  refine add_mem (add_mem ?_ ?_) ?_
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, u, v, rfl⟩ := hy
      have hsplit : single u 1 * (mt d k r.2 - 1) * single v 1 * X j =
          single u 1 * (mt d (k + 1) r.2 - 1) * single (v * FreeMonoid.of (letter d j)) 1 +
          single u 1 * (mt d k r.2 - mt d (k + 1) r.2) * single (v * FreeMonoid.of (letter d j)) 1 := by
        rw [X, mul_assoc _ (single v 1), single_mul_single, one_mul]; noncomm_ring
      rw [hsplit]
      refine add_mem (Jt_le_Lt D (k + 1) (Submodule.subset_span ⟨r, hr, u, _, rfl⟩)) (Ik_le_Lt D (k + 1) ?_)
      have := single_mul_mem_Ik (mt_sub_mem (d := d) k r.2) u (v * FreeMonoid.of (letter d j))
      exact Ik_mono (by simp only [FreeMonoid.length_mul, FreeMonoid.length_of]; omega) this
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact add_mem hy hz
    | smul n y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hy
  · refine Ik_le_Lt D (k + 1) ?_
    have := single_mul_mem_Ik hb 1 (FreeMonoid.of (letter d j))
    rw [← one_def, one_mul] at this
    exact Ik_mono (by simp only [FreeMonoid.length_of, FreeMonoid.length_one]; omega) this
  · obtain ⟨z, rfl⟩ := mem_DR.mp hc
    rw [smul_mul_assoc]; exact DR_le_Lt D (k + 1) (smul_mem_DR d D _)

end Modulo

/-! ## The replay -/

section Replay

variable {d : ℕ} [NeZero d]

theorem find_mem {L : Submodule ℤ (R d)} (id : ℕ) :
    ∀ cur : List (ℕ × Vec), (∀ y ∈ cur, eval d y.2 ∈ L) → eval d (find id cur) ∈ L
  | [], _ => by simp [find]
  | (i, v) :: t, h => by
    simp only [find]
    cases hb : (i == id)
    · simp only [Bool.cond_false]; exact find_mem id t fun y hy => h y (List.mem_cons_of_mem _ hy)
    · simp only [Bool.cond_true]; exact h (i, v) List.mem_cons_self

theorem findWord_cases (i : ℕ) :
    ∀ l : List (ℕ × List (ℕ × ℤ)), findWord i l = [] ∨ ∃ y ∈ l, y.2 = findWord i l
  | [] => by simp [findWord]
  | (i', w) :: t => by
    simp only [findWord]
    cases hb : (i' == i)
    · simp only [Bool.cond_false]
      rcases findWord_cases i t with h | ⟨y, hy, hyw⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hyw⟩
    · simp only [Bool.cond_true]; exact Or.inr ⟨(i', w), List.mem_cons_self, rfl⟩

theorem combo_sub_mem {L : Submodule ℤ (R d)} {D : ℕ} (hDL : DR d D ≤ L)
    (cur : List (ℕ × Vec)) (hcur : ∀ y ∈ cur, eval d y.2 ∈ L) (terms : List (ℕ × ℤ)) :
    ∀ w : Vec, eval d (combo D cur terms w) - eval d w ∈ L := by
  induction terms with
  | nil => intro w; simp [combo]
  | cons t terms ih =>
    intro w
    have h1 := ih (addSmul D (red D t.2) (find t.1 cur) w)
    have h2 := eval_addSmul (d := d) D (red D t.2) (find t.1 cur) w
    have h3 := Submodule.smul_mem L ((red D t.2 : ℕ) : ℤ) (find_mem t.1 cur hcur)
    simp only [combo, List.foldl_cons] at h1 ⊢
    rw [show ∀ a b c : R d, a - c = (a - b) + (b - (c + ((red D t.2 : ℕ) : ℤ) • eval d (find t.1 cur))) +
      ((red D t.2 : ℕ) : ℤ) • eval d (find t.1 cur) from fun a b c => by abel]
    exact add_mem (add_mem h1 (hDL h2)) h3

theorem combo_eq_nil_mem {L : Submodule ℤ (R d)} {D : ℕ} (hDL : DR d D ≤ L)
    {cur : List (ℕ × Vec)} (hcur : ∀ y ∈ cur, eval d y.2 ∈ L) {terms : List (ℕ × ℤ)} {w : Vec}
    (h : combo D cur terms w = []) : eval d w ∈ L := by
  have := combo_sub_mem hDL cur hcur terms w
  rw [h, eval_nil, zero_sub, Submodule.neg_mem_iff] at this; exact this

end Replay

section Trace

variable (T : Trace) [NeZero T.d]

/-- The level-`k` target of a trace. -/
abbrev LT (k : ℕ) : Submodule ℤ (R T.d) := Lt T.d T.rels (T.p ^ T.E) k

theorem genVec_mem (hD : 0 < T.p ^ T.E) (hrels : ∀ r ∈ T.rels, okWord T.d r.2) (k : ℕ)
    (prev : List (ℕ × Vec)) (hprev : ∀ y ∈ prev, eval T.d y.2 ∈ LT T k) (gen : Gen) :
    eval T.d (genVec T (k + 1) prev gen) ∈ LT T (k + 1) := by
  cases gen with
  | zero => simp [genVec]
  | rel i =>
    simp only [genVec]
    have hok : okWord T.d (findWord i T.rels) := by
      rcases findWord_cases i T.rels with h | ⟨y, hy, hyw⟩
      · rw [h]; intro f hf; simp at hf
      · rw [← hyw]; exact hrels y hy
    have h1 := M_le_Lt (rels := T.rels) _ _
      (eval_magnus1 (d := T.d) (T.p ^ T.E) (k + 1) hD (Nat.succ_pos k) _ hok)
    have h2 : mt T.d (k + 1) (findWord i T.rels) - 1 ∈ LT T (k + 1) := by
      rcases findWord_cases i T.rels with h | ⟨y, hy, hyw⟩
      · rw [h]; simp [mt]
      · rw [← hyw]
        refine Jt_le_Lt _ _ (Submodule.subset_span ⟨y, hy, 1, 1, ?_⟩)
        rw [← one_def, one_mul, mul_one]
    have := add_mem h1 h2; rwa [sub_add_cancel] at this
  | lsh id j =>
    simp only [genVec]
    cases hj : Nat.blt j T.d
    · simp
    · have hj' : j < T.d := Nat.blt_eq.mp hj
      simp only [Bool.cond_true]
      have h1 := DR_le_Lt (rels := T.rels) (T.p ^ T.E) (k + 1)
        (eval_lshift (d := T.d) (T.p ^ T.E) hj' (find id prev))
      have h2 := X_mul_mem (j := j) (find_mem id prev hprev)
      have := add_mem h1 h2; rwa [sub_add_cancel] at this
  | rsh id j =>
    simp only [genVec]
    cases hj : Nat.blt j T.d
    · simp
    · have hj' : j < T.d := Nat.blt_eq.mp hj
      simp only [Bool.cond_true]
      have h1 := DR_le_Lt (rels := T.rels) (T.p ^ T.E) (k + 1)
        (eval_rshift (d := T.d) (T.p ^ T.E) hj' (find id prev))
      have h2 := mul_X_mem (j := j) (find_mem id prev hprev)
      have := add_mem h1 h2; rwa [sub_add_cancel] at this

/-- Lines (statement 3 of `cert/TRACE.md`): every vector of a level lies in its target. -/
theorem runLevel_mem (hD : 0 < T.p ^ T.E) (hrels : ∀ r ∈ T.rels, okWord T.d r.2) (k : ℕ)
    (prev : List (ℕ × Vec)) (hprev : ∀ y ∈ prev, eval T.d y.2 ∈ LT T k) :
    ∀ (ls : List Line) (cur : List (ℕ × Vec)), (∀ y ∈ cur, eval T.d y.2 ∈ LT T (k + 1)) →
      ∀ y ∈ runLevel T (k + 1) prev ls cur, eval T.d y.2 ∈ LT T (k + 1) := by
  intro ls
  induction ls with
  | nil => intro cur hcur; simpa [runLevel] using hcur
  | cons l ls ih =>
    intro cur hcur
    simp only [runLevel]
    apply ih
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have hg := genVec_mem T hD hrels k prev hprev l.gen
      have hc := combo_sub_mem (DR_le_Lt (rels := T.rels) _ _) cur hcur l.terms (genVec T (k + 1) prev l.gen)
      have hcm : eval T.d (combo (T.p ^ T.E) cur l.terms (genVec T (k + 1) prev l.gen)) ∈ LT T (k + 1) := by
        have := add_mem hc hg; rwa [sub_add_cancel] at this
      have hs := eval_smul (d := T.d) (T.p ^ T.E) (red (T.p ^ T.E) l.u)
        (combo (T.p ^ T.E) cur l.terms (genVec T (k + 1) prev l.gen))
      have := add_mem (DR_le_Lt (rels := T.rels) _ (k + 1) hs) (Submodule.smul_mem (LT T (k + 1)) ((red (T.p ^ T.E) l.u : ℕ) : ℤ) hcm)
      rwa [sub_add_cancel] at this
    · exact hcur y hy

theorem runLevels_mem (hD : 0 < T.p ^ T.E) (hrels : ∀ r ∈ T.rels, okWord T.d r.2) :
    ∀ (lv : List (ℕ × List Line)) (k : ℕ) (prev : List (ℕ × Vec)),
      (∀ y ∈ prev, eval T.d y.2 ∈ LT T k) →
      ∀ k' cur, runLevels T lv k prev = some (k', cur) → ∀ y ∈ cur, eval T.d y.2 ∈ LT T k'
  | [], k, prev, hprev, k', cur, h => by
    simp only [runLevels, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hprev
  | (k1, ls) :: rest, k, prev, hprev, k', cur, h => by
    simp only [runLevels] at h
    cases hb : (k1 == k + 1)
    · simp [hb] at h
    · have hk : k1 = k + 1 := by simpa using hb
      simp only [hb, Bool.cond_true] at h
      subst hk
      exact runLevels_mem hD hrels rest (k + 1) _
        (runLevel_mem T hD hrels k prev hprev ls [] (by simp)) k' cur h

end Trace

/-! ## Positions of words -/

section Index

variable {d : ℕ} [NeZero d]

/-- The index of a word within its degree. -/
def idxOf (w : List (Fin d)) : ℕ := w.foldl (fun acc l => acc * d + l) 0

theorem idxOf_spec (w : List (Fin d)) :
    idxOf w < d ^ w.length ∧ wordOf d w.length (idxOf w) = FreeMonoid.ofList w := by
  induction w using List.reverseRecOn with
  | nil => simp [idxOf, wordOf]
  | append_singleton w l ih =>
    have hidx : idxOf (w ++ [l]) = idxOf w * d + l := by simp [idxOf, List.foldl_append]
    rw [hidx, List.length_append, List.length_singleton]
    constructor
    · calc idxOf w * d + l < idxOf w * d + d := Nat.add_lt_add_left l.isLt _
        _ = (idxOf w + 1) * d := by ring
        _ ≤ d ^ w.length * d := Nat.mul_le_mul_right _ ih.1
        _ = d ^ (w.length + 1) := (pow_succ _ _).symm
    · rw [wordOf_append _ _ _ l.isLt, ih.2, FreeMonoid.ofList_append, FreeMonoid.ofList_singleton]
      congr 2; ext; simp [letter, Nat.mod_eq_of_lt l.isLt]

/-- The monomial `X_w` sits at position `off |w| + idx w`. -/
theorem e_wordPos (w : FreeMonoid (Fin d)) :
    e d (off d w.length + idxOf w.toList) = single w 1 := by
  have h := idxOf_spec w.toList
  rw [show w.length = w.toList.length from rfl, e_of_pos h.1, h.2, FreeMonoid.ofList_toList]

end Index

/-! ## The main theorem -/

/-- **Soundness of the replay.** If `check T members` passes, then for every test `t` claimed in,
`mt n w_t − 1 ∈ Lt n` (membership modulo `p^E`, statement 4 of `cert/TRACE.md`), and
`p^{E−1} X_w ∈ Lt n` for every word `w ≠ 1` (exactness (X) with `F = ∅`, statement 5). -/
theorem check_sound (T : Trace) (members : List ℕ) [NeZero T.d] (h : check T members = true) :
    (∀ t ∈ members, mt T.d T.n (findWord t T.tests) - 1 ∈ LT T T.n) ∧
    (∀ w : FreeMonoid (Fin T.d), w ≠ 1 → ((T.p ^ (T.E - 1) : ℕ) : ℤ) • single w 1 ∈ LT T T.n) := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Nat.blt_eq,
    Nat.ble_eq, Bool.or_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hd1, hp1⟩, hE⟩, hn⟩, -⟩, hrels⟩, htests⟩, hm⟩ := h
  have hD : 0 < T.p ^ T.E := Nat.pow_pos (by omega)
  have hrels' : ∀ r ∈ T.rels, okWord T.d r.2 := fun r hr f hf => hrels r hr f hf
  cases hr : runLevels T T.levels 1 [] with
  | none => rw [hr] at hm; simp at hm
  | some kc =>
    obtain ⟨k, cur⟩ := kc
    rw [hr] at hm
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Bool.or_eq_true,
      List.isEmpty_iff, decide_eq_true_eq] at hm
    obtain ⟨⟨⟨hk, hxs⟩, hcov⟩, hmem⟩ := hm
    rw [← hk] at hmem hcov ⊢
    have hrun := hr
    have hcur := runLevels_mem T hD hrels' T.levels 1 [] (by simp) k cur hrun
    have hDL := DR_le_Lt (d := T.d) (rels := T.rels) (T.p ^ T.E) k
    constructor
    · intro t ht
      obtain ⟨w, -, -, hw⟩ := hmem t ht
      have h1 := combo_eq_nil_mem hDL hcur hw
      have hok : okWord T.d (findWord t T.tests) := by
        rcases findWord_cases t T.tests with h | ⟨y, hy, hyw⟩
        · rw [h]; intro f hf; simp at hf
        · rw [← hyw]; exact fun f hf => htests y hy f hf
      have h2 := M_le_Lt (rels := T.rels) _ _
        (eval_magnus1 (d := T.d) (T.p ^ T.E) k hD (by omega) _ hok)
      have := sub_mem h1 h2; rwa [sub_sub_cancel] at this
    · intro w hw
      by_cases hlen : k ≤ w.length
      · rw [← single_eq_smul]; exact Ik_le_Lt _ _ (single_mem_Ik hlen _)
      · have hd := NeZero.pos T.d
        have hw1 : 1 ≤ w.length := by
          rcases Nat.eq_zero_or_pos w.length with h0 | h0
          · exfalso; apply hw
            have h0' : w.toList = [] := List.length_eq_zero_iff.mp h0
            rw [← FreeMonoid.ofList_toList w, h0']; rfl
          · exact h0
        obtain ⟨c, hcdef⟩ : ∃ c, c = off T.d w.length + idxOf w.toList := ⟨_, rfl⟩
        have hc : c < off T.d k := by
          have h1 := (idxOf_spec w.toList).1
          have h2 := off_mono hd (show w.length + 1 ≤ k by omega)
          rw [off_succ] at h2
          have h3 : w.toList.length = w.length := rfl
          rw [h3] at h1; rw [hcdef]; omega
        have hc0 : c ≠ 0 := by have := le_off hd w.length; rw [hcdef]; omega
        obtain ⟨x, hx, hxc⟩ := (hcov c (List.mem_range.mpr hc)).resolve_left hc0
        have h1 := combo_eq_nil_mem hDL hcur (hxs x hx)
        have h2 := eval_ins (d := T.d) (T.p ^ T.E) x.1 (T.p ^ (T.E - 1)) []
        rw [hxc] at h1 h2
        rw [eval_nil, zero_add, hcdef, e_wordPos] at h2
        rw [hcdef] at h1
        have := sub_mem h1 (hDL h2); rwa [sub_sub_cancel] at this
end

end GroupDimension.TraceReplay
