module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.RingTheory.Binomial
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

/-- The degree of position `c`. -/
def deg (c : ℕ) : ℕ := degOf d c

/-- The word at position `c`. -/
def wordAt (c : ℕ) : FreeMonoid (Fin d) := wordOf d (deg d c) (c - off d (deg d c))

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

theorem deg_spec (hd : 0 < d) (c : ℕ) : off d (deg d c) ≤ c ∧ c < off d (deg d c + 1) :=
  degAux_spec hd c (c + 1) 0 (by simp [off]) (by
    simp only [Nat.zero_add]; have := le_off hd (c + 1)
    have := off_lt_off hd (Nat.lt_succ_self (c + 1)); omega)

/-- `degAux` with fuel `k` computes `deg` below `off k`. -/
theorem degAux_eq_deg (hd : 0 < d) {c k : ℕ} (hc : c < off d k) : degAux d c k 0 = deg d c :=
  deg_unique hd (degAux_spec hd c k 0 (by simp [off]) (by simpa using hc)) (deg_spec hd c)

theorem deg_eq (hd : 0 < d) {c g : ℕ} (h1 : off d g ≤ c) (h2 : c < off d (g + 1)) : deg d c = g :=
  deg_unique hd (deg_spec hd c) ⟨h1, h2⟩

theorem idx_lt (hd : 0 < d) (c : ℕ) : c - off d (deg d c) < d ^ deg d c := by
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
    rw [h1, h2, ih _ (by rw [pow_succ] at hidx; exact Nat.div_lt_of_lt_mul hidx), mul_assoc]

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
  have : ((a : ℕ) : ℤ) • x - ((a % D : ℕ) : ℤ) • x = ((D : ℕ) : ℤ) • (((a / D : ℕ) : ℤ) • x) := by
    rw [smul_smul, ← sub_smul]; congr 1
    have := Nat.mod_add_div a D; push_cast; omega
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
    have := Int.emod_add_ediv a D; linarith
  rw [this]; exact smul_mem_DR d D _

end Modulo

end

end GroupDimension.TraceReplay
