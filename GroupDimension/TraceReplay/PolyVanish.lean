module

public import GroupDimension.TraceReplay.PolyPres
public import GroupDimension.TraceReplay.PolyVanishBin

@[expose] public section

/-!
# A kernel check of `Vanish` (MATH-314, docs §3.2(e), check 1)

`check_mem_D_poly_pres` takes `Vanish rels (w, λ)` as a hypothesis: `λ(X_u (μ(r) − 1) X_v) = 0` in
`A_{w+1} = ℤ⟨X⟩/I_{w+1}` for every relator `r` and all monomials `u`, `v`. Here it becomes a Boolean
check the kernel can run (`checkVanish`), with its soundness proof (`vanish_of_check`):

* `μ(r)` is computed exactly over `ℤ`, cut below degree `w + 1`, as a sparse vector of monomial
  positions (`VecZ`): `mulZ` multiplies two such vectors, `sVec` is `(1 + X_j)^e` (binomial
  coefficients, any `e ∈ ℤ`), and a relator is a list of factors `(word, k)` (a flat relator is
  `[(w, 1)]`; nested `[word, k]` factors of the presentations come out as `(word, k)`, and the generator
  writes long flat relators as runs `u^k`), each a power
  computed by repeated squaring (`powZ`), a negative power from the inverse word.
* `λ(X_U v X_V)` is evaluated at the position of `X_U X_c X_V` (`posMul`, `lamPos`; on terms with their
  degrees precomputed, `vanValD`), the same reading of `λ` as `IsBase` (`lamR_e`), over all
  `|U| + |V| ≤ w − 1`; `vanish_of_short` covers the rest.

`check_mem_D_poly_presN` is then `check_mem_D_poly_pres` for a list of relators in this form, with
`Vanish` given by `checkVanish` or `checkVanishB` (PolyVanishBin.lean: powers by the binomial series) (decidable, so no hypothesis is left outside the kernel beyond the
trace's own and `hord`).
-/

namespace GroupDimension.TraceReplay

open MonoidAlgebra

/-! ## The group side -/

/-- The element `Π w_i^{k_i}` of the free group. -/
def relElt (d : ℕ) [NeZero d] (r : List (List (ℕ × ℤ) × ℤ)) : FreeGroup (Fin d) :=
  (r.map fun f => gword FreeGroup.of f.1 ^ f.2).prod

/-- The relators as a set. -/
def relSetN (d : ℕ) [NeZero d] (rels : List (List (List (ℕ × ℤ) × ℤ))) : Set (FreeGroup (Fin d)) :=
  {x | ∃ r ∈ rels, x = relElt d r}

/-! ## Soundness -/

section Sound

variable {d : ℕ} [NeZero d]

variable (d) in
/-- The element a vector stands for. -/
noncomputable def evalZ (v : VecZ) : R d := (v.map fun t => t.2 • e d t.1).sum

variable (d) in
/-- The quotient map `R → A_k`. -/
noncomputable abbrev mkK (k : ℕ) : R d →+* Ak d k := Ideal.Quotient.mk (IkI k)

@[simp] theorem evalZ_nil : evalZ d [] = 0 := rfl

@[simp] theorem evalZ_cons (t : ℕ × ℤ) (v : VecZ) : evalZ d (t :: v) = t.2 • e d t.1 + evalZ d v := by
  simp [evalZ]

theorem evalZ_append (a b : VecZ) : evalZ d (a ++ b) = evalZ d a + evalZ d b := by
  simp [evalZ]

theorem e_zero : e d 0 = 1 := by
  have h := e_of_pos (d := d) (g := 0) (idx := 0) (by simp)
  simpa [off, wordOf, ← one_def] using h

theorem evalZ_one : evalZ d [(0, 1)] = 1 := by simp [e_zero]

theorem evalZ_mergeZ : ∀ (n : ℕ) (a b : VecZ), evalZ d (mergeZ n a b) = evalZ d a + evalZ d b
  | 0, a, b => evalZ_append a b
  | _ + 1, [], b => by simp [mergeZ]
  | _ + 1, a :: as, [] => by simp [mergeZ]
  | n + 1, (i, x) :: a, (j, y) :: b => by
    simp only [mergeZ]
    cases h1 : Nat.blt i j
    · cases h2 : Nat.blt j i
      · have hij : i = j := by simp only [← Bool.not_eq_true, Nat.blt_eq] at h1 h2; omega
        subst hij
        cases h3 : (x + y == 0)
        · simp only [Bool.cond_false, evalZ_cons, evalZ_mergeZ n, add_smul]; abel
        · have h0 : x + y = 0 := by simpa using h3
          simp only [Bool.cond_false, Bool.cond_true, evalZ_mergeZ n, evalZ_cons]
          rw [show x • e d i + evalZ d a + (y • e d i + evalZ d b) =
            (x + y) • e d i + (evalZ d a + evalZ d b) by rw [add_smul]; abel, h0, zero_smul, zero_add]
      · simp only [Bool.cond_false, Bool.cond_true, evalZ_cons, evalZ_mergeZ n]; abel
    · simp only [Bool.cond_true, evalZ_cons, evalZ_mergeZ n]; abel

/-- `w(g + h, idx·d^h + idx') = w(g, idx) w(h, idx')`. -/
theorem wordOf_mul (g : ℕ) : ∀ (h idx idx' : ℕ), idx' < d ^ h →
    wordOf d (g + h) (idx * d ^ h + idx') = wordOf d g idx * wordOf d h idx'
  | 0, idx, idx', hi => by
    have : idx' = 0 := by simpa using hi
    subst this; simp [wordOf]
  | h + 1, idx, idx', hi => by
    have hd := NeZero.pos d
    have e1 : idx * d ^ (h + 1) + idx' = (idx * d ^ h + idx' / d) * d + idx' % d := by
      calc idx * d ^ (h + 1) + idx' = idx * d ^ (h + 1) + (idx' / d * d + idx' % d) := by
            rw [Nat.div_add_mod']
        _ = (idx * d ^ h + idx' / d) * d + idx' % d := by ring
    have hq : idx' / d < d ^ h := Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hi; exact hi)
    rw [e1, show g + (h + 1) = (g + h) + 1 by omega, wordOf_append _ _ _ (Nat.mod_lt _ hd),
      wordOf_mul g h idx (idx' / d) hq, mul_assoc, wordOf_succ (d := d) h idx']
    rw [show letter d (idx' % d) = letter d idx' by ext; simp [letter, Nat.mod_mod]]

theorem length_wordAt (c : ℕ) : (wordAt d c).length = degOf d c := length_wordOf _ _

theorem e_mul (c c' : ℕ) :
    e d c * e d c' = e d (off d (degOf d c + degOf d c') + (c - off d (degOf d c)) * d ^ degOf d c' +
      (c' - off d (degOf d c'))) := by
  have hd := NeZero.pos d
  have h1 := idx_lt hd c
  have h2 := idx_lt hd c'
  have hlt : (c - off d (degOf d c)) * d ^ degOf d c' + (c' - off d (degOf d c')) <
      d ^ (degOf d c + degOf d c') := by
    calc (c - off d (degOf d c)) * d ^ degOf d c' + (c' - off d (degOf d c'))
        < (c - off d (degOf d c)) * d ^ degOf d c' + d ^ degOf d c' := Nat.add_lt_add_left h2 _
      _ = (c - off d (degOf d c) + 1) * d ^ degOf d c' := by ring
      _ ≤ d ^ degOf d c * d ^ degOf d c' := Nat.mul_le_mul_right _ h1
      _ = d ^ (degOf d c + degOf d c') := (pow_add _ _ _).symm
  rw [Nat.add_assoc, e_of_pos hlt, wordOf_mul _ _ _ _ h2]
  simp only [e, wordAt, single_mul_single, one_mul]

theorem e_mul_mem_Ik {k c c' : ℕ} (h : k ≤ degOf d c + degOf d c') : e d c * e d c' ∈ Ik d k := by
  simp only [e, single_mul_single, one_mul]
  exact single_mem_Ik (by rw [FreeMonoid.length_mul, length_wordAt, length_wordAt]; exact h) _

theorem mkK_shiftZ {k K : ℕ} (hk : k ≤ K) (c' : ℕ) (a' : ℤ) (x : VecZ) :
    mkK d k (evalZ d (shiftZ d K (degOf d c') (c' - off d (degOf d c')) a' x)) =
      mkK d k (evalZ d x) * mkK d k (a' • e d c') := by
  induction x with
  | nil => simp [shiftZ]
  | cons t x ih =>
    simp only [shiftZ]
    cases h : Nat.blt (degOf d t.1 + degOf d c') K
    · simp only [Bool.cond_false]
      rw [ih, evalZ_cons, map_add, add_mul]
      have h0 : mkK d k (t.2 • e d t.1) * mkK d k (a' • e d c') = 0 := by
        rw [← map_mul, smul_mul_smul_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact Submodule.smul_mem _ _ (e_mul_mem_Ik (by simp only [← Bool.not_eq_true, Nat.blt_eq] at h; omega))
      rw [h0, zero_add]
    · simp only [Bool.cond_true]
      rw [evalZ_cons, map_add, ih, evalZ_cons, map_add, add_mul]
      congr 1
      rw [← map_mul, smul_mul_smul_comm, e_mul]

theorem mkK_mulZ {k K : ℕ} (hk : k ≤ K) (x y : VecZ) :
    mkK d k (evalZ d (mulZ d K x y)) = mkK d k (evalZ d x) * mkK d k (evalZ d y) := by
  suffices h : ∀ acc, mkK d k (evalZ d (y.foldl (fun acc t => mergeZ (acc.length + x.length) acc
      (shiftZ d K (degOf d t.1) (t.1 - off d (degOf d t.1)) t.2 x)) acc)) =
      mkK d k (evalZ d acc) + mkK d k (evalZ d x) * mkK d k (evalZ d y) by
    simpa [mulZ] using h []
  induction y with
  | nil => intro acc; simp
  | cons t y ih =>
    intro acc
    rw [List.foldl_cons, ih, evalZ_mergeZ, map_add, mkK_shiftZ hk, evalZ_cons, map_add, mul_add]
    abel

theorem jIdx_spec {j : ℕ} (hj : j < d) :
    ∀ m, jIdx d j m < d ^ m ∧ wordOf d m (jIdx d j m) = FreeMonoid.of (letter d j) ^ m
  | 0 => by simp [jIdx, wordOf]
  | m + 1 => by
    obtain ⟨h1, h2⟩ := jIdx_spec hj m
    refine ⟨?_, ?_⟩
    · show jIdx d j m * d + j < d ^ (m + 1)
      calc jIdx d j m * d + j < jIdx d j m * d + d := Nat.add_lt_add_left hj _
        _ = (jIdx d j m + 1) * d := by ring
        _ ≤ d ^ m * d := Nat.mul_le_mul_right _ h1
        _ = d ^ (m + 1) := (pow_succ _ _).symm
    · show wordOf d (m + 1) (jIdx d j m * d + j) = _
      rw [wordOf_append _ _ _ hj, h2, pow_succ]

theorem evalZ_sVec {j : ℕ} (hj : j < d) (ex : ℤ) : ∀ k, evalZ d (sVec d j ex k) = S (d := d) k j ex
  | 0 => by simp [sVec, S]
  | k + 1 => by
    rw [sVec, evalZ_append, evalZ_sVec hj ex k, S, S, Finset.sum_range_succ]
    congr 1
    have he : e d (off d k + jIdx d j k) = single (FreeMonoid.of (letter d j) ^ k) 1 := by
      rw [e_of_pos (jIdx_spec hj k).1, (jIdx_spec hj k).2]
    cases h : (binom ex k == 0)
    · simp [he]
    · have h0 : binom ex k = 0 := by simpa using h
      simp [h0]

/-- `Σ_{m<k} C(e, m) y^m = u^e` when `u = 1 + y` and `y^k = 0`. -/
theorem bser_eq_zpow {A : Type*} [Ring A] (y : A) (u : Aˣ) (hu : (u : A) = 1 + y) (k : ℕ)
    (hk : y ^ k = 0) (ex : ℤ) : bser y k ex = ((u ^ ex : Aˣ) : A) := by
  rcases k with _ | k
  · have h10 : (1 : A) = 0 := by simpa using hk
    exact (subsingleton_of_zero_eq_one h10.symm).elim _ _
  have hstep : ∀ e : ℤ, bser y (k + 1) e * u = bser y (k + 1) (e + 1) := by
    intro e; rw [hu, bser_mul, hk, smul_zero, add_zero]
  induction ex using Int.induction_on with
  | zero => rw [bser_at_zero, zpow_zero, Units.val_one]
  | succ i ih => rw [← hstep, ih, zpow_add_one, Units.val_mul]
  | pred i ih =>
    have h := hstep (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    calc bser y (k + 1) (-(i : ℤ) - 1) = bser y (k + 1) (-(i : ℤ) - 1) * u * ((u⁻¹ : Aˣ) : A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = ((u ^ (-(i : ℤ) - 1) : Aˣ) : A) := by rw [h, ← Units.val_mul, ← zpow_sub_one]

theorem mkK_S {k K : ℕ} (hk : k ≤ K) (j : ℕ) (ex : ℤ) :
    mkK d k (S (d := d) K j ex) = ((unitX k j ^ ex : (Ak d k)ˣ) : Ak d k) := by
  have hS : S (d := d) K j ex = bser (X (d := d) j) K ex := by
    simp only [S, bser, binom_eq_choose, X, single_pow, one_pow]
  have hmap : mkK d k (bser (X (d := d) j) K ex) = bser (mkK d k (X j)) K ex := by
    simp only [bser, map_sum, map_zsmul, map_pow]
  rw [hS, hmap]
  apply bser_eq_zpow
  · rw [unitX, IsUnit.unit_spec]
  · rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ik_mono hk (X_pow_mem_Ik K j))

theorem gword_cons {G : Type*} [Group G] (g : Fin d → G) (f : ℕ × ℤ) (w : List (ℕ × ℤ)) :
    gword g (f :: w) = g (letter d (f.1 - 1)) ^ f.2 * gword g w := by
  simp [gword]

theorem mkK_magnusW {k K : ℕ} (hk : k ≤ K) (w : List (ℕ × ℤ)) :
    mkK d k (evalZ d (magnusW d K w)) = ((muA k (gword FreeGroup.of w) : (Ak d k)ˣ) : Ak d k) := by
  suffices h : ∀ x, mkK d k (evalZ d (w.foldl (fun x f => mulZ d K x (sVec d ((f.1 - 1) % d) f.2 K)) x)) =
      mkK d k (evalZ d x) * ((muA k (gword FreeGroup.of w) : (Ak d k)ˣ) : Ak d k) by
    rw [magnusW, h, evalZ_one, map_one, one_mul]
  induction w with
  | nil => intro x; simp [gword]
  | cons f w ih =>
    intro x
    rw [List.foldl_cons, ih, mkK_mulZ hk, evalZ_sVec (Nat.mod_lt _ (NeZero.pos d)), mkK_S hk, mul_assoc,
      gword_cons, map_mul, Units.val_mul, map_zpow]
    congr 3
    rw [muA, FreeGroup.lift_apply_of]
    rfl

theorem mkK_powZ {k K : ℕ} (hk : k ≤ K) : ∀ (f : ℕ) (acc b : VecZ) (n : ℕ), n < 2 ^ f →
    mkK d k (evalZ d (powZ d K f acc b n)) = mkK d k (evalZ d acc) * mkK d k (evalZ d b) ^ n
  | 0, acc, b, n, hn => by
    have : n = 0 := by simpa using hn
    subst this; simp [powZ]
  | f + 1, acc, b, n, hn => by
    simp only [powZ]
    cases h0 : (n == 0)
    · simp only [Bool.cond_false]
      have hn2 : n / 2 < 2 ^ f := Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hn; exact hn)
      rw [mkK_powZ hk f _ _ _ hn2, mkK_mulZ hk]
      cases h1 : (n % 2 == 1)
      · simp only [Bool.cond_false]
        have h1' : n % 2 = 0 := by simp only [beq_eq_false_iff_ne, ne_eq] at h1; omega
        rw [show mkK d k (evalZ d b) ^ n = (mkK d k (evalZ d b) * mkK d k (evalZ d b)) ^ (n / 2) by
          rw [← sq, ← pow_mul]; congr 1; omega]
      · simp only [Bool.cond_true]
        have h1' : n % 2 = 1 := by simpa using h1
        rw [mkK_mulZ hk, mul_assoc, show mkK d k (evalZ d b) ^ n =
          mkK d k (evalZ d b) * (mkK d k (evalZ d b) * mkK d k (evalZ d b)) ^ (n / 2) by
          rw [← sq, ← pow_mul, ← pow_succ']; congr 1; omega]
    · have : n = 0 := by simpa using h0
      subst this; simp

theorem gword_invW {G : Type*} [Group G] (g : Fin d → G) (w : List (ℕ × ℤ)) :
    gword g (invW w) = (gword g w)⁻¹ := by
  simp only [gword, invW, List.map_map, List.prod_inv_reverse, List.map_reverse, Function.comp_def,
    zpow_neg]

theorem mkK_powFactor {k K : ℕ} (hk : k ≤ K) (w : List (ℕ × ℤ)) (ex : ℤ) :
    mkK d k (evalZ d (powZ d K ex.natAbs [(0, 1)]
      (magnusW d K (bif decide (ex < 0) then invW w else w)) ex.natAbs)) =
      ((muA k (gword FreeGroup.of w ^ ex) : (Ak d k)ˣ) : Ak d k) := by
  rw [mkK_powZ hk _ _ _ _ Nat.lt_two_pow_self, evalZ_one, map_one, one_mul, mkK_magnusW hk,
    ← Units.val_pow_eq_pow_val, ← map_pow]
  congr 2
  cases h : decide (ex < 0)
  · have h' : 0 ≤ ex := by simpa using h
    simp only [Bool.cond_false]
    rw [← zpow_natCast, Int.natAbs_of_nonneg h']
  · have h' : ex < 0 := by simpa using h
    simp only [Bool.cond_true]
    rw [gword_invW, inv_pow, ← zpow_natCast, Int.ofNat_natAbs_of_nonpos h'.le, zpow_neg, inv_inv]

theorem relElt_cons (f : List (ℕ × ℤ) × ℤ) (r : List (List (ℕ × ℤ) × ℤ)) :
    relElt d (f :: r) = gword FreeGroup.of f.1 ^ f.2 * relElt d r := by
  simp [relElt]

theorem mkK_magnusN {k K : ℕ} (hk : k ≤ K) (r : List (List (ℕ × ℤ) × ℤ)) :
    mkK d k (evalZ d (magnusN d K r)) = ((muA k (relElt d r) : (Ak d k)ˣ) : Ak d k) := by
  suffices h : ∀ x, mkK d k (evalZ d (r.foldl (fun acc f => mulZ d K acc
      (powZ d K f.2.natAbs [(0, 1)] (magnusW d K (bif decide (f.2 < 0) then invW f.1 else f.1)) f.2.natAbs))
      x)) = mkK d k (evalZ d x) * ((muA k (relElt d r) : (Ak d k)ˣ) : Ak d k) by
    rw [magnusN, h, evalZ_one, map_one, one_mul]
  induction r with
  | nil => intro x; simp [relElt]
  | cons f r ih =>
    intro x
    rw [List.foldl_cons, ih, mkK_mulZ hk, mkK_powFactor hk, mul_assoc, ← Units.val_mul, ← map_mul,
      relElt_cons]

theorem mkK_subOne (k : ℕ) (v : VecZ) : mkK d k (evalZ d (subOne v)) = mkK d k (evalZ d v) - 1 := by
  rw [subOne, evalZ_mergeZ, map_add]
  simp [e_zero, sub_eq_add_neg]

theorem lamW_eq_baseVal (m : ℕ × List ℤ) (w : FreeMonoid (Fin d)) :
    lamW m w = baseVal d m (w.toList.map (·.val)) := by
  have hl : w.length = w.toList.length := rfl
  unfold lamW baseVal
  rw [List.length_map, ← hl]
  by_cases h : 1 ≤ w.length ∧ w.length ≤ m.1
  · have hb : (Nat.blt 0 w.length && Nat.ble w.length m.1) = true := by
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]; omega
    simp only [h, and_self, ↓reduceIte, hb, Bool.cond_true]
  · have hb : (Nat.blt 0 w.length && Nat.ble w.length m.1) = false := by
      rw [Bool.eq_false_iff]
      intro hc; rw [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc; exact h ⟨hc.1, hc.2⟩
    simp only [h, ↓reduceIte, hb, Bool.cond_false]

theorem foldl_wordOf : ∀ (g i : ℕ), i < d ^ g →
    ((wordOf d g i).toList.map (·.val)).foldl (fun acc j => acc * d + j) 0 = i
  | 0, i, hi => by
    have : i = 0 := by simpa using hi
    subst this; rfl
  | g + 1, i, hi => by
    have hq : i / d < d ^ g := Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hi; exact hi)
    rw [wordOf_succ, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.map_append, List.foldl_append,
      foldl_wordOf g (i / d) hq]
    simp [letter, Nat.div_add_mod']

theorem posN_wordAt (p : ℕ) : posN d ((wordAt d p).toList.map (·.val)) = p := by
  have hd := NeZero.pos d
  have hs := deg_spec hd p
  unfold posN
  rw [List.length_map]
  show off d (wordAt d p).length + _ = p
  rw [length_wordAt]
  have := foldl_wordOf (d := d) (degOf d p) (p - off d (degOf d p)) (idx_lt hd p)
  simp only [wordAt] at this ⊢
  rw [this]; omega

theorem lamR_e (m : ℕ × List ℤ) (p : ℕ) : lamR m (e d p) = lamPos d m p := by
  rw [e, lamR_single, one_mul, lamW_eq_baseVal]
  unfold baseVal lamPos
  rw [List.length_map]
  show (bif Nat.blt 0 (wordAt d p).length && Nat.ble (wordAt d p).length m.1 then _ else _) = _
  rw [length_wordAt, posN_wordAt]

theorem e_posMul (c c' : ℕ) : e d c * e d c' = e d (posMul d c c') := e_mul c c'

theorem vanVal_eq (m : ℕ × List ℤ) (v : VecZ) (a u b vv : ℕ) (hu : u < d ^ a) (hv : vv < d ^ b) :
    vanVal d m v a u b vv = lamA m (mkK d (m.1 + 1) (single (wordOf d a u) 1) *
      mkK d (m.1 + 1) (evalZ d v) * mkK d (m.1 + 1) (single (wordOf d b vv) 1)) := by
  suffices h : ∀ s, v.foldl (fun s t => s + t.2 * lamPos d m (posMul d (posMul d (off d a + u) t.1)
      (off d b + vv))) s = s + lamA m (mkK d (m.1 + 1) (single (wordOf d a u) 1) *
        mkK d (m.1 + 1) (evalZ d v) * mkK d (m.1 + 1) (single (wordOf d b vv) 1)) by
    simpa [vanVal] using h 0
  induction v with
  | nil => intro s; simp
  | cons t v ih =>
    intro s
    rw [List.foldl_cons, ih, evalZ_cons, map_add, mul_add, add_mul, map_add, add_assoc]
    congr 2
    rw [← map_mul, ← map_mul, lamA_mk, mul_smul_comm, smul_mul_assoc, map_zsmul, smul_eq_mul,
      ← e_of_pos hu, ← e_of_pos hv, e_posMul, e_posMul, lamR_e]

theorem degOf_offAdd {a x : ℕ} (hx : x < d ^ a) : degOf d (off d a + x) = a :=
  deg_eq (NeZero.pos d) (by omega) (by rw [off_succ]; omega)

omit [NeZero d] in
theorem concat_lt {a b x y : ℕ} (hx : x < d ^ a) (hy : y < d ^ b) : x * d ^ b + y < d ^ (a + b) := by
  calc x * d ^ b + y < x * d ^ b + d ^ b := Nat.add_lt_add_left hy _
    _ = (x + 1) * d ^ b := by ring
    _ ≤ d ^ a * d ^ b := Nat.mul_le_mul_right _ hx
    _ = d ^ (a + b) := (pow_add _ _ _).symm

theorem posMul_pos {a b x y : ℕ} (hx : x < d ^ a) (hy : y < d ^ b) :
    posMul d (off d a + x) (off d b + y) = off d (a + b) + (x * d ^ b + y) := by
  simp only [posMul, degOf_offAdd hx, degOf_offAdd hy, Nat.add_sub_cancel_left]
  omega

theorem lamPos_pos (m : ℕ × List ℤ) {a x : ℕ} (hx : x < d ^ a) :
    lamPos d m (off d a + x) =
      bif Nat.blt 0 a && Nat.ble a m.1 then m.2.getD (off d a + x - 1) 0 else 0 := by
  simp only [lamPos, degOf_offAdd hx]

theorem vanValD_eq (m : ℕ × List ℤ) (v : VecZ) {a u b vv : ℕ} (hu : u < d ^ a) (hv : vv < d ^ b) :
    vanValD d m (withDeg d v) a u b vv = vanVal d m v a u b vv := by
  have hd := NeZero.pos d
  suffices h : ∀ s, (withDeg d v).foldl (fun s t =>
      bif Nat.blt 0 (a + t.1 + b) && Nat.ble (a + t.1 + b) m.1 then
        s + t.2.2 * m.2.getD (off d (a + t.1 + b) + (u * d ^ t.1 + t.2.1) * d ^ b + vv - 1) 0
      else s) s =
      v.foldl (fun s t => s + t.2 * lamPos d m (posMul d (posMul d (off d a + u) t.1) (off d b + vv))) s by
    exact h 0
  induction v with
  | nil => intro s; rfl
  | cons t v ih =>
    intro s
    simp only [withDeg, List.map_cons, List.foldl_cons] at ih ⊢
    rw [← ih]
    congr 1
    have hi := idx_lt hd t.1
    have hg := (deg_spec hd t.1).1
    have ht : t.1 = off d (degOf d t.1) + (t.1 - off d (degOf d t.1)) := by omega
    set g := degOf d t.1
    set i := t.1 - off d g
    have hc := concat_lt hu hi
    rw [ht, posMul_pos hu hi, posMul_pos hc hv, lamPos_pos m (concat_lt hc hv)]
    cases (Nat.blt 0 (a + g + b) && Nat.ble (a + g + b) m.1) <;> simp [Nat.add_assoc]

theorem checkMap_sound {m : ℕ × List ℤ} {v : VecZ} (h : checkMap d m (withDeg d v) = true) (u w : FreeMonoid (Fin d))
    (huw : u.length + w.length + 1 ≤ m.1) :
    lamA m (mkK d (m.1 + 1) (single u 1) * mkK d (m.1 + 1) (evalZ d v) * mkK d (m.1 + 1) (single w 1)) = 0 := by
  simp only [checkMap, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hu := idxOf_spec u.toList
  have hw := idxOf_spec w.toList
  have hu2 : wordOf d u.length (idxOf u.toList) = u := by
    rw [show u.length = u.toList.length from rfl, hu.2, FreeMonoid.ofList_toList]
  have hw2 : wordOf d w.length (idxOf w.toList) = w := by
    rw [show w.length = w.toList.length from rfl, hw.2, FreeMonoid.ofList_toList]
  have := h u.length (by omega) w.length (by omega) _ hu.1 _ hw.1
  rw [vanValD_eq m v (a := u.length) (b := w.length) hu.1 hw.1, vanVal_eq m v u.length _ w.length _ hu.1 hw.1, hu2, hw2] at this
  exact this

/-- **Soundness of the kernel check of `Vanish`.** -/
theorem vanish_of_check {K : ℕ} {maps : List (ℕ × List ℤ)} {rels : List (List (List (ℕ × ℤ) × ℤ))}
    (h : checkVanish d K maps rels = true) : ∀ m ∈ maps, Vanish (relSetN d rels) m := by
  intro m hm
  apply vanish_of_short
  rintro _ ⟨r, hr, rfl⟩ u w huw
  have hr' := List.all_eq_true.1 h r hr
  simp only [checkVanishRel, List.all_eq_true, Bool.and_eq_true, Nat.ble_eq] at hr'
  obtain ⟨hK, hc⟩ := hr' m hm
  have := checkMap_sound hc u w huw
  rw [mkK_subOne, mkK_magnusN hK] at this
  exact this

/-! ### Powers by the binomial series (`checkVanishB`) -/

theorem evalZ_scaleZ (c : ℤ) (v : VecZ) : evalZ d (scaleZ c v) = c • evalZ d v := by
  induction v with
  | nil => simp [scaleZ]
  | cons t v ih =>
    simp only [scaleZ, List.map_cons] at ih ⊢
    rw [evalZ_cons, evalZ_cons, ih, smul_add, smul_smul]

theorem mkK_powBAux {k K : ℕ} (hk : k ≤ K) (y : VecZ) (e : ℤ) : ∀ (f : ℕ) (acc ym : VecZ) (m : ℕ),
    mkK d k (evalZ d ym) = mkK d k (evalZ d y) ^ m →
    mkK d k (evalZ d (powBAux d K y e f acc ym m)) =
      mkK d k (evalZ d acc) + ∑ i ∈ Finset.Ico m (m + f), Ring.choose e i • mkK d k (evalZ d y) ^ i
  | 0, acc, ym, m, _ => by simp [powBAux]
  | f + 1, acc, ym, m, hym => by
    simp only [powBAux]
    rw [mkK_powBAux hk y e f _ _ (m + 1) (by rw [mkK_mulZ hk, hym, pow_succ]),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : m < m + (f + 1)), show m + (f + 1) = m + 1 + f by omega,
      ← add_assoc]
    congr 1
    cases h : (binom e m == 0)
    · simp only [Bool.cond_false, evalZ_mergeZ, map_add, evalZ_scaleZ, map_zsmul, hym, binom_eq_choose]
    · have h0 : binom e m = 0 := by simpa using h
      simp only [Bool.cond_true]
      rw [← binom_eq_choose, h0, zero_smul, add_zero]

theorem mkK_powB {k K : ℕ} (hk : k ≤ K) (hK : 1 ≤ K) (y : VecZ) (e : ℤ) :
    mkK d k (evalZ d (powB d K y e)) = bser (mkK d k (evalZ d y)) K e := by
  rw [powB, mkK_powBAux hk y e (K - 1) _ _ 1 (by rw [pow_one]), evalZ_one, map_one, bser,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < K), show 1 + (K - 1) = K by omega]
  simp [Ring.choose_zero_right]

theorem pow_mem_Ik {z : R d} (hz : z ∈ Ik d 1) : ∀ n : ℕ, z ^ n ∈ Ik d n
  | 0 => by rw [pow_zero]; exact single_mem_Ik (by simp) _
  | n + 1 => by rw [pow_succ]; exact mul_mem_Ik_add (pow_mem_Ik hz n) hz

theorem mkK_powFactorB {k K : ℕ} (hk : k ≤ K) (hk1 : 1 ≤ k) (w : List (ℕ × ℤ)) (ex : ℤ) :
    mkK d k (evalZ d (powB d K (subOne (magnusW d K w)) ex)) =
      ((muA k (gword FreeGroup.of w ^ ex) : (Ak d k)ˣ) : Ak d k) := by
  rw [mkK_powB hk (by omega), mkK_subOne, mkK_magnusW hk, map_zpow]
  apply bser_eq_zpow
  · abel
  · obtain ⟨z, hz, ez⟩ := muA_sub_one_mem (d := d) k (gword FreeGroup.of w)
    rw [← ez, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ik_mono hk (pow_mem_Ik hz K)

theorem mkK_magnusNB {k K : ℕ} (hk : k ≤ K) (hk1 : 1 ≤ k) (r : List (List (ℕ × ℤ) × ℤ)) :
    mkK d k (evalZ d (magnusNB d K r)) = ((muA k (relElt d r) : (Ak d k)ˣ) : Ak d k) := by
  suffices h : ∀ x, mkK d k (evalZ d (r.foldl (fun acc f => mulZ d K acc
      (powB d K (subOne (magnusW d K f.1)) f.2)) x)) =
      mkK d k (evalZ d x) * ((muA k (relElt d r) : (Ak d k)ˣ) : Ak d k) by
    rw [magnusNB, h, evalZ_one, map_one, one_mul]
  induction r with
  | nil => intro x; simp [relElt]
  | cons f r ih =>
    intro x
    rw [List.foldl_cons, ih, mkK_mulZ hk, mkK_powFactorB hk hk1, mul_assoc, ← Units.val_mul, ← map_mul,
      relElt_cons]

/-- **Soundness of `checkVanishB`.** -/
theorem vanish_of_checkB {K : ℕ} {maps : List (ℕ × List ℤ)} {rels : List (List (List (ℕ × ℤ) × ℤ))}
    (h : checkVanishB d K maps rels = true) : ∀ m ∈ maps, Vanish (relSetN d rels) m := by
  intro m hm
  apply vanish_of_short
  rintro _ ⟨r, hr, rfl⟩ u w huw
  have hr' := List.all_eq_true.1 h r hr
  simp only [checkVanishRelB, List.all_eq_true, Bool.and_eq_true, Nat.ble_eq] at hr'
  obtain ⟨hK, hc⟩ := hr' m hm
  have := checkMap_sound hc u w huw
  rw [mkK_subOne, mkK_magnusNB hK (by omega)] at this
  exact this

end Sound

/-! ## Membership in a presented group, checked in full -/

theorem relElt_single {d : ℕ} [NeZero d] (w : List (ℕ × ℤ)) : relElt d [(w, 1)] = gword FreeGroup.of w := by
  simp [relElt]

/-- A relator written out as a flat word (each factor `(w, k)` as `w^k`, `w⁻¹^|k|` for `k < 0`). -/
def expandRel (r : List (List (Nat × Int) × Int)) : List (Nat × Int) :=
  r.flatMap fun f => (List.replicate f.2.natAbs (bif decide (f.2 < 0) then invW f.1 else f.1)).flatten

theorem gword_append {G : Type*} [Group G] {d : ℕ} [NeZero d] (g : Fin d → G) (a b : List (ℕ × ℤ)) :
    gword g (a ++ b) = gword g a * gword g b := by
  simp [gword, List.map_append, List.prod_append]

theorem gword_flatten_replicate {G : Type*} [Group G] {d : ℕ} [NeZero d] (g : Fin d → G)
    (w : List (ℕ × ℤ)) : ∀ n : ℕ, gword g (List.replicate n w).flatten = gword g w ^ n
  | 0 => by simp [gword]
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, gword_append, gword_flatten_replicate g w n, pow_succ']

/-- The flat word of a relator is the relator. -/
theorem gword_expandRel {d : ℕ} [NeZero d] (r : List (List (ℕ × ℤ) × ℤ)) :
    gword FreeGroup.of (expandRel r) = relElt d r := by
  induction r with
  | nil => simp [expandRel, relElt, gword]
  | cons f r ih =>
    have hc : expandRel (f :: r) = (List.replicate f.2.natAbs
        (bif decide (f.2 < 0) then invW f.1 else f.1)).flatten ++ expandRel r := by
      simp only [expandRel, List.flatMap_cons]
    rw [hc, gword_append, ih, relElt_cons, gword_flatten_replicate]
    congr 1
    cases h : decide (f.2 < 0)
    · have h' : 0 ≤ f.2 := by simpa using h
      simp only [Bool.cond_false]
      rw [← zpow_natCast, Int.natAbs_of_nonneg h']
    · have h' : f.2 < 0 := by simpa using h
      simp only [Bool.cond_true]
      rw [gword_invW, inv_pow, ← zpow_natCast, Int.ofNat_natAbs_of_nonpos h'.le, zpow_neg, inv_inv]

theorem rel_hold_of_sub (T : Trace) [NeZero T.d] (allRels : List (List (List (ℕ × ℤ) × ℤ)))
    (hsub : T.rels.all (fun r => allRels.any (fun R => expandRel R == r.2)) = true) :
    ∀ r ∈ T.rels, gword (PresentedGroup.of (rels := relSetN T.d allRels)) r.2 = 1 := by
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hsub
  intro r hr
  obtain ⟨R, hR, hRr⟩ := hsub r hr
  have e : (PresentedGroup.of : Fin T.d → PresentedGroup (relSetN T.d allRels)) =
      PresentedGroup.mk _ ∘ FreeGroup.of := rfl
  rw [e, ← map_gword]
  exact PresentedGroup.one_of_mem ⟨R, hR, by rw [← hRr, gword_expandRel]⟩

theorem maps_isBase (T : Trace) [NeZero T.d] (P : PolyCert) (allRels : List (List (List (ℕ × ℤ) × ℤ)))
    (hvan : ∀ m ∈ P.maps, Vanish (relSetN T.d allRels) m) :
    ∀ i < P.maps.length, ∃ φ : PresentedGroup (relSetN T.d allRels) → ℤ,
      IsBase (PresentedGroup.of (rels := relSetN T.d allRels)) (P.maps.getD i (0, [])) φ := by
  intro i hi
  have hm : P.maps.getD i (0, []) ∈ P.maps := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  exact ⟨_, isBase_of_vanish (hvan _ hm)⟩

/-- **Exact membership in a presented group, every hypothesis but `hord` decidable.** `check`,
`checkPoly` and `hsub` (each relator of the trace, written out, is a relator of the presentation:
`expandRel`, `gword_expandRel`) are Boolean checks, and `hvan` (check 1 for every base map against all
relators) follows from one (`vanish_of_check` or `vanish_of_checkB`); then in
`G = ⟨x_1, …, x_d | allRels⟩` every lintest claimed whose element has `p`-power order in `Δ/Δ^n`
lies in `Δ^n`. -/
theorem check_mem_D_poly_lin_presN (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (P : PolyCert) (hP : checkPoly T P = true) (allRels : List (List (List (ℕ × ℤ) × ℤ)))
    (hsub : T.rels.all (fun r => allRels.any (fun R => expandRel R == r.2)) = true)
    (hvan : ∀ m ∈ P.maps, Vanish (relSetN T.d allRels) m)
    (t : ℕ) (ht : t ∈ members)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) • linG (PresentedGroup.of (rels := relSetN T.d allRels)) (testLin T t) ∈
      augIdeal (PresentedGroup (relSetN T.d allRels)) ^ T.n) :
    linG (PresentedGroup.of (rels := relSetN T.d allRels)) (testLin T t) ∈
      augIdeal (PresentedGroup (relSetN T.d allRels)) ^ T.n :=
  check_mem_D_poly_lin T members hc P hP _ (rel_hold_of_sub T allRels hsub)
    (PresentedGroup.closure_range_of _) (maps_isBase T P allRels hvan) t ht hord

/-- `check_mem_D_poly_lin_presN` for a word test: `w_t ∈ D_n(G)`. -/
theorem check_mem_D_poly_presN (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (P : PolyCert) (hP : checkPoly T P = true) (allRels : List (List (List (ℕ × ℤ) × ℤ)))
    (hsub : T.rels.all (fun r => allRels.any (fun R => expandRel R == r.2)) = true)
    (hvan : ∀ m ∈ P.maps, Vanish (relSetN T.d allRels) m)
    (t : ℕ) (ht : t ∈ members) (hw : T.tests.any (fun y => y.1 == t) = true)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) •
      (of ℤ (PresentedGroup (relSetN T.d allRels))
        (gword (PresentedGroup.of (rels := relSetN T.d allRels)) (findWord t T.tests)) - 1) ∈
      augIdeal (PresentedGroup (relSetN T.d allRels)) ^ T.n) :
    gword (PresentedGroup.of (rels := relSetN T.d allRels)) (findWord t T.tests) ∈
      GroupDimension.D T.n (PresentedGroup (relSetN T.d allRels)) :=
  check_mem_D_poly T members hc P hP _ (rel_hold_of_sub T allRels hsub)
    (PresentedGroup.closure_range_of _) (maps_isBase T P allRels hvan) t ht hw hord

end GroupDimension.TraceReplay
