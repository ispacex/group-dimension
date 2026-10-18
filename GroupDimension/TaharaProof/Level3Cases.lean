import GroupDimension.TaharaProof.Level3

/-!
# `ψ₃(Λ₅) ⊆ R₅*`: the case analysis ([Tah81, Lemmas 3.5, 5.3–5.6])

The induction `U3`: `ψ₃(P(a)) ≡ Φ₃(a) (mod R₅*)` for every `m`-sequence `a` of weight `≥ 3`.
For non-basic `a`, reduced at a letter `x` (`d = o(x)`, `r = a - d e_x`), the cases are:

* `W(r) + w(x) ≥ 4`: `T` has weight `≥ 5` and the binomial terms vanish by torsion;
* `w(x) = 3`, `r = 0`: relation (I);  `w(x) = 2`, `W(r) = 1`: relation (IV);
* `w(x) = 1`, `W(r) = 2`: relations (III) (a letter of weight 2), (V), (VI), (VII) (the power
  first, in the middle, last);
* `w(x) = 1`, `W(r) = 1`: relation (II) and the value (3) of `ψ₃`;
* `r = 0`, `w(x) ≤ 2`: members of Losey's basis.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable [Fintype G] {F : Frame G ι} {hF : F.Class4}

section Step

variable {a : ι → ℕ} (IH : IHat hF a) {x : ι} (hx : F.o x ≤ a x)
include IH hx

/-! ## Assembling a reduction step -/

/-- The reduction step: from values of `T` and of the binomial sum, and the identity in `M3`. -/
theorem combine {vT vB : F.M3}
    (hT : (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x), vT) ∈ rel3 hF)
    (hB : (∑ h ∈ Finset.range (F.o x - 1), ((F.o x).choose (h + 1) : ℤ) •
      F.P (a - (F.o x - (h + 1)) • (Pi.single x 1 : ι → ℕ)), vB) ∈ rel3 hF)
    (hid : vT - vB - F.Φ3 a ∈ F.R5) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  rw [F.P_reduce hx]
  exact rel3_congr hF (rel3_sub hF hT hB) hid

/-- The binomial terms, by the induction hypothesis. -/
theorem binom_IH (h3 : 3 ≤ F.W (F.lo a x + hi a x) + F.w x) :
    ∀ h ∈ Finset.range (F.o x - 1),
      (F.P (a - (F.o x - (h + 1)) • (Pi.single x 1 : ι → ℕ)),
        F.Φ3 (a - (F.o x - (h + 1)) • (Pi.single x 1 : ι → ℕ))) ∈ rel3 hF := by
  intro h hh
  rw [Finset.mem_range] at hh
  refine IH _ (lexLT_of x (fun j hj => ?_) ?_) ?_
  · simp only [Pi.sub_apply, nsmul_single_apply, if_neg hj.ne, tsub_zero]
  · simp only [Pi.sub_apply, nsmul_single_apply, ↓reduceIte]; omega
  · rw [← F.lo_add_hi hx (h + 1) (by omega), W_add, W_add]
    have : F.W ((h + 1) • (Pi.single x 1 : ι → ℕ)) = (h + 1) * F.w x := by
      rw [← cnt_replicate, W_cnt]; simp
    rw [W_add] at h3
    rw [this]; nlinarith

omit IH hx in
/-- `∑_{0<h<d} C(d,h) f(h) + f(d) = d f(1) + C(d,2) f(2) + C(d,3) f(3)` if `f` vanishes from 4 on. -/
theorem binom_trunc {M : Type*} [AddCommGroup M] (f : ℕ → M) {d : ℕ} (hd : 1 ≤ d)
    (hf : ∀ m, 4 ≤ m → f m = 0) :
    ∑ h ∈ Finset.range (d - 1), ((d.choose (h + 1) : ℤ) • f (h + 1)) + f d =
      (d : ℤ) • f 1 + ((d.choose 2 : ℤ) • f 2 + (d.choose 3 : ℤ) • f 3) := by
  set g : ℕ → M := fun h => (d.choose (h + 1) : ℤ) • f (h + 1)
  have e1 : ∑ h ∈ Finset.range (d - 1), g h + f d = ∑ h ∈ Finset.range d, g h := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]; simp [g]
  have hg : ∀ h, (3 ≤ h ∨ d ≤ h) → g h = 0 := by
    intro h hh
    rcases hh with hh | hh
    · simp [g, hf (h + 1) (by omega)]
    · simp [g, Nat.choose_eq_zero_of_lt (show d < h + 1 by omega)]
  have e2 : ∑ h ∈ Finset.range d, g h = ∑ h ∈ Finset.range (max d 3), g h :=
    Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun h hh hn => by
      simp at hh hn; exact hg h (Or.inr hn)
  have e3 : ∑ h ∈ Finset.range 3, g h = ∑ h ∈ Finset.range (max d 3), g h :=
    Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun h hh hn => by
      simp at hh hn; exact hg h (Or.inl hn)
  show ∑ h ∈ Finset.range (d - 1), g h + f d = _
  rw [e1, e2, ← e3]
  simp [g, Finset.sum_range_succ, add_assoc]

/-! ## Auxiliary facts for the case analysis -/

omit IH in
theorem lo_eq_restrict : F.lo a x = fun j => if j ≤ x then (F.lo a x + hi a x) j else 0 := by
  funext j
  simp only [Pi.add_apply]
  rcases lt_trichotomy j x with h | rfl | h
  · simp [lo, hi, h, h.le, not_lt.2 h.le]
  · simp [lo, hi]
  · simp [lo, hi, h, not_le.2 h, not_lt.2 h.le, h.ne']

omit IH hx in
theorem hi_eq_restrict : hi a x = fun j => if x < j then (F.lo a x + hi a x) j else 0 := by
  funext j
  simp only [Pi.add_apply]
  by_cases h : x < j
  · simp [lo, hi, h, not_lt.2 h.le, h.ne']
  · simp [hi, h]

omit IH hx in
theorem cnt_filter (l : List ι) (p : ι → Prop) [DecidablePred p] :
    cnt (l.filter fun j => decide (p j)) = fun j => if p j then cnt l j else 0 := by
  funext j
  induction l with
  | nil => simp [cnt]
  | cons i l ih =>
    by_cases hi : p i
    · rw [List.filter_cons_of_pos (by simpa using hi)]
      simp only [cnt, List.count_cons] at ih ⊢
      rw [ih]; split_ifs <;> simp_all
    · rw [List.filter_cons_of_neg (by simpa using hi)]
      simp only [cnt, List.count_cons] at ih ⊢
      rw [ih]; split_ifs <;> simp_all

omit IH hx in
theorem nfc_one : F.nfc 1 = 0 := F.nfc_eq (fun j => by have := F.o_pos j; simp; omega) (by
  simp [nprod])

omit IH hx in
theorem nsum_one (β : ι → ℕ) : F.nsum 1 β = 0 := by simp [nsum, nfc_one]

omit IH hx in
theorem cc_self (z : ι) : F.cc z z = 1 := by
  simp only [cc, yy, tc]
  have h : F.x z ^ F.o z * F.x z = F.x z * F.x z ^ F.o z := pow_mul_comm' (F.x z) (F.o z)
  calc (F.x z ^ F.o z)⁻¹ * (F.x z)⁻¹ * F.x z ^ F.o z * F.x z
      = (F.x z ^ F.o z)⁻¹ * (F.x z)⁻¹ * (F.x z ^ F.o z * F.x z) := by group
    _ = 1 := by rw [h]; group

omit IH hx in
theorem tc_one_left (g : G) : tc (1 : G) g = 1 := by simp [tc]

omit IH hx in
/-- `nsum g β = 0` when everything has weight `≥ 5`. -/
theorem nsum_eq_zero {g : G} {k : ℕ} (hg : g ∈ lowerCentralSeries G (k - 1)) {β : ι → ℕ}
    (h5 : 5 ≤ F.W β + k) : F.nsum g β = 0 := by
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : F.nfc g m = 0
  · simp [hm]
  · have := F.nf_weight hg (F.nfc_lt g) (F.nprod_nfc g) hm
    rw [F.Φ3_eq_zero_of_five_le (by rw [W_add, W_single]; omega), smul_zero]

omit IH hx in
theorem zsmul_single_zmod' {κ : Type*} [DecidableEq κ] (m : κ → ℕ) (p : κ) {n : ℤ}
    (h : (m p : ℤ) ∣ n) : n • (Pi.single p 1 : (q : κ) → ZMod (m q)) = 0 := by
  funext q
  by_cases hq : q = p
  · subst hq
    simp only [Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul, mul_one, Pi.zero_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  · simp [Pi.single_eq_of_ne hq]

omit IH hx in
theorem Φ3w_single3 {l : ι} (h : F.w l = 3) : F.Φ3w [l] = F.E3' l := by
  simp only [Φ3w, if_pos h]

omit IH hx in
theorem Φ3w_single4 {l : ι} (h : F.w l = 4) : F.Φ3w [l] = F.A4 (F.x l) := by
  simp only [Φ3w, if_neg (show F.w l ≠ 3 by omega), if_pos h]

omit IH hx in
theorem Φ3w_12 {i j : ι} (hi : F.w i = 1) (hj : F.w j = 2) : F.Φ3w [i, j] = F.E12 i j := by
  simp only [Φ3w, if_pos (And.intro hi hj)]

omit IH hx in
theorem Φ3w_13 {i j : ι} (hi : F.w i = 1) (hj : F.w j = 3) : F.Φ3w [i, j] = F.T13 i j := by
  simp only [Φ3w, if_neg (show ¬ (F.w i = 1 ∧ F.w j = 2) by omega), if_pos (And.intro hi hj)]

omit IH hx in
theorem Φ3w_22 {i j : ι} (hi : F.w i = 2) (hj : F.w j = 2) : F.Φ3w [i, j] = F.S2' i j := by
  simp only [Φ3w, if_neg (show ¬ (F.w i = 1 ∧ F.w j = 2) by omega),
    if_neg (show ¬ (F.w i = 1 ∧ F.w j = 3) by omega), if_pos (And.intro hi hj)]

omit IH hx in
theorem Φ3w_111 {i j k : ι} (hi : F.w i = 1) (hj : F.w j = 1) (hk : F.w k = 1) :
    F.Φ3w [i, j, k] = F.E3 i j k := by
  simp only [Φ3w, if_pos (And.intro hi (And.intro hj hk))]

omit IH hx in
theorem Φ3w_112 {i j k : ι} (hi : F.w i = 1) (hj : F.w j = 1) (hk : F.w k = 2) :
    F.Φ3w [i, j, k] = F.S22 i j k := by
  simp only [Φ3w, if_neg (show ¬ (F.w i = 1 ∧ F.w j = 1 ∧ F.w k = 1) by omega),
    if_pos (And.intro hi (And.intro hj hk))]

omit IH hx in
theorem Φ3w_1111 {i j k l : ι} (hi : F.w i = 1) (hj : F.w j = 1) (hk : F.w k = 1)
    (hl : F.w l = 1) : F.Φ3w [i, j, k, l] = F.S4 i j k l := by
  simp only [Φ3w, if_pos (And.intro hi (And.intro hj (And.intro hk hl)))]

omit IH hx in
/-- **Torsion**: `o_z Φ(c) = 0` when the letter `z` occurs in `c` and `W(c) = 4`. -/
theorem torsion (hF : F.Class4) {c : ι → ℕ} {z : ι} (hz : c z ≠ 0) (hW : F.W c = 4) :
    (F.o z : ℤ) • F.Φ3 c = 0 := by
  have hcnt := count_of_word (a := c) rfl
  have hWw := F.W_eq_word c
  have hsort := word_pairwise c
  rw [hW] at hWw
  unfold Φ3
  generalize word c = l at hcnt hWw hsort
  have hzl : z ∈ l := by
    by_contra h; exact hz (by rw [hcnt z]; exact List.count_eq_zero.mpr h)
  have hp := F.w_pos
  have hmono : ∀ i j, i ≤ j → F.w i ≤ F.w j := fun i j h => F.w_mono h
  have hdvd : ∀ i j, F.w i = F.w j → i ≤ j → (F.o i : ℤ) ∣ (F.o j : ℤ) := fun i j h1 h2 =>
    Int.natCast_dvd_natCast.mpr (hF.dvd i j h1 h2)
  match l, hzl, hWw, hsort with
  | [q], hzl, hWw, _ =>
    simp at hzl hWw; subst hzl
    rw [Φ3w_single4 hWw.symm]
    have h1 : F.x z ^ F.o z = 1 := by
      have := F.pow_mem z; rw [← hWw, hF.top] at this; simpa using this
    have hm : F.x z ∈ lowerCentralSeries G 3 := by simpa [← hWw] using F.mem z
    simp only [A4, Prod.smul_mk, smul_zero]
    rw [← cl_zpow hm, zpow_natCast, h1, cl_one]; rfl
  | [i, j], hzl, hWw, hs =>
    have hij : i ≤ j := (List.pairwise_cons.mp hs).1 j (by simp)
    simp at hzl hWw
    have := hmono i j hij; have := hp i; have := hp j
    rcases (show (F.w i = 1 ∧ F.w j = 3) ∨ (F.w i = 2 ∧ F.w j = 2) by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hd : ((Nat.gcd (F.o i) (F.o j) : ℕ) : ℤ) ∣ (F.o z : ℤ) := by
        rcases hzl with rfl | rfl
        · exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
        · exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
      rw [Φ3w_13 h1 h2]
      simp only [T13, Prod.smul_mk, smul_zero]
      rw [zsmul_single_zmod' (fun q : ι × ι => Nat.gcd (F.o q.1) (F.o q.2)) (i, j) hd]; rfl
    · have hd : ((F.o i : ℕ) : ℤ) ∣ (F.o z : ℤ) := by
        rcases hzl with rfl | rfl
        · exact dvd_rfl
        · exact hdvd i z (by omega) hij
      rw [Φ3w_22 h1 h2]
      simp only [S2', Prod.smul_mk, smul_zero]
      rw [zsmul_single_zmod' (fun q : ι × ι => F.o q.1) (i, j) hd]; rfl
  | [i, j, k], hzl, hWw, hs =>
    have hij : i ≤ j := (List.pairwise_cons.mp hs).1 j (by simp)
    have hik : i ≤ k := (List.pairwise_cons.mp hs).1 k (by simp)
    have hjk : j ≤ k := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 k (by simp)
    simp at hzl hWw
    have := hmono i j hij; have := hmono j k hjk; have := hp i; have := hp j; have := hp k
    have h1 : F.w i = 1 := by omega
    have h2 : F.w j = 1 := by omega
    have h3 : F.w k = 2 := by omega
    have hd : ((Nat.gcd (F.o i) (F.o k) : ℕ) : ℤ) ∣ (F.o z : ℤ) := by
      rcases hzl with rfl | rfl | rfl
      · exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
      · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))
          (hdvd i z (by omega) hij)
      · exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    rw [Φ3w_112 h1 h2 h3]
    simp only [S22, Prod.smul_mk, smul_zero]
    rw [zsmul_single_zmod' (fun q : ι × ι × ι => Nat.gcd (F.o q.1) (F.o q.2.2)) (i, j, k) hd]; rfl
  | [i, j, k, l], hzl, hWw, hs =>
    have hle : ∀ b ∈ [j, k, l], i ≤ b := (List.pairwise_cons.mp hs).1
    simp at hzl hWw
    have := hp i; have := hp j; have := hp k; have := hp l
    have h1 : F.w i = 1 := by omega
    have h2 : F.w j = 1 := by omega
    have h3 : F.w k = 1 := by omega
    have h4 : F.w l = 1 := by omega
    have hd : ((F.o i : ℕ) : ℤ) ∣ (F.o z : ℤ) := by
      rcases hzl with rfl | rfl | rfl | rfl
      · exact dvd_rfl
      · exact hdvd i z (by omega) (hle z (by simp))
      · exact hdvd i z (by omega) (hle z (by simp))
      · exact hdvd i z (by omega) (hle z (by simp))
    rw [Φ3w_1111 h1 h2 h3 h4]
    simp only [S4, Prod.smul_mk, smul_zero]
    rw [zsmul_single_zmod' (fun q : ι × ι × ι × ι => F.o q.1) (i, j, k, l) hd]; rfl
  | [], hzl, _, _ => simp at hzl
  | i :: j :: k :: l :: m :: t, _, hWw, _ =>
    simp at hWw
    have := hp i; have := hp j; have := hp k; have := hp l; have := hp m
    omega

/-! ## The shape of the rest `r = a - d e_x` -/

omit IH in
theorem sub_eq_r {h : ℕ} (hh : h ≤ F.o x) :
    a - (F.o x - h) • (Pi.single x 1 : ι → ℕ) = (F.lo a x + hi a x) + h • Pi.single x 1 := by
  rw [← F.lo_add_hi hx h hh]; abel

omit IH in
theorem a_eq_r : a = (F.lo a x + hi a x) + F.o x • Pi.single x 1 := by
  have := sub_eq_r hx (le_refl (F.o x)); rwa [Nat.sub_self, zero_smul, tsub_zero] at this

omit IH in
/-- If the rest is `cnt (l₁ ++ l₂)` with `l₁ ≤ x < l₂`, then `a_lo = cnt l₁`, `a_hi = cnt l₂`. -/
theorem lo_hi_split {l₁ l₂ : List ι} (h₁ : ∀ i ∈ l₁, i ≤ x) (h₂ : ∀ i ∈ l₂, x < i)
    (hr : F.lo a x + hi a x = cnt (l₁ ++ l₂)) : F.lo a x = cnt l₁ ∧ hi a x = cnt l₂ := by
  have c1 : ∀ i, i ∈ l₂ → ¬ i ≤ x := fun i hi h => absurd (h₂ i hi) (not_lt.2 h)
  constructor
  · rw [lo_eq_restrict hx, hr]
    funext j
    rw [cnt_append]
    by_cases hj : j ≤ x
    · simp only [hj, if_true, Pi.add_apply]
      have : cnt l₂ j = 0 := List.count_eq_zero.mpr fun hm => c1 j hm hj
      rw [this, add_zero]
    · simp only [hj, if_false]
      exact (List.count_eq_zero.mpr fun hm => hj (h₁ j hm)).symm
  · rw [hi_eq_restrict (F := F) (a := a) (x := x), hr]
    funext j
    rw [cnt_append]
    by_cases hj : x < j
    · simp only [hj, if_true, Pi.add_apply]
      have : cnt l₁ j = 0 := List.count_eq_zero.mpr fun hm => absurd (h₁ j hm) (not_le.2 hj)
      rw [this, zero_add]
    · simp only [hj, if_false]
      exact (List.count_eq_zero.mpr fun hm => hj (h₂ j hm)).symm

omit IH hx in
theorem W_nsmul_single (m : ℕ) (z : ι) : F.W (m • (Pi.single z 1 : ι → ℕ)) = m * F.w z := by
  rw [← cnt_replicate, W_cnt]; simp

omit IH hx in
/-- The rest of weight `≤ 2` is one of a few words. -/
theorem shape_of_W {r : ι → ℕ} (hr : F.W r ≤ 2) :
    r = 0 ∨ (∃ i, F.w i = 1 ∧ r = cnt [i]) ∨ (∃ k, F.w k = 2 ∧ r = cnt [k]) ∨
      (∃ i j, i ≤ j ∧ F.w i = 1 ∧ F.w j = 1 ∧ r = cnt [i, j]) := by
  have hcnt : r = cnt (word r) := funext fun j => (count_of_word rfl j)
  have hWw := F.W_eq_word r
  have hsort := word_pairwise r
  have hp := F.w_pos
  generalize word r = l at hcnt hWw hsort
  match l, hWw, hsort with
  | [], _, _ => left; rw [hcnt, cnt_nil]
  | [i], hWw, _ =>
    simp at hWw
    rcases (show F.w i = 1 ∨ F.w i = 2 by have := hp i; omega) with h | h
    · exact Or.inr (Or.inl ⟨i, h, hcnt⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, h, hcnt⟩))
  | [i, j], hWw, hs =>
    simp at hWw
    have := hp i; have := hp j
    exact Or.inr (Or.inr (Or.inr ⟨i, j, (List.pairwise_cons.mp hs).1 j (by simp), by omega,
      by omega, hcnt⟩))
  | i :: j :: k :: t, hWw, _ =>
    simp at hWw; have := hp i; have := hp j; have := hp k; omega

/-! ## The standard reduction step -/

/-- When all binomial terms have weight `≥ 3`: `ψ(P a) - Φ(a) ≡ vT - ∑_m C(d,m) Φ(r + m e_x)`. -/
theorem std_case {vT : F.M3}
    (hT : (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x), vT) ∈ rel3 hF)
    (h3 : 3 ≤ F.W (F.lo a x + hi a x) + F.w x)
    (hf4 : ∀ m, 4 ≤ m → F.Φ3 ((F.lo a x + hi a x) + m • Pi.single x 1) = 0)
    (hid : vT - ((F.o x : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 1 • Pi.single x 1) +
      (((F.o x).choose 2 : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 2 • Pi.single x 1) +
        ((F.o x).choose 3 : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 3 • Pi.single x 1))) ∈ F.R5) :
    (F.P a, F.Φ3 a) ∈ rel3 hF := by
  refine combine IH hx hT (rel3_sum hF _ _ _ _ (binom_IH IH hx h3)) ?_
  have e : ∑ h ∈ Finset.range (F.o x - 1), ((F.o x).choose (h + 1) : ℤ) •
        F.Φ3 (a - (F.o x - (h + 1)) • (Pi.single x 1 : ι → ℕ)) + F.Φ3 a =
      (F.o x : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 1 • Pi.single x 1) +
        (((F.o x).choose 2 : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 2 • Pi.single x 1) +
          ((F.o x).choose 3 : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 3 • Pi.single x 1)) := by
    have := binom_trunc (fun m => F.Φ3 ((F.lo a x + hi a x) + m • Pi.single x 1)) (F.o_pos x)
      hf4
    rw [← this]
    congr 1
    · refine Finset.sum_congr rfl fun h hh => ?_
      rw [Finset.mem_range] at hh
      rw [sub_eq_r hx (by omega)]
    · conv_lhs => rw [a_eq_r hx]
  rw [sub_sub, e]; exact hid

end Step


section Cases

variable {a : ι → ℕ} (IH : IHat hF a) {x : ι} (hx : F.o x ≤ a x)
include IH hx

theorem W_r_add (m : ℕ) : F.W ((F.lo a x + hi a x) + m • Pi.single x 1) =
    F.W (F.lo a x + hi a x) + m * F.w x := by
  rw [W_add, W_nsmul_single]

/-- **Case A**: `W(r) + w(x) ≥ 4`; everything vanishes. -/
theorem case_A (h4 : 4 ≤ F.W (F.lo a x + hi a x) + F.w x) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  have hwx := F.w_pos x
  have hWr := W_add (F := F) (F.lo a x) (hi a x)
  have hT : (F.P (F.lo a x) * E (F.yy x) * F.P (hi a x), (0 : F.M3)) ∈ rel3 hF := by
    refine F.below_rel (rel3 hF) (a := a) (K := 5) (fun β hβ h5 => ?_)
      (F.Below_mono (by omega) (F.T_mem hx))
    have := IH β hβ (by omega)
    rwa [F.Φ3_eq_zero_of_five_le h5] at this
  refine std_case IH hx hT (by omega) (fun m hm => F.Φ3_eq_zero_of_five_le (by
    rw [W_r_add IH hx]; nlinarith)) ?_
  have h2 : F.Φ3 ((F.lo a x + hi a x) + 2 • Pi.single x 1) = 0 :=
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx]; omega)
  have h3 : F.Φ3 ((F.lo a x + hi a x) + 3 • Pi.single x 1) = 0 :=
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx]; omega)
  have h1 : (F.o x : ℤ) • F.Φ3 ((F.lo a x + hi a x) + 1 • Pi.single x 1) = 0 := by
    rcases (show F.W (F.lo a x + hi a x) + F.w x = 4 ∨ 5 ≤ F.W (F.lo a x + hi a x) + F.w x
      by omega) with h | h
    · exact torsion hF (by simp) (by rw [W_r_add IH hx]; omega)
    · rw [F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx]; omega), smul_zero]
  rw [h1, h2, h3, smul_zero, smul_zero, add_zero, add_zero, sub_zero]; exact zero_mem _

/-- **Case (I)**: `w(x) = 3`, `r = 0`. -/
theorem case_I (hw : F.w x = 3) (hr : F.lo a x + hi a x = 0) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  have hlo : F.lo a x = 0 := funext fun j => by
    have := congrFun hr j; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; omega
  have hhi : hi a x = 0 := funext fun j => by
    have := congrFun hr j; simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; omega
  have hT := TE1 IH hx hhi (by rw [hlo, W_zero (F := F)]; omega)
    (by rw [hlo, W_zero (F := F)]; omega)
  refine std_case IH hx hT (by rw [hr, W_zero (F := F)]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, W_zero (F := F)]; nlinarith)) ?_
  rw [hr, hlo, zero_add, zero_add, zero_add,
    F.Φ3_eq_zero_of_five_le (a := 2 • Pi.single x 1) (by rw [W_nsmul_single]; omega),
    F.Φ3_eq_zero_of_five_le (a := 3 • Pi.single x 1) (by rw [W_nsmul_single]; omega),
    one_smul, smul_zero, smul_zero, add_zero, add_zero]
  have := neg_mem (F.gI_mem hw)
  convert this using 1
  rw [gI, ← cnt_single]; abel

/-- **Case (IV)**: `w(x) = 2`, `r = e_i` with `w(i) = 1`. -/
theorem case_IV (hw : F.w x = 2) {i : ι} (hi1 : F.w i = 1) (hr : F.lo a x + hi a x = cnt [i]) :
    (F.P a, F.Φ3 a) ∈ rel3 hF := by
  have hix : i < x := F.lt_of_w_lt (by omega)
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := [i]) (l₂ := []) (by simp [hix.le]) (by simp)
    (by simpa using hr)
  rw [cnt_nil] at hhi
  have hWi : F.W (cnt [i]) = 1 := by rw [W_cnt]; simp [hi1]
  have hT := TE1 IH hx hhi (by rw [hlo, hWi]; omega) (by rw [hlo, hWi]; omega)
  refine std_case IH hx hT (by rw [hr, hWi]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hWi]; nlinarith)) ?_
  rw [hr, hlo, F.Φ3_eq_zero_of_five_le (a := cnt [i] + 2 • Pi.single x 1)
      (by rw [W_add, W_nsmul_single, hWi]; omega),
    F.Φ3_eq_zero_of_five_le (a := cnt [i] + 3 • Pi.single x 1)
      (by rw [W_add, W_nsmul_single, hWi]; omega),
    smul_zero, smul_zero, add_zero, add_zero, one_smul,
    show cnt [i] + Pi.single x 1 = cnt [i, x] by rw [← cnt_single, ← cnt_append]; rfl]
  exact F.gIV_mem hi1 hw

omit IH in
theorem Φ3_r_rep {l₁ l₂ : List ι} (hr : F.lo a x + hi a x = cnt (l₁ ++ l₂)) (m : ℕ)
    (hs : (l₁ ++ List.replicate m x ++ l₂).Pairwise (· ≤ ·)) :
    F.Φ3 ((F.lo a x + hi a x) + m • Pi.single x 1) = F.Φ3w (l₁ ++ List.replicate m x ++ l₂) := by
  rw [← F.Φ3_cnt hs, hr, ← cnt_replicate, cnt_append, cnt_append, cnt_append]
  abel_nf

omit IH in
theorem f3_zero {r : ι → ℕ} (hr : F.lo a x + hi a x = r) (hW : 2 ≤ F.W r) (hw : F.w x = 1) :
    F.Φ3 ((F.lo a x + hi a x) + 3 • Pi.single x 1) = 0 :=
  F.Φ3_eq_zero_of_five_le (by rw [hr, W_add, W_nsmul_single, hw]; omega)

/-- **Case (VII)**: `j ≤ k < x`, all of weight 1. -/
theorem case_VII (hw : F.w x = 1) {j k : ι} (hj : F.w j = 1) (hk : F.w k = 1) (hjk : j ≤ k)
    (hkx : k < x) (hr : F.lo a x + hi a x = cnt [j, k]) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := [j, k]) (l₂ := []) (by simp [hkx.le, hjk.trans hkx.le])
    (by simp) (by simpa using hr)
  rw [cnt_nil] at hhi
  have hW : F.W (cnt [j, k]) = 2 := by rw [W_cnt]; simp [hj, hk]
  have hT := TE1 IH hx hhi (by rw [hlo, hW]; omega) (by rw [hlo, hW]; omega)
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  rw [f3_zero hx hr (by rw [hW]) hw,
    Φ3_r_rep hx (l₁ := [j, k]) (l₂ := []) (by simpa using hr) 1 (by simp [hjk, hkx.le, (hjk.trans hkx.le)]),
    Φ3_r_rep hx (l₁ := [j, k]) (l₂ := []) (by simpa using hr) 2 (by simp [hjk, hkx.le, (hjk.trans hkx.le)]),
    hlo]
  have := F.gVII_mem hj hk hw hjk hkx
  convert this using 1
  simp only [gVII, F.Φ3_cnt (show [j, k, x].Pairwise (· ≤ ·) by simp [hjk, hkx.le, (hjk.trans hkx.le)]),
    F.Φ3_cnt (show [j, k, x, x].Pairwise (· ≤ ·) by simp [hjk, hkx.le, (hjk.trans hkx.le)])]
  simp; abel

/-- **Case (VI)**, `j < x < k`. -/
theorem case_VI (hw : F.w x = 1) {j k : ι} (hj : F.w j = 1) (hk : F.w k = 1) (hjx : j < x)
    (hxk : x < k) (hr : F.lo a x + hi a x = cnt [j, k]) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := [j]) (l₂ := [k]) (by simp [hjx.le]) (by simp [hxk])
    (by simpa using hr)
  have hW : F.W (cnt [j, k]) = 2 := by rw [W_cnt]; simp [hj, hk]
  have hT := TE2 IH hx hw hk hxk hhi
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  have hs : ∀ m, ([j] ++ List.replicate m x ++ [k]).Pairwise (· ≤ ·) := by
    intro m
    rw [List.append_assoc, List.singleton_append, List.pairwise_cons, List.pairwise_append]
    refine ⟨fun b hb => ?_, List.pairwise_replicate.mpr (Or.inr le_rfl),
      List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    · rcases List.mem_append.mp hb with hb | hb
      · rw [List.eq_of_mem_replicate hb]; exact hjx.le
      · rw [List.mem_singleton.mp hb]; exact (hjx.trans hxk).le
    · rw [List.eq_of_mem_replicate ha, List.mem_singleton.mp hb]; exact hxk.le
  rw [f3_zero hx hr (by rw [hW]) hw, Φ3_r_rep hx (by simpa using hr) 1 (hs 1),
    Φ3_r_rep hx (by simpa using hr) 2 (hs 2), hlo,
    show cnt [j] + cnt [k] = cnt [j, k] by rw [← cnt_append]; rfl,
    F.nsum_eq_zero (k := 3) (cc_mem (F := F) (x := x) hw k hk) (β := cnt [j, k]) (by rw [hW])]
  have := F.gVI_mem hj hw hk hjx.le hxk.le
  convert this using 1
  simp only [gVI, F.Φ3_cnt (show [j, x, k].Pairwise (· ≤ ·) by
      simp [hjx.le, hxk.le, (hjx.trans hxk).le]),
    F.Φ3_cnt (show [j, x, x, k].Pairwise (· ≤ ·) by simp [hjx.le, hxk.le, (hjx.trans hxk).le])]
  simp; abel

/-- **Case (VI)**, `j < x`, the second letter `x` itself. -/
theorem case_VI' (hw : F.w x = 1) {j : ι} (hj : F.w j = 1) (hjx : j < x)
    (hr : F.lo a x + hi a x = cnt [j, x]) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := [j, x]) (l₂ := []) (by simp [hjx.le]) (by simp)
    (by simpa using hr)
  rw [cnt_nil] at hhi
  have hW : F.W (cnt [j, x]) = 2 := by rw [W_cnt]; simp [hj, hw]
  have hT := TE1 IH hx hhi (by rw [hlo, hW]; omega) (by rw [hlo, hW]; omega)
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  rw [f3_zero hx hr (by rw [hW]) hw,
    Φ3_r_rep hx (l₁ := [j, x]) (l₂ := []) (by simpa using hr) 1 (by simp [hjx.le]),
    Φ3_r_rep hx (l₁ := [j, x]) (l₂ := []) (by simpa using hr) 2 (by simp [hjx.le]), hlo]
  have := F.gVI_mem hj hw hw hjx.le le_rfl
  convert this using 1
  simp only [gVI, cc_self, nsum_one, F.Φ3_cnt (show [j, x, x].Pairwise (· ≤ ·) by simp [hjx.le]),
    F.Φ3_cnt (show [j, x, x, x].Pairwise (· ≤ ·) by simp [hjx.le])]
  simp; abel

/-- **Case (V)**, `x < j ≤ k`. -/
theorem case_V (hw : F.w x = 1) {j k : ι} (hj : F.w j = 1) (hk : F.w k = 1) (hxj : x < j)
    (hjk : j ≤ k) (hr : F.lo a x + hi a x = cnt [j, k]) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  have hxk := lt_of_lt_of_le hxj hjk
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := []) (l₂ := [j, k]) (by simp) (by simp [hxj, hxk])
    (by simpa using hr)
  rw [cnt_nil] at hlo
  have hW : F.W (cnt [j, k]) = 2 := by rw [W_cnt]; simp [hj, hk]
  have hT := TE3 IH hx hw hj hk hxj hjk hhi
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  rw [f3_zero hx hr (by rw [hW]) hw,
    Φ3_r_rep hx (l₁ := []) (l₂ := [j, k]) (by simpa using hr) 1 (by simp [hjk, hxj.le, hxk.le]),
    Φ3_r_rep hx (l₁ := []) (l₂ := [j, k]) (by simpa using hr) 2 (by simp [hjk, hxj.le, hxk.le]),
    hlo, zero_add, zero_add, zero_add]
  have := F.gV_mem hw hj hk hxj.le hjk
  convert this using 1
  simp only [gV, F.Φ3_cnt (show [x, j, k].Pairwise (· ≤ ·) by simp [hjk, hxj.le, hxk.le]),
    F.Φ3_cnt (show [x, x, j, k].Pairwise (· ≤ ·) by simp [hjk, hxj.le, hxk.le])]
  simp; abel

/-- **Case (V)**, `x < k`, the first letter `x` itself. -/
theorem case_V' (hw : F.w x = 1) {k : ι} (hk : F.w k = 1) (hxk : x < k)
    (hr : F.lo a x + hi a x = cnt [x, k]) : (F.P a, F.Φ3 a) ∈ rel3 hF := by
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := [x]) (l₂ := [k]) (by simp) (by simp [hxk])
    (by simpa using hr)
  have hW : F.W (cnt [x, k]) = 2 := by rw [W_cnt]; simp [hk, hw]
  have hT := TE2 IH hx hw hk hxk hhi
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  have hs : ∀ m, ([x] ++ List.replicate m x ++ [k]).Pairwise (· ≤ ·) := by
    intro m
    rw [List.append_assoc, List.singleton_append, List.pairwise_cons, List.pairwise_append]
    refine ⟨fun b hb => ?_, List.pairwise_replicate.mpr (Or.inr le_rfl),
      List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    · rcases List.mem_append.mp hb with hb | hb
      · rw [List.eq_of_mem_replicate hb]
      · rw [List.mem_singleton.mp hb]; exact hxk.le
    · rw [List.eq_of_mem_replicate ha, List.mem_singleton.mp hb]; exact hxk.le
  rw [f3_zero hx hr (by rw [hW]) hw, Φ3_r_rep hx (by simpa using hr) 1 (hs 1),
    Φ3_r_rep hx (by simpa using hr) 2 (hs 2), hlo,
    show cnt [x] + cnt [k] = cnt [x, k] by rw [← cnt_append]; rfl,
    F.nsum_eq_zero (k := 3) (cc_mem (F := F) (x := x) hw k hk) (β := cnt [x, k]) (by rw [hW])]
  have := F.gV_mem hw hw hk le_rfl hxk.le
  convert this using 1
  simp only [gV, cc_self, tc_one_left, nsum_one,
    F.Φ3_cnt (show [x, x, k].Pairwise (· ≤ ·) by simp [hxk.le]),
    F.Φ3_cnt (show [x, x, x, k].Pairwise (· ≤ ·) by simp [hxk.le])]
  simp; abel

/-- **Case (V)**, the rest `x, x`. -/
theorem case_V'' (hw : F.w x = 1) (hr : F.lo a x + hi a x = cnt [x, x]) :
    (F.P a, F.Φ3 a) ∈ rel3 hF := by
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := [x, x]) (l₂ := []) (by simp) (by simp)
    (by simpa using hr)
  rw [cnt_nil] at hhi
  have hW : F.W (cnt [x, x]) = 2 := by rw [W_cnt]; simp [hw]
  have hT := TE1 IH hx hhi (by rw [hlo, hW]; omega) (by rw [hlo, hW]; omega)
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  rw [f3_zero hx hr (by rw [hW]) hw,
    Φ3_r_rep hx (l₁ := [x, x]) (l₂ := []) (by simpa using hr) 1 (by simp),
    Φ3_r_rep hx (l₁ := [x, x]) (l₂ := []) (by simpa using hr) 2 (by simp), hlo]
  have := F.gV_mem hw hw hw le_rfl le_rfl
  convert this using 1
  simp only [gV, cc_self, tc_one_left, nsum_one, F.Φ3_cnt (show [x, x, x].Pairwise (· ≤ ·) by simp),
    F.Φ3_cnt (show [x, x, x, x].Pairwise (· ≤ ·) by simp)]
  simp; abel

/-- **Case (III)**: the rest is a letter `k` of weight 2. -/
theorem case_III (hw : F.w x = 1) {k : ι} (hk : F.w k = 2) (hr : F.lo a x + hi a x = cnt [k]) :
    (F.P a, F.Φ3 a) ∈ rel3 hF := by
  have hxk : x < k := F.lt_of_w_lt (by omega)
  obtain ⟨hlo, hhi⟩ := lo_hi_split hx (l₁ := []) (l₂ := [k]) (by simp) (by simp [hxk])
    (by simpa using hr)
  rw [cnt_nil] at hlo
  have hW : F.W (cnt [k]) = 2 := by rw [W_cnt]; simp [hk]
  have hT := TE4 IH hx hw hk hxk hhi
  refine std_case IH hx hT (by rw [hr, hW]; omega) (fun m hm =>
    F.Φ3_eq_zero_of_five_le (by rw [W_r_add IH hx, hr, hW]; nlinarith)) ?_
  rw [f3_zero hx hr (by rw [hW]) hw,
    Φ3_r_rep hx (l₁ := []) (l₂ := [k]) (by simpa using hr) 1 (by simp [hxk.le]),
    Φ3_r_rep hx (l₁ := []) (l₂ := [k]) (by simpa using hr) 2 (by simp [hxk.le]), hlo, zero_add]
  have := F.gIII_mem hw hk
  convert this using 1
  simp only [gIII, F.Φ3_cnt (show [x, k].Pairwise (· ≤ ·) by simp [hxk.le]),
    F.Φ3_cnt (show [x, x, k].Pairwise (· ≤ ·) by simp [hxk.le])]
  simp; abel

end Cases

end Frame

end TaharaProof

end GroupDimension
