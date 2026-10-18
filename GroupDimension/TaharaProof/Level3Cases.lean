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

end Step

end Frame

end TaharaProof

end GroupDimension
