module

public import GroupDimension.TaharaProof.Decode1

@[expose] public section

/-!
# Coordinates of `W₃* ⊕ W₄`, and `D₅ ⊆ ker S mod R₅*` ([Tah81, §6])

Coordinate maps of `M3` (`cE3`, …, `cA4`), injectivity of the symbol modulo (I), and the key
consequence of Lemma 5.6: for `z ∈ D₅ ∩ γ₃`, `ψ₃(z - 1) = S z` lies in `R₅*`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

section Coords

variable (F : Frame G ι)

/-! ## Coordinates of `M3` -/

/-- The coordinate `E3` at `p`. -/
def cE3 (F : Frame G ι) (p : ι × ι × ι) : F.M3 →+ ℤ where
  toFun m := m.1.1 p
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coordinate `E12` at `p`. -/
def cE12 (F : Frame G ι) (p : ι × ι) : F.M3 →+ ℤ where
  toFun m := m.1.2.1 p
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coordinate `E3'` at `p`. -/
def cE3' (F : Frame G ι) (p : ι) : F.M3 →+ ℤ where
  toFun m := m.1.2.2 p
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coordinate `S4` at `p`. -/
def cS4 (F : Frame G ι) (a b c d : ι) : F.M3 →+ ZMod (F.o a) where
  toFun m := m.2.1 (a, b, c, d)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coordinate `S22` at `p`. -/
def cS22 (F : Frame G ι) (a b c : ι) : F.M3 →+ ZMod (Nat.gcd (F.o a) (F.o c)) where
  toFun m := m.2.2.1 (a, b, c)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coordinate `T13` at `p`. -/
def cT13 (F : Frame G ι) (a l : ι) : F.M3 →+ ZMod (Nat.gcd (F.o a) (F.o l)) where
  toFun m := m.2.2.2.1 (a, l)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coordinate `S2'` at `p`. -/
def cS2' (F : Frame G ι) (k l : ι) : F.M3 →+ ZMod (F.o k) where
  toFun m := m.2.2.2.2.1 (k, l)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `A₄` component. -/
def cA4 (F : Frame G ι) : F.M3 →+ Additive (Layer G 3) where
  toFun m := m.2.2.2.2.2
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem cE3_E3 {i : ι} {j : ι} {k : ι} (p : ι × ι × ι) : F.cE3 p (F.E3 i j k) = if p = (i, j, k) then 1 else 0 := by
  simp [cE3, E3, Pi.single_apply]

@[simp] theorem cE3_E12 {i : ι} {k : ι} (p : ι × ι × ι) : F.cE3 p (F.E12 i k) = 0 := by
  simp [cE3, E12]

@[simp] theorem cE3_E3p {l : ι} (p : ι × ι × ι) : F.cE3 p (F.E3' l) = 0 := by
  simp [cE3, E3']

@[simp] theorem cE3_S4 {i : ι} {j : ι} {k : ι} {l : ι} (p : ι × ι × ι) : F.cE3 p (F.S4 i j k l) = 0 := by
  simp [cE3, S4]

@[simp] theorem cE3_S22 {i : ι} {j : ι} {k : ι} (p : ι × ι × ι) : F.cE3 p (F.S22 i j k) = 0 := by
  simp [cE3, S22]

@[simp] theorem cE3_T13 {i : ι} {l : ι} (p : ι × ι × ι) : F.cE3 p (F.T13 i l) = 0 := by
  simp [cE3, T13]

@[simp] theorem cE3_S2p {k : ι} {l : ι} (p : ι × ι × ι) : F.cE3 p (F.S2' k l) = 0 := by
  simp [cE3, S2']

@[simp] theorem cE3_A4 {g : G} (p : ι × ι × ι) : F.cE3 p (F.A4 g) = 0 := by
  simp [cE3, A4]

@[simp] theorem cE12_E3 {i : ι} {j : ι} {k : ι} (p : ι × ι) : F.cE12 p (F.E3 i j k) = 0 := by
  simp [cE12, E3]

@[simp] theorem cE12_E12 {i : ι} {k : ι} (p : ι × ι) : F.cE12 p (F.E12 i k) = if p = (i, k) then 1 else 0 := by
  simp [cE12, E12, Pi.single_apply]

@[simp] theorem cE12_E3p {l : ι} (p : ι × ι) : F.cE12 p (F.E3' l) = 0 := by
  simp [cE12, E3']

@[simp] theorem cE12_S4 {i : ι} {j : ι} {k : ι} {l : ι} (p : ι × ι) : F.cE12 p (F.S4 i j k l) = 0 := by
  simp [cE12, S4]

@[simp] theorem cE12_S22 {i : ι} {j : ι} {k : ι} (p : ι × ι) : F.cE12 p (F.S22 i j k) = 0 := by
  simp [cE12, S22]

@[simp] theorem cE12_T13 {i : ι} {l : ι} (p : ι × ι) : F.cE12 p (F.T13 i l) = 0 := by
  simp [cE12, T13]

@[simp] theorem cE12_S2p {k : ι} {l : ι} (p : ι × ι) : F.cE12 p (F.S2' k l) = 0 := by
  simp [cE12, S2']

@[simp] theorem cE12_A4 {g : G} (p : ι × ι) : F.cE12 p (F.A4 g) = 0 := by
  simp [cE12, A4]

@[simp] theorem cE3'_E3 {i : ι} {j : ι} {k : ι} (p : ι) : F.cE3' p (F.E3 i j k) = 0 := by
  simp [cE3', E3]

@[simp] theorem cE3'_E12 {i : ι} {k : ι} (p : ι) : F.cE3' p (F.E12 i k) = 0 := by
  simp [cE3', E12]

@[simp] theorem cE3'_E3p {l : ι} (p : ι) : F.cE3' p (F.E3' l) = if p = l then 1 else 0 := by
  simp [cE3', E3', Pi.single_apply]

@[simp] theorem cE3'_S4 {i : ι} {j : ι} {k : ι} {l : ι} (p : ι) : F.cE3' p (F.S4 i j k l) = 0 := by
  simp [cE3', S4]

@[simp] theorem cE3'_S22 {i : ι} {j : ι} {k : ι} (p : ι) : F.cE3' p (F.S22 i j k) = 0 := by
  simp [cE3', S22]

@[simp] theorem cE3'_T13 {i : ι} {l : ι} (p : ι) : F.cE3' p (F.T13 i l) = 0 := by
  simp [cE3', T13]

@[simp] theorem cE3'_S2p {k : ι} {l : ι} (p : ι) : F.cE3' p (F.S2' k l) = 0 := by
  simp [cE3', S2']

@[simp] theorem cE3'_A4 {g : G} (p : ι) : F.cE3' p (F.A4 g) = 0 := by
  simp [cE3', A4]

@[simp] theorem cS4_E3 {i : ι} {j : ι} {k : ι} (a b c d : ι) : F.cS4 a b c d (F.E3 i j k) = 0 := by
  simp [cS4, E3]

@[simp] theorem cS4_E12 {i : ι} {k : ι} (a b c d : ι) : F.cS4 a b c d (F.E12 i k) = 0 := by
  simp [cS4, E12]

@[simp] theorem cS4_E3p {l : ι} (a b c d : ι) : F.cS4 a b c d (F.E3' l) = 0 := by
  simp [cS4, E3']

@[simp] theorem cS4_S4 {i : ι} {j : ι} {k : ι} {l : ι} (a b c d : ι) : F.cS4 a b c d (F.S4 i j k l) = if (a, b, c, d) = (i, j, k, l) then 1 else 0 := by
  simp only [cS4, S4, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h
  · cases h; simp
  · simp [Pi.single_eq_of_ne h]

@[simp] theorem cS4_S22 {i : ι} {j : ι} {k : ι} (a b c d : ι) : F.cS4 a b c d (F.S22 i j k) = 0 := by
  simp [cS4, S22]

@[simp] theorem cS4_T13 {i : ι} {l : ι} (a b c d : ι) : F.cS4 a b c d (F.T13 i l) = 0 := by
  simp [cS4, T13]

@[simp] theorem cS4_S2p {k : ι} {l : ι} (a b c d : ι) : F.cS4 a b c d (F.S2' k l) = 0 := by
  simp [cS4, S2']

@[simp] theorem cS4_A4 {g : G} (a b c d : ι) : F.cS4 a b c d (F.A4 g) = 0 := by
  simp [cS4, A4]

@[simp] theorem cS22_E3 {i : ι} {j : ι} {k : ι} (a b c : ι) : F.cS22 a b c (F.E3 i j k) = 0 := by
  simp [cS22, E3]

@[simp] theorem cS22_E12 {i : ι} {k : ι} (a b c : ι) : F.cS22 a b c (F.E12 i k) = 0 := by
  simp [cS22, E12]

@[simp] theorem cS22_E3p {l : ι} (a b c : ι) : F.cS22 a b c (F.E3' l) = 0 := by
  simp [cS22, E3']

@[simp] theorem cS22_S4 {i : ι} {j : ι} {k : ι} {l : ι} (a b c : ι) : F.cS22 a b c (F.S4 i j k l) = 0 := by
  simp [cS22, S4]

@[simp] theorem cS22_S22 {i : ι} {j : ι} {k : ι} (a b c : ι) : F.cS22 a b c (F.S22 i j k) = if (a, b, c) = (i, j, k) then 1 else 0 := by
  simp only [cS22, S22, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h
  · cases h; simp
  · simp [Pi.single_eq_of_ne h]

@[simp] theorem cS22_T13 {i : ι} {l : ι} (a b c : ι) : F.cS22 a b c (F.T13 i l) = 0 := by
  simp [cS22, T13]

@[simp] theorem cS22_S2p {k : ι} {l : ι} (a b c : ι) : F.cS22 a b c (F.S2' k l) = 0 := by
  simp [cS22, S2']

@[simp] theorem cS22_A4 {g : G} (a b c : ι) : F.cS22 a b c (F.A4 g) = 0 := by
  simp [cS22, A4]

@[simp] theorem cT13_E3 {i : ι} {j : ι} {k : ι} (a l' : ι) : F.cT13 a l' (F.E3 i j k) = 0 := by
  simp [cT13, E3]

@[simp] theorem cT13_E12 {i : ι} {k : ι} (a l' : ι) : F.cT13 a l' (F.E12 i k) = 0 := by
  simp [cT13, E12]

@[simp] theorem cT13_E3p {l : ι} (a l' : ι) : F.cT13 a l' (F.E3' l) = 0 := by
  simp [cT13, E3']

@[simp] theorem cT13_S4 {i : ι} {j : ι} {k : ι} {l : ι} (a l' : ι) : F.cT13 a l' (F.S4 i j k l) = 0 := by
  simp [cT13, S4]

@[simp] theorem cT13_S22 {i : ι} {j : ι} {k : ι} (a l' : ι) : F.cT13 a l' (F.S22 i j k) = 0 := by
  simp [cT13, S22]

@[simp] theorem cT13_T13 {i : ι} {l : ι} (a l' : ι) : F.cT13 a l' (F.T13 i l) = if (a, l') = (i, l) then 1 else 0 := by
  simp only [cT13, T13, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h
  · cases h; simp
  · simp [Pi.single_eq_of_ne h]

@[simp] theorem cT13_S2p {k : ι} {l : ι} (a l' : ι) : F.cT13 a l' (F.S2' k l) = 0 := by
  simp [cT13, S2']

@[simp] theorem cT13_A4 {g : G} (a l' : ι) : F.cT13 a l' (F.A4 g) = 0 := by
  simp [cT13, A4]

@[simp] theorem cS2'_E3 {i : ι} {j : ι} {k : ι} (k' l' : ι) : F.cS2' k' l' (F.E3 i j k) = 0 := by
  simp [cS2', E3]

@[simp] theorem cS2'_E12 {i : ι} {k : ι} (k' l' : ι) : F.cS2' k' l' (F.E12 i k) = 0 := by
  simp [cS2', E12]

@[simp] theorem cS2'_E3p {l : ι} (k' l' : ι) : F.cS2' k' l' (F.E3' l) = 0 := by
  simp [cS2', E3']

@[simp] theorem cS2'_S4 {i : ι} {j : ι} {k : ι} {l : ι} (k' l' : ι) : F.cS2' k' l' (F.S4 i j k l) = 0 := by
  simp [cS2', S4]

@[simp] theorem cS2'_S22 {i : ι} {j : ι} {k : ι} (k' l' : ι) : F.cS2' k' l' (F.S22 i j k) = 0 := by
  simp [cS2', S22]

@[simp] theorem cS2'_T13 {i : ι} {l : ι} (k' l' : ι) : F.cS2' k' l' (F.T13 i l) = 0 := by
  simp [cS2', T13]

@[simp] theorem cS2'_S2p {k : ι} {l : ι} (k' l' : ι) : F.cS2' k' l' (F.S2' k l) = if (k', l') = (k, l) then 1 else 0 := by
  simp only [cS2', S2', AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h
  · cases h; simp
  · simp [Pi.single_eq_of_ne h]

@[simp] theorem cS2'_A4 {g : G} (k' l' : ι) : F.cS2' k' l' (F.A4 g) = 0 := by
  simp [cS2', A4]

@[simp] theorem cA4_E3 {i : ι} {j : ι} {k : ι} : F.cA4 (F.E3 i j k) = 0 := by
  simp [cA4, E3]

@[simp] theorem cA4_E12 {i : ι} {k : ι} : F.cA4 (F.E12 i k) = 0 := by
  simp [cA4, E12]

@[simp] theorem cA4_E3p {l : ι} : F.cA4 (F.E3' l) = 0 := by
  simp [cA4, E3']

@[simp] theorem cA4_S4 {i : ι} {j : ι} {k : ι} {l : ι} : F.cA4 (F.S4 i j k l) = 0 := by
  simp [cA4, S4]

@[simp] theorem cA4_S22 {i : ι} {j : ι} {k : ι} : F.cA4 (F.S22 i j k) = 0 := by
  simp [cA4, S22]

@[simp] theorem cA4_T13 {i : ι} {l : ι} : F.cA4 (F.T13 i l) = 0 := by
  simp [cA4, T13]

@[simp] theorem cA4_S2p {k : ι} {l : ι} : F.cA4 (F.S2' k l) = 0 := by
  simp [cA4, S2']

@[simp] theorem cA4_A4 {g : G} : F.cA4 (F.A4 g) = cl G 3 g := by
  simp [cA4, A4]

end Coords

variable [Fintype G] {F : Frame G ι} (hF : F.Class4)
include hF

omit hF in
theorem S_one : F.S (1 : G) = 0 := nsum_one 0

theorem S_inv {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) : F.S z⁻¹ + F.S z ∈ F.RI := by
  have := S_mul hF (inv_mem hz) hz
  rw [inv_mul_cancel, S_one, zero_sub] at this
  have := neg_mem this; rwa [neg_neg] at this

theorem S_zpow {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (k : ℤ) :
    F.S (z ^ k) - k • F.S z ∈ F.RI := by
  induction k using Int.induction_on with
  | zero => simp [S_one]
  | succ k ih =>
    have h1 := S_mul hF (zpow_mem hz k) hz
    rw [← zpow_add_one] at h1
    have := add_mem h1 ih
    convert this using 1; rw [add_smul, one_smul]; abel
  | pred k ih =>
    have h1 := S_mul hF (zpow_mem hz (-(k : ℤ))) (inv_mem hz)
    rw [← zpow_sub_one] at h1
    have h2 := S_inv hF hz
    have := add_mem (add_mem h1 ih) h2
    convert this using 1
    rw [sub_smul, neg_smul, one_smul]; abel

/-- **Injectivity**: an element of `γ₃` whose symbol lies in the span of (I) is trivial. -/
theorem eq_one_of_S_mem {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (hS : F.S z ∈ F.RI) :
    z = 1 := by
  classical
  obtain ⟨n3, n4, h3b, h3w, -, -, hzeq, hh0, hSeq⟩ := nf_split hF hz
  rw [hSeq] at hS
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hS
  have hgI : ∀ l : F.IdxI, F.gI l.1 = (F.o l.1 : ℤ) • F.E3' l.1 - F.A4 (F.x l.1 ^ F.o l.1) :=
    fun l => by rw [gI_eq hF l.2, Φ3_single, if_pos l.2]
  have hΦ : ∀ j, (n3 j : ℤ) • F.Φ3 (Pi.single j 1) = (n3 j : ℤ) • F.E3' j := fun j => by
    by_cases h : n3 j = 0
    · simp [h]
    · rw [Φ3_single, if_pos (h3w j h)]
  -- the coordinate at `x̄_l`
  have hcoord : ∀ l : F.IdxI, c l * (F.o l.1 : ℤ) = n3 l.1 := by
    intro l
    have := congrArg (F.cE3' l.1) hc
    simp only [map_sum, map_zsmul, map_add, hgI, hΦ, _root_.map_sub, cE3'_E3p, cE3'_A4, smul_eq_mul]
      at this
    rw [Finset.sum_eq_single l, Finset.sum_eq_single l.1] at this
    · simpa [mul_comm] using this
    · intro j _ hj; simp [Ne.symm hj]
    · simp
    · intro l' _ hl'
      have : l.1 ≠ l'.1 := fun h => hl' (Subtype.ext h.symm)
      simp [this]
    · simp
  have hc0 : ∀ l, c l = 0 := by
    intro l
    have h1 := hcoord l
    have h2 := h3b l.1
    have ho := F.o_pos l.1
    by_contra hcl
    rcases lt_or_gt_of_ne hcl with h | h
    · nlinarith
    · have : (F.o l.1 : ℤ) ≤ c l * F.o l.1 := le_mul_of_one_le_left (by omega) (by omega)
      omega
  have hn3 : n3 = 0 := funext fun j => by
    by_cases hj : n3 j = 0
    · exact hj
    · have := hcoord ⟨j, h3w j hj⟩; rw [hc0] at this; simp at this; omega
  simp only [hc0, zero_smul, Finset.sum_const_zero] at hc
  rw [hn3] at hc
  simp only [Pi.zero_apply, Nat.cast_zero, zero_smul, Finset.sum_const_zero, zero_add] at hc
  have h4 : F.nprod n4 = 1 := by
    have := congrArg F.cA4 hc
    simp only [cA4_A4, map_zero] at this
    have := (cl_eq_zero_iff hh0).mp this.symm
    rwa [hF.top, Subgroup.mem_bot] at this
  rw [hzeq, hn3, h4]
  simp [nprod, lprod]

/-- `ψ₃(z - 1) = S z` for `z ∈ γ₃`. -/
theorem rel3_S {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    (of ℤ G z - 1, F.S z) ∈ rel3 hF := by
  classical
  obtain ⟨-, h2⟩ := F.of_nprod_sub_one (F.nfc z)
  rw [F.nprod_nfc] at h2
  have hn : ∀ j, F.nfc z j ≠ 0 → 3 ≤ F.w j := fun j hj =>
    F.nf_weight (k := 3) (by simpa using hz) (F.nfc_lt z) (F.nprod_nfc z) hj
  -- the remainder
  have hrem : (of ℤ G z - 1 - ∑ j, (F.nfc z j : ℤ) • F.X j, (0 : F.M3)) ∈ rel3 hF := by
    generalize of ℤ G z - 1 - ∑ j, (F.nfc z j : ℤ) • F.X j = z0 at h2 ⊢
    induction h2 using Submodule.span_induction with
    | zero => exact rel3_zero hF
    | add u v _ _ hu hv => have := rel3_add hF hu hv; rwa [add_zero] at this
    | smul c u _ hu => have := rel3_smul hF c hu; rwa [smul_zero] at this
    | mem x hx =>
    obtain ⟨β, hβ, hβ2, rfl⟩ := hx
    have hβb : ∀ j, β j < F.o j := fun j => lt_of_le_of_lt (hβ j) (F.nfc_lt z j)
    have hW : 6 ≤ F.W β := by
      calc 6 = 2 * 3 := rfl
        _ ≤ (∑ j, β j) * 3 := Nat.mul_le_mul_right _ hβ2
        _ = ∑ j, β j * 3 := Finset.sum_mul _ _ _
        _ ≤ ∑ j, β j * F.w j := Finset.sum_le_sum fun j _ => by
            by_cases h : β j = 0
            · simp [h]
            · exact Nat.mul_le_mul_left _ (hn j (fun h0 => h (by
                have : β j ≤ F.nfc z j := hβ j; omega)))
    have := rel3_fam hF (F := F) (.inr (.inr (.inr ⟨F.toBasic β hβb, by
      rw [toBasic_val]; omega⟩)))
    simp only [fam, famVal, toBasic_val] at this
    rwa [F.Φ3_eq_zero_of_five_le (by omega)] at this
  -- the linear part
  have hlin : (∑ j, (F.nfc z j : ℤ) • F.X j, F.S z) ∈ rel3 hF := by
    have key : ∀ j ∈ Finset.univ.filter fun j => F.nfc z j ≠ 0,
        (F.P (Pi.single j 1), F.Φ3 (0 + Pi.single j 1)) ∈ rel3 hF := by
      intro j hj
      have hj0 := (Finset.mem_filter.mp hj).2
      have hb : ∀ i, (Pi.single j 1 : ι → ℕ) i < F.o i := single_basic hF j
      have := rel3_fam hF (F := F) (.inr (.inr (.inr ⟨F.toBasic _ hb, by
        rw [toBasic_val, W_single]; exact hn j hj0⟩)))
      simp only [fam, famVal, toBasic_val] at this
      rwa [zero_add]
    have := rel3_sum hF _ (fun j => (F.nfc z j : ℤ)) _ _ key
    rw [Finset.sum_filter_of_ne (p := fun j => F.nfc z j ≠ 0) (fun j _ h0 hj => h0 (by simp [hj])),
      Finset.sum_filter_of_ne (p := fun j => F.nfc z j ≠ 0) (fun j _ h0 hj => h0 (by simp [hj]))]
      at this
    simpa [F.P_single, S, nsum] using this
  have := rel3_add hF hlin hrem
  rwa [add_sub_cancel, add_zero] at this

/-- **`D₅ ∩ γ₃` has symbols in `R₅*`** ([Tah81, §6]). -/
theorem S_mem_R5 {z : G} (hz5 : z ∈ D 5 G) (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    F.S z ∈ F.R5 := by
  have r1 := rel3_S hF hz
  have r2 := rel3_of_mem_Sp5 hF (F.augIdeal_pow_le_Sp 5 (mem_D.mp hz5))
  obtain ⟨h1, e1⟩ := r1
  obtain ⟨h2, e2⟩ := r2
  have := sub_mem e2 e1
  simp only [sub_zero] at this
  rwa [sub_sub_cancel] at this

end Frame

end TaharaProof

end GroupDimension
