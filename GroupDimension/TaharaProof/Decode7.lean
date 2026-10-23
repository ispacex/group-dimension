module

public import GroupDimension.TaharaProof.Decode6

@[expose] public section

/-!
# An element of `R₅*` in Tahara's frame, explicitly

An element of `RT` is a combination of the relations (I)–(VII) with integer coefficients
(`RT_coeffs`); by the explicit forms of the relations (`Decode4`), it is the combination `combx`
of the basis vectors of `W₃* ⊕ W₄`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

section TFrame

variable [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4) (ho4 : ∀ q, 1 < o4 q)

local notation "TF" => Tframe h4 hT hy4

/-- A combination of the relations (I)–(VII). -/
noncomputable def comb (p : Fin T.u → ℤ) (U : Fin T.s × Fin T.s → ℤ)
    (V V' : Fin T.s × Fin T.t → ℤ) (W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ) : (TF).M3 :=
  ∑ l, p l • (TF).gI (ℓ3 l) +
  ∑ x, U x • (if x.1 < x.2 then (TF).gII (ℓ1 x.1) (ℓ1 x.2) else 0) +
  ∑ x, V x • (TF).gIII (ℓ1 x.1) (ℓ2 x.2) +
  ∑ x, V' x • (TF).gIV (ℓ1 x.1) (ℓ2 x.2) +
  ∑ x, W5 x • (if x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then (TF).gV (ℓ1 x.1) (ℓ1 x.2.1) (ℓ1 x.2.2)
    else 0) +
  ∑ x, W6 x • (if x.1 < x.2.1 ∧ x.2.1 ≤ x.2.2 then (TF).gVI (ℓ1 x.1) (ℓ1 x.2.1) (ℓ1 x.2.2)
    else 0) +
  ∑ x, W7 x • (if x.1 ≤ x.2.1 ∧ x.2.1 < x.2.2 then (TF).gVII (ℓ1 x.1) (ℓ1 x.2.1) (ℓ1 x.2.2)
    else 0)

theorem RT_coeffs {m : (TF).M3} (hm : m ∈ RT h4 hT hy4) :
    ∃ p U V V' W5 W6 W7, m = comb h4 hT hy4 p U V V' W5 W6 W7 := by
  unfold RT at hm
  obtain ⟨m6, h6, m7, h7, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨m5, h5, m6', h6', rfl⟩ := Submodule.mem_sup.mp h6
  obtain ⟨m4, h4', m5', h5', rfl⟩ := Submodule.mem_sup.mp h5
  obtain ⟨m3, h3, m4', h4'', rfl⟩ := Submodule.mem_sup.mp h4'
  obtain ⟨m2, h2, m3', h3', rfl⟩ := Submodule.mem_sup.mp h3
  obtain ⟨m1, h1, m2', h2', rfl⟩ := Submodule.mem_sup.mp h2
  obtain ⟨p, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
  obtain ⟨U, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h2'
  obtain ⟨V, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h3'
  obtain ⟨V', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h4''
  obtain ⟨W5, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h5'
  obtain ⟨W6, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h6'
  obtain ⟨W7, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h7
  exact ⟨p, U, V, V', W5, W6, W7, rfl⟩

/-! ## The explicit forms -/

/-- (II), explicitly. -/
noncomputable def XII (i j : Fin T.s) : (TF).M3 :=
  ∑ k, T.b j k • (TF).E12 (ℓ1 i) (ℓ2 k) + ∑ l, T.c j l • (TF).T13 (ℓ1 i) (ℓ3 l) -
    T.q i j • (∑ k, T.b i k • (TF).E12 (ℓ1 j) (ℓ2 k) + ∑ l, T.c i l • (TF).T13 (ℓ1 j) (ℓ3 l) +
      (TF).S ((TF).cc (ℓ1 i) (ℓ1 j)) + ∑ l, T.α i j l • (TF).T13 (ℓ1 j) (ℓ3 l) -
      ((T.d i).choose 2 : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 i) (ℓ1 j) -
      ((T.d i).choose 3 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 i) (ℓ1 i) (ℓ1 j)) -
    ((T.d j).choose 2 : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 j) -
    ((T.d j).choose 3 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 j) (ℓ1 j) (ℓ1 j)

/-- (III), explicitly. -/
noncomputable def XIII (i : Fin T.s) (k : Fin T.t) : (TF).M3 :=
  ∑ m, T.b i m • (if k ≤ m then (TF).S2' (ℓ2 k) (ℓ2 m) else (TF).S2' (ℓ2 m) (ℓ2 k)) +
    ∑ m, T.b i m • (if k < m then (TF).A4 (tc (T.x₂ m) (T.x₂ k)) else 0) -
    (T.d i : ℤ) • (TF).E12 (ℓ1 i) (ℓ2 k) -
    ((T.d i).choose 2 : ℤ) • (TF).S22 (ℓ1 i) (ℓ1 i) (ℓ2 k)

/-- (IV), explicitly. -/
noncomputable def XIV (i : Fin T.s) (k : Fin T.t) : (TF).M3 :=
  ∑ l, T.dd k l • (TF).T13 (ℓ1 i) (ℓ3 l) - (T.e k : ℤ) • (TF).E12 (ℓ1 i) (ℓ2 k)

/-- (V), explicitly. -/
noncomputable def XV (i j k : Fin T.s) : (TF).M3 :=
  ∑ m, T.b i m • (TF).S22 (ℓ1 j) (ℓ1 k) (ℓ2 m) +
    ∑ l, T.α i k l • (TF).T13 (ℓ1 j) (ℓ3 l) + ∑ l, T.α i j l • (TF).T13 (ℓ1 k) (ℓ3 l) +
    (TF).A4 (tc ((TF).cc (ℓ1 i) (ℓ1 j)) (T.x₁ k)) -
    (T.d i : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 k) -
    ((T.d i).choose 2 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 i) (ℓ1 j) (ℓ1 k)

/-- (VI), explicitly. -/
noncomputable def XVI (i j k : Fin T.s) : (TF).M3 :=
  ∑ m, T.b j m • (TF).S22 (ℓ1 i) (ℓ1 k) (ℓ2 m) + ∑ l, T.α j k l • (TF).T13 (ℓ1 i) (ℓ3 l) -
    (T.d j : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 k) -
    ((T.d j).choose 2 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 j) (ℓ1 j) (ℓ1 k)

/-- (VII), explicitly. -/
noncomputable def XVII (i j k : Fin T.s) : (TF).M3 :=
  ∑ m, T.b k m • (TF).S22 (ℓ1 i) (ℓ1 j) (ℓ2 m) -
    (T.d k : ℤ) • (TF).E3 (ℓ1 i) (ℓ1 j) (ℓ1 k) -
    ((T.d k).choose 2 : ℤ) • (TF).S4 (ℓ1 i) (ℓ1 j) (ℓ1 k) (ℓ1 k)

/-- The combination, explicitly. -/
noncomputable def combx (p : Fin T.u → ℤ) (U : Fin T.s × Fin T.s → ℤ)
    (V V' : Fin T.s × Fin T.t → ℤ) (W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ) : (TF).M3 :=
  ∑ l, p l • ((T.f l : ℤ) • (TF).E3' (ℓ3 l) - (TF).A4 (T.x₃ l ^ T.f l)) +
  ∑ x, U x • (if x.1 < x.2 then XII h4 hT hy4 x.1 x.2 else 0) +
  ∑ x, V x • XIII h4 hT hy4 x.1 x.2 +
  ∑ x, V' x • XIV h4 hT hy4 x.1 x.2 +
  ∑ x, W5 x • (if x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 then XV h4 hT hy4 x.1 x.2.1 x.2.2 else 0) +
  ∑ x, W6 x • (if x.1 < x.2.1 ∧ x.2.1 ≤ x.2.2 then XVI h4 hT hy4 x.1 x.2.1 x.2.2 else 0) +
  ∑ x, W7 x • (if x.1 ≤ x.2.1 ∧ x.2.1 < x.2.2 then XVII h4 hT hy4 x.1 x.2.1 x.2.2 else 0)

include ho4 in
theorem comb_eq (p : Fin T.u → ℤ) (U : Fin T.s × Fin T.s → ℤ)
    (V V' : Fin T.s × Fin T.t → ℤ) (W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ) :
    comb h4 hT hy4 p U V V' W5 W6 W7 = combx h4 hT hy4 p U V V' W5 W6 W7 := by
  unfold comb combx
  simp only [gI_T h4 hT hy4 ho4, gIII_T h4 hT hy4 ho4, gIV_T h4 hT hy4]
  congr 1; congr 1; congr 1; congr 1; congr 1; congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [gII_T h4 hT hy4 h, V3val_T h4 hT hy4 h.le]; rfl
    · rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [gV_T h4 hT hy4 ho4 h.1 h.2]; rfl
    · rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [gVI_T h4 hT hy4 h.1.le h.2]; rfl
    · rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · rw [gVII_T h4 hT hy4 h.1 h.2]; rfl
    · rfl

/-! ## Coordinates -/

theorem map_ite0 {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N) (P : Prop)
    [Decidable P] (a : M) : f (if P then a else 0) = if P then f a else 0 := by
  split_ifs <;> simp

theorem ite_sub0 {M : Type*} [AddCommGroup M] (P : Prop) [Decidable P] (a b : M) :
    (if P then a - b else 0) = (if P then a else 0) - (if P then b else 0) := by
  split_ifs <;> simp

theorem ite_add0 {M : Type*} [AddCommMonoid M] (P : Prop) [Decidable P] (a b : M) :
    (if P then a + b else 0) = (if P then a else 0) + (if P then b else 0) := by
  split_ifs <;> simp

end TFrame

end TaharaProof

end GroupDimension
