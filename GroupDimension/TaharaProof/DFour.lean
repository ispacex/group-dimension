module

public import GroupDimension.TaharaProof.Decode12

@[expose] public section

/-!
# `D₄` of a finite group of class `≤ 3`: decoding the `W₃*` part ([Tah81, §5])

For `g ∈ D₄ ∩ γ₃` the symbol `S g` need not lie in `R₅*`, but its `W₃*` part does: `g - 1` is
a combination of proper products of weight `≥ 4`, and `ψ₃` of those is their symbol `Φ₃` modulo
`R₅*`, which has no `W₃*` part (`S_fst_mem_R5`). In Tahara's frame of a group of class `≤ 3`
the `W₃*` coordinates of the combination of the relations give Tahara's conditions (A₂), (A₃)
and (B) (`admissibleAB_tau`). As `A₄ = γ₄` is trivial, its projection to `A₃ ⊕ A₄` is determined
by the `W₃*` part, and `eq_gen_of_proj` gives `g = gen τ` (`exists_gen_of_D_four`); the part
`W₄` of the symbol does not enter.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable [Fintype G] {F : Frame G ι} (hF : F.Class4)

omit [Fintype G] in
/-- The symbol of an `m`-sequence of weight `≠ 3` has no `W₃*` part. -/
theorem Φ3_fst_eq_zero {a : ι → ℕ} (h : F.W a ≠ 3) : (F.Φ3 a).1 = 0 := by
  have hW := F.W_eq_word a
  unfold Φ3
  generalize word a = l at hW
  have hp := F.w_pos
  match l with
  | [] => rfl
  | [i] =>
    simp at hW
    simp only [Φ3w]; split_ifs <;> first | omega | rfl
  | [i, j] =>
    simp at hW
    have := hp i; have := hp j
    simp only [Φ3w]; split_ifs <;> first | omega | rfl
  | [i, j, k] =>
    simp at hW
    have := hp i; have := hp j; have := hp k
    simp only [Φ3w]; split_ifs <;> first | omega | rfl
  | [i, j, k, l] =>
    simp at hW
    simp only [Φ3w]; split_ifs <;> rfl
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

/-- `ψ₃` of an element of `Sp 4` is, modulo `R₅*`, without `W₃*` part. -/
theorem rel3_of_mem_Sp4 {z : MonoidAlgebra ℤ G} (hz : z ∈ F.Sp 4 Set.univ) :
    ∃ v : F.M3, v.1 = 0 ∧ (z, v) ∈ rel3 hF := by
  induction hz using Submodule.span_induction with
  | zero => exact ⟨0, rfl, rel3_zero hF⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, ha'⟩ := hu
    obtain ⟨b, hb, hb'⟩ := hv
    exact ⟨a + b, by simp [ha, hb], rel3_add hF ha' hb'⟩
  | smul c u _ hu =>
    obtain ⟨a, ha, ha'⟩ := hu
    exact ⟨c • a, by simp [ha], rel3_smul hF c ha'⟩
  | mem z hz =>
    obtain ⟨a, ha, -, rfl⟩ := hz
    exact ⟨F.Φ3 a, Φ3_fst_eq_zero (by omega), U3 hF a (by omega)⟩

include hF in
/-- **The `W₃*` part of the symbol of `g ∈ D₄ ∩ γ₃` is that of an element of `R₅*`.** -/
theorem S_fst_mem_R5 {z : G} (hz4 : z ∈ D 4 G) (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    ∃ r ∈ F.R5, (F.S z).1 = r.1 := by
  obtain ⟨v, hv, h2⟩ := rel3_of_mem_Sp4 hF (F.augIdeal_pow_le_Sp 4 (mem_D.mp hz4))
  obtain ⟨h1, e1⟩ := rel3_S hF hz
  obtain ⟨h2', e2⟩ := h2
  refine ⟨F.S z - v, ?_, by simp [hv]⟩
  have := sub_mem e2 e1
  rwa [sub_sub_sub_cancel_left] at this

end Frame

/-- Tahara's conditions (A₂), (A₃) and (B) ([Tah81, pp. 159–160]): the ones that come from the
`W₃*` coordinates and involve `u`. -/
structure _root_.GroupDimension.Tahara.Data.AdmissibleAB {G : Type*} [Group G] (T : Data G)
    (τ : Coeffs T.s T.t) : Prop where
  A₂ : ∀ i j, i < j →
    τ.u i j * T.q i j * T.ch i 2 + τ.w i i j * T.d i + τ.w'' i i j * T.d j = 0
  A₃ : ∀ i j, i < j → -τ.u i j * T.ch j 2 + τ.w i j j * T.d i + τ.w' i j j * T.d j = 0
  B : ∀ i k, (∑ h, if i < h then τ.u i h * T.b h k else 0)
      - (∑ h, if h < i then τ.u h i * T.q h i * T.b h k else 0)
      + τ.v i k * T.d i + τ.v' i k * T.e k = 0

section TFrame

variable [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4) (ho4 : ∀ q, 1 < o4 q)

local notation "TF" => Tframe h4 hT hy4

attribute [-simp] Tframe_o1 Tframe_o2 Tframe_o3 Tframe_o4

variable {p : Fin T.u → ℤ} {U : Fin T.s × Fin T.s → ℤ} {V V' : Fin T.s × Fin T.t → ℤ}
  {W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ} {g : G}

theorem hE3_fst (hS : ((TF).S g).1 = (combx h4 hT hy4 p U V V' W5 W6 W7).1)
    (a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sII h4 hT hy4 U) +
      (if a ≤ b ∧ b ≤ c then -(W5 (a, b, c) * T.d a) else 0) +
      (if a < b ∧ b ≤ c then -(W6 (a, b, c) * T.d b) else 0) +
      (if a ≤ b ∧ b < c then -(W7 (a, b, c) * T.d c) else 0) = 0 := by
  have h : (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) ((TF).S g) =
      (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (combx h4 hT hy4 p U V V' W5 W6 W7) :=
    congrArg (fun x => x.1 (ℓ1 a, ℓ1 b, ℓ1 c)) hS
  rw [Frame.cE3_S, combx_eq] at h
  simp only [map_add, cE3_sI, cE3_sIII, cE3_sIV, cE3_sV, cE3_sVI, cE3_sVII] at h
  linear_combination -h

theorem hE12_fst (hS : ((TF).S g).1 = (combx h4 hT hy4 p U V V' W5 W6 W7).1)
    (i : Fin T.s) (k : Fin T.t) :
    (∑ h, if i < h then U (i, h) * T.b h k else 0) -
      (∑ h, if h < i then U (h, i) * (T.q h i * T.b h k) else 0) -
      V (i, k) * T.d i - V' (i, k) * T.e k = 0 := by
  have h : (TF).cE12 (ℓ1 i, ℓ2 k) ((TF).S g) =
      (TF).cE12 (ℓ1 i, ℓ2 k) (combx h4 hT hy4 p U V V' W5 W6 W7) :=
    congrArg (fun x => x.2.1 (ℓ1 i, ℓ2 k)) hS
  rw [Frame.cE12_S, combx_eq] at h
  simp only [map_add, cE12_sI, cE12_sII, cE12_sIII, cE12_sIV, cE12_sV, cE12_sVI,
    cE12_sVII] at h
  linear_combination -h

/-- Conditions (A₂), (A₃), (B) for the coefficients of the `W₃*` part of the symbol. -/
theorem admissibleAB_tau (hS : ((TF).S g).1 = (combx h4 hT hy4 p U V V' W5 W6 W7).1) :
    T.AdmissibleAB (tau U V V' W5 W6 W7) where
  A₂ i j hij := by
    have h := hE3_fst h4 hT hy4 hS i i j
    rw [cE3_sII_iij h4 hT hy4 U i j hij] at h
    simp only [le_refl, hij.le, hij, and_self, ite_true, lt_irrefl, false_and, ite_false,
      add_zero] at h
    show -U (i, j) * T.q i j * T.ch i 2 + W5 (i, i, j) * T.d i + W7 (i, i, j) * T.d j = 0
    simp only [Data.ch]
    first | linear_combination h | linear_combination -h
  A₃ i j hij := by
    have h := hE3_fst h4 hT hy4 hS i j j
    rw [cE3_sII_ijj h4 hT hy4 U i j hij] at h
    simp only [le_refl, hij.le, hij, and_self, ite_true, lt_irrefl, and_false, ite_false,
      add_zero] at h
    show -(-U (i, j)) * T.ch j 2 + W5 (i, j, j) * T.d i + W6 (i, j, j) * T.d j = 0
    simp only [Data.ch]
    first | linear_combination h | linear_combination -h
  B i k := by
    have h := hE12_fst h4 hT hy4 hS i k
    show (∑ h, if i < h then -U (i, h) * T.b h k else 0)
      - (∑ h, if h < i then -U (h, i) * T.q h i * T.b h k else 0)
      + V (i, k) * T.d i + V' (i, k) * T.e k = 0
    simp only [neg_mul, mul_assoc, sum_ite_neg]
    first | linear_combination h | linear_combination -h

omit [Fintype G] in
/-- With `γ₄ = 1`, `A₄` is trivial, so `proj` sees only the `W₃*` part. -/
theorem proj_eq_of_fst (h3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) {m m' : (TF).M3}
    (h : m.1 = m'.1) : (TF).proj m = (TF).proj m' := by
  have h0 : ∀ x : Additive (Layer G 3), x = 0 := by
    intro x
    obtain ⟨y, hy, rfl⟩ := cl_surj 3 x
    rw [h3, Subgroup.mem_bot] at hy
    rw [hy, cl_one]
  show ((0, 0, m.1.2.2), (0, 0, 0, 0, m.2.2.2.2.2)) =
    ((0, 0, m'.1.2.2), (0, 0, 0, 0, m'.2.2.2.2.2))
  rw [h, h0 m.2.2.2.2.2, h0 m'.2.2.2.2.2]

end TFrame

/-- **`D₄` in class `≤ 3`**: in a finite group with `γ₄ = 1` and Tahara's data `T`, an element of
`D₄` is Tahara's generator `gen τ` for a family `τ` satisfying (A₂), (A₃) and (B). -/
theorem exists_gen_of_D_four [Fintype G] {T : Data G} (hT : T.Valid)
    (h3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) {g : G} (hg4 : g ∈ D 4 G) :
    ∃ τ : Coeffs T.s T.t, T.AdmissibleAB τ ∧ g = T.gen τ := by
  have h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥ :=
    le_bot_iff.mp (h3 ▸ Subgroup.lowerCentralSeries_antitone ⊤ (by norm_num : 3 ≤ 4))
  obtain ⟨v, y4, o4, hy4, ho4⟩ := exists_layer4 (G := G)
  have hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    (Tframe h4 hT hy4).D_three_le (D_antitone (by norm_num : 3 ≤ 4) hg4)
  obtain ⟨r, hr, hgr⟩ := Frame.S_fst_mem_R5 (Tframe_class4 h4 hT hy4 ho4) hg4 hg
  obtain ⟨p, U, V, V', W5, W6, W7, rfl⟩ := RT_coeffs h4 hT hy4 (R5_le_RT h4 hT hy4 hr)
  rw [comb_eq h4 hT hy4 ho4] at hgr
  exact ⟨tau U V V' W5 W6 W7, admissibleAB_tau h4 hT hy4 hgr,
    eq_gen_of_proj h4 hT hy4 ho4 hg (proj_eq_of_fst h4 hT hy4 h3 hgr)⟩

end TaharaProof

end GroupDimension
