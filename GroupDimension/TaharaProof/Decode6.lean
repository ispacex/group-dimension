module

public import GroupDimension.TaharaProof.Decode5

@[expose] public section

/-!
# The symbol modulo (I): coordinates, the projection to `A₃ ⊕ A₄`, products

The symbol `S z` of `z ∈ γ₃` lives in the `A₃ ⊕ A₄` part of `W₃* ⊕ W₄`; `proj` is the projection
to that part. Modulo (I), `S` turns products in `γ₃` into sums.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G] {ι : Type*} [LinearOrder ι] [Fintype ι]

namespace Frame

variable {F : Frame G ι}

/-- The projection of `W₃* ⊕ W₄` to `A₃ ⊕ A₄`. -/
def proj (F : Frame G ι) : F.M3 →+ F.M3 where
  toFun m := ((0, 0, m.1.2.2), (0, 0, 0, 0, m.2.2.2.2.2))
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

@[simp] theorem proj_E3 (i j k : ι) : F.proj (F.E3 i j k) = 0 := rfl
@[simp] theorem proj_E12 (i k : ι) : F.proj (F.E12 i k) = 0 := rfl
@[simp] theorem proj_E3p (l : ι) : F.proj (F.E3' l) = F.E3' l := rfl
@[simp] theorem proj_S4 (i j k l : ι) : F.proj (F.S4 i j k l) = 0 := rfl
@[simp] theorem proj_S22 (i j k : ι) : F.proj (F.S22 i j k) = 0 := rfl
@[simp] theorem proj_T13 (i l : ι) : F.proj (F.T13 i l) = 0 := rfl
@[simp] theorem proj_S2p (k l : ι) : F.proj (F.S2' k l) = 0 := rfl
@[simp] theorem proj_A4 (g : G) : F.proj (F.A4 g) = F.A4 g := rfl

@[simp] theorem cE3_proj (p : ι × ι × ι) (m : F.M3) : F.cE3 p (F.proj m) = 0 := rfl
@[simp] theorem cE12_proj (p : ι × ι) (m : F.M3) : F.cE12 p (F.proj m) = 0 := rfl
@[simp] theorem cS4_proj (a b c d : ι) (m : F.M3) : F.cS4 a b c d (F.proj m) = 0 := rfl
@[simp] theorem cS22_proj (a b c : ι) (m : F.M3) : F.cS22 a b c (F.proj m) = 0 := rfl
@[simp] theorem cT13_proj (a l : ι) (m : F.M3) : F.cT13 a l (F.proj m) = 0 := rfl
@[simp] theorem cS2'_proj (k l : ι) (m : F.M3) : F.cS2' k l (F.proj m) = 0 := rfl

theorem proj_S (z : G) : F.proj (F.S z) = F.S z := by
  simp only [S, nsum, map_sum, map_zsmul, zero_add, Φ3_single]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

@[simp] theorem cE3_S (p : ι × ι × ι) (z : G) : F.cE3 p (F.S z) = 0 := by
  rw [← proj_S]; rfl
@[simp] theorem cE12_S (p : ι × ι) (z : G) : F.cE12 p (F.S z) = 0 := by
  rw [← proj_S]; rfl
@[simp] theorem cS4_S (a b c d : ι) (z : G) : F.cS4 a b c d (F.S z) = 0 := by
  rw [← proj_S]; rfl
@[simp] theorem cS22_S (a b c : ι) (z : G) : F.cS22 a b c (F.S z) = 0 := by
  rw [← proj_S]; rfl
@[simp] theorem cT13_S (a l : ι) (z : G) : F.cT13 a l (F.S z) = 0 := by
  rw [← proj_S]; rfl
@[simp] theorem cS2'_S (k l : ι) (z : G) : F.cS2' k l (F.S z) = 0 := by
  rw [← proj_S]; rfl

/-! ## The symbol of a product, modulo (I) -/

variable [Fintype G] (hF : F.Class4)
include hF

/-- `S` as a map to `W₃* ⊕ W₄` modulo (I). -/
theorem mkQ_S_mul {z z' : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (hz' : z' ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    F.RI.mkQ (F.S (z * z')) = F.RI.mkQ (F.S z) + F.RI.mkQ (F.S z') := by
  rw [← map_add, ← sub_eq_zero, ← _root_.map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact S_mul hF hz hz'

theorem mkQ_S_zpow {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (k : ℤ) :
    F.RI.mkQ (F.S (z ^ k)) = k • F.RI.mkQ (F.S z) := by
  rw [← map_zsmul, ← sub_eq_zero, ← _root_.map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact S_zpow hF hz k

theorem mkQ_S_list_prod (L : List G) (hL : ∀ z ∈ L, z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    F.RI.mkQ (F.S L.prod) = (L.map fun z => F.RI.mkQ (F.S z)).sum := by
  induction L with
  | nil => simp [S_one]
  | cons a L ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      mkQ_S_mul hF (hL a List.mem_cons_self)
        (Subgroup.list_prod_mem _ (fun z hz => hL z (List.mem_cons_of_mem a hz))),
      ih fun z hz => hL z (List.mem_cons_of_mem a hz)]

theorem mkQ_S_ofFn {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    F.RI.mkQ (F.S (List.ofFn f).prod) = ∑ i, F.RI.mkQ (F.S (f i)) := by
  rw [mkQ_S_list_prod hF _ (fun z hz => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' f z).mp hz; exact hf i), List.map_ofFn, List.sum_ofFn]
  rfl

theorem ofFn_mem {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    (List.ofFn f).prod ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  Subgroup.list_prod_mem _ (fun z hz => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' f z).mp hz; exact hf i)

omit hF in
theorem S_ite (P : Prop) [Decidable P] (z : G) :
    F.S (if P then z else 1) = if P then F.S z else 0 := by
  split_ifs <;> simp [S_one]

/-- On `γ₄`, the symbol is the class in `A₄`. -/
theorem S_of_mem4 {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 3) : F.S z = F.A4 z :=
  nsum_zero_of_mem4 hF hz

end Frame

end TaharaProof

end GroupDimension
