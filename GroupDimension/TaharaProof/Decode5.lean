import GroupDimension.TaharaProof.Decode4

/-!
# Coefficients of an element of `R₅*` in Tahara's frame

`R₅*` is spanned by the relations (I)–(VII) indexed by Tahara's indices; (VI) with `i = j`
coincides with (V) and is dropped ([Tah81, §6]). An element of `R₅*` is a combination with
integer coefficients `p_l, u_{ij}, v_{ik}, v'_{ik}, w_{ijk}, w'_{ijk}, w''_{ijk}`.
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

namespace Frame

variable [Fintype G] {ι : Type*} [LinearOrder ι] [Fintype ι] {F : Frame G ι}

/-- (VI) with `i = j` is (V). -/
theorem gVI_diag (i k : ι) : F.gVI i i k = F.gV i i k := by
  simp only [gVI, gV, cc_self, tc_one_left, nsum_one, add_zero]

end Frame

section TFrame

variable [Fintype G] (h4 : lowerCentralSeries G 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

local notation "TF" => Tframe h4 hT hy4

/-- The relations (I)–(VII) indexed by Tahara's indices. -/
noncomputable def RT : Submodule ℤ (TF).M3 :=
  Submodule.span ℤ (Set.range fun l : Fin T.u => (TF).gI (ℓ3 l)) ⊔
  Submodule.span ℤ (Set.range fun p : Fin T.s × Fin T.s =>
    if p.1 < p.2 then (TF).gII (ℓ1 p.1) (ℓ1 p.2) else 0) ⊔
  Submodule.span ℤ (Set.range fun p : Fin T.s × Fin T.t => (TF).gIII (ℓ1 p.1) (ℓ2 p.2)) ⊔
  Submodule.span ℤ (Set.range fun p : Fin T.s × Fin T.t => (TF).gIV (ℓ1 p.1) (ℓ2 p.2)) ⊔
  Submodule.span ℤ (Set.range fun q : Fin T.s × Fin T.s × Fin T.s =>
    if q.1 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 then (TF).gV (ℓ1 q.1) (ℓ1 q.2.1) (ℓ1 q.2.2) else 0) ⊔
  Submodule.span ℤ (Set.range fun q : Fin T.s × Fin T.s × Fin T.s =>
    if q.1 < q.2.1 ∧ q.2.1 ≤ q.2.2 then (TF).gVI (ℓ1 q.1) (ℓ1 q.2.1) (ℓ1 q.2.2) else 0) ⊔
  Submodule.span ℤ (Set.range fun q : Fin T.s × Fin T.s × Fin T.s =>
    if q.1 ≤ q.2.1 ∧ q.2.1 < q.2.2 then (TF).gVII (ℓ1 q.1) (ℓ1 q.2.1) (ℓ1 q.2.2) else 0)

theorem w_TIdx (p : TIdx T.s T.t T.u v) :
    ((TF).w p = 1 → ∃ i, p = ℓ1 i) ∧ ((TF).w p = 2 → ∃ k, p = ℓ2 k) ∧
      ((TF).w p = 3 → ∃ l, p = ℓ3 l) := by
  rcases TIdx_cases p with ⟨i, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩ | ⟨q, rfl⟩ <;> simp

theorem memRT_A {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun l : Fin T.u => (TF).gI (ℓ3 l))) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  exact h

theorem memRT_B {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun p : Fin T.s × Fin T.s =>
      if p.1 < p.2 then (TF).gII (ℓ1 p.1) (ℓ1 p.2) else 0)) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact h

theorem memRT_C {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun p : Fin T.s × Fin T.t => (TF).gIII (ℓ1 p.1) (ℓ2 p.2))) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact h

theorem memRT_D {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun p : Fin T.s × Fin T.t => (TF).gIV (ℓ1 p.1) (ℓ2 p.2))) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact h

theorem memRT_E {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun q : Fin T.s × Fin T.s × Fin T.s =>
      if q.1 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2 then (TF).gV (ℓ1 q.1) (ℓ1 q.2.1) (ℓ1 q.2.2) else 0)) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact h

theorem memRT_F {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun q : Fin T.s × Fin T.s × Fin T.s =>
      if q.1 < q.2.1 ∧ q.2.1 ≤ q.2.2 then (TF).gVI (ℓ1 q.1) (ℓ1 q.2.1) (ℓ1 q.2.2) else 0)) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_left
  apply Submodule.mem_sup_right
  exact h

theorem memRT_G {x : (TF).M3}
    (h : x ∈ Submodule.span ℤ (Set.range fun q : Fin T.s × Fin T.s × Fin T.s =>
      if q.1 ≤ q.2.1 ∧ q.2.1 < q.2.2 then (TF).gVII (ℓ1 q.1) (ℓ1 q.2.1) (ℓ1 q.2.2) else 0)) :
    x ∈ RT h4 hT hy4 := by
  unfold RT
  apply Submodule.mem_sup_right
  exact h

/-- `R₅* ⊆` the span of the relations in Tahara's indices. -/
theorem R5_le_RT : (TF).R5 ≤ RT h4 hT hy4 := by
  have hs : ∀ {S : Set (TF).M3} {N : Submodule ℤ (TF).M3}, (∀ x ∈ S, x ∈ N) →
      Submodule.span ℤ S ≤ N := fun h => Submodule.span_le.mpr h
  unfold Frame.R5
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · refine hs ?_
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨l, rfl⟩ := (w_TIdx h4 hT hy4 p).2.2 hp
    exact memRT_A h4 hT hy4 (Submodule.subset_span ⟨l, rfl⟩)
  · refine hs ?_
    rintro _ ⟨⟨⟨p1, p2⟩, hp1, hp2, hp⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (w_TIdx h4 hT hy4 p1).1 hp1
    obtain ⟨j, rfl⟩ := (w_TIdx h4 hT hy4 p2).1 hp2
    have hij : i < j := ℓ1_lt_ℓ1.mp hp
    exact memRT_B h4 hT hy4 (Submodule.subset_span ⟨(i, j), by simp [hij]⟩)
  · refine hs ?_
    rintro _ ⟨⟨⟨p1, p2⟩, hp1, hp2⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (w_TIdx h4 hT hy4 p1).1 hp1
    obtain ⟨k, rfl⟩ := (w_TIdx h4 hT hy4 p2).2.1 hp2
    exact memRT_C h4 hT hy4 (Submodule.subset_span ⟨(i, k), rfl⟩)
  · refine hs ?_
    rintro _ ⟨⟨⟨p1, p2⟩, hp1, hp2⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (w_TIdx h4 hT hy4 p1).1 hp1
    obtain ⟨k, rfl⟩ := (w_TIdx h4 hT hy4 p2).2.1 hp2
    exact memRT_D h4 hT hy4 (Submodule.subset_span ⟨(i, k), rfl⟩)
  · refine hs ?_
    rintro _ ⟨⟨⟨p1, p2, p3⟩, hp1, hp2, hp3, h12, h23⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (w_TIdx h4 hT hy4 p1).1 hp1
    obtain ⟨j, rfl⟩ := (w_TIdx h4 hT hy4 p2).1 hp2
    obtain ⟨k, rfl⟩ := (w_TIdx h4 hT hy4 p3).1 hp3
    exact memRT_E h4 hT hy4 (Submodule.subset_span ⟨(i, j, k), by
      simp [ℓ1_le_ℓ1.mp h12, ℓ1_le_ℓ1.mp h23]⟩)
  · refine hs ?_
    rintro _ ⟨⟨⟨p1, p2, p3⟩, hp1, hp2, hp3, h12, h23⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (w_TIdx h4 hT hy4 p1).1 hp1
    obtain ⟨j, rfl⟩ := (w_TIdx h4 hT hy4 p2).1 hp2
    obtain ⟨k, rfl⟩ := (w_TIdx h4 hT hy4 p3).1 hp3
    have hij := ℓ1_le_ℓ1.mp h12
    have hjk := ℓ1_le_ℓ1.mp h23
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact memRT_F h4 hT hy4 (Submodule.subset_span ⟨(i, j, k), by simp [hij, hjk]⟩)
    · simp only
      rw [Frame.gVI_diag]
      exact memRT_E h4 hT hy4 (Submodule.subset_span ⟨(i, i, k), by simp [hjk]⟩)
  · refine hs ?_
    rintro _ ⟨⟨⟨p1, p2, p3⟩, hp1, hp2, hp3, h12, h23⟩, rfl⟩
    obtain ⟨i, rfl⟩ := (w_TIdx h4 hT hy4 p1).1 hp1
    obtain ⟨j, rfl⟩ := (w_TIdx h4 hT hy4 p2).1 hp2
    obtain ⟨k, rfl⟩ := (w_TIdx h4 hT hy4 p3).1 hp3
    exact memRT_G h4 hT hy4 (Submodule.subset_span ⟨(i, j, k), by
      simp [ℓ1_le_ℓ1.mp h12, ℓ1_lt_ℓ1.mp h23]⟩)

end TFrame

end TaharaProof

end GroupDimension
