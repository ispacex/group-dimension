module

public import GroupDimension.TaharaProof.Decode9

@[expose] public section

/-!
# Tahara's conditions (A)–(F) for an element of `D₅`

If the symbol of `g ∈ D₅ ∩ γ₃` is the combination `combx` of the relations with coefficients
`p, U, V, V', W5, W6, W7`, the family `τ = (-U, V, V', W5, W6, W7)` satisfies Tahara's conditions
(A)–(F): each condition is the vanishing of one coordinate of `combx` (the symbol has no
coordinates outside `A₃ ⊕ A₄`).
-/

namespace GroupDimension

namespace TaharaProof

open MonoidAlgebra Tahara ExpThree ClassFour

variable {G : Type*} [Group G]

/-- Tahara's family attached to the coefficients. -/
def tau {s t : ℕ} (U : Fin s × Fin s → ℤ) (V V' : Fin s × Fin t → ℤ)
    (W5 W6 W7 : Fin s × Fin s × Fin s → ℤ) : Coeffs s t where
  u i j := -U (i, j)
  v i k := V (i, k)
  v' i k := V' (i, k)
  w i j k := W5 (i, j, k)
  w' i j k := W6 (i, j, k)
  w'' i j k := W7 (i, j, k)

theorem sum_ite_neg {α : Type*} [Fintype α] {R : Type*} [AddCommGroup R] (P : α → Prop)
    [DecidablePred P] (f : α → R) :
    (∑ h, if P h then -f h else 0) = -∑ h, if P h then f h else 0 := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun h _ => by split_ifs <;> simp

theorem lt_and_le_false {α : Type*} [LinearOrder α] (a b : α) : (a < b ∧ b ≤ a) ↔ False :=
  ⟨fun h => absurd (lt_of_lt_of_le h.1 h.2) (lt_irrefl a), False.elim⟩

theorem le_and_lt_false {α : Type*} [LinearOrder α] (a b : α) : (a ≤ b ∧ b < a) ↔ False :=
  ⟨fun h => absurd (lt_of_le_of_lt h.1 h.2) (lt_irrefl a), False.elim⟩

section TFrame

variable [Fintype G] (h4 : (⊤ : Subgroup G).lowerCentralSeries 4 = ⊥) {T : Data G} (hT : T.Valid)
  {v : ℕ} {y4 : Fin v → G} {o4 : Fin v → ℕ} (hy4 : LayerNF 3 y4 o4)

local notation "TF" => Tframe h4 hT hy4

attribute [-simp] Tframe_o1 Tframe_o2 Tframe_o3 Tframe_o4

variable {p : Fin T.u → ℤ} {U : Fin T.s × Fin T.s → ℤ} {V V' : Fin T.s × Fin T.t → ℤ}
  {W5 W6 W7 : Fin T.s × Fin T.s × Fin T.s → ℤ} {g : G}

theorem hE3 (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    (a b c : Fin T.s) :
    (TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c) (sII h4 hT hy4 U) +
      (if a ≤ b ∧ b ≤ c then -(W5 (a, b, c) * T.d a) else 0) +
      (if a < b ∧ b ≤ c then -(W6 (a, b, c) * T.d b) else 0) +
      (if a ≤ b ∧ b < c then -(W7 (a, b, c) * T.d c) else 0) = 0 := by
  have h := congrArg ((TF).cE3 (ℓ1 a, ℓ1 b, ℓ1 c)) hS
  rw [Frame.cE3_S, combx_eq] at h
  simp only [map_add, cE3_sI, cE3_sIII, cE3_sIV, cE3_sV, cE3_sVI, cE3_sVII] at h
  linear_combination -h

theorem hE12 (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    (i : Fin T.s) (k : Fin T.t) :
    (∑ h, if i < h then U (i, h) * T.b h k else 0) -
      (∑ h, if h < i then U (h, i) * (T.q h i * T.b h k) else 0) -
      V (i, k) * T.d i - V' (i, k) * T.e k = 0 := by
  have h := congrArg ((TF).cE12 (ℓ1 i, ℓ2 k)) hS
  rw [Frame.cE12_S, combx_eq] at h
  simp only [map_add, cE12_sI, cE12_sII, cE12_sIII, cE12_sIV, cE12_sV, cE12_sVI,
    cE12_sVII] at h
  linear_combination -h

theorem hS4 (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    (a b c d : Fin T.s) :
    (TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d) (sII h4 hT hy4 U) +
      (if a = b ∧ a ≤ c ∧ c ≤ d then -((W5 (a, c, d) * ((T.d a).choose 2 : ℤ) : ℤ) : ZMod _)
        else 0) +
      (if a < b ∧ b = c ∧ c ≤ d then -((W6 (a, b, d) * ((T.d b).choose 2 : ℤ) : ℤ) : ZMod _)
        else 0) +
      (if a ≤ b ∧ b < c ∧ c = d then -((W7 (a, b, c) * ((T.d c).choose 2 : ℤ) : ℤ) : ZMod _)
        else 0) = 0 := by
  have h := congrArg ((TF).cS4 (ℓ1 a) (ℓ1 b) (ℓ1 c) (ℓ1 d)) hS
  rw [Frame.cS4_S, combx_eq] at h
  simp only [map_add, cS4_sI, cS4_sIII, cS4_sIV, cS4_sV, cS4_sVI, cS4_sVII] at h
  linear_combination -h

theorem hS22 (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    (a b : Fin T.s) (m : Fin T.t) :
    (if a = b then -((V (a, m) * ((T.d a).choose 2 : ℤ) : ℤ) : ZMod _) else 0) +
      (∑ h, if h ≤ a ∧ a ≤ b then ((W5 (h, a, b) * T.b h m : ℤ) : ZMod _) else 0) +
      (∑ h, if a < h ∧ h ≤ b then ((W6 (a, h, b) * T.b h m : ℤ) : ZMod _) else 0) +
      (∑ h, if a ≤ b ∧ b < h then ((W7 (a, b, h) * T.b h m : ℤ) : ZMod _) else 0) =
        (0 : ZMod (Nat.gcd ((TF).o (ℓ1 a)) ((TF).o (ℓ2 m)))) := by
  have h := congrArg ((TF).cS22 (ℓ1 a) (ℓ1 b) (ℓ2 m)) hS
  rw [Frame.cS22_S, combx_eq] at h
  simp only [map_add, cS22_sI, cS22_sII, cS22_sIII, cS22_sIV, cS22_sV, cS22_sVI,
    cS22_sVII] at h
  linear_combination -h

theorem hT13 (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    (i : Fin T.s) (l : Fin T.u) :
    ((∑ h, if i < h then ((U (i, h) * T.c h l : ℤ) : ZMod _) else 0) -
      ∑ h, if h < i then ((U (h, i) * (T.q h i * (T.c h l + T.α h i l)) : ℤ) : ZMod _)
        else 0) +
      (∑ k, ((V' (i, k) * T.dd k l : ℤ) : ZMod _)) +
      ((∑ g, ∑ h, if g ≤ i ∧ i ≤ h then ((W5 (g, i, h) * T.α g h l : ℤ) : ZMod _) else 0) +
        ∑ g, ∑ h, if g ≤ h ∧ h ≤ i then ((W5 (g, h, i) * T.α g h l : ℤ) : ZMod _) else 0) +
      (∑ g, ∑ h, if i < g ∧ g ≤ h then ((W6 (i, g, h) * T.α g h l : ℤ) : ZMod _) else 0) =
        (0 : ZMod (Nat.gcd ((TF).o (ℓ1 i)) ((TF).o (ℓ3 l)))) := by
  have h := congrArg ((TF).cT13 (ℓ1 i) (ℓ3 l)) hS
  rw [Frame.cT13_S, combx_eq] at h
  simp only [map_add, cT13_sI, cT13_sII, cT13_sIII, cT13_sIV, cT13_sV, cT13_sVI,
    cT13_sVII] at h
  linear_combination -h

theorem hS2'_kk (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    (k : Fin T.t) :
    ∑ i, ((V (i, k) * T.b i k : ℤ) : ZMod ((TF).o (ℓ2 k))) = 0 := by
  have h := congrArg ((TF).cS2' (ℓ2 k) (ℓ2 k)) hS
  rw [Frame.cS2'_S, combx_eq] at h
  simp only [map_add, cS2'_sI, cS2'_sII, cS2'_sIII_kk, cS2'_sIV, cS2'_sV, cS2'_sVI,
    cS2'_sVII] at h
  linear_combination -h

theorem hS2'_km (hS : (Tframe h4 hT hy4).S g = combx h4 hT hy4 p U V V' W5 W6 W7)
    {k m : Fin T.t} (hkm : k < m) :
    (∑ i, ((V (i, k) * T.b i m : ℤ) : ZMod ((TF).o (ℓ2 k)))) +
      ∑ i, ((V (i, m) * T.b i k : ℤ) : ZMod ((TF).o (ℓ2 k))) = 0 := by
  have h := congrArg ((TF).cS2' (ℓ2 k) (ℓ2 m)) hS
  rw [Frame.cS2'_S, combx_eq] at h
  simp only [map_add, cS2'_sI, cS2'_sII, cS2'_sIII_km h4 hT hy4 V k m hkm, cS2'_sIV, cS2'_sV,
    cS2'_sVI, cS2'_sVII] at h
  linear_combination -h

end TFrame

end TaharaProof

end GroupDimension
