module

public import GroupDimension.Jennings.Lazard
public import GroupDimension.ClassFour

@[expose] public section

/-!
# `S₅ ≤ Q⁸ γ₂⁴ γ₃²` for groups of class `≤ 3` (`p = 2`)

For a group `G` with `γ₄(G) = 1` the Lazard series for `p = 2` satisfies
`S₂ ≤ F₂ = γ₂ G²`, `S₃ ≤ F₃ = G⁴ γ₂² γ₃`, `S₄ ≤ F₄ = G⁴ γ₂² γ₃²` and
`S₅ ≤ F₅ = G⁸ γ₂⁴ γ₃²` (`lazard_five_le`), and `F₅` is the Jennings product
`∏_{i 2^j ≥ 5} γ_i^{2^j}` of `Candidate.lean` (`F₅_le_jennings`). Here `F_k` is the Jennings product
`∏_{i 2^j ≥ k} γ_i^{2^j}` in class `≤ 3`.

The proof checks the generators of each piece. Everything rests on `γ₃` being central:
`[g^n, h] = [g, h]^n [g, [g, h]]^{n(n-1)/2}` (`commutator_pow_left`), and `[c^n, g] = [c, g]^n` for
`c ∈ γ₂`. Products and squares are handled modulo a normal subgroup `N`: `Cent N B` is the subgroup
of the `a` with `[a, B] ≤ N`, and `Sq N A m` the subgroup of the `a ∈ A` with `a^m ∈ N` (when
`[A, A] ≤ N`).
-/

namespace GroupDimension

namespace ClassThree

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## Commutators modulo a normal subgroup -/

section Modulo

variable (N : Subgroup G) [N.Normal]

theorem mem_iff_mk'_eq_one (x : G) : x ∈ N ↔ QuotientGroup.mk' N x = 1 :=
  (QuotientGroup.eq_one_iff x).symm

theorem commutator_mem_iff (a b : G) :
    ⁅a, b⁆ ∈ N ↔ QuotientGroup.mk' N a * QuotientGroup.mk' N b =
      QuotientGroup.mk' N b * QuotientGroup.mk' N a := by
  rw [mem_iff_mk'_eq_one, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]

/-- The `a` with `[a, b] ∈ N` for all `b ∈ B`. -/
def Cent (B : Subgroup G) : Subgroup G :=
  (Subgroup.centralizer ((B.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))).comap
    (QuotientGroup.mk' N)

theorem mem_Cent {B : Subgroup G} {a : G} : a ∈ Cent N B ↔ ∀ b ∈ B, ⁅a, b⁆ ∈ N := by
  simp only [Cent, mem_comap, mem_centralizer_iff, SetLike.mem_coe, mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, commutator_mem_iff]
  exact forall₂_congr fun b _ => eq_comm

theorem commutator_le_iff {A B : Subgroup G} : ⁅A, B⁆ ≤ N ↔ A ≤ Cent N B := by
  rw [commutator_le]
  exact ⟨fun h a ha => (mem_Cent N).mpr fun b hb => h a ha b hb,
    fun h a ha b hb => (mem_Cent N).mp (h ha) b hb⟩

/-- The `b` with `[b, x] ∈ N`. -/
def Cx (x : G) : Subgroup G :=
  (Subgroup.centralizer ({QuotientGroup.mk' N x} : Set (G ⧸ N))).comap (QuotientGroup.mk' N)

theorem mem_Cx {x b : G} : b ∈ Cx N x ↔ ⁅b, x⁆ ∈ N := by
  simp only [Cx, mem_comap, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    commutator_mem_iff]
  exact eq_comm

theorem mem_Cent_iff_le {B : Subgroup G} {x : G} : x ∈ Cent N B ↔ B ≤ Cx N x := by
  rw [mem_Cent]
  refine ⟨fun h b hb => (mem_Cx N).mpr ?_, fun h b hb => ?_⟩
  · rw [← commutatorElement_inv]; exact inv_mem (h b hb)
  · have := (mem_Cx N).mp (h hb)
    rw [← commutatorElement_inv] at this
    simpa using inv_mem this

/-- The `a ∈ A` with `a^m ∈ N`, a subgroup when `[A, A] ≤ N`. -/
def Sq (A : Subgroup G) (hA : ⁅A, A⁆ ≤ N) (m : ℕ) : Subgroup G where
  carrier := {a | a ∈ A ∧ a ^ m ∈ N}
  one_mem' := ⟨one_mem _, by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hc : Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) :=
      (commutator_mem_iff N a b).mp (hA (commutator_mem_commutator ha hb))
    rw [mem_iff_mk'_eq_one] at ha' hb' ⊢
    rw [map_pow, map_mul, hc.mul_pow, ← map_pow, ← map_pow, ha', hb', one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨inv_mem ha, by rw [inv_pow]; exact inv_mem ha'⟩

theorem powSubgroup_le_of {A : Subgroup G} (hA : ⁅A, A⁆ ≤ N) {m : ℕ} (h : A ≤ Sq N A hA m) :
    powSubgroup A m ≤ N :=
  (closure_le N).mpr fun _ ⟨_, ha, hg⟩ => hg ▸ (h ha).2

end Modulo

/-! ## Commutator identities -/

theorem commutator_central_left {z : G} (hz : z ∈ center G) (g : G) : ⁅z, g⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz g).symm

theorem commutator_central_right {z : G} (hz : z ∈ center G) (g : G) : ⁅g, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz g)

/-- `[g^n, h] = [g, h]^n [g, [g, h]]^{n(n-1)/2}` when `[g, [g, h]]` is central. -/
theorem commutator_pow_left {g h : G} (hd : ⁅g, ⁅g, h⁆⁆ ∈ center G) :
    ∀ n : ℕ, ⁅g ^ n, h⁆ = ⁅g, h⁆ ^ n * ⁅g, ⁅g, h⁆⁆ ^ n.choose 2
  | 0 => by simp
  | n + 1 => by
    set c := ⁅g, h⁆ with hc
    set d := ⁅g, c⁆ with hdd
    have hcent : ∀ x : G, Commute d x := fun x => (mem_center_iff.mp hd x).symm
    have h1 : ⁅g ^ (n + 1), h⁆ = g * ⁅g ^ n, h⁆ * g⁻¹ * c := by
      rw [pow_succ', hc]; simp only [commutatorElement_def]; group
    have hdc : g * c * g⁻¹ = d * c := by rw [hdd, commutatorElement_def]; group
    have h2 : g * c ^ n * g⁻¹ = d ^ n * c ^ n := by
      rw [← conj_pow, hdc, (hcent c).mul_pow]
    have h3 : ∀ k : ℕ, g * d ^ k * g⁻¹ = d ^ k := fun k => by
      rw [← ((hcent g).pow_left k).eq]; group
    rw [h1, commutator_pow_left hd n, Nat.choose_succ_succ, Nat.choose_one_right]
    calc g * (c ^ n * d ^ n.choose 2) * g⁻¹ * c
        = (g * c ^ n * g⁻¹) * (g * d ^ n.choose 2 * g⁻¹) * c := by group
      _ = d ^ n * c ^ n * d ^ n.choose 2 * c := by rw [h2, h3]
      _ = c ^ n * (d ^ n * d ^ n.choose 2) * c := by
          rw [((hcent (c ^ n)).pow_left n).eq]; simp only [mul_assoc]
      _ = c ^ n * (c * (d ^ n * d ^ n.choose 2)) := by
          rw [mul_assoc, (((hcent c).pow_left n).mul_left ((hcent c).pow_left _)).eq]
      _ = c ^ (n + 1) * d ^ (n + n.choose 2) := by rw [pow_succ c n, pow_add d n]; simp only [mul_assoc]

/-- `[g, x⁻¹] = [g, x]⁻¹` when `[g, x]` is central. -/
theorem commutator_inv_right {g x : G} (h : ⁅g, x⁆ ∈ center G) : ⁅g, x⁻¹⁆ = ⁅g, x⁆⁻¹ := by
  have : ⁅g, x⁻¹⁆ = x⁻¹ * ⁅g, x⁆⁻¹ * x := by simp only [commutatorElement_def]; group
  rw [this, mem_center_iff.mp (inv_mem h) x⁻¹]
  group

/-- `[g, x e] = [g, x]` when `e` is central. -/
theorem commutator_mul_central {g x e : G} (he : e ∈ center G) : ⁅g, x * e⁆ = ⁅g, x⁆ := by
  have hc : e * g⁻¹ = g⁻¹ * e := (mem_center_iff.mp he g⁻¹).symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (x * e) * g⁻¹ * (e⁻¹ * x⁻¹) = g * x * (e * g⁻¹) * e⁻¹ * x⁻¹ := by group
    _ = g * x * g⁻¹ * x⁻¹ := by rw [hc]; group

/-! ## Groups of class `≤ 3` -/

section ClassThree

variable (h4 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥)
include h4

omit h4 in
theorem lcs_two_eq : (⊤ : Subgroup G).lowerCentralSeries 2 = ⁅(⊤ : Subgroup G).lowerCentralSeries 1, ⊤⁆ := Subgroup.lowerCentralSeries_succ ⊤ 1

omit h4 in
theorem comm_mem_lcs_one (g h : G) : ⁅g, h⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  rw [Subgroup.top_lowerCentralSeries_one, _root_.commutator_def]
  exact commutator_mem_commutator (mem_top g) (mem_top h)

omit h4 in
theorem comm_mem_lcs_two {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (g : G) :
    ⁅c, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  rw [Subgroup.lowerCentralSeries_succ ⊤ 1]; exact commutator_mem_commutator hc (mem_top g)

omit h4 in
theorem comm_mem_lcs_two' {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (g : G) :
    ⁅g, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  rw [← commutatorElement_inv]; exact inv_mem (comm_mem_lcs_two hc g)

theorem mem_center_of_lcs_two {w : G} (hw : w ∈ (⊤ : Subgroup G).lowerCentralSeries 2) : w ∈ center G := by
  rw [mem_center_iff]
  intro g
  have e3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⁅(⊤ : Subgroup G).lowerCentralSeries 2, ⊤⁆ := Subgroup.lowerCentralSeries_succ ⊤ 2
  have : ⁅w, g⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    rw [e3]; exact commutator_mem_commutator hw (mem_top g)
  rw [h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this.symm

theorem comm_lcs_one_eq_one {c c' : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hc' : c' ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : ⁅c, c'⁆ = 1 := by
  have := commutator_lcs_le (G := G) 1 1 (commutator_mem_commutator hc hc')
  rwa [show 1 + 1 + 1 = 3 from rfl, h4, mem_bot] at this

/-- `[g^n, h] = [g, h]^n [g, [g, h]]^{n(n-1)/2}`. -/
theorem comm_pow_left (g h : G) (n : ℕ) :
    ⁅g ^ n, h⁆ = ⁅g, h⁆ ^ n * ⁅g, ⁅g, h⁆⁆ ^ n.choose 2 :=
  commutator_pow_left (mem_center_of_lcs_two h4 (comm_mem_lcs_two' (comm_mem_lcs_one g h) g)) n

/-- `[c^n, g] = [c, g]^n` for `c ∈ γ₂`. -/
theorem comm_pow_left_of_lcs_one {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (g : G) (n : ℕ) :
    ⁅c ^ n, g⁆ = ⁅c, g⁆ ^ n := by
  have hz := mem_center_of_lcs_two h4 (comm_mem_lcs_two hc g)
  rw [commutator_pow_left (by rw [commutator_central_right hz]; exact one_mem _) n,
    commutator_central_right hz, one_pow, mul_one]

/-- `[g^n, c] = [g, c]^n` for `c ∈ γ₂`. -/
theorem comm_pow_left_lcs_one {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (g : G) (n : ℕ) :
    ⁅g ^ n, c⁆ = ⁅g, c⁆ ^ n := by
  have hz := mem_center_of_lcs_two h4 (comm_mem_lcs_two' hc g)
  rw [commutator_pow_left (by rw [commutator_central_right hz]; exact one_mem _) n,
    commutator_central_right hz, one_pow, mul_one]

/-- `[g, c^n] = [g, c]^n` for `c ∈ γ₂`. -/
theorem comm_pow_right_of_lcs_one {c : G} (hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (g : G) (n : ℕ) :
    ⁅g, c ^ n⁆ = ⁅g, c⁆ ^ n := by
  rw [← commutatorElement_inv, comm_pow_left_of_lcs_one h4 hc g n, ← inv_pow,
    commutatorElement_inv]

end ClassThree

theorem mem_Sq {N : Subgroup G} [N.Normal] {A : Subgroup G} {hA : ⁅A, A⁆ ≤ N} {m : ℕ} {x : G} :
    x ∈ Sq N A hA m ↔ x ∈ A ∧ x ^ m ∈ N := Iff.rfl

theorem pow_mul_mem {H : Subgroup G} {x : G} (hx : x ∈ H) (a m : ℕ) :
    x ^ (a * m) ∈ powSubgroup H m := by
  rw [pow_mul]; exact pow_mem_powSubgroup (pow_mem hx a) m

/-! ## The products `F₂, …, F₅` -/

variable (G) in
/-- `F₂ = γ₂ G²`. -/
def F2 : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries 1 ⊔ powSubgroup ⊤ 2

variable (G) in
/-- `F₃ = G⁴ γ₂² γ₃`. -/
def F3 : Subgroup G :=
  powSubgroup ⊤ 4 ⊔ powSubgroup ((⊤ : Subgroup G).lowerCentralSeries 1) 2 ⊔ (⊤ : Subgroup G).lowerCentralSeries 2

variable (G) in
/-- `F₄ = G⁴ γ₂² γ₃²`. -/
def F4 : Subgroup G :=
  powSubgroup ⊤ 4 ⊔ powSubgroup ((⊤ : Subgroup G).lowerCentralSeries 1) 2 ⊔
    powSubgroup ((⊤ : Subgroup G).lowerCentralSeries 2) 2

variable (G) in
/-- `F₅ = G⁸ γ₂⁴ γ₃²`. -/
def F5 : Subgroup G :=
  powSubgroup ⊤ 8 ⊔ powSubgroup ((⊤ : Subgroup G).lowerCentralSeries 1) 4 ⊔
    powSubgroup ((⊤ : Subgroup G).lowerCentralSeries 2) 2

instance (m : ℕ) : (powSubgroup (⊤ : Subgroup G) m).Normal := powSubgroup_normal _ _
instance instNormalPowSubgroupLowerCentralSeries (k m : ℕ) :
    (powSubgroup ((⊤ : Subgroup G).lowerCentralSeries k) m).Normal := powSubgroup_normal _ _
instance : (F2 G).Normal := by unfold F2; infer_instance
instance : (F3 G).Normal := by unfold F3; infer_instance
instance : (F4 G).Normal := by unfold F4; infer_instance
instance : (F5 G).Normal := by unfold F5; infer_instance

theorem F3_le_F2 : F3 G ≤ F2 G := by
  refine sup_le (sup_le ((closure_le _).mpr ?_) ((closure_le _).mpr ?_)) fun z hz =>
    mem_sup_left ((Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num) hz)
  · rintro _ ⟨g, -, rfl⟩; exact mem_sup_right (pow_mul_mem (mem_top g) 2 2)
  · rintro _ ⟨c, hc, rfl⟩; exact mem_sup_left (pow_mem hc 2)

theorem F5_le_jennings : F5 G ≤ jennings 2 G 5 := by
  have t : ∀ i j, 5 ≤ (i + 1) * 2 ^ j →
      powSubgroup ((⊤ : Subgroup G).lowerCentralSeries i) (2 ^ j) ≤ jennings 2 G 5 :=
    fun i j h => le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h le_rfl))
  refine sup_le (sup_le ?_ (t 1 2 (by norm_num))) (t 2 1 (by norm_num))
  have := t 0 3 (by norm_num)
  rwa [Subgroup.lowerCentralSeries_zero] at this

section Inclusions

variable (h4 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥)
include h4

/-- `[F₂, G] ≤ F₃`. -/
theorem comm_F2_top : ⁅F2 G, ⊤⁆ ≤ F3 G := by
  rw [commutator_le_iff]
  refine sup_le (fun c hc => (mem_Cent _).mpr fun g _ => mem_sup_right (comm_mem_lcs_two hc g))
    ((closure_le _).mpr ?_)
  rintro _ ⟨g, -, rfl⟩
  refine (mem_Cent _).mpr fun h _ => ?_
  have e := comm_pow_left h4 g h 2
  rw [show Nat.choose 2 2 = 1 from rfl, pow_one] at e
  rw [e]
  exact mul_mem (mem_sup_left (mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_one g h) 2)))
    (mem_sup_right (comm_mem_lcs_two' (comm_mem_lcs_one g h) g))

/-- `F₂² ≤ F₃`. -/
theorem pow_F2_le_F3 : powSubgroup (F2 G) 2 ≤ F3 G := by
  have hA : ⁅F2 G, F2 G⁆ ≤ F3 G := (commutator_mono le_rfl le_top).trans (comm_F2_top h4)
  refine powSubgroup_le_of _ hA (sup_le (fun c hc => mem_Sq.mpr ⟨mem_sup_left hc,
    mem_sup_left (mem_sup_right (pow_mem_powSubgroup hc 2))⟩) ((closure_le _).mpr ?_))
  rintro _ ⟨g, -, rfl⟩
  refine mem_Sq.mpr ⟨mem_sup_right (pow_mem_powSubgroup (mem_top g) 2), ?_⟩
  rw [← pow_mul]
  exact mem_sup_left (mem_sup_left (pow_mem_powSubgroup (mem_top g) 4))

/-- `[F₃, G] ≤ F₄`. -/
theorem comm_F3_top : ⁅F3 G, ⊤⁆ ≤ F4 G := by
  rw [commutator_le_iff]
  refine sup_le (sup_le ((closure_le _).mpr ?_) ((closure_le _).mpr ?_)) fun z hz => ?_
  · rintro _ ⟨g, -, rfl⟩
    refine (mem_Cent _).mpr fun h _ => ?_
    rw [comm_pow_left h4 g h 4, show Nat.choose 4 2 = 3 * 2 from rfl]
    exact mul_mem (mem_sup_left (mem_sup_right (pow_mul_mem (comm_mem_lcs_one g h) 2 2)))
      (mem_sup_right (pow_mul_mem (comm_mem_lcs_two' (comm_mem_lcs_one g h) g) 3 2))
  · rintro _ ⟨c, hc, rfl⟩
    refine (mem_Cent _).mpr fun h _ => ?_
    rw [comm_pow_left_of_lcs_one h4 hc h 2]
    exact mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_two hc h) 2)
  · refine (mem_Cent _).mpr fun h _ => ?_
    rw [commutator_central_left (mem_center_of_lcs_two h4 hz)]
    exact one_mem _

/-- `[F₂, F₂] ≤ F₄`. -/
theorem comm_F2_F2 : ⁅F2 G, F2 G⁆ ≤ F4 G := by
  rw [commutator_le_iff]
  refine sup_le (fun c hc => (mem_Cent_iff_le _).mpr (sup_le (fun c' hc' => ?_)
    ((closure_le _).mpr ?_))) ((closure_le _).mpr ?_)
  · rw [mem_Cx, comm_lcs_one_eq_one h4 hc' hc]; exact one_mem _
  · rintro _ ⟨h, -, rfl⟩
    rw [SetLike.mem_coe, mem_Cx, comm_pow_left_lcs_one h4 hc h 2]
    exact mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_two' hc h) 2)
  · rintro _ ⟨g, -, rfl⟩
    refine (mem_Cent_iff_le _).mpr (sup_le (fun c' hc' => ?_) ((closure_le _).mpr ?_))
    · rw [mem_Cx, ← commutatorElement_inv, comm_pow_left_lcs_one h4 hc' g 2]
      exact inv_mem (mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_two' hc' g) 2))
    · rintro _ ⟨h, -, rfl⟩
      rw [SetLike.mem_coe, mem_Cx, comm_pow_left h4 h (g ^ 2) 2,
        show Nat.choose 2 2 = 1 from rfl, pow_one]
      refine mul_mem (mem_sup_left (mem_sup_right
        (pow_mem_powSubgroup (comm_mem_lcs_one h (g ^ 2)) 2))) ?_
      -- `[h, [h, g²]] = [h, [g, h]²]⁻¹`
      set c := ⁅g, h⁆ with hcdef
      have hc : c ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := comm_mem_lcs_one g h
      have he : ⁅g, c⁆ ∈ center G := mem_center_of_lcs_two h4 (comm_mem_lcs_two' hc g)
      have hu : ⁅h, g ^ 2⁆ = (c ^ 2 * ⁅g, c⁆)⁻¹ := by
        rw [← commutatorElement_inv, comm_pow_left h4 g h 2, show Nat.choose 2 2 = 1 from rfl,
          pow_one]
      have hx : c ^ 2 * ⁅g, c⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
        mul_mem (pow_mem hc 2) ((Subgroup.lowerCentralSeries_antitone ⊤) (by norm_num)
          (comm_mem_lcs_two' hc g))
      rw [hu, commutator_inv_right (mem_center_of_lcs_two h4 (comm_mem_lcs_two' hx h)),
        commutator_mul_central he, comm_pow_right_of_lcs_one h4 hc h 2]
      exact inv_mem (mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_two' hc h) 2))

/-- `F₂² ≤ F₄`. -/
theorem pow_F2_le_F4 : powSubgroup (F2 G) 2 ≤ F4 G := by
  refine powSubgroup_le_of _ (comm_F2_F2 h4) (sup_le (fun c hc => mem_Sq.mpr ⟨mem_sup_left hc,
    mem_sup_left (mem_sup_right (pow_mem_powSubgroup hc 2))⟩) ((closure_le _).mpr ?_))
  rintro _ ⟨g, -, rfl⟩
  refine mem_Sq.mpr ⟨mem_sup_right (pow_mem_powSubgroup (mem_top g) 2), ?_⟩
  rw [← pow_mul]
  exact mem_sup_left (mem_sup_left (pow_mem_powSubgroup (mem_top g) 4))

/-- `[F₄, G] ≤ F₅`. -/
theorem comm_F4_top : ⁅F4 G, ⊤⁆ ≤ F5 G := by
  rw [commutator_le_iff]
  refine sup_le (sup_le ((closure_le _).mpr ?_) ((closure_le _).mpr ?_)) ((closure_le _).mpr ?_)
  · rintro _ ⟨g, -, rfl⟩
    refine (mem_Cent _).mpr fun h _ => ?_
    rw [comm_pow_left h4 g h 4, show Nat.choose 4 2 = 3 * 2 from rfl]
    exact mul_mem (mem_sup_left (mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_one g h) 4)))
      (mem_sup_right (pow_mul_mem (comm_mem_lcs_two' (comm_mem_lcs_one g h) g) 3 2))
  · rintro _ ⟨c, hc, rfl⟩
    refine (mem_Cent _).mpr fun h _ => ?_
    rw [comm_pow_left_of_lcs_one h4 hc h 2]
    exact mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_two hc h) 2)
  · rintro _ ⟨z, hz, rfl⟩
    refine (mem_Cent _).mpr fun h _ => ?_
    rw [commutator_central_left (mem_center_of_lcs_two h4 (pow_mem hz 2))]
    exact one_mem _

/-- `[F₂, F₃] ≤ F₅`. -/
theorem comm_F2_F3 : ⁅F2 G, F3 G⁆ ≤ F5 G := by
  rw [commutator_le_iff]
  refine sup_le (fun c hc => (mem_Cent_iff_le _).mpr (sup_le (sup_le ((closure_le _).mpr ?_)
    ((closure_le _).mpr ?_)) fun z hz => ?_)) ((closure_le _).mpr ?_)
  · rintro _ ⟨h, -, rfl⟩
    rw [SetLike.mem_coe, mem_Cx, comm_pow_left_lcs_one h4 hc h 4]
    exact mem_sup_right (pow_mul_mem (comm_mem_lcs_two' hc h) 2 2)
  · rintro _ ⟨c', hc', rfl⟩
    rw [SetLike.mem_coe, mem_Cx, comm_lcs_one_eq_one h4 (pow_mem hc' 2) hc]
    exact one_mem _
  · rw [mem_Cx, commutator_central_left (mem_center_of_lcs_two h4 hz)]
    exact one_mem _
  · rintro _ ⟨g, -, rfl⟩
    refine (mem_Cent_iff_le _).mpr (sup_le (sup_le ((closure_le _).mpr ?_)
      ((closure_le _).mpr ?_)) fun z hz => ?_)
    · rintro _ ⟨h, -, rfl⟩
      rw [SetLike.mem_coe, mem_Cx, comm_pow_left h4 h (g ^ 2) 4,
        show Nat.choose 4 2 = 3 * 2 from rfl]
      exact mul_mem (mem_sup_left (mem_sup_right
          (pow_mem_powSubgroup (comm_mem_lcs_one h (g ^ 2)) 4)))
        (mem_sup_right (pow_mul_mem (comm_mem_lcs_two' (comm_mem_lcs_one h (g ^ 2)) h) 3 2))
    · rintro _ ⟨c', hc', rfl⟩
      rw [SetLike.mem_coe, mem_Cx, comm_pow_left_of_lcs_one h4 hc' (g ^ 2) 2]
      exact mem_sup_right (pow_mem_powSubgroup (comm_mem_lcs_two hc' (g ^ 2)) 2)
    · rw [mem_Cx, commutator_central_left (mem_center_of_lcs_two h4 hz)]
      exact one_mem _

/-- `F₃² ≤ F₅`. -/
theorem pow_F3_le_F5 : powSubgroup (F3 G) 2 ≤ F5 G := by
  have hA : ⁅F3 G, F3 G⁆ ≤ F5 G := (commutator_mono F3_le_F2 le_rfl).trans (comm_F2_F3 h4)
  refine powSubgroup_le_of _ hA (sup_le (sup_le ((closure_le _).mpr ?_) ((closure_le _).mpr ?_))
    fun z hz => mem_Sq.mpr ⟨mem_sup_right hz, mem_sup_right (pow_mem_powSubgroup hz 2)⟩)
  · rintro _ ⟨h, -, rfl⟩
    refine mem_Sq.mpr ⟨mem_sup_left (mem_sup_left (pow_mem_powSubgroup (mem_top h) 4)), ?_⟩
    rw [← pow_mul]
    exact mem_sup_left (mem_sup_left (pow_mem_powSubgroup (mem_top h) 8))
  · rintro _ ⟨c, hc, rfl⟩
    refine mem_Sq.mpr ⟨mem_sup_left (mem_sup_right (pow_mem_powSubgroup hc 2)), ?_⟩
    rw [← pow_mul]
    exact mem_sup_left (mem_sup_right (pow_mem_powSubgroup hc 4))

/-! ## The Lazard series in class `≤ 3` -/

omit h4 in
theorem lazard_two_le : lazard 2 G 2 ≤ F2 G := by
  refine lazard_le le_rfl (fun a b ha hb han hbn _ => ?_) (fun a ha han _ => ?_)
  · obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    rw [lazard_one, ← _root_.commutator_def, ← Subgroup.top_lowerCentralSeries_one]
    exact le_sup_left
  · obtain rfl : a = 1 := by omega
    rw [lazard_one]
    exact le_sup_right

omit h4 in
theorem lazard_le_F2 {k : ℕ} (hk : 2 ≤ k) : lazard 2 G k ≤ F2 G :=
  (lazard_antitone (by norm_num) hk).trans lazard_two_le

theorem lazard_three_le : lazard 2 G 3 ≤ F3 G := by
  refine lazard_le (by norm_num) (fun a b ha hb han hbn hab => ?_) (fun a ha han h => ?_)
  · rcases le_or_gt 2 a with ha2 | ha2
    · exact (commutator_mono (lazard_le_F2 ha2) le_top).trans (comm_F2_top h4)
    · exact (commutator_mono le_top (lazard_le_F2 (by omega))).trans
        ((commutator_comm _ _).le.trans (comm_F2_top h4))
  · exact (powSubgroup_mono (lazard_le_F2 (by omega)) 2).trans (pow_F2_le_F3 h4)

theorem lazard_le_F3 {k : ℕ} (hk : 3 ≤ k) : lazard 2 G k ≤ F3 G :=
  (lazard_antitone (by norm_num) hk).trans (lazard_three_le h4)

theorem lazard_four_le : lazard 2 G 4 ≤ F4 G := by
  refine lazard_le (by norm_num) (fun a b ha hb han hbn hab => ?_) (fun a ha han h => ?_)
  · rcases le_or_gt 3 a with ha3 | ha3
    · exact (commutator_mono (lazard_le_F3 h4 ha3) le_top).trans (comm_F3_top h4)
    rcases le_or_gt 3 b with hb3 | hb3
    · exact (commutator_mono le_top (lazard_le_F3 h4 hb3)).trans
        ((commutator_comm _ _).le.trans (comm_F3_top h4))
    · exact (commutator_mono (lazard_le_F2 (by omega)) (lazard_le_F2 (by omega))).trans
        (comm_F2_F2 h4)
  · exact (powSubgroup_mono (lazard_le_F2 (by omega)) 2).trans (pow_F2_le_F4 h4)

/-- `S₅ ≤ G⁸ γ₂⁴ γ₃²` in class `≤ 3`. -/
theorem lazard_five_le : lazard 2 G 5 ≤ F5 G := by
  have hle4 : ∀ k, 4 ≤ k → lazard 2 G k ≤ F4 G := fun k hk =>
    (lazard_antitone (by norm_num) hk).trans (lazard_four_le h4)
  refine lazard_le (by norm_num) (fun a b ha hb han hbn hab => ?_) (fun a ha han h => ?_)
  · rcases le_or_gt 4 a with ha4 | ha4
    · exact (commutator_mono (hle4 a ha4) le_top).trans (comm_F4_top h4)
    rcases le_or_gt 4 b with hb4 | hb4
    · exact (commutator_mono le_top (hle4 b hb4)).trans
        ((commutator_comm _ _).le.trans (comm_F4_top h4))
    rcases le_or_gt 3 a with ha3 | ha3
    · exact (commutator_mono (lazard_le_F3 h4 ha3) (lazard_le_F2 (by omega))).trans
        ((commutator_comm _ _).le.trans (comm_F2_F3 h4))
    · exact (commutator_mono (lazard_le_F2 (by omega)) (lazard_le_F3 h4 (by omega))).trans
        (comm_F2_F3 h4)
  · exact (powSubgroup_mono (lazard_le_F3 h4 (by omega)) 2).trans (pow_F3_le_F5 h4)

/-- `S₅ ≤ ∏_{i 2^j ≥ 5} γ_i^{2^j}` in class `≤ 3`. -/
theorem lazard_five_le_jennings : lazard 2 G 5 ≤ jennings 2 G 5 :=
  (lazard_five_le h4).trans F5_le_jennings

end Inclusions

end ClassThree

end GroupDimension
