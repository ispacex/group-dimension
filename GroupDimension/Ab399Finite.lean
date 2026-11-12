module

public import GroupDimension.Ab399

@[expose] public section

/-!
# The finite theorem for the abelianization `C₃ × C₉ × C₉`

This file contains the finite reduction for `Ab399.Setup.gen_eq_one`. The construction of the
uniqueness bases and of the basis adapted to the kernel of the cube map follows
`ExpThree.D_five_eq_bot_of_class_four_g4_cube`.
-/

namespace GroupDimension

namespace Ab399

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

/-- In the stipulated abelianization, the ninth power of every element is trivial. -/
private theorem pow_nine_eq_one {Q : Type*} [Group Q]
    (hab : Nonempty (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 1 ≃*
      Multiplicative (ZMod 3 × ZMod 9 × ZMod 9))) (x : Q) :
    x ^ 9 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
  obtain ⟨e⟩ := hab
  have hz : ∀ (n : ℕ), n ∣ 9 → ∀ z : ZMod n, (9 : ℕ) • z = 0 := by
    intro n hn z
    obtain ⟨k, hk⟩ := hn
    calc
      (9 : ℕ) • z = n • (k • z) := by rw [hk, Nat.mul_comm n k, mul_nsmul]
      _ = (n : ZMod n) • (k • z) := (Nat.cast_smul_eq_nsmul (ZMod n) n (k • z)).symm
      _ = 0 := by rw [ZMod.natCast_self, zero_smul]
  have htarget : ∀ z : Multiplicative (ZMod 3 × ZMod 9 × ZMod 9), z ^ 9 = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    simp only [toAdd_pow, toAdd_one]
    refine Prod.ext ?_ ?_
    · exact hz 3 (by norm_num) _
    · exact Prod.ext (hz 9 (by norm_num) _) (hz 9 (by norm_num) _)
  rw [← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk' ((⊤ : Subgroup Q).lowerCentralSeries 1)) (x ^ 9) = 1
  rw [map_pow]
  apply e.injective
  simp only [map_pow, map_one]
  exact htarget _

/-- Normal forms associated to a uniqueness basis of the first layer. -/
private noncomputable def normalFormEquiv {Q : Type*} [Group Q] {s : ℕ}
    {x : Fin s → Q} {ht : Fin s → ℕ}
    (B : IsLayerBasis 0 x (fun i => 3 ^ (ht i + 1))) :
    ((i : Fin s) → ZMod (3 ^ (ht i + 1))) ≃ Additive (Layer Q 0) := by
  classical
  letI : ∀ i, NeZero (3 ^ (ht i + 1)) := fun i => ⟨pow_ne_zero _ (by norm_num)⟩
  let d : Fin s → ℕ := fun i => 3 ^ (ht i + 1)
  let v : Fin s → Additive (Layer Q 0) := fun i => cl Q 0 (x i)
  have hzero : ∀ a : Fin s → ℤ,
      (∑ i, a i • v i = 0) ↔ ∀ i, (d i : ℤ) ∣ a i := by
    intro a
    simp only [d, v]
    rw [← cl_oprod B.mem, cl_eq_zero_iff (oprod_mem B.mem a), B.indep]
  let F : ((i : Fin s) → ZMod (d i)) → Additive (Layer Q 0) := fun a =>
    ∑ i, ((a i).val : ℤ) • v i
  have hmod : ∀ a : Fin s → ℤ, F (fun i => (a i : ZMod (d i))) = ∑ i, a i • v i := by
    intro a
    let c : Fin s → ℤ := fun i => (((a i : ZMod (d i))).val : ℤ)
    have hd : ∀ i, (d i : ℤ) ∣ c i - a i := by
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [c, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
    have hz : ∑ i, (c i - a i) • v i = 0 := (hzero _).mpr hd
    simp only [sub_smul, Finset.sum_sub_distrib] at hz
    exact sub_eq_zero.mp hz
  have hspan : ∀ w : Additive (Layer Q 0), ∃ a : Fin s → ℤ, w = ∑ i, a i • v i := by
    intro w
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 0 w
    obtain ⟨a, ha⟩ := B.span g hg
    refine ⟨a, ?_⟩
    rw [← cl_oprod B.mem]
    exact ((cl_eq_cl (oprod_mem B.mem a) hg).mpr ha).symm
  have hsurj : Function.Surjective F := by
    intro w
    obtain ⟨a, ha⟩ := hspan w
    refine ⟨fun i => (a i : ZMod (d i)), ?_⟩
    exact (hmod a).trans ha.symm
  have hinj : Function.Injective F := by
    intro a b hab
    have hz : ∑ i, (((a i).val : ℤ) - ((b i).val : ℤ)) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hab
    have hd := (hzero _).mp hz
    funext i
    apply ZMod.val_injective
    obtain ⟨q, hq⟩ := hd i
    have ha := (a i).val_lt
    have hb := (b i).val_lt
    have hq0 : q = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : (d i : ℤ) * q ≤ -(d i : ℤ) := by nlinarith
        omega
      · have : (d i : ℤ) ≤ (d i : ℤ) * q := by nlinarith
        omega
    subst q
    omega
  exact Equiv.ofBijective F ⟨hinj, hsurj⟩

/-- The `3`-torsion normal forms associated to a first-layer uniqueness basis. -/
private noncomputable def socleEquiv {Q : Type*} [Group Q] {s : ℕ}
    {x : Fin s → Q} {ht : Fin s → ℕ}
    (B : IsLayerBasis 0 x (fun i => 3 ^ (ht i + 1))) :
    (Fin s → ZMod 3) ≃ {w : Additive (Layer Q 0) // (3 : ℤ) • w = 0} := by
  classical
  let d : Fin s → ℕ := fun i => 3 ^ (ht i + 1)
  let v : Fin s → Additive (Layer Q 0) := fun i => cl Q 0 (x i)
  have hzero : ∀ a : Fin s → ℤ,
      (∑ i, a i • v i = 0) ↔ ∀ i, (d i : ℤ) ∣ a i := by
    intro a
    simp only [d, v]
    rw [← cl_oprod B.mem, cl_eq_zero_iff (oprod_mem B.mem a), B.indep]
  have hdo : ∀ i, (d i : ℤ) • v i = 0 := fun i =>
    TaharaProof.LayerNF.o_smul_cl (TaharaProof.IsLayerBasis.layerNF B) i
  have hpow : ∀ i, (3 : ℤ) * (3 ^ ht i : ℤ) = (d i : ℤ) := by
    intro i
    simp only [d]
    push_cast
    rw [pow_succ]
    ring
  let F3 : (Fin s → ZMod 3) → Additive (Layer Q 0) := fun a =>
    ∑ i, ((3 ^ ht i : ℤ) * ((a i).val : ℤ)) • v i
  have hF3 : ∀ a, (3 : ℤ) • F3 a = 0 := by
    intro a
    simp only [F3, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc
      (3 : ℤ) • ((3 ^ ht i : ℤ) * ((a i).val : ℤ)) • v i =
          ((a i).val : ℤ) • ((3 : ℤ) * (3 ^ ht i : ℤ)) • v i := by
        module
      _ = ((a i).val : ℤ) • (d i : ℤ) • v i := by rw [hpow]
      _ = 0 := by rw [hdo, smul_zero]
  have hmod3 : ∀ b : Fin s → ℤ, F3 (fun i => (b i : ZMod 3)) =
      ∑ i, ((3 ^ ht i : ℤ) * b i) • v i := by
    intro b
    let c : Fin s → ℤ := fun i => (((b i : ZMod 3)).val : ℤ)
    have hc : ∀ i, (3 : ℤ) ∣ c i - b i := by
      intro i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simp only [c, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
    have hd : ∀ i, (d i : ℤ) ∣ (3 ^ ht i : ℤ) * c i - (3 ^ ht i : ℤ) * b i := by
      intro i
      rw [← hpow i, ← mul_sub, mul_comm (3 : ℤ) (3 ^ ht i : ℤ)]
      exact mul_dvd_mul_left _ (hc i)
    have hz : ∑ i, ((3 ^ ht i : ℤ) * c i - (3 ^ ht i : ℤ) * b i) • v i = 0 :=
      (hzero _).mpr hd
    simp only [sub_smul, Finset.sum_sub_distrib] at hz
    exact sub_eq_zero.mp hz
  have hspan : ∀ w : Additive (Layer Q 0), ∃ a : Fin s → ℤ, w = ∑ i, a i • v i := by
    intro w
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 0 w
    obtain ⟨a, ha⟩ := B.span g hg
    refine ⟨a, ?_⟩
    rw [← cl_oprod B.mem]
    exact ((cl_eq_cl (oprod_mem B.mem a) hg).mpr ha).symm
  have hsurj : Function.Surjective (fun a => ⟨F3 a, hF3 a⟩ :
      (Fin s → ZMod 3) → {w : Additive (Layer Q 0) // (3 : ℤ) • w = 0}) := by
    rintro ⟨w, hw⟩
    obtain ⟨a, ha⟩ := hspan w
    have hz : ∑ i, ((3 : ℤ) * a i) • v i = 0 := by
      calc
        _ = (3 : ℤ) • ∑ i, a i • v i := by simp only [Finset.smul_sum, mul_smul]
        _ = 0 := by rw [← ha]; exact hw
    have hd := (hzero _).mp hz
    have hdiv : ∀ i, (3 ^ ht i : ℤ) ∣ a i := by
      intro i
      have hdi : ((3 : ℤ) * (3 ^ ht i : ℤ)) ∣ (3 : ℤ) * a i := by
        rw [hpow]
        exact hd i
      exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp hdi
    choose b hb using hdiv
    refine ⟨fun i => (b i : ZMod 3), ?_⟩
    apply Subtype.ext
    refine (hmod3 b).trans ?_
    simp_rw [← hb]
    exact ha.symm
  have hinj : Function.Injective (fun a => ⟨F3 a, hF3 a⟩ :
      (Fin s → ZMod 3) → {w : Additive (Layer Q 0) // (3 : ℤ) • w = 0}) := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    have hz : ∑ i, ((3 ^ ht i : ℤ) * (((a i).val : ℤ) - ((b i).val : ℤ))) • v i = 0 := by
      simp_rw [mul_sub]
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hab'
    have hd := (hzero _).mp hz
    funext i
    apply ZMod.val_injective
    have hdi := hd i
    rw [← hpow i, mul_comm (3 : ℤ) (3 ^ ht i : ℤ)] at hdi
    have h3 : (3 : ℤ) ∣ ((a i).val : ℤ) - ((b i).val : ℤ) := by
      exact (mul_dvd_mul_iff_left (by positivity : (3 ^ ht i : ℤ) ≠ 0)).mp hdi
    obtain ⟨q, hq⟩ := h3
    have ha := (a i).val_lt
    have hb := (b i).val_lt
    omega
  exact Equiv.ofBijective _ ⟨hinj, hsurj⟩

/-- `3`-torsion splits over a product of additive groups. -/
private def socleProdEquiv {A B : Type*} [AddGroup A] [AddGroup B] :
    {z : A × B // (3 : ℤ) • z = 0} ≃
      {a : A // (3 : ℤ) • a = 0} × {b : B // (3 : ℤ) • b = 0} where
  toFun z := (⟨z.1.1, by simpa using congrArg Prod.fst z.2⟩,
    ⟨z.1.2, by simpa using congrArg Prod.snd z.2⟩)
  invFun z := ⟨⟨z.1.1, z.2.1⟩, by apply Prod.ext <;> simp [z.1.2, z.2.2]⟩
  left_inv z := rfl
  right_inv z := rfl

/-- The `3`-torsion of `ZMod 9`, represented by `0, 3, 6`. -/
private noncomputable def socleZModNineEquiv :
    {z : ZMod 9 // (3 : ℤ) • z = 0} ≃ ZMod 3 := by
  classical
  let F : {z : ZMod 9 // (3 : ℤ) • z = 0} → ZMod 3 := fun z =>
    ((z.1.val / 3 : ℕ) : ZMod 3)
  have hval : ∀ z : {z : ZMod 9 // (3 : ℤ) • z = 0}, ∃ q, z.1.val = 3 * q := by
    intro z
    have hz : (3 : ℕ) • z.1 = 0 := by
      rw [← natCast_zsmul]
      exact z.2
    rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val z.1, ← Nat.cast_mul] at hz
    obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact ⟨q, by omega⟩
  have hgmem : ∀ a : ZMod 3, (3 : ℤ) • ((a.val * 3 : ℕ) : ZMod 9) = 0 := by
    intro a
    have hz : (3 : ℕ) • ((a.val * 3 : ℕ) : ZMod 9) = 0 := by
      rw [nsmul_eq_mul, ← Nat.cast_mul]
      have e : 3 * (a.val * 3) = 9 * a.val := by ring
      rw [e, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    exact (natCast_zsmul ((a.val * 3 : ℕ) : ZMod 9) 3).trans hz
  have hsurj : Function.Surjective F := by
    intro a
    refine ⟨⟨((a.val * 3 : ℕ) : ZMod 9), hgmem a⟩, ?_⟩
    dsimp only [F]
    have hv : a.val * 3 / 3 = a.val := by omega
    rw [ZMod.val_natCast_of_lt (by have ha := a.val_lt; omega), hv, ZMod.natCast_zmod_val]
  have hinj : Function.Injective F := by
    intro z w hzw
    obtain ⟨q, hq⟩ := hval z
    obtain ⟨p, hp⟩ := hval w
    have hltq : q < 3 := by have := z.1.val_lt; omega
    have hltp : p < 3 := by have := w.1.val_lt; omega
    have hzw' := hzw
    dsimp only [F] at hzw'
    rw [hq, hp] at hzw'
    have hvq : 3 * q / 3 = q := by omega
    have hvp : 3 * p / 3 = p := by omega
    rw [hvq, hvp] at hzw'
    have heq := congrArg ZMod.val hzw'
    rw [ZMod.val_natCast_of_lt hltq, ZMod.val_natCast_of_lt hltp] at heq
    apply Subtype.ext
    apply ZMod.val_injective
    rw [hq, hp, heq]
  exact Equiv.ofBijective F ⟨hinj, hsurj⟩

/-- The usual presentation of `Q/γ₂` and `Layer Q 0` are canonically isomorphic. -/
private noncomputable def layerZeroMulEquiv (Q : Type*) [Group Q] :
    (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 1) ≃* Layer Q 0 := by
  let f : (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 1) → Layer Q 0 :=
    Quotient.lift (fun g => QuotientGroup.mk ⟨g, mem_lcs_zero g⟩) (fun a b hab => by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact QuotientGroup.leftRel_apply.mp hab)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a using QuotientGroup.induction_on with | H a =>
      induction b using QuotientGroup.induction_on with | H b =>
        apply QuotientGroup.eq.mpr
        exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hab)
    · intro w
      induction w using QuotientGroup.induction_on with | H a =>
      exact ⟨(a : Q), rfl⟩
  exact
    { toEquiv := Equiv.ofBijective f hf
      map_mul' := by
        intro a b
        induction a using QuotientGroup.induction_on with | H a =>
        induction b using QuotientGroup.induction_on with | H b =>
        rfl }

/-- **`D₅(Q) = 1` for `Q_ab ≅ C₃ × C₉ × C₉`, modulo Tahara.** -/
@[d5 "own:ab399"]
theorem D_five_eq_bot_of_class_four_ab399 (hT : TaharaFiveOne) {Q : Type} [Group Q] [Finite Q]
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (hab : Nonempty (Q ⧸ (⊤ : Subgroup Q).lowerCentralSeries 1 ≃*
      Multiplicative (ZMod 3 × ZMod 9 × ZMod 9))) :
    D 5 Q = ⊥ := by
  classical
  have h3grp : ∀ x : Q, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
    fun x => ⟨2, by simpa using pow_nine_eq_one hab x⟩
  have hcl_pow : ∀ (g : Q) (k : ℕ),
      (k • cl Q 0 g = 0 ↔ g ^ k ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) := by
    intro g k
    rw [← natCast_zsmul, ← cl_zpow (mem_lcs_zero g), zpow_natCast, cl_eq_zero_iff (mem_lcs_zero _)]
  have hexp0 : ∀ v : Additive (Layer Q 0), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, -, rfl⟩ := cl_surj (G := Q) 0 v
    obtain ⟨k, hk⟩ := h3grp g
    refine ⟨k, ?_⟩
    rw [show ((3 : ℤ) ^ k) = ((3 ^ k : ℕ) : ℤ) by push_cast; rfl, natCast_zsmul]
    exact (hcl_pow g _).mpr hk
  -- The stipulated abelianization gives the uniform exponent `9 = 3²` on `Q/γ₂`.
  let N : ℕ := 2
  have hN : ∀ x : Q, x ^ (3 ^ N) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
    intro x
    simpa only [N, show 3 ^ 2 = 9 by norm_num] using pow_nine_eq_one hab x
  have hp0 : ∀ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 0,
      a ^ (3 ^ N) ∈ (⊤ : Subgroup Q).lowerCentralSeries (0 + 1) := fun a _ => hN a
  have hp1 := pow_succ_mem hp0
  have hp2 := pow_succ_mem hp1
  have hp3 := pow_succ_mem hp2
  have hexp1 : ∀ v : Additive (Layer Q 1), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 1 v
    refine ⟨N, ?_⟩
    rw [← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _),
      show ((3 : ℤ) ^ N) = ((3 ^ N : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    exact hp1 g hg
  have hexp2 : ∀ v : Additive (Layer Q 2), ∃ k : ℕ, ((3 : ℤ) ^ k) • v = 0 := by
    intro v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) 2 v
    refine ⟨N, ?_⟩
    rw [← cl_zpow hg, cl_eq_zero_iff (zpow_mem hg _),
      show ((3 : ℤ) ^ N) = ((3 ^ N : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
    exact hp2 g hg
  have htor : ∀ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1 := by
    intro c hc
    refine ⟨N + N, ?_⟩
    have hm : (c ^ (3 ^ N)) ^ (3 ^ N) = 1 := by
      have hm := hp3 _ (hp2 c hc)
      rwa [h5, mem_bot] at hm
    calc
      c ^ (3 ^ (N + N)) = (c ^ (3 ^ N)) ^ (3 ^ N) := by rw [pow_add, pow_mul]
      _ = 1 := hm
  -- the cube map `Ω₁(Q/γ₂) → L₂/3L₂` and its kernel
  choose L0 hL0 using fun v : Additive (Layer Q 0) => cl_surj (G := Q) 0 v
  let T3 : AddSubgroup (Additive (Layer Q 1)) :=
    { carrier := {v | ∃ w, (3 : ℤ) • w = v}
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, smul_add _ _ _⟩
      zero_mem' := ⟨0, smul_zero _⟩
      neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, smul_neg _ _⟩ }
  have hT3 : ∀ w, (3 : ℤ) • w ∈ T3 := fun w => ⟨w, rfl⟩
  have hmemW : ∀ x : Q, (3 : ℕ) • cl Q 0 x = 0 → x ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
    fun x h => (hcl_pow x 3).mp h
  have hwd : ∀ x y : Q, (3 : ℕ) • cl Q 0 x = 0 → cl Q 0 x = cl Q 0 y →
      cl Q 1 (y ^ 3) - cl Q 1 (x ^ 3) ∈ T3 := by
    intro x y hx hxy
    have hm : x⁻¹ * y ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
      (cl_eq_cl (mem_lcs_zero _) (mem_lcs_zero _)).mp hxy
    obtain ⟨-, he⟩ := cl_cube_mul (hmemW x hx) (pow_mem hm 3)
    rw [mul_inv_cancel_left] at he
    rw [he, cl_pow3 hm]
    have : cl Q 1 (x ^ 3) + (3 : ℤ) • cl Q 1 (x⁻¹ * y) + (3 : ℤ) • cl Q 1 (tc (x⁻¹ * y) x) -
        cl Q 1 (x ^ 3) = (3 : ℤ) • (cl Q 1 (x⁻¹ * y) + cl Q 1 (tc (x⁻¹ * y) x)) := by
      rw [smul_add]; abel
    rw [this]; exact hT3 _
  have hL0W : ∀ v : Additive (Layer Q 0), (3 : ℕ) • v = 0 → (3 : ℕ) • cl Q 0 (L0 v) = 0 :=
    fun v hv => by rw [(hL0 v).2]; exact hv
  let Ker0 : AddSubgroup (Additive (Layer Q 0)) :=
    { carrier := {v | (3 : ℕ) • v = 0 ∧ cl Q 1 (L0 v ^ 3) ∈ T3}
      zero_mem' := by
        refine ⟨smul_zero _, ?_⟩
        have h0 : L0 0 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
          (cl_eq_zero_iff (mem_lcs_zero _)).mp (hL0 0).2
        rw [cl_pow3 h0]; exact hT3 _
      add_mem' := by
        rintro u v ⟨hu3, hu⟩ ⟨hv3, hv⟩
        refine ⟨by rw [smul_add, hu3, hv3, add_zero], ?_⟩
        have hg : cl Q 0 (L0 u * L0 v) = u + v := by
          rw [cl_mul (mem_lcs_zero _) (mem_lcs_zero _), (hL0 u).2, (hL0 v).2]
        have hg3 : (3 : ℕ) • cl Q 0 (L0 u * L0 v) = 0 := by rw [hg, smul_add, hu3, hv3, add_zero]
        have h1 := hwd _ _ hg3 (hg.trans (hL0 (u + v)).2.symm)
        obtain ⟨-, he⟩ := cl_cube_mul (hmemW _ (hL0W u hu3)) (hmemW _ (hL0W v hv3))
        have : cl Q 1 (L0 (u + v) ^ 3) = (cl Q 1 (L0 (u + v) ^ 3) - cl Q 1 ((L0 u * L0 v) ^ 3)) +
            (cl Q 1 (L0 u ^ 3) + cl Q 1 (L0 v ^ 3) + (3 : ℤ) • cl Q 1 (tc (L0 v) (L0 u))) := by
          rw [← he]; abel
        rw [this]
        exact add_mem h1 (add_mem (add_mem hu hv) (hT3 _))
      neg_mem' := by
        rintro v ⟨hv3, hv⟩
        refine ⟨by rw [smul_neg, hv3, neg_zero], ?_⟩
        have hg : cl Q 0 (L0 v)⁻¹ = -v := by rw [cl_inv (mem_lcs_zero _), (hL0 v).2]
        have hg3 : (3 : ℕ) • cl Q 0 (L0 v)⁻¹ = 0 := by rw [hg, smul_neg, hv3, neg_zero]
        have h1 := hwd _ _ hg3 (hg.trans (hL0 (-v)).2.symm)
        have hv1 := hmemW _ (hL0W v hv3)
        have hinv : cl Q 1 ((L0 v)⁻¹ ^ 3) = -cl Q 1 (L0 v ^ 3) := by
          rw [inv_pow, cl_inv hv1]
        have : cl Q 1 (L0 (-v) ^ 3) = (cl Q 1 (L0 (-v) ^ 3) - cl Q 1 ((L0 v)⁻¹ ^ 3)) +
            -cl Q 1 (L0 v ^ 3) := by rw [← hinv]; abel
        rw [this]
        exact add_mem h1 (neg_mem hv) }
  -- the three uniqueness bases
  obtain ⟨s, x1, ht, B1, hpow1, -, hKer⟩ := exists_layer_basis (G := Q) 0 hexp0 Ker0
  obtain ⟨t, x2, ht2, B2, hpow2, nf2, -⟩ := exists_layer_basis (G := Q) 1 hexp1 ⊥
  obtain ⟨u, x3, ht3, B3, -, nf3, -⟩ := exists_layer_basis (G := Q) 2 hexp2 ⊥
  have hY1 : ∀ i, x1 i ^ (3 ^ (ht i + 1)) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := hpow1
  -- the structure constants
  choose b hbr hbm using fun i => nf2 _ (hY1 i)
  have hrem : ∀ i, (oprod x2 (b i))⁻¹ * x1 i ^ (3 ^ (ht i + 1)) ∈
      (⊤ : Subgroup Q).lowerCentralSeries 2 := hbm
  choose c hcr hcm using fun i => nf3 _ (hrem i)
  have hx2e : ∀ k, x2 k ^ (3 ^ (ht2 k + 1)) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := hpow2
  choose dd hddr hddm using fun k => nf3 _ (hx2e k)
  have hαm : ∀ g h, tc (x1 g ^ (3 ^ (ht g + 1))) (x1 h) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 :=
    fun g h => tc_mem (i := 1) (j := 0) (by omega) (hY1 g) (mem_lcs_zero (x1 h))
  choose α hαr hαm' using fun g h => nf3 _ (hαm g h)
  let T : Tahara.Data Q :=
    { s := s, t := t, u := u, x₁ := x1, d := fun i => 3 ^ (ht i + 1), x₂ := x2,
      e := fun k => 3 ^ (ht2 k + 1), x₃ := x3, f := fun l => 3 ^ (ht3 l + 1),
      b := b, c := c, dd := dd, α := α }
  have hvalid : T.Valid := by
    refine ⟨B1, B2, B3, fun i k => hbr i k, fun i l => hcr i l, fun k l => hddr k l,
      fun g h l _ => hαr g h l, fun i => ?_, fun k => hddm k, fun g h _ => hαm' g h⟩
    show (oprod x2 (b i) * oprod x3 (c i))⁻¹ * x1 i ^ (3 ^ (ht i + 1)) ∈ _
    rw [mul_inv_rev, mul_assoc]
    exact hcm i
  let act : Fin s → Prop := fun i => ¬ ∃ a ∈ (⊤ : Subgroup Q).lowerCentralSeries 1,
    ∃ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, x1 i ^ (3 ^ (ht i + 1)) = a ^ 3 * c
  -- the socle vectors `z_i = 3^{h_i} x̄_i`, with `z_i ∈ Ker0` exactly for the inactive `i`
  have hz3 : ∀ i, (3 : ℕ) • cl Q 0 (x1 i ^ (3 ^ ht i)) = 0 := by
    intro i
    rw [← natCast_zsmul, ← cl_zpow (mem_lcs_zero _), zpow_natCast, ← pow_mul, ← pow_succ,
      cl_eq_zero_iff (mem_lcs_zero _)]
    exact hY1 i
  have hcube : ∀ i, (x1 i ^ (3 ^ ht i)) ^ 3 = x1 i ^ (3 ^ (ht i + 1)) := fun i => by
    rw [← pow_mul, ← pow_succ]
  have hnotK : ∀ i, act i → cl Q 0 (x1 i ^ (3 ^ ht i)) ∉ Ker0 := by
    intro i hi hK
    apply hi
    obtain ⟨-, hT⟩ := hK
    have h1 := hwd _ _ (hL0W _ (hz3 i)) (hL0 _).2
    rw [hcube] at h1
    obtain ⟨w, hw⟩ := add_mem h1 hT
    rw [sub_add_cancel] at hw
    obtain ⟨a, ha, rfl⟩ := cl_surj (G := Q) 1 w
    rw [← cl_pow3 ha] at hw
    refine ⟨a, ha, (a ^ 3)⁻¹ * x1 i ^ (3 ^ (ht i + 1)),
      (cl_eq_cl (pow_mem ha 3) (hY1 i)).mp hw, by group⟩
  -- the cube of a product of the `z_i`
  have hprod : ∀ l : List Q, (∀ w ∈ l, w ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) →
      l.prod ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 ∧
      cl Q 1 (l.prod ^ 3) - (l.map fun w => cl Q 1 (w ^ 3)).sum ∈ T3 := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.prod_nil, one_pow, List.map_nil, List.sum_nil, sub_zero]
      exact ⟨one_mem _, by rw [cl_one]; exact zero_mem _⟩
    | cons w l ih =>
      intro hl
      obtain ⟨hl3, hlT⟩ := ih fun z hz => hl z (List.mem_cons_of_mem _ hz)
      obtain ⟨hm, he⟩ := cl_cube_mul (hl w List.mem_cons_self) hl3
      refine ⟨by rw [List.prod_cons]; exact hm, ?_⟩
      rw [List.prod_cons, he, List.map_cons, List.sum_cons]
      have : cl Q 1 (w ^ 3) + cl Q 1 (l.prod ^ 3) + (3 : ℤ) • cl Q 1 (tc l.prod w) -
          (cl Q 1 (w ^ 3) + (l.map fun w => cl Q 1 (w ^ 3)).sum) =
          (cl Q 1 (l.prod ^ 3) - (l.map fun w => cl Q 1 (w ^ 3)).sum) +
            (3 : ℤ) • cl Q 1 (tc l.prod w) := by abel
      rw [this]
      exact add_mem hlT (hT3 _)
  have hind : ∀ cf : Fin s → ℤ, (∀ k, (3 : ℤ) ∣ ∑ h, cf h * b h k) → ∀ h, act h → (3 : ℤ) ∣ cf h := by
    intro cf hcf h hh
    refine hKer cf ?_ h (hnotK h hh)
    -- `∑ cf_i z_i ∈ Ker0`
    let z : Fin s → Q := fun i => x1 i ^ (3 ^ ht i)
    have e3 : ∀ i, (z i ^ cf i) ^ 3 = (z i ^ 3) ^ cf i := fun i => by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hz1 : ∀ i, (z i ^ cf i) ^ 3 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := fun i => by
      rw [e3]
      exact zpow_mem (hmemW _ (hz3 i)) _
    have hcl : cl Q 0 (oprod z cf) = ∑ i, cf i • cl Q 0 (x1 i ^ (3 ^ ht i)) :=
      cl_oprod (fun i => mem_lcs_zero _) cf
    have hsum3 : (3 : ℕ) • ∑ i, cf i • cl Q 0 (x1 i ^ (3 ^ ht i)) = 0 := by
      rw [Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_comm, hz3 i, smul_zero]
    refine ⟨hsum3, ?_⟩
    have hwd' := hwd _ _ (by rw [hcl]; exact hsum3) (hcl.trans (hL0 _).2.symm)
    have hP := hprod (List.ofFn fun i => z i ^ cf i) (fun w hw => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw; exact hz1 i)
    have hsumY : (List.map (fun w => cl Q 1 (w ^ 3)) (List.ofFn fun i => z i ^ cf i)).sum =
        ∑ i, cf i • cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) := by
      rw [List.map_ofFn, List.sum_ofFn]
      refine Finset.sum_congr rfl fun i _ => ?_
      show cl Q 1 ((z i ^ cf i) ^ 3) = _
      rw [e3 i, cl_zpow (hmemW _ (hz3 i)), show z i ^ 3 = x1 i ^ (3 ^ (ht i + 1)) from hcube i]
    have hYb : ∀ i, cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) = ∑ k, b i k • cl Q 1 (x2 k) := by
      intro i
      rw [← cl_oprod (k := 1) (y := x2) (fun k => B2.mem k) (b i)]
      exact ((cl_eq_cl (oprod_mem (fun k => B2.mem k) _) (hY1 i)).mpr (hrem i)).symm
    have hT : ∑ i, cf i • cl Q 1 (x1 i ^ (3 ^ (ht i + 1))) ∈ T3 := by
      simp_rw [hYb, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      refine sum_mem fun k _ => ?_
      obtain ⟨m, hm⟩ := hcf k
      rw [hm, mul_smul]
      exact hT3 _
    have hS : (List.map (fun w => cl Q 1 (w ^ 3)) (List.ofFn fun i => z i ^ cf i)).sum ∈ T3 := by
      rw [hsumY]; exact hT
    have hP2 : cl Q 1 ((oprod z cf) ^ 3) ∈ T3 := by
      have := add_mem hP.2 hS
      rwa [sub_add_cancel] at this
    have := add_mem hwd' hP2
    rwa [sub_add_cancel] at this
  obtain ⟨i₀, i₁, i₂, h01, h12, hall, hd₀, hd₁, hd₂⟩ :
      ∃ i₀ i₁ i₂ : Fin s, i₀ < i₁ ∧ i₁ < i₂ ∧ (∀ i, i = i₀ ∨ i = i₁ ∨ i = i₂) ∧
        T.d i₀ = 3 ∧ T.d i₁ = 9 ∧ T.d i₂ = 9 := by
    obtain ⟨e⟩ := hab
    let eA : Additive (Layer Q 0) ≃+
        Additive (Multiplicative (ZMod 3 × ZMod 9 × ZMod 9)) :=
      MulEquiv.toAdditive ((layerZeroMulEquiv Q).symm.trans e)
    have hcardA : Nat.card (Additive (Layer Q 0)) = 243 := by
      rw [Nat.card_congr eA.toEquiv]
      norm_num [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]
    have hprod : ∏ i, 3 ^ (ht i + 1) = 243 := by
      calc
        _ = Nat.card ((i : Fin s) → ZMod (3 ^ (ht i + 1))) := by
          simp only [Nat.card_pi, Nat.card_zmod]
        _ = Nat.card (Additive (Layer Q 0)) := Nat.card_congr (normalFormEquiv B1)
        _ = 243 := hcardA
    let targetEquiv : {z : Additive (Multiplicative (ZMod 3 × ZMod 9 × ZMod 9)) //
        (3 : ℤ) • z = 0} ≃ ZMod 3 × ZMod 3 × ZMod 3 := by
      let e1 := socleProdEquiv (A := ZMod 3) (B := ZMod 9 × ZMod 9)
      let e2 := socleProdEquiv (A := ZMod 9) (B := ZMod 9)
      let e3 : {z : ZMod 3 // (3 : ℤ) • z = 0} ≃ ZMod 3 :=
        Equiv.subtypeUnivEquiv (fun z => (natCast_zsmul z 3).trans
          (ZModModule.char_nsmul_eq_zero 3 z))
      exact e1.trans (e3.prodCongr (e2.trans
        (socleZModNineEquiv.prodCongr socleZModNineEquiv)))
    have htargetSoc : Nat.card {z : Additive (Multiplicative (ZMod 3 × ZMod 9 × ZMod 9)) //
        (3 : ℤ) • z = 0} = 27 := by
      calc
        _ = Nat.card (ZMod 3 × ZMod 3 × ZMod 3) := Nat.card_congr targetEquiv
        _ = 27 := by norm_num [Nat.card_prod, Nat.card_zmod]
    let esoc : {w : Additive (Layer Q 0) // (3 : ℤ) • w = 0} ≃
        {z : Additive (Multiplicative (ZMod 3 × ZMod 9 × ZMod 9)) //
          (3 : ℤ) • z = 0} :=
      Equiv.subtypeEquiv eA.toEquiv (fun w => by
        constructor
        · intro hw
          change (3 : ℤ) • eA w = 0
          rw [← map_zsmul, hw, map_zero]
        · intro hw
          apply eA.injective
          rw [map_zsmul, map_zero]
          exact hw)
    have hsPow : 3 ^ s = 27 := by
      calc
        3 ^ s = Nat.card (Fin s → ZMod 3) := by simp [Nat.card_fun, Nat.card_zmod]
        _ = Nat.card {w : Additive (Layer Q 0) // (3 : ℤ) • w = 0} :=
          Nat.card_congr (socleEquiv B1)
        _ = Nat.card {z : Additive (Multiplicative (ZMod 3 × ZMod 9 × ZMod 9)) //
            (3 : ℤ) • z = 0} := Nat.card_congr esoc
        _ = 27 := htargetSoc
    have hs3 : s = 3 := by
      have hp : 3 ^ s = 3 ^ 3 := by norm_num [hsPow]
      exact Nat.pow_right_injective (by norm_num) hp
    have hdvd : ∀ i, 3 ^ (ht i + 1) ∣ 9 := by
      intro i
      have hx9 : x1 i ^ 9 ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
        simpa only [N, show 3 ^ 2 = 9 by norm_num] using hN (x1 i)
      have hs : ∑ j, (if j = i then (9 : ℤ) else 0) • cl Q 0 (x1 j) = 0 := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
        simp only [ite_true]
        exact (natCast_zsmul (cl Q 0 (x1 i)) 9).trans ((hcl_pow (x1 i) 9).mpr hx9)
      have hm : oprod x1 (fun j => if j = i then (9 : ℤ) else 0) ∈
          (⊤ : Subgroup Q).lowerCentralSeries 1 := by
        rw [← cl_eq_zero_iff (oprod_mem B1.mem _), cl_oprod B1.mem]
        exact hs
      have hd := (B1.indep _).mp hm i
      have hd' : ((3 ^ (ht i + 1) : ℕ) : ℤ) ∣ (9 : ℤ) := by simpa using hd
      exact_mod_cast hd'
    have hht : ∀ i, ht i = 0 ∨ ht i = 1 := by
      intro i
      have hle9 := Nat.le_of_dvd (by norm_num : 0 < 9) (hdvd i)
      have hle : ht i + 1 ≤ 2 := by
        by_contra hn
        have hpow : 3 ^ 3 ≤ 3 ^ (ht i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        norm_num at hpow
        omega
      omega
    have hmono : ∀ {i j : Fin s}, i ≤ j → ht i ≤ ht j := by
      intro i j hij
      have hd := B1.dvd i j hij
      have hle : ht i + 1 ≤ ht j + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd
      omega
    subst s
    rw [Fin.prod_univ_three] at hprod
    have hm01 := hmono (i := 0) (j := 1) (by norm_num)
    have hm12 := hmono (i := 1) (j := 2) (by norm_num)
    have hvals : ht (0 : Fin 3) = 0 ∧ ht (1 : Fin 3) = 1 ∧ ht (2 : Fin 3) = 1 := by
      rcases hht 0 with h0 | h0 <;> rcases hht 1 with h1 | h1 <;>
        rcases hht 2 with h2 | h2 <;> simp [h0, h1, h2] at hprod ⊢ <;> omega
    obtain ⟨h0, h1, h2⟩ := hvals
    refine ⟨0, 1, 2, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · change 3 ^ (ht 0 + 1) = 3
      norm_num [h0]
    · change 3 ^ (ht 1 + 1) = 9
      norm_num [h1]
    · change 3 ^ (ht 2 + 1) = 9
      norm_num [h2]
  have S : Setup T act i₀ i₁ i₂ :=
    ⟨h5, htor, hvalid, h01, h12, hall, hd₀, hd₁, hd₂,
      fun k => dvd_pow_self 3 (Nat.succ_ne_zero _),
      fun l => dvd_pow_self 3 (Nat.succ_ne_zero _), fun i hi => not_not.mp hi, hind⟩
  have hle := hT Q h5 T hvalid
  rw [eq_bot_iff]
  refine hle.trans ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨τ, hτ, rfl⟩
  rw [SetLike.mem_coe, S.gen_eq_one hτ]
  exact one_mem _

end Ab399

end GroupDimension
