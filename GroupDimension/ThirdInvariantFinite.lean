module

public import GroupDimension.ThirdInvariant
public import GroupDimension.TaharaTheorem

@[expose] public section

/-!
# Theorem 12.6 and Theorem 11.2 of wiki 891 for finite groups (MATH-468)

Let `Q` be a finite `3`-group of class `≤ 4`. The hypothesis "at most two invariants of `Q_ab`
exceed `3^μ`" is stated intrinsically: the socle `Ω₁` of the subgroup `Q_ab^{3^μ}` of `3^μ`-th
powers has at most `9` elements (for `Q_ab ≅ ∏ C_{3^{k_i}}` it has `3^{#{i : k_i > μ}}`).

* `D_five_pow_eq_one_of_third_invariant` (Theorem 12.6): every `z ∈ D₅(Q)` has
  `z^{3^{μ-1}} = 1` (with `3^{μ-1} = 1` for `μ = 0`), i.e. `D₅(Q) ⊆ Ω_{μ-1}`;
* `D_five_eq_bot_of_two_large_invariants` (Theorem 11.2, the case `μ = 1`): if at most two
  invariants of `Q_ab` are `≥ 9`, then `D₅(Q) = 1`, with no condition on `γ₄(Q)`.

The finite reduction (the uniqueness bases, the basis adapted to the kernel of the cube map) is
that of `Ab399Finite.lean`; the hypothesis `hsmall` of `ThirdInvariant.Setup` comes from the socle
bound: three indices `i < j < k` with `d(i) ∤ 3^μ` would give the `27` socle vectors
`∑ a_l 3^{h_l} x̄_l` (`l ∈ {i, j, k}`, `a_l ∈ {0,1,2}`), all `3^μ`-th powers.
-/

namespace GroupDimension

namespace ThirdInvariant

open Subgroup Tahara ClassFour ExpThree
open scoped commutatorElement

/-- **Theorem 12.6 of wiki 891, modulo Tahara.** -/
theorem D_five_pow_eq_one_of_third_invariant' (hT : TaharaFiveOne) {Q : Type} [Group Q]
    [Finite Q] (h3 : IsPGroup 3 Q) (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) (μ : ℕ)
    (hsoc : Nat.card {w : Abelianization Q // w ^ 3 = 1 ∧ ∃ v, w = v ^ (3 ^ μ)} ≤ 9) :
    ∀ z ∈ D 5 Q, z ^ (3 ^ (μ - 1)) = 1 := by
  classical
  have h3grp : ∀ x : Q, ∃ k : ℕ, x ^ (3 ^ k) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by
    intro x
    obtain ⟨k, hk⟩ := h3 x
    exact ⟨k, by rw [hk]; exact one_mem _⟩
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
  have hexpk : ∀ k : ℕ, ∀ v : Additive (Layer Q k), ∃ m : ℕ, ((3 : ℤ) ^ m) • v = 0 := by
    intro k v
    obtain ⟨g, hg, rfl⟩ := cl_surj (G := Q) k v
    obtain ⟨m, hm⟩ := h3 g
    refine ⟨m, ?_⟩
    rw [← cl_zpow hg, show ((3 : ℤ) ^ m) = ((3 ^ m : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
      hm, cl_one]
  have hexp1 := hexpk 1
  have hexp2 := hexpk 2
  have htor : ∀ c ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, ∃ m : ℕ, c ^ (3 ^ m) = 1 :=
    fun c _ => h3 c
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
  -- `Abelianization.of` and the layer classes
  have hof : ∀ g h : Q, Abelianization.of g = Abelianization.of h ↔ cl Q 0 g = cl Q 0 h := by
    intro g h
    have e : Abelianization.of g = Abelianization.of h ↔ Abelianization.of (g⁻¹ * h) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
    rw [e, cl_eq_cl (mem_lcs_zero _) (mem_lcs_zero _), ← MonoidHom.mem_ker, Abelianization.ker_of]
    show _ ↔ _ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1
    rw [Subgroup.top_lowerCentralSeries_one]
  -- `hsmall` from the socle bound
  have hsmall : ∀ i j k : Fin s, i < j → j < k → 3 ^ (ht i + 1) ∣ 3 ^ μ := by
    intro i j k hij hjk
    by_contra hnd
    have hμ : μ ≤ ht i := by
      by_contra hlt
      exact hnd (Nat.pow_dvd_pow 3 (by omega))
    have hmono : ∀ {a b : Fin s}, a ≤ b → ht a ≤ ht b := by
      intro a b hab
      have hd := B1.dvd a b hab
      have hle : ht a + 1 ≤ ht b + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd
      omega
    have hμj : μ ≤ ht j := hμ.trans (hmono hij.le)
    have hμk : μ ≤ ht k := hμ.trans (hmono (hij.trans hjk).le)
    have hik : i < k := hij.trans hjk
    -- the coefficient vectors of the `27` socle vectors and of their `3^μ`-th roots
    let cf : ℕ → (Fin 3 → ZMod 3) → Fin s → ℤ := fun e a l =>
      (if l = i then (3 : ℤ) ^ (ht i - e) * ((a 0).val : ℤ) else 0) +
        (if l = j then (3 : ℤ) ^ (ht j - e) * ((a 1).val : ℤ) else 0) +
        (if l = k then (3 : ℤ) ^ (ht k - e) * ((a 2).val : ℤ) else 0)
    have hcf_i : ∀ e a, cf e a i = (3 : ℤ) ^ (ht i - e) * ((a 0).val : ℤ) := by
      intro e a
      simp [cf, hij.ne, hik.ne]
    have hcf_j : ∀ e a, cf e a j = (3 : ℤ) ^ (ht j - e) * ((a 1).val : ℤ) := by
      intro e a
      simp [cf, hij.ne', hjk.ne]
    have hcf_k : ∀ e a, cf e a k = (3 : ℤ) ^ (ht k - e) * ((a 2).val : ℤ) := by
      intro e a
      simp [cf, hik.ne', hjk.ne']
    have hcf_root : ∀ a l, (3 : ℤ) ^ μ * cf μ a l = cf 0 a l := by
      intro a l
      have e : ∀ m : ℕ, μ ≤ m → (3 : ℤ) ^ μ * (3 : ℤ) ^ (m - μ) = (3 : ℤ) ^ (m - 0) := by
        intro m hm
        rw [← pow_add, Nat.sub_zero, Nat.add_sub_cancel' hm]
      simp only [cf, mul_add]
      split_ifs <;> simp only [mul_zero, add_zero, zero_add, ← mul_assoc, e _ hμ, e _ hμj, e _ hμk]
    have hcl_sum : ∀ c : Fin s → ℤ, cl Q 0 (oprod x1 c) = ∑ l, c l • cl Q 0 (x1 l) :=
      fun c => cl_oprod (fun l => mem_lcs_zero _) c
    have hmem0 : ∀ c : Fin s → ℤ, (∀ l, ((3 ^ (ht l + 1) : ℕ) : ℤ) ∣ c l) →
        cl Q 0 (oprod x1 c) = 0 := by
      intro c hc
      rw [cl_eq_zero_iff (oprod_mem B1.mem c)]
      exact (B1.indep c).mpr hc
    have hdvd0 : ∀ a l, (3 : ℤ) ^ ht l ∣ cf 0 a l := by
      intro a l
      by_cases hi : l = i
      · subst hi
        rw [hcf_i, Nat.sub_zero]
        exact dvd_mul_right _ _
      by_cases hj : l = j
      · subst hj
        rw [hcf_j, Nat.sub_zero]
        exact dvd_mul_right _ _
      by_cases hk : l = k
      · subst hk
        rw [hcf_k, Nat.sub_zero]
        exact dvd_mul_right _ _
      simp [cf, hi, hj, hk]
    have hcube : ∀ a, cl Q 0 (oprod x1 (cf 0 a) ^ 3) = 0 := by
      intro a
      have e : cl Q 0 (oprod x1 (cf 0 a) ^ 3) = cl Q 0 (oprod x1 (fun l => 3 * cf 0 a l)) := by
        rw [← zpow_natCast, cl_zpow (mem_lcs_zero _), hcl_sum, hcl_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [smul_smul]
        norm_num
      rw [e]
      refine hmem0 _ fun l => ?_
      obtain ⟨q, hq⟩ := hdvd0 a l
      exact ⟨q, by rw [hq]; push_cast; ring⟩
    have hroot : ∀ a, cl Q 0 (oprod x1 (cf 0 a)) = cl Q 0 (oprod x1 (cf μ a) ^ (3 ^ μ)) := by
      intro a
      rw [← zpow_natCast, cl_zpow (mem_lcs_zero _), hcl_sum, hcl_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, ← hcf_root a l]
      push_cast
      rfl
    let w : (Fin 3 → ZMod 3) → {w : Abelianization Q // w ^ 3 = 1 ∧ ∃ v, w = v ^ (3 ^ μ)} :=
      fun a => ⟨Abelianization.of (oprod x1 (cf 0 a)), by
        refine ⟨?_, ⟨Abelianization.of (oprod x1 (cf μ a)), ?_⟩⟩
        · rw [← map_pow, ← map_one Abelianization.of, hof, cl_one]
          exact hcube a
        · rw [← map_pow, hof]
          exact hroot a⟩
    have hw : Function.Injective w := by
      intro a b hab
      have hab' : Abelianization.of (oprod x1 (cf 0 a)) = Abelianization.of (oprod x1 (cf 0 b)) :=
        congrArg Subtype.val hab
      rw [hof, hcl_sum, hcl_sum] at hab'
      have hz : cl Q 0 (oprod x1 (fun l => cf 0 a l - cf 0 b l)) = 0 := by
        rw [hcl_sum]
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [hab', sub_self]
      have hd := (B1.indep _).mp ((cl_eq_zero_iff (oprod_mem B1.mem _)).mp hz)
      have key : ∀ (l : Fin s) (r : Fin 3), cf 0 a l - cf 0 b l =
          (3 : ℤ) ^ ht l * (((a r).val : ℤ) - ((b r).val : ℤ)) → a r = b r := by
        intro l r he
        have h := hd l
        rw [he] at h
        push_cast at h
        rw [pow_succ] at h
        have h3 : (3 : ℤ) ∣ ((a r).val : ℤ) - ((b r).val : ℤ) :=
          (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h
        have ha := (a r).val_lt
        have hb := (b r).val_lt
        apply ZMod.val_injective
        omega
      funext r
      fin_cases r
      · exact key i 0 (by rw [hcf_i, hcf_i, Nat.sub_zero]; ring)
      · exact key j 1 (by rw [hcf_j, hcf_j, Nat.sub_zero]; ring)
      · exact key k 2 (by rw [hcf_k, hcf_k, Nat.sub_zero]; ring)
    have hcard := Nat.card_le_card_of_injective w hw
    have h27 : Nat.card (Fin 3 → ZMod 3) = 27 := by simp
    omega
  have S : Setup T act μ :=
    ⟨h5, htor, hvalid, fun i => ⟨ht i, rfl⟩,
      fun k => dvd_pow_self 3 (Nat.succ_ne_zero _),
      fun l => dvd_pow_self 3 (Nat.succ_ne_zero _), hsmall, fun i hi => not_not.mp hi, hind⟩
  intro z hz
  have hle := hT Q h5 T hvalid hz
  let Ωμ : Subgroup Q :=
    { carrier := {y | y ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 ∧ y ^ (3 ^ (μ - 1)) = 1}
      one_mem' := ⟨one_mem _, one_pow _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hc : Commute a b := comm_L2 h5 ha hb
        rw [hc.mul_pow, ha', hb', one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hcl : Subgroup.closure {y | ∃ τ : Coeffs T.s T.t, T.Admissible τ ∧ y = T.gen τ} ≤ Ωμ := by
    rw [Subgroup.closure_le]
    rintro y ⟨τ, hτ, rfl⟩
    exact ⟨S.gen_mem hτ, S.gen_pow_eq_one hτ⟩
  exact (hcl hle).2

end ThirdInvariant

end GroupDimension

namespace GroupDimension

/-- **Theorem 12.6 of wiki 891** (`D₅ ⊆ Ω_{μ-1}`). Let `Q` be a finite `3`-group of class `≤ 4`
and `μ` such that at most two invariants of `Q_ab` exceed `3^μ`, stated as: the elements of order
dividing `3` among the `3^μ`-th powers of `Q_ab` are at most `9`. Then every `z ∈ D₅(Q)`
satisfies `z^{3^{μ-1}} = 1` (`z = 1` when `μ ≤ 1`). -/
@[d5 "own:thm126"]
theorem D_five_pow_eq_one_of_third_invariant {Q : Type} [Group Q] [Finite Q] (h3 : IsPGroup 3 Q)
    (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥) (μ : ℕ)
    (hsoc : Nat.card {w : Abelianization Q // w ^ 3 = 1 ∧ ∃ v, w = v ^ (3 ^ μ)} ≤ 9) :
    ∀ z ∈ D 5 Q, z ^ (3 ^ (μ - 1)) = 1 :=
  ThirdInvariant.D_five_pow_eq_one_of_third_invariant' taharaFiveOne h3 h5 μ hsoc

/-- **Theorem 11.2 of wiki 891.** Let `Q` be a finite `3`-group of class `≤ 4` such that at most
two invariants of `Q_ab` are `≥ 9` (the cubes of `Q_ab` contain at most `9` elements of order
dividing `3`). Then `D₅(Q) = 1`, with no condition on `γ₄(Q)`. -/
@[d5 "own:thm126" "Theorem 11.2: at most two invariants ≥ 9"]
theorem D_five_eq_bot_of_two_large_invariants {Q : Type} [Group Q] [Finite Q]
    (h3 : IsPGroup 3 Q) (h5 : (⊤ : Subgroup Q).lowerCentralSeries 4 = ⊥)
    (hsoc : Nat.card {w : Abelianization Q // w ^ 3 = 1 ∧ ∃ v, w = v ^ 3} ≤ 9) :
    D 5 Q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h := D_five_pow_eq_one_of_third_invariant h3 h5 1 (by simpa using hsoc) z hz
  simpa using h

end GroupDimension
