module

public import GroupDimension.TraceReplay.HomPow
public import GroupDimension.TraceCert
import Mathlib.Data.Set.Finite.List
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

/-!
# Exact membership with free columns, from weight-1 polynomial maps (MATH-314)

A trace with free columns `F ≠ []` gives, through `check_sound`, the exactness statement
(X) `p^{E−1} Q ⊆ F̄ + p^E Q` in `Q = Δ/Δ^n`. Here `F̄` is spanned by the images `v_f` of the
monomials `ψ(X_f)`, `f ∈ F`. To conclude, `F̄` must meet the torsion of `Q` trivially
(`TraceCert.eq_zero_of_mem_pow`).

The certificate (`HomCert`) gives functionals `ν = φ_a^K`. Here `φ_a` is the homomorphism
`G → ℤ` with `g_j ↦ a_j`, and `K < n`. By `nu_eq_zero` they vanish on `Δ^n`, so they are defined
on `Q`, and they kill the torsion. The certificate also gives an integer matrix `C`, one row per
free column, with `C · (ν_κ(v_f)) = diag(D_f)` and every `D_f ≠ 0`. The kernel checks this
(`checkHom`; the values `ν_κ(v_f)` are `hval`, `nu_psi`). So `a ↦ ν(Σ a_f v_f)` is injective on
`ℤ^F`, and `F̄` meets the torsion trivially.

Contents:
* `Qn G n = Δ/Δ^n` and `toQ`. `Qn` is finitely generated when the `g_j` generate `G`, with no
  hypothesis on the exponent: `x^{−1} − 1` is a geometric series modulo `Δ^n`.
* `check_mem_D_hom`. Suppose the trace and the certificate pass, the `g_j` generate `G`, the
  relators hold, each `a` is the restriction of a homomorphism `G → ℤ`, and the test element has
  `p`-power order in `Δ/Δ^n` (a hypothesis, as in `cert/TRACE.md`, step 6). Then the test word
  lies in `D_n(G)`.
* `check_mem_D_pres`: the same for the group presented by `allRels`. The homomorphisms then come
  from a kernel check (exponent sums), and the generation and relator hypotheses come for free.
-/

namespace GroupDimension.TraceReplay

open MonoidAlgebra

/-! ## The certificate -/

/-- Weight-1 polynomial maps for a trace with free columns. -/
structure HomCert where
  /-- the functionals `(a, K)`: `ν = φ_a^K`, `φ_a(g_j) = a_j` (generator `j + 1`) -/
  funcs : List (List Int × Nat)
  /-- one row per free column, in the order of `T.F`: `(C_f, D_f)` with `C_f · (ν(v_{f'})) = D_f δ` -/
  rows : List (List Int × Int)
  deriving Repr

/-- `ν_κ(ψ(X_f))`, by `hval`. -/
def colVal (d : Nat) [NeZero d] (κ : List Int × Nat) (f : Nat) : Int :=
  hval κ.1 κ.2 0 ((wordAt d f).toList.map (·.val))

/-- `Σ_{i<n} f i`. -/
def lsum (n : Nat) (f : Nat → Int) : Int := ((List.range n).map f).sum

/-- The certificate check: every `K < n`, and `C · M = diag(D)` with `D_f ≠ 0`, where
`M_{κ,f} = ν_κ(ψ(X_f))`. -/
def checkHom (T : Trace) [NeZero T.d] (H : HomCert) : Bool :=
  H.funcs.all (fun κ => decide (κ.2 < T.n)) &&
  (List.range T.F.length).all (fun i => decide ((H.rows.getD i ([], 0)).2 ≠ 0) &&
    (List.range T.F.length).all (fun j => decide (
      lsum H.funcs.length (fun k => (H.rows.getD i ([], 0)).1.getD k 0 *
        colVal T.d (H.funcs.getD k ([], 0)) (T.F.getD j 0)) =
      if i = j then (H.rows.getD i ([], 0)).2 else 0)))

theorem lsum_eq (n : ℕ) (f : ℕ → ℤ) : lsum n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lsum, List.range_succ, List.map_append, List.sum_append, ← lsum, ih,
      Finset.sum_range_succ]; simp

/-- Linear algebra of the certificate: `C · M = diag(D)`, `D_i ≠ 0`, and `a · Mᵀ = 0` force `a = 0`. -/
theorem eq_zero_of_cert {nf nk : ℕ} (C M : ℕ → ℕ → ℤ) (Dg : ℕ → ℤ) (hD : ∀ i < nf, Dg i ≠ 0)
    (hCM : ∀ i < nf, ∀ j < nf, ∑ k ∈ Finset.range nk, C i k * M k j = if i = j then Dg i else 0)
    (a : ℕ → ℤ) (ha : ∀ k < nk, ∑ j ∈ Finset.range nf, a j * M k j = 0) : ∀ i < nf, a i = 0 := by
  intro i hi
  have h1 : ∑ j ∈ Finset.range nf, a j * (∑ k ∈ Finset.range nk, C i k * M k j) = 0 := by
    have e : ∑ j ∈ Finset.range nf, a j * (∑ k ∈ Finset.range nk, C i k * M k j) =
        ∑ k ∈ Finset.range nk, C i k * ∑ j ∈ Finset.range nf, a j * M k j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Finset.sum_eq_zero fun k hk => by rw [ha k (Finset.mem_range.mp hk), mul_zero]
  rw [Finset.sum_eq_single i (fun j hj hji => by
      rw [hCM i hi j (Finset.mem_range.mp hj), if_neg (Ne.symm hji), mul_zero])
    (fun h => absurd (Finset.mem_range.mpr hi) h), hCM i hi i hi, if_pos rfl] at h1
  exact (mul_eq_zero.mp h1).resolve_right (hD i hi)

/-! ## Positions -/

section Pos

variable {d : ℕ} [NeZero d]

theorem wordAt_length (c : ℕ) : (wordAt d c).length = degOf d c := by
  rw [wordAt, length_wordOf]

theorem degOf_pos {c : ℕ} (hc : 0 < c) : 0 < degOf d c := by
  have h := (deg_spec (NeZero.pos d) c).2
  by_contra h0
  rw [show degOf d c = 0 by omega] at h
  simp [off] at h
  omega

variable {G : Type*} [Group G] (g : Fin d → G)

theorem psi_e_mem {c : ℕ} (hc : 0 < c) : psi g (e d c) ∈ augIdeal G := by
  have h := psi_single_mem g (wordAt d c) 1
  rw [wordAt_length] at h
  exact Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp (degOf_pos hc)) h

end Pos

/-! ## `Q = Δ/Δ^n` -/

section Q

variable (G : Type*) [Group G]

/-- `Δ` as a `ℤ`-module. -/
noncomputable abbrev Del : Submodule ℤ (MonoidAlgebra ℤ G) := (augIdeal G).restrictScalars ℤ

/-- `Δ^n` inside `Δ`. -/
noncomputable abbrev NnD (n : ℕ) : Submodule ℤ (Del G) :=
  ((augIdeal G ^ n).restrictScalars ℤ).comap (Del G).subtype

/-- `Q = Δ/Δ^n`. -/
abbrev Qn (n : ℕ) := Del G ⧸ NnD G n

variable {G}

open Classical in
/-- The class in `Δ/Δ^n` (`0` off `Δ`). -/
noncomputable def toQ (n : ℕ) (y : MonoidAlgebra ℤ G) : Qn G n :=
  if h : y ∈ augIdeal G then Submodule.Quotient.mk ⟨y, h⟩ else 0

variable {n : ℕ}

theorem toQ_of_mem {y : MonoidAlgebra ℤ G} (h : y ∈ augIdeal G) :
    toQ n y = Submodule.Quotient.mk ⟨y, h⟩ := dif_pos h

theorem toQ_add {x y : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G) (hy : y ∈ augIdeal G) :
    toQ n (x + y) = toQ n x + toQ n y := by
  rw [toQ_of_mem hx, toQ_of_mem hy, toQ_of_mem (add_mem hx hy), ← Submodule.Quotient.mk_add]; rfl

theorem toQ_smul (c : ℤ) {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G) :
    toQ n (c • x) = c • toQ n x := by
  rw [toQ_of_mem hx, toQ_of_mem (Submodule.smul_of_tower_mem _ c hx),
    ← Submodule.Quotient.mk_smul]; rfl

theorem toQ_zero : toQ n (0 : MonoidAlgebra ℤ G) = 0 := by
  rw [toQ_of_mem (zero_mem _)]; exact (Submodule.Quotient.mk_eq_zero _).2 (zero_mem _)

theorem toQ_eq_zero_iff {y : MonoidAlgebra ℤ G} (hy : y ∈ augIdeal G) :
    toQ n y = 0 ↔ y ∈ augIdeal G ^ n := by
  rw [toQ_of_mem hy, Submodule.Quotient.mk_eq_zero]; rfl

theorem toQ_eq_zero (hn : n ≠ 0) {y : MonoidAlgebra ℤ G} (h : y ∈ augIdeal G ^ n) : toQ n y = 0 :=
  (toQ_eq_zero_iff (Ideal.pow_le_self hn h)).2 h

theorem toQ_surj (q : Qn G n) : ∃ y ∈ augIdeal G, toQ n y = q := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨y, hy, toQ_of_mem hy⟩

/-- `ν = φ^K` on `Δ/Δ^n`, `K < n`. -/
noncomputable def nuQ (φ : G →* Multiplicative ℤ) (K : ℕ) (hK : K < n) : Qn G n →ₗ[ℤ] ℚ :=
  (NnD G n).liftQ ((nu φ K).toIntLinearMap ∘ₗ (Del G).subtype) (by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      AddMonoidHom.coe_toIntLinearMap]
    exact nu_eq_zero φ hK hx)

theorem nuQ_toQ (φ : G →* Multiplicative ℤ) {K : ℕ} (hK : K < n) {y : MonoidAlgebra ℤ G}
    (hy : y ∈ augIdeal G) : nuQ φ K hK (toQ n y) = nu φ K y := by
  rw [toQ_of_mem hy]; rfl

end Q

/-! ## `Δ/Δ^n` is finitely generated -/

section Fin

variable {G : Type*} [Group G] {d : ℕ} [NeZero d] (g : Fin d → G)

/-- If the `g_j` generate `G`, every `x − 1` lies in `Sp` (no hypothesis on the exponent). -/
theorem sub_one_mem_Sp' (hgen : Subgroup.closure (Set.range g) = ⊤) {n : ℕ} (hn : 1 ≤ n)
    (x : G) : of ℤ G x - 1 ∈ Sp g n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hmul : ∀ a b : G, of ℤ G a - 1 ∈ Sp g (k + 1) → of ℤ G b - 1 ∈ Sp g (k + 1) →
      of ℤ G (a * b) - 1 ∈ Sp g (k + 1) := by
    intro a b ha hb
    have e : of ℤ G (a * b) - 1 =
        (of ℤ G a - 1) * (of ℤ G b - 1) + (of ℤ G a - 1) + (of ℤ G b - 1) := by
      rw [map_mul]; noncomm_ring
    rw [e]; exact add_mem (add_mem (Sp_mul g ha hb) ha) hb
  have hx : x ∈ Subgroup.closure (Set.range g) := by rw [hgen]; trivial
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨FreeMonoid.of j, ?_, ?_⟩)
    · intro h
      have := congrArg FreeMonoid.length h
      simp at this
    · rw [psi_single, FreeMonoid.toList_of, List.map_singleton, List.prod_singleton, one_smul]
  | one => simp only [map_one, sub_self]; exact zero_mem _
  | mul a b _ _ ha hb => exact hmul a b ha hb
  | inv a _ ha =>
    -- `y = 1 − a`, `z = a⁻¹`: `z − Σ_{i<m} y^i = y^m z`
    set y : MonoidAlgebra ℤ G := 1 - of ℤ G a with hydef
    have hyS : y ∈ Sp g (k + 1) := by
      have := neg_mem ha; rwa [neg_sub] at this
    have hyD : y ∈ augIdeal G := by
      have := neg_mem (of_sub_one_mem_augIdeal (G := G) a); rwa [neg_sub] at this
    have hz : y * of ℤ G a⁻¹ = of ℤ G a⁻¹ - 1 := by
      rw [hydef, sub_mul, one_mul, ← map_mul, mul_inv_cancel, map_one]
    have key : ∀ m : ℕ, of ℤ G a⁻¹ - ∑ i ∈ Finset.range m, y ^ i = y ^ m * of ℤ G a⁻¹ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ← sub_sub, ih, pow_succ, mul_assoc, hz, mul_sub, mul_one]
    have e : of ℤ G a⁻¹ - 1 = ∑ i ∈ Finset.range k, y ^ (i + 1) + y ^ (k + 1) * of ℤ G a⁻¹ := by
      have h := key (k + 1)
      rw [Finset.sum_range_succ', pow_zero] at h
      rw [← h]; abel
    have hpow : ∀ i : ℕ, y ^ (i + 1) ∈ Sp g (k + 1) := by
      intro i
      induction i with
      | zero => rw [zero_add, pow_one]; exact hyS
      | succ i ih => rw [pow_succ]; exact Sp_mul g ih hyS
    rw [e]
    refine add_mem (Submodule.sum_mem _ fun i _ => hpow i) (Submodule.mem_sup_right ?_)
    show y ^ (k + 1) * of ℤ G a⁻¹ ∈ augIdeal G ^ (k + 1)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hyD _)

theorem aug_le_Sp' (hgen : Subgroup.closure (Set.range g) = ⊤) {n : ℕ} (hn : 1 ≤ n)
    {y : MonoidAlgebra ℤ G} (hy : y ∈ augIdeal G) : y ∈ Sp g n :=
  CentralRoot.augIdeal_induction (p := fun y => y ∈ Sp g n) hy (zero_mem _)
    (sub_one_mem_Sp' g hgen hn) (fun _ h => neg_mem h) (fun _ _ h h' => add_mem h h')

/-- The generators `ψ(X_w)`, `1 ≤ |w| < n`. -/
def gensF (n : ℕ) : Set (MonoidAlgebra ℤ G) :=
  {y | ∃ w : FreeMonoid (Fin d), w ≠ 1 ∧ w.length < n ∧ y = psi g (single w 1)}

omit [NeZero d] in
theorem one_le_length {w : FreeMonoid (Fin d)} (hw : w ≠ 1) : 1 ≤ w.length := by
  rcases Nat.eq_zero_or_pos w.length with h0 | h0
  · exfalso; apply hw
    have h0' : w.toList = [] := List.length_eq_zero_iff.mp h0
    rw [← FreeMonoid.ofList_toList w, h0']; rfl
  · exact h0

theorem psi_mem_aug {w : FreeMonoid (Fin d)} (hw : w ≠ 1) : psi g (single w 1) ∈ augIdeal G :=
  Ideal.pow_le_self (by have := one_le_length hw; omega) (psi_single_mem g w 1)

/-- `Δ ⊆ span(ψ(X_w) : 1 ≤ |w| < n) + Δ^n`. -/
theorem aug_le_spanF (hgen : Subgroup.closure (Set.range g) = ⊤) {n : ℕ} (hn : 1 ≤ n)
    {y : MonoidAlgebra ℤ G} (hy : y ∈ augIdeal G) :
    y ∈ Submodule.span ℤ (gensF g n) ⊔ (augIdeal G ^ n).restrictScalars ℤ := by
  refine (show Sp g n ≤ _ from sup_le ?_ le_sup_right) (aug_le_Sp' g hgen hn hy)
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  by_cases hlt : w.length < n
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨w, hw, hlt, rfl⟩)
  · exact Submodule.mem_sup_right (Ideal.pow_le_pow_right (not_lt.mp hlt) (psi_single_mem g w 1))

theorem span_gensF_le_aug (n : ℕ) : Submodule.span ℤ (gensF g n) ≤ Del G := by
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, -, rfl⟩
  exact psi_mem_aug g hw

/-- `Δ/Δ^n` is a finitely generated `ℤ`-module. -/
theorem finite_Qn (hgen : Subgroup.closure (Set.range g) = ⊤) {n : ℕ} (hn : 1 ≤ n) :
    Module.Finite ℤ (Qn G n) := by
  let S : Set (Qn G n) := (fun l : List (Fin d) => toQ n (psi g (single (FreeMonoid.ofList l) 1))) ''
    {l | l.length < n}
  have hS : S.Finite := (List.finite_length_lt (Fin d) n).image _
  have hspan : ∀ s ∈ Submodule.span ℤ (gensF g n), toQ n s ∈ Submodule.span ℤ S := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, -, hlt, rfl⟩ := hx
      exact Submodule.subset_span ⟨w.toList, hlt, by simp only [FreeMonoid.ofList_toList]⟩
    | zero => rw [toQ_zero]; exact zero_mem _
    | add x y hx hy ihx ihy =>
      rw [toQ_add (span_gensF_le_aug g n hx) (span_gensF_le_aug g n hy)]; exact add_mem ihx ihy
    | smul c x hx ih =>
      rw [toQ_smul c (span_gensF_le_aug g n hx)]; exact Submodule.smul_mem _ c ih
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨S, hS, eq_top_iff.mpr fun q _ => ?_⟩
  obtain ⟨y, hy, rfl⟩ := toQ_surj q
  obtain ⟨s, hs, δ, hδ, rfl⟩ := Submodule.mem_sup.mp (aug_le_spanF g hgen hn hy)
  have hsD : s ∈ augIdeal G := span_gensF_le_aug g n hs
  rw [toQ_add hsD (Ideal.pow_le_self (by omega) hδ), toQ_eq_zero (by omega) hδ, add_zero]
  exact hspan s hs

end Fin

/-! ## Exact membership -/

theorem checkHom_spec (T : Trace) [NeZero T.d] (H : HomCert) (h : checkHom T H = true) :
    (∀ κ ∈ H.funcs, κ.2 < T.n) ∧
    (∀ i < T.F.length, (H.rows.getD i ([], 0)).2 ≠ 0) ∧
    (∀ i < T.F.length, ∀ j < T.F.length,
      ∑ k ∈ Finset.range H.funcs.length, (H.rows.getD i ([], 0)).1.getD k 0 *
        colVal T.d (H.funcs.getD k ([], 0)) (T.F.getD j 0) =
      if i = j then (H.rows.getD i ([], 0)).2 else 0) := by
  simp only [checkHom, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨hK, hrows⟩ := h
  refine ⟨hK, fun i hi => (hrows i hi).1, fun i hi j hj => ?_⟩
  rw [← lsum_eq]; exact (hrows i hi).2 j hj

theorem check_F_pos (T : Trace) (members : List ℕ) (h : check T members = true) :
    ∀ f ∈ T.F, 0 < f := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact h.1.1.1.2

/-- **Exact membership with free columns.** Suppose `check` accepts the trace and `checkHom` the
certificate. Let `G` be a group and `g : Fin d → G` such that:
* the `g j` generate `G`, and the relators listed in the trace hold at `g`;
* every functional `(a, K)` of the certificate comes from a homomorphism `φ : G → ℤ` with
  `φ(g_j) = a_j`;
* the test element `w_t(g) − 1` has `p`-power order in `Δ/Δ^n` (`hord`).

Then `w_t(g) ∈ D_n(G)`. Generator `i` of a word (1-based) is `g ⟨i − 1⟩`. -/
theorem check_mem_D_hom (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (H : HomCert) (hH : checkHom T H = true)
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hφ : ∀ k < H.funcs.length, ∃ φ : G →* Multiplicative ℤ,
      ∀ j : Fin T.d, Multiplicative.toAdd (φ (g j)) = (H.funcs.getD k ([], 0)).1.getD j.val 0)
    (t : ℕ) (ht : t ∈ members)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) • (of ℤ G (gword g (findWord t T.tests)) - 1) ∈
      augIdeal G ^ T.n) :
    gword g (findWord t T.tests) ∈ GroupDimension.D T.n G := by
  obtain ⟨hp, hE, hn⟩ := check_params T members hc
  have hn0 : T.n ≠ 0 := by omega
  have hFpos := check_F_pos T members hc
  obtain ⟨hK, hDg, hCM⟩ := checkHom_spec T H hH
  have : Module.Finite ℤ (Qn G T.n) := finite_Qn g hgen (n := T.n) (by omega)
  have hD0 : ((T.p ^ T.E : ℕ) : ℤ) ≠ 0 := by
    have : 0 < T.p ^ T.E := Nat.pow_pos (by omega)
    exact_mod_cast this.ne'
  have hDp : ((T.p ^ T.E : ℕ) : ℤ) = (T.p : ℤ) ^ T.E := Nat.cast_pow T.p T.E
  -- the free columns in `Q`
  let nf := T.F.length
  have hFget : ∀ i < nf, 0 < T.F.getD i 0 := fun i hi => by
    apply hFpos; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  let v : Fin nf → Qn G T.n := fun i => toQ T.n (psi g (e T.d (T.F.getD i 0)))
  let Fb := Submodule.span ℤ (Set.range v)
  -- `ψ(Fspan) ⊆ Δ`, with image in `F̄`
  have hFspan : ∀ φ' ∈ Fspan T.d T.F, psi g φ' ∈ augIdeal G ∧ toQ T.n (psi g φ') ∈ Fb := by
    intro φ' hφ'
    induction hφ' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
      have hget := List.getD_eq_getElem T.F 0 hi
      refine ⟨psi_e_mem g (hFpos _ hf), Submodule.subset_span ⟨⟨i, hi⟩, ?_⟩⟩
      show toQ T.n (psi g (e T.d (T.F.getD i 0))) = _
      rw [hget]
    | zero => rw [map_zero]; exact ⟨zero_mem _, by rw [toQ_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      rw [map_add]; exact ⟨add_mem hx.1 hy.1, by rw [toQ_add hx.1 hy.1]; exact add_mem hx.2 hy.2⟩
    | smul c x _ hx =>
      rw [map_zsmul]
      exact ⟨Submodule.smul_of_tower_mem _ c hx.1,
        by rw [toQ_smul c hx.1]; exact Submodule.smul_mem _ c hx.2⟩
  -- (X) in `Q`
  have hX : ∀ q : Qn G T.n, ∃ f ∈ Fb, ∃ r : Qn G T.n,
      ((T.p : ℤ) ^ (T.E - 1)) • q = f + ((T.p : ℤ) ^ T.E) • r := by
    intro q
    obtain ⟨y, hy, rfl⟩ := toQ_surj q
    obtain ⟨s, hs, δ, hδ, rfl⟩ := Submodule.mem_sup.mp (aug_le_spanF g hgen (n := T.n) (by omega) hy)
    have hsD : s ∈ augIdeal G := span_gensF_le_aug g T.n hs
    rw [toQ_add hsD (Ideal.pow_le_self hn0 hδ), toQ_eq_zero hn0 hδ, add_zero]
    clear hy hδ
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, -, rfl⟩ := hx
      obtain ⟨l, hl, φ', hφ', heq⟩ := Submodule.mem_sup.mp ((check_sound T members hc).2 w hw)
      obtain ⟨a, ha, b, hab⟩ := psi_Lt g hrel hl
      obtain ⟨hφD, hφF⟩ := hFspan φ' hφ'
      have hxD := psi_mem_aug g hw
      have hrx : ((T.p ^ (T.E - 1) : ℕ) : ℤ) • psi g (single w 1) - psi g φ' = a + ((T.p ^ T.E : ℕ) : ℤ) • b := by
        rw [← map_zsmul, ← heq, map_add, hab]; abel
      have hb : b ∈ augIdeal G :=
        mem_aug_of_eq hn0 hD0 (sub_mem (Submodule.smul_of_tower_mem _ _ hxD) hφD) ha hrx
      refine ⟨toQ T.n (psi g φ'), hφF, toQ T.n b, ?_⟩
      have h1 : ((T.p : ℤ) ^ (T.E - 1)) • toQ T.n (psi g (single w 1)) =
          toQ T.n (((T.p ^ (T.E - 1) : ℕ) : ℤ) • psi g (single w 1)) := by
        rw [toQ_smul _ hxD, Nat.cast_pow]
      rw [h1, show ((T.p ^ (T.E - 1) : ℕ) : ℤ) • psi g (single w 1) = psi g φ' + (a + ((T.p ^ T.E : ℕ) : ℤ) • b) by
        rw [← hrx]; abel, toQ_add hφD (add_mem (Ideal.pow_le_self hn0 ha)
          (Submodule.smul_of_tower_mem _ ((T.p ^ T.E : ℕ) : ℤ) hb)), toQ_add (Ideal.pow_le_self hn0 ha)
          (Submodule.smul_of_tower_mem _ ((T.p ^ T.E : ℕ) : ℤ) hb), toQ_eq_zero hn0 ha, zero_add, toQ_smul ((T.p ^ T.E : ℕ) : ℤ) hb, hDp]
    | zero => exact ⟨0, zero_mem _, 0, by rw [toQ_zero, smul_zero, smul_zero, add_zero]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨f1, hf1, r1, e1⟩ := ihx (span_gensF_le_aug g T.n hx)
      obtain ⟨f2, hf2, r2, e2⟩ := ihy (span_gensF_le_aug g T.n hy)
      refine ⟨f1 + f2, add_mem hf1 hf2, r1 + r2, ?_⟩
      rw [toQ_add (span_gensF_le_aug g T.n hx) (span_gensF_le_aug g T.n hy), smul_add, e1, e2,
        smul_add]; abel
    | smul c x hx ih =>
      obtain ⟨f1, hf1, r1, e1⟩ := ih (span_gensF_le_aug g T.n hx)
      refine ⟨c • f1, Submodule.smul_mem _ c hf1, c • r1, ?_⟩
      rw [toQ_smul c (span_gensF_le_aug g T.n hx), smul_comm, e1, smul_add, smul_comm c]
  -- `F̄` meets the torsion trivially
  choose! φ hφ' using hφ
  have hFt : ∀ f ∈ Fb, ∀ k : ℕ, 0 < k → (k : ℤ) • f = 0 → f = 0 := by
    intro f hf k hk hkf
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hf
    let a' : ℕ → ℤ := fun j => if h : j < nf then a ⟨j, h⟩ else 0
    have hzero : ∀ k' < H.funcs.length, ∑ j ∈ Finset.range nf,
        a' j * colVal T.d (H.funcs.getD k' ([], 0)) (T.F.getD j 0) = 0 := by
      intro k' hk'
      have hKk : (H.funcs.getD k' ([], 0)).2 < T.n := by
        apply hK; rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
      have h0 : nuQ (φ k') _ hKk (∑ i, a i • v i) = 0 := by
        have h1 : (k : ℚ) * nuQ (φ k') _ hKk (∑ i, a i • v i) = 0 := by
          have := congrArg (nuQ (φ k') _ hKk) hkf
          rw [map_zsmul, map_zero, zsmul_eq_mul] at this
          exact_mod_cast this
        exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hk.ne')
      rw [map_sum] at h0
      have hval_i : ∀ i : Fin nf, nuQ (φ k') _ hKk (a i • v i) =
          ((a i * colVal T.d (H.funcs.getD k' ([], 0)) (T.F.getD i 0) : ℤ) : ℚ) := by
        intro i
        rw [map_zsmul, show v i = toQ T.n (psi g (e T.d (T.F.getD i 0))) from rfl,
          nuQ_toQ _ hKk (psi_e_mem g (hFget i i.2)),
          show e T.d (T.F.getD i 0) = single (wordAt T.d (T.F.getD i 0)) 1 from rfl,
          nu_psi (φ k') g _ (hφ' k' hk'), colVal, zsmul_eq_mul]
        push_cast; ring
      simp only [hval_i] at h0
      rw [← Fin.sum_univ_eq_sum_range (fun j => a' j * colVal T.d (H.funcs.getD k' ([], 0))
        (T.F.getD j 0)) nf]
      have h2 : ((∑ i : Fin nf, a i * colVal T.d (H.funcs.getD k' ([], 0)) (T.F.getD i 0) : ℤ) :
          ℚ) = 0 := by exact_mod_cast h0
      have h3 := (Int.cast_eq_zero (α := ℚ)).mp h2
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h3
      simp only [a', dif_pos i.2]
    have ha0 := eq_zero_of_cert (nf := nf) (nk := H.funcs.length)
      (fun i k' => (H.rows.getD i ([], 0)).1.getD k' 0)
      (fun k' j => colVal T.d (H.funcs.getD k' ([], 0)) (T.F.getD j 0))
      (fun i => (H.rows.getD i ([], 0)).2) hDg hCM a' hzero
    have : a = 0 := by
      funext i
      have := ha0 i i.2
      simpa [a', dif_pos i.2] using this
    simp [this]
  -- the test element
  obtain ⟨a, ha, b, e⟩ := check_group T members hc g hrel t ht
  have hb : b ∈ augIdeal G := mem_aug_of_eq hn0 hD0 (of_sub_one_mem_augIdeal _) ha e
  have hx0 : toQ T.n (of ℤ G (gword g (findWord t T.tests)) - 1) = 0 := by
    refine TraceCert.eq_zero_of_mem_pow T.p (by omega) T.E hE Fb hX hFt _ ?_ ?_
    · refine ⟨toQ T.n b, ?_⟩
      rw [e, toQ_add (Ideal.pow_le_self hn0 ha) (Submodule.smul_of_tower_mem _ ((T.p ^ T.E : ℕ) : ℤ) hb),
        toQ_eq_zero hn0 ha, zero_add, toQ_smul ((T.p ^ T.E : ℕ) : ℤ) hb, hDp]
    · obtain ⟨m, hm⟩ := hord
      refine ⟨m, ?_⟩
      rw [← toQ_smul _ (of_sub_one_mem_augIdeal _)]
      exact toQ_eq_zero hn0 hm
  rw [mem_D]
  exact (toQ_eq_zero_iff (of_sub_one_mem_augIdeal _)).1 hx0

/-- The functionals' `a` are among the polynomial maps `maps` (kernel-checked), so homomorphisms for
the maps give homomorphisms for the functionals. -/
theorem homs_of_maps {G : Type*} [Group G] {d : ℕ} (g : Fin d → G) (maps : List (List ℤ))
    (H : HomCert) (hm : H.funcs.all (fun κ => maps.any (fun a => a == κ.1)) = true)
    (h : ∀ a ∈ maps, ∃ φ : G →* Multiplicative ℤ,
      ∀ j : Fin d, Multiplicative.toAdd (φ (g j)) = a.getD j.val 0) :
    ∀ k < H.funcs.length, ∃ φ : G →* Multiplicative ℤ,
      ∀ j : Fin d, Multiplicative.toAdd (φ (g j)) = (H.funcs.getD k ([], 0)).1.getD j.val 0 := by
  intro k hk
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hm
  have hκ : H.funcs.getD k ([], 0) ∈ H.funcs := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  obtain ⟨a, ha, hak⟩ := hm _ hκ
  rw [← hak]
  exact h a ha

/-! ## The presented group -/

section Pres

/-- `gword` commutes with homomorphisms. -/
theorem map_gword {d : ℕ} [NeZero d] {G H : Type*} [Group G] [Group H] (ρ : G →* H)
    (g : Fin d → G) (w : List (ℕ × ℤ)) : ρ (gword g w) = gword (ρ ∘ g) w := by
  simp only [gword, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_apply, map_zpow]

/-- The relators `allRels` in the free group on `Fin d`. -/
def relSet (d : ℕ) [NeZero d] (allRels : List (List (ℕ × ℤ))) : Set (FreeGroup (Fin d)) :=
  {x | ∃ r ∈ allRels, x = gword FreeGroup.of r}

/-- `Σ e · a_{(i−1) mod d}` over a word: `φ_a` of the word. -/
def expSum (d : Nat) (a : List Int) (w : List (Nat × Int)) : Int :=
  (w.map fun f => f.2 * a.getD ((f.1 - 1) % d) 0).sum

theorem toAdd_gword {d : ℕ} [NeZero d] (a : List ℤ) (w : List (ℕ × ℤ)) :
    Multiplicative.toAdd (gword (fun j : Fin d => Multiplicative.ofAdd (a.getD j.val 0)) w) =
      expSum d a w := by
  induction w with
  | nil => rfl
  | cons f w ih =>
    simp only [gword, List.map_cons, List.prod_cons, toAdd_mul, toAdd_zpow, toAdd_ofAdd,
      expSum, List.sum_cons, smul_eq_mul] at ih ⊢
    rw [ih]; rfl

/-- The presentation check: the trace's relators are among `allRels`, and every functional's
`a` has exponent sum `0` on every relator (so `g_j ↦ a_j` is a homomorphism of the presented
group to `ℤ`). -/
def checkPres (T : Trace) (H : HomCert) (allRels : List (List (ℕ × ℤ))) : Bool :=
  T.rels.all (fun r => allRels.any (fun r' => r' == r.2)) &&
  H.funcs.all (fun κ => allRels.all (fun r => expSum T.d κ.1 r == 0))

/-- **Exact membership in the presented group.** If `check`, `checkHom` and `checkPres` pass, then
in `G = ⟨x_1, …, x_d | allRels⟩` every test claimed in whose element has `p`-power order in
`Δ/Δ^n` (`hord`) lies in `D_n(G)`. -/
theorem check_mem_D_pres (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (H : HomCert) (hH : checkHom T H = true) (allRels : List (List (ℕ × ℤ)))
    (hP : checkPres T H allRels = true) (t : ℕ) (ht : t ∈ members)
    (hord : ∃ m : ℕ, ((T.p : ℤ) ^ m) •
      (of ℤ (PresentedGroup (relSet T.d allRels))
        (gword (PresentedGroup.of (rels := relSet T.d allRels)) (findWord t T.tests)) - 1) ∈
      augIdeal (PresentedGroup (relSet T.d allRels)) ^ T.n) :
    gword (PresentedGroup.of (rels := relSet T.d allRels)) (findWord t T.tests) ∈
      GroupDimension.D T.n (PresentedGroup (relSet T.d allRels)) := by
  simp only [checkPres, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hP
  obtain ⟨hsub, hexp⟩ := hP
  refine check_mem_D_hom T members hc H hH (PresentedGroup.of (rels := relSet T.d allRels)) ?_
    (PresentedGroup.closure_range_of _) ?_ t ht hord
  · intro r hr
    obtain ⟨r', hr', hrr⟩ := hsub r hr
    have e : (PresentedGroup.of : Fin T.d → PresentedGroup (relSet T.d allRels)) =
        PresentedGroup.mk _ ∘ FreeGroup.of := rfl
    rw [e, ← map_gword]
    exact PresentedGroup.one_of_mem ⟨r', hr', by rw [hrr]⟩
  · intro k hk
    set a := (H.funcs.getD k ([], 0)).1
    have hκ : H.funcs.getD k ([], 0) ∈ H.funcs := by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    let f : Fin T.d → Multiplicative ℤ := fun j => Multiplicative.ofAdd (a.getD j.val 0)
    have hrels : ∀ r ∈ relSet T.d allRels, FreeGroup.lift f r = 1 := by
      rintro _ ⟨r, hr, rfl⟩
      rw [map_gword]
      have e : (FreeGroup.lift f ∘ FreeGroup.of) = f := funext fun j => FreeGroup.lift_apply_of
      rw [e]
      apply Multiplicative.toAdd.injective
      rw [toAdd_gword, toAdd_one]
      exact hexp _ hκ r hr
    exact ⟨PresentedGroup.toGroup hrels, fun j => by rw [PresentedGroup.toGroup.of]; rfl⟩

end Pres

end GroupDimension.TraceReplay
