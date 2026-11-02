module

public import Mathlib

@[expose] public section

/-!
# Soundness of membership traces (MATH-314, item 1; cflint-fast-core `cert/TRACE.md`)

A trace proves `x ∈ J_n` for the ideal `J_n ⊆ A_n^+` of the truncated Magnus algebra. The checker
`cert/trace` verifies:

* every vector of the trace lies in `L_k = J_k + p^E A_k^+` (steps 1–4 below: the lines are
  combinations, the shifts follow Lemma N1);
* a membership witness: `x ∈ L_n`;
* exactness (X): `p^{E-1} e_c ∈ S + ℤ^F + p^E A_n^+` for every column `c`;
* functionals `ν` (the products of polynomial maps, checked to vanish on `J_{w+1}` for each map) whose
  values on the monomials `X_f`, `f ∈ F`, have rank `|F|` modulo a prime, so that `a ↦ ν (Σ a_f X_f)` is
  injective on `ℤ^F` (the hypothesis `hinj`). That `ν` is defined on `Q` (Passi, `ℤ[F]/Δⁿ ≅ A_n`) is not
  formalized here.

This file proves, in an abstract setting, that these checks imply `x ∈ J_n` whenever the image of
`x` in `Q = A_n^+ / J_n` is killed by a power of `p` (`TraceCert.eq_zero_of_trace`). The rank of
`Q` is not used: the functionals give `F̄ ∩ T = 0` directly, and Vasconcelos' theorem (a surjective
endomorphism of a finitely generated module is injective, `OrzechProperty`) replaces the rank count.
-/

namespace TraceCert

/-! ## Steps 1–4: the lines of a trace stay in `L` -/

section Lines

variable {A : Type*} [AddCommGroup A]

/-- Step 3. A line `u · (g + Σ cᵢ vᵢ)` with `g` and the `vᵢ` in `L` is in `L`. -/
theorem line_mem (L : AddSubgroup A) (u : ℤ) (g : A) (cs : List (ℤ × A)) (hg : g ∈ L)
    (hc : ∀ c ∈ cs, c.2 ∈ L) : u • (g + (cs.map fun c => c.1 • c.2).sum) ∈ L := by
  refine L.zsmul_mem (L.add_mem hg ?_) u
  refine L.list_sum_mem ?_
  intro y hy
  obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hy
  exact L.zsmul_mem (hc c hc') c.1

/-- Step 2 (Lemma N1, the easy direction), abstractly. `π : A → B` is the truncation
`A_k → A_{k-1}`, `s` views an element of `A_{k-1}` in `A_k`, and `f` is a shift `a_j · _` or
`_ · a_j`. `f` kills the kernel of `π` (degree `k − 1` times `a_j` is `0` in `A_k`), `f` maps `L`
into `L`, and `L` maps onto `L'`. Then `f (s b) ∈ L` for every `b ∈ L'`. -/
theorem shift_mem {B : Type*} [AddCommGroup B] (π : A →+ B) (s : B → A) (hs : ∀ b, π (s b) = b)
    (f : A →+ A) (hf : ∀ a, π a = 0 → f a = 0) (L : AddSubgroup A) (L' : AddSubgroup B)
    (hfL : ∀ a ∈ L, f a ∈ L) (honto : ∀ b ∈ L', ∃ a ∈ L, π a = b) (b : B) (hb : b ∈ L') :
    f (s b) ∈ L := by
  obtain ⟨a, ha, rfl⟩ := honto b hb
  have : f (s (π a)) = f a := by
    have h0 : f (s (π a) - a) = 0 := hf _ (by rw [map_sub, hs, sub_self])
    rwa [map_sub, sub_eq_zero] at h0
  rw [this]
  exact hfL a ha

end Lines

/-! ## Steps 5–6: exactness, in `Q = A_n^+ / J_n` -/

section Exactness

variable {Q : Type*} [AddCommGroup Q] [Module.Finite ℤ Q]

/-- A finitely generated `ℤ`-module on which multiplication by `p` is onto: it is also injective
(Vasconcelos; `OrzechProperty` for commutative rings). -/
theorem smul_injective_of_surjective {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] (p : ℤ)
    (h : Function.Surjective fun x : M => p • x) : Function.Injective fun x : M => p • x := by
  let f : M →ₗ[ℤ] M := p • LinearMap.id
  have hf : ∀ x, f x = p • x := fun x => rfl
  have hs : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, by rw [hf]; exact hx⟩
  have hi := OrzechProperty.injective_of_surjective_endomorphism f hs
  intro a b hab
  exact hi (by rw [hf, hf]; exact hab)

/-- Step 5. Let `F̄ ⊆ Q` meet the torsion trivially and suppose (X):
`p^{E-1} q ∈ F̄ + p^E Q` for every `q`. Then `p^{E-1}` kills every element of `p`-power order. -/
theorem pow_pred_smul_eq_zero (p : ℕ) (hp : p ≠ 0) (E : ℕ) (hE : 1 ≤ E) (Fb : Submodule ℤ Q)
    (hX : ∀ q : Q, ∃ f ∈ Fb, ∃ r : Q, ((p : ℤ) ^ (E - 1)) • q = f + ((p : ℤ) ^ E) • r)
    (hF : ∀ f ∈ Fb, ∀ k : ℕ, 0 < k → (k : ℤ) • f = 0 → f = 0)
    (y : Q) (m : ℕ) (hy : ((p : ℤ) ^ m) • y = 0) : ((p : ℤ) ^ (E - 1)) • y = 0 := by
  set π := Fb.mkQ
  -- M = p^{E-1} (Q / F̄), a finitely generated module on which p· is onto
  let M : Submodule ℤ (Q ⧸ Fb) := LinearMap.range (((p : ℤ) ^ (E - 1)) • LinearMap.id)
  have : IsNoetherian ℤ (Q ⧸ Fb) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  have : Module.Finite ℤ M := Module.IsNoetherian.finite ℤ M
  have hpE : (p : ℤ) ^ E = (p : ℤ) * (p : ℤ) ^ (E - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hsurj : Function.Surjective fun x : M => (p : ℤ) • x := by
    rintro ⟨z, ⟨q', rfl⟩⟩
    obtain ⟨q, rfl⟩ := Fb.mkQ_surjective q'
    obtain ⟨f, hf, r, hr⟩ := hX q
    refine ⟨⟨((p : ℤ) ^ (E - 1)) • π r, ⟨π r, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    simp only [LinearMap.smul_apply, LinearMap.id_apply, SetLike.val_smul]
    have hf0 : Fb.mkQ f = 0 := by
      rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero Fb).2 hf
    rw [smul_smul, ← hpE, ← map_zsmul, ← map_zsmul, hr, map_add, hf0, zero_add]
  have hinj := smul_injective_of_surjective (M := M) (p : ℤ) hsurj
  -- w = p^{E-1} ȳ ∈ M has p-power order, so it is 0
  let w : M := ⟨((p : ℤ) ^ (E - 1)) • π y, ⟨π y, rfl⟩⟩
  have hw : w = 0 := by
    have key : ∀ j : ℕ, ((p : ℤ) ^ j) • w = 0 → w = 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        intro h
        apply ih
        apply hinj
        simp only [smul_zero]
        rw [smul_smul, ← pow_succ']
        exact h
    apply key m
    apply Subtype.ext
    simp only [w, SetLike.val_smul, Submodule.coe_zero, smul_smul]
    rw [mul_comm, ← smul_smul, ← map_zsmul, hy, map_zero, smul_zero]
  -- so p^{E-1} y ∈ F̄, and it is torsion
  have hmem : ((p : ℤ) ^ (E - 1)) • y ∈ Fb := by
    have : π (((p : ℤ) ^ (E - 1)) • y) = 0 := by
      have := congrArg Subtype.val hw
      simpa [w, map_zsmul] using this
    exact (Submodule.Quotient.mk_eq_zero Fb).1 this
  refine hF _ hmem (p ^ m) (pow_pos (Nat.pos_of_ne_zero hp) m) ?_
  rw [smul_comm]
  push_cast
  rw [hy, smul_zero]

/-- Step 6. With (X) and `F̄ ∩ T = 0`: an element of `p^E Q` of `p`-power order is `0`.
(For `x ∈ J_n + p^E A_n^+` its image lies in `p^E Q`.) -/
theorem eq_zero_of_mem_pow (p : ℕ) (hp : p ≠ 0) (E : ℕ) (hE : 1 ≤ E) (Fb : Submodule ℤ Q)
    (hX : ∀ q : Q, ∃ f ∈ Fb, ∃ r : Q, ((p : ℤ) ^ (E - 1)) • q = f + ((p : ℤ) ^ E) • r)
    (hF : ∀ f ∈ Fb, ∀ k : ℕ, 0 < k → (k : ℤ) • f = 0 → f = 0)
    (x : Q) (hx : ∃ y : Q, x = ((p : ℤ) ^ E) • y) (hord : ∃ m : ℕ, ((p : ℤ) ^ m) • x = 0) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨m, hm⟩ := hord
  have hy : ((p : ℤ) ^ (m + E)) • y = 0 := by rw [pow_add, ← smul_smul]; exact hm
  have h := pow_pred_smul_eq_zero p hp E hE Fb hX hF y (m + E) hy
  have hpE : (p : ℤ) ^ E = (p : ℤ) * (p : ℤ) ^ (E - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpE, ← smul_smul, h, smul_zero]

/-- `F̄ ∩ T = 0` from functionals: if `ν : Q → ℤ^κ` is additive and `a ↦ ν (Σ aᵢ vᵢ)` is injective,
then the span of the `vᵢ` meets the torsion trivially (`ℤ^κ` is torsion-free). In the trace
checker the `vᵢ` are the images in `Q` of the monomials `X_f`, `f ∈ F` (the free columns), and `ν` the
products of polynomial maps. -/
omit [Module.Finite ℤ Q] in
theorem span_torsion_free {ι κ : Type*} [Fintype ι] (v : ι → Q) (ν : Q →+ (κ → ℤ))
    (hinj : Function.Injective fun a : ι → ℤ => ν (∑ i, a i • v i)) :
    ∀ f ∈ Submodule.span ℤ (Set.range v), ∀ k : ℕ, 0 < k → (k : ℤ) • f = 0 → f = 0 := by
  intro f hf k hk hkf
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hf
  have h0 : ν (∑ i, a i • v i) = 0 := by
    have h1 : (k : ℤ) • ν (∑ i, a i • v i) = 0 := by rw [← map_zsmul, hkf, map_zero]
    funext j
    have h2 := congrFun h1 j
    rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
    rw [Pi.zero_apply]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (by exact_mod_cast hk.ne')
    · exact h
  have : a = 0 := hinj (by simpa using h0)
  simp [this]

/-- Steps 5–6 together, as the trace checker uses them. `Q = A_n^+ / J_n` is finitely generated,
`v` are the images of the free columns, `ν` the polynomial-map functionals (injective on `ℤ^F`),
(X) holds for `F̄ = span v`, and `x` lies in `p^E Q` (the membership witness) with `p`-power order.
Then `x = 0` in `Q`, i.e. the element lies in `J_n`. -/
theorem eq_zero_of_trace {ι κ : Type*} [Fintype ι] (p : ℕ) (hp : p ≠ 0) (E : ℕ) (hE : 1 ≤ E)
    (v : ι → Q) (ν : Q →+ (κ → ℤ)) (hinj : Function.Injective fun a : ι → ℤ => ν (∑ i, a i • v i))
    (hX : ∀ q : Q, ∃ f ∈ Submodule.span ℤ (Set.range v), ∃ r : Q,
      ((p : ℤ) ^ (E - 1)) • q = f + ((p : ℤ) ^ E) • r)
    (x : Q) (hx : ∃ y : Q, x = ((p : ℤ) ^ E) • y) (hord : ∃ m : ℕ, ((p : ℤ) ^ m) • x = 0) :
    x = 0 :=
  eq_zero_of_mem_pow p hp E hE _ hX (span_torsion_free v ν hinj) x hx hord

end Exactness

end TraceCert
