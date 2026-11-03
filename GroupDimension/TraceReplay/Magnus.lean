module

public import GroupDimension.Basic
public import GroupDimension.CentralRoot
public import GroupDimension.TraceReplay.Sound

@[expose] public section

/-!
# From a replayed trace to the group ring (MATH-314, item 1: the Magnus link)

`TraceReplay.Sound` proves, for a trace that `check` accepts, statements in `R = ℤ⟨X_1..X_d⟩`:
`mt n w − 1 ∈ Lt = Jt + I_n + D·R`. Here we push them to the group ring. Let `G` be any group and
`g : Fin d → G` elements in which the trace's relators hold. The ring map

  `ψ : R → ℤ[G]`, `X_j ↦ g_j − 1`

sends `I_n` into `Δ^n` (a monomial of length `≥ n` goes to a product of `≥ n` elements of `Δ`),
`mt n w` to `w(g)` modulo `Δ^n` (each factor `Σ_{m<n} C(e,m) X_j^m` is the binomial series of
`(1 + X_j)^e`, cut below degree `n`, and `1 + ψ X_j = g_j`), hence `Jt` into `Δ^n` (the relators
are `1` in `G`), and `D·R` into `D·ℤ[G]`. So

  `w(g) − 1 ∈ Δ^n + D·ℤ[G]`   (`sub_one_mem_of_mem_Lt`, `check_group`),

and `w(g) ∈ D_n(G)` when the `D·R` part is absent (`mem_D_of_mem_Jt_sup_Ik`; unused by the pipeline,
since `check_sound` always lands in `Lt`, with the `D·R` part: `D_n` is reached by exactness,
`check_mem_D`). This is the easy
direction of §3.1 of the paper (`J_n ↦ Δ^n`), the one a certificate of membership needs; removing
`D·ℤ[G]` below completes it. `binom` (the checker's own generalised binomial coefficient) is
`Ring.choose` (`binom_eq_choose`).

Since `ε(Δ^n) = 0`, `w(g) − 1 ∈ Δ^n + D·ℤ[G]` is the same as `w(g) − 1 ∈ Δ^n + D·Δ`. It says
nothing when `Δ = Δ^2 + pΔ` (`H_1(G; 𝔽_p) = 0`, e.g. `G` of order prime to `p`), and it is `D_n`
membership as soon as `p^E Δ ⊆ Δ^n`; the intended case is `G` a finite `p`-group.

Removing `D·ℤ[G]` (exactness, `check_mem_D` at the end) needs `p^{E−1} Δ ⊆ Δ^n + p^E Δ` (the second
half of `check_sound`, pushed by `ψ`, which covers `Δ` modulo `Δ^n` only when the `g_j` generate
`G`), and that `Δ/Δ^n` has bounded `p`-power exponent (e.g. `x^{p^N} = 1` for all `x : G`, which
gives `p^N Δ ⊆ Δ^2`, hence `p^{N(n−1)} Δ ⊆ Δ^n`).
-/

namespace GroupDimension.TraceReplay

noncomputable section

open MonoidAlgebra

/-! ## `binom = Ring.choose` -/

theorem descProd_eq_eval (e : ℤ) (m : ℕ) : descProd e m = (descPochhammer ℤ m).eval e := by
  induction m with
  | zero => simp [descProd]
  | succ m ih =>
    rw [descProd, ih, descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast]

theorem fact_eq_factorial (m : ℕ) : fact m = m.factorial := by
  induction m with
  | zero => rfl
  | succ m ih => rw [fact, ih, Nat.factorial_succ]

/-- The checker's binomial coefficient is the generalised binomial coefficient of Mathlib. -/
theorem binom_eq_choose (e : ℤ) (m : ℕ) : binom e m = Ring.choose e m := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose e m
  rw [← Polynomial.eval_eq_smeval, ← descProd_eq_eval, nsmul_eq_mul] at h
  rw [binom, h, fact_eq_factorial]
  have h0 : ((m.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  exact Int.mul_ediv_cancel_left _ h0

/-! ## Truncated binomial series in a ring -/

section Series

variable {A : Type*} [Ring A]

/-- `Σ_{m<k} C(e, m) y^m`. -/
def bser (y : A) (k : ℕ) (e : ℤ) : A := ∑ m ∈ Finset.range k, Ring.choose e m • y ^ m

theorem bser_zero (y : A) (e : ℤ) : bser y 0 e = 0 := by simp [bser]

theorem bser_succ (y : A) (k : ℕ) (e : ℤ) :
    bser y (k + 1) e = bser y k e + Ring.choose e k • y ^ k := Finset.sum_range_succ _ _

theorem bser_one (y : A) (e : ℤ) : bser y 1 e = 1 := by
  rw [bser_succ, bser_zero, Ring.choose_zero_right, pow_zero, one_smul, zero_add]

theorem bser_at_zero (y : A) (k : ℕ) : bser y (k + 1) 0 = 1 := by
  induction k with
  | zero => exact bser_one y 0
  | succ k ih =>
    have h0 : Ring.choose (0 : ℤ) (k + 1) = 0 := by
      have := Ring.choose_natCast (R := ℤ) 0 (k + 1)
      simpa using this
    rw [bser_succ, ih, h0, zero_smul, add_zero]

/-- Pascal's rule, summed: `T_e · (1 + y) = T_{e+1} + C(e, k) y^{k+1}` for `T = bser y (k + 1)`. -/
theorem bser_mul (y : A) (e : ℤ) :
    ∀ k : ℕ, bser y (k + 1) e * (1 + y) = bser y (k + 1) (e + 1) + Ring.choose e k • y ^ (k + 1)
  | 0 => by
    rw [bser_one, bser_one, Ring.choose_zero_right, one_smul, one_mul, pow_one]
  | k + 1 => by
    rw [bser_succ y (k + 1) e, add_mul, bser_mul y e k, bser_succ y (k + 1) (e + 1),
      Ring.choose_succ_succ, add_smul, smul_mul_assoc, mul_add, mul_one, ← pow_succ, smul_add]
    abel

end Series

/-! ## The map `ψ : R → ℤ[G]` -/

section Psi

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] (g : Fin d → G)

/-- `X_j ↦ g_j − 1`. -/
def psi : R d →ₐ[ℤ] MonoidAlgebra ℤ G :=
  (MonoidAlgebra.lift _ _ _ (FreeMonoid.lift fun j => of ℤ G (g j) - 1) :
    MonoidAlgebra ℤ (FreeMonoid (Fin d)) →ₐ[ℤ] MonoidAlgebra ℤ G)

theorem psi_single (w : FreeMonoid (Fin d)) (a : ℤ) :
    psi g (single w a) = a • (w.toList.map fun j => of ℤ G (g j) - 1).prod := by
  rw [psi, MonoidAlgebra.lift_single, FreeMonoid.lift_apply]

theorem psi_single_pow (l : Fin d) (m : ℕ) :
    psi g (single (FreeMonoid.of l ^ m) 1) = (of ℤ G (g l) - 1) ^ m := by
  have : (single (FreeMonoid.of l ^ m) (1 : ℤ) : R d) = single (FreeMonoid.of l) 1 ^ m := by
    rw [MonoidAlgebra.single_pow, one_pow]
  rw [this, map_pow, psi_single, FreeMonoid.toList_of, List.map_singleton, List.prod_singleton,
    one_smul]

theorem list_prod_mem_pow (l : List (MonoidAlgebra ℤ G)) (h : ∀ x ∈ l, x ∈ augIdeal G) :
    l.prod ∈ augIdeal G ^ l.length := by
  induction l with
  | nil => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | cons x t ih =>
    rw [List.prod_cons, List.length_cons, add_comm]
    have hx : x ∈ augIdeal G ^ 1 := by rw [Submodule.pow_one]; exact h x (by simp)
    exact mul_mem_augIdeal_pow hx (ih fun y hy => h y (by simp [hy]))

theorem psi_single_mem (w : FreeMonoid (Fin d)) (a : ℤ) :
    psi g (single w a) ∈ augIdeal G ^ w.length := by
  rw [psi_single]
  refine Submodule.smul_of_tower_mem _ a ?_
  have := list_prod_mem_pow (w.toList.map fun j => of ℤ G (g j) - 1) (fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact of_sub_one_mem_augIdeal _)
  rw [List.length_map] at this
  exact this

theorem psi_Ik {k : ℕ} {x : R d} (hx : x ∈ Ik d k) : psi g x ∈ augIdeal G ^ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact Ideal.pow_le_pow_right hw (psi_single_mem g w 1)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ a hx

theorem psi_S (k j : ℕ) (e : ℤ) : psi g (S k j e) = bser (of ℤ G (g (letter d j)) - 1) k e := by
  simp only [S, bser, map_sum, map_smul, psi_single_pow, binom_eq_choose]

/-- `Σ_{m<k} C(e, m) (h − 1)^m ≡ h^e` modulo `Δ^k`. -/
theorem bser_sub_mem (h : G) (k : ℕ) (e : ℤ) :
    bser (of ℤ G h - 1) k e - of ℤ G (h ^ e) ∈ augIdeal G ^ k := by
  rcases k with _ | k
  · simp [Submodule.pow_zero, Ideal.one_eq_top]
  set y := of ℤ G h - 1
  have hy : 1 + y = of ℤ G h := by simp only [y]; abel
  have hZ : ∀ e' : ℤ, Ring.choose e' k • y ^ (k + 1) ∈ augIdeal G ^ (k + 1) := fun e' =>
    Submodule.smul_of_tower_mem _ _ (Ideal.pow_mem_pow (of_sub_one_mem_augIdeal h) _)
  have hinv : of ℤ G h * of ℤ G h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  induction e using Int.induction_on with
  | zero => rw [bser_at_zero, zpow_zero, map_one, sub_self]; exact zero_mem _
  | succ i ih =>
    have hQ := bser_mul y (i : ℤ) k
    rw [hy] at hQ
    have e1 : bser y (k + 1) ((i : ℤ) + 1) - of ℤ G (h ^ ((i : ℤ) + 1)) =
        (bser y (k + 1) (i : ℤ) - of ℤ G (h ^ (i : ℤ))) * of ℤ G h
          - Ring.choose (i : ℤ) k • y ^ (k + 1) := by
      rw [zpow_add_one, map_mul, sub_mul, hQ]; abel
    rw [e1]
    exact sub_mem (Ideal.mul_mem_right _ _ ih) (hZ _)
  | pred i ih =>
    have hQ := bser_mul y (-(i : ℤ) - 1) k
    rw [hy, sub_add_cancel] at hQ
    have hX : bser y (k + 1) (-(i : ℤ) - 1) =
        (bser y (k + 1) (-(i : ℤ)) + Ring.choose (-(i : ℤ) - 1) k • y ^ (k + 1)) * of ℤ G h⁻¹ := by
      rw [← hQ, mul_assoc, hinv, mul_one]
    have hW : of ℤ G (h ^ (-(i : ℤ) - 1)) = of ℤ G (h ^ (-(i : ℤ))) * of ℤ G h⁻¹ := by
      rw [← map_mul, ← zpow_neg_one, ← zpow_add, sub_eq_add_neg]
    rw [hX, hW]
    have e1 : (bser y (k + 1) (-(i : ℤ)) + Ring.choose (-(i : ℤ) - 1) k • y ^ (k + 1)) * of ℤ G h⁻¹
        - of ℤ G (h ^ (-(i : ℤ))) * of ℤ G h⁻¹ =
        (bser y (k + 1) (-(i : ℤ)) - of ℤ G (h ^ (-(i : ℤ)))) * of ℤ G h⁻¹
          + (Ring.choose (-(i : ℤ) - 1) k • y ^ (k + 1)) * of ℤ G h⁻¹ := by
      noncomm_ring
    rw [e1]
    exact add_mem (Ideal.mul_mem_right _ _ ih) (Ideal.mul_mem_right _ _ (hZ _))

/-- A flat word evaluated in `G` (generators `1..d`; other indices read modulo `d`, exactly as in `mt`). -/
def gword (w : List (ℕ × ℤ)) : G := (w.map fun f => g (letter d (f.1 - 1)) ^ f.2).prod

/-- `ψ (mt k w) ≡ w(g)` modulo `Δ^k`. -/
theorem psi_mt_sub_mem (k : ℕ) (w : List (ℕ × ℤ)) :
    psi g (mt d k w) - of ℤ G (gword g w) ∈ augIdeal G ^ k := by
  induction w with
  | nil =>
    simp only [mt, gword, List.map_nil, List.prod_nil, map_one, sub_self]; exact zero_mem _
  | cons f t ih =>
    simp only [mt, gword, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, map_mul, psi_S]
    set a := bser (of ℤ G (g (letter d (f.1 - 1))) - 1) k f.2
    set a' := of ℤ G (g (letter d (f.1 - 1)) ^ f.2)
    set b := psi g (List.map (fun f => S k (f.1 - 1) f.2) t).prod
    set b' := of ℤ G (List.map (fun f => g (letter d (f.1 - 1)) ^ f.2) t).prod
    have e1 : a * b - a' * b' = (a - a') * b + a' * (b - b') := by noncomm_ring
    rw [e1]
    exact add_mem (Ideal.mul_mem_right _ _ (bser_sub_mem _ k f.2)) (Ideal.mul_mem_left _ _ ih)

/-- `Σ c_k (w_k(g) − 1)` in `ℤ[G]`: the image of a lintest (a word test `w` is `[(1, w)]`). -/
noncomputable def linG (l : List (ℤ × List (ℕ × ℤ))) : MonoidAlgebra ℤ G :=
  (l.map fun c => c.1 • (of ℤ G (gword g c.2) - 1)).sum

theorem linG_cons (c : ℤ × List (ℕ × ℤ)) (l : List (ℤ × List (ℕ × ℤ))) :
    linG g (c :: l) = c.1 • (of ℤ G (gword g c.2) - 1) + linG g l := by
  simp [linG]

theorem linG_single (w : List (ℕ × ℤ)) : linG g [(1, w)] = of ℤ G (gword g w) - 1 := by
  simp [linG]

theorem linG_mem_aug (l : List (ℤ × List (ℕ × ℤ))) : linG g l ∈ augIdeal G := by
  induction l with
  | nil => simp only [linG, List.map_nil, List.sum_nil]; exact zero_mem _
  | cons c l ih =>
    rw [linG_cons]
    exact add_mem (Submodule.smul_of_tower_mem _ c.1 (of_sub_one_mem_augIdeal _)) ih

/-- `ψ (Σ c_k (mt k w_k − 1)) ≡ Σ c_k (w_k(g) − 1)` modulo `Δ^k`. -/
theorem psi_linElt_sub_mem (k : ℕ) (l : List (ℤ × List (ℕ × ℤ))) :
    psi g (linElt d k l) - linG g l ∈ augIdeal G ^ k := by
  induction l with
  | nil => simp only [linElt, linG, List.map_nil, List.sum_nil, map_zero, sub_self]; exact zero_mem _
  | cons c l ih =>
    have hl : linElt d k (c :: l) = c.1 • (mt d k c.2 - 1) + linElt d k l := by simp [linElt]
    rw [hl, linG_cons, map_add, map_zsmul, map_sub, map_one]
    have e : c.1 • (psi g (mt d k c.2) - 1) + psi g (linElt d k l) -
        (c.1 • (of ℤ G (gword g c.2) - 1) + linG g l) =
        c.1 • (psi g (mt d k c.2) - of ℤ G (gword g c.2)) + (psi g (linElt d k l) - linG g l) := by
      simp only [smul_sub]; abel
    rw [e]
    exact add_mem (Submodule.smul_of_tower_mem _ c.1 (psi_mt_sub_mem g k c.2)) ih

variable {rels : List (ℕ × List (ℕ × ℤ))}

theorem psi_Jt (hrel : ∀ r ∈ rels, gword g r.2 = 1) {k : ℕ} {x : R d} (hx : x ∈ Jt d rels k) :
    psi g x ∈ augIdeal G ^ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, u, v, rfl⟩ := hx
    rw [map_mul, map_mul, map_sub, map_one]
    have h1 : psi g (mt d k r.2) - 1 ∈ augIdeal G ^ k := by
      have := psi_mt_sub_mem g k r.2
      rwa [hrel r hr, map_one] at this
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h1)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_of_tower_mem _ a hx

theorem psi_Jt_sup_Ik (hrel : ∀ r ∈ rels, gword g r.2 = 1) {k : ℕ} {x : R d}
    (hx : x ∈ Jt d rels k ⊔ Ik d k) : psi g x ∈ augIdeal G ^ k := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]; exact add_mem (psi_Jt g hrel ha) (psi_Ik g hb)

/-- `ψ (Lt) ⊆ Δ^k + D·ℤ[G]`. -/
theorem psi_Lt (hrel : ∀ r ∈ rels, gword g r.2 = 1) {D k : ℕ} {x : R d}
    (hx : x ∈ Lt d rels D k) : ∃ a ∈ augIdeal G ^ k, ∃ b, psi g x = a + (D : ℤ) • b := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨z', rfl⟩ := mem_DR.mp hz
  exact ⟨psi g y, psi_Jt_sup_Ik g hrel hy, psi g z', by rw [map_add, map_smul]⟩

/-- **The Magnus link.** If `mt n w − 1 ∈ Jt + I_n + D·R` and the relators hold in `G` at `g`,
then `w(g) − 1 ∈ Δ^n + D·ℤ[G]`. -/
theorem sub_one_mem_of_mem_Lt (hrel : ∀ r ∈ rels, gword g r.2 = 1) {D n : ℕ}
    {w : List (ℕ × ℤ)} (h : mt d n w - 1 ∈ Lt d rels D n) :
    ∃ a ∈ augIdeal G ^ n, ∃ b, of ℤ G (gword g w) - 1 = a + (D : ℤ) • b := by
  obtain ⟨a, ha, b, hb⟩ := psi_Lt g hrel h
  rw [map_sub, map_one] at hb
  refine ⟨a - (psi g (mt d n w) - of ℤ G (gword g w)), sub_mem ha (psi_mt_sub_mem g n w), b, ?_⟩
  have e1 : a - (psi g (mt d n w) - of ℤ G (gword g w)) + (D : ℤ) • b =
      (a + (D : ℤ) • b) - (psi g (mt d n w) - of ℤ G (gword g w)) := by abel
  rw [e1, ← hb]; abel

/-- The Magnus link for a lintest: if `Σ c_k (mt n w_k − 1) ∈ Jt + I_n + D·R` and the relators
hold in `G` at `g`, then `Σ c_k (w_k(g) − 1) ∈ Δ^n + D·ℤ[G]`. -/
theorem linG_mem_of_mem_Lt (hrel : ∀ r ∈ rels, gword g r.2 = 1) {D n : ℕ}
    {l : List (ℤ × List (ℕ × ℤ))} (h : linElt d n l ∈ Lt d rels D n) :
    ∃ a ∈ augIdeal G ^ n, ∃ b, linG g l = a + (D : ℤ) • b := by
  obtain ⟨a, ha, b, hb⟩ := psi_Lt g hrel h
  refine ⟨a - (psi g (linElt d n l) - linG g l), sub_mem ha (psi_linElt_sub_mem g n l), b, ?_⟩
  have e1 : a - (psi g (linElt d n l) - linG g l) + (D : ℤ) • b =
      (a + (D : ℤ) • b) - (psi g (linElt d n l) - linG g l) := by abel
  rw [e1, ← hb]; abel

/-- Without the `D·R` part: `w(g) ∈ D_n(G)`. -/
theorem mem_D_of_mem_Jt_sup_Ik (hrel : ∀ r ∈ rels, gword g r.2 = 1) {n : ℕ}
    {w : List (ℕ × ℤ)} (h : mt d n w - 1 ∈ Jt d rels n ⊔ Ik d n) :
    gword g w ∈ GroupDimension.D n G := by
  rw [mem_D]
  have h1 := psi_Jt_sup_Ik g hrel h
  rw [map_sub, map_one] at h1
  have e1 : of ℤ G (gword g w) - 1 =
      (psi g (mt d n w) - 1) - (psi g (mt d n w) - of ℤ G (gword g w)) := by abel
  rw [e1]
  exact sub_mem h1 (psi_mt_sub_mem g n w)

end Psi

/-- `check_sound`, in the group ring: for any group `G` and `g : Fin d → G` in which the trace's
relators hold, every test claimed in has `x_t ∈ Δ^n + p^E ℤ[G]`, where `x_t = linG g (testLin T t)` is
`w_t(g) − 1` for a word test and `Σ c_k (w_k(g) − 1)` for a lintest. This is informative only
when `H_1(G; 𝔽_p) ≠ 0` (e.g. `G` a nontrivial finite `p`-group), and it is `w_t(g) ∈ D_n(G)` once
`p^E Δ ⊆ Δ^n`. Fewer relators listed in the trace make it stronger. That `T.tests` holds the
intended words, and `g` the presentation's generators in order, is the reader's to check (the data
file transcribes them; `trace_to_lean.py`). -/
theorem check_group (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1) :
    ∀ t ∈ members, ∃ a ∈ augIdeal G ^ T.n, ∃ b,
      linG g (testLin T t) = a + ((T.p ^ T.E : ℕ) : ℤ) • b :=
  fun t ht => linG_mem_of_mem_Lt g hrel ((check_sound T members hc).1 t ht)


/-! ## Exactness: removing `p^E ℤ[G]`

If the `g_j` generate `G` and `x^{p^N} = 1` in `G`, the second half of `check_sound` gives
`p^{E−1} Δ ⊆ Δ^n` (below), so the `p^E ℤ[G]` of `check_group` drops and `w_t(g) ∈ D_n(G)`. -/

section Exact

variable {G : Type*} [Group G]

/-- `x^m − 1 ≡ m (x − 1)` modulo `Δ²`. -/
theorem of_pow_sub_mem (x : G) : ∀ m : ℕ,
    of ℤ G (x ^ m) - 1 - (m : ℤ) • (of ℤ G x - 1) ∈ augIdeal G ^ 2
  | 0 => by
    simp only [pow_zero, map_one, sub_self, Nat.cast_zero, zero_smul]; exact zero_mem _
  | m + 1 => by
    have hx : of ℤ G x - 1 ∈ augIdeal G ^ 1 := by
      rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal x
    have hxm : of ℤ G (x ^ m) - 1 ∈ augIdeal G ^ 1 := by
      rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal _
    have e : of ℤ G (x ^ (m + 1)) - 1 - ((m + 1 : ℕ) : ℤ) • (of ℤ G x - 1) =
        (of ℤ G (x ^ m) - 1) * (of ℤ G x - 1) + (of ℤ G (x ^ m) - 1 - (m : ℤ) • (of ℤ G x - 1)) := by
      rw [pow_succ, map_mul, Nat.cast_succ, add_smul, one_smul]; noncomm_ring
    rw [e]
    exact add_mem (mul_mem_augIdeal_pow hxm hx) (of_pow_sub_mem x m)

theorem smul_mem_sq {q : ℕ} (hexp : ∀ x : G, x ^ q = 1) {y : MonoidAlgebra ℤ G}
    (hy : y ∈ augIdeal G) : (q : ℤ) • y ∈ augIdeal G ^ 2 := by
  refine CentralRoot.augIdeal_induction (p := fun y => (q : ℤ) • y ∈ augIdeal G ^ 2) hy
    (by simp) (fun x => ?_) (fun y h => by rw [smul_neg]; exact neg_mem h)
    (fun y z hy hz => by rw [smul_add]; exact add_mem hy hz)
  have := of_pow_sub_mem x q
  rwa [hexp, map_one, sub_self, zero_sub, neg_mem_iff] at this

/-- `q Δ^{k+1} ⊆ Δ^{k+2}` when `x^q = 1` in `G`. -/
theorem smul_pow_mem {q : ℕ} (hexp : ∀ x : G, x ^ q = 1) :
    ∀ k : ℕ, ∀ y ∈ augIdeal G ^ (k + 1), (q : ℤ) • y ∈ augIdeal G ^ (k + 2)
  | 0, y, hy => by rw [zero_add, Submodule.pow_one] at hy; exact smul_mem_sq hexp hy
  | k + 1, y, hy => by
    rw [Submodule.pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_)
      (fun _ _ h h' => by rw [smul_add]; exact add_mem h h')
    rw [← smul_mul_assoc]
    have hb1 : b ∈ augIdeal G ^ 1 := by rw [Submodule.pow_one]; exact hb
    have := mul_mem_augIdeal_pow (smul_pow_mem hexp k a ha) hb1
    rwa [show k + 2 + 1 = k + 1 + 2 by omega] at this

/-- `q^j Δ ⊆ Δ^{j+1}` when `x^q = 1` in `G`. -/
theorem pow_smul_mem {q : ℕ} (hexp : ∀ x : G, x ^ q = 1) :
    ∀ j : ℕ, ∀ y ∈ augIdeal G, ((q ^ j : ℕ) : ℤ) • y ∈ augIdeal G ^ (j + 1)
  | 0, y, hy => by simpa [Submodule.pow_one] using hy
  | j + 1, y, hy => by
    rw [pow_succ', Nat.cast_mul, mul_smul]
    exact smul_pow_mem hexp j _ (pow_smul_mem hexp j y hy)

/-- If `x ∈ Δ` and `x = a + D b` with `a ∈ Δ^n` (`n ≥ 1`, `D ≠ 0`), then `b ∈ Δ`. -/
theorem mem_aug_of_eq {n : ℕ} (hn : n ≠ 0) {D : ℤ} (hD : D ≠ 0) {x a b : MonoidAlgebra ℤ G}
    (hx : x ∈ augIdeal G) (ha : a ∈ augIdeal G ^ n) (h : x = a + D • b) : b ∈ augIdeal G := by
  rw [mem_augIdeal] at hx ⊢
  have ha' : augmentation G a = 0 := mem_augIdeal.mp (Ideal.pow_le_self hn ha)
  have hs : augmentation G (D • b) = D * augmentation G b := by simp [Algebra.smul_def]
  rw [h, map_add, ha', zero_add, hs] at hx
  exact (mul_eq_zero.mp hx).resolve_left hD

/-- `x ∈ Δ^n + D Δ`. -/
def InT (n : ℕ) (D : ℤ) (x : MonoidAlgebra ℤ G) : Prop :=
  ∃ a ∈ augIdeal G ^ n, ∃ b ∈ augIdeal G, x = a + D • b

theorem InT.of_pow {n : ℕ} {D : ℤ} {x : MonoidAlgebra ℤ G} (hx : x ∈ augIdeal G ^ n) :
    InT n D x := ⟨x, hx, 0, zero_mem _, by simp⟩

theorem InT.add {n : ℕ} {D : ℤ} {x y : MonoidAlgebra ℤ G} (hx : InT n D x) (hy : InT n D y) :
    InT n D (x + y) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hy
  exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by rw [smul_add]; abel⟩

theorem InT.smul {n : ℕ} {D : ℤ} {x : MonoidAlgebra ℤ G} (c : ℤ) (hx : InT n D x) :
    InT n D (c • x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨c • a, Submodule.smul_of_tower_mem _ c ha, c • b, Submodule.smul_of_tower_mem _ c hb,
    by rw [smul_add, smul_comm c D b]⟩

/-- Iterating `r Δ ⊆ Δ^n + P r Δ`: `r Δ ⊆ Δ^n + P^j r Δ` for every `j`. -/
theorem iterate_exact {n : ℕ} (P r : ℤ)
    (h1 : ∀ x ∈ augIdeal G, InT n (P * r) (r • x)) :
    ∀ j : ℕ, ∀ x ∈ augIdeal G, InT n (P ^ j * r) (r • x)
  | 0, x, hx => ⟨0, zero_mem _, x, hx, by simp⟩
  | j + 1, x, hx => by
    obtain ⟨a, ha, b, hb, e⟩ := iterate_exact P r h1 j x hx
    obtain ⟨a', ha', b', hb', e'⟩ := h1 b hb
    refine ⟨a + P ^ j • a', add_mem ha (Submodule.smul_of_tower_mem _ _ ha'), b', hb', ?_⟩
    rw [e, mul_smul, e', smul_add, smul_smul, show P ^ (j + 1) * r = P ^ j * (P * r) by ring,
      add_assoc]

variable {d : ℕ} [NeZero d] (g : Fin d → G)

/-- The `ℤ`-span of the `ψ(X_w)`, `w ≠ 1`, plus `Δ^n`. -/
def Sp (n : ℕ) : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ {y | ∃ w : FreeMonoid (Fin d), w ≠ 1 ∧ y = psi g (single w 1)} ⊔
    (augIdeal G ^ n).restrictScalars ℤ

theorem ne_one_of_mul_ne_one {u v : FreeMonoid (Fin d)} (hu : u ≠ 1) : u * v ≠ 1 := by
  intro h; apply hu
  have h2 := congrArg FreeMonoid.toList h
  rw [FreeMonoid.toList_mul, FreeMonoid.toList_one, List.append_eq_nil_iff] at h2
  rw [← FreeMonoid.ofList_toList u, h2.1]; rfl

theorem Sp_mul {n : ℕ} {a b : MonoidAlgebra ℤ G} (ha : a ∈ Sp g n) (hb : b ∈ Sp g n) :
    a * b ∈ Sp g n := by
  obtain ⟨s, hs, δ, hδ, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨s', hs', δ', hδ', rfl⟩ := Submodule.mem_sup.mp hb
  have e : (s + δ) * (s' + δ') = s * s' + (s * δ' + δ * (s' + δ')) := by noncomm_ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (add_mem (Ideal.mul_mem_left _ s hδ') (Ideal.mul_mem_right _ _ hδ))
  clear e ha hb
  induction hs using Submodule.span_induction with
  | mem x hx =>
    induction hs' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, -, rfl⟩ := hy
      refine Submodule.subset_span ⟨u * v, ne_one_of_mul_ne_one hu, ?_⟩
      rw [← map_mul, single_mul_single, one_mul]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- If the `g_j` generate `G` (of finite exponent `q`), every `x − 1` lies in `Sp`. -/
theorem sub_one_mem_Sp (hgen : Subgroup.closure (Set.range g) = ⊤) {q : ℕ} (hq : 0 < q)
    (hexp : ∀ x : G, x ^ q = 1) (n : ℕ) (x : G) : of ℤ G x - 1 ∈ Sp g n := by
  have hmul : ∀ a b : G, of ℤ G a - 1 ∈ Sp g n → of ℤ G b - 1 ∈ Sp g n →
      of ℤ G (a * b) - 1 ∈ Sp g n := by
    intro a b ha hb
    have e : of ℤ G (a * b) - 1 =
        (of ℤ G a - 1) * (of ℤ G b - 1) + (of ℤ G a - 1) + (of ℤ G b - 1) := by
      rw [map_mul]; noncomm_ring
    rw [e]; exact add_mem (add_mem (Sp_mul g ha hb) ha) hb
  have hpow : ∀ a : G, of ℤ G a - 1 ∈ Sp g n → ∀ m : ℕ, of ℤ G (a ^ m) - 1 ∈ Sp g n := by
    intro a ha m
    induction m with
    | zero => simp only [pow_zero, map_one, sub_self]; exact zero_mem _
    | succ m ih => rw [pow_succ]; exact hmul _ _ ih ha
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
    have h1 : a ^ (q - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel hq, hexp]
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact hpow a ha (q - 1)

theorem aug_le_Sp (hgen : Subgroup.closure (Set.range g) = ⊤) {q : ℕ} (hq : 0 < q)
    (hexp : ∀ x : G, x ^ q = 1) (n : ℕ) {y : MonoidAlgebra ℤ G} (hy : y ∈ augIdeal G) :
    y ∈ Sp g n :=
  CentralRoot.augIdeal_induction (p := fun y => y ∈ Sp g n) hy (zero_mem _)
    (sub_one_mem_Sp g hgen hq hexp n) (fun _ h => neg_mem h) (fun _ _ h h' => add_mem h h')

end Exact

theorem check_params (T : Trace) (members : List ℕ) (h : check T members = true) :
    1 < T.p ∧ 0 < T.E ∧ 1 < T.n := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Nat.blt_eq,
    Nat.ble_eq, Bool.or_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hp1⟩, hE⟩, hn⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hp1, hE, hn⟩

/-- **Exact membership.** If `check` accepts the trace, then for every group `G` and `g : Fin d → G`
such that the `g j` generate `G`, the relators listed in the trace hold at `g`, and `x^{p^N} = 1`
for all `x : G` (some `N`), every test claimed in has `x_t ∈ Δ^n`: for a word test,
`w_t(g) − 1 ∈ Δ^n`, i.e. `w_t(g) ∈ D_n(G)` (`check_mem_D`); for a lintest, `Σ c_k (w_k(g) − 1) ∈ Δ^n`. Generator `i` of a word (1-based)
is `g ⟨i − 1⟩`.

For the paper's group the reader supplies `g` = the images of `x_1, …, x_d` and discharges the
hypotheses (for a finite `p`-group, `hexp` holds with `p^N = |G|`). The trace lists a subset of the
relators (fewer make the statement stronger), and no free columns (`hF`; for `F ≠ []` see
`TraceReplay/HomExact.lean`); that `T.rels` and `T.tests` are the presentation's
relators and test words is the data file's transcription (`trace_to_lean.py`), not checked here.
The conclusion is about the word: that it is `≠ 1`, or not in `γ_n`, is a separate claim. -/
theorem check_mem_D_lin (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (hF : T.F = [])
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (N : ℕ) (hexp : ∀ x : G, x ^ (T.p ^ N) = 1) :
    ∀ t ∈ members, linG g (testLin T t) ∈ augIdeal G ^ T.n := by
  obtain ⟨hp, hE, hn⟩ := check_params T members hc
  have hn0 : T.n ≠ 0 := by omega
  have hq : 0 < T.p ^ N := Nat.pow_pos (by omega)
  set r : ℤ := ((T.p ^ (T.E - 1) : ℕ) : ℤ) with hr
  have hDe : ((T.p ^ T.E : ℕ) : ℤ) = (T.p : ℤ) * r := by
    rw [hr, ← Nat.cast_mul, ← pow_succ', Nat.sub_add_cancel hE]
  have hD0 : ((T.p ^ T.E : ℕ) : ℤ) ≠ 0 := by
    have : 0 < T.p ^ T.E := Nat.pow_pos (by omega)
    exact_mod_cast this.ne'
  -- `r Δ ⊆ Δ^n + p r Δ`
  have h1 : ∀ x ∈ augIdeal G, InT T.n ((T.p : ℤ) * r) (r • x) := by
    intro x hx
    obtain ⟨s, hs, δ, hδ, rfl⟩ := Submodule.mem_sup.mp (aug_le_Sp g hgen hq hexp T.n hx)
    rw [smul_add]
    refine InT.add ?_ (InT.of_pow (Submodule.smul_of_tower_mem _ r hδ))
    clear hx
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      have hL0 := (check_sound T members hc).2 w hw
      rw [hF, show Fspan T.d ([] : List ℕ) = ⊥ by simp [Fspan], sup_bot_eq] at hL0
      have hL := hL0
      obtain ⟨a, ha, b, hb⟩ := psi_Lt g hrel hL
      rw [map_smul] at hb
      have hmem : r • psi g (single w 1) ∈ augIdeal G := by
        refine Submodule.smul_of_tower_mem _ r ?_
        have hw1 : 1 ≤ w.length := by
          rcases Nat.eq_zero_or_pos w.length with h0 | h0
          · exfalso; apply hw
            have h0' : w.toList = [] := List.length_eq_zero_iff.mp h0
            rw [← FreeMonoid.ofList_toList w, h0']; rfl
          · exact h0
        exact Ideal.pow_le_self (by omega) (psi_single_mem g w 1)
      rw [← hDe]
      exact ⟨a, ha, b, mem_aug_of_eq hn0 hD0 hmem ha hb, hb⟩
    | zero => rw [smul_zero]; exact InT.of_pow (zero_mem _)
    | add y z _ _ hy hz => rw [smul_add]; exact InT.add hy hz
    | smul c y _ hy => rw [smul_comm]; exact InT.smul c hy
  -- `r Δ ⊆ Δ^n`
  have h2 : ∀ x ∈ augIdeal G, r • x ∈ augIdeal G ^ T.n := by
    intro x hx
    obtain ⟨a, ha, b, hb, e⟩ := iterate_exact (T.p : ℤ) r h1 (N * (T.n - 1)) x hx
    rw [e]
    refine add_mem ha ?_
    have hK := pow_smul_mem hexp (T.n - 1) b hb
    rw [Nat.sub_add_cancel (by omega)] at hK
    have hc' : ((T.p : ℤ) ^ (N * (T.n - 1)) * r) • b = r • (((T.p ^ N) ^ (T.n - 1) : ℕ) : ℤ) • b := by
      rw [smul_smul]; congr 1; push_cast; rw [← pow_mul, mul_comm]
    rw [hc']
    exact Submodule.smul_of_tower_mem _ r hK
  intro t ht
  obtain ⟨a, ha, b, e⟩ := check_group T members hc g hrel t ht
  have hb : b ∈ augIdeal G := mem_aug_of_eq hn0 hD0 (linG_mem_aug g _) ha e
  rw [e, hDe, mul_smul]
  exact add_mem ha (Submodule.smul_of_tower_mem _ _ (h2 b hb))

/-- `check_mem_D_lin` for a word test (`hw`): `w_t(g) ∈ D_n(G)`. -/
theorem check_mem_D (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    (hF : T.F = [])
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (N : ℕ) (hexp : ∀ x : G, x ^ (T.p ^ N) = 1)
    (t : ℕ) (ht : t ∈ members) (hw : T.tests.any (fun y => y.1 == t) = true) :
    gword g (findWord t T.tests) ∈ GroupDimension.D T.n G := by
  have h := check_mem_D_lin T members hc hF g hrel hgen N hexp t ht
  rw [testLin_of_word T hw, linG_single] at h
  exact mem_D.2 h

end

end GroupDimension.TraceReplay
