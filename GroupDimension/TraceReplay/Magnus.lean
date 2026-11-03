module

public import GroupDimension.Basic
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

and `w(g) ∈ D_n(G)` when the `D·R` part is absent (`mem_D_of_mem_Jt_sup_Ik`). This is the easy
direction of §3.1 of the paper (`J_n ↦ Δ^n`); only it is needed for a certificate of membership.
`binom` (the checker's own generalised binomial coefficient) is `Ring.choose` (`binom_eq_choose`).

Removing `D·ℤ[G]` (exactness) is a separate step: it needs `p^{E−1} Δ ⊆ Δ^n + p^E Δ` (the second
half of `check_sound`, pushed by `ψ`) and that `Δ/Δ^n` is a `p`-group.
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
      Ring.choose_succ_succ, add_smul, smul_mul_assoc, mul_add, mul_one, ← pow_succ]
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
  | hz => rw [bser_at_zero, zpow_zero, map_one, sub_self]; exact zero_mem _
  | hp i ih =>
    have hQ := bser_mul y (i : ℤ) k
    rw [hy] at hQ
    have e1 : bser y (k + 1) ((i : ℤ) + 1) - of ℤ G (h ^ ((i : ℤ) + 1)) =
        (bser y (k + 1) (i : ℤ) - of ℤ G (h ^ (i : ℤ))) * of ℤ G h
          - Ring.choose (i : ℤ) k • y ^ (k + 1) := by
      rw [zpow_add_one, map_mul, sub_mul, hQ]; abel
    rw [e1]
    exact sub_mem (Ideal.mul_mem_right _ _ ih) (hZ _)
  | hn i ih =>
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

/-- A flat word evaluated in `G` (generators `1..d`, as in `mt`). -/
def gword (w : List (ℕ × ℤ)) : G := (w.map fun f => g (letter d (f.1 - 1)) ^ f.2).prod

/-- `ψ (mt k w) ≡ w(g)` modulo `Δ^k`. -/
theorem psi_mt_sub_mem (k : ℕ) (w : List (ℕ × ℤ)) :
    psi g (mt d k w) - of ℤ G (gword g w) ∈ augIdeal G ^ k := by
  induction w with
  | nil => simp [mt, gword]
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
relators hold, every test claimed in has `w_t(g) − 1 ∈ Δ^n + p^E ℤ[G]`. -/
theorem check_group (T : Trace) (members : List ℕ) [NeZero T.d] (hc : check T members = true)
    {G : Type*} [Group G] (g : Fin T.d → G) (hrel : ∀ r ∈ T.rels, gword g r.2 = 1) :
    ∀ t ∈ members, ∃ a ∈ augIdeal G ^ T.n, ∃ b,
      of ℤ G (gword g (findWord t T.tests)) - 1 = a + ((T.p ^ T.E : ℕ) : ℤ) • b :=
  fun t ht => sub_one_mem_of_mem_Lt g hrel ((check_sound T members hc).1 t ht)

end

end GroupDimension.TraceReplay
