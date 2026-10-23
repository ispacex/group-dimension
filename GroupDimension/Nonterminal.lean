module

public import GroupDimension.PCover

@[expose] public section

/-!
# Theorem 6.12, necessity: a nonterminal group of type `(d, 2, 1)` satisfies (N1)–(N4)

Let `p` be an odd prime and `P` a group of type `(d, 2, 1)` with `P/γ₂(P)` elementary abelian:
`γ₄(P) = 1`, `|γ₂(P)/γ₃(P)| = p²`, `|γ₃(P)| = p` and `x^p ∈ γ₂(P)` for all `x`. By Lemma 10.1 of
the paper, `P` is nonterminal if and only if there is a group `Q` with a central subgroup `⟨z⟩` of
order `p`, `Q/⟨z⟩ ≅ P` and `γ₄(Q) ≠ 1`. This existence is what "nonterminal" means here: we take
`π : Q →* P` onto with `ker π = ⟨z⟩`, `z` central of order `p`, and `γ₄(Q) ≠ 1`. (That it is
equivalent to a nontrivial nucleus is O'Brien's theory and is not formalized.)

**Theorem 6.12, "⇒"** (`nonterminal_necessary`; Appendix, Steps 2 and 4) concludes
* (N1) `|Z(P) ∩ γ₂(P)| = p²`;
* (N2) `γ₂(P)` is elementary abelian;
* (N3) `P^p ≤ Z(P)`;
* (N4) for every choice of `u, v, w, x_1, …, x_d` as in the theorem and of exponents
  `ω_r(i,j), α_i, β_i, f_i ∈ 𝔽_p` with `[x_i,x_j] = u^{ω₁(i,j)} v^{ω₂(i,j)} w^{ω₃(i,j)}`,
  `x_i^p = v^{α_i} w^{β_i}` and `[u,x_i] = w^{f_i}`, the linear system (E)+(J) (`SystemEJ`) has a
  solution with `c = 1`. The `x_i` need not generate `P`.

The proof is the paper's. `Q'' = 1` (Theorem 6.10, `metabelian_of_central_ext_card`),
`γ₄(Q) = ⟨z⟩`, and `γ₃(Q)` has exponent `p` (`pow_p_lcs2`). For `ℓ ∈ γ₂(Q)`,
`[[ℓ,x],y] = [[ℓ,y],x]` (`pc_pc_symm`, the Jacobi identity with `[ℓ,[x,y]] = 1`), which gives
`ψ = c f` with `c ≠ 0`, where `[w,x] = z^{ψ(x)}`. The Hall–Witt identity becomes
`[x,y,t][y,t,x][t,x,y] = 1` (`pc_jacobi`), whose `z`-component is (J). Finally
`(x^p)^y = (x[x,y])^p = x^p [x,y]^p [x,y,x]^{\binom p2} [x,y,x,x]^{\binom p3}`
(`mul_pow_formula`) gives (E); `\binom p3 ≡ ε_p (mod p)`.

Commutators are the paper's, `[a,b] = a⁻¹b⁻¹ab` (`pc`); Mathlib's `⁅a,b⁆` is `aba⁻¹b⁻¹`. Powers
with exponents in `𝔽_p = ZMod p` are written `g ^ k.val`. Indexing as in `ClassFour`:
`(⊤ : Subgroup G).lowerCentralSeries k` is `γ_{k+1}(G)`.
-/

namespace GroupDimension

open Subgroup
open scoped commutatorElement

/-- The linear system (E)+(J) of Theorem 6.12 over `𝔽_p`, in the unknowns `c, μ_u, μ_v, η, σ`,
for the exponents `ω_r(i,j)`, `α_i`, `β_i`, `f_i` of a normal form of `P`; `ε_3 = 1` and
`ε_p = 0` for `p ≥ 5`. (J) is required for `i < j < k`, as in the paper. -/
def SystemEJ {p d : ℕ} (ω₁ ω₂ ω₃ : Fin d → Fin d → ZMod p) (α β f : Fin d → ZMod p)
    (c μu μv : ZMod p) (η σ : Fin d → ZMod p) : Prop :=
  (∀ i j, α j * η i + c * β j * f i + μu * ω₁ i j + μv * ω₂ i j +
      (if p = 3 then 1 else 0) * c * f j ^ 2 * ω₁ i j = 0) ∧
  (∀ i j k, i < j → j < k →
      (ω₁ i j * σ k + ω₂ i j * η k + c * ω₃ i j * f k) +
      (ω₁ j k * σ i + ω₂ j k * η i + c * ω₃ j k * f i) +
      (ω₁ k i * σ j + ω₂ k i * η j + c * ω₃ k i * f j) = 0)

namespace Nonterminal

section General

variable {G : Type*} [Group G]

/-- The paper's commutator `[a, b] = a⁻¹ b⁻¹ a b`. -/
def pc (a b : G) : G := a⁻¹ * b⁻¹ * a * b

theorem pc_eq_comm (a b : G) : pc a b = ⁅a⁻¹, b⁻¹⁆ := by
  simp only [pc, commutatorElement_def, inv_inv]

theorem comm_eq_pc (a b : G) : ⁅a, b⁆ = pc a⁻¹ b⁻¹ := by
  simp only [pc, commutatorElement_def, inv_inv]

theorem pc_mem {i j n : ℕ} (h : i + j + 1 = n) {x y : G} (hx : x ∈ (⊤ : Subgroup G).lowerCentralSeries i) (hy : y ∈ (⊤ : Subgroup G).lowerCentralSeries j) :
    pc x y ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
  rw [pc_eq_comm]; exact commutator_mem_lcs h (inv_mem hx) (inv_mem hy)

theorem pc_mem_one (x y : G) : pc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
  pc_mem (by norm_num) (mem_lcs_zero x) (mem_lcs_zero y)

theorem conj_eq_mul_pc (a x : G) : x⁻¹ * a * x = a * pc a x := by
  simp only [pc]; group

theorem pc_eq_one_iff {a x : G} : pc a x = 1 ↔ a * x = x * a := by
  simp only [pc]
  constructor
  · intro h
    calc a * x = x * a * (a⁻¹ * x⁻¹ * a * x) := by group
      _ = x * a := by rw [h, mul_one]
  · intro h
    rw [mul_assoc (a⁻¹ * x⁻¹), h]; group

theorem pc_of_mem_center {a : G} (ha : a ∈ center G) (x : G) : pc a x = 1 :=
  pc_eq_one_iff.mpr (mem_center_iff.mp ha x).symm

theorem mem_center_of_pc {a : G} (h : ∀ x, pc a x = 1) : a ∈ center G :=
  mem_center_iff.mpr fun x => (pc_eq_one_iff.mp (h x)).symm

theorem pc_mul_central {g c : G} (hc : c ∈ center G) (x : G) : pc (g * c) x = pc g x := by
  have h1 : pc (g * c) x = c⁻¹ * pc g x * (x⁻¹ * c * x) := by simp only [pc]; group
  rw [h1, conj_eq_mul_pc, pc_of_mem_center hc, mul_one, mul_assoc,
    mem_center_iff.mp hc (pc g x), inv_mul_cancel_left]

theorem pc_mul {g h x : G} (hc : Commute h (pc g x)) : pc (g * h) x = pc g x * pc h x := by
  have h1 : pc (g * h) x = h⁻¹ * pc g x * h * pc h x := by simp only [pc]; group
  rw [h1, mul_assoc h⁻¹, ← hc.eq, inv_mul_cancel_left]

theorem pc_pow {g x : G} (hc : Commute g (pc g x)) (n : ℕ) : pc (g ^ n) x = pc g x ^ n := by
  induction n with
  | zero => simp [pc]
  | succ n ih =>
    rw [pow_succ, pc_mul (g := g ^ n) (h := g) (x := x) (by rw [ih]; exact hc.pow_right n), ih,
      pow_succ]

theorem conj_mul' (x a b : G) : x⁻¹ * (a * b) * x = x⁻¹ * a * x * (x⁻¹ * b * x) := by group

theorem conj_pow' (x a : G) (n : ℕ) : (x⁻¹ * a * x) ^ n = x⁻¹ * a ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]

theorem choose_three_succ (n : ℕ) : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ']

/-- `x^{-n} a x^n = a b^n c^{\binom n2}` for `b = [a,x]` and `c = [b,x]` commuting with `x`. -/
theorem conj_pow_formula {a b c x : G} (hb : pc a x = b) (hc : pc b x = c) (hcx : pc c x = 1)
    (hbc : Commute b c) (n : ℕ) : (x ^ n)⁻¹ * a * x ^ n = a * b ^ n * c ^ n.choose 2 := by
  have ha' : x⁻¹ * a * x = a * b := by rw [conj_eq_mul_pc, hb]
  have hb' : x⁻¹ * b * x = b * c := by rw [conj_eq_mul_pc, hc]
  have hc' : x⁻¹ * c * x = c := by rw [conj_eq_mul_pc, hcx, mul_one]
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (x ^ (n + 1))⁻¹ * a * x ^ (n + 1) = x⁻¹ * ((x ^ n)⁻¹ * a * x ^ n) * x := by
      rw [pow_succ]; group
    rw [e, ih, choose_two_succ, conj_mul' x (a * b ^ n) (c ^ n.choose 2), conj_mul' x a (b ^ n),
      ← conj_pow' x b n, ← conj_pow' x c (n.choose 2), ha', hb', hc', hbc.mul_pow, pow_succ' b n,
      pow_add c n]
    simp only [mul_assoc]

/-- `(x a)^n = x^n a^n b^{\binom n2} c^{\binom n3}` for `b = [a,x]` and `c = [b,x]` commuting with
`x`, when `a, b, c` commute. -/
theorem mul_pow_formula {a b c x : G} (hb : pc a x = b) (hc : pc b x = c) (hcx : pc c x = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) (n : ℕ) :
    (x * a) ^ n = x ^ n * (a ^ n * b ^ n.choose 2 * c ^ n.choose 3) := by
  have ha' : x⁻¹ * a * x = a * b := by rw [conj_eq_mul_pc, hb]
  have hb' : x⁻¹ * b * x = b * c := by rw [conj_eq_mul_pc, hc]
  have hc' : x⁻¹ * c * x = c := by rw [conj_eq_mul_pc, hcx, mul_one]
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (x * a) ^ (n + 1) = x ^ (n + 1) *
        (x⁻¹ * (a ^ n * b ^ n.choose 2 * c ^ n.choose 3) * x * a) := by
      rw [pow_succ, ih, pow_succ]; simp only [mul_assoc, mul_inv_cancel_left]
    rw [e, choose_two_succ, choose_three_succ, conj_mul' x (a ^ n * b ^ n.choose 2) (c ^ n.choose 3),
      conj_mul' x (a ^ n) (b ^ n.choose 2), ← conj_pow' x a n, ← conj_pow' x b (n.choose 2),
      ← conj_pow' x c (n.choose 3), ha', hb', hc', hab.mul_pow, hbc.mul_pow]
    congr 1
    have hX : Commute a (b ^ n * (b ^ n.choose 2 * c ^ n.choose 2) * c ^ n.choose 3) :=
      ((hab.pow_right _).mul_right ((hab.pow_right _).mul_right (hac.pow_right _))).mul_right
        (hac.pow_right _)
    calc a ^ n * b ^ n * (b ^ n.choose 2 * c ^ n.choose 2) * c ^ n.choose 3 * a
        = a ^ n * ((b ^ n * (b ^ n.choose 2 * c ^ n.choose 2) * c ^ n.choose 3) * a) := by
          simp only [mul_assoc]
      _ = a ^ n * (a * (b ^ n * (b ^ n.choose 2 * c ^ n.choose 2) * c ^ n.choose 3)) := by
          rw [hX.eq]
      _ = a ^ (n + 1) * b ^ (n + n.choose 2) * c ^ (n.choose 2 + n.choose 3) := by
          rw [pow_succ a n, pow_add b, pow_add c]; simp only [mul_assoc]

/-- **Jacobi identity with `[ℓ,[x,y]] = 1`**: if `A` is an abelian normal subgroup containing all
commutators, then `[[ℓ,x],y] = [[ℓ,y],x]` for `ℓ ∈ A`. -/
theorem pc_pc_symm {A : Subgroup G} [hAn : A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hpc : ∀ x y : G, pc x y ∈ A) {ℓ : G} (hℓ : ℓ ∈ A) (x y : G) :
    pc (pc ℓ x) y = pc (pc ℓ y) x := by
  have e1 : (x * y)⁻¹ * ℓ * (x * y) = ℓ * pc ℓ y * (pc ℓ x * pc (pc ℓ x) y) := by
    simp only [pc]; group
  have e2 : (y * x)⁻¹ * ℓ * (y * x) = ℓ * pc ℓ x * (pc ℓ y * pc (pc ℓ y) x) := by
    simp only [pc]; group
  have e3 : (x * y)⁻¹ * ℓ * (x * y) = (pc x y)⁻¹ * ((y * x)⁻¹ * ℓ * (y * x)) * pc x y := by
    simp only [pc]; group
  have hm : (y * x)⁻¹ * ℓ * (y * x) ∈ A := by
    simpa only [inv_inv] using hAn.conj_mem ℓ hℓ (y * x)⁻¹
  rw [mul_assoc _ _ (pc x y), hA _ hm _ (hpc x y), inv_mul_cancel_left, e2, e1] at e3
  have key : ℓ * (pc ℓ x * pc ℓ y) * pc (pc ℓ x) y = ℓ * (pc ℓ x * pc ℓ y) * pc (pc ℓ y) x := by
    calc ℓ * (pc ℓ x * pc ℓ y) * pc (pc ℓ x) y = ℓ * pc ℓ y * (pc ℓ x * pc (pc ℓ x) y) := by
          rw [hA _ (hpc ℓ x) _ (hpc ℓ y)]; simp only [mul_assoc]
      _ = ℓ * pc ℓ x * (pc ℓ y * pc (pc ℓ y) x) := e3
      _ = ℓ * (pc ℓ x * pc ℓ y) * pc (pc ℓ y) x := by simp only [mul_assoc]
  exact mul_left_cancel key

theorem inv_mul_mul_of_comm {a b : G} (h : b * a = a * b) : a⁻¹ * b * a = b := by
  rw [mul_assoc, h, inv_mul_cancel_left]

/-- **The Hall–Witt identity as a Jacobi identity**: if `A` is an abelian normal subgroup
containing all commutators, then `[x,y,t][y,t,x][t,x,y] = 1`. -/
theorem pc_jacobi {A : Subgroup G} [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hpc : ∀ x y : G, pc x y ∈ A) (x y t : G) :
    pc (pc x y) t * pc (pc y t) x * pc (pc t x) y = 1 := by
  have key : ∀ x y t : G, y⁻¹ * pc (pc x y⁻¹) t * y = (pc (pc x y) t)⁻¹ := by
    intro x y t
    have ha : (pc x y)⁻¹ ∈ A := inv_mem (hpc x y)
    have e1 : y⁻¹ * pc (pc x y⁻¹) t * y = pc (pc x y)⁻¹ (t * pc t y) := by simp only [pc]; group
    have e2 : pc (pc x y)⁻¹ (t * pc t y) =
        pc (pc x y)⁻¹ (pc t y) * ((pc t y)⁻¹ * pc (pc x y)⁻¹ t * pc t y) := by
      simp only [pc]; group
    have e3 : pc (pc x y)⁻¹ t = pc x y * (pc (pc x y) t)⁻¹ * (pc x y)⁻¹ := by
      simp only [pc]; group
    rw [e1, e2, pc_eq_one_iff.mpr (hA _ ha _ (hpc t y)), one_mul,
      inv_mul_mul_of_comm (hA _ (hpc _ t) _ (hpc t y)), e3,
      hA _ (hpc x y) _ (inv_mem (hpc _ t)), mul_inv_cancel_right]
  have hw : y⁻¹ * pc (pc x y⁻¹) t * y * (t⁻¹ * pc (pc y t⁻¹) x * t) *
      (x⁻¹ * pc (pc t x⁻¹) y * x) = 1 := by
    simp only [pc]; group
  rw [key x y t, key y t x, key t x y] at hw
  have hX := hpc (pc x y) t
  have hY := hpc (pc y t) x
  have hZ := hpc (pc t x) y
  have h' : (pc (pc t x) y * pc (pc y t) x * pc (pc x y) t)⁻¹ = 1 := by
    rw [mul_inv_rev, mul_inv_rev, ← mul_assoc]; exact hw
  have h2 := inv_eq_one.mp h'
  calc pc (pc x y) t * pc (pc y t) x * pc (pc t x) y
      = pc (pc y t) x * pc (pc x y) t * pc (pc t x) y := by rw [hA _ hX _ hY]
    _ = pc (pc t x) y * (pc (pc y t) x * pc (pc x y) t) := hA _ (mul_mem hY hX) _ hZ
    _ = 1 := by rw [← mul_assoc]; exact h2

theorem mul_central_rearrange {a₁ a₂ c₁ c₂ : G} (hc : c₁ ∈ center G) :
    a₁ * c₁ * (a₂ * c₂) = a₁ * a₂ * (c₁ * c₂) := by
  rw [mul_assoc a₁, ← mul_assoc c₁, ← mem_center_iff.mp hc a₂]; simp only [mul_assoc]

/-! ### Exponents in `𝔽_p` -/

/-- The exponent of `y` with respect to `g` in `𝔽_p` (meaningful for `y ∈ ⟨g⟩`, `g^p = 1`). -/
noncomputable def coef (q : ℕ) (g y : G) : ZMod q := by
  classical exact if h : ∃ k : ZMod q, g ^ k.val = y then h.choose else 0

variable {p : ℕ} [Fact p.Prime] {g : G}

omit [Fact p.Prime] in
theorem pow_mod_of_pow_eq_one (hg : g ^ p = 1) (n : ℕ) : g ^ (n % p) = g ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hg, one_pow, mul_one]

theorem pow_natCast_val (hg : g ^ p = 1) (n : ℕ) : g ^ ((n : ZMod p).val) = g ^ n := by
  rw [ZMod.val_natCast, pow_mod_of_pow_eq_one hg]

theorem pow_val_add (hg : g ^ p = 1) (a b : ZMod p) : g ^ a.val * g ^ b.val = g ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add, pow_mod_of_pow_eq_one hg]

theorem pow_val_pow (hg : g ^ p = 1) (a : ZMod p) (n : ℕ) : (g ^ a.val) ^ n = g ^ (a * n).val := by
  have e : ((a.val * n : ℕ) : ZMod p) = a * n := by simp
  rw [← pow_mul, ← pow_natCast_val hg (a.val * n), e]

theorem pow_val_inj (hg : orderOf g = p) {a b : ZMod p} (h : g ^ a.val = g ^ b.val) : a = b := by
  rw [pow_eq_pow_iff_modEq, hg] at h
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

theorem pow_val_eq_one (hg : orderOf g = p) {a : ZMod p} (h : g ^ a.val = 1) : a = 0 :=
  pow_val_inj hg (by rw [h, ZMod.val_zero, pow_zero])

theorem exists_pow_val (hg : g ^ p = 1) {y : G} (hy : y ∈ zpowers g) : ∃ k : ZMod p, g ^ k.val = y := by
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : p.Prime).pos, hg⟩
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y g).mp (hfin.mem_powers_iff_mem_zpowers.mpr hy)
  exact ⟨n, pow_natCast_val hg n⟩

theorem pow_coef (hg : g ^ p = 1) {y : G} (hy : y ∈ zpowers g) : g ^ (coef p g y).val = y := by
  have h := exists_pow_val hg hy
  unfold coef
  split_ifs
  exact h.choose_spec

theorem coef_pow (hg : orderOf g = p) (k : ZMod p) : coef p g (g ^ k.val) = k :=
  pow_val_inj hg (pow_coef (hg ▸ pow_orderOf_eq_one g) (pow_mem (mem_zpowers g) _))

theorem coef_one (hg : orderOf g = p) : coef p g 1 = 0 := by
  simpa using coef_pow hg 0

theorem orderOf_eq_of_card {H : Subgroup G} (hH : Nat.card H = p) {w : G} (hw : w ∈ H)
    (hw1 : w ≠ 1) : orderOf w = p ∧ zpowers w = H := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact (Fact.out : p.Prime).ne_zero)
  have hdvd : orderOf w ∣ p := by
    rw [← hH, ← Subgroup.orderOf_mk w hw]; exact orderOf_dvd_natCard _
  have ho : orderOf w = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  refine ⟨ho, Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hw) ?_⟩
  rw [hH, Nat.card_zpowers, ho]

theorem mul3_pow_val {g h k : G} (hg : g ^ p = 1) (hh : h ^ p = 1) (hk : k ^ p = 1)
    (hgh : Commute g h) (hgk : Commute g k) (hhk : Commute h k) (a b c a' b' c' : ZMod p) :
    g ^ a.val * h ^ b.val * k ^ c.val * (g ^ a'.val * h ^ b'.val * k ^ c'.val) =
      g ^ (a + a').val * h ^ (b + b').val * k ^ (c + c').val := by
  have h1 : Commute (h ^ b.val * k ^ c.val) (g ^ a'.val) :=
    (hgh.symm.pow_pow _ _).mul_left (hgk.symm.pow_pow _ _)
  have h2 : Commute (k ^ c.val) (h ^ b'.val) := hhk.symm.pow_pow _ _
  calc g ^ a.val * h ^ b.val * k ^ c.val * (g ^ a'.val * h ^ b'.val * k ^ c'.val)
      = g ^ a.val * ((h ^ b.val * k ^ c.val) * g ^ a'.val) * h ^ b'.val * k ^ c'.val := by
        simp only [mul_assoc]
    _ = g ^ a.val * (g ^ a'.val * (h ^ b.val * k ^ c.val)) * h ^ b'.val * k ^ c'.val := by
        rw [h1.eq]
    _ = g ^ a.val * g ^ a'.val * h ^ b.val * (k ^ c.val * h ^ b'.val) * k ^ c'.val := by
        simp only [mul_assoc]
    _ = g ^ a.val * g ^ a'.val * h ^ b.val * (h ^ b'.val * k ^ c.val) * k ^ c'.val := by
        rw [h2.eq]
    _ = g ^ (a + a').val * h ^ (b + b').val * k ^ (c + c').val := by
        rw [← pow_val_add hg, ← pow_val_add hh, ← pow_val_add hk]; simp only [mul_assoc]

/-- `u, v, w` are independent: `u^a v^b w^c = 1` forces `a = b = c = 0`, when `u` is not central,
`v` is central and not in `K`, and `w ∈ K` is central of order `p`. -/
theorem indep {u v w : G} {K : Subgroup G} (hu : u ^ p = 1) (huc : u ∉ center G)
    (hvc : v ∈ center G) (hvK : v ∉ K) (hwK : w ∈ K) (hwc : w ∈ center G) (hwo : orderOf w = p)
    (hv : v ^ p = 1) {a b c : ZMod p} (h : u ^ a.val * v ^ b.val * w ^ c.val = 1) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have root : ∀ {g : G}, g ^ p = 1 → ∀ {a : ZMod p}, a ≠ 0 → (g ^ a.val) ^ (a⁻¹).val = g := by
    intro g hg a ha
    rw [pow_val_pow hg, ZMod.natCast_zmod_val, mul_inv_cancel₀ ha, ZMod.val_one, pow_one]
  have ha : a = 0 := by
    by_contra ha
    apply huc
    have e : u ^ a.val = (v ^ b.val * w ^ c.val)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h)
    rw [← root hu ha, e]
    exact pow_mem (inv_mem (mul_mem (pow_mem hvc _) (pow_mem hwc _))) _
  subst ha
  rw [ZMod.val_zero, pow_zero, one_mul] at h
  have hb : b = 0 := by
    by_contra hb
    apply hvK
    rw [← root hv hb, eq_inv_of_mul_eq_one_left h]
    exact pow_mem (inv_mem (pow_mem hwK _)) _
  subst hb
  rw [ZMod.val_zero, pow_zero, one_mul] at h
  exact ⟨rfl, rfl, pow_val_eq_one hwo h⟩

end General

/-- The standing hypotheses: `P` of type `(·, 2, 1)` with `P/γ₂(P)` elementary abelian, and
`π : Q → P` onto with kernel `⟨z⟩` central of order `p`, and `γ₄(Q) ≠ 1`. -/
structure Setup {Q P : Type*} [Group Q] [Group P] (p : ℕ) (π : Q →* P) (z : Q) : Prop where
  hp2 : p ≠ 2
  surj : Function.Surjective π
  ker : π.ker = zpowers z
  central : z ∈ center Q
  order : orderOf z = p
  h4 : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥
  h2 : ((⊤ : Subgroup P).lowerCentralSeries 2).relIndex ((⊤ : Subgroup P).lowerCentralSeries 1) = p ^ 2
  h3 : Nat.card ((⊤ : Subgroup P).lowerCentralSeries 2) = p
  hel : ∀ x : P, x ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 1
  hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥

namespace Setup

variable {Q P : Type*} [Group Q] [Group P] {p : ℕ} [Fact p.Prime] {π : Q →* P} {z : Q}
  (S : Setup p π z)
include S

theorem two_lt : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm S.hp2)

theorem pow_choose_two {G : Type*} [Group G] {g : G} (hg : g ^ p = 1) : g ^ p.choose 2 = 1 := by
  obtain ⟨m, hm⟩ := Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num : (2 : ℕ) ≠ 0) S.two_lt
  rw [hm, pow_mul, hg, one_pow]

theorem choose_three_cast : ((p.choose 3 : ℕ) : ZMod p) = if p = 3 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have h3 : 3 < p := by have := (Fact.out : p.Prime).two_le; have := S.hp2; omega
    obtain ⟨m, hm⟩ := Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num : (3 : ℕ) ≠ 0) h3
    rw [hm, Nat.cast_mul, ZMod.natCast_self, zero_mul]

omit [Fact p.Prime] in
theorem pz : z ^ p = 1 := S.order ▸ pow_orderOf_eq_one z

omit [Fact p.Prime] in
theorem mem_center_of_mem_zpowers {g : Q} (hg : g ∈ zpowers z) : g ∈ center Q :=
  zpowers_le.mpr S.central hg

omit [Fact p.Prime] in
theorem pow_z_central (k : ℕ) : z ^ k ∈ center Q := pow_mem S.central k

omit [Fact p.Prime] in
theorem map_mem {k : ℕ} {g : Q} (hg : g ∈ (⊤ : Subgroup Q).lowerCentralSeries k) : π g ∈ (⊤ : Subgroup P).lowerCentralSeries k := by
  rw [← lcs_map_of_surjective S.surj k]; exact mem_map_of_mem π hg

omit [Fact p.Prime] in
theorem exists_lift {k : ℕ} {y : P} (hy : y ∈ (⊤ : Subgroup P).lowerCentralSeries k) : ∃ y' ∈ (⊤ : Subgroup Q).lowerCentralSeries k, π y' = y := by
  rw [← lcs_map_of_surjective S.surj k] at hy
  exact Subgroup.mem_map.mp hy

theorem exists_eq_mul {g h : Q} (he : π g = π h) : ∃ k : ZMod p, g = h * z ^ k.val := by
  have : h⁻¹ * g ∈ zpowers z := by
    rw [← S.ker, MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  obtain ⟨k, hk⟩ := exists_pow_val S.pz this
  exact ⟨k, by rw [hk, mul_inv_cancel_left]⟩

omit [Fact p.Prime] in
theorem map_z_pow (k : ℕ) : π (z ^ k) = 1 := by
  have : z ^ k ∈ π.ker := by rw [S.ker]; exact pow_mem (mem_zpowers z) k
  exact this

omit [Fact p.Prime] in
theorem lcs3_le : (⊤ : Subgroup Q).lowerCentralSeries 3 ≤ zpowers z := by
  rw [← S.ker, ← Subgroup.map_eq_bot_iff, lcs_map_of_surjective S.surj 3, S.h4]

omit [Fact p.Prime] in
theorem mem_center_of_lcs3 {g : Q} (hg : g ∈ (⊤ : Subgroup Q).lowerCentralSeries 3) : g ∈ center Q :=
  S.mem_center_of_mem_zpowers (S.lcs3_le hg)

theorem z_mem_lcs3 : z ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.hQ
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  obtain ⟨k, rfl⟩ := exists_pow_val S.pz (S.lcs3_le hg)
  have hk : k ≠ 0 := by rintro rfl; exact hg1' (by rw [ZMod.val_zero, pow_zero])
  have e : (z ^ k.val) ^ (k⁻¹).val = z := by
    rw [pow_val_pow S.pz, ZMod.natCast_zmod_val, mul_inv_cancel₀ hk, ZMod.val_one, pow_one]
  rw [← e]; exact pow_mem hg _

theorem pow_z_mem_lcs1 (k : ℕ) : z ^ k ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 :=
  pow_mem (lcs_mem_of_le (by norm_num) S.z_mem_lcs3) k

theorem metabelian : derivedSeries Q 2 = ⊥ :=
  metabelian_of_central_ext_card S.hp2 S.surj (by rw [S.ker]; exact zpowers_le.mpr S.central)
    (by rw [S.ker, Nat.card_zpowers, S.order]) S.h4 S.h2 S.h3

/-- `γ₂(Q)` is abelian. -/
theorem comm1 {a b : Q} (ha : a ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) (hb : b ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) : Commute a b := by
  have h : ⁅a, b⁆ ∈ derivedSeries Q 2 := commutator_mem_commutator ha hb
  rw [S.metabelian, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

omit [Fact p.Prime] in
theorem P_lcs2_central {g : P} (hg : g ∈ (⊤ : Subgroup P).lowerCentralSeries 2) : g ∈ center P := by
  rw [mem_center_iff]; intro y
  have h : ⁅g, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 3 := commutator_mem_lcs (by norm_num) hg (mem_lcs_zero y)
  rw [S.h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h.symm

omit [Fact p.Prime] in
/-- `γ₂(P)` is abelian. -/
theorem P_comm1 {a b : P} (ha : a ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hb : b ∈ (⊤ : Subgroup P).lowerCentralSeries 1) : Commute a b := by
  have h : ⁅a, b⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 3 := commutator_mem_lcs (by norm_num) ha hb
  rw [S.h4, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

omit [Fact p.Prime] in
theorem P_card_lcs1 : Nat.card ((⊤ : Subgroup P).lowerCentralSeries 1) = p ^ 3 := by
  have hle : (⊤ : Subgroup P).lowerCentralSeries 2 ≤ (⊤ : Subgroup P).lowerCentralSeries 1 := fun g hg => lcs_mem_of_le (by norm_num) hg
  have h := Subgroup.card_mul_index (H := ((⊤ : Subgroup P).lowerCentralSeries 2).subgroupOf ((⊤ : Subgroup P).lowerCentralSeries 1))
  have h2 := S.h2
  rw [Subgroup.relIndex] at h2
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, S.h3, h2] at h
  rw [← h]; ring

/-- `[ℓ, y]^p = 1` for `ℓ ∈ γ₂(Q)`. -/
theorem pc_pow_p_lcs1 {ℓ : Q} (hℓ : ℓ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) (y : Q) : pc ℓ y ^ p = 1 := by
  have hb : pc ℓ y ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := pc_mem (by norm_num) hℓ (mem_lcs_zero y)
  have hc : pc (pc ℓ y) y ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 := pc_mem (by norm_num) hb (mem_lcs_zero y)
  have hcc := S.mem_center_of_lcs3 hc
  have hf := conj_pow_formula (a := ℓ) (x := y) rfl rfl (pc_of_mem_center hcc y)
    (mem_center_iff.mp hcc _) p
  have hcp : pc (pc ℓ y) y ^ p = 1 := by
    obtain ⟨k, hk⟩ := exists_pow_val S.pz (S.lcs3_le hc)
    rw [← hk, ← pow_mul, mul_comm, pow_mul, S.pz, one_pow]
  obtain ⟨ℓ0, hℓ0, he⟩ := S.exists_lift (S.hel (π y))
  obtain ⟨k, hk⟩ := S.exists_eq_mul (g := y ^ p) (h := ℓ0) (by rw [map_pow, he])
  have hyp : y ^ p ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := by rw [hk]; exact mul_mem hℓ0 (S.pow_z_mem_lcs1 _)
  have hconj : (y ^ p)⁻¹ * ℓ * y ^ p = ℓ := by
    rw [mul_assoc, (S.comm1 hℓ hyp).eq, inv_mul_cancel_left]
  rw [hconj, S.pow_choose_two hcp, mul_one] at hf
  exact mul_left_cancel (a := ℓ) (by rw [mul_one]; exact hf.symm)

/-- `γ₃(Q)` has exponent `p`. -/
theorem pow_p_lcs2 {g : Q} (hg : g ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) : g ^ p = 1 := by
  let T : Subgroup Q :=
    { carrier := {g | g ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 ∧ g ^ p = 1}
      mul_mem' := fun {a b} ha hb =>
        ⟨mul_mem ha.1 hb.1, by rw [(S.comm1 ha.1 hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hle : (⊤ : Subgroup Q).lowerCentralSeries 2 ≤ T := by
    show ⁅(⊤ : Subgroup Q).lowerCentralSeries 1, ⊤⁆ ≤ T
    rw [commutator_le]
    intro a ha b _
    rw [comm_eq_pc]
    exact ⟨pc_mem_one _ _, S.pc_pow_p_lcs1 (inv_mem ha) _⟩
  exact (hle hg).2

/-! ### A generator `w` of `γ₃(P)`, a lift `w'`, and `ψ` with `[w', y] = z^{ψ(y)}` -/

section W

variable {w : P} {w' : Q}

omit [Fact p.Prime] in
theorem pc_w'_mem (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (y : Q) : pc w' y ∈ zpowers z :=
  S.lcs3_le (pc_mem (by norm_num) hw' (mem_lcs_zero y))

theorem pc_w'_pow (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (n : ℕ) (y : Q) :
    pc (w' ^ n) y = z ^ (coef p z (pc w' y) * n).val := by
  rw [pc_pow (mem_center_iff.mp (S.mem_center_of_mem_zpowers (S.pc_w'_mem hw' y)) w')]
  conv_lhs => rw [← pow_coef S.pz (S.pc_w'_mem hw' y)]
  rw [pow_val_pow S.pz]

theorem pc_lift_eq (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hπw : π w' = w) {ℓ : Q}
    (hℓ : ℓ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) (x : Q) :
    ∃ m : ZMod p, pc ℓ x = w' ^ (coef p w (pc (π ℓ) (π x))).val * z ^ m.val := by
  obtain ⟨hwo, hzw⟩ := orderOf_eq_of_card S.h3 hw2 hw1
  have hmem : pc (π ℓ) (π x) ∈ zpowers w := hzw ▸ pc_mem (by norm_num) (S.map_mem hℓ) (mem_lcs_zero _)
  apply S.exists_eq_mul
  rw [map_pow, hπw, pow_coef (hwo ▸ pow_orderOf_eq_one w) hmem]
  simp only [pc, map_mul, map_inv]

theorem pc_pc_lift (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (hπw : π w' = w)
    {ℓ : Q} (hℓ : ℓ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) (x y : Q) :
    pc (pc ℓ x) y = z ^ (coef p z (pc w' y) * coef p w (pc (π ℓ) (π x))).val := by
  obtain ⟨m, hm⟩ := S.pc_lift_eq hw2 hw1 hπw hℓ x
  rw [hm, pc_mul_central (S.pow_z_central _), S.pc_w'_pow hw', ZMod.natCast_zmod_val]

/-- **Step 2 of the paper**: `φ_ℓ(x) ψ(y) = φ_ℓ(y) ψ(x)`, where `[ℓ, x] ≡ w^{φ_ℓ(x)}` and
`[w', y] = z^{ψ(y)}`. -/
theorem psi_phi_symm (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (hπw : π w' = w)
    {ℓ : Q} (hℓ : ℓ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1) (x y : Q) :
    coef p z (pc w' y) * coef p w (pc (π ℓ) (π x)) =
      coef p z (pc w' x) * coef p w (pc (π ℓ) (π y)) := by
  have h := pc_pc_symm (A := (⊤ : Subgroup Q).lowerCentralSeries 1) (fun a ha b hb => (S.comm1 ha hb).eq) pc_mem_one hℓ x y
  rw [S.pc_pc_lift hw2 hw1 hw' hπw hℓ x y, S.pc_pc_lift hw2 hw1 hw' hπw hℓ y x] at h
  exact pow_val_inj S.order h

/-- `ψ ≠ 0`, since `γ₄(Q) = [γ₃(Q), Q] ≠ 1`. -/
theorem exists_psi_ne (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (hπw : π w' = w) :
    ∃ y, coef p z (pc w' y) ≠ 0 := by
  obtain ⟨hwo, hzw⟩ := orderOf_eq_of_card S.h3 hw2 hw1
  by_contra h
  push Not at h
  have hwc : w' ∈ center Q := mem_center_of_pc fun y => by
    rw [← pow_coef S.pz (S.pc_w'_mem hw' y), h y, ZMod.val_zero, pow_zero]
  apply S.hQ
  rw [eq_bot_iff]
  show ⁅(⊤ : Subgroup Q).lowerCentralSeries 2, ⊤⁆ ≤ ⊥
  rw [commutator_le]
  intro g hg y _
  have hmem : π g ∈ zpowers w := hzw ▸ S.map_mem hg
  obtain ⟨k, hk⟩ := exists_pow_val (hwo ▸ pow_orderOf_eq_one w) hmem
  obtain ⟨m, hm⟩ := S.exists_eq_mul (g := g) (h := w' ^ k.val) (by rw [map_pow, hπw, hk])
  have hgc : g ∈ center Q := by rw [hm]; exact mul_mem (pow_mem hwc _) (S.pow_z_central _)
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (mem_center_iff.mp hgc y).symm

omit [Fact p.Prime] in
/-- `[a, b]^p ∈ γ₃(P)`. -/
theorem P_pc_pow_mem (a b : P) : pc a b ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 2 := by
  have hs : pc a b ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := pc_mem_one a b
  have ht : pc (pc a b) a ∈ (⊤ : Subgroup P).lowerCentralSeries 2 := pc_mem (by norm_num) hs (mem_lcs_zero a)
  have htc := S.P_lcs2_central ht
  have hc1 : pc (pc (pc a b) a) a = 1 := pc_of_mem_center htc a
  have hcm : pc (pc (pc a b) a) a ∈ (⊤ : Subgroup P).lowerCentralSeries 2 := by rw [hc1]; exact one_mem _
  have hf := mul_pow_formula (a := pc a b) (x := a) rfl rfl (by rw [hc1]; simp [pc])
    (mem_center_iff.mp htc _) (by rw [hc1]; exact Commute.one_right _)
    (by rw [hc1]; exact Commute.one_right _) p
  have e : b⁻¹ * a ^ p * b = a ^ p * (pc a b ^ p * pc (pc a b) a ^ p.choose 2 *
      pc (pc (pc a b) a) a ^ p.choose 3) := by
    rw [← conj_pow', conj_eq_mul_pc, hf]
  have e2 : pc (a ^ p) b = (a ^ p)⁻¹ * (b⁻¹ * a ^ p * b) := by simp only [pc]; group
  have : pc a b ^ p = pc (a ^ p) b *
      (pc (pc a b) a ^ p.choose 2 * pc (pc (pc a b) a) a ^ p.choose 3)⁻¹ := by
    rw [e2, e]; group
  rw [this]
  exact mul_mem (pc_mem (by norm_num) (S.hel a) (mem_lcs_zero b))
    (inv_mem (mul_mem (pow_mem ht _) (pow_mem hcm _)))

omit [Fact p.Prime] in
/-- `γ₂(P)/γ₃(P)` has exponent `p`. -/
theorem P_pow_mem_lcs2 {g : P} (hg : g ∈ (⊤ : Subgroup P).lowerCentralSeries 1) : g ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 2 := by
  let T : Subgroup P :=
    { carrier := {g | g ∈ (⊤ : Subgroup P).lowerCentralSeries 1 ∧ g ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 2}
      mul_mem' := fun {a b} ha hb =>
        ⟨mul_mem ha.1 hb.1, by rw [(S.P_comm1 ha.1 hb.1).mul_pow]; exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow]; exact inv_mem ha.2⟩ }
  have hle : (⊤ : Subgroup P).lowerCentralSeries 1 ≤ T := by
    show ⁅(⊤ : Subgroup P).lowerCentralSeries 0, ⊤⁆ ≤ T
    rw [commutator_le]
    intro a _ b _
    rw [comm_eq_pc]
    exact ⟨pc_mem_one _ _, S.P_pc_pow_mem _ _⟩
  exact (hle hg).2

/-- **(N2)**: `γ₂(P)` has exponent `p`. -/
theorem N2_exp (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (hπw : π w' = w)
    {ℓ : P} (hℓ : ℓ ∈ (⊤ : Subgroup P).lowerCentralSeries 1) : ℓ ^ p = 1 := by
  obtain ⟨hwo, hzw⟩ := orderOf_eq_of_card S.h3 hw2 hw1
  obtain ⟨ℓ', hℓ', rfl⟩ := S.exists_lift hℓ
  obtain ⟨y0, hy0⟩ := S.exists_psi_ne hw2 hw1 hw' hπw
  have hcent : ∀ y, pc (ℓ' ^ p) y = 1 := fun y => by
    rw [pc_pow (S.comm1 hℓ' (pc_mem_one ℓ' y)), S.pc_pow_p_lcs1 hℓ' y]
  have hmem : π ℓ' ^ p ∈ zpowers w := hzw ▸ S.P_pow_mem_lcs2 hℓ
  obtain ⟨k, hk⟩ := exists_pow_val (hwo ▸ pow_orderOf_eq_one w) hmem
  obtain ⟨m, hm⟩ := S.exists_eq_mul (g := ℓ' ^ p) (h := w' ^ k.val)
    (by rw [map_pow, map_pow, hπw, hk])
  have h0 := hcent y0
  rw [hm, pc_mul_central (S.pow_z_central _), S.pc_w'_pow hw'] at h0
  have hk0 := pow_val_eq_one S.order h0
  rw [ZMod.natCast_zmod_val] at hk0
  have : k = 0 := (mul_eq_zero.mp hk0).resolve_left hy0
  rw [← hk, this, ZMod.val_zero, pow_zero]

/-- **(N3)**: `x^p` is central in `P`. -/
theorem N3 (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (hπw : π w' = w) (x : P) :
    x ^ p ∈ center P := by
  apply mem_center_of_pc
  intro y
  have ha : pc x y ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := pc_mem_one x y
  have hb : pc (pc x y) x ∈ (⊤ : Subgroup P).lowerCentralSeries 2 := pc_mem (by norm_num) ha (mem_lcs_zero x)
  have hb1 : pc (pc x y) x ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := lcs_mem_of_le (by norm_num) hb
  have hc : pc (pc (pc x y) x) x = 1 := by
    have h : pc (pc (pc x y) x) x ∈ (⊤ : Subgroup P).lowerCentralSeries 3 := pc_mem (by norm_num) hb (mem_lcs_zero x)
    rwa [S.h4, mem_bot] at h
  have hf := mul_pow_formula (a := pc x y) (x := x) rfl rfl (by rw [hc]; simp [pc])
    (S.P_comm1 ha hb1) (by rw [hc]; exact Commute.one_right _)
    (by rw [hc]; exact Commute.one_right _) p
  rw [hc, one_pow, mul_one, S.N2_exp hw2 hw1 hw' hπw ha, one_mul,
    S.pow_choose_two (S.N2_exp hw2 hw1 hw' hπw hb1), mul_one] at hf
  have e : y⁻¹ * x ^ p * y = x ^ p := by rw [← conj_pow', conj_eq_mul_pc, hf]
  rw [conj_eq_mul_pc] at e
  exact mul_left_cancel (e.trans (mul_one _).symm)

/-- **(N1)**: `|Z(P) ∩ γ₂(P)| = p²`. -/
theorem N1 (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hw' : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 2) (hπw : π w' = w) :
    Nat.card (center P ⊓ ((⊤ : Subgroup P).lowerCentralSeries 1) : Subgroup P) = p ^ 2 := by
  obtain ⟨hwo, hzw⟩ := orderOf_eq_of_card S.h3 hw2 hw1
  have hwp : w ^ p = 1 := hwo ▸ pow_orderOf_eq_one w
  obtain ⟨y0, hy0⟩ := S.exists_psi_ne hw2 hw1 hw' hπw
  have hmem : ∀ ℓ ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ∀ x : P, pc ℓ x ∈ zpowers w := fun ℓ hℓ x =>
    hzw ▸ pc_mem (by norm_num) hℓ (mem_lcs_zero x)
  -- `ℓ ∈ γ₂(P)` is central iff `φ_ℓ(y₀) = 0`
  have hker : ∀ ℓ ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ℓ ∈ center P ↔ coef p w (pc ℓ (π y0)) = 0 := by
    intro ℓ hℓ
    constructor
    · intro hc; rw [pc_of_mem_center hc, coef_one hwo]
    · intro h0
      apply mem_center_of_pc
      intro x
      obtain ⟨x', rfl⟩ := S.surj x
      obtain ⟨ℓ', hℓ', rfl⟩ := S.exists_lift hℓ
      have hs := S.psi_phi_symm hw2 hw1 hw' hπw hℓ' x' y0
      rw [h0, mul_zero] at hs
      have h1 : coef p w (pc (π ℓ') (π x')) = 0 := (mul_eq_zero.mp hs).resolve_left hy0
      rw [← pow_coef hwp (hmem _ hℓ _), h1, ZMod.val_zero, pow_zero]
  have hadd : ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
      coef p w (pc (a * b) (π y0)) = coef p w (pc a (π y0)) + coef p w (pc b (π y0)) := by
    intro a ha b hb
    rw [pc_mul (mem_center_iff.mp (S.P_lcs2_central (pc_mem (by norm_num) ha (mem_lcs_zero _))) b)]
    conv_lhs => rw [← pow_coef hwp (hmem a ha _), ← pow_coef hwp (hmem b hb _), pow_val_add hwp,
      coef_pow hwo]
  let Φ : (⊤ : Subgroup P).lowerCentralSeries 1 →* Multiplicative (ZMod p) :=
    { toFun := fun ℓ => Multiplicative.ofAdd (coef p w (pc (ℓ : P) (π y0)))
      map_one' := by simp [pc, coef_one hwo]
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul]; rw [hadd _ a.2 _ b.2, ofAdd_add] }
  -- some `ℓ ∈ γ₂(P)` is not central, as `γ₃(P) ≠ 1`
  obtain ⟨ℓ0, hℓ0, hℓ0c⟩ : ∃ ℓ ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ℓ ∉ center P := by
    by_contra h
    push Not at h
    have h0 : (⊤ : Subgroup P).lowerCentralSeries 2 = ⊥ := by
      rw [eq_bot_iff]
      show ⁅(⊤ : Subgroup P).lowerCentralSeries 1, ⊤⁆ ≤ ⊥
      rw [commutator_le]
      intro a ha b _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp (h a ha) b).symm
    have h3 := S.h3
    rw [h0, Subgroup.card_bot] at h3
    exact (Fact.out : p.Prime).one_lt.ne h3
  have hcardM : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have : Fact (Nat.card (Multiplicative (ZMod p))).Prime := ⟨by rw [hcardM]; exact (Fact.out : p.Prime)⟩
  have hrange : Φ.range = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card Φ.range with h | h
    · exfalso
      apply hℓ0c
      rw [hker ℓ0 hℓ0]
      have h1 : Φ ⟨ℓ0, hℓ0⟩ ∈ Φ.range := ⟨_, rfl⟩
      rw [h, mem_bot] at h1
      exact ofAdd_eq_one.mp h1
    · exact h
  have hidx : Φ.ker.index = p := by rw [Subgroup.index_ker, hrange, Subgroup.card_top, hcardM]
  have hkerEq : Φ.ker = (center P ⊓ ((⊤ : Subgroup P).lowerCentralSeries 1)).subgroupOf ((⊤ : Subgroup P).lowerCentralSeries 1) := by
    ext ℓ
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, hker ℓ ℓ.2]
    constructor
    · intro h; exact ⟨ofAdd_eq_one.mp h, ℓ.2⟩
    · rintro ⟨h, -⟩; exact ofAdd_eq_one.mpr h
  have hmul := Subgroup.card_mul_index (H := Φ.ker)
  rw [hidx, hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
    S.P_card_lcs1, show p ^ 3 = p ^ 2 * p by ring] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hmul

end W

/-- **(N4)**: for any normal form of `P`, the system (E)+(J) has a solution with `c = 1`. -/
theorem N4 {d : ℕ} (x : Fin d → P) {u v w : P} {ω₁ ω₂ ω₃ : Fin d → Fin d → ZMod p}
    {α β f : Fin d → ZMod p} (hw2 : w ∈ (⊤ : Subgroup P).lowerCentralSeries 2) (hw1 : w ≠ 1) (hvc : v ∈ center P)
    (hv1 : v ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (hv2 : v ∉ (⊤ : Subgroup P).lowerCentralSeries 2) (hu : u ∈ (⊤ : Subgroup P).lowerCentralSeries 1) (huc : u ∉ center P)
    (hω : ∀ i j, (x i)⁻¹ * (x j)⁻¹ * x i * x j =
      u ^ (ω₁ i j).val * v ^ (ω₂ i j).val * w ^ (ω₃ i j).val)
    (hpow : ∀ i, x i ^ p = v ^ (α i).val * w ^ (β i).val)
    (hf : ∀ i, u⁻¹ * (x i)⁻¹ * u * x i = w ^ (f i).val) :
    ∃ μu μv : ZMod p, ∃ η σ : Fin d → ZMod p, SystemEJ ω₁ ω₂ ω₃ α β f 1 μu μv η σ := by
  obtain ⟨hwo, hzw⟩ := orderOf_eq_of_card S.h3 hw2 hw1
  have hwp : w ^ p = 1 := hwo ▸ pow_orderOf_eq_one w
  have hwc : w ∈ center P := S.P_lcs2_central hw2
  have hw1' : w ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := lcs_mem_of_le (by norm_num) hw2
  obtain ⟨w', hw', hπw⟩ := S.exists_lift hw2
  have hw'1 : w' ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := lcs_mem_of_le (by norm_num) hw'
  have hw'p : w' ^ p = 1 := S.pow_p_lcs2 hw'
  obtain ⟨u', hu', hπu⟩ := S.exists_lift hu
  obtain ⟨v', hv', hπv⟩ := S.exists_lift hv1
  choose x' hx' using fun i => S.surj (x i)
  have hexp : ∀ g ∈ (⊤ : Subgroup P).lowerCentralSeries 1, g ^ p = 1 := fun g hg => S.N2_exp hw2 hw1 hw' hπw hg
  -- the `ω_r` are alternating
  have hanti : ∀ i j, ω₁ j i = -ω₁ i j ∧ ω₂ j i = -ω₂ i j ∧ ω₃ j i = -ω₃ i j := by
    intro i j
    have e : (x j)⁻¹ * (x i)⁻¹ * x j * x i = ((x i)⁻¹ * (x j)⁻¹ * x i * x j)⁻¹ := by group
    rw [hω j i, hω i j] at e
    have h1 := mul_eq_one_iff_eq_inv.mpr e
    rw [mul3_pow_val (hexp u hu) (hexp v hv1) hwp (S.P_comm1 hu hv1) (S.P_comm1 hu hw1')
      (S.P_comm1 hv1 hw1')] at h1
    obtain ⟨h₁, h₂, h₃⟩ := indep (hexp u hu) huc hvc hv2 hw2 hwc hwo (hexp v hv1) h1
    exact ⟨eq_neg_of_add_eq_zero_left h₁, eq_neg_of_add_eq_zero_left h₂,
      eq_neg_of_add_eq_zero_left h₃⟩
  -- the unknowns: `[v, x_i] = z^{η_i}`, `[u, x_i] = w^{f_i} z^{σ_i}`, `u^p = z^{μ_u}`, `v^p = z^{μ_v}`
  have hker' : ∀ g : Q, π g = 1 → g ∈ zpowers z := fun g hg => by rw [← S.ker]; exact hg
  choose η hη using fun i => exists_pow_val S.pz (hker' (pc v' (x' i)) (by
    simp only [pc, map_mul, map_inv, hπv, hx']; exact pc_of_mem_center hvc (x i)))
  choose σ hσ using fun i => S.exists_eq_mul (g := pc u' (x' i)) (h := w' ^ (f i).val) (by
    simp only [pc, map_mul, map_inv, map_pow, hπu, hπw, hx']; exact hf i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Q → ZMod p, ∀ y, pc w' y = z ^ (ψ y).val :=
    ⟨fun y => coef p z (pc w' y), fun y => (pow_coef S.pz (S.pc_w'_mem hw' y)).symm⟩
  have hψcoef : ∀ y, coef p z (pc w' y) = ψ y := fun y => by rw [hψ, coef_pow S.order]
  obtain ⟨μu, hμu⟩ := exists_pow_val S.pz (hker' (u' ^ p) (by rw [map_pow, hπu, hexp u hu]))
  obtain ⟨μv, hμv⟩ := exists_pow_val S.pz (hker' (v' ^ p) (by rw [map_pow, hπv, hexp v hv1]))
  -- `ψ = c f` with `c ≠ 0` (Step 2)
  have hφ : ∀ y : Q, pc u (π y) ∈ zpowers w := fun y =>
    hzw ▸ pc_mem (by norm_num) hu (mem_lcs_zero _)
  obtain ⟨g1, hg1⟩ : ∃ g, g * u ≠ u * g := by
    by_contra h; push Not at h; exact huc (mem_center_iff.mpr h)
  obtain ⟨y1, rfl⟩ := S.surj g1
  have hφ1 : coef p w (pc u (π y1)) ≠ 0 := by
    intro h0
    apply hg1
    have h1 : pc u (π y1) = 1 := by rw [← pow_coef hwp (hφ y1), h0, ZMod.val_zero, pow_zero]
    exact (pc_eq_one_iff.mp h1).symm
  have hsym : ∀ y t : Q, ψ t * coef p w (pc u (π y)) = ψ y * coef p w (pc u (π t)) := by
    intro y t
    have h := S.psi_phi_symm hw2 hw1 hw' hπw hu' y t
    rwa [hψcoef, hψcoef, hπu] at h
  have hψc' : ∀ y, ψ y = ψ y1 / coef p w (pc u (π y1)) * coef p w (pc u (π y)) := by
    intro y
    rw [div_mul_eq_mul_div, eq_div_iff hφ1]
    exact (hsym y y1).symm
  generalize hcdef : ψ y1 / coef p w (pc u (π y1)) = c at hψc'
  have hc0 : c ≠ 0 := by
    obtain ⟨y0, hy0⟩ := S.exists_psi_ne hw2 hw1 hw' hπw
    intro h0; apply hy0; rw [hψcoef, hψc', h0, zero_mul]
  have hψx : ∀ i, ψ (x' i) = c * f i := by
    intro i
    rw [hψc', hx', show pc u (x i) = w ^ (f i).val from hf i, coef_pow hwo]
  -- `[u^{n₁} v^{n₂} w^{n₃} z^m, x_k]`
  have GA : ∀ (k : Fin d) (n₁ n₂ n₃ : ℕ) (m : ZMod p),
      pc (u' ^ n₁ * v' ^ n₂ * w' ^ n₃ * z ^ m.val) (x' k) =
        w' ^ ((f k).val * n₁) * z ^ (σ k * n₁ + η k * n₂ + ψ (x' k) * n₃).val := by
    intro k n₁ n₂ n₃ m
    rw [pc_mul_central (S.pow_z_central _), pc_mul (S.comm1 (pow_mem hw'1 n₃) (pc_mem_one _ _)),
      pc_mul (S.comm1 (pow_mem hv' n₂) (pc_mem_one _ _)), pc_pow (S.comm1 hu' (pc_mem_one _ _)),
      pc_pow (S.comm1 hv' (pc_mem_one _ _)), pc_pow (S.comm1 hw'1 (pc_mem_one _ _)), hσ k,
      ← hη k, hψ,
      Commute.mul_pow (mem_center_iff.mp (S.pow_z_central (σ k).val) (w' ^ (f k).val)) n₁,
      ← pow_mul, pow_val_pow S.pz, pow_val_pow S.pz, pow_val_pow S.pz, mul_assoc, mul_assoc,
      pow_val_add S.pz, pow_val_add S.pz, add_assoc]
  -- `(u^{n₁} v^{n₂} w^{n₃} z^m)^p`
  have hap : ∀ (n₁ n₂ n₃ : ℕ) (m : ZMod p),
      (u' ^ n₁ * v' ^ n₂ * w' ^ n₃ * z ^ m.val) ^ p = z ^ (μu * n₁ + μv * n₂).val := by
    intro n₁ n₂ n₃ m
    have h12 : u' ^ n₁ * v' ^ n₂ ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := mul_mem (pow_mem hu' _) (pow_mem hv' _)
    rw [(S.comm1 (mul_mem h12 (pow_mem hw'1 _)) (S.pow_z_mem_lcs1 _)).mul_pow,
      (S.comm1 h12 (pow_mem hw'1 _)).mul_pow, (S.comm1 (pow_mem hu' _) (pow_mem hv' _)).mul_pow,
      pow_right_comm u', pow_right_comm v', pow_right_comm w', hw'p, one_pow, mul_one,
      pow_val_pow S.pz, ZMod.natCast_self, mul_zero, ZMod.val_zero, pow_zero, mul_one, ← hμu, ← hμv,
      pow_val_pow S.pz, pow_val_pow S.pz, pow_val_add S.pz]
  -- (E)
  have hE : ∀ i j, α j * η i + c * β j * f i + μu * ω₁ i j + μv * ω₂ i j +
      (if p = 3 then 1 else 0) * c * f j ^ 2 * ω₁ i j = 0 := by
    intro i j
    obtain ⟨τ, hτ⟩ := S.exists_eq_mul (g := pc (x' j) (x' i))
      (h := u' ^ (ω₁ j i).val * v' ^ (ω₂ j i).val * w' ^ (ω₃ j i).val) (by
        simp only [pc, map_mul, map_inv, map_pow, hπu, hπv, hπw, hx']; exact hω j i)
    obtain ⟨ρ, hρ⟩ := S.exists_eq_mul (g := x' j ^ p)
      (h := u' ^ (0 : ℕ) * v' ^ (α j).val * w' ^ (β j).val) (by
        simp only [map_pow, map_mul, hπv, hπw, hx', pow_zero, one_mul]; exact hpow j)
    have ha1 : pc (x' j) (x' i) ∈ (⊤ : Subgroup Q).lowerCentralSeries 1 := pc_mem_one _ _
    have hb2 : pc (pc (x' j) (x' i)) (x' j) ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 := pc_mem (by norm_num) ha1 (mem_lcs_zero _)
    have hc3 : pc (pc (pc (x' j) (x' i)) (x' j)) (x' j) ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 :=
      pc_mem (by norm_num) hb2 (mem_lcs_zero _)
    have hcc := S.mem_center_of_lcs3 hc3
    have hL1 := mul_pow_formula (a := pc (x' j) (x' i)) (x := x' j) rfl rfl
      (pc_of_mem_center hcc _) (S.comm1 ha1 (lcs_mem_of_le (by norm_num) hb2))
      (mem_center_iff.mp hcc _) (mem_center_iff.mp hcc _) p
    have hconj : pc (x' j ^ p) (x' i) = pc (x' j) (x' i) ^ p *
        pc (pc (x' j) (x' i)) (x' j) ^ p.choose 2 *
        pc (pc (pc (x' j) (x' i)) (x' j)) (x' j) ^ p.choose 3 := by
      have e : (x' i)⁻¹ * x' j ^ p * x' i = x' j ^ p * pc (x' j ^ p) (x' i) := conj_eq_mul_pc _ _
      rw [← conj_pow', conj_eq_mul_pc, hL1] at e
      exact (mul_left_cancel e).symm
    rw [S.pow_choose_two (S.pow_p_lcs2 hb2), mul_one, hρ, GA i, hτ, hap, GA j,
      pc_mul_central (S.pow_z_central _), S.pc_w'_pow hw', hψcoef, pow_val_pow S.pz,
      pow_val_add S.pz, mul_zero, pow_zero, one_mul] at hconj
    have heq := pow_val_inj S.order hconj
    simp only [Nat.cast_zero, mul_zero, zero_add, Nat.cast_mul, ZMod.natCast_zmod_val, hψx,
      S.choose_three_cast, (hanti i j).1, (hanti i j).2.1] at heq
    linear_combination heq
  -- (J)
  have hJ : ∀ i j k, (ω₁ i j * σ k + ω₂ i j * η k + c * ω₃ i j * f k) +
      (ω₁ j k * σ i + ω₂ j k * η i + c * ω₃ j k * f i) +
      (ω₁ k i * σ j + ω₂ k i * η j + c * ω₃ k i * f j) = 0 := by
    intro i j k
    have hjac := pc_jacobi (A := (⊤ : Subgroup Q).lowerCentralSeries 1) (fun a ha b hb => (S.comm1 ha hb).eq) pc_mem_one
      (x' i) (x' j) (x' k)
    have hpair : ∀ a b, ∃ τ : ZMod p, pc (x' a) (x' b) =
        u' ^ (ω₁ a b).val * v' ^ (ω₂ a b).val * w' ^ (ω₃ a b).val * z ^ τ.val := fun a b =>
      S.exists_eq_mul (by simp only [pc, map_mul, map_inv, map_pow, hπu, hπv, hπw, hx']; exact hω a b)
    obtain ⟨τ₁, h₁⟩ := hpair i j
    obtain ⟨τ₂, h₂⟩ := hpair j k
    obtain ⟨τ₃, h₃⟩ := hpair k i
    rw [h₁, h₂, h₃, GA, GA, GA, mul_central_rearrange (S.pow_z_central _),
      mul_central_rearrange (mul_mem (S.pow_z_central _) (S.pow_z_central _)), ← pow_add w',
      ← pow_add w', pow_val_add S.pz, pow_val_add S.pz] at hjac
    have key : ∀ (A : ℕ) (s : ZMod p), w' ^ A * z ^ s.val = 1 → s = 0 := by
      intro A s h
      have h' := congrArg π h
      rw [map_mul, map_pow, hπw, S.map_z_pow, mul_one, map_one] at h'
      obtain ⟨m, hm⟩ : p ∣ A := hwo ▸ orderOf_dvd_of_pow_eq_one h'
      rw [hm, pow_mul, hw'p, one_pow, one_mul] at h
      exact pow_val_eq_one S.order h
    have hs := key _ _ hjac
    simp only [ZMod.natCast_zmod_val, hψx] at hs
    linear_combination hs
  have hcinv : c⁻¹ * c - 1 = 0 := by rw [inv_mul_cancel₀ hc0, sub_self]
  refine ⟨c⁻¹ * μu, c⁻¹ * μv, fun i => c⁻¹ * η i, fun i => c⁻¹ * σ i, fun i j => ?_,
    fun i j k _ _ => ?_⟩
  · linear_combination c⁻¹ * hE i j -
      (β j * f i + (if p = 3 then 1 else 0) * f j ^ 2 * ω₁ i j) * hcinv
  · linear_combination c⁻¹ * hJ i j k - (ω₃ i j * f k + ω₃ j k * f i + ω₃ k i * f j) * hcinv

end Setup

end Nonterminal

open Nonterminal in
/-- **Theorem 6.12, "⇒"** (Appendix, Steps 2 and 4). Let `p` be an odd prime and `P` a group with
`γ₄(P) = 1`, `|γ₂(P)/γ₃(P)| = p²`, `|γ₃(P)| = p` and `P/γ₂(P)` of exponent `p`. Suppose `P` is
nonterminal in the sense of Lemma 10.1: there are a group `Q`, `π : Q →* P` onto with
`ker π = ⟨z⟩`, `z` central of order `p`, and `γ₄(Q) ≠ 1`. Then
(N1) `|Z(P) ∩ γ₂(P)| = p²`, (N2) `γ₂(P)` is elementary abelian, (N3) `x^p ∈ Z(P)` for all `x`,
and (N4): for every `w` generating `γ₃(P)`, `v ∈ Z(P) ∩ γ₂(P) \ γ₃(P)`, `u ∈ γ₂(P) \ Z(P)` and
`x_1, …, x_d ∈ P`, with `[x_i,x_j] = u^{ω₁(i,j)} v^{ω₂(i,j)} w^{ω₃(i,j)}`,
`x_i^p = v^{α_i} w^{β_i}` and `[u,x_i] = w^{f_i}` (`[a,b] = a⁻¹b⁻¹ab`), the system (E)+(J) has a
solution with `c = 1`. -/
theorem nonterminal_necessary {Q P : Type*} [Group Q] [Group P] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (h4 : (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥)
    (h2 : ((⊤ : Subgroup P).lowerCentralSeries 2).relIndex ((⊤ : Subgroup P).lowerCentralSeries 1) = p ^ 2)
    (h3 : Nat.card ((⊤ : Subgroup P).lowerCentralSeries 2) = p)
    (hel : ∀ x : P, x ^ p ∈ (⊤ : Subgroup P).lowerCentralSeries 1)
    (π : Q →* P) (hπ : Function.Surjective π) (z : Q) (hz : z ∈ center Q) (hzo : orderOf z = p)
    (hker : π.ker = zpowers z) (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 ≠ ⊥) :
    Nat.card (center P ⊓ (⊤ : Subgroup P).lowerCentralSeries 1 : Subgroup P) = p ^ 2 ∧
    ((∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, a ^ p = 1) ∧
      ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
        a * b = b * a) ∧
    (∀ x : P, x ^ p ∈ center P) ∧
    ∀ (d : ℕ) (x : Fin d → P) (u v w : P) (ω₁ ω₂ ω₃ : Fin d → Fin d → ZMod p)
      (α β f : Fin d → ZMod p),
      w ∈ (⊤ : Subgroup P).lowerCentralSeries 2 → w ≠ 1 →
      v ∈ center P → v ∈ (⊤ : Subgroup P).lowerCentralSeries 1 →
      v ∉ (⊤ : Subgroup P).lowerCentralSeries 2 →
      u ∈ (⊤ : Subgroup P).lowerCentralSeries 1 → u ∉ center P →
      (∀ i j, (x i)⁻¹ * (x j)⁻¹ * x i * x j =
        u ^ (ω₁ i j).val * v ^ (ω₂ i j).val * w ^ (ω₃ i j).val) →
      (∀ i, x i ^ p = v ^ (α i).val * w ^ (β i).val) →
      (∀ i, u⁻¹ * (x i)⁻¹ * u * x i = w ^ (f i).val) →
      ∃ μu μv : ZMod p, ∃ η σ : Fin d → ZMod p, SystemEJ ω₁ ω₂ ω₃ α β f 1 μu μv η σ := by
  have S : Setup p π z := ⟨hp2, hπ, hker, hz, hzo, h4, h2, h3, hel, hQ⟩
  obtain ⟨w, hw2, hw1⟩ : ∃ w ∈ (⊤ : Subgroup P).lowerCentralSeries 2, w ≠ 1 := by
    have hne : (⊤ : Subgroup P).lowerCentralSeries 2 ≠ ⊥ := by
      intro h
      have h3' := h3
      rw [h, Subgroup.card_bot] at h3'
      exact (Fact.out : p.Prime).one_lt.ne h3'
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨w, hw, fun h => hw1 (Subtype.ext h)⟩
  obtain ⟨w', hw', hπw⟩ := S.exists_lift hw2
  refine ⟨S.N1 hw2 hw1 hw' hπw, ⟨fun a ha => S.N2_exp hw2 hw1 hw' hπw ha,
    fun a ha b hb => (S.P_comm1 ha hb).eq⟩, fun x => S.N3 hw2 hw1 hw' hπw x, ?_⟩
  intro d x u v w₀ ω₁ ω₂ ω₃ α β f hw₀2 hw₀1 hvc hv1 hv2 hu huc hω hpow hf
  exact S.N4 x hw₀2 hw₀1 hvc hv1 hv2 hu huc hω hpow hf

end GroupDimension
