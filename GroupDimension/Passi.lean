module

public import GroupDimension.TaharaProof.DFour
public import GroupDimension.Gruenberg

@[expose] public section

/-!
# Passi's theorem `D₄(G)² ⊆ γ₄(G)` [Pas68]

`passiDFourSquare : PassiDFourSquare` proves the statement that `Statements.lean` records, and
which was an explicit hypothesis of Proposition 2.1, Remark 2.3 and Lemma 6.9.

**Finite groups of class `≤ 3` with Tahara's data.** By `exists_gen_of_D_four` (`DFour.lean`) an
element `g ∈ D₄` is `gen τ` for a family `τ` satisfying Tahara's conditions (A₂), (A₃), (B). With
`γ₄ = 1` the `v`- and `w`-parts of `gen τ` are trivial, so `g = ∏_{i<j} κ_{ij}^{u_{ij} q_{ij}}`,
`κ_{ij} = [x_i^{d(i)}, x_j]`, `q_{ij} = d(j)/d(i)` (`gen_eq_genA`). In the abelian group `γ₃`
(written additively through `cl`):
* `[x^n, y] = [x, y]^n [[x, y], x]^{C(n,2)}` gives `q_{ij} κ_{ij} + κ_{ji} = q_{ij} C(d(i),2) t_i -
  C(d(j),2) t_j` with `t_i, t_j` killed by `d(i)`; by (A₂), (A₃), `u_{ij} q_{ij} κ_{ij} =
  -u_{ij} κ_{ji}` (`swap`);
* `κ_{hi} = ∑_k b_{hk} [x_{2k}, x_i]`, and `[x_{2k}, x_i]` is killed by `d(i)` and by `e(k)`; so
  (B), multiplied by `[x_{2k}, x_i]` and summed, says `∑_{i<j} u_{ij} κ_{ji} =
  ∑_{i<j} u_{ij} q_{ij} κ_{ij}`.
Together, `g = -g` in `γ₃`, so `g² = 1` (`sq_eq_one_of_D_four`).
-/

namespace GroupDimension

namespace Passi

open Subgroup Tahara ExpThree TaharaProof

variable {G : Type*} [Group G]

/-! ## Commutator calculus in class `≤ 3` -/

section ClassThree

variable (h3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥)
include h3

theorem central3 {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (g : G) :
    g * z = z * g := by
  have h : tc z g ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    tc_mem (i := 2) (j := 0) (by norm_num) hz (mem_lcs_zero g)
  rw [h3, mem_bot] at h
  calc g * z = z * g * (z⁻¹ * g⁻¹ * z * g)⁻¹ := by group
    _ = z * g := by rw [show z⁻¹ * g⁻¹ * z * g = tc z g from rfl, h, inv_one, mul_one]

theorem tc_eq_one_of_mem3 {z : G} (hz : z ∈ (⊤ : Subgroup G).lowerCentralSeries 2) (x : G) :
    tc z x = 1 :=
  tc_of_central (central3 h3 hz) x

theorem tc_eq_one_of_mem2 {a b : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries 1) : tc a b = 1 := by
  have h := tc_mem (i := 1) (j := 1) (n := 3) (by norm_num) ha hb
  rwa [h3, mem_bot] at h

omit h3 in
theorem tc_mul_left' (a b x : G) : tc (a * b) x = b⁻¹ * tc a x * b * tc b x := by
  simp only [tc]; group

theorem tc_mul_left2 {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (b x : G) :
    tc (a * b) x = tc a x * tc b x := by
  have hc := central3 h3 (tc_mem (i := 1) (j := 0) (by norm_num) ha (mem_lcs_zero x))
  rw [tc_mul_left', mul_assoc b⁻¹, ← hc b, inv_mul_cancel_left]

theorem tc_mul_right2 {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x y : G) :
    tc a (x * y) = tc a x * tc a y := by
  have hc := central3 h3 (tc_mem (i := 1) (j := 0) (by norm_num) ha (mem_lcs_zero x))
  rw [tc_mul_right, mul_assoc y⁻¹, ← hc y, inv_mul_cancel_left, ← hc]

/-- `a ↦ [a, x]` on `γ₂`. -/
def tcHom (x : G) : ↥((⊤ : Subgroup G).lowerCentralSeries 1) →* G where
  toFun a := tc a x
  map_one' := by simp [tc]
  map_mul' a b := tc_mul_left2 h3 a.2 b x

theorem tc_zpow_left {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) (n : ℤ) :
    tc (a ^ n) x = tc a x ^ n :=
  map_zpow (tcHom h3 x) ⟨a, ha⟩ n

theorem tc_pow_left {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) (n : ℕ) :
    tc (a ^ n) x = tc a x ^ n :=
  map_pow (tcHom h3 x) ⟨a, ha⟩ n

theorem tc_inv_left {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) :
    tc a⁻¹ x = (tc a x)⁻¹ := by
  simpa using tc_zpow_left h3 ha x (-1)

theorem tc_pow_right {a : G} (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1) (x : G) (n : ℕ) :
    tc a (x ^ n) = tc a x ^ n := by
  induction n with
  | zero => simp [tc]
  | succ n ih => rw [pow_succ, tc_mul_right2 h3 ha, ih, pow_succ]

theorem tc_oprod_left {n : ℕ} {y : Fin n → G}
    (hy : ∀ i, y i ∈ (⊤ : Subgroup G).lowerCentralSeries 1)
    (a : Fin n → ℤ) (x : G) : tc (oprod y a) x = oprod (fun i => tc (y i) x) a := by
  have hl : ∀ l : List G, (∀ m ∈ l, m ∈ (⊤ : Subgroup G).lowerCentralSeries 1) →
      tc l.prod x = (l.map fun m => tc m x).prod := by
    intro l
    induction l with
    | nil => intro _; simp [tc]
    | cons m l ih =>
      intro hl
      rw [List.prod_cons, tc_mul_left2 h3 (hl m List.mem_cons_self),
        ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.prod_cons]
  unfold oprod
  rw [hl _ fun m hm => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm; exact zpow_mem (hy i) _,
    List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  exact tc_zpow_left h3 (hy i) x (a i)

/-- `[x^n, y] = [x, y]^n [[x, y], x]^{C(n,2)}` in class `≤ 3`. -/
theorem tc_pow_left_gen (x y : G) (n : ℕ) :
    tc (x ^ n) y = tc x y ^ n * tc (tc x y) x ^ n.choose 2 := by
  have ha : tc x y ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (by norm_num) (mem_lcs_zero x) (mem_lcs_zero y)
  have ht : tc (tc x y) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (by norm_num) ha (mem_lcs_zero x)
  set A := tc x y with hA
  set t := tc A x with htdef
  have hz : ∀ g : G, Commute g t := fun g => central3 h3 ht g
  have hcomm : ∀ (k : ℕ) (g w : G), t ^ k * (g * w) = g * (t ^ k * w) := fun k g w => by
    rw [← mul_assoc, ← mul_assoc, ← ((hz g).pow_right k).eq]
  have hconj : x⁻¹ * A * x = A * t := by rw [htdef]; simp only [tc]; group
  have key : ∀ m : ℕ, x⁻¹ * A ^ m * x = A ^ m * t ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc x⁻¹ * A ^ (m + 1) * x = (x⁻¹ * A ^ m * x) * (x⁻¹ * A * x) := by group
        _ = A ^ m * t ^ m * (A * t) := by rw [ih, hconj]
        _ = A ^ (m + 1) * t ^ (m + 1) := by
          rw [mul_assoc, hcomm, ← mul_assoc, ← pow_succ, ← pow_succ]
  induction n with
  | zero => simp [tc]
  | succ n ih =>
    have hC : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [pow_succ, tc_mul_left', ih, hC, pow_add t]
    calc x⁻¹ * (A ^ n * t ^ n.choose 2) * x * A
        = (x⁻¹ * A ^ n * x) * (x⁻¹ * t ^ n.choose 2 * x) * A := by group
      _ = A ^ n * t ^ n * t ^ n.choose 2 * A := by
          rw [key, mul_assoc x⁻¹ (t ^ _) x, ← ((hz x).pow_right _).eq, inv_mul_cancel_left]
      _ = A ^ (n + 1) * (t ^ n * t ^ n.choose 2) := by
          rw [mul_assoc, mul_assoc, ← ((hz A).pow_right _).eq, hcomm, ← mul_assoc, ← pow_succ]

end ClassThree

/-! ## `gen τ` has order `≤ 2` -/

theorem cl_ofFn_prod {k n : ℕ} (f : Fin n → G)
    (hf : ∀ i, f i ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    cl G k (List.ofFn f).prod = ∑ i, cl G k (f i) := by
  have : ∀ l : List G, (∀ x ∈ l, x ∈ (⊤ : Subgroup G).lowerCentralSeries k) →
      cl G k l.prod = (l.map (cl G k)).sum := by
    intro l
    induction l with
    | nil => intro _; simp [cl_one]
    | cons x l ih =>
      intro hl
      rw [List.prod_cons, cl_mul (hl x List.mem_cons_self)
        (list_prod_mem fun z hz => hl z (List.mem_cons_of_mem _ hz)),
        ih fun z hz => hl z (List.mem_cons_of_mem _ hz), List.map_cons, List.sum_cons]
  rw [this _ fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hf i, List.map_ofFn,
    List.sum_ofFn]
  rfl

section Gen

variable (h3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) {T : Data G} (hT : T.Valid)
include h3 hT

/-- `κ_{hi} = [x_h^{d(h)}, x_i]`. -/
def κ (T : Data G) (h i : Fin T.s) : G := tc (T.x₁ h ^ T.d h) (T.x₁ i)

omit h3 in
theorem pow_d_mem (i : Fin T.s) : T.x₁ i ^ T.d i ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  have hm : oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i) ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    mul_mem (oprod_mem hT.basis₂.mem _) (oprod_mem (fun l => lcs_mem_of_le (by norm_num)
      (hT.basis₃.mem l)) _)
  have := mul_mem hm (lcs_mem_of_le (by norm_num) (hT.hb i))
  rwa [mul_inv_cancel_left] at this

theorem pow_d_eq (i : Fin T.s) : T.x₁ i ^ T.d i = oprod T.x₂ (T.b i) * oprod T.x₃ (T.c i) := by
  have := hT.hb i
  rw [h3, mem_bot, inv_mul_eq_one] at this
  exact this.symm

omit h3 in
theorem κ_mem (h i : Fin T.s) : κ T h i ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  tc_mem (i := 1) (j := 0) (by norm_num) (pow_d_mem hT h) (mem_lcs_zero _)

omit h3 hT in
theorem tc2_mem (T : Data G) (hT : T.Valid) (k : Fin T.t) (x : G) :
    tc (T.x₂ k) x ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  tc_mem (i := 1) (j := 0) (by norm_num) (hT.basis₂.mem k) (mem_lcs_zero x)

theorem cl_κ (h i : Fin T.s) :
    cl G 2 (κ T h i) = ∑ k, T.b h k • cl G 2 (tc (T.x₂ k) (T.x₁ i)) := by
  rw [κ, pow_d_eq h3 hT, tc_mul_left2 h3 (oprod_mem hT.basis₂.mem _),
    tc_eq_one_of_mem3 h3 (oprod_mem hT.basis₃.mem _), mul_one, tc_oprod_left h3 hT.basis₂.mem,
    cl_oprod fun k => tc2_mem T hT k _]

theorem e_smul_cl (k : Fin T.t) (x : G) : (T.e k : ℤ) • cl G 2 (tc (T.x₂ k) x) = 0 := by
  have he : T.x₂ k ^ T.e k ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
    have := hT.hdd k
    rw [h3, mem_bot, inv_mul_eq_one] at this
    rw [← this]; exact oprod_mem hT.basis₃.mem _
  rw [← cl_zpow (tc2_mem T hT k x), ← tc_zpow_left h3 (hT.basis₂.mem k), zpow_natCast,
    tc_eq_one_of_mem3 h3 he, cl_one]

theorem d_smul_cl (k : Fin T.t) (i : Fin T.s) :
    (T.d i : ℤ) • cl G 2 (tc (T.x₂ k) (T.x₁ i)) = 0 := by
  rw [← cl_zpow (tc2_mem T hT k _), zpow_natCast, ← tc_pow_right h3 (hT.basis₂.mem k),
    tc_eq_one_of_mem2 h3 (hT.basis₂.mem k) (pow_d_mem hT i), cl_one]

/-- `u_{ij} q_{ij} κ_{ij} = -u_{ij} κ_{ji}` under (A₂), (A₃). -/
theorem swap {τ : Coeffs T.s T.t} (hτ : T.AdmissibleAB τ) {i j : Fin T.s} (hij : i < j) :
    (τ.u i j * T.q i j) • cl G 2 (κ T i j) = -(τ.u i j • cl G 2 (κ T j i)) := by
  set a := tc (T.x₁ i) (T.x₁ j) with ha_def
  have ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
    tc_mem (i := 0) (j := 0) (by norm_num) (mem_lcs_zero _) (mem_lcs_zero _)
  set ti := tc a (T.x₁ i)
  set tj := tc a (T.x₁ j)
  have hti : ti ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (by norm_num) ha (mem_lcs_zero _)
  have htj : tj ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
    tc_mem (i := 1) (j := 0) (by norm_num) ha (mem_lcs_zero _)
  have hdvd : T.d i ∣ T.d j := hT.basis₁.dvd i j hij.le
  have hq : T.d i * (T.d j / T.d i) = T.d j := Nat.mul_div_cancel' hdvd
  have hκij : κ T i j = a ^ T.d i * ti ^ (T.d i).choose 2 := tc_pow_left_gen h3 _ _ _
  have hκji : κ T j i = (a ^ T.d j)⁻¹ * (tj ^ (T.d j).choose 2)⁻¹ := by
    rw [κ, tc_pow_left_gen h3, ← tc_inv, tc_inv_left h3 ha, inv_pow, inv_pow]
  -- `κ_{ij}^q κ_{ji} = t_i^{q C(d(i),2)} t_j^{-C(d(j),2)}`
  have hprod : κ T i j ^ (T.d j / T.d i) * κ T j i =
      ti ^ ((T.d i).choose 2 * (T.d j / T.d i)) * (tj ^ (T.d j).choose 2)⁻¹ := by
    have hc : Commute (a ^ T.d i) (ti ^ (T.d i).choose 2) :=
      ((show Commute (a ^ T.d i) ti from central3 h3 hti _).pow_right _)
    have hc' : Commute (a ^ T.d j) (ti ^ ((T.d i).choose 2 * (T.d j / T.d i))) :=
      ((show Commute (a ^ T.d j) ti from central3 h3 hti _).pow_right _)
    rw [hκij, hκji, hc.mul_pow, ← pow_mul, ← pow_mul, hq, ← mul_assoc,
      hc'.mul_inv_cancel]
  have hcl : (T.q i j) • cl G 2 (κ T i j) + cl G 2 (κ T j i) =
      ((((T.d i).choose 2 * (T.d j / T.d i) : ℕ) : ℤ)) • cl G 2 ti -
        (((T.d j).choose 2 : ℕ) : ℤ) • cl G 2 tj := by
    have e := congrArg (cl G 2) hprod
    rw [cl_mul (pow_mem (κ_mem hT i j) _) (κ_mem hT j i), cl_mul (pow_mem hti _)
      (inv_mem (pow_mem htj _)), cl_inv (pow_mem htj _), ← zpow_natCast, ← zpow_natCast,
      ← zpow_natCast, cl_zpow (κ_mem hT i j), cl_zpow hti, cl_zpow htj] at e
    rw [Data.q, e, sub_eq_add_neg]
  have hdi : (T.d i : ℤ) • cl G 2 ti = 0 := by
    rw [← cl_zpow hti, zpow_natCast, ← tc_pow_right h3 ha,
      tc_eq_one_of_mem2 h3 ha (pow_d_mem hT i), cl_one]
  have hdj : (T.d i : ℤ) • cl G 2 tj = 0 := by
    have hai : a ^ T.d i ∈ (⊤ : Subgroup G).lowerCentralSeries 2 := by
      have : a ^ T.d i = κ T i j * (ti ^ (T.d i).choose 2)⁻¹ := by
        rw [hκij, mul_inv_cancel_right]
      rw [this]; exact mul_mem (κ_mem hT i j) (inv_mem (pow_mem hti _))
    rw [← cl_zpow htj, zpow_natCast, ← tc_pow_left h3 ha, tc_eq_one_of_mem3 h3 hai, cl_one]
  -- (A₂), (A₃): the coefficients are multiples of `d(i)`
  have hA2 := hτ.A₂ i j hij
  have hA3 := hτ.A₃ i j hij
  simp only [Data.q, Data.ch] at hA2 hA3
  have hdj' : (T.d j : ℤ) = T.d i * ((T.d j / T.d i : ℕ) : ℤ) := by exact_mod_cast hq.symm
  rw [hdj'] at hA2 hA3
  have e1 : (((T.d i).choose 2 * (T.d j / T.d i) : ℕ) : ℤ) * τ.u i j =
      (T.d i : ℤ) * (-τ.w i i j - τ.w'' i i j * ((T.d j / T.d i : ℕ) : ℤ)) := by
    rw [Nat.cast_mul]; linear_combination hA2
  have e2 : (((T.d j).choose 2 : ℕ) : ℤ) * τ.u i j =
      (T.d i : ℤ) * (τ.w i j j + τ.w' i j j * ((T.d j / T.d i : ℕ) : ℤ)) := by
    linear_combination -hA3
  have z1 : τ.u i j • ((((T.d i).choose 2 * (T.d j / T.d i) : ℕ) : ℤ) • cl G 2 ti) = 0 := by
    rw [smul_smul, mul_comm (τ.u i j), e1, mul_comm (T.d i : ℤ), ← smul_smul, hdi, smul_zero]
  have z2 : τ.u i j • ((((T.d j).choose 2 : ℕ) : ℤ) • cl G 2 tj) = 0 := by
    rw [smul_smul, mul_comm (τ.u i j), e2, mul_comm (T.d i : ℤ), ← smul_smul, hdj, smul_zero]
  have key := congrArg (τ.u i j • ·) hcl
  simp only [smul_add, smul_sub, z1, z2, sub_zero] at key
  rw [mul_smul]
  exact eq_neg_of_add_eq_zero_left key

omit h3 in
theorem genA_mem' (τ : Coeffs T.s T.t) : T.genA τ ∈ (⊤ : Subgroup G).lowerCentralSeries 2 :=
  list_prod_mem fun z hz => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact list_prod_mem fun w hw => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      split_ifs
      · exact zpow_mem (κ_mem hT i j) _
      · exact one_mem _

omit h3 in
theorem cl_genA (τ : Coeffs T.s T.t) :
    cl G 2 (T.genA τ) = ∑ i, ∑ j, if i < j then (τ.u i j * T.q i j) • cl G 2 (κ T i j) else 0 := by
  have hite : ∀ i j, (if i < j then tc (T.x₁ i ^ T.d i) (T.x₁ j) ^ (τ.u i j * T.q i j) else 1) ∈
      (⊤ : Subgroup G).lowerCentralSeries 2 := fun i j => by
    split_ifs
    · exact zpow_mem (κ_mem hT i j) _
    · exact one_mem _
  rw [Data.genA, cl_ofFn_prod _ fun i => list_prod_mem fun z hz => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz; exact hite i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cl_ofFn_prod _ (hite i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact cl_zpow (κ_mem hT i j) _
  · exact cl_one 2

theorem gen_eq_genA (τ : Coeffs T.s T.t) : T.gen τ = T.genA τ := by
  have hB : T.genB τ = 1 := by
    have : ∀ l k, tc (T.x₂ l) (T.x₂ k) = 1 := fun l k =>
      tc_eq_one_of_mem2 h3 (hT.basis₂.mem l) (hT.basis₂.mem k)
    simp [Data.genB, this]
  have hC : T.genC τ = 1 := by
    have : ∀ i j k, tc (tc (T.x₁ i ^ T.d i) (T.x₁ j)) (T.x₁ k) = 1 := fun i j k =>
      tc_eq_one_of_mem3 h3 (κ_mem hT i j) _
    simp [Data.genC, this]
  rw [Data.gen, hB, hC, mul_one, mul_one]

/-- **`gen τ² = 1`** in class `≤ 3`, under (A₂), (A₃), (B). -/
theorem genA_sq {τ : Coeffs T.s T.t} (hτ : T.AdmissibleAB τ) : T.genA τ ^ 2 = 1 := by
  set K : Fin T.s → Fin T.s → Additive (Layer G 2) := fun h i => cl G 2 (κ T h i) with hK
  set Tk : Fin T.t → Fin T.s → Additive (Layer G 2) := fun k i => cl G 2 (tc (T.x₂ k) (T.x₁ i))
  have hsum : ∀ (c : Fin T.s → ℤ) (i : Fin T.s),
      ∑ k, (∑ h, c h * T.b h k) • Tk k i = ∑ h, c h • K h i := by
    intro c i
    simp only [Tk, hK, cl_κ h3 hT, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  -- (B), multiplied by `[x_{2k}, x_i]` and summed over `k`
  have hrow : ∀ i, ∑ h, (if i < h then τ.u i h else 0) • K h i =
      ∑ h, (if h < i then τ.u h i * T.q h i else 0) • K h i := by
    intro i
    have e : ∑ k, ((∑ h, (if i < h then τ.u i h else 0) * T.b h k) -
        (∑ h, (if h < i then τ.u h i * T.q h i else 0) * T.b h k) +
        τ.v i k * T.d i + τ.v' i k * T.e k) • Tk k i = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hb := hτ.B i k
      simp only [ite_mul, zero_mul] at hb ⊢
      rw [hb, zero_smul]
    simp only [add_smul, sub_smul, Finset.sum_sub_distrib, hsum,
      mul_smul, Tk, d_smul_cl h3 hT, e_smul_cl h3 hT,
      smul_zero, add_zero] at e
    exact sub_eq_zero.mp e
  have hX := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hrow i
  -- the swap relation
  have hY : (∑ i, ∑ h, (if h < i then τ.u h i * T.q h i else 0) • K h i) =
      -∑ i, ∑ h, (if i < h then τ.u i h else 0) • K h i := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hhi
    · exact swap h3 hT hτ hhi
    · simp
  have hg : cl G 2 (T.genA τ) = ∑ i, ∑ h, (if h < i then τ.u h i * T.q h i else 0) • K h i := by
    rw [cl_genA hT, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> first | rfl | simp
  have h2 : (2 : ℤ) • cl G 2 (T.genA τ) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hg]
    rw [hY, hX, ← hg, neg_add_cancel]
  have hmem := genA_mem' hT τ
  rw [← cl_zpow hmem, cl_eq_zero_iff (zpow_mem hmem _), h3, mem_bot] at h2
  exact_mod_cast h2

end Gen

/-! ## Tahara's data for a finite `p`-group -/

section Layers

open TaharaProof in
theorem cl_oprod_eq_zero_iff {k n : ℕ} {y : Fin n → G}
    (hy : ∀ i, y i ∈ (⊤ : Subgroup G).lowerCentralSeries k) (a : Fin n → ℤ) :
    oprod y a ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) ↔ ∑ i, a i • cl G k (y i) = 0 := by
  rw [← cl_oprod hy, cl_eq_zero_iff (oprod_mem hy a)]

theorem cl_span_iff {k n : ℕ} {y : Fin n → G}
    (hy : ∀ i, y i ∈ (⊤ : Subgroup G).lowerCentralSeries k) (a : Fin n → ℤ) {g : G}
    (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    (oprod y a)⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) ↔
      cl G k g = ∑ i, a i • cl G k (y i) := by
  have hm := oprod_mem hy a
  rw [← cl_eq_zero_iff (mul_mem (inv_mem hm) hg), cl_mul (inv_mem hm) hg, cl_inv hm, cl_oprod hy,
    neg_add_eq_zero, eq_comm]

/-- A permutation of a normal-form basis of a layer is one. -/
theorem _root_.GroupDimension.TaharaProof.LayerNF.comp_equiv {k n : ℕ} {y : Fin n → G}
    {o : Fin n → ℕ} (h : LayerNF k y o)
    (σ : Equiv.Perm (Fin n)) : LayerNF k (y ∘ σ) (o ∘ σ) := by
  have hy' : ∀ i, (y ∘ σ) i ∈ (⊤ : Subgroup G).lowerCentralSeries k := fun i => h.mem (σ i)
  refine ⟨hy', fun i => h.pos (σ i), fun a => ?_, fun g hg => ?_⟩
  · rw [cl_oprod_eq_zero_iff hy']
    have e := (cl_oprod_eq_zero_iff h.mem (a ∘ σ.symm)).symm.trans (h.indep (a ∘ σ.symm))
    have hs : ∑ i, a i • cl G k ((y ∘ σ) i) = ∑ i, (a ∘ σ.symm) i • cl G k (y i) := by
      rw [← Equiv.sum_comp σ (fun i => (a ∘ σ.symm) i • cl G k (y i))]; simp
    rw [hs, e]
    exact ⟨fun h' i => by simpa using h' (σ i), fun h' i => by simpa using h' (σ.symm i)⟩
  · obtain ⟨a, ha⟩ := h.span g hg
    refine ⟨a ∘ σ, ?_⟩
    rw [cl_span_iff hy' _ hg]
    rw [cl_span_iff h.mem _ hg] at ha
    rw [ha, ← Equiv.sum_comp σ]
    rfl

variable {p : ℕ} [hp : Fact p.Prime]

/-- In a finite `p`-group, the orders of a normal-form basis of a layer are powers of `p`. -/
theorem _root_.GroupDimension.TaharaProof.LayerNF.exists_pow [Finite G] (hG : IsPGroup p G)
    {k n : ℕ} {y : Fin n → G} {o : Fin n → ℕ} (h : LayerNF k y o) (i : Fin n) :
    ∃ m, o i = p ^ m := by
  have : Finite (Additive (Layer G k)) := by unfold Layer; infer_instance
  have hL : IsPGroup p (Layer G k) := (hG.to_subgroup _).to_quotient _
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hL
  have hcard : Nat.card (Additive (Layer G k)) = p ^ N := by
    rw [← hN]; rfl
  have hdiv : (o i : ℤ) ∣ (Nat.card (Additive (Layer G k)) : ℤ) := by
    have := (h.indep (Pi.single i (Nat.card (Additive (Layer G k)) : ℤ))).mp (by
      rw [cl_oprod_eq_zero_iff h.mem]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp) i
    simpa using this
  rw [hcard] at hdiv
  exact (Nat.dvd_prime_pow hp.out).mp (by exact_mod_cast hdiv) |>.imp fun m hm => hm.2

/-- **A uniqueness basis of each layer of a finite `p`-group** ([Tah81, p. 143]). -/
theorem exists_isLayerBasis [Finite G] (hG : IsPGroup p G) (k : ℕ) :
    ∃ (n : ℕ) (x : Fin n → G) (o : Fin n → ℕ), IsLayerBasis k x o := by
  obtain ⟨n, y, o, hy, ho⟩ := exists_layerNF (G := G) k
  set σ := Tuple.sort o
  have hy' := hy.comp_equiv σ
  have hmono : Monotone (o ∘ σ) := Tuple.monotone_sort o
  refine ⟨n, y ∘ σ, o ∘ σ, ⟨hy'.mem, fun i => ho (σ i), fun i j hij => ?_, hy'.indep, hy'.span⟩⟩
  obtain ⟨a, ha⟩ := hy'.exists_pow hG i
  obtain ⟨b, hb⟩ := hy'.exists_pow hG j
  have hle := hmono hij
  rw [ha, hb] at hle ⊢
  exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle)

/-- Normal forms with exponents `0 ≤ a_i < o_i`. -/
theorem _root_.GroupDimension.Tahara.IsLayerBasis.exists_nf {k n : ℕ} {x : Fin n → G}
    {o : Fin n → ℕ} (h : IsLayerBasis k x o)
    {g : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries k) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i < o i) ∧
      (oprod x a)⁻¹ * g ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  obtain ⟨a, ha⟩ := h.span g hg
  have hpos : ∀ i, (0 : ℤ) < o i := fun i => by have := h.one_lt i; omega
  have hord : ∀ i, (o i : ℤ) • cl G k (x i) = 0 := by
    intro i
    have := (cl_oprod_eq_zero_iff h.mem (Pi.single i (o i : ℤ))).mp ((h.indep _).mpr fun j => by
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj])
    rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp),
      Pi.single_eq_same] at this
  refine ⟨fun i => a i % o i,
    fun i => ⟨Int.emod_nonneg _ (hpos i).ne', Int.emod_lt_of_pos _ (hpos i)⟩,
    ?_⟩
  rw [cl_span_iff h.mem _ hg] at ha ⊢
  rw [ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.emod_def, sub_smul, mul_comm, mul_smul, hord, smul_zero, sub_zero]

theorem _root_.GroupDimension.Tahara.IsLayerBasis.pow_mem {k n : ℕ} {x : Fin n → G}
    {o : Fin n → ℕ} (h : IsLayerBasis k x o)
    (i : Fin n) : x i ^ o i ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := by
  have := (h.indep (Pi.single i (o i : ℤ))).mpr fun j => by
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [cl_oprod_eq_zero_iff h.mem,
    Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp),
    Pi.single_eq_same, ← cl_zpow (h.mem i), zpow_natCast,
    cl_eq_zero_iff (_root_.pow_mem (h.mem i) _)] at this
  exact this

/-- **Tahara's data exist** for a finite `p`-group of class `≤ 3`. -/
theorem exists_valid_data [Finite G] (hG : IsPGroup p G) : ∃ T : Data G, T.Valid := by
  classical
  obtain ⟨s, x₁, d, B1⟩ := exists_isLayerBasis hG 0
  obtain ⟨t, x₂, e, B2⟩ := exists_isLayerBasis hG 1
  obtain ⟨u, x₃, f, B3⟩ := exists_isLayerBasis hG 2
  have hyd : ∀ i, x₁ i ^ d i ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := B1.pow_mem
  -- `x_{1i}^{d(i)}`
  have nb : ∀ i, ∃ b : Fin t → ℤ, (∀ k, 0 ≤ b k ∧ b k < e k) ∧ ∃ c : Fin u → ℤ,
      (∀ l, 0 ≤ c l ∧ c l < f l) ∧
      (oprod x₂ b * oprod x₃ c)⁻¹ * x₁ i ^ d i ∈ (⊤ : Subgroup G).lowerCentralSeries 3 := by
    intro i
    obtain ⟨b, hb, hb'⟩ := B2.exists_nf (hyd i)
    obtain ⟨c, hc, hc'⟩ := B3.exists_nf hb'
    exact ⟨b, hb, c, hc, by rw [mul_inv_rev, mul_assoc]; exact hc'⟩
  choose b hb c hc hbc using nb
  have nd : ∀ k, ∃ dd : Fin u → ℤ, (∀ l, 0 ≤ dd l ∧ dd l < f l) ∧
      (oprod x₃ dd)⁻¹ * x₂ k ^ e k ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun k => B3.exists_nf (B2.pow_mem k)
  choose dd hdd hdd' using nd
  have na : ∀ g h, ∃ α : Fin u → ℤ, (∀ l, 0 ≤ α l ∧ α l < f l) ∧
      (oprod x₃ α)⁻¹ * tc (x₁ g ^ d g) (x₁ h) ∈ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    fun g h => B3.exists_nf (tc_mem (i := 1) (j := 0) (by norm_num) (hyd g) (mem_lcs_zero _))
  choose α hα hα' using na
  exact ⟨⟨s, t, u, x₁, d, x₂, e, x₃, f, b, c, dd, α⟩,
    ⟨B1, B2, B3, hb, hc, hdd, fun g h l _ => hα g h l, hbc, hdd', fun g h _ => hα' g h⟩⟩

/-- **Passi's theorem for finite `p`-groups of class `≤ 3`**: `D₄ ⊆ Ω₁`, i.e. `g ∈ D₄ ⇒ g² = 1`. -/
theorem sq_eq_one_of_pGroup [Finite G] (hG : IsPGroup p G)
    (h3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) {g : G} (hg : g ∈ D 4 G) : g ^ 2 = 1 := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨T, hT⟩ := exists_valid_data hG
  obtain ⟨τ, hτ, rfl⟩ := exists_gen_of_D_four hT h3 hg
  rw [gen_eq_genA h3 hT]
  exact genA_sq h3 hT hτ

end Layers

/-! ## Finite and all groups -/

/-- In a finite nilpotent group an element `x ≠ 1` survives in the projection to some Sylow
subgroup. -/
theorem exists_sylow_proj [Finite G] (hG : Group.IsNilpotent G) {x : G} (hx : x ≠ 1) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G) (π : G →* (P : Subgroup G)), π x ≠ 1 := by
  have hn := ((Group.isNilpotent_of_finite_tfae (G := G)).out 1 4).mp hG
  let e := Sylow.directProductOfNormal (G := G) (fun {p} _ P => hn p inferInstance P)
  have he : e.symm x ≠ 1 := fun h => hx (by simpa using congrArg e h)
  obtain ⟨⟨p, hpm⟩, hne⟩ : ∃ q, e.symm x q ≠ 1 := by
    by_contra hc; push Not at hc; exact he (funext hc)
  obtain ⟨P, hP⟩ : ∃ P, e.symm x ⟨p, hpm⟩ P ≠ 1 := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpm⟩
  exact ⟨p, inferInstance, P,
    { toFun := fun g => e.symm g ⟨p, hpm⟩ P
      map_one' := by simp
      map_mul' := fun a b => by simp }, hP⟩

/-- **Passi's theorem for finite groups of class `≤ 3`**: `g ∈ D₄ ⇒ g² = 1`. -/
theorem sq_eq_one_of_finite [Finite G] (h3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) {g : G}
    (hg : g ∈ D 4 G) : g ^ 2 = 1 := by
  by_contra hg2
  have hnil : Group.IsNilpotent G := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3, h3⟩
  obtain ⟨p, _, P, π, hπ⟩ := exists_sylow_proj hnil hg2
  have hP3 : (⊤ : Subgroup (P : Subgroup G)).lowerCentralSeries 3 = ⊥ :=
    lowerCentralSeries_eq_bot_of_injective _ (P : Subgroup G).subtype_injective h3
  exact hπ (by rw [map_pow]; exact sq_eq_one_of_pGroup P.isPGroup' hP3 (map_mem_D π hg))

/-- `g ∈ D₄ ⇒ g² = 1` for every group of class `≤ 3`. -/
theorem sq_eq_one_of_class_three {H : Type*} [Group H]
    (h3 : (⊤ : Subgroup H).lowerCentralSeries 3 = ⊥) {x : H} (hx : x ∈ D 4 H) : x ^ 2 = 1 := by
  by_contra hx2
  obtain ⟨s, hs, hD⟩ := exists_closure_finset_mem_D hx
  set K := closure (s : Set H)
  have : Group.FG K := (Group.fg_iff_subgroup_fg _).mpr ((Subgroup.fg_iff _).mpr
    ⟨_, rfl, s.finite_toSet⟩)
  have hK3 : (⊤ : Subgroup K).lowerCentralSeries 3 = ⊥ :=
    lowerCentralSeries_eq_bot_of_injective _ K.subtype_injective h3
  have hnil : Group.IsNilpotent K := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3, hK3⟩
  have := Gruenberg.residuallyFinite hnil
  have hne : (⟨x, hs⟩ : K) ^ 2 ≠ 1 := fun h => hx2 (by simpa using congrArg Subtype.val h)
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem _ hne
  have : N.toSubgroup.Normal := N.isNormal'
  have : N.toSubgroup.FiniteIndex := N.isFiniteIndex'
  have : Finite (K ⧸ N.toSubgroup) := Subgroup.finite_quotient_of_finiteIndex
  have hQ3 : (⊤ : Subgroup (K ⧸ N.toSubgroup)).lowerCentralSeries 3 = ⊥ :=
    Gruenberg.lowerCentralSeries_eq_bot_of_surjective _ (QuotientGroup.mk'_surjective _) hK3
  have h := sq_eq_one_of_finite hQ3 (map_mem_D (QuotientGroup.mk' N.toSubgroup) hD)
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact hN h

end Passi

open Passi in
/-- **Passi's theorem** [Pas68]: `D₄(G)² ⊆ γ₄(G)` for every group, the statement
`PassiDFourSquare` of `Statements.lean`. -/
theorem passiDFourSquare : PassiDFourSquare := by
  intro G _ g hg
  have h := sq_eq_one_of_class_three (lowerCentralSeries_quotient_eq_bot 3)
    (map_mem_D (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries 3)) hg)
  rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

end GroupDimension
