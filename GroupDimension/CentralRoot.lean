module

public import GroupDimension.DTwo

@[expose] public section

/-!
# Adjoining a central root (Lemma 5.9 of the D5 paper)

Let `K` be a group, `H ≤ K`, and `r ∈ K` central with `K = H⟨r⟩`. Suppose that every power of
`r` lying in `H` is the same power of a fixed `g ∈ H`: `r^d ∈ H → r^d = g^d`. (If `|K : H| = m`
and `r^m = g^m`, this holds: `r^d ∈ H` iff `m ∣ d`; see `of_index`.) The element `g` need not be
central. Then

  `ℤ[H] ∩ Δ(K)^n = Δ(H)^n` for all `n`, and `D_n(K) = D_n(H)` for `n ≥ 2`.

The proof is the one in the paper. Write `k = h r^l` with `h ∈ H`; the map `h r^l ↦ h g^l` is
well defined (`retr`), and its linear extension `q : ℤ[K] → ℤ[H]` satisfies
`q(h r^l y) = h q(y) g^l` and `q(x) = x` on `ℤ[H]`. `Δ(K)^n` lies in the left ideal spanned by
the `x (r - 1)^i` with `x ∈ Δ(H)^(n-i)`, and `q(x (r - 1)^i) = x (g - 1)^i ∈ Δ(H)^n`.

MATH-205; the paper's statement is `D_n_eq_of_index`.
-/

namespace GroupDimension

open MonoidAlgebra

/-- The data of Lemma 5.9: `K = H⟨r⟩` with `r` central, and `r^d = g^d` whenever `r^d ∈ H`. -/
structure CentralRoot (K : Type*) [Group K] where
  H : Subgroup K
  r : K
  g : H
  central : ∀ x : K, r * x = x * r
  gen : ∀ k : K, ∃ l : ℤ, k * r ^ (-l) ∈ H
  pow : ∀ d : ℤ, r ^ d ∈ H → r ^ d = (g : K) ^ d

theorem center_comm {R : Type*} [Ring R] {u : R} (hu : u ∈ Subring.center R) (y : R) :
    y * u = u * y :=
  Subring.mem_center_iff.mp hu y

/-- `⁅a c, b d⁆ = ⁅a, b⁆` for central `c`, `d`. -/
theorem comm_central {G : Type*} [Group G] (a b c d : G) (hc : ∀ y, c * y = y * c)
    (hd : ∀ y, d * y = y * d) :
    a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have conj : ∀ (z : G), (∀ y, z * y = y * z) → ∀ x, z * x * z⁻¹ = x := by
    intro z hz x; rw [hz, mul_inv_cancel_right]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * (b * d) * c⁻¹) * a⁻¹ * (b * d)⁻¹ := by group
    _ = a * (b * d) * a⁻¹ * (b * d)⁻¹ := by rw [conj c hc]
    _ = a * b * (d * a⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [conj d hd]

namespace CentralRoot

variable {K : Type*} [Group K] (S : CentralRoot K)

theorem zpow_central (l : ℤ) (x : K) : S.r ^ l * x = x * S.r ^ l :=
  (Commute.zpow_left (show Commute S.r x from S.central x) l).eq

theorem decomp (k : K) : ∃ h ∈ S.H, ∃ l : ℤ, k = h * S.r ^ l := by
  obtain ⟨l, hl⟩ := S.gen k
  exact ⟨_, hl, l, by rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]⟩

/-- An exponent `l` with `k r^(-l) ∈ H`, chosen once and for all. -/
noncomputable def ell (k : K) : ℤ := Classical.choose (S.gen k)

theorem ell_spec (k : K) : k * S.r ^ (-S.ell k) ∈ S.H := Classical.choose_spec (S.gen k)

/-- The retraction `h r^l ↦ h g^l` on elements (well defined by `retr_spec`). -/
noncomputable def retr (k : K) : S.H :=
  ⟨k * S.r ^ (-S.ell k), S.ell_spec k⟩ * S.g ^ S.ell k

theorem coe_retr (k : K) :
    (S.retr k : K) = k * S.r ^ (-S.ell k) * (S.g : K) ^ S.ell k := by
  simp [retr]

/-- Well-definedness: `retr (h r^l) = h g^l` for every `h ∈ H` and `l`. -/
theorem retr_spec {h : K} (hh : h ∈ S.H) (l : ℤ) :
    (S.retr (h * S.r ^ l) : K) = h * (S.g : K) ^ l := by
  have h0 := S.ell_spec (h * S.r ^ l)
  have e1 : h * S.r ^ l * S.r ^ (-S.ell (h * S.r ^ l)) =
      h * S.r ^ (l - S.ell (h * S.r ^ l)) := by
    rw [mul_assoc, ← zpow_add, sub_eq_add_neg]
  have hmem : S.r ^ (l - S.ell (h * S.r ^ l)) ∈ S.H := by
    have e2 : S.r ^ (l - S.ell (h * S.r ^ l)) =
        h⁻¹ * (h * S.r ^ l * S.r ^ (-S.ell (h * S.r ^ l))) := by
      rw [e1, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e2]
    exact S.H.mul_mem (S.H.inv_mem hh) h0
  rw [coe_retr, e1, S.pow _ hmem, mul_assoc, ← zpow_add, sub_add_cancel]

theorem retr_coe (h : S.H) : S.retr (h : K) = h := by
  apply Subtype.ext
  have := S.retr_spec h.2 0
  simpa using this

/-- `retr (h r^l k) = h · retr k · g^l`. -/
theorem retr_mul {h : K} (hh : h ∈ S.H) (l : ℤ) (k : K) :
    (S.retr (h * S.r ^ l * k) : K) = h * (S.retr k : K) * (S.g : K) ^ l := by
  obtain ⟨h0, hh0, l0, rfl⟩ := S.decomp k
  have e : h * S.r ^ l * (h0 * S.r ^ l0) = (h * h0) * S.r ^ (l + l0) := by
    rw [mul_assoc h, S.zpow_central l, zpow_add]
    group
  rw [e, S.retr_spec (S.H.mul_mem hh hh0), S.retr_spec hh0, zpow_add]
  group

/-! ## The projection `q : ℤ[K] → ℤ[H]` -/

/-- `ι : ℤ[H] → ℤ[K]`. -/
noncomputable abbrev ι : MonoidAlgebra ℤ S.H →+* MonoidAlgebra ℤ K :=
  mapDomainRingHom ℤ S.H.subtype

/-- `q (Σ a_k k) = Σ a_k retr(k)`. -/
noncomputable def q : MonoidAlgebra ℤ K →+ MonoidAlgebra ℤ S.H :=
  MonoidAlgebra.liftNC (Int.castAddHom _) (fun k => of ℤ S.H (S.retr k))

theorem q_of (k : K) : S.q (of ℤ K k) = of ℤ S.H (S.retr k) := by
  simp [q, MonoidAlgebra.of_apply, MonoidAlgebra.liftNC_single]

/-- An additive property of `ℤ[G]` that holds on group elements holds everywhere. -/
theorem induction_of {G : Type*} [Group G] {p : MonoidAlgebra ℤ G → Prop}
    (x : MonoidAlgebra ℤ G) (h0 : p 0) (hof : ∀ g, p (of ℤ G g))
    (hneg : ∀ y, p y → p (-y)) (hadd : ∀ y z, p y → p z → p (y + z)) : p x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact h0
  | add y z hy hz => exact hadd y z hy hz
  | single g n =>
    have e : (MonoidAlgebra.single g n : MonoidAlgebra ℤ G) = n • of ℤ G g := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    rw [e]; clear e
    induction n using Int.induction_on with
    | zero => simpa using h0
    | succ n ih => rw [add_smul, one_smul]; exact hadd _ _ ih (hof g)
    | pred n ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]; exact hadd _ _ ih (hneg _ (hof g))

/-- `q (h r^l y) = h · q(y) · g^l`. -/
theorem q_mul_left {h : K} (hh : h ∈ S.H) (l : ℤ) (y : MonoidAlgebra ℤ K) :
    S.q (of ℤ K (h * S.r ^ l) * y) =
      of ℤ S.H ⟨h, hh⟩ * S.q y * of ℤ S.H (S.g ^ l) := by
  induction y using induction_of with
  | h0 => simp
  | hof k =>
    rw [← _root_.map_mul, q_of, q_of, ← _root_.map_mul, ← _root_.map_mul]
    congr 1
    apply Subtype.ext
    simp [S.retr_mul hh l k]
  | hneg y hy => rw [mul_neg, _root_.map_neg, hy, _root_.map_neg, mul_neg, neg_mul]
  | hadd y z hy hz => rw [mul_add, _root_.map_add, hy, hz, _root_.map_add, mul_add, add_mul]

theorem q_mul_of_r (y : MonoidAlgebra ℤ K) :
    S.q (y * of ℤ K S.r) = S.q y * of ℤ S.H S.g := by
  have hc : y * of ℤ K S.r = of ℤ K (1 * S.r ^ (1 : ℤ)) * y := by
    rw [one_mul, zpow_one]
    induction y using induction_of with
    | h0 => simp
    | hof k => rw [← _root_.map_mul, ← _root_.map_mul, S.central]
    | hneg y hy => rw [neg_mul, hy, mul_neg]
    | hadd y z hy hz => rw [add_mul, hy, hz, mul_add]
  rw [hc, S.q_mul_left S.H.one_mem, zpow_one,
    show (⟨1, S.H.one_mem⟩ : S.H) = 1 from rfl, _root_.map_one, one_mul]

theorem q_iota (x : MonoidAlgebra ℤ S.H) : S.q (S.ι x) = x := by
  induction x using induction_of with
  | h0 => rw [_root_.map_zero, _root_.map_zero]
  | hof h => rw [mapDomainRingHom_of, q_of]; simp [S.retr_coe]
  | hneg y hy => rw [_root_.map_neg, _root_.map_neg, hy]
  | hadd y z hy hz => rw [_root_.map_add, _root_.map_add, hy, hz]

/-! ## Centrality of `r` in `ℤ[K]` -/

theorem of_r_mem_center : of ℤ K S.r ∈ Subring.center (MonoidAlgebra ℤ K) := by
  rw [Subring.mem_center_iff]
  intro y
  induction y using induction_of with
  | h0 => simp
  | hof k => rw [← _root_.map_mul, ← _root_.map_mul, S.central]
  | hneg y hy => rw [neg_mul, hy, mul_neg]
  | hadd y z hy hz => rw [add_mul, hy, hz, mul_add]

theorem of_zpow_mem_center (l : ℤ) :
    of ℤ K (S.r ^ l) ∈ Subring.center (MonoidAlgebra ℤ K) := by
  rw [Subring.mem_center_iff]
  intro y
  induction y using induction_of with
  | h0 => simp
  | hof k => rw [← _root_.map_mul, ← _root_.map_mul, S.zpow_central]
  | hneg y hy => rw [neg_mul, hy, mul_neg]
  | hadd y z hy hz => rw [add_mul, hy, hz, mul_add]

/-- `r^l - 1 = u (r - 1)` with `u` central. -/
theorem of_zpow_sub_one_eq (l : ℤ) : ∃ u ∈ Subring.center (MonoidAlgebra ℤ K),
    of ℤ K (S.r ^ l) - 1 = u * (of ℤ K S.r - 1) := by
  have hr := S.of_r_mem_center
  have hri := S.of_zpow_mem_center (-1)
  induction l using Int.induction_on with
  | zero => exact ⟨0, Subring.zero_mem _, by rw [zpow_zero, _root_.map_one, sub_self, zero_mul]⟩
  | succ l ih =>
    obtain ⟨u, hu, e⟩ := ih
    refine ⟨of ℤ K S.r * u + 1, Subring.add_mem _ (Subring.mul_mem _ hr hu) (Subring.one_mem _), ?_⟩
    rw [zpow_add_one, _root_.map_mul, add_mul, mul_assoc, ← e]
    have : of ℤ K (S.r ^ (l : ℤ)) * of ℤ K S.r = of ℤ K S.r * of ℤ K (S.r ^ (l : ℤ)) := by
      rw [← _root_.map_mul, ← _root_.map_mul, ← zpow_add_one, ← zpow_one_add, add_comm]
    rw [this]; noncomm_ring
  | pred l ih =>
    obtain ⟨u, hu, e⟩ := ih
    refine ⟨of ℤ K (S.r ^ (-1 : ℤ)) * u - of ℤ K (S.r ^ (-1 : ℤ)),
      Subring.sub_mem _ (Subring.mul_mem _ hri hu) hri, ?_⟩
    have hinv : of ℤ K (S.r ^ (-1 : ℤ)) * of ℤ K S.r = 1 := by
      rw [← _root_.map_mul, zpow_neg_one, inv_mul_cancel, _root_.map_one]
    have hsplit : of ℤ K (S.r ^ (-(l : ℤ) - 1)) =
        of ℤ K (S.r ^ (-1 : ℤ)) * of ℤ K (S.r ^ (-(l : ℤ))) := by
      rw [← _root_.map_mul, ← zpow_add, add_comm, sub_eq_add_neg]
    rw [hsplit, sub_mul, mul_assoc, ← e]
    rw [mul_sub, mul_sub, hinv]
    noncomm_ring

/-! ## The filtration -/

/-- The left ideal of `ℤ[K]` spanned by the `x (r - 1)^i`, `x ∈ Δ(H)^(n-i)`, `i ≤ n`. -/
noncomputable def W (n : ℕ) : Ideal (MonoidAlgebra ℤ K) :=
  Ideal.span {y | ∃ i ≤ n, ∃ x ∈ augIdeal S.H ^ (n - i), y = S.ι x * (of ℤ K S.r - 1) ^ i}

theorem gen_mem_W {n i : ℕ} (hi : i ≤ n) {x : MonoidAlgebra ℤ S.H}
    (hx : x ∈ augIdeal S.H ^ (n - i)) : S.ι x * (of ℤ K S.r - 1) ^ i ∈ S.W n :=
  Ideal.subset_span ⟨i, hi, x, hx, rfl⟩

theorem sub_one_mem_center : of ℤ K S.r - 1 ∈ Subring.center (MonoidAlgebra ℤ K) :=
  Subring.sub_mem _ S.of_r_mem_center (Subring.one_mem _)

/-- An element of `Δ(K)` is a `ℤ`-combination of the `k - 1`. -/
theorem augIdeal_induction {p : MonoidAlgebra ℤ K → Prop} {b : MonoidAlgebra ℤ K}
    (hb : b ∈ augIdeal K) (h0 : p 0) (hof : ∀ k, p (of ℤ K k - 1))
    (hneg : ∀ y, p y → p (-y)) (hadd : ∀ y z, p y → p z → p (y + z)) : p b := by
  have key : ∀ y : MonoidAlgebra ℤ K, p (y - (augmentation K y : MonoidAlgebra ℤ K)) := by
    intro y
    induction y using induction_of with
    | h0 => simpa using h0
    | hof k => rw [augmentation_of, Int.cast_one]; exact hof k
    | hneg y hy => simpa [neg_sub_neg, sub_eq_add_neg, add_comm] using hneg _ hy
    | hadd y z hy hz =>
      have := hadd _ _ hy hz
      rw [_root_.map_add, Int.cast_add]
      convert this using 1; abel
  have := key b
  rwa [(mem_augIdeal.mp hb), Int.cast_zero, sub_zero] at this

theorem W_mul_augIdeal (n : ℕ) {a b : MonoidAlgebra ℤ K} (ha : a ∈ S.W n)
    (hb : b ∈ augIdeal K) : a * b ∈ S.W (n + 1) := by
  -- the generators
  have gen : ∀ i ≤ n, ∀ x ∈ augIdeal S.H ^ (n - i),
      S.ι x * (of ℤ K S.r - 1) ^ i * b ∈ S.W (n + 1) := by
    intro i hi x hx
    refine augIdeal_induction (p := fun b => S.ι x * (of ℤ K S.r - 1) ^ i * b ∈ S.W (n + 1))
      hb (by simp) ?_ (fun y hy => by simpa [mul_neg] using neg_mem hy)
      (fun y z hy hz => by simpa [mul_add] using add_mem hy hz)
    intro k
    obtain ⟨h, hh, l, rfl⟩ := S.decomp k
    obtain ⟨u, hu, hul⟩ := S.of_zpow_sub_one_eq l
    have hc := S.sub_one_mem_center
    have hcpow : (of ℤ K S.r - 1) ^ i ∈ Subring.center (MonoidAlgebra ℤ K) :=
      Subring.pow_mem _ hc i
    -- h r^l - 1 = (h - 1) r^l + (r^l - 1)
    have hsplit : of ℤ K (h * S.r ^ l) - 1 =
        S.ι (of ℤ S.H ⟨h, hh⟩ - 1) * of ℤ K (S.r ^ l) + u * (of ℤ K S.r - 1) := by
      rw [← hul, _root_.map_sub, _root_.map_one, mapDomainRingHom_of, _root_.map_mul]
      simp only [Subgroup.coe_subtype]
      noncomm_ring
    rw [hsplit, mul_add]
    refine add_mem ?_ ?_
    · -- x (r-1)^i (h-1) r^l = r^l · [x (h-1)] (r-1)^i
      have e : S.ι x * (of ℤ K S.r - 1) ^ i * (S.ι (of ℤ S.H ⟨h, hh⟩ - 1) * of ℤ K (S.r ^ l)) =
          of ℤ K (S.r ^ l) * (S.ι (x * (of ℤ S.H ⟨h, hh⟩ - 1)) * (of ℤ K S.r - 1) ^ i) := by
        rw [_root_.map_mul, ← center_comm (S.of_zpow_mem_center l), mul_assoc,
          ← mul_assoc ((of ℤ K S.r - 1) ^ i), ← center_comm hcpow]
        simp only [mul_assoc]
      rw [e]
      refine Ideal.mul_mem_left _ _ (S.gen_mem_W (by omega) ?_)
      have := mul_mem_augIdeal_pow hx
        (show of ℤ S.H ⟨h, hh⟩ - 1 ∈ augIdeal S.H ^ 1 by
          rw [Submodule.pow_one]; exact of_sub_one_mem_augIdeal _)
      rwa [show n - i + 1 = n + 1 - i by omega] at this
    · -- x (r-1)^i u (r-1) = u · x (r-1)^(i+1)
      have e : S.ι x * (of ℤ K S.r - 1) ^ i * (u * (of ℤ K S.r - 1)) =
          u * (S.ι x * (of ℤ K S.r - 1) ^ (i + 1)) := by
        rw [← mul_assoc, center_comm hu, pow_succ]
        noncomm_ring
      rw [e]
      refine Ideal.mul_mem_left _ _ (S.gen_mem_W (by omega) ?_)
      rwa [show n + 1 - (i + 1) = n - i by omega]
  -- induction over the span
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, hi, x, hx, rfl⟩
    exact gen i hi x hx
  · simp
  · intro y z _ _ hy hz
    rw [add_mul]; exact add_mem hy hz
  · intro c y _ hy
    rw [smul_eq_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ hy

theorem augIdeal_pow_le_W (n : ℕ) : augIdeal K ^ n ≤ S.W n := by
  induction n with
  | zero =>
    rw [Submodule.pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
    have := S.gen_mem_W (n := 0) (i := 0) le_rfl (x := 1)
      (by rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    rwa [_root_.map_one, pow_zero, mul_one] at this
  | succ n ih =>
    rw [Submodule.pow_succ, Ideal.mul_le]
    intro a ha b hb
    exact S.W_mul_augIdeal n (ih ha) hb

/-- The left ideal `{y | q y ∈ Δ(H)^n}`. -/
noncomputable def T (n : ℕ) : Ideal (MonoidAlgebra ℤ K) where
  carrier := {y | S.q y ∈ augIdeal S.H ^ n}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz
    simp only [Set.mem_setOf_eq, _root_.map_add] at *
    exact add_mem hy hz
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    induction c using induction_of with
    | h0 => simp
    | hof k =>
      obtain ⟨h, hh, l, rfl⟩ := S.decomp k
      rw [S.q_mul_left hh]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hy)
    | hneg c hc => rw [neg_mul, _root_.map_neg]; exact neg_mem hc
    | hadd c d hc hd => rw [add_mul, _root_.map_add]; exact add_mem hc hd

theorem q_gen (x : MonoidAlgebra ℤ S.H) (i : ℕ) :
    S.q (S.ι x * (of ℤ K S.r - 1) ^ i) = x * (of ℤ S.H S.g - 1) ^ i := by
  induction i with
  | zero => rw [pow_zero, mul_one, pow_zero, mul_one]; exact S.q_iota x
  | succ i ih =>
    rw [pow_succ, ← mul_assoc, mul_sub, mul_one, _root_.map_sub, S.q_mul_of_r, ih, pow_succ]
    noncomm_ring

theorem W_le_T (n : ℕ) : S.W n ≤ S.T n := by
  rw [W, Ideal.span_le]
  rintro _ ⟨i, hi, x, hx, rfl⟩
  show S.q (S.ι x * (of ℤ K S.r - 1) ^ i) ∈ augIdeal S.H ^ n
  rw [q_gen]
  have := mul_mem_augIdeal_pow hx
    (Ideal.pow_mem_pow (of_sub_one_mem_augIdeal S.g) i)
  rwa [Nat.sub_add_cancel hi] at this

/-! ## The lemma -/

/-- **Lemma 5.9, ring form**: `ℤ[H] ∩ Δ(K)^n = Δ(H)^n`. -/
theorem iota_mem_augIdeal_pow_iff (n : ℕ) (x : MonoidAlgebra ℤ S.H) :
    S.ι x ∈ augIdeal K ^ n ↔ x ∈ augIdeal S.H ^ n := by
  constructor
  · intro hx
    have := S.W_le_T n (S.augIdeal_pow_le_W n hx)
    change S.q (S.ι x) ∈ augIdeal S.H ^ n at this
    rwa [S.q_iota] at this
  · exact mapDomain_mem_augIdeal_pow S.H.subtype n

theorem commutator_le : commutator K ≤ S.H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨h1, hh1, l1, rfl⟩ := S.decomp a
  obtain ⟨h2, hh2, l2, rfl⟩ := S.decomp b
  rw [commutatorElement_def, comm_central h1 h2 _ _ (S.zpow_central l1) (S.zpow_central l2)]
  exact S.H.mul_mem (S.H.mul_mem (S.H.mul_mem hh1 hh2) (S.H.inv_mem hh1)) (S.H.inv_mem hh2)

/-- **Lemma 5.9**: `D_n(K) = D_n(H)` for `n ≥ 2`. -/
theorem D_eq (n : ℕ) (hn : 2 ≤ n) : D n K = (D n S.H).map S.H.subtype := by
  refine le_antisymm ?_ (map_D_le _ n)
  intro k hk
  have hk2 : k ∈ S.H := by
    have : k ∈ D 2 K := D_antitone hn hk
    rw [D_two, Subgroup.top_lowerCentralSeries_one] at this
    exact S.commutator_le this
  refine ⟨⟨k, hk2⟩, ?_, rfl⟩
  show (⟨k, hk2⟩ : S.H) ∈ D n S.H
  rw [mem_D, ← S.iota_mem_augIdeal_pow_iff, _root_.map_sub, _root_.map_one, mapDomainRingHom_of]
  exact hk

end CentralRoot

/-- **Lemma 5.9 as stated in the paper.** `K = H⟨r⟩` with `r` central, `|K : H| = m`
(i.e. `r^d ∈ H ↔ m ∣ d`; only `→` is needed), and `r^m = g^m` for some `g ∈ H`, not necessarily
central. Then `ℤ[H] ∩ Δ(K)^n = Δ(H)^n` for all `n` and `D_n(K) = D_n(H)` for `n ≥ 2`.
The other direction of `|K : H| = m` (`m ∣ d → r^d ∈ H`) follows from `root`; `m = 0` is allowed
and covers `K ≅ H × ℤ`. -/
theorem D_n_eq_of_index {K : Type*} [Group K] (H : Subgroup K) (r : K) (g : H) (m : ℕ)
    (central : ∀ x : K, r * x = x * r) (gen : ∀ k : K, ∃ l : ℤ, k * r ^ (-l) ∈ H)
    (index : ∀ d : ℤ, r ^ d ∈ H → (m : ℤ) ∣ d) (root : r ^ m = (g : K) ^ m) :
    (∀ (n : ℕ) (x : MonoidAlgebra ℤ H),
        mapDomainRingHom ℤ H.subtype x ∈ augIdeal K ^ n ↔ x ∈ augIdeal H ^ n) ∧
      ∀ n, 2 ≤ n → D n K = (D n H).map H.subtype := by
  let S : CentralRoot K :=
    { H := H, r := r, g := g, central := central, gen := gen
      pow := fun d hd => by
        obtain ⟨t, rfl⟩ := index d hd
        rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, root] }
  exact ⟨S.iota_mem_augIdeal_pow_iff, S.D_eq⟩

end GroupDimension
