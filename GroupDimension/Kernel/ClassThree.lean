module

public import GroupDimension.Passi

@[expose] public section

/-!
# The class-3 quotient: `Dₙ(Q) ⊆ τ(γ₃ Q)`, the map `θ`, Corollary 2, the relation to MATH-41
(fast-core paper, §6.8(a); MATH-309)

`cflint-fast-core`, `docs/analysis.md`, §6.8(a):

> **Lemma 1.** Let `Q` be a finitely generated nilpotent group of class `≤ 3` and `n ∈ {4, 5}`.
> Then `D_n(Q) ⊆ τ(γ₃(Q))` (the torsion of `γ₃`), and `θ : γ₃(Q) → Δ³/Δⁿ`, `g ↦ g − 1`, is a
> homomorphism with kernel `D_n(Q) ∩ γ₃(Q)`. Hence, if `τ(γ₃(Q))` is a 2-group, `D_n(Q) = 1` iff
> `θ` is injective on the elements of order 2 of `τ(γ₃(Q))`.
>
> **Corollary 2.** Let `G` be a group with `γ₅(G) = 1` and `Q = G/γ₄(G)` with `D₅(Q) = 1`. Then
> `D_r(G) ∩ γ₄(G) = 1` implies `D_r(G) = 1` for every `r ≥ 5`.
>
> **Relation to MATH-41.** An element of `D₇(G) ∖ γ₄(G)` in a class-4 group gives `1 ≠ x ∈ D₅(Q)`
> for the class-3 quotient; `x` has 2-power order, and … (Gruenberg) `x` survives in a finite
> 2-group of class `≤ 3` with `D₅ ≠ 1`.

Indexing as in `Statements.lean`: `γ₃ = (⊤ : Subgroup G).lowerCentralSeries 2`,
`γ₄ = … 3`, `γ_n = … (n − 1)`.

## What is proved

* **Lemma 1, the map `θ`** (any group, any `n ≤ 6`; class and finite generation are not used).
  `thetaHom G n hn : γ₃(G) →* Multiplicative (ℤ[G]/Δⁿ)`, `g ↦ (g − 1) mod Δⁿ`, is a homomorphism,
  since `(g − 1)(h − 1) ∈ Δ³·Δ³ ⊆ Δ⁶ ⊆ Δⁿ` (`sub_one_mul_sub_one_mem_pow`); its values lie in
  `Δ³/Δⁿ` (`sub_one_mem_pow_three`); its kernel is `D_n ∩ γ₃` (`ker_thetaHom`,
  `map_ker_thetaHom`), and, given `D₃ = γ₃` and `n ≥ 3`, it is `D_n` itself (`map_ker_thetaHom_eq`).
* **Lemma 1, `D_n(Q) ⊆ τ(γ₃ Q)`**, by the paper's proof: with `DThreeEqGammaThree` and Jennings'
  theorem in the form `JenningsIsolator` (`Statements.lean`, a hypothesis, not proved here), for
  `Q` finitely generated with `γ₄(Q) = 1` and `n ≥ 4`, every `g ∈ D_n(Q)` lies in `γ₃(Q)` and has
  finite order (`mem_gammaThree_isOfFinOrder_of_mem_D`).
  **Without any hypothesis** and without finite generation, more is true: `g ∈ D_n(Q)`, `n ≥ 4`,
  `γ₄(Q) = 1` give `g ∈ γ₃(Q)` and `g² = 1` (`mem_gammaThree_sq_eq_one_of_mem_D'`), by Passi's
  `D₄² ⊆ γ₄` (`passiDFourSquare`) and `D₃ = γ₃` (`dThreeEqGammaThree`), both proved in this project.
* **Lemma 1, the criterion.** As in the paper (hypotheses `DThreeEqGammaThree`,
  `JenningsIsolator`; `Q` f.g., `γ₄(Q) = 1`, every element of finite order of `γ₃(Q)` of
  `2`-power order, `4 ≤ n ≤ 6`): `D_n(Q) = 1` iff `θ` has no nontrivial `g` with `g² = 1` in its
  kernel (`D_eq_bot_iff_theta`). Without hypotheses, for every `Q` with `γ₄(Q) = 1` and
  `4 ≤ n ≤ 6`, with no condition on the torsion of `γ₃` (`D_eq_bot_iff_theta'`).
* **Corollary 2** (`D_eq_bot_of_inf_gammaFour_eq_bot`): if `D₅(G/γ₄(G)) = 1`, `r ≥ 5` and
  `D_r(G) ∩ γ₄(G) = 1`, then `D_r(G) = 1`. The hypothesis `γ₅(G) = 1` of the paper is not needed
  (the proof does not use it).
* **Relation to MATH-41** (`exists_two_group_of_mem_D_five`, and `exists_two_group_of_mem_D_seven`
  for the paper's `D₇`): with `PassiDFourSquare` and `GruenbergResidualTwo`, an element of
  `D₅(G) ∖ γ₄(G)` of a finitely generated group `G` (of any class) gives a finite `2`-group `P` with
  `γ₄(P) = 1` and `D₅(P) ≠ 1`; the primed versions use the proved `passiDFourSquare`,
  `gruenbergResidualTwo`. The paper's "`x` has 2-power order" is Passi's `D₄² ⊆ γ₄`: the image of
  the element in `G/γ₄(G)` has order `2`.

## What is not formalized here

* Jennings' theorem itself (`JenningsIsolator` is a hypothesis; the hypothesis-free versions avoid
  it via Passi's theorem). Its link to Quillen's theorem behind the certificate of §6.4.
* `θ` as a map into `Δ³/Δⁿ` (here into `ℤ[Q]/Δⁿ`, with `sub_one_mem_pow_three` for the values),
  and "injective on the elements of order 2 of `τ(γ₃)`" as a statement about a restricted map: the
  criterion is stated with "`g² = 1`, `θ g = 1` ⟹ `g = 1`".
* Everything computational in §6.8(a): the 80 groups `Q`, the presentations from the records, `nq`,
  `scripts/c4_q3.py`, the Howell forms of `howell_gpu.py`, the table of results and the statement that
  `G_φ/γ₄ = M/γ₄(M) = Γ/γ₄(Γ)Γ''` depends only on `Γ`.
* Part (b) of §6.8 (Lemma 3, Proposition 4).
-/

namespace GroupDimension.Kernel.ClassThree

noncomputable section

open MonoidAlgebra

/-! ## The map `θ` -/

section Theta

variable {G : Type*} [Group G]

/-- `(g − 1)(h − 1) ∈ Δ^{i+j}` for `g ∈ D_i`, `h ∈ D_j`. -/
theorem sub_one_mul_sub_one_mem_pow {i j : ℕ} {g h : G} (hg : g ∈ D i G) (hh : h ∈ D j G) :
    (of ℤ G g - 1) * (of ℤ G h - 1) ∈ augIdeal G ^ (i + j) :=
  mul_mem_augIdeal_pow hg hh

/-- `g − 1 ∈ Δ³` for `g ∈ γ₃`. -/
theorem sub_one_mem_pow_three {g : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    of ℤ G g - 1 ∈ augIdeal G ^ 3 :=
  lowerCentralSeries_le_D G 2 hg

/-- `gh − 1 ≡ (g − 1) + (h − 1) (mod Δⁿ)` for `g, h ∈ γ₃`, `n ≤ 6`. -/
theorem mk_mul_sub_one {n : ℕ} (hn : n ≤ 6) {g h : G}
    (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries 2)
    (hh : h ∈ (⊤ : Subgroup G).lowerCentralSeries 2) :
    Ideal.Quotient.mk (augIdeal G ^ n) (of ℤ G (g * h) - 1) =
      Ideal.Quotient.mk (augIdeal G ^ n) (of ℤ G g - 1) +
        Ideal.Quotient.mk (augIdeal G ^ n) (of ℤ G h - 1) := by
  rw [← map_add, Ideal.Quotient.eq]
  have e : of ℤ G (g * h) - 1 - ((of ℤ G g - 1) + (of ℤ G h - 1)) =
      (of ℤ G g - 1) * (of ℤ G h - 1) := by
    rw [map_mul]; noncomm_ring
  rw [e]
  exact Ideal.pow_le_pow_right hn
    (sub_one_mul_sub_one_mem_pow (lowerCentralSeries_le_D G 2 hg) (lowerCentralSeries_le_D G 2 hh))

variable (G) in
/-- **Lemma 1**: `θ : γ₃(G) → ℤ[G]/Δⁿ`, `g ↦ (g − 1) mod Δⁿ`, is a homomorphism for `n ≤ 6`
(to the additive group, written multiplicatively). -/
def thetaHom (n : ℕ) (hn : n ≤ 6) :
    (⊤ : Subgroup G).lowerCentralSeries 2 →* Multiplicative (MonoidAlgebra ℤ G ⧸ augIdeal G ^ n) where
  toFun g := Multiplicative.ofAdd (Ideal.Quotient.mk _ (of ℤ G (g : G) - 1))
  map_one' := by
    show Multiplicative.ofAdd _ = 1
    rw [OneMemClass.coe_one, map_one, sub_self, map_zero, ofAdd_zero]
  map_mul' g h := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add, Subgroup.coe_mul, mk_mul_sub_one hn g.2 h.2]

theorem thetaHom_apply (n : ℕ) (hn : n ≤ 6) (g : (⊤ : Subgroup G).lowerCentralSeries 2) :
    thetaHom G n hn g = Multiplicative.ofAdd (Ideal.Quotient.mk _ (of ℤ G (g : G) - 1)) := rfl

theorem thetaHom_eq_one_iff (n : ℕ) (hn : n ≤ 6) (g : (⊤ : Subgroup G).lowerCentralSeries 2) :
    thetaHom G n hn g = 1 ↔ (g : G) ∈ D n G := by
  rw [thetaHom_apply, ofAdd_eq_one, Ideal.Quotient.eq_zero_iff_mem]
  exact Iff.rfl

/-- **Lemma 1**: the kernel of `θ` is `D_n ∩ γ₃`. -/
theorem ker_thetaHom (n : ℕ) (hn : n ≤ 6) :
    (thetaHom G n hn).ker = (D n G).subgroupOf ((⊤ : Subgroup G).lowerCentralSeries 2) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, thetaHom_eq_one_iff]

/-- The same, as a subgroup of `G`: `ker θ = D_n ⊓ γ₃`. -/
theorem map_ker_thetaHom (n : ℕ) (hn : n ≤ 6) :
    (thetaHom G n hn).ker.map ((⊤ : Subgroup G).lowerCentralSeries 2).subtype =
      D n G ⊓ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  rw [ker_thetaHom, Subgroup.subgroupOf_map_subtype]

/-- `D_n ≤ γ₃` for `n ≥ 3`, given `D₃ = γ₃`. -/
theorem D_le_gammaThree (hD3 : DThreeEqGammaThree) (G : Type) [Group G] {n : ℕ} (hn : 3 ≤ n) :
    D n G ≤ (⊤ : Subgroup G).lowerCentralSeries 2 := by
  rw [← hD3 G]
  exact D_antitone hn

/-- Given `D₃ = γ₃`, the kernel of `θ` is `D_n` itself (`3 ≤ n ≤ 6`). -/
theorem map_ker_thetaHom_eq (hD3 : DThreeEqGammaThree) (G : Type) [Group G] {n : ℕ}
    (hn3 : 3 ≤ n) (hn : n ≤ 6) :
    (thetaHom G n hn).ker.map ((⊤ : Subgroup G).lowerCentralSeries 2).subtype = D n G := by
  rw [map_ker_thetaHom, inf_eq_left.mpr (D_le_gammaThree hD3 G hn3)]

end Theta

/-! ## `D_n(Q) ⊆ τ(γ₃ Q)` -/

/-- **Lemma 1**, the paper's proof: given `D₃ = γ₃` and Jennings' `D_n ⊆ √γ_n`, for `Q` finitely
generated of class `≤ 3` and `n ≥ 4`, every element of `D_n(Q)` lies in `γ₃(Q)` and has finite
order. -/
theorem mem_gammaThree_isOfFinOrder_of_mem_D (hD3 : DThreeEqGammaThree) (hJ : JenningsIsolator)
    (Q : Type) [Group Q] (hfg : Group.FG Q) (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥)
    {n : ℕ} (hn : 4 ≤ n) {g : Q} (hg : g ∈ D n Q) :
    g ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 ∧ IsOfFinOrder g := by
  refine ⟨D_le_gammaThree hD3 Q (by omega) hg, ?_⟩
  obtain ⟨m, hm, hgm⟩ := hJ Q hfg (Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨3, hQ⟩) n
    (by omega) g hg
  have h4 : g ^ m ∈ (⊤ : Subgroup Q).lowerCentralSeries 3 :=
    (Subgroup.lowerCentralSeries_antitone ⊤) (by omega : 3 ≤ n - 1) hgm
  rw [hQ, Subgroup.mem_bot] at h4
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h4⟩

/-- **Lemma 1, stronger**: given `D₃ = γ₃` and Passi's `D₄² ⊆ γ₄`, for any `Q` of class `≤ 3`
(not necessarily finitely generated) and `n ≥ 4`, every `g ∈ D_n(Q)` lies in `γ₃(Q)` and
`g² = 1`. -/
theorem mem_gammaThree_sq_eq_one_of_mem_D (hD3 : DThreeEqGammaThree) (hP : PassiDFourSquare)
    (Q : Type) [Group Q] (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥)
    {n : ℕ} (hn : 4 ≤ n) {g : Q} (hg : g ∈ D n Q) :
    g ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 ∧ g ^ 2 = 1 := by
  refine ⟨D_le_gammaThree hD3 Q (by omega) hg, ?_⟩
  have := hP Q g (D_antitone hn hg)
  rwa [hQ, Subgroup.mem_bot] at this

/-- **Lemma 1** (`D_n(Q) ⊆ τ(γ₃ Q)`, indeed of exponent `2`) without hypotheses. -/
theorem mem_gammaThree_sq_eq_one_of_mem_D' (Q : Type) [Group Q]
    (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) {n : ℕ} (hn : 4 ≤ n) {g : Q}
    (hg : g ∈ D n Q) : g ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 ∧ g ^ 2 = 1 :=
  mem_gammaThree_sq_eq_one_of_mem_D dThreeEqGammaThree passiDFourSquare Q hQ hn hg

/-- `D_n(Q) ⊆ τ(γ₃ Q)` in the paper's form, without hypotheses. -/
theorem mem_gammaThree_isOfFinOrder_of_mem_D' (Q : Type) [Group Q]
    (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) {n : ℕ} (hn : 4 ≤ n) {g : Q}
    (hg : g ∈ D n Q) : g ∈ (⊤ : Subgroup Q).lowerCentralSeries 2 ∧ IsOfFinOrder g := by
  obtain ⟨h3, h2⟩ := mem_gammaThree_sq_eq_one_of_mem_D' Q hQ hn hg
  exact ⟨h3, isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, h2⟩⟩

/-! ## The criterion: `D_n(Q) = 1` iff `θ` is injective on the elements of order `2` -/

/-- If no `g ≠ 1` of `D_n ∩ γ₃` has `g² = 1`, then no `g ≠ 1` of `D_n ∩ γ₃` has
`g^{2^k} = 1`. -/
theorem eq_one_of_pow_two_pow_eq_one {Q : Type*} [Group Q] {n : ℕ}
    (h : ∀ g ∈ D n Q ⊓ (⊤ : Subgroup Q).lowerCentralSeries 2, g ^ 2 = 1 → g = 1) :
    ∀ (k : ℕ) (g : Q), g ∈ D n Q ⊓ (⊤ : Subgroup Q).lowerCentralSeries 2 → g ^ 2 ^ k = 1 →
      g = 1
  | 0, g, _, hk => by rwa [pow_zero, pow_one] at hk
  | k + 1, g, hg, hk => by
    refine eq_one_of_pow_two_pow_eq_one h k g hg ?_
    refine h _ (pow_mem hg _) ?_
    rw [← pow_mul, ← pow_succ, hk]

/-- **Lemma 1, the criterion**, as in the paper: given `D₃ = γ₃` and Jennings, for `Q` finitely
generated of class `≤ 3` whose `τ(γ₃ Q)` is a `2`-group and `4 ≤ n ≤ 6`, `D_n(Q) = 1` iff no
`g ≠ 1` of `γ₃(Q)` with `g² = 1` is killed by `θ`. -/
theorem D_eq_bot_iff_theta (hD3 : DThreeEqGammaThree) (hJ : JenningsIsolator)
    (Q : Type) [Group Q] (hfg : Group.FG Q) (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥)
    (h2 : ∀ g ∈ (⊤ : Subgroup Q).lowerCentralSeries 2, IsOfFinOrder g → ∃ k : ℕ, g ^ 2 ^ k = 1)
    {n : ℕ} (hn4 : 4 ≤ n) (hn : n ≤ 6) :
    D n Q = ⊥ ↔ ∀ g : (⊤ : Subgroup Q).lowerCentralSeries 2,
      (g : Q) ^ 2 = 1 → thetaHom Q n hn g = 1 → g = 1 := by
  constructor
  · intro hD g _ hθ
    rw [thetaHom_eq_one_iff, hD, Subgroup.mem_bot] at hθ
    exact Subtype.ext hθ
  · intro hθ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨h3, hfin⟩ := mem_gammaThree_isOfFinOrder_of_mem_D hD3 hJ Q hfg hQ hn4 hg
    obtain ⟨k, hk⟩ := h2 g h3 hfin
    refine eq_one_of_pow_two_pow_eq_one (fun x hx hx2 => ?_) k g ⟨hg, h3⟩ hk
    have := hθ ⟨x, hx.2⟩ hx2 ((thetaHom_eq_one_iff n hn _).mpr hx.1)
    exact congrArg Subtype.val this

/-- **Lemma 1, the criterion, stronger**: given `D₃ = γ₃` and Passi's theorem, for any `Q` of
class `≤ 3` and `4 ≤ n ≤ 6` (no finite generation, no condition on `τ(γ₃ Q)`), `D_n(Q) = 1` iff
no `g ≠ 1` of `γ₃(Q)` with `g² = 1` is killed by `θ`. -/
theorem D_eq_bot_iff_theta_of_passi (hD3 : DThreeEqGammaThree) (hP : PassiDFourSquare)
    (Q : Type) [Group Q] (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥)
    {n : ℕ} (hn4 : 4 ≤ n) (hn : n ≤ 6) :
    D n Q = ⊥ ↔ ∀ g : (⊤ : Subgroup Q).lowerCentralSeries 2,
      (g : Q) ^ 2 = 1 → thetaHom Q n hn g = 1 → g = 1 := by
  constructor
  · intro hD g _ hθ
    rw [thetaHom_eq_one_iff, hD, Subgroup.mem_bot] at hθ
    exact Subtype.ext hθ
  · intro hθ
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨h3, h2⟩ := mem_gammaThree_sq_eq_one_of_mem_D hD3 hP Q hQ hn4 hg
    exact congrArg Subtype.val (hθ ⟨g, h3⟩ h2 ((thetaHom_eq_one_iff n hn _).mpr hg))

/-- **Lemma 1, the criterion**, without hypotheses. -/
theorem D_eq_bot_iff_theta' (Q : Type) [Group Q]
    (hQ : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥) {n : ℕ} (hn4 : 4 ≤ n) (hn : n ≤ 6) :
    D n Q = ⊥ ↔ ∀ g : (⊤ : Subgroup Q).lowerCentralSeries 2,
      (g : Q) ^ 2 = 1 → thetaHom Q n hn g = 1 → g = 1 :=
  D_eq_bot_iff_theta_of_passi dThreeEqGammaThree passiDFourSquare Q hQ hn4 hn

/-! ## Corollary 2 -/

/-- **Corollary 2**: if `D₅(G/γ₄(G)) = 1`, then for `r ≥ 5`, `D_r(G) ∩ γ₄(G) = 1` implies
`D_r(G) = 1`. (The paper assumes `γ₅(G) = 1`; it is not needed.) -/
theorem D_eq_bot_of_inf_gammaFour_eq_bot {G : Type*} [Group G]
    (hQ : D 5 (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 3) = ⊥) {r : ℕ} (hr : 5 ≤ r)
    (h : D r G ⊓ (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥) : D r G = ⊥ := by
  have h5 : D r G ≤ (⊤ : Subgroup G).lowerCentralSeries 3 :=
    (D_antitone hr).trans (D_le_of_D_quotient_eq_bot _ 5 hQ)
  rwa [inf_eq_left.mpr h5] at h

/-! ## Relation to MATH-41 -/

/-- **Relation to MATH-41**: given Passi's and Gruenberg's theorems, an element of
`D₅(G) ∖ γ₄(G)` of a finitely generated group `G` gives a finite `2`-group `P` of class `≤ 3`
with `D₅(P) ≠ 1`, a negative answer to MATH-41 (Kourovka 20.84 for finite `2`-groups). -/
theorem exists_two_group_of_mem_D_five (hP : PassiDFourSquare) (hG : GruenbergResidualTwo)
    (G : Type) [Group G] (hfg : Group.FG G) {x : G} (hx : x ∈ D 5 G)
    (hx4 : x ∉ (⊤ : Subgroup G).lowerCentralSeries 3) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P), IsPGroup 2 P ∧
      (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ ∧ D 5 P ≠ ⊥ := by
  by_contra hne
  have hall : ∀ (P : Type) [Group P] [Finite P], IsPGroup 2 P →
      (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ → D 5 P = ⊥ := by
    intro P _ _ h2 h3
    by_contra hD
    exact hne ⟨P, inferInstance, inferInstance, h2, h3, hD⟩
  haveI := hfg
  have hfgQ : Group.FG (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 3) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  have hQ := D_five_eq_bot_of_fg hP hG hall _ hfgQ
    (lowerCentralSeries_quotient_eq_bot 3)
  exact hx4 (D_le_of_D_quotient_eq_bot _ 5 hQ hx)

/-- **Relation to MATH-41**, the paper's form: an element of `D₇(G) ∖ γ₄(G)` (`G` finitely
generated; the paper's `G` has class `4`, which is not needed) gives a finite `2`-group of class
`≤ 3` with `D₅ ≠ 1`. -/
theorem exists_two_group_of_mem_D_seven (hP : PassiDFourSquare) (hG : GruenbergResidualTwo)
    (G : Type) [Group G] (hfg : Group.FG G) {x : G} (hx : x ∈ D 7 G)
    (hx4 : x ∉ (⊤ : Subgroup G).lowerCentralSeries 3) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P), IsPGroup 2 P ∧
      (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ ∧ D 5 P ≠ ⊥ :=
  exists_two_group_of_mem_D_five hP hG G hfg (D_antitone (by norm_num : 5 ≤ 7) hx) hx4

/-- **Relation to MATH-41** (`D₅`), without hypotheses. -/
theorem exists_two_group_of_mem_D_five' (G : Type) [Group G] (hfg : Group.FG G) {x : G}
    (hx : x ∈ D 5 G) (hx4 : x ∉ (⊤ : Subgroup G).lowerCentralSeries 3) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P), IsPGroup 2 P ∧
      (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ ∧ D 5 P ≠ ⊥ :=
  exists_two_group_of_mem_D_five passiDFourSquare gruenbergResidualTwo G hfg hx hx4

/-- **Relation to MATH-41** (`D₇`), without hypotheses. -/
theorem exists_two_group_of_mem_D_seven' (G : Type) [Group G] (hfg : Group.FG G) {x : G}
    (hx : x ∈ D 7 G) (hx4 : x ∉ (⊤ : Subgroup G).lowerCentralSeries 3) :
    ∃ (P : Type) (_ : Group P) (_ : Finite P), IsPGroup 2 P ∧
      (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ ∧ D 5 P ≠ ⊥ :=
  exists_two_group_of_mem_D_seven passiDFourSquare gruenbergResidualTwo G hfg hx hx4

end

end GroupDimension.Kernel.ClassThree
