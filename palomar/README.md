# Palomar submission

This repository is submitted to the [Palomar registry](https://palomar-registry.org) in the
ordinary layout: `Challenge.lean`, `Solution.lean`, `comparator.json` and `formalization.yaml` at
the repository root, licence `LICENSE` (MIT). The Lean project is the repository itself
(Lean/Mathlib `v4.35.0`, every file a module).

* `Challenge.lean` states the results using **Mathlib only**; every theorem ends in `sorry`.
* `Solution.lean` is **generated** from `Challenge.lean` by `palomar/make_solution.py`. It
  repeats the definitions verbatim, which Comparator requires, and adds bridge lemmas to the
  development's definitions (`DSet_eq : DSet n G = D n G`, `isCandidate_iff`, ...). It then
  proves each theorem from the development. After editing the Challenge, run
  `python3 palomar/make_solution.py`.
* `comparator.json` names the nine compared theorems. The permitted axioms are `propext`,
  `Quot.sound` and `Classical.choice`.
* `formalization.yaml` holds the metadata: sources, the automation and review account, fidelity
  notes and alignment.
* `.github/workflows/palomar-preflight.yml` runs Palomar's complete reusable verification
  workflow on every relevant push. It is pinned to one PalomarSubmission commit, and runs in mode
  `full` with profile `palomar-standard-v1`. A commit is submitted only if that run reports
  `status: pass`.

## What is claimed

Indexing: Mathlib's `(⊤ : Subgroup G).lowerCentralSeries k` is `γ_{k+1}(G)`.
`DSet n G = {g | g - 1 ∈ Δ(G)^n}` is the integral dimension subgroup `D_n(G)`.

### Unconditional

| Paper | Statement | Lean (`GroupDimension.Palomar.`) |
|---|---|---|
| Thm 6.6 | `G/γ₂` finite of exponent 3 ⇒ `D₅(G) = γ₅(G)` | `D_five_eq_gamma_five_of_exp_three` |
| Thm 6.8 | `G/γ₂` a finite 3-group whose cubes form a cyclic group ⇒ `D₅(G) = γ₅(G)` | `D_five_eq_gamma_five_of_cubes_cyclic` |
| Jennings, case used in §5 | finite 2-group of class ≤ 3 ⇒ `D₅(G) ⊆ M₅(G) = ∏_{i2^j≥5} γ_i^{2^j}` | `D_five_le_jennings` |
| Lemma 5.6 | no candidate of order `2^11` with `Q/P₃ ≅ ℤ/4 × (ℤ/2)^7` | `not_isCandidate_of_quotient_z4` |
| Prop 5.7, part | every candidate has `\|P₂(Q)\| ≥ 16` | `false_of_card_expCentral_two_le` |
| Prop 5.7, candidate form | no candidate of order `2^11` and rank `≥ 8` | `not_isCandidate_of_rank` |

### Conditional (hypotheses are explicit arguments, not axioms)

| Paper | Hypotheses | Lean |
|---|---|---|
| Prop 2.1 (1) ⇔ (3) | `D₃ = γ₃`, Passi's `D₄² ⊆ γ₄`, Gruenberg's theorem; "metabelian" dropped (Remark 2.2 not formalized) | `dimensionQuestion5_iff_class_three` |
| Lemma 5.2 (a)–(c) | `D₃ = γ₃` | `isCandidate_of_minimal` |
| Prop 5.7, `D₅` form | `D₃ = γ₃`; Prop 5.3 at order `2^10`, which the paper proves by computer | `D_five_eq_bot_of_rank` |

### Caveats

* Kourovka Problem 20.84 (`D₅ ⊆ γ₄` for all groups) is open. It appears only as one side of an
  equivalence.
* A *candidate* (`IsCandidate`) uses `M₅` defined by Jennings' product formula. The paper defines
  it as `G ∩ (1 + Δ_{𝔽₂}(G)^5)`. The two agree by Jennings' theorem, which is formalized only in the
  needed direction for `D₅` (`D_five_le_jennings`).
* Lemma 5.6 states the isomorphism as a surjective homomorphism with kernel `P₃(Q)`.
* Because the formalized inclusion is `G ∩ (1 + Δ_{𝔽₂}(G)^5) ⊆ jennings 2 G 5` (class ≤ 3), the
  non-existence results for candidates are at least as strong as the paper's. Lemma 5.2 (b),
  in contrast, gives `n ∈ M₅` only in the product sense.
* The paper's computer results (Props 5.1, 5.3, 5.10, Thms 5.4, 6.14) and its paper-only results
  (Lemmas 6.1, 6.2, 6.9, Thm 6.12) are not submitted. Proposition 5.8, Lemma 5.9,
  Lemma 6.3, Proposition 6.5, Theorem 6.10 (for central extensions by a subgroup of exponent
  `p`) and the inclusion part of Tahara's Theorem 6.1 are formalized in the development but are
  not compared statements.
