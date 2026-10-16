Русская версия: [README.ru.md](README.ru.md).

# groups — dimension subgroups of groups in Lean

The statement of Problem 20.84 of the Kourovka notebook — **is $D_5(G) \subseteq \gamma_4(G)$ for
every group $G$?** — in Lean 4 / Mathlib, with the basic facts fully proved and a comparison with
the Lie ring case, which is proved and formalized in [IMP26] (arXiv:2610.02042, repository
<https://github.com/TimmPeterson/lie-algebras>).

Lean `v4.29.0`, Mathlib `v4.29.0` (rev `8a17838`), the same version as the authors'. The authors'
package `lie-rings` is pulled in by `require` at the audited commit `ed3d9fb` (the same as in the
submodule `upstream/lie-algebras`); only `LieComparison.lean` needs it.

## Definitions (`GroupDimension/Basic.lean`)

| In the paper | In Lean |
|---|---|
| $\mathbb Z[G]$ | `MonoidAlgebra ℤ G` |
| $\varepsilon\colon \mathbb Z[G]\to\mathbb Z$, $g\mapsto 1$ | `augmentation G := (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom` |
| $\Delta(G)=\ker\varepsilon$ | `augIdeal G := RingHom.ker (augmentation G)` — an `Ideal`, with an `IsTwoSided` instance |
| $D_n(G)=\{g \mid g-1\in\Delta^n\}$ | `D n G : Subgroup G`, `mem_D` — by definition (`Iff.rfl`) |
| $\gamma_n(G)$, $\gamma_1=G$ | Mathlib `lowerCentralSeries G (n-1)` |

**Numbering of the lower central series.** In Mathlib (`Mathlib/GroupTheory/Nilpotent.lean`)
`lowerCentralSeries G 0 = ⊤`, `lowerCentralSeries G (k+1) = ⁅lowerCentralSeries G k, ⊤⁆`,
so **`lowerCentralSeries G k` = $\gamma_{k+1}(G)$**: $\gamma_2$ = `lowerCentralSeries G 1`
(= `commutator G`, `lowerCentralSeries_one`), $\gamma_4$ = `lowerCentralSeries G 3`. The numbering
of `D n G` follows the literature, with no shift ($D_0 = D_1 = G$).

**Commutator.** In Mathlib `⁅a, b⁆ = a b a⁻¹ b⁻¹`. The identity in $\mathbb Z[G]$:
$[a,b]-1 = \bigl((a-1)(b-1)-(b-1)(a-1)\bigr)\,a^{-1}b^{-1}$. For the paper's convention
$[a,b]=a^{-1}b^{-1}ab$ — $[a,b]-1 = a^{-1}b^{-1}\bigl((a-1)(b-1)-(b-1)(a-1)\bigr)$, as in the
statement of the problem. Both identities are proved (`of_commutator_sub_one`,
`of_inv_mul_inv_mul_mul_sub_one`).

## Proved in Lean (0 `sorry`)

| Statement | Declaration | File |
|---|---|---|
| $D_n(G)$ is a normal subgroup | `D_normal` (instance) | `Basic.lean` |
| $D_0(G) = D_1(G) = G$ | `D_zero`, `D_one` | `Basic.lean` |
| $D_n$ is decreasing | `D_antitone` | `Basic.lean` |
| $\Delta^i\Delta^j \subseteq \Delta^{i+j}$ | `mul_mem_augIdeal_pow` | `Basic.lean` |
| both commutator identities | `of_commutator_sub_one`, `of_inv_mul_inv_mul_mul_sub_one` | `LowerCentral.lean` |
| $[D_i, D_j] \subseteq D_{i+j}$ | `commutator_mem_D`, `commutator_D_le` | `LowerCentral.lean` |
| $\gamma_n(G) \subseteq D_n(G)$, $n \ge 1$ | `lowerCentralSeries_le_D` (`lcs k ≤ D (k+1)`), `gamma_le_D` (`lcs (n-1) ≤ D n`) | `LowerCentral.lean` |
| functoriality $f(D_n(G)) \subseteq D_n(H)$ | `map_mem_D`, `map_D_le`, `D_le_comap` | `LowerCentral.lean` |
| $D_2(G) = \gamma_2(G)$ (in full, both inclusions) | `D_two`, `D_two_le_commutator` | `DTwo.lean` |
| for a surjection $\gamma_k(H) \subseteq f(\gamma_k(G))$; $\gamma_k(G/\gamma_k G)=1$ | `lowerCentralSeries_le_map_of_surjective`, `lowerCentralSeries_quotient_eq_bot` | `Reduction.lean` |
| $D_n(G/N)=1 \Rightarrow D_n(G)\subseteq N$ | `D_le_of_D_quotient_eq_bot` | `Reduction.lean` |
| **reduction**: the question $D_5\subseteq\gamma_4$ ⇔ $D_5(Q)=1$ for all $Q$ of class $\le 3$ | `forall_D_le_iff`, `dimensionQuestion5_iff` | `Reduction.lean` |
| Lie $D_5(L)\subseteq\gamma_4(L)$ (from the authors' `corollaryD`) | `LieComparison.lieDimensionQuestion5` | `LieComparison.lean` |

$D_2 = \gamma_2$ is proved via the trivial square-zero extension $T=\mathbb Z\oplus G_{ab}$
(`TrivSqZeroExt`): $g\mapsto(1,\bar g)$ extends to a ring map $\Phi\colon\mathbb Z[G]\to T$ whose
first coordinate is $\varepsilon$, so $\Phi(\Delta^2)=0$ and $\Phi(g-1)=(0,\bar g)$. This is the
same idea as the authors' `DegreeTwo.lean` (a square-zero representation).

`#print axioms` for all 23 proved declarations (`AxiomAudit.lean`) — only `propext`,
`Classical.choice`, `Quot.sound`. No `sorry` and no `axiom` in the sources.

## Only stated (`def … : Prop`, no proof and no assumption)

These are **statements, not proofs**: none is declared as an `axiom`, and none is assumed
anywhere. References are in the docstrings; data marked † have not been checked against the
original.

| `Prop` | Content | Literature |
|---|---|---|
| `DimensionQuestion5` | $\forall G,\ D_5(G)\subseteq\gamma_4(G)$ — **open question** | Kourovka notebook 20.84 [KM26]; [IMP26, §1.3] |
| `DThreeEqGammaThree` | $D_3=\gamma_3$ | Higman, Rees (unpubl.), Passi [Pas68]†; [Pas79], [MP09] |
| `PassiDFourSquare` | $g\in D_4 \Rightarrow g^2\in\gamma_4$ | Passi [Pas68]† |
| `RipsExample` | $\exists G,\ D_4(G)\ne\gamma_4(G)$ | Rips [Rip72] |
| `TaharaDFiveExponentSix` | $g\in D_5 \Rightarrow g^6\in\gamma_5$ | Tahara [Tah81]†; [MP09] |
| `GuptaKuzminAbelian` | $[D_n,D_n]\subseteq\gamma_{n+1}$ | [GK92], quoted from [IMP26, §1.2] |
| `GuptaKuzminDFourCentral` | $[D_4,G]=\gamma_5$ | [GK92], quoted from [IMP26, §1.2] |
| `LieComparison.FifthDimensionSquare` | $g\in D_5 \Rightarrow g^2\in G''\gamma_5$ | [MP09, Thm 2.28], quoted from [IMP26, §3.3] |
| `LieComparison.GroupCorollaryD c` | $D_{2c-1}\subseteq\gamma_{c+1}G''$ — group analogue of Corollary D | status for $c\ge4$ unknown to us |
| `LieComparison.GroupTheoremC c` | metabelian of class $\le c$ ⇒ $D_{2c-1}=1$ | analogue of Theorem C, no claim of truth |

## Comparison with Lie rings (`LieComparison.lean`)

The file imports `LieRings.Publication.Results`, puts the Lie and the group statements side by side
(`LieDimensionQuestion5` — proved from `corollaryD`; `DimensionQuestion5` — open) and discusses
in a comment which steps of §§5–6 of the paper carry over. In short:

* **carry over**: passing to a quotient (Corollary 6.14; for groups proved here —
  `dimensionQuestion5_iff`), reduction to finitely generated (Lemma 6.13), the construction of the
  central extension $T = G\times_{G_{ab}}P$ (but $T'\to T\to P$ splits as a semidirect, not a
  direct product);
* **no direct analogue**: the PBW filtrations $P_{\le r}U(T)$ with $\mathrm{gr}\cong\mathrm{Sym}$
  and the basis of ordered monomials (Thm 2.3, Cor 2.4); the additive retractions
  $p\colon U(T)\to P_{\le2}U(T)$ and $r\colon P_{\le2}U(T)\to T$ (Thm 5.1, Lemma 5.3), which rest
  on $T\subset U(T)$ being an additive subgroup: for groups the embedding $g\mapsto g-1$ is
  additive only modulo $\Delta^2$; the explicit $\mathbb Z$-description of $\Delta(T)^n$ on which
  the retraction $p$ is built (Prop. 6.12).

## Build

```bash
cd groups
lake exe cache get          # Mathlib from the cache
lake build                  # GroupDimension + the needed part of lie-rings
lake env lean AxiomAudit.lean
```

From scratch, besides Mathlib from the cache, the authors' package is built — about 4 min on 16
cores (see the audit, [`../notes/formalization-audit.md`](../notes/formalization-audit.md)).

## Literature

* [IMP26] V. Ionin, R. Mikhailov, T. Petrov, *Dimension subrings of Lie rings*, arXiv:2610.02042.
* [KM26] *The Kourovka notebook*, 21st ed., arXiv:1401.0300v46, Problem 20.84.
* [Rip72] E. Rips, Israel J. Math. 12 (1972), 342–346.
* [GK92] N. Gupta, Yu. V. Kuz'min, J. Pure Appl. Algebra 78 (1992), 165–172.
* [Pas79] I. B. S. Passi, *Group rings and their augmentation ideals*, LNM 715, 1979.
* [MP09] R. Mikhailov, I. B. S. Passi, *Lower central and dimension series of groups*, LNM 1952, 2009.
* [Pas68]† I. B. S. Passi, *Dimension subgroups*, J. Algebra 9 (1968), 152–182.
* [Tah81]† K.-I. Tahara, J. Algebra 71 (1981), 141–173.
* Quillen 1968† — D. Quillen, *On the associated graded ring of a group ring*, J. Algebra 10 (1968).
