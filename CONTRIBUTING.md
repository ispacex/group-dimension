# Contributing

The library formalizes the paper *The $D_5$ problem* (<https://ispacex.github.io/d5>). Work on it
follows the process of the [Stacks project in Lean](https://github.com/AxiomMath/Stacks): blueprint,
claim, pull request, review.

## 1. Blueprint

Every labelled statement of the paper is a node of the blueprint, `site/blueprint.toml` in
[ispacex/dimension-subrings](https://github.com/ispacex/dimension-subrings) (where this package is
the submodule `groups/`). A node has a permanent tag `D5:XXXX` (four characters, digits and capital letters
without `I` and `O`; wiki 912 of the project's tracker), lists the Lean declarations that state or
prove the statement and says whether the proof is formalized; the pages are
[blueprint.html](https://ispacex.github.io/d5/blueprint.html) and the leanblueprint graph under
`blueprint/` of the site.

In the code, each such declaration carries the attribute `@[d5 <tag>]` with the tag of its node,
written without the prefix (`GroupDimension/D5Tag.lean`), e.g. for Theorem `thm:g4cube`, tag
`D5:000P`:

```lean
@[d5 000P]
theorem D_five_eq_gamma_five_of_g4_cube ...
```

with an optional comment, `@[d5 000P "part (a)"]`; a declaration may carry several tags,
`@[d5 002V, d5 0031]`. A label of the paper (`@[d5 "thm:g4cube"]`) is refused. `#d5_tags` lists all
of them, one JSON object per line (`lake env lean D5Tags.lean`). **The attribute is the source of
truth** for which declaration formalizes which statement (MATH-458): the `lean` fields of
`blueprint.toml` are written from `#d5_tags` by `python3 site/blueprint.py sync LOG`, and the CI of
dimension-subrings (`.github/workflows/blueprint.yml`) fails unless they are exactly the tagged
pairs. A new declaration for a node is tagged here; then, in dimension-subrings, `groups/` is
bumped and `sync` rewrites the `lean` fields, in one pull request. A statement that has no node yet
gets its node and tag there first (the tags are issued in the project D5 of the tracker).

## 2. Claim

Before starting, open an issue with the **Claim a statement to formalize** template: the paper
label, the statement, the Lean statement you will prove (with `sorry`), what it uses and a proof
outline. It gets the label `claim`; a maintainer adds `blueprint-approved` once the Lean statement
is agreed (it matches the paper, or the difference is stated). Work on statements without an
approved claim may be duplicated or declined. Small fixes (typos, golfing, documentation) need no
claim.

## 3. Pull request

One pull request per claim, referring to it (`Closes #N`). It must

* build with no `sorry` and pass the axiom audit of CI (`AxiomAudit.lean`: only `propext`,
  `Classical.choice`, `Quot.sound`; add the new declarations there);
* tag the declarations that formalize the statement with `@[d5 <tag>]`, the tag of its node;
* say, in the module docstring, which statement of the paper it is and how the Lean version
  differs.

## 4. Review

Every change is reviewed before it is merged by someone other than its author, checking the Lean
statement against the paper and the cited sources, not only that it compiles. So far all reviews
have been by independent AI agents (see `review` in `formalization.yaml`).

## AI-written code: Frontier and Core

All Lean code of this repository so far was written by AI agents under the direction of the
author, who did not review the proofs line by line (`automation` in `formalization.yaml`). Claude
Code agents wrote all of it, with one exception (and the reuse noted below): for the theorem on
$Q/\gamma_2(Q)\cong C_3\times C_9\times C_9$ (2026-11-12), the proofs in `GroupDimension/Star.lean`,
`GroupDimension/Star/`, `Ab399.lean` and `Ab399Finite.lean` were written by Kimi K3.1 Pro agents
(through Open Math OS) against statements and a skeleton fixed by a Claude Code agent, and later
edited in review by Claude Code agents.
`ThirdInvariant.lean` and `ThirdInvariantFinite.lean` (Theorems 12.6 and 11.2 of the notes,
2026-11-13) were written by Claude Code, but about half of their lines (helper lemmas and the
finite reduction) are carried over, verbatim or nearly so, from the Kimi-written `Ab399.lean` and
`Ab399Finite.lean`, and their proof rests on the Kimi-written identity in `Star/`. A Kimi K3.1 Pro
agent run on their skeleton was not used.
In the terms of the Stacks project, the whole library is therefore **Frontier**: checked by the Lean
kernel and the axiom audit, reviewed by agents, but not by human experts. There is no **Core**
(human-reviewed) part yet; a statement moves to Core only after a human review of its Lean
statement against the paper, recorded in `formalization.yaml`. Say in the claim and in the pull
request whether the code is AI-written.
