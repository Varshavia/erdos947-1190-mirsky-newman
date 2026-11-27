# Mirsky–Newman: no exact covering system with distinct moduli

[![CI](https://github.com/Varshavia/erdos947-1190-mirsky-newman/actions/workflows/ci.yml/badge.svg)](https://github.com/Varshavia/erdos947-1190-mirsky-newman/actions/workflows/ci.yml)

This repository is a Lean 4 and Mathlib proof of two statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(FC). Both are stated word for word as in FC at commit
[`ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`](https://github.com/google-deepmind/formal-conjectures/tree/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8).
It is prepared as a [Palomar](https://palomar-registry.org/) submission.

**Palomar entry:** _not yet registered. The link will go here once the
entry exists._

## What is proved

| Lean declaration | Statement |
| --- | --- |
| `Erdos947.erdos_947` | No finite family of residue classes `a_i mod n_i`, with pairwise distinct moduli `n_i ≥ 2`, partitions `ℤ`. That is, no exact covering system with distinct moduli exists ([Erdős problem 947](https://www.erdosproblems.com/947)). This is the theorem of Mirsky and Newman, which Davenport and Rado also proved independently. |
| `Erdos1190.erdos_1190.variants.lt_one` | Let `m ≥ 1`, and let `S` be a finite set of integers, each `> m`. If residue classes `a_n mod n` (`n ∈ S`) are pairwise disjoint, then `∑_{n ∈ S} 1/n < 1` ([Erdős problem 1190](https://www.erdosproblems.com/1190)). |

In the first statement, a family of residue classes is FC's
`StrictCoveringSystem ℤ`, which covers `ℤ` with ideals as moduli that are
pairwise distinct and neither `⊥` nor `⊤`. "Partitions" means that the classes
are pairwise disjoint (`Pairwise (Disjoint on c.coset)`).

In the second statement, Erdős's `ε_m` is the supremum of such sums. The
bound on each single sum gives `ε_m ≤ 1`. It does not, by itself, give the
strict bound `ε_m < 1` for the supremum, and this repository does not claim
that.

Both theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
No `sorry` is left outside `Challenge.lean`.

## Proof idea

Both results come from one finite lemma, `MirskyNewman.core`. Let some residue
classes be pairwise disjoint, with pairwise distinct moduli `≥ 2`, and let
every modulus divide some `N > 0`. Then these classes cannot cover
`{0, …, N−1}`.

* To prove `core`, let `m` be the largest modulus and `ζ = e^{2πi/m}`. Then
  `∑_{x<N} ζ^x = 0`. Split this sum over the classes. A class with modulus
  `n < m` sums a geometric series in `ζ^n ≠ 1` over a full period, so it
  contributes `0`. The class with modulus `m` contributes `ζ^c · N/m ≠ 0`.
  This is a contradiction.
* For `erdos_947`, take `N` to be the product of the moduli. An exact cover of
  `ℤ` would cover `{0, …, N−1}`.
* For `lt_one`, take `N = ∏_{n∈S} n`. The disjoint classes have `N/n` elements
  each in `{0, …, N−1}`, so `∑ 1/n ≤ 1`. Equality would mean that the classes
  cover `{0, …, N−1}`, which `core` rules out.

## File layout

- `Challenge.lean` is the statement surface to audit. It contains FC's
  `CoveringSystem`, `StrictCoveringSystem` and `CoveringSystem.coset`, and the
  two theorems with `sorry`, all copied verbatim between `-- BEGIN FC` and
  `-- END FC` markers.
- `Solution.lean` restates the two theorems and proves them from the library.
- `MirskyNewman/Defs.lean` holds the FC definitions, byte-identical to the
  Challenge block.
- `MirskyNewman/Core.lean` holds `core`, the finite roots-of-unity lemma, and
  the lemmas for counting and summing over residue classes in
  `{0, …, N−1}`.
- `MirskyNewman/Bridge.lean` takes `StrictCoveringSystem ℤ` to integer moduli
  `≥ 2` and proves `MirskyNewman.erdos_947`.
- `MirskyNewman/Counting.lean` contains the counting argument and proves
  `MirskyNewman.erdos_1190_lt_one`.
- `comparator.json` lists both theorems for `lake comparator`.
- `formalization.yaml` records the Palomar metadata: sources, provenance,
  automation and review.
- `scripts/check_fc_fidelity.py` diffs the Challenge text against FC at the
  pinned commit. `scripts/verify-comparator.sh` runs the toolchain's
  `lake comparator`. `scripts/check-lean-sources.py` checks the module
  headers and file sizes.
- `docbuild/` is the nested doc-gen4 project.

## Build and check

The toolchain is `leanprover/lean4:v4.35.0-rc2` and Mathlib is pinned in
`lake-manifest.json`. The Mathlib cache and build take several GiB under
`.lake/`.

```text
lake exe cache get
lake build
```

To check axioms, put this in a scratch file and run it with
`lake env lean <file>`:

```lean
import Solution
#print axioms Erdos947.erdos_947
#print axioms Erdos1190.erdos_1190.variants.lt_one
```

Each line should report `[propext, Classical.choice, Quot.sound]`.

Further checks:

```text
python3 scripts/check-lean-sources.py
python3 scripts/check_fc_fidelity.py --fc-repo <path to a formal-conjectures clone>
(cd docbuild && lake build MirskyNewman:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

`verify-comparator.sh` needs Linux with `bwrap` (bubblewrap). The Ruby
validator needs Ruby. GitHub Actions runs all of these checks on every push,
except the doc build. That one runs out of memory on the standard runner, so it
runs only when started by hand (`workflow_dispatch`). Palomar does not require
API documentation.

## Provenance and licence

- The statements and definitions in `Challenge.lean` and
  `MirskyNewman/Defs.lean` are copied from FC at the pinned commit. FC is
  Copyright 2025–2026 The Formal Conjectures Authors and is released under the
  Apache License 2.0. Only FC-only metadata is removed: the `@[category …]`
  attributes, the `formal_proof_palomar` linter option, and the unused lemma
  `CoveringSystem.iUnion_cosets`.
- The mathematics follows the Mirsky–Newman argument, first published in
  Erdős, *On integers of the form 2^k + p and some related problems*, Summa
  Brasil. Math. (1950). The ε_m remark is from Erdős, *A survey of problems in
  combinatorial number theory*, Ann. Discrete Math. (1980). See
  `formalization.yaml` for all sources.
- Related work: FC links an earlier, unlicensed Lean proof of `erdos_947` in
  [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos947.lean#L277).
  Palomar entry
  [PALOMAR-2026-10-02-000004](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-02-000004)
  proves Herzog–Schönheim for solvable groups, which implies the content of
  947 for `ℤ`. No code from either is used here. FC links no formal proof for
  `lt_one`.
- Claude Code (Claude Opus 5.5, `claude-opus-5-5`) wrote the Lean proofs. The
  human author, Yusuf Suat Babacan, chose the targets, approved the core lemma
  statements, and reviewed the Challenge fidelity to FC.
- This repository is released under the Apache License 2.0 (`LICENSE`). Cited
  papers and dependencies keep their own licences.

Palomar submissions go through the
[submission form](https://submit.palomar-registry.org/), which takes the full
40-character commit SHA. See the
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
