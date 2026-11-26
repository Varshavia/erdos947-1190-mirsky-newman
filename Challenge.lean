module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq

/-!
# Mirsky–Newman: no exact covering system with distinct moduli

This file is the statement surface of the submission. It states two results
from google-deepmind/formal-conjectures (FC) at commit
`ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`, word for word:

* `Erdos947.erdos_947` (`FormalConjectures/ErdosProblems/947.lean`). No finite
  family of residue classes `a_i mod n_i` with pairwise distinct moduli
  `n_i ≥ 2` partitions `ℤ`. This is the Mirsky–Newman theorem, also proved
  independently by Davenport and Rado.
* `Erdos1190.erdos_1190.variants.lt_one`
  (`FormalConjectures/ErdosProblems/1190.lean`). If residue classes
  `a_n mod n`, for `n` in a finite set `S` of integers all `> m ≥ 1`, are
  pairwise disjoint, then `∑_{n ∈ S} 1/n < 1`.

## Encoding of covering systems

The structures `CoveringSystem` and `StrictCoveringSystem` and the function
`CoveringSystem.coset` are copied verbatim from FC's
`FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean` at the same
commit (Copyright 2025 The Formal Conjectures Authors, Apache License 2.0).
The FC lemma `CoveringSystem.iUnion_cosets`, which no statement here uses, is
omitted. For `R = ℤ`, every ideal is `nℤ` for a unique `n : ℕ`, and:

* `ne_bot` means `n ≠ 0` and `ne_top` means `n ≠ 1`, so every modulus is `≥ 2`;
* `injective_moduli` means that distinct indices have distinct moduli;
* `c.coset i = {c.residue i} + c.moduli i` is the residue class
  `residue i mod n_i`;
* `unionCovers` says that every integer lies in some class, and
  `Pairwise (Disjoint on c.coset)` says that no integer lies in two classes.

So `∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset)` says exactly
that an exact covering system of `ℤ` with distinct moduli exists. The trivial
cover `{0 mod 1}` is excluded by `ne_top`.

## Differences from the FC source

The only text removed from the FC declarations is FC-specific metadata that
does not affect the statements: the `@[category …, AMS …, formal_proof …]`
attributes and the line `set_option linter.style.formal_proof_palomar false
in`. FC's `open Filter Real` and `open scoped Topology` in `1190.lean` are also
left out, because the `lt_one` statement uses none of their names. FC's other
declarations in that file (`eps` and the remaining variants) are not part of
this submission. `scripts/check_fc_fidelity.py` checks all of this
mechanically against the pinned FC commit.
-/

@[expose] public section

-- BEGIN FC: CoveringSystem definitions
open Pointwise

/--
A covering system of a semiring `R` is a finite set of cosets of non-zero ideals whose union
covers the whole ring. In the case where `R = ℤ`, this corresponds to a choice of finitely many
congruence relations such that every integer satisfies at least one of the relations.
-/
structure CoveringSystem (R : Type*) [CommSemiring R] where
  ι : Type
  [fintypeIndex : Fintype ι]
  residue : ι → R
  moduli : ι → Ideal R
  unionCovers : ⋃ i, ({residue i} : Set R) + (moduli i : Set R) = @Set.univ R
  ne_bot : ∀ i, moduli i ≠ ⊥
  ne_top : ∀ i, moduli i ≠ ⊤

/--
We say a covering system is strict if all the congruence relations that define it are take modulo
a different ideal (or number).

Note: this corresponds to the notion of a covering system that Erdos was using in
[ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number theory. Monographies de L'Enseignement Mathematique (1980).
-/
structure StrictCoveringSystem (R : Type*) [CommSemiring R] extends CoveringSystem R where
  injective_moduli : moduli.Injective

namespace CoveringSystem

variable {R : Type*} [CommSemiring R]

def coset (c : CoveringSystem R) (i : c.ι) : Set R :=
  {c.residue i} + c.moduli i

end CoveringSystem
-- END FC: CoveringSystem definitions

-- BEGIN FC: Erdos947
open Function

namespace Erdos947

/--
There is no exact covering system - that is, a finite collection of congruence classes
$a_i\pmod{n_i}$ with distinct $n_i$ such that every integer satisfies exactly one of these
congruence classes.

This is true, and was proved independently by Mirsky and Newman and by Davenport and Rado; the
Mirsky–Newman proof first appeared in [Er50]. See also [Er77c].

A `StrictCoveringSystem ℤ` is a finite family of congruence classes with distinct moduli
$n_i \geq 2$ covering $\mathbb{Z}$; the trivial exact covering system consisting of the single
class $0 \pmod 1$ is therefore excluded.
-/
theorem erdos_947 : ¬ ∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset) := by
  sorry

end Erdos947
-- END FC: Erdos947

-- BEGIN FC: Erdos1190
namespace Erdos1190

/--
Erdős [Er80] seems to credit Mirsky and Newman with the result that $\epsilon_m<1$, but gives no
reference.
-/
theorem erdos_1190.variants.lt_one (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  sorry

end Erdos1190
-- END FC: Erdos1190
