module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Covering-system definitions

The block between the `BEGIN FC` and `END FC` markers below is byte-for-byte
identical to the matching block in `Challenge.lean`. Comparator needs the
proof development to build its statements from the same constants as the
Challenge; `scripts/check_fc_fidelity.py` checks that the two blocks are
identical.

The definitions are copied verbatim from google-deepmind/formal-conjectures,
`FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`, at commit
`ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8` (Copyright 2025 The Formal
Conjectures Authors, Apache License 2.0).
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
