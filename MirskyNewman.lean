module

public import MirskyNewman.Core
public import MirskyNewman.Defs
-- Supplies `∑`, `ℝ`, and `[ZMOD n]` for the `lt_one` statement until
-- `MirskyNewman.Counting` (Step E) imports them itself.
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq

/-!
# Mirsky–Newman

Root module of the proof development. Planned modules:

* `MirskyNewman.Defs`: the FC covering-system definitions (byte-identical to `Challenge.lean`).
* `MirskyNewman.Core`: the finite roots-of-unity Mirsky–Newman lemma.
* `MirskyNewman.Bridge`: from `StrictCoveringSystem ℤ` to residue classes; proves `erdos_947`.
* `MirskyNewman.Counting`: the counting argument; proves `erdos_1190.variants.lt_one`.
-/
