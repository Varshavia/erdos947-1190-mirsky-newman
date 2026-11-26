module

public import MirskyNewman.Bridge
public import MirskyNewman.Core
public import MirskyNewman.Counting
public import MirskyNewman.Defs

/-!
# Mirsky–Newman

Root module of the proof development. Planned modules:

* `MirskyNewman.Defs`: the FC covering-system definitions (byte-identical to `Challenge.lean`).
* `MirskyNewman.Core`: the finite roots-of-unity Mirsky–Newman lemma.
* `MirskyNewman.Bridge`: from `StrictCoveringSystem ℤ` to residue classes; proves `erdos_947`.
* `MirskyNewman.Counting`: the counting argument; proves `erdos_1190.variants.lt_one`.
-/
