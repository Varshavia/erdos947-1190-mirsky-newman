module

public import MirskyNewman

/-!
# Proved solution

Restates the two compared declarations of `Challenge.lean`. The covering-system
constants come from `MirskyNewman.Defs`, which is byte-identical to the
Challenge definitions. Comparator checks that each declaration here has exactly
the type of its Challenge counterpart and uses only the permitted axioms.

`erdos_947` is `MirskyNewman.erdos_947` from `MirskyNewman.Bridge` (Step D).
`lt_one` is `MirskyNewman.erdos_1190_lt_one` from `MirskyNewman.Counting` (Step E).
-/

@[expose] public section

open Function

namespace Erdos947

theorem erdos_947 : ¬ ∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset) :=
  MirskyNewman.erdos_947

end Erdos947

namespace Erdos1190

theorem erdos_1190.variants.lt_one (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 :=
  MirskyNewman.erdos_1190_lt_one m hm S a hS hdisj

end Erdos1190
