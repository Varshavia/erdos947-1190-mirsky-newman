module

public import MirskyNewman

/-!
# Proved solution

Restates the two compared declarations of `Challenge.lean`. The covering-system
constants come from `MirskyNewman.Defs`, which is byte-identical to the
Challenge definitions. Comparator checks that each declaration here has exactly
the type of its Challenge counterpart and uses only the permitted axioms.

Skeleton stage (Step B): both proofs are still `sorry`. Step D supplies
`erdos_947` from `MirskyNewman.Bridge`, and Step E supplies `lt_one` from
`MirskyNewman.Counting`.
-/

@[expose] public section

open Function

namespace Erdos947

theorem erdos_947 : ¬ ∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset) := by
  sorry

end Erdos947

namespace Erdos1190

theorem erdos_1190.variants.lt_one (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  sorry

end Erdos1190
