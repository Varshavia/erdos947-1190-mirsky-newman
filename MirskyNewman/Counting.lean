module

public import MirskyNewman.Core
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Field

/-!
# The counting argument for `erdos_1190.variants.lt_one`

Let `N = ∏ n ∈ S, n`. For `n ∈ S` the class `A n` of `x < N` with `x ≡ a n [ZMOD n]`
has `N / n` elements (`card_filter_modEq_range`), and the classes are pairwise
disjoint by `hdisj`. Hence `∑ n ∈ S, N / n ≤ N`, that is, `∑ n ∈ S, 1 / n ≤ 1`.
If equality held, the classes would fill `{0, …, N - 1}`, and `MirskyNewman.core`
(with `s = S`, `n = id`, `r = a`) gives a contradiction. So the sum is `< 1`.
-/

public section

open Finset

namespace MirskyNewman

/-- `N * n⁻¹` is the natural number `N / n` when `n ∣ N` and `n ≠ 0`. -/
theorem natCast_mul_inv_eq_div {N n : ℕ} (hn : 0 < n) (hnN : n ∣ N) :
    (N : ℝ) * (n : ℝ)⁻¹ = ((N / n : ℕ) : ℝ) := by
  rw [Nat.cast_div hnN (by exact_mod_cast hn.ne'), div_eq_mul_inv]

/-- **Erdős 1190, `lt_one` variant.** This is the statement of
`Erdos1190.erdos_1190.variants.lt_one`, which `Solution.lean` derives from it. -/
theorem erdos_1190_lt_one (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  classical
  set N : ℕ := ∏ n ∈ S, n with hN_def
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by have := hS n hn; omega
  have hN : 0 < N := prod_pos hpos
  have hdvd : ∀ n ∈ S, n ∣ N := fun n hn => dvd_prod_of_mem _ hn
  -- The residue classes inside the window `range N`.
  let t : ℕ → Finset ℕ := fun n => (range N).filter (fun x : ℕ => (x : ℤ) ≡ a n [ZMOD n])
  have hpd : (S : Set ℕ).PairwiseDisjoint t := by
    intro n hn n' hn' hne
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    simp only [t, mem_filter] at hx hx'
    exact hdisj n hn n' hn' hne ⟨x, hx.2, hx'.2⟩
  have hsub : S.biUnion t ⊆ range N := by
    intro x hx
    simp only [t, mem_biUnion, mem_filter] at hx
    obtain ⟨_, _, hx, _⟩ := hx
    exact hx
  have hcard : #(S.biUnion t) = ∑ n ∈ S, N / n := by
    rw [card_biUnion hpd]
    exact sum_congr rfl fun n hn => card_filter_modEq_range (hpos n hn) (hdvd n hn) _
  have hle : ∑ n ∈ S, N / n ≤ N := by
    rw [← hcard, ← card_range N]
    exact card_le_card hsub
  -- `N * ∑ 1 / n` is the natural number `∑ N / n`.
  have hsum : (N : ℝ) * ∑ n ∈ S, (n : ℝ)⁻¹ = ((∑ n ∈ S, N / n : ℕ) : ℝ) := by
    rw [mul_sum, Nat.cast_sum]
    exact sum_congr rfl fun n hn => natCast_mul_inv_eq_div (hpos n hn) (hdvd n hn)
  rcases hle.lt_or_eq with hlt | heq
  · have hlt' : (N : ℝ) * ∑ n ∈ S, (n : ℝ)⁻¹ < (N : ℝ) * 1 := by
      rw [hsum, mul_one]
      exact_mod_cast hlt
    exact lt_of_mul_lt_mul_left hlt' (Nat.cast_nonneg N)
  · -- Equality: the classes fill the window, which `core` rules out.
    exfalso
    have hfill : S.biUnion t = range N :=
      eq_of_subset_of_card_le hsub (by rw [card_range, hcard, heq])
    refine core S id a (fun n hn => by have := hS n hn; simp only [id]; omega)
      (Set.injOn_id _) hdisj hN hdvd ?_
    intro x hx
    have hx' : x ∈ S.biUnion t := hfill ▸ mem_range.mpr hx
    simp only [t, mem_biUnion, mem_filter] at hx'
    obtain ⟨n, hn, -, hxn⟩ := hx'
    exact ⟨n, hn, hxn⟩

end MirskyNewman
