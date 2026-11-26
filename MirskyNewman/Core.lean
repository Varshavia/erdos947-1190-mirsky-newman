module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The finite Mirsky–Newman lemma

Residue classes `r i mod n i` (`i ∈ s`) with pairwise distinct moduli `n i ≥ 2`,
pairwise disjoint, cannot cover the window `{0, …, N - 1}` when every `n i`
divides `N > 0`.

Proof (Step C): take `ζ` a primitive `m`-th root of unity for the largest
modulus `m`. Summing `ζ ^ x` over the window gives `0`. Summed class by class,
every class with `n i < m` contributes `0`, and the unique class with
`n i = m` contributes `ζ ^ c * (N / m) ≠ 0`.

`sum_filter_modEq_range` is the reindexing of one residue class inside the
window. The core proof uses it with `f x = ζ ^ x`, and the `lt_one` counting
step (Step E) uses its corollary `card_filter_modEq_range`.
-/

public section

open Finset

namespace MirskyNewman

/-- Reindexing of one residue class inside `range N`: the `x < N` with `x ≡ r [ZMOD n]`
are exactly `c + n * j` for `j < N / n`, where `c = (r % n).toNat`. -/
theorem sum_filter_modEq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {N n : ℕ} (hn : 0 < n) (hnN : n ∣ N) (r : ℤ) :
    ∑ x ∈ (range N).filter (fun x : ℕ => (x : ℤ) ≡ r [ZMOD n]), f x =
      ∑ j ∈ range (N / n), f ((r % n).toNat + n * j) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hc0 : (0 : ℤ) ≤ r % n := Int.emod_nonneg r hn'.ne'
  have hcn' : r % n < n := Int.emod_lt_of_pos r hn'
  have hcz : ((r % n).toNat : ℤ) = r % n := Int.toNat_of_nonneg hc0
  have hcn : (r % n).toNat < n := by omega
  symm
  apply Finset.sum_nbij' (fun j => (r % n).toNat + n * j) (fun x => x / n)
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    refine ⟨?_, ?_⟩
    · obtain ⟨k, rfl⟩ := hnN
      rw [Nat.mul_div_cancel_left _ hn] at hj
      nlinarith
    · unfold Int.ModEq
      push_cast
      rw [Int.add_mul_emod_self_left, hcz, Int.emod_emod_of_dvd _ dvd_rfl]
  · intro x hx
    simp only [mem_filter, mem_range] at hx ⊢
    exact Nat.div_lt_div_of_lt_of_dvd hnN hx.1
  · intro j _
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hcn, zero_add]
  · intro x hx
    simp only [mem_filter, mem_range] at hx
    have hmod : (x : ℤ) % n = r % n := hx.2
    have hxn : x % n = (r % n).toNat := by
      have : ((x % n : ℕ) : ℤ) = (x : ℤ) % n := Int.natCast_mod x n
      omega
    rw [← hxn, Nat.mod_add_div]
  · intro j _
    rfl

/-- A residue class mod `n` contains exactly `N / n` elements of `range N` when `n ∣ N`. -/
theorem card_filter_modEq_range {N n : ℕ} (hn : 0 < n) (hnN : n ∣ N) (r : ℤ) :
    #((range N).filter (fun x : ℕ => (x : ℤ) ≡ r [ZMOD n])) = N / n := by
  rw [card_eq_sum_ones, sum_filter_modEq_range (fun _ => 1) hn hnN r, sum_const, card_range,
    smul_eq_mul, mul_one]

/-- **Finite Mirsky–Newman lemma.** Pairwise disjoint residue classes with pairwise
distinct moduli `≥ 2` do not cover `range N` when every modulus divides `N > 0`. -/
theorem core {ι : Type*} (s : Finset ι) (n : ι → ℕ) (r : ι → ℤ)
    (hn : ∀ i ∈ s, 2 ≤ n i) (hinj : Set.InjOn n s)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ ∃ x : ℤ, x ≡ r i [ZMOD n i] ∧ x ≡ r j [ZMOD n j])
    {N : ℕ} (hN : 0 < N) (hnN : ∀ i ∈ s, n i ∣ N)
    (hcover : ∀ x < N, ∃ i ∈ s, (x : ℤ) ≡ r i [ZMOD n i]) :
    False := by
  classical
  -- `s` is nonempty since `0 < N` is covered; pick `i₀` with the largest modulus.
  obtain ⟨i₁, hi₁, -⟩ := hcover 0 hN
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image n ⟨i₁, hi₁⟩
  have hm2 : 2 ≤ n i₀ := hn i₀ hi₀
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n i₀ : ℂ)) with hζdef
  have hζ : IsPrimitiveRoot ζ (n i₀) := Complex.isPrimitiveRoot_exp (n i₀) (by omega)
  have hζN : ζ ^ N = 1 := (hζ.pow_eq_one_iff_dvd N).mpr (hnN i₀ hi₀)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have geom0 : ∀ {y : ℂ} {k : ℕ}, y ≠ 1 → y ^ k = 1 → ∑ j ∈ range k, y ^ j = 0 := by
    intro y k hy hyk
    rw [geom_sum_eq hy, hyk, sub_self, zero_div]
  -- The classes partition the window.
  let t : ι → Finset ℕ := fun i => (range N).filter (fun x : ℕ => (x : ℤ) ≡ r i [ZMOD n i])
  have hunion : s.biUnion t = range N := by
    ext x
    simp only [t, mem_biUnion, mem_filter, mem_range]
    constructor
    · rintro ⟨i, -, hx, -⟩
      exact hx
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hcover x hx
      exact ⟨i, hi, hx, hxi⟩
  have hpd : (s : Set ι).PairwiseDisjoint t := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    simp only [t, mem_filter] at hxi hxj
    exact hdisj i hi j hj hij ⟨x, hxi.2, hxj.2⟩
  -- Each class sum is a geometric sum.
  have hclass : ∀ i ∈ s, ∑ x ∈ t i, ζ ^ x =
      ζ ^ (r i % n i).toNat * ∑ j ∈ range (N / n i), (ζ ^ n i) ^ j := by
    intro i hi
    have := hn i hi
    rw [sum_filter_modEq_range (fun x => ζ ^ x) (by omega) (hnN i hi), mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_mul]
  have htotal : ∑ x ∈ range N, ζ ^ x = 0 := geom0 hζ1 hζN
  rw [← hunion, sum_biUnion hpd, sum_eq_single i₀] at htotal
  · -- Only the class with the largest modulus survives, and it contributes `ζ ^ c * (N / m) ≠ 0`.
    have hNm : 0 < N / n i₀ := Nat.div_pos (Nat.le_of_dvd hN (hnN i₀ hi₀)) (by omega)
    rw [hclass i₀ hi₀, hζ.pow_eq_one] at htotal
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at htotal
    exact mul_ne_zero (pow_ne_zero _ hζ0) (Nat.cast_ne_zero.mpr hNm.ne') htotal
  · -- Classes with a smaller modulus `n i < m` contribute `0`.
    intro i hi hne
    have := hn i hi
    have hlt : n i < n i₀ := lt_of_le_of_ne (hmax i hi) (fun h => hne (hinj hi hi₀ h))
    rw [hclass i hi, geom0 (hζ.pow_ne_one_of_pos_of_lt (by omega) hlt), mul_zero]
    rw [← pow_mul, Nat.mul_div_cancel' (hnN i hi), hζN]
  · intro h
    exact absurd hi₀ h

end MirskyNewman
