module

public import MirskyNewman.Core
public import MirskyNewman.Defs
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic

/-!
# From strict covering systems of `ℤ` to residue classes

For `c : StrictCoveringSystem ℤ`, set `n i := (generator (c.moduli i)).natAbs`.
Then `c.moduli i = (n i)ℤ`, `2 ≤ n i` (from `ne_bot` and `ne_top`), the map `n`
is injective (from `injective_moduli`), and `x ∈ c.coset i` holds exactly when
`x ≡ c.residue i [ZMOD n i]`. If the cosets were pairwise disjoint, the classes
`c.residue i mod n i` would partition `ℤ`, so in particular they would cover
`{0, …, N - 1}` for `N = ∏ i, n i`. `MirskyNewman.core` rules this out.
-/

public section

open Function

namespace MirskyNewman

/-- The natural-number generator of an ideal of `ℤ`. -/
noncomputable def idealNat (I : Ideal ℤ) : ℕ :=
  (Submodule.IsPrincipal.generator I).natAbs

theorem span_idealNat (I : Ideal ℤ) : Ideal.span {((idealNat I : ℕ) : ℤ)} = I := by
  rw [idealNat, Int.natCast_natAbs, Ideal.span_singleton_abs,
    Ideal.span_singleton_generator]

theorem two_le_idealNat {I : Ideal ℤ} (hbot : I ≠ ⊥) (htop : I ≠ ⊤) : 2 ≤ idealNat I := by
  rw [← span_idealNat I] at hbot htop
  have h0 : idealNat I ≠ 0 := by
    rintro h
    exact hbot (by simp [h])
  have h1 : idealNat I ≠ 1 := by
    rintro h
    exact htop (by simp [h])
  omega

theorem mem_coset_iff (c : CoveringSystem ℤ) (i : c.ι) (x : ℤ) :
    x ∈ c.coset i ↔ x ≡ c.residue i [ZMOD idealNat (c.moduli i)] := by
  rw [CoveringSystem.coset, Set.singleton_add, Set.mem_image, Int.modEq_comm,
    Int.modEq_iff_dvd]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← span_idealNat (c.moduli i)] at hy
    simpa using Ideal.mem_span_singleton.mp hy
  · intro h
    refine ⟨x - c.residue i, ?_, by ring⟩
    rw [SetLike.mem_coe, ← span_idealNat (c.moduli i)]
    exact Ideal.mem_span_singleton.mpr h

/-- **Mirsky–Newman.** There is no exact covering system of `ℤ` with distinct moduli.
This is the statement of `Erdos947.erdos_947`, which `Solution.lean` derives from it. -/
theorem erdos_947 : ¬ ∃ c : StrictCoveringSystem ℤ, Pairwise (Disjoint on c.coset) := by
  classical
  rintro ⟨c, hc⟩
  let _ : Fintype c.ι := c.fintypeIndex
  set n : c.ι → ℕ := fun i => idealNat (c.moduli i) with hn_def
  have hn2 : ∀ i, 2 ≤ n i := fun i =>
    two_le_idealNat (c.ne_bot i) (c.ne_top i)
  have hmem : ∀ i x, x ∈ c.coset i ↔ x ≡ c.residue i [ZMOD n i] := fun i x =>
    mem_coset_iff c.toCoveringSystem i x
  refine core Finset.univ n c.residue (fun i _ => hn2 i) ?_ ?_
    (N := ∏ i, n i) ?_ (fun i _ => Finset.dvd_prod_of_mem n (Finset.mem_univ i)) ?_
  · intro i _ j _ hij
    apply c.injective_moduli
    rw [← span_idealNat (c.moduli i), ← span_idealNat (c.moduli j)]
    exact congrArg (fun k : ℕ => Ideal.span {(k : ℤ)}) hij
  · rintro i - j - hij ⟨x, hxi, hxj⟩
    exact Set.disjoint_left.mp (hc hij) ((hmem i x).mpr hxi) ((hmem j x).mpr hxj)
  · exact Finset.prod_pos fun i _ => by have := hn2 i; omega
  · intro x _
    have hx : (x : ℤ) ∈ ⋃ i, c.coset i := by
      simp only [CoveringSystem.coset]
      rw [c.unionCovers]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, Finset.mem_univ i, (hmem i x).mp hi⟩

end MirskyNewman
