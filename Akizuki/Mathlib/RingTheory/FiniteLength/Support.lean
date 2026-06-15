/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Support
public import Akizuki.Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Akizuki.Mathlib.RingTheory.KrullDimension.Basic
public import Akizuki.Mathlib.RingTheory.QuotientAnnihilator

/-!
# Finite length, support and associated primes

For a finitely generated module `M` over a Noetherian ring the following are equivalent
(`Module.isFiniteLength_tfae`, [Matsumura, *Commutative Ring Theory*, Theorem 6.5]):

* `M` has finite length;
* every associated prime of `M` is maximal;
* every prime in the support of `M` is maximal.
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module

variable [Module.Finite R M]

/-- For a finitely generated module, every prime in the support is maximal iff every minimal
prime over the annihilator is maximal. -/
theorem forall_support_isMaximal_iff :
    (∀ p ∈ support R M, p.asIdeal.IsMaximal) ↔
      ∀ J ∈ (annihilator R M).minimalPrimes, J.IsMaximal := by
  refine ⟨fun h J hJ => h ⟨J, hJ.1.1⟩ (mem_support_iff_of_finite.mpr hJ.1.2), fun h p hp => ?_⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (mem_support_iff_of_finite.mp hp)
  have hq_max := h q hq
  rwa [← hq_max.eq_of_le p.2.ne_top hqp]

variable [IsNoetherianRing R]

/-- Over a Noetherian ring, the quotient of `R` by the annihilator of a finitely generated
module `M` is an Artinian ring iff every prime in the support of `M` is maximal. -/
theorem isArtinianRing_quotient_annihilator_iff :
    IsArtinianRing (R ⧸ annihilator R M) ↔ ∀ p ∈ support R M, p.asIdeal.IsMaximal := by
  rw [isArtinianRing_iff_krullDimLE_zero,
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal, forall_support_isMaximal_iff]

/-- A finitely generated module over a Noetherian ring has finite length iff every prime in
its support is maximal. -/
theorem isFiniteLength_iff_support_isMaximal :
    IsFiniteLength R M ↔ ∀ p ∈ support R M, p.asIdeal.IsMaximal := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian,
    and_iff_right (inferInstanceAs (IsNoetherian R M)),
    isArtinian_iff_isArtinianRing_quotient_annihilator, isArtinianRing_quotient_annihilator_iff]

/-- A finite torsion module over a Noetherian ring of Krull dimension at most one has finite
length. -/
theorem IsTorsion.isFiniteLength [Ring.KrullDimLE 1 R] (hM : IsTorsion R M) :
    IsFiniteLength R M := by
  obtain ⟨x, hxann, hxreg⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  rw [Submodule.annihilator_top] at hxann
  refine isFiniteLength_iff_support_isMaximal.mpr fun p hp => ?_
  exact p.2.isMaximal_of_mem_nonZeroDivisors hxreg (mem_support_iff_of_finite.mp hp hxann)

/-- For a finitely generated module `M` over a Noetherian ring, the following are equivalent:
`M` has finite length; every associated prime of `M` is maximal; every prime in the support
of `M` is maximal. -/
theorem isFiniteLength_tfae :
    List.TFAE [IsFiniteLength R M,
      ∀ p ∈ associatedPrimes R M, p.IsMaximal,
      ∀ p ∈ support R M, p.asIdeal.IsMaximal] := by
  tfae_have 1 ↔ 3 := isFiniteLength_iff_support_isMaximal
  tfae_have 3 → 2 := fun h p hp ↦ h ⟨p, hp.isPrime⟩ hp.mem_support
  tfae_have 2 → 3 := fun h ↦ forall_support_isMaximal_iff.mpr fun J hJ ↦
    h J (associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hJ)
  tfae_finish

end Module
