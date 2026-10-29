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
public import Akizuki.Mathlib.RingTheory.KrullDimension.Zero
public import Akizuki.Mathlib.RingTheory.QuotientAnnihilator

/-!
# Finite length, support and associated primes

## Main results

* `IsFiniteLength.isMaximal_of_mem_support`: every prime in the support of a module of finite
  length is maximal.
* `Module.isFiniteLength_iff_forall_support_isMaximal`: a Noetherian module has finite length iff
  every prime in its support is maximal.
* `Module.isFiniteLength_tfae`: for a finitely generated module `M` over a Noetherian ring, the
  following are equivalent: `M` has finite length; `M` is Artinian; every associated prime of `M`
  is maximal; every prime in the support of `M` is maximal.

## References

* [H. Matsumura, *Commutative Ring Theory*][matsumura1987]
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Every prime in the support of a module of finite length is maximal. -/
theorem IsFiniteLength.isMaximal_of_mem_support (h : IsFiniteLength R M)
    {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) : p.asIdeal.IsMaximal := by
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  have := (isArtinian_iff_isArtinianRing_quotient_annihilator (M := M)).mp ‹_›
  exact (Ideal.krullDimLE_zero_quotient_iff_forall_isPrime_isMaximal.mp inferInstance) _ p.isPrime
    (Module.mem_support_iff_of_finite.mp hp)

namespace Module

/-- A Noetherian module has finite length iff every prime in its support is maximal. -/
theorem isFiniteLength_iff_forall_support_isMaximal [IsNoetherian R M] :
    IsFiniteLength R M ↔ ∀ p ∈ support R M, p.asIdeal.IsMaximal := by
  refine ⟨fun h _ hp ↦ h.isMaximal_of_mem_support hp, fun h ↦ ?_⟩
  rw [isFiniteLength_iff_isNoetherian_isArtinian, and_iff_right ‹_›,
    isArtinian_iff_isArtinianRing_quotient_annihilator, isArtinianRing_iff_krullDimLE_zero,
    Ideal.krullDimLE_zero_quotient_iff_forall_isPrime_isMaximal]
  exact fun J hJ hle ↦ h ⟨J, hJ⟩ (mem_support_iff_of_finite.mpr hle)

/-- For a finitely generated module `M` over a Noetherian ring, the following are equivalent:
`M` has finite length; `M` is Artinian; every associated prime of `M` is maximal; every prime in
the support of `M` is maximal. -/
theorem isFiniteLength_tfae [IsNoetherianRing R] [Module.Finite R M] :
    List.TFAE [IsFiniteLength R M, IsArtinian R M,
      ∀ p ∈ associatedPrimes R M, p.IsMaximal,
      ∀ p ∈ support R M, p.asIdeal.IsMaximal] := by
  tfae_have 1 ↔ 2 := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian,
      and_iff_right (inferInstanceAs (IsNoetherian R M))]
  tfae_have 1 ↔ 4 := isFiniteLength_iff_forall_support_isMaximal
  tfae_have 4 → 3 := fun h p hp ↦ h ⟨p, hp.isPrime⟩ hp.mem_support
  tfae_have 3 → 4 := fun h p hp ↦ by
    obtain ⟨q, hq, hqp⟩ := exists_associatedPrimes_le_of_mem_support hp
    exact (h q hq).eq_of_le p.isPrime.ne_top hqp ▸ h q hq
  tfae_finish

end Module
