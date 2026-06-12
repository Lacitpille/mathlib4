/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Support
public import Akizuki.Mathlib_copy.RingTheory.QuotientAnnihilator

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

/-- Associated primes of a finitely generated module lie in its support. -/
theorem IsAssociatedPrime.mem_support [Module.Finite R M] {p : Ideal R}
    (hp : IsAssociatedPrime p M) : ⟨p, hp.isPrime⟩ ∈ Module.support R M :=
  Module.mem_support_iff_of_finite.mpr <|
    le_of_eq_of_le Submodule.annihilator_top.symm hp.annihilator_le

namespace Module

variable [IsNoetherianRing R] [Module.Finite R M]

/-- Over a Noetherian ring, the quotient of `R` by the annihilator of a finitely generated
module `M` is an Artinian ring iff every prime in the support of `M` is maximal. -/
theorem isArtinianRing_quotient_annihilator_iff :
    IsArtinianRing (R ⧸ annihilator R M) ↔ ∀ p ∈ support R M, p.asIdeal.IsMaximal := by
  constructor
  · intro h p hp
    have hle : annihilator R M ≤ p.asIdeal := mem_support_iff_of_finite.mp hp
    haveI := Ideal.isPrime_map_quotientMk_of_isPrime hle
    rw [← Ideal.comap_map_mk hle]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  · intro h
    rw [isArtinianRing_iff_krullDimLE_zero]
    refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
    haveI := Ideal.comap_isPrime (Ideal.Quotient.mk (annihilator R M)) I
    have hle : annihilator R M ≤ I.comap (Ideal.Quotient.mk (annihilator R M)) :=
      Ideal.mk_ker.ge.trans (Ideal.comap_mono bot_le)
    haveI : (I.comap (Ideal.Quotient.mk (annihilator R M))).IsMaximal :=
      h ⟨_, ‹_›⟩ (mem_support_iff_of_finite.mpr hle)
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I]
    exact .map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (Ideal.mk_ker.le.trans hle)

/-- A finitely generated module over a Noetherian ring has finite length iff every prime in
its support is maximal. -/
theorem isFiniteLength_iff_support_isMaximal :
    IsFiniteLength R M ↔ ∀ p ∈ support R M, p.asIdeal.IsMaximal := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian,
    and_iff_right (inferInstanceAs (IsNoetherian R M)),
    isArtinian_iff_isArtinianRing_quotient_annihilator, isArtinianRing_quotient_annihilator_iff]

/-- For a finitely generated module `M` over a Noetherian ring, the following are equivalent:
`M` has finite length; every associated prime of `M` is maximal; every prime in the support
of `M` is maximal. -/
theorem isFiniteLength_tfae :
    List.TFAE [IsFiniteLength R M,
      ∀ p ∈ associatedPrimes R M, p.IsMaximal,
      ∀ p ∈ support R M, p.asIdeal.IsMaximal] := by
  tfae_have 1 ↔ 3 := isFiniteLength_iff_support_isMaximal
  tfae_have 3 → 2 := fun h p hp ↦ h ⟨p, hp.isPrime⟩ hp.mem_support
  tfae_have 2 → 3 := fun h p hp ↦ by
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (mem_support_iff_of_finite.mp hp)
    have hq_max := h q
      (associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq)
    rwa [← hq_max.eq_of_le p.2.ne_top hqp]
  tfae_finish

end Module
