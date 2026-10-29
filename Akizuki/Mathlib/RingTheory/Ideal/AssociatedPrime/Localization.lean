/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Associated primes and the support

## Main results

* `IsAssociatedPrime.mem_support`: an associated prime of a module lies in its support.
* `Module.exists_associatedPrimes_le_of_mem_support`: for a finitely generated module over a
  Noetherian ring, every prime in the support contains an associated prime.

When upstreaming, also update the TODO "Connect to associated primes" in
`Mathlib.RingTheory.Support`.
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An associated prime of a module lies in its support. -/
theorem IsAssociatedPrime.mem_support {p : Ideal R} (hp : IsAssociatedPrime p M) :
    ⟨p, hp.isPrime⟩ ∈ Module.support R M := by
  obtain ⟨x, hx⟩ := hp.2
  rw [Submodule.bot_colon'] at hx
  exact Module.mem_support_iff_exists_annihilator.mpr ⟨x, hx ▸ Ideal.le_radical⟩

/-- For a finitely generated module over a Noetherian ring, every prime in the support contains
an associated prime. -/
theorem Module.exists_associatedPrimes_le_of_mem_support [IsNoetherianRing R] [Module.Finite R M]
    {p : PrimeSpectrum R} (hp : p ∈ Module.support R M) :
    ∃ q ∈ associatedPrimes R M, q ≤ p.asIdeal := by
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hp)
  exact ⟨q, associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq, hqp⟩
