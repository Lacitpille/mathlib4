/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Associated primes lie in the support

An associated prime of a module is a point of its support.
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An associated prime of a module lies in its support. -/
theorem IsAssociatedPrime.mem_support {p : Ideal R} (hp : IsAssociatedPrime p M) :
    ⟨p, hp.isPrime⟩ ∈ Module.support R M := by
  obtain ⟨x, hx⟩ := hp.2
  refine Module.mem_support_iff_exists_annihilator.mpr ⟨x, ?_⟩
  change (R ∙ x).annihilator ≤ p
  rw [hx]
  intro r hr
  rw [Submodule.mem_annihilator_span_singleton] at hr
  exact Ideal.le_radical (Submodule.mem_colon_singleton.mpr (by simp [hr]))
