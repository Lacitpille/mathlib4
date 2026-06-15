/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Primes containing a non-zero-divisor in dimension at most one

In a commutative ring of Krull dimension at most one, every prime ideal containing a
non-zero-divisor is maximal. This generalizes `Ideal.IsPrime.isMaximal_of_ne_bot` from
domains to arbitrary commutative rings.
-/

public section

/-- In a ring of Krull dimension at most one, a prime ideal containing a non-zero-divisor is
maximal. -/
theorem Ideal.IsPrime.isMaximal_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    [Ring.KrullDimLE 1 R] {p : Ideal R} (hp : p.IsPrime) {x : R} (hx : x ∈ nonZeroDivisors R)
    (hxp : x ∈ p) : p.IsMaximal :=
  (Ring.krullDimLE_one_iff.mp ‹_› p hp).resolve_left fun hmin =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hxp hmin hx
