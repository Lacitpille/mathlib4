/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Zero-dimensional quotients

`R ⧸ I` has Krull dimension zero iff every prime ideal containing `I` is maximal
(`Ideal.krullDimLE_zero_quotient_iff_forall_isPrime_isMaximal`). This is a companion of
`Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal`.
-/

public section

/-- `R ⧸ I` has Krull dimension zero iff every prime ideal containing `I` is maximal. -/
theorem Ideal.krullDimLE_zero_quotient_iff_forall_isPrime_isMaximal {R : Type*} [CommRing R]
    {I : Ideal R} :
    Ring.KrullDimLE 0 (R ⧸ I) ↔ ∀ J : Ideal R, J.IsPrime → I ≤ J → J.IsMaximal := by
  rw [krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
  refine ⟨fun h J hJ hIJ ↦ ?_, fun h J hJ ↦ h J hJ.1.1 hJ.1.2⟩
  obtain ⟨q, hq, hqJ⟩ := Ideal.exists_minimalPrimes_le hIJ
  exact (h q hq).eq_of_le hJ.ne_top hqJ ▸ h q hq
