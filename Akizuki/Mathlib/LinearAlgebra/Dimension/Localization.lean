/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Rank of an intermediate ring of a finite extension of the fraction field

If `K` is the fraction field of `A`, `L / K` is a finite extension and `A → B → L` with
`B → L` injective, then `B` has finite rank over `A`
(`IsFractionRing.rank_lt_aleph0_of_faithfulSMul`). This applies in particular to subalgebras of
`L`, to `integralClosure A L` and to any `C` with `IsIntegralClosure C A L`.
-/

public section

open Cardinal

/-- If `A → B → L` with `B → L` injective, where `L` is a finite extension of the fraction field
`K` of `A`, then `B` has finite rank over `A`. -/
theorem IsFractionRing.rank_lt_aleph0_of_faithfulSMul (A K L B : Type*) [CommRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra A L] [IsScalarTower A K L] [CommRing B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [FaithfulSMul B L] : Module.rank A B < ℵ₀ := by
  have h := LinearMap.lift_rank_le_of_injective (IsScalarTower.toAlgHom A B L).toLinearMap
    (FaithfulSMul.algebraMap_injective B L)
  rw [← IsFractionRing.rank_right_eq A K L] at h
  exact Cardinal.lift_lt_aleph0.mp <| h.trans_lt <|
    Cardinal.lift_lt_aleph0.mpr <| Module.rank_lt_aleph0 K L
