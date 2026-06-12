/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Pointwise scalar multiplication as the image of `lsmul`

The pointwise scalar multiple `x • N` of a submodule is the image of `N` under scalar
multiplication by `x` as a linear map.
-/

public section

open scoped Pointwise

namespace Submodule

/-- The pointwise scalar multiple of a submodule is its image under `LinearMap.lsmul`. -/
@[simp]
theorem map_lsmul {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (x : R)
    (N : Submodule R M) : N.map (LinearMap.lsmul R M x) = x • N :=
  rfl

end Submodule
