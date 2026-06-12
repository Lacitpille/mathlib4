/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Algebra.Module.PointwisePi
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Pi

/-!
# Pointwise scalar multiplication of pi submodules

Scaling a product of submodules over a full index set is the product of the scaled submodules.
-/

public section

open scoped Pointwise

namespace Submodule

/-- Scaling a product of submodules over a full index set is the product of the scaled
submodules. -/
theorem smul_univ_pi {S R ι : Type*} [Monoid S] [Semiring R] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, DistribMulAction S (M i)]
    [∀ i, SMulCommClass S R (M i)] (x : S) (p : ∀ i, Submodule R (M i)) :
    x • Submodule.pi Set.univ p = Submodule.pi Set.univ fun i => x • p i := by
  apply SetLike.coe_injective
  change x • Set.pi Set.univ (fun i => (p i : Set (M i))) =
    Set.pi Set.univ fun i => x • (p i : Set (M i))
  exact _root_.smul_univ_pi x _

end Submodule
