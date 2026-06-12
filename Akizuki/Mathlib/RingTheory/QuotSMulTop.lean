/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.QuotSMulTop
public import Akizuki.Mathlib.Algebra.Module.PointwisePi

/-!
# Reduction of a finite product modulo an element

Reducing a finite product of modules modulo `x` is the product of the coordinatewise reductions.
-/

public section

open scoped Pointwise

namespace QuotSMulTop

variable {R ι : Type*} [CommRing R] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)]

/-- Reducing a finite product modulo `x` is the product of the coordinatewise reductions. -/
def piEquiv [Fintype ι] [DecidableEq ι] (x : R) :
    QuotSMulTop x ((i : ι) → M i) ≃ₗ[R] (i : ι) → QuotSMulTop x (M i) :=
  (Submodule.quotEquivOfEq _ _ (by rw [← Submodule.pi_top Set.univ, Submodule.smul_univ_pi])).trans
    (Submodule.quotientPi _)

end QuotSMulTop
