/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Algebras of finite rank are algebraic

`Algebra.IsAlgebraic.of_rank_lt_aleph0` generalizes `Algebra.IsAlgebraic.of_finite` from finite
modules to modules of finite rank.
-/

public section

open Cardinal

/-- An algebra of finite rank is algebraic. -/
theorem Algebra.IsAlgebraic.of_rank_lt_aleph0 {R A : Type*} [CommRing R] [Nontrivial R] [Ring A]
    [Algebra R A] (h : Module.rank R A < ℵ₀) : Algebra.IsAlgebraic R A := by
  refine ⟨fun x => not_not.mp fun hx => h.not_ge ?_⟩
  have hli : LinearIndependent R (fun n : ℕ => x ^ n) := by
    have := (Polynomial.linearIndependent_powers_iff_aeval (Algebra.lmul R A x) 1).mpr
      fun p hp => transcendental_iff_injective.mp hx (by
        rw [Polynomial.aeval_algHom_apply] at hp
        simpa using hp)
    simp_rw [← map_pow] at this
    simpa using this
  simpa using hli.cardinal_lift_le_rank
