/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Contraction of nonzero ideals along algebraic extensions

If `S` is a domain that is algebraic over `R`, the contraction of a nonzero ideal of `S` is
nonzero (`Ideal.IsAlgebraic.under_ne_bot`). This generalizes `Ideal.IsIntegral.under_ne_bot` and
`Ideal.under_ne_bot` from integral to algebraic extensions.
-/

public section

namespace Ideal

/-- If `S` is a domain that is algebraic over `R`, the contraction to `R` of a nonzero ideal of
`S` is nonzero. -/
theorem IsAlgebraic.under_ne_bot (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.IsAlgebraic R S] {I : Ideal S} (I_ne_bot : I ≠ ⊥) :
    I.under R ≠ ⊥ :=
  let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  under_ne_bot_of_algebraic_mem x_ne_zero x_mem (Algebra.IsAlgebraic.isAlgebraic x)

end Ideal
