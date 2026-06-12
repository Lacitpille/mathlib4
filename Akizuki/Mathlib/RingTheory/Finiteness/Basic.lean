/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Suprema and images of finitely generated submodules

Every module is the supremum of its finitely generated submodules, and a finitely generated
submodule of the codomain of a surjective linear map lifts to a finitely generated submodule
of the domain.
-/

public section

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N]

/-- Every module is the supremum of its finitely generated submodules. -/
theorem iSup_fg_eq_top : (⨆ N : {N : Submodule R M // N.FG}, N.1) = ⊤ :=
  le_antisymm le_top fun x _ ↦ mem_iSup_of_mem ⟨R ∙ x, fg_span_singleton x⟩
    (mem_span_singleton_self x)

/-- A finitely generated submodule of the codomain of a surjective linear map is the image of a
finitely generated submodule of the domain. -/
theorem FG.exists_fg_map_eq {P : Submodule R N} (hP : P.FG) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) : ∃ Q : Submodule R M, Q.FG ∧ Q.map f = P := by
  obtain ⟨t, htf, rfl⟩ := Submodule.fg_def.mp hP
  choose g hg using fun y : t => hf y
  haveI := htf.to_subtype
  refine ⟨Submodule.span R (Set.range g), Submodule.fg_span (Set.finite_range g), ?_⟩
  rw [Submodule.map_span, ← Set.range_comp, show f ∘ g = Subtype.val from funext hg,
    Subtype.range_coe]

end Submodule
