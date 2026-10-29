/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Suprema and images of finitely generated submodules

Every module is the supremum of its finitely generated submodules
(`Submodule.iSup_fg_eq_top`), and a finitely generated submodule of the codomain of a surjective
(semi)linear map is the image of a finitely generated submodule of the domain
(`Submodule.FG.exists_fg_map_eq_of_surjective`).
-/

public section

open Function

namespace Submodule

variable {R S M P : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid P]
  [Module R M] [Module S P]

/-- Every module is the supremum of its finitely generated submodules. -/
theorem iSup_fg_eq_top : (⨆ N : {N : Submodule R M // N.FG}, N.1) = ⊤ :=
  le_antisymm le_top fun x _ ↦ mem_iSup_of_mem ⟨R ∙ x, fg_span_singleton x⟩
    (mem_span_singleton_self x)

variable {σ : R →+* S} [RingHomSurjective σ] (f : M →ₛₗ[σ] P)

/-- A finitely generated submodule of the codomain of a surjective (semi)linear map is the image
of a finitely generated submodule of the domain. -/
theorem FG.exists_fg_map_eq_of_surjective (hf : Surjective f) {N : Submodule S P} (hN : N.FG) :
    ∃ N' : Submodule R M, N'.FG ∧ N'.map f = N := by
  obtain ⟨s, hs, rfl⟩ := fg_def.mp hN
  exact ⟨span R (surjInv hf '' s), fg_span (hs.image _), by
    simp only [map_span, Set.image_image, surjInv_eq hf, Set.image_id']⟩

end Submodule
