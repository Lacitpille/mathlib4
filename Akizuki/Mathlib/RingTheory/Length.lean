/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.Length
public import Akizuki.Mathlib.Order.KrullDimension
public import Akizuki.Mathlib.RingTheory.Finiteness.Basic

/-!
# Length of modules via finitely generated submodules

We express `Module.length` and the Krull dimension of the submodule lattice as suprema over
finitely generated submodules, and prove subadditivity of length along an exact pair.
-/

public section

namespace Submodule

/-- The height of `⊤` in the submodule lattice is the supremum over finitely generated
submodules. -/
theorem height_top_eq_iSup_fg {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Order.height (⊤ : Submodule R M) = ⨆ N : {N : Submodule R M // N.FG}, Order.height N.1 := by
  rw [← iSup_fg_eq_top]
  exact Order.height_iSup_of_monotone fun _ _ h => h

/-- The Krull dimension of the submodule lattice is the supremum over finitely generated
submodules. -/
theorem krullDim_eq_iSup_fg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    Order.krullDim (Submodule R M) =
      ⨆ N : {N : Submodule R M // N.FG}, Order.krullDim (Submodule R N.1) := by
  simp_rw [← Module.coe_length, Module.length_submodule, Module.length_eq_height,
    ← WithBot.coe_iSup (OrderTop.bddAbove _), height_top_eq_iSup_fg]

end Submodule

namespace Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A length bound from an exact pair of linear maps. -/
theorem length_le_add_of_exact {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N]
    [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hfg : Function.Exact f g) :
    length R M ≤ length R N + length R P := by
  rw [length_eq_add_of_exact (LinearMap.ker g).subtype (LinearMap.ker g).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    LinearEquiv.length_eq (LinearMap.quotKerEquivRange g), LinearMap.exact_iff.mp hfg]
  exact add_le_add (length_le_of_surjective _ f.surjective_rangeRestrict)
    (length_le_of_injective _ (Submodule.subtype_injective _))

/-- If `f` is injective, the quotient by the image of a submodule adds the length of the
cokernel of `f`. -/
theorem length_quotient_map_eq_add_quotient_range {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (N : Submodule R M) :
    length R (M' ⧸ N.map f) = length R (M ⧸ N) + length R (M' ⧸ LinearMap.range f) := by
  refine length_eq_add_of_exact (N.mapQ (N.map f) f (Submodule.le_comap_map f N))
    (Submodule.factor ((LinearMap.range_eq_map f).symm ▸ Submodule.map_mono le_top)) ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.comap_map_eq_of_injective hf]
    simp
  · exact Submodule.factor_surjective _
  · rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_id, Submodule.range_mapQ]

/-- The length of a module is the supremum of the lengths of its finitely generated
submodules. -/
theorem length_eq_iSup_fg : length R M = ⨆ N : {N : Submodule R M // N.FG}, length R N := by
  rw [length_eq_height, Submodule.height_top_eq_iSup_fg]
  exact iSup_congr fun N => length_submodule.symm

end Module
