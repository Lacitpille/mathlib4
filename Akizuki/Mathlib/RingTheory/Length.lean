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
# More on the length of modules

## Main results

* `Module.length_quotient_map_eq_add_quotient_range`: for injective `f : M → M'`,
  `length (M' ⧸ f(N)) = length (M ⧸ N) + length (M' ⧸ range f)`.
* `Module.length_iSup_of_directed`: length commutes with directed unions of submodules.
* `Module.length_eq_iSup_fg`: the length of a module is the supremum of the lengths of its
  finitely generated submodules.
-/

public section

namespace Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If `f` is injective, the quotient by the image of a submodule adds the length of the
cokernel of `f`. -/
theorem length_quotient_map_eq_add_quotient_range {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (N : Submodule R M) :
    length R (M' ⧸ N.map f) = length R (M ⧸ N) + length R (M' ⧸ LinearMap.range f) := by
  refine length_eq_add_of_exact (N.mapQ (N.map f) f (Submodule.le_comap_map f N))
    (Submodule.factor LinearMap.map_le_range) ?_ (Submodule.factor_surjective _) ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.comap_map_eq_of_injective hf,
      Submodule.mkQ_map_self]
  · rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_id, Submodule.range_mapQ]

/-- Length commutes with directed unions of submodules. -/
theorem length_iSup_of_directed {ι : Sort*} {N : ι → Submodule R M}
    (hN : Directed (· ≤ ·) N) : length R ↥(⨆ i, N i) = ⨆ i, length R (N i) := by
  simp_rw [length_submodule]
  exact Order.height_iSup_of_directed hN

/-- The length of a module is the supremum of the lengths of its finitely generated
submodules. -/
theorem length_eq_iSup_fg : length R M = ⨆ N : {N : Submodule R M // N.FG}, length R N := by
  rw [← length_top, ← Submodule.iSup_fg_eq_top,
    length_iSup_of_directed (Subtype.mono_coe _).directed_le]

end Module
