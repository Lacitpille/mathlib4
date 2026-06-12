/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Maximal linearly independent families

Every module has a maximal linearly independent family, and if `v` is a maximal linearly
independent family over a nontrivial ring and `m` is any vector, then some nonzero multiple
of `m` lies in the span of `v`.
-/

public section

/-- Every module has a maximal linearly independent family. -/
theorem exists_maximal_linearIndependent (R : Type*) {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] : ∃ (s : Set M) (hs : LinearIndependent R ((↑) : s → M)), hs.Maximal := by
  obtain ⟨s, hs_li, hs_max⟩ := exists_maximal_linearIndepOn' R (id : M → M)
  refine ⟨s, hs_li, fun t ht hst => ?_⟩
  simp_rw [Subtype.range_coe] at hst ⊢
  exact hs_max t hst ht

namespace LinearIndependent.Maximal

/-- Over a nontrivial ring, if `v` is a maximal linearly independent family and `m : M`,
then there is `a ≠ 0` with `a • m ∈ span (range v)`. -/
theorem exists_ne_zero_smul_mem_span {ι R M : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [Module R M] {v : ι → M} (hv : LinearIndependent R v) (hmax : hv.Maximal) (m : M) :
    ∃ a : R, a ≠ 0 ∧ a • m ∈ Submodule.span R (Set.range v) := by
  by_contra h
  have key : ∀ r : R, r • m ∈ Submodule.span R (Set.range v) → r = 0 :=
    fun r hr => of_not_not fun hr0 => h ⟨r, hr0, hr⟩
  have hmrange : m ∉ Set.range v := fun hm =>
    one_ne_zero (key 1 (by simpa using Submodule.subset_span hm))
  have heq := hmax _ (hv.linearIndepOn_id.id_insert' key) (Set.subset_insert _ _)
  exact (heq ▸ hmrange) (Set.mem_insert m _)

end LinearIndependent.Maximal
