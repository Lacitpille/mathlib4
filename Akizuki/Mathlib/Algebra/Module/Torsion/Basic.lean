/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Akizuki.Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Torsion quotients by spans of maximal linearly independent families

Over a domain, the quotient of a module by the span of a maximal linearly independent family
is a torsion module.
-/

public section

namespace LinearIndependent.Maximal

/-- The quotient by the span of a maximal linearly independent family over a domain
is torsion. -/
theorem isTorsion_quotient_span {ι R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] {v : ι → M} (hv : LinearIndependent R v) (hmax : hv.Maximal) :
    Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) := by
  intro x
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨a, ha, ha_mem⟩ := hmax.exists_ne_zero_smul_mem_span hv m
  exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, by
    rwa [← Submodule.Quotient.mk_eq_zero] at ha_mem⟩

end LinearIndependent.Maximal
