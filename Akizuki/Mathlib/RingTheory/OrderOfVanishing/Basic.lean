/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Finite torsion modules over one-dimensional Noetherian rings

A finite torsion module over a Noetherian ring of Krull dimension at most one has finite length.
-/

public section

namespace Module

/-- A finite torsion module over a Noetherian ring of Krull dimension at most one has finite
length. -/
theorem IsTorsion.isFiniteLength {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [Module.Finite R M] (hM : IsTorsion R M) :
    IsFiniteLength R M := by
  obtain ⟨x, hxann, hxreg⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hxM : IsTorsionBy R M x := fun m ↦ Submodule.mem_annihilator.mp hxann m trivial
  have hset : IsTorsionBySet R M (Ideal.span {x}) :=
    (isTorsionBySet_span_singleton_iff x).mpr hxM
  let S := R ⧸ Ideal.span {x}
  letI : SMul S M := hset.hasSMul
  letI : Module S M := hset.module
  have : IsScalarTower R S M := hset.isScalarTower
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite R S M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  have hSfl := isFiniteLength_quotient_span_singleton (R := R) hxreg
  have : IsNoetherian R S := (isFiniteLength_iff_isNoetherian_isArtinian.mp hSfl).1
  have : IsArtinian R S := (isFiniteLength_iff_isNoetherian_isArtinian.mp hSfl).2
  exact IsFiniteLength.of_surjective (f := f.restrictScalars R)
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩) hf

end Module
