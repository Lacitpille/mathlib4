/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Akizuki.Mathlib.LinearAlgebra.Dimension.Localization
public import Akizuki.Mathlib.RingTheory.Algebraic.Integral
public import Akizuki.Mathlib.RingTheory.Ideal.GoingUp
public import Akizuki.Mathlib.RingTheory.Length.QuotSMulTop

/-!
# The Krull–Akizuki theorem

Let `A` be a Noetherian domain of Krull dimension at most one and let `B` be a domain which is a
torsion-free `A`-algebra of finite rank. The Krull–Akizuki theorem says that `B` is again a
Noetherian ring of Krull dimension at most one, and that `B ⧸ b` has finite length over `A` for
every nonzero ideal `b` of `B`.

The finite rank hypothesis holds whenever `A → B → L` with `B → L` injective, for a finite
extension `L` of the fraction field `K` of `A`
(`IsFractionRing.rank_lt_aleph0_of_faithfulSMul`): for instance for every subalgebra of `L` and
for the integral closure of `A` in `L`.

## Main results

* `KrullAkizuki.isFiniteLength_quotient`: `B ⧸ b` has finite length over `A` for `b ≠ ⊥`.
* `KrullAkizuki.finite_quotient`: `B ⧸ b` is a finite `A`-module for `b ≠ ⊥`.
* `KrullAkizuki.isNoetherianRing`: `B` is a Noetherian ring.
* `KrullAkizuki.krullDimLE_one`: `B` has Krull dimension at most one.
* `KrullAkizuki.isNoetherianRing_of_faithfulSMul`, `KrullAkizuki.krullDimLE_one_of_faithfulSMul`:
  the same for `A → B → L` as above.
* `IsIntegralClosure.isDedekindDomain_of_krullDimLE_one`,
  `integralClosure.isDedekindDomain_of_krullDimLE_one`: the integral closure of `A` in `L` is a
  Dedekind domain. Unlike `IsIntegralClosure.isDedekindDomain`, this needs neither `L / K`
  separable nor `A` integrally closed.

## Implementation notes

Pick `a ≠ 0` in `b ∩ A` (`Ideal.IsAlgebraic.under_ne_bot`). Then `B ⧸ b` is a quotient of
`B ⧸ aB`, whose length is at most `rank_A B * length (A ⧸ aA) < ⊤`
(`Module.isFiniteLength_quotSMulTop`).

When upstreaming, the Dedekind domain results should replace the hypotheses
`[IsDedekindDomain A] [Algebra.IsSeparable K L]` of `IsIntegralClosure.isDedekindDomain`,
`integralClosure.isDedekindDomain` and `integralClosure.isDedekindDomain_fractionRing` in
`Mathlib.RingTheory.DedekindDomain.IntegralClosure` instead of adding parallel declarations.

## References

* [H. Matsumura, *Commutative Ring Theory*, Theorem 11.7][matsumura1987]
-/

public section

open Cardinal
open scoped Pointwise

namespace KrullAkizuki

section Intrinsic

variable (A : Type*) {B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B]

/-- **Krull–Akizuki theorem**, key step: if `B` has finite rank over `A`, the quotient of `B` by
a nonzero ideal has finite length as an `A`-module. -/
theorem isFiniteLength_quotient (hB : Module.rank A B < ℵ₀) {b : Ideal B} (hb : b ≠ ⊥) :
    IsFiniteLength A (B ⧸ b) := by
  have := Algebra.IsAlgebraic.of_rank_lt_aleph0 hB
  obtain ⟨a, haI, ha0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.IsAlgebraic.under_ne_bot A hb)
  have hle : a • (⊤ : Submodule A B) ≤ b.restrictScalars A := by
    rintro _ ⟨w, -, rfl⟩
    simpa [Algebra.smul_def] using b.mul_mem_right w haI
  have hfl := Module.isFiniteLength_quotSMulTop
    (isRegular_iff_ne_zero.mpr ha0).isSMulRegular hB (M := B)
  let e := Submodule.Quotient.restrictScalarsEquiv A b
  exact hfl.of_surjective (f := e.toLinearMap ∘ₗ Submodule.factor hle)
    (e.surjective.comp (Submodule.factor_surjective hle))

/-- **Krull–Akizuki theorem**: if `B` has finite rank over `A`, the quotient of `B` by a nonzero
ideal is a finite `A`-module. -/
theorem finite_quotient (hB : Module.rank A B < ℵ₀) {b : Ideal B} (hb : b ≠ ⊥) :
    Module.Finite A (B ⧸ b) :=
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient A hB hb)).1
  inferInstance

/-- **Krull–Akizuki theorem**: if `B` has finite rank over `A`, then `B` is a Noetherian ring. -/
theorem isNoetherianRing (hB : Module.rank A B < ℵ₀) : IsNoetherianRing B := by
  refine (isNoetherianRing_iff_ideal_fg B).mpr fun I => ?_
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hJ : Ideal.span {x} ≠ ⊥ := by simpa using hx0
  have : IsNoetherian A (B ⧸ Ideal.span {x}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient A hB hJ)).1
  have : IsNoetherian B (B ⧸ Ideal.span {x}) := isNoetherian_of_tower A this
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {x}))
    (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hxI)]
  exact Submodule.fg_span_singleton x

/-- **Krull–Akizuki theorem**: if `B` has finite rank over `A`, then `B` has Krull dimension at
most one. -/
theorem krullDimLE_one (hB : Module.rank A B < ℵ₀) : Ring.KrullDimLE 1 B := by
  refine .mk₁' fun P hP _ => ?_
  have : IsArtinianRing (B ⧸ P) := isArtinian_of_tower A
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient A hB hP)).2
  exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain (B ⧸ P))

end Intrinsic

section FaithfulSMul

variable (A K L B : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L] [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [FaithfulSMul B L]

include A K L

/-- **Krull–Akizuki theorem**: a domain `B` with `A → B → L` and `B → L` injective, where `L` is
a finite extension of the fraction field `K` of `A`, is a Noetherian ring. This applies to every
subalgebra of `L`. -/
theorem isNoetherianRing_of_faithfulSMul : IsNoetherianRing B :=
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := .of_faithfulSMul (S := A) B L
  isNoetherianRing A (IsFractionRing.rank_lt_aleph0_of_faithfulSMul A K L B)

/-- **Krull–Akizuki theorem**: a domain `B` with `A → B → L` and `B → L` injective, where `L` is
a finite extension of the fraction field `K` of `A`, has Krull dimension at most one. This
applies to every subalgebra of `L`. -/
theorem krullDimLE_one_of_faithfulSMul : Ring.KrullDimLE 1 B :=
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := .of_faithfulSMul (S := A) B L
  krullDimLE_one A (IsFractionRing.rank_lt_aleph0_of_faithfulSMul A K L B)

end FaithfulSMul

end KrullAkizuki

section Dedekind

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L]
  (C : Type*) [CommRing C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L] [Algebra A C]
  [IsScalarTower A C L]

include A K L in
/-- **Krull–Akizuki theorem**: if `A` is a Noetherian domain of Krull dimension at most one with
fraction field `K` and `L / K` is finite, then the integral closure of `A` in `L` is a Dedekind
domain. Unlike `IsIntegralClosure.isDedekindDomain`, this needs neither `L / K` separable nor
`A` integrally closed. -/
theorem IsIntegralClosure.isDedekindDomain_of_krullDimLE_one : IsDedekindDomain C :=
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).mpr
    (IsIntegralClosure.algebraMap_injective C A L)
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have := KrullAkizuki.isNoetherianRing_of_faithfulSMul A K L C
  have := KrullAkizuki.krullDimLE_one_of_faithfulSMul A K L C
  { (inferInstance : IsNoetherianRing C),
    (⟨fun hP hp => hp.isMaximal_of_ne_bot hP⟩ : Ring.DimensionLEOne C),
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }

include K in
/-- **Krull–Akizuki theorem**: if `A` is a Noetherian domain of Krull dimension at most one with
fraction field `K` and `L / K` is finite, then the integral closure of `A` in `L` is a Dedekind
domain. Unlike `integralClosure.isDedekindDomain`, this needs neither `L / K` separable nor
`A` integrally closed.

This cannot be an instance since `K` cannot be inferred; see
`integralClosure.isDedekindDomain_fractionRing_of_krullDimLE_one` for the instance. -/
theorem integralClosure.isDedekindDomain_of_krullDimLE_one :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain_of_krullDimLE_one A K L (integralClosure A L)

end Dedekind

/-- **Krull–Akizuki theorem**: the integral closure of a Noetherian domain `A` of Krull dimension
at most one in a finite extension `L` of `FractionRing A` is a Dedekind domain. -/
instance integralClosure.isDedekindDomain_fractionRing_of_krullDimLE_one (A L : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Field L]
    [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L] [Algebra A L]
    [IsScalarTower A (FractionRing A) L] : IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain_of_krullDimLE_one A (FractionRing A) L
