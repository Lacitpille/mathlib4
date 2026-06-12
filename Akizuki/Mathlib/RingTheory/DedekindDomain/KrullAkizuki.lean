/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import Akizuki.Mathlib.RingTheory.Ideal.GoingUp
public import Akizuki.Mathlib.RingTheory.Length.QuotSMulTop

/-!
# The Krull–Akizuki theorem

Let `A` be a Noetherian domain of Krull dimension at most one with fraction field `K`, let
`L / K` be a finite field extension and let `B` be an `A`-subalgebra of `L`. We prove:

* `KrullAkizuki.isFiniteLength_quotient`: `B ⧸ b` has finite length over `A` for every nonzero
  ideal `b` of `B`;
* `KrullAkizuki.isNoetherianRing`: `B` is a Noetherian ring;
* `KrullAkizuki.isMaximal_of_ne_bot`: every nonzero prime ideal of `B` is maximal;
* `KrullAkizuki.finite_quotient`: `B ⧸ b` is a finite `A`-module for every nonzero ideal `b`;
* `integralClosure.isDedekindDomain_of_krullDimLE_one`: the integral closure of `A` in `L` is a
  Dedekind domain. Unlike `integralClosure.isDedekindDomain`, this requires neither separability
  of `L / K` nor `A` to be integrally closed.
-/

public section

open scoped Pointwise

namespace KrullAkizuki

variable {A : Type*} (K : Type*) {L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] (B : Subalgebra A L)

include K

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
private lemma isAlgebraic_aux : Algebra.IsAlgebraic A B := by
  have : Algebra.IsAlgebraic A L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  exact (Subalgebra.isAlgebraic_iff B).mp fun x _ => Algebra.IsAlgebraic.isAlgebraic (R := A) x

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [FiniteDimensional K L] in
private lemma isTorsionFree_aux : Module.IsTorsionFree A B := by
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  exact Function.Injective.moduleIsTorsionFree (fun x : B => (x : L)) Subtype.val_injective
    fun r x => rfl

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
private lemma rank_lt_aleph0_aux : Module.rank A B < Cardinal.aleph0 := by
  have hBL : Module.rank A B ≤ Module.rank A L := by
    simpa [Subalgebra.rank_toSubmodule] using Submodule.rank_le B.toSubmodule
  exact lt_of_le_of_lt (hBL.trans_eq (IsLocalization.rank_eq K (nonZeroDivisors A) le_rfl).symm)
    (Module.rank_lt_aleph0 K L)

private lemma quotSMulTop_isFiniteLength_aux (a : A) (ha : a ≠ 0) :
    IsFiniteLength A (QuotSMulTop a B) := by
  have : Module.IsTorsionFree A B := isTorsionFree_aux K B
  have ha_reg : IsSMulRegular B a := (isRegular_iff_ne_zero.mpr ha).isSMulRegular
  have hrank_ne : (Module.rank A B).toENat ≠ ⊤ :=
    Cardinal.toENat_ne_top.mpr (rank_lt_aleph0_aux K B)
  have hspan : Ideal.span {a} = a • (⊤ : Submodule A A) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have hAfl : IsFiniteLength A (QuotSMulTop a A) :=
    IsFiniteLength.of_surjective (f := (Submodule.quotEquivOfEq _ _ hspan).toLinearMap)
      (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
      (Submodule.quotEquivOfEq _ _ hspan).surjective
  exact Module.length_ne_top_iff.mp <|
    ne_top_of_le_ne_top (WithTop.mul_ne_top hrank_ne (Module.length_ne_top_iff.mpr hAfl))
      (Module.length_quotSMulTop_le_rank_toENat_mul ha_reg)

/-- **Krull–Akizuki theorem**, key step: the quotient of `B` by a nonzero ideal has finite
length as an `A`-module. -/
theorem isFiniteLength_quotient (b : Ideal B) (hb : b ≠ ⊥) : IsFiniteLength A (B ⧸ b) := by
  have : Algebra.IsAlgebraic A B := isAlgebraic_aux K B
  obtain ⟨a, haI, ha0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.IsAlgebraic.comap_ne_bot A hb)
  have hle : a • (⊤ : Submodule A B) ≤ b.restrictScalars A := by
    intro z hz
    rcases (Submodule.mem_smul_pointwise_iff_exists z a ⊤).mp hz with ⟨w, _, hzw⟩
    rw [← hzw]
    simpa [Algebra.smul_def] using b.mul_mem_right w (Ideal.mem_comap.mp haI)
  change IsFiniteLength A (B ⧸ b.restrictScalars A)
  exact IsFiniteLength.of_surjective (quotSMulTop_isFiniteLength_aux K B a ha0)
    (Submodule.factor_surjective hle)

/-- **Krull–Akizuki theorem**: an intermediate ring between a Noetherian domain `A` of Krull
dimension at most one and a finite extension of its fraction field is Noetherian. -/
theorem isNoetherianRing : IsNoetherianRing B := by
  refine (isNoetherianRing_iff_ideal_fg B).mpr fun I => ?_
  by_cases hI : I = ⊥
  · subst hI; exact Submodule.fg_bot
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let J : Ideal B := Ideal.span {x}
  let Jsub : Submodule B B := J
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ Jsub) ?_ ?_
  · have hJ : J ≠ ⊥ := fun hJ =>
      hx0 (Ideal.span_singleton_eq_bot.mp (by simpa [J] using hJ))
    have : IsNoetherian B (B ⧸ Jsub) := isNoetherian_of_tower A
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient K B J hJ)).1
    exact IsNoetherian.noetherian (R := B) (M := B ⧸ Jsub)
      (Submodule.map (Submodule.mkQ Jsub) (I : Submodule B B))
  · have hJI : Jsub ≤ (I : Submodule B B) := (Ideal.span_singleton_le_iff_mem I).mpr hxI
    rw [Submodule.ker_mkQ, inf_eq_right.mpr hJI]
    simpa [Jsub, J, Ideal.submodule_span_eq] using Submodule.fg_span_singleton x

/-- **Krull–Akizuki theorem**: every nonzero prime ideal of `B` is maximal. -/
theorem isMaximal_of_ne_bot (P : Ideal B) [Ideal.IsPrime P] (hP : P ≠ ⊥) :
    Ideal.IsMaximal P := by
  have : IsArtinianRing (B ⧸ P) := isArtinian_of_tower A (S := B ⧸ P) (M := B ⧸ P)
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient K B P hP)).2
  have : IsDomain (B ⧸ P) := (Ideal.Quotient.isDomain_iff_prime P).mpr inferInstance
  exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain (B ⧸ P))

/-- **Krull–Akizuki theorem**: `B` has Krull dimension at most one. -/
theorem dimensionLEOne : Ring.DimensionLEOne B where
  maximalOfPrime {P} hP hP_prime :=
    have : P.IsPrime := hP_prime
    isMaximal_of_ne_bot K B P hP

/-- **Krull–Akizuki theorem**: `B` has Krull dimension at most one. -/
theorem krullDimLE_one : Ring.KrullDimLE 1 B :=
  haveI := dimensionLEOne K B
  inferInstance

/-- **Krull–Akizuki theorem**: the quotient of `B` by a nonzero ideal is a finite
`A`-module. -/
theorem finite_quotient (b : Ideal B) (hb : b ≠ ⊥) : Module.Finite A (B ⧸ b) := by
  have : IsNoetherian A (B ⧸ b) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_quotient K B b hb)).1
  exact Module.Finite.of_fg_top (IsNoetherian.noetherian (⊤ : Submodule A (B ⧸ b)))

end KrullAkizuki

section

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]

include K in
/-- **Krull–Akizuki theorem**: the integral closure of a Noetherian domain `A` of Krull
dimension at most one in a finite extension `L` of its fraction field is a Dedekind domain.
Unlike `integralClosure.isDedekindDomain`, this requires neither separability of `L / K` nor
`A` to be integrally closed. -/
theorem integralClosure.isDedekindDomain_of_krullDimLE_one :
    IsDedekindDomain (integralClosure A L) :=
  { KrullAkizuki.isNoetherianRing K (integralClosure A L),
    KrullAkizuki.dimensionLEOne K (integralClosure A L),
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) K (L := L),
    (inferInstance : IsDomain (integralClosure A L)) with }

end

/-- **Krull–Akizuki theorem**: specialization of
`integralClosure.isDedekindDomain_of_krullDimLE_one` to `K := FractionRing A`. -/
instance integralClosure.isDedekindDomain_fractionRing_of_krullDimLE_one (A L : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Field L]
    [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L] [Algebra A L]
    [IsScalarTower A (FractionRing A) L] : IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain_of_krullDimLE_one A (FractionRing A) L
