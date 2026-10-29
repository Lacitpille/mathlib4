/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Chain conditions and the quotient by the annihilator

## Main results

* `Module.exists_injective_quotient_annihilator_pi`: for a finitely generated module `M`, the
  quotient `R ⧸ Module.annihilator R M` embeds linearly into a finite power of `M`.
* `isArtinian_iff_isArtinianRing_quotient_annihilator`,
  `isNoetherian_iff_isNoetherianRing_quotient_annihilator`: a finitely generated module `M` is
  Artinian (resp. Noetherian) iff `R ⧸ Module.annihilator R M` is an Artinian (resp. Noetherian)
  ring.

When upstreaming, consider putting these into `Mathlib.RingTheory.HopkinsLevitzki`: with them,
the proof of `isNoetherian_of_finite_isArtinian` there becomes two lines.
-/

public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The kernel of `r ↦ (r • s i)ᵢ` is the annihilator of the span of the family `s`. -/
theorem LinearMap.ker_pi_toSpanSingleton {ι : Type*} (s : ι → M) :
    ker (pi fun i ↦ toSpanSingleton R M (s i)) = (Submodule.span R (Set.range s)).annihilator := by
  simp_rw [ker_pi, ← Submodule.annihilator_span_singleton, ← Submodule.annihilator_iSup,
    ← Submodule.span_iUnion, Set.iUnion_singleton_eq_range]

variable (R M) in
/-- For a finitely generated module `M`, the quotient of `R` by the annihilator of `M` embeds
linearly into a finite power of `M`. -/
theorem Module.exists_injective_quotient_annihilator_pi [Module.Finite R M] :
    ∃ (n : ℕ) (f : (R ⧸ annihilator R M) →ₗ[R] (Fin n → M)), Function.Injective f := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hker := (LinearMap.ker_pi_toSpanSingleton s).trans (by rw [hs, Submodule.annihilator_top])
  exact ⟨n, (annihilator R M).liftQ _ hker.ge,
    LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ hker.le⟩

/-- A finitely generated module is Artinian iff the quotient of the base ring by its
annihilator is an Artinian ring. -/
theorem isArtinian_iff_isArtinianRing_quotient_annihilator [Module.Finite R M] :
    IsArtinian R M ↔ IsArtinianRing (R ⧸ Module.annihilator R M) := by
  let _ := Module.quotientAnnihilator (R := R) (M := M)
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨n, f, hf⟩ := Module.exists_injective_quotient_annihilator_pi R M
    exact isArtinian_of_tower R (isArtinian_of_injective f hf)
  · have := Module.Finite.of_restrictScalars_finite R (R ⧸ Module.annihilator R M) M
    have : IsArtinian (R ⧸ Module.annihilator R M) M := isArtinian_of_fg_of_artinian'
    exact isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := Module.annihilator R M))

/-- A finitely generated module is Noetherian iff the quotient of the base ring by its
annihilator is a Noetherian ring. -/
theorem isNoetherian_iff_isNoetherianRing_quotient_annihilator [Module.Finite R M] :
    IsNoetherian R M ↔ IsNoetherianRing (R ⧸ Module.annihilator R M) := by
  let _ := Module.quotientAnnihilator (R := R) (M := M)
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · obtain ⟨n, f, hf⟩ := Module.exists_injective_quotient_annihilator_pi R M
    exact isNoetherian_of_tower R (isNoetherian_of_injective f hf)
  · have := Module.Finite.of_restrictScalars_finite R (R ⧸ Module.annihilator R M) M
    exact ((Module.isTorsionBySet_annihilator R M).semilinearMap.isNoetherian_iff_of_bijective
      Function.bijective_id).mpr inferInstance

instance IsNoetherian.isNoetherianRing_quotient_annihilator [IsNoetherian R M] :
    IsNoetherianRing (R ⧸ Module.annihilator R M) :=
  isNoetherian_iff_isNoetherianRing_quotient_annihilator.mp ‹_›

instance IsArtinian.isArtinianRing_quotient_annihilator [Module.Finite R M] [IsArtinian R M] :
    IsArtinianRing (R ⧸ Module.annihilator R M) :=
  isArtinian_iff_isArtinianRing_quotient_annihilator.mp ‹_›
