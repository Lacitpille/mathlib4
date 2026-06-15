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

For a finitely generated module `M` over a commutative ring `R`, the quotient
`R ⧸ Module.annihilator R M` embeds linearly into a finite power of `M`. Consequently `M` is
an Artinian (resp. Noetherian) `R`-module if and only if `R ⧸ Module.annihilator R M` is an
Artinian (resp. Noetherian) ring.
-/

public section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If the family `s` spans `M`, then the kernel of `r ↦ (r • s i)ᵢ` is the annihilator
of `M`. -/
theorem ker_pi_toSpanSingleton_of_span_eq_top {ι : Type*} {s : ι → M}
    (hs : Submodule.span R (Set.range s) = ⊤) :
    LinearMap.ker (LinearMap.pi fun i ↦ LinearMap.toSpanSingleton R M (s i)) =
      annihilator R M := by
  simp_rw [LinearMap.ker_pi, ← Submodule.annihilator_span_singleton,
    ← Submodule.annihilator_iSup, ← Submodule.span_iUnion, Set.iUnion_singleton_eq_range, hs,
    Submodule.annihilator_top]

/-- For a finitely generated module `M`, the quotient of `R` by the annihilator of `M` embeds
linearly into a finite power of `M`. -/
theorem exists_injective_quotient_annihilator_pi [Module.Finite R M] :
    ∃ (n : ℕ) (f : (R ⧸ annihilator R M) →ₗ[R] (Fin n → M)), Function.Injective f := by
  obtain ⟨n, s, hs⟩ := Finite.exists_fin (R := R) (M := M)
  have hker := ker_pi_toSpanSingleton_of_span_eq_top hs
  exact ⟨n, (annihilator R M).liftQ _ hker.ge,
    LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ hker.le⟩

end Module

section
attribute [local instance] Module.quotientAnnihilator

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The submodule lattice of `M` over `R` is the same as over `R ⧸ Module.annihilator R M`. -/
def Submodule.orderIsoQuotientAnnihilator :
    Submodule R M ≃o Submodule (R ⧸ Module.annihilator R M) M :=
  Submodule.orderIsoMapComapOfBijective
    (Module.isTorsionBySet_annihilator R M).semilinearMap Function.bijective_id

variable {R M}

/-- A finitely generated module is Artinian iff the quotient of the base ring by its
annihilator is an Artinian ring. -/
theorem isArtinian_iff_isArtinianRing_quotient_annihilator [Module.Finite R M] :
    IsArtinian R M ↔ IsArtinianRing (R ⧸ Module.annihilator R M) := by
  constructor
  · intro h
    obtain ⟨n, f, hf⟩ := Module.exists_injective_quotient_annihilator_pi (R := R) (M := M)
    exact isArtinian_of_tower R (isArtinian_of_injective f hf)
  · intro h
    haveI : Module.Finite (R ⧸ Module.annihilator R M) M :=
      Module.Finite.of_restrictScalars_finite R _ M
    haveI : IsArtinian (R ⧸ Module.annihilator R M) M := isArtinian_of_fg_of_artinian'
    exact (Submodule.orderIsoQuotientAnnihilator R M).toOrderEmbedding.wellFoundedLT

/-- A finitely generated module is Noetherian iff the quotient of the base ring by its
annihilator is a Noetherian ring. -/
theorem isNoetherian_iff_isNoetherianRing_quotient_annihilator [Module.Finite R M] :
    IsNoetherian R M ↔ IsNoetherianRing (R ⧸ Module.annihilator R M) := by
  constructor
  · intro h
    obtain ⟨n, f, hf⟩ := Module.exists_injective_quotient_annihilator_pi (R := R) (M := M)
    exact isNoetherian_of_tower R (isNoetherian_of_injective f hf)
  · intro h
    haveI : Module.Finite (R ⧸ Module.annihilator R M) M :=
      Module.Finite.of_restrictScalars_finite R _ M
    haveI : IsNoetherian (R ⧸ Module.annihilator R M) M :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    exact isNoetherian_mk
      (Submodule.orderIsoQuotientAnnihilator R M).toOrderEmbedding.wellFoundedGT

end
