/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Akizuki.Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Akizuki.Mathlib.RingTheory.Length

/-!
# The length of `M ⧸ xM`

We compute the length of `QuotSMulTop x M = M ⧸ xM` for `x` regular on `M`.

## Main results

* `Module.length_quotSMulTop_eq_of_isFiniteLength_quotient`: if `M ⧸ E` has finite length, then
  `length (M ⧸ xM) = length (E ⧸ xE)`.
* `Module.length_quotSMulTop_of_free`: for `M` free,
  `length (M ⧸ xM) = rank M * length (R ⧸ (x))`.
* `Module.IsTorsion.isFiniteLength`: a finite torsion module over a Noetherian ring of Krull
  dimension at most one has finite length.
* `Module.length_quotSMulTop_eq_toENat_rank_mul`, `Module.length_quotSMulTop_le_toENat_rank_mul`:
  over a Noetherian domain of Krull dimension at most one, `length (M ⧸ xM) = rank M * length
  (R ⧸ (x))` for `M` finite, and `≤` in general.
* `Module.isFiniteLength_quotSMulTop`: hence `M ⧸ xM` has finite length if `M` has finite rank.

The last three results are the lemma in the proof of the Krull–Akizuki theorem in
[Matsumura, *Commutative Ring Theory*, Theorem 11.7][matsumura1987]. The right-hand side
`length R (R ⧸ Ideal.span {x})` is `Ring.ord R x`.

## Implementation notes

In general only the inequality holds: for `M = Frac R` and a nonzero nonunit `x`, `M ⧸ xM = 0`.
It is deduced from the finite case by writing `M ⧸ xM` as the directed union of the images of
the finitely generated submodules of `M`.
-/

public section

open scoped Pointwise nonZeroDivisors

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For `x` regular on `M`: `length (M ⧸ xN) = length (M ⧸ N) + length (M ⧸ xM)`. -/
theorem length_quotient_smul_eq_add_of_isSMulRegular {x : R} (N : Submodule R M)
    (hx : IsSMulRegular M x) :
    length R (M ⧸ x • N) = length R (M ⧸ N) + length R (QuotSMulTop x M) := by
  have h := length_quotient_map_eq_add_quotient_range (DistribSMul.toLinearMap R M x) hx N
  rwa [← Submodule.pointwise_smul_def, LinearMap.range_eq_map,
    ← Submodule.pointwise_smul_def] at h

/-- `length (M ⧸ xE) = length (E ⧸ xE) + length (M ⧸ E)`. -/
theorem length_quotient_smul_eq_add (E : Submodule R M) (x : R) :
    length R (M ⧸ x • E) = length R (QuotSMulTop x E) + length R (M ⧸ E) := by
  have h := length_quotient_map_eq_add_quotient_range E.subtype E.injective_subtype
    (x • (⊤ : Submodule R E))
  rwa [Submodule.map_pointwise_smul, Submodule.map_subtype_top, Submodule.range_subtype] at h

/-- If `M ⧸ E` has finite length and `x` is regular on `M`, then
`length (M ⧸ xM) = length (E ⧸ xE)`. -/
theorem length_quotSMulTop_eq_of_isFiniteLength_quotient (E : Submodule R M)
    (hME : IsFiniteLength R (M ⧸ E)) {x : R} (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) = length R (QuotSMulTop x E) := by
  have h := length_quotient_smul_eq_add_of_isSMulRegular E hx
  rw [length_quotient_smul_eq_add, add_comm (length R (QuotSMulTop x E))] at h
  exact (WithTop.add_left_cancel (length_ne_top_iff.mpr hME) h).symm

/-- For a free module `M`, `length (M ⧸ xM) = rank M * length (R ⧸ (x))`. -/
theorem length_quotSMulTop_of_free [Module.Free R M] (x : R) :
    length R (QuotSMulTop x M) = (Module.rank R M).toENat * length R (R ⧸ Ideal.span {x}) := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  rw [(QuotSMulTop.equivTensorQuot x M ≪≫ₗ b.repr.rTensor _ ≪≫ₗ
    TensorProduct.finsuppScalarLeft R _ _).length_eq, length_finsupp,
    Free.rank_eq_card_chooseBasisIndex, ENat.card]

section KrullDimLE

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/- This is upstream `isFiniteLength_quotient_span_singleton`, which lives in the much heavier
`Mathlib.RingTheory.OrderOfVanishing.Basic` (it imports power series). When upstreaming, move
that lemma here with this proof instead of keeping a private copy. -/
private theorem isFiniteLength_quotient_span_singleton_aux {x : R} (hx : x ∈ R⁰) :
    IsFiniteLength R (R ⧸ Ideal.span {x}) := by
  have : Ring.KrullDimLE 0 (R ⧸ Ideal.span {x}) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun J hJ =>
      hJ.1.1.isMaximal_of_mem_nonZeroDivisors hx (hJ.1.2 (Ideal.mem_span_singleton_self x))
  have : IsArtinianRing (R ⧸ Ideal.span {x}) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_quotient _,
      isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := .span {x}))⟩

/-- A finite torsion module over a Noetherian ring of Krull dimension at most one has finite
length. The case `M = R ⧸ (x)` is `isFiniteLength_quotient_span_singleton`. -/
theorem IsTorsion.isFiniteLength [Module.Finite R M] (hM : IsTorsion R M) :
    IsFiniteLength R M := by
  obtain ⟨x, hxann, hx⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have h0 : x • (⊤ : Submodule R M) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, -, rfl⟩
    exact (Submodule.mem_bot R).mpr (Submodule.mem_annihilator.mp hxann y trivial)
  have hpi : IsFiniteLength R (QuotSMulTop x (Fin n → R)) := by
    nontriviality R
    rw [← length_ne_top_iff, length_quotSMulTop_of_free]
    exact WithTop.mul_ne_top (Cardinal.toENat_ne_top.mpr (rank_lt_aleph0 R _))
      (length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton_aux hx))
  exact (Submodule.quotEquivOfEqBot _ h0).isFiniteLength
    (hpi.of_surjective (QuotSMulTop.map_surjective x hf))

variable [IsDomain R]

/-- Over a Noetherian domain of Krull dimension at most one, for a finite module `M` and `x`
regular on `M`: `length (M ⧸ xM) = rank M * length (R ⧸ (x))`. -/
theorem length_quotSMulTop_eq_toENat_rank_mul [Module.Finite R M] {x : R}
    (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) = (Module.rank R M).toENat * length R (R ⧸ Ideal.span {x}) := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent_of_isDomain R M
  have hv : LinearIndependent R ((↑) : s → M) := hli
  set E := Submodule.span R (Set.range ((↑) : s → M))
  have hE : Module.rank R E = Module.rank R M := by rw [rank_span hv, Subtype.range_coe, hs]
  have htors : IsTorsion R (M ⧸ E) := by
    have h := E.rank_quotient_add_rank
    rw [hE] at h
    simpa [IsTorsion, rank_eq_zero_iff] using
      Cardinal.eq_of_add_eq_add_right (h.trans (zero_add _).symm) (rank_lt_aleph0 R M)
  have := Module.Free.of_basis (Basis.span hv)
  rw [length_quotSMulTop_eq_of_isFiniteLength_quotient E htors.isFiniteLength hx,
    length_quotSMulTop_of_free, hE]

/-- `finrank` version of `Module.length_quotSMulTop_eq_toENat_rank_mul`. -/
theorem length_quotSMulTop_eq_finrank_mul [Module.Finite R M] {x : R}
    (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) = finrank R M * length R (R ⧸ Ideal.span {x}) := by
  rw [length_quotSMulTop_eq_toENat_rank_mul hx,
    Cardinal.toENat_eq_natCast.mpr (finrank_eq_rank _ _).symm]

/-- Over a Noetherian domain of Krull dimension at most one, for `x` regular on `M`:
`length (M ⧸ xM) ≤ rank M * length (R ⧸ (x))`. -/
theorem length_quotSMulTop_le_toENat_rank_mul {x : R} (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) ≤ (Module.rank R M).toENat * length R (R ⧸ Ideal.span {x}) := by
  rw [length_eq_iSup_fg]
  refine iSup_le fun ⟨P, hP⟩ ↦ ?_
  obtain ⟨N, hN, rfl⟩ := hP.exists_fg_map_eq_of_surjective _ (Submodule.mkQ_surjective _)
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have hle : N.map (Submodule.mkQ _) ≤ LinearMap.range (QuotSMulTop.map x N.subtype) := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨n, hn⟩, rfl⟩
  calc length R (N.map (Submodule.mkQ _))
      ≤ length R (LinearMap.range (QuotSMulTop.map x N.subtype)) :=
        length_le_of_injective _ (Submodule.inclusion_injective hle)
    _ ≤ length R (QuotSMulTop x N) :=
        length_le_of_surjective _ (QuotSMulTop.map x N.subtype).surjective_rangeRestrict
    _ = (Module.rank R N).toENat * length R (R ⧸ Ideal.span {x}) :=
        length_quotSMulTop_eq_toENat_rank_mul (hx.submodule N)
    _ ≤ _ := by grw [Submodule.rank_le N]

/-- Over a Noetherian domain of Krull dimension at most one, if `M` has finite rank and `x` is
regular on `M`, then `M ⧸ xM` has finite length. -/
theorem isFiniteLength_quotSMulTop {x : R} (hx : IsSMulRegular M x)
    (hM : Module.rank R M < Cardinal.aleph0) : IsFiniteLength R (QuotSMulTop x M) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have : Subsingleton M := ⟨fun a b => hx (by simp)⟩
    exact .of_subsingleton
  refine length_ne_top_iff.mp (ne_top_of_le_ne_top ?_ (length_quotSMulTop_le_toENat_rank_mul hx))
  exact WithTop.mul_ne_top (Cardinal.toENat_ne_top.mpr hM) <| length_ne_top_iff.mpr <|
    isFiniteLength_quotient_span_singleton_aux (mem_nonZeroDivisors_of_ne_zero hx0)

end KrullDimLE

end Module
