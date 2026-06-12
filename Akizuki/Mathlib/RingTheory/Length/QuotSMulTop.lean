/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Akizuki.Mathlib.Algebra.Module.Submodule.Pointwise
public import Akizuki.Mathlib.Algebra.Module.Torsion.Basic
public import Akizuki.Mathlib.Algebra.Order.Archimedean.WithTop
public import Akizuki.Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Akizuki.Mathlib.RingTheory.Length
public import Akizuki.Mathlib.RingTheory.OrderOfVanishing.Basic
public import Akizuki.Mathlib.RingTheory.QuotSMulTop

/-!
# Length bounds for reductions modulo a regular element

For `x` regular on `M` we relate the length of `QuotSMulTop x M = M ⧸ xM` to lengths of
reductions of submodules, culminating in the bound
`length (M ⧸ xM) ≤ rank M * length (R ⧸ xR)` over a Noetherian domain of Krull dimension ≤ 1.
-/

public section

open scoped Pointwise

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For `x` regular on `M`: `length (M ⧸ xN) = length (M ⧸ N) + length (M ⧸ xM)`. -/
theorem length_quotient_smul_eq_add_of_isSMulRegular {x : R} (N : Submodule R M)
    (hx : IsSMulRegular M x) :
    length R (M ⧸ x • N) = length R (M ⧸ N) + length R (QuotSMulTop x M) := by
  have h := length_quotient_map_eq_add_quotient_range (LinearMap.lsmul R M x) hx N
  rwa [Submodule.map_lsmul, LinearMap.range_eq_map, Submodule.map_lsmul] at h

/-- For `x` regular on `M`: `length (M ⧸ xⁿM) = n * length (M ⧸ xM)`. -/
theorem length_quotSMulTop_pow {x : R} (hx : IsSMulRegular M x) (n : ℕ) :
    length R (QuotSMulTop (x ^ n) M) = n * length R (QuotSMulTop x M) := by
  induction n with
  | zero => simp [QuotSMulTop]
  | succ n ih =>
    calc length R (QuotSMulTop (x ^ (n + 1)) M)
        = length R (M ⧸ x • (x ^ n • (⊤ : Submodule R M))) := by rw [← mul_smul, ← pow_succ']
      _ = length R (M ⧸ x ^ n • (⊤ : Submodule R M)) + length R (QuotSMulTop x M) :=
          length_quotient_smul_eq_add_of_isSMulRegular _ hx
      _ = (n + 1 : ℕ) * length R (QuotSMulTop x M) := by
          rw [ih, Nat.cast_succ, add_mul, one_mul]

/-- Length of a product reduced modulo `x`. -/
theorem length_quotSMulTop_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (x : R) :
    length R (QuotSMulTop x (ι → R)) = ENat.card ι * length R (QuotSMulTop x R) := by
  rw [(QuotSMulTop.piEquiv (M := fun _ : ι => R) x).length_eq, length_pi]

/-- The reduction of `M` modulo `x` is bounded by the corresponding reduction of a submodule
`E` plus `length (M ⧸ E)`. -/
theorem length_quotSMulTop_le_submodule_add_quotient (E : Submodule R M) (x : R) :
    length R (QuotSMulTop x M) ≤ length R (QuotSMulTop x E) + length R (M ⧸ E) := by
  have hlen := length_le_add_of_exact _ _ <| QuotSMulTop.map_exact (r := x)
    (LinearMap.exact_subtype_mkQ E) E.mkQ_surjective
  have hquot : length R (QuotSMulTop x (M ⧸ E)) ≤ length R (M ⧸ E) :=
    length_le_of_surjective ((x • (⊤ : Submodule R (M ⧸ E))).mkQ) (Submodule.mkQ_surjective _)
  exact hlen.trans (add_le_add le_rfl hquot)

/-- If `M ⧸ E` has finite length and `x` is regular on `M`, then
`length (M ⧸ xM) ≤ length (E ⧸ xE)`. -/
theorem length_quotSMulTop_le_submodule_of_isFiniteLength_quotient (E : Submodule R M)
    (hME : IsFiniteLength R (M ⧸ E)) {x : R} (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) ≤ length R (QuotSMulTop x E) := by
  apply ENat.le_of_forall_natCast_mul_le_natCast_mul_add (length_ne_top_iff.mpr hME)
  intro n
  rw [← length_quotSMulTop_pow hx n, ← length_quotSMulTop_pow (hx.submodule E) n]
  exact length_quotSMulTop_le_submodule_add_quotient E (x ^ n)

variable [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- Length bound for `QuotSMulTop x M` when `M` is a finite module over a Noetherian domain
of Krull dimension at most one. -/
theorem length_quotSMulTop_le_rank_toENat_mul_of_finite [Module.Finite R M] {x : R}
    (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) ≤ (Module.rank R M).toENat * length R (QuotSMulTop x R) := by
  classical
  obtain ⟨s, hv, hmax⟩ := exists_maximal_linearIndependent R (M := M)
  have hcard : s.encard ≤ (Module.rank R M).toENat :=
    LinearIndepOn.encard_le_toENat_rank (v := id) hv
  have := (Set.encard_lt_top_iff.mp <| hcard.trans_lt <|
    Cardinal.toENat_lt_top.mpr (Module.rank_lt_aleph0 (R := R) (M := M))).fintype
  set E := Submodule.span R (Set.range (Subtype.val : s → M))
  have hfl := (hmax.isTorsion_quotient_span hv).isFiniteLength
  calc length R (QuotSMulTop x M)
      ≤ length R (QuotSMulTop x E) :=
        length_quotSMulTop_le_submodule_of_isFiniteLength_quotient E hfl hx
    _ = length R (QuotSMulTop x (s → R)) := (QuotSMulTop.congr x (Basis.span hv).equivFun).length_eq
    _ = ENat.card s * length R (QuotSMulTop x R) := length_quotSMulTop_pi x
    _ = s.encard * length R (QuotSMulTop x R) := by rw [ENat.card_coe_set_eq]
    _ ≤ (Module.rank R M).toENat * length R (QuotSMulTop x R) := by gcongr

/-- Length bound for `QuotSMulTop x M` with no finiteness hypothesis on `M`. -/
theorem length_quotSMulTop_le_rank_toENat_mul {x : R} (hx : IsSMulRegular M x) :
    length R (QuotSMulTop x M) ≤ (Module.rank R M).toENat * length R (QuotSMulTop x R) := by
  rw [length_eq_iSup_fg]
  refine iSup_le ?_
  rintro ⟨P, hP_fg⟩
  obtain ⟨N, hN_fg, rfl⟩ :=
    hP_fg.exists_fg_map_eq _ (Submodule.mkQ_surjective (x • (⊤ : Submodule R M)))
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN_fg
  have hle : N.map (Submodule.mkQ _) ≤ LinearMap.range (QuotSMulTop.map x N.subtype) := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨n, hn⟩, rfl⟩
  calc length R (N.map (Submodule.mkQ _))
      ≤ length R (LinearMap.range (QuotSMulTop.map x N.subtype)) :=
        length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ length R (QuotSMulTop x N) :=
        length_le_of_surjective (QuotSMulTop.map x N.subtype).rangeRestrict
          (QuotSMulTop.map x N.subtype).surjective_rangeRestrict
    _ ≤ (Module.rank R N).toENat * length R (QuotSMulTop x R) :=
        length_quotSMulTop_le_rank_toENat_mul_of_finite (hx.submodule N)
    _ ≤ (Module.rank R M).toENat * length R (QuotSMulTop x R) := by
        gcongr; exact Submodule.rank_le N

end Module
