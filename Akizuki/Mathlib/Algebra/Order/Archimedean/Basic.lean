/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# An Archimedean comparison lemma

If `n • a ≤ n • b + c` for all `n : ℕ`, then `a ≤ b`.
-/

public section

/-- In an Archimedean ordered monoid, if `n • a ≤ n • b + c` for all `n : ℕ`, then `a ≤ b`. -/
theorem le_of_forall_nsmul_le_nsmul_add {M : Type*} [AddCommMonoid M] [LinearOrder M]
    [AddLeftStrictMono M] [AddLeftReflectLT M] [ExistsAddOfLE M] [Archimedean M] {a b c : M}
    (h : ∀ n : ℕ, n • a ≤ n • b + c) : a ≤ b := by
  refine le_of_not_gt fun hba => ?_
  obtain ⟨d, hdpos, rfl⟩ := exists_pos_add_of_lt' hba
  obtain ⟨n, hn⟩ := exists_lt_nsmul hdpos c
  exact not_lt_of_ge (h n) <| nsmul_add b d n ▸ add_lt_add_right hn _
