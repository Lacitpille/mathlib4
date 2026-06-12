/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.ENat.Basic
public import Akizuki.Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Archimedean comparison in `WithTop` and `ℕ∞`

The lemma `le_of_forall_nsmul_le_nsmul_add` transferred to `WithTop α` and specialized to `ℕ∞`.
-/

public section

namespace WithTop

/-- In `WithTop α` with `α` Archimedean, if `n • a ≤ n • b + c` for all `n : ℕ` with `c ≠ ⊤`,
then `a ≤ b`. -/
theorem le_of_forall_nsmul_le_nsmul_add {α : Type*} [AddCommMonoid α] [LinearOrder α]
    [AddLeftStrictMono α] [AddLeftReflectLT α] [ExistsAddOfLE α] [Archimedean α]
    {a b : WithTop α} {c : α} (h : ∀ n : ℕ, n • a ≤ n • b + c) : a ≤ b := by
  induction b with
  | top => exact le_top
  | coe B =>
    induction a with
    | top => exact absurd (by simpa [one_nsmul] using h 1) (not_top_le_coe (B + c))
    | coe A =>
      exact coe_le_coe.mpr <| _root_.le_of_forall_nsmul_le_nsmul_add fun n => mod_cast h n

end WithTop

namespace ENat

/-- In `ℕ∞`, if `n * a ≤ n * b + c` for all `n : ℕ` with `c ≠ ⊤`, then `a ≤ b`. -/
theorem le_of_forall_natCast_mul_le_natCast_mul_add {a b c : ℕ∞} (hc : c ≠ ⊤)
    (h : ∀ n : ℕ, n * a ≤ n * b + c) : a ≤ b := by
  obtain ⟨_, rfl⟩ := ENat.ne_top_iff_exists.mp hc
  exact WithTop.le_of_forall_nsmul_le_nsmul_add <| by simpa

end ENat
