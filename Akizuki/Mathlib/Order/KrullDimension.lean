/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Order.ScottContinuity

/-!
# Scott continuity of height

## Main results

* `Order.scottContinuous_height`: the height function `Order.height : α → ℕ∞` is Scott
  continuous.
* `Order.height_iSup_of_directed`: hence height commutes with directed suprema.
-/

public section

namespace Order

variable {α : Type*} [Preorder α]

/-- A nonempty directed set on which `Order.height` has finite supremum has a greatest
element. -/
theorem _root_.DirectedOn.exists_isGreatest_of_iSup_height_ne_top {d : Set α}
    (hdir : DirectedOn (· ≤ ·) d) (hne : d.Nonempty) (hd : ⨆ x ∈ d, height x ≠ ⊤) :
    ∃ x, IsGreatest d x := by
  rw [← sSup_image] at hd
  have : Nonempty ↥(height '' d) := (hne.image height).to_subtype
  obtain ⟨x, hx, hxe⟩ := ENat.sSup_mem_of_nonempty_of_lt_top hd.lt_top
  refine ⟨x, hx, fun y hy => ?_⟩
  obtain ⟨z, hz, hyz, hxz⟩ := hdir y hy x hx
  refine hyz.trans <| not_lt_iff_le_imp_ge.mp (fun hlt => ?_) hxz
  exact (height_strictMono hlt (hxe.trans_lt hd.lt_top)).not_ge <|
    hxe ▸ le_sSup (Set.mem_image_of_mem height hz)

/-- The height function is Scott continuous. -/
theorem scottContinuous_height : ScottContinuous (height : α → ℕ∞) := by
  intro d hne hdir a hlub
  suffices h : height a = ⨆ x ∈ d, height x by rw [h, ← sSup_image]; exact isLUB_sSup _
  refine le_antisymm ?_ (iSup₂_le fun x hx => height_mono (hlub.1 hx))
  rcases eq_or_ne (⨆ x ∈ d, height x) ⊤ with hS | hS
  · exact hS ▸ le_top
  · obtain ⟨x, hxd, hxub⟩ := hdir.exists_isGreatest_of_iSup_height_ne_top hne hS
    exact (height_mono (hlub.2 hxub)).trans (le_iSup₂ (f := fun x _ => height x) x hxd)

/-- Height commutes with directed suprema. -/
theorem height_iSup_of_directed {ι : Sort*} {β : Type*} [CompleteLattice β] {f : ι → β}
    (hf : Directed (· ≤ ·) f) : height (⨆ i, f i) = ⨆ i, height (f i) := by
  cases isEmpty_or_nonempty ι
  · simp
  have := scottContinuous_height (Set.range_nonempty f) hf.directedOn_range isLUB_iSup
  rw [← Set.range_comp] at this
  exact this.iSup_eq.symm

end Order
