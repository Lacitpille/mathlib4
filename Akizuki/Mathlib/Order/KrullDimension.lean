/-
Copyright (c) 2026 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Order.ScottContinuity.Complete

/-!
# Scott continuity of height

We show that `Order.height` is Scott continuous, and deduce that it commutes with suprema of
monotone functions over a directed index type.
-/

public section

namespace Order

/-- A nonempty directed set whose image under `Order.height` has finite supremum has a greatest
element. -/
theorem exists_isGreatest_of_sSup_height_ne_top {α : Type*} [PartialOrder α] {d : Set α}
    (hne : d.Nonempty) (hdir : DirectedOn (· ≤ ·) d) (hd : sSup (height '' d) ≠ ⊤) :
    ∃ x, IsGreatest d x := by
  haveI : Nonempty ↥(height '' d) := (hne.image height).to_subtype
  obtain ⟨x, hx, hxe⟩ := ENat.sSup_mem_of_nonempty_of_lt_top (lt_top_iff_ne_top.mpr hd)
  refine ⟨x, hx, fun y hy => ?_⟩
  obtain ⟨z, hz, hyz, hxz⟩ := hdir y hy x hx
  rcases eq_or_lt_of_le hxz with rfl | hlt
  · exact hyz
  · exact absurd (height_strictMono hlt (hxe.trans_lt (lt_top_iff_ne_top.mpr hd)))
      (not_lt.mpr ((le_sSup (Set.mem_image_of_mem height hz)).trans_eq hxe.symm))

/-- The height function on a partial order is Scott continuous. -/
theorem scottContinuous_height {α : Type*} [PartialOrder α] :
    ScottContinuous (Order.height : α → ℕ∞) := by
  intro d hne hdir a hlub
  suffices h : height a = sSup (height '' d) by rw [h]; exact isLUB_sSup _
  refine le_antisymm ?_ (sSup_le fun _ ⟨x, hx, hxe⟩ => hxe ▸ height_mono (hlub.1 hx))
  rcases eq_or_ne (sSup (height '' d)) ⊤ with hS | hS
  · exact hS ▸ le_top
  · obtain ⟨x, hxd, hxub⟩ := exists_isGreatest_of_sSup_height_ne_top hne hdir hS
    rw [le_antisymm (hlub.2 hxub) (hlub.1 hxd)]
    exact le_sSup (Set.mem_image_of_mem height hxd)

/-- Height commutes with suprema of monotone functions over a directed index type. -/
theorem height_iSup_of_monotone {α ι : Type*} [CompleteLattice α] [Nonempty ι] [Preorder ι]
    [IsDirected ι (· ≤ ·)] {f : ι → α} (hf : Monotone f) :
    height (⨆ i, f i) = ⨆ i, height (f i) := by
  have hmap := (scottContinuous_height (α := α)).map_sSup (d := Set.range f)
    (Set.range_nonempty f) hf.directed_le.directedOn_range
  rw [sSup_range, ← Set.range_comp, sSup_range] at hmap
  simpa [Function.comp_def] using hmap

end Order
