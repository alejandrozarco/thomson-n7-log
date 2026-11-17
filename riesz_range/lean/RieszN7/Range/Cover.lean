import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# `RieszN7.Range.Cover` — gluing statements on adjacent closed s-intervals

Hand-written (Phase 2a, 2026-11-08; private, AI-written; AI-produced, not peer-reviewed; AI-reviewed 2026-11-12 (`plan_range/REVIEW_fable_range.md`)).  `Icc_cover`: a property holding on
`[a, b]` and on `[b, c]` holds on `[a, c]`.  The per-cell chain modules `RieszN7.Range.Cells.*` fold it over the
pieces of a cell.
-/

namespace RieszN7.Range

theorem Icc_cover {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ s ∈ Set.Icc a b, P s) (h2 : ∀ s ∈ Set.Icc b c, P s) :
    ∀ s ∈ Set.Icc a c, P s := by
  rintro s ⟨h0, h3⟩
  rcases le_total s b with h | h
  · exact h1 s ⟨h0, h⟩
  · exact h2 s ⟨h, h3⟩

end RieszN7.Range
