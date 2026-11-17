import ThomsonGen.Generic.Energy
import RieszN7.Basic

/-!
# The Riesz energy as a pair energy (LEAN_PLAN_range.md §1.2; deferred from Phase 1, PHASE1_RESULTS.md §4.4)

* `rieszEnergy_eq_pairEnergy`: for unit vectors, `rieszEnergy s x = pairEnergy (phiS s) x`, the form consumed by the
  generic glue (`ThomsonGen.Generic.Glue`, `ThomsonGen.Main`).
* `pairEnergy_pent`: `E_s(P)` in `phiS` form at the four contact values.

Private working module (2026-11-07), AI-written, not reviewed.
-/

namespace RieszN7

open ThomsonN7 ThomsonN7.Base ThomsonGen

theorem rieszEnergy_eq_pairEnergy (s : ℝ) {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    rieszEnergy s x = pairEnergy (phiS s) x := by
  rw [rieszEnergy_eq_sum_phiS s hx]
  rfl

theorem pairEnergy_pent (s : ℝ) :
    pairEnergy (phiS s) pentBipyramid
      = phiS s (-1) + 10 * phiS s 0 + 5 * phiS s c1 + 5 * phiS s c2 := by
  rw [← rieszEnergy_eq_pairEnergy s pent_norm, rieszEnergy_pent]

end RieszN7
