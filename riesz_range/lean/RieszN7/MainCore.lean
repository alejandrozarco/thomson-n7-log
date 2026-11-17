import RieszN7.Energy
import RieszN7.Range.Cap
import RieszN7.Range.Cells.Case1
import RieszN7.Range.Cells.S99_98
import RieszN7.Range.Cells.S98_96
import RieszN7.Range.Cells.S96_94
import RieszN7.Range.Cells.S94_93
import RieszN7.Range.Cells.S93_915
import RieszN7.Range.Cells.S915_90

/-!
# N = 7, Riesz s-energy, the M-core range s ∈ [1/2, 3/2]: assembly (LEAN_PLAN_range.md §1.2, Route 2)

* `seven_of_specs_sharp` (generic glue, sharp cap, no local lemma) with the six-slab breakpoints
  `-99/100, -49/50, -24/25, -47/50, -93/100, -183/200, -9/10` (K = 6), Case 1, the six slabs and the sharp cap, each
  certified for all s ∈ [1/2, 3/2] by the chain modules `RieszN7.Range.{Cells.*, Cap}`;
* transfer of `Main (phiS s)` to `rieszEnergy s` (`rieszEnergy_eq_pairEnergy`).

The full range [1/3, 7/4] extends the same chains (`RieszN7/MainFull.lean`, closed 2026-11-11). Private, AI-written
(Phase 2 parent agent, 2026-11-08). AI-produced, not peer-reviewed; AI-reviewed 2026-11-12 (`plan_range/REVIEW_fable_range.md`).
-/

open Real

namespace RieszN7.Core12

open ThomsonN7 ThomsonN7.Base ThomsonGen RieszN7

/-- The breakpoints `a 0 < … < a 6 = -9/10`. -/
noncomputable def a : ℕ → ℝ
  | 0 => (-99 / 100 : ℝ)
  | 1 => (-49 / 50 : ℝ)
  | 2 => (-24 / 25 : ℝ)
  | 3 => (-47 / 50 : ℝ)
  | 4 => (-93 / 100 : ℝ)
  | 5 => (-183 / 200 : ℝ)
  | _ => (-9 / 10 : ℝ)

def K : ℕ := 6

theorem hK : -9 / 10 ≤ a K := by norm_num [a, K]

theorem hslab (s : ℝ) (hs : s ∈ Set.Icc ((1 : ℝ) / 2) ((3 : ℝ) / 2)) :
    ∀ k, k < K → SlabSpec (phiS s) (a k) (a (k + 1)) := by
  intro k hk
  unfold K at hk
  interval_cases k
  · exact Range.Cells.S99_98.cell s hs
  · exact Range.Cells.S98_96.cell s hs
  · exact Range.Cells.S96_94.cell s hs
  · exact Range.Cells.S94_93.cell s hs
  · exact Range.Cells.S93_915.cell s hs
  · exact Range.Cells.S915_90.cell s hs

theorem main (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) : ThomsonGen.Main (phiS s) :=
  seven_of_specs_sharp (phiS s) (Range.Cells.Case1.cell s hs) a K hK (Range.Cap.cap s hs) (hslab s hs)

/-- **Riesz s-energy, N = 7, 1/2 ≤ s ≤ 3/2 (minimality).** -/
theorem riesz_seven_core (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x := by
  intro x hx
  have h := (main s hs).1 x hx
  rwa [← rieszEnergy_eq_pairEnergy s hx.1, ← rieszEnergy_eq_pairEnergy s pent_norm] at h

/-- **Riesz s-energy, N = 7, 1/2 ≤ s ≤ 3/2 (uniqueness)** up to an orthogonal map and a relabelling. -/
theorem riesz_seven_unique_core (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  intro x hx hE
  refine (main s hs).2 x hx ?_
  rw [← rieszEnergy_eq_pairEnergy s hx.1, ← rieszEnergy_eq_pairEnergy s pent_norm]
  exact hE

end RieszN7.Core12
