import RieszN7.Range.Cover
import RieszN7.Cap.P1o2_13o24.Closed
import RieszN7.Cap.P13o24_7o12.Closed
import RieszN7.Cap.P7o12_2o3.Closed
import RieszN7.Cap.P2o3_17o24.Closed
import RieszN7.Cap.P17o24_3o4.Closed
import RieszN7.Cap.P3o4_5o6.Closed
import RieszN7.Cap.P5o6_11o12.Closed
import RieszN7.Cap.P11o12_1o1.Closed
import RieszN7.Cap.P1o1_13o12.Closed
import RieszN7.Cap.P13o12_7o6.Closed
import RieszN7.Cap.P7o6_5o4.Closed
import RieszN7.Cap.P5o4_4o3.Closed
import RieszN7.Cap.P4o3_17o12.Closed
import RieszN7.Cap.P17o12_3o2.Closed

/-!
# `RieszN7.Range.Cap` — the cap, all of s ∈ [1/2, 3/2] (M-core)

`Range.Icc_cover` folded over the 14 closed core cap pieces `RieszN7.Cap.P*.Closed.capSharp` (Route 2, sharp), in
order of s. Written by the Phase 2 parent agent (2026-11-08); private, AI-written.
AI-produced, not peer-reviewed; AI-reviewed 2026-11-12 (`plan_range/REVIEW_fable_range.md`).
-/

namespace RieszN7.Range.Cap

open ThomsonGen RieszN7 RieszN7.Range

theorem piece0 : ∀ s ∈ Set.Icc (1 / 2 : ℝ) (13 / 24 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P1o2_13o24.Closed.capSharp s hs.1 hs.2

theorem piece1 : ∀ s ∈ Set.Icc (13 / 24 : ℝ) (7 / 12 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P13o24_7o12.Closed.capSharp s hs.1 hs.2

theorem piece2 : ∀ s ∈ Set.Icc (7 / 12 : ℝ) (2 / 3 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P7o12_2o3.Closed.capSharp s hs.1 hs.2

theorem piece3 : ∀ s ∈ Set.Icc (2 / 3 : ℝ) (17 / 24 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P2o3_17o24.Closed.capSharp s hs.1 hs.2

theorem piece4 : ∀ s ∈ Set.Icc (17 / 24 : ℝ) (3 / 4 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P17o24_3o4.Closed.capSharp s hs.1 hs.2

theorem piece5 : ∀ s ∈ Set.Icc (3 / 4 : ℝ) (5 / 6 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P3o4_5o6.Closed.capSharp s hs.1 hs.2

theorem piece6 : ∀ s ∈ Set.Icc (5 / 6 : ℝ) (11 / 12 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P5o6_11o12.Closed.capSharp s hs.1 hs.2

theorem piece7 : ∀ s ∈ Set.Icc (11 / 12 : ℝ) (1 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P11o12_1o1.Closed.capSharp s hs.1 hs.2

theorem piece8 : ∀ s ∈ Set.Icc (1 : ℝ) (13 / 12 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P1o1_13o12.Closed.capSharp s hs.1 hs.2

theorem piece9 : ∀ s ∈ Set.Icc (13 / 12 : ℝ) (7 / 6 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P13o12_7o6.Closed.capSharp s hs.1 hs.2

theorem piece10 : ∀ s ∈ Set.Icc (7 / 6 : ℝ) (5 / 4 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P7o6_5o4.Closed.capSharp s hs.1 hs.2

theorem piece11 : ∀ s ∈ Set.Icc (5 / 4 : ℝ) (4 / 3 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P5o4_4o3.Closed.capSharp s hs.1 hs.2

theorem piece12 : ∀ s ∈ Set.Icc (4 / 3 : ℝ) (17 / 12 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P4o3_17o12.Closed.capSharp s hs.1 hs.2

theorem piece13 : ∀ s ∈ Set.Icc (17 / 12 : ℝ) (3 / 2 : ℝ), CapSpecSharp (phiS s) (-99 / 100) :=
  fun s hs => RieszN7.Cap.P17o12_3o2.Closed.capSharp s hs.1 hs.2

theorem cap : ∀ s ∈ Set.Icc ((1 : ℝ) / 2) ((3 : ℝ) / 2), CapSpecSharp (phiS s) (-99 / 100) := by
  have h := piece0
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece1
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece2
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece3
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece4
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece5
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece6
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece7
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece8
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece9
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece10
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece11
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece12
  have h := Icc_cover (P := fun s => CapSpecSharp (phiS s) (-99 / 100)) h piece13
  exact h

end RieszN7.Range.Cap
