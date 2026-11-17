import RieszN7.MainCore

/-!
# Solution of `RieszN7/Release/Core12Challenge.lean`

Same statements over the same definitions (`ThomsonN7.R3/SphereConfig/pentBipyramid` of `ThomsonGen.Preamble`,
`RieszN7.rieszEnergy` of `RieszN7.Basic`), proved by `RieszN7.Core12.riesz_seven_core(_unique_core)`
(`RieszN7/MainCore.lean`). Private, AI-written (2026-11-10).
AI-produced, not peer-reviewed; AI-reviewed 2026-11-12 (`plan_range/REVIEW_fable_range.md`).
-/

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

theorem riesz_seven_core (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x :=
  RieszN7.Core12.riesz_seven_core s hs

theorem riesz_seven_unique_core (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  RieszN7.Core12.riesz_seven_unique_core s hs

end ThomsonN7Riesz
