import RieszN7.MainFull

/-!
# Solution of `RieszN7/Release/FullChallenge.lean`

Same statements over the same definitions (`ThomsonN7.R3/SphereConfig/pentBipyramid` of `ThomsonGen.Preamble`,
`RieszN7.rieszEnergy` of `RieszN7.Basic`), proved by `RieszN7.Full.riesz_seven_range` / `riesz_seven_unique_range`
(`RieszN7/MainFull.lean`). Private, AI-written (2026-11-11).
AI-produced, not peer-reviewed; AI-reviewed 2026-11-12 (`plan_range/REVIEW_fable_range.md`).
-/

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

theorem riesz_seven_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x :=
  RieszN7.Full.riesz_seven_range s hs

theorem riesz_seven_unique_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  RieszN7.Full.riesz_seven_unique_range s hs

end ThomsonN7Riesz
