import RieszN7.Basic

/-!
# Riesz s-energy of 7 points on the sphere, 1/3 ≤ s ≤ 7/4 (Comparator challenge statement)

For every `s` with `1/3 ≤ s ≤ 7/4`, among all configurations of 7 pairwise distinct unit vectors in `ℝ³` the regular
pentagonal bipyramid minimises the Riesz `s`-energy `∑_{i<j} ‖x i − x j‖^(−s)`, uniquely up to an orthogonal map of
`ℝ³` and a relabelling.

Definitions used by the statements (nothing else is trusted):
* `ThomsonN7.R3 = EuclideanSpace ℝ (Fin 3)`, `ThomsonN7.SphereConfig n = {x | (∀ i, ‖x i‖ = 1) ∧ Injective x}`,
  `ThomsonN7.cyl`, `ThomsonN7.pentBipyramid` (equatorial pentagon at angles `2πk/5`, poles `±e₃`):
  `ThomsonGen/Preamble.lean`, regenerated from the Coulomb formalisation huwngtran/thomson-n7-lean @ 25f2fa5;
* `RieszN7.rieszEnergy s x = ∑ i, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ (-s)` (real power `Real.rpow`):
  `RieszN7/Basic.lean`.
This module imports `RieszN7.Basic` only (closure: Mathlib, `ThomsonGen.Preamble`, `ThomsonGen.Base`,
`RieszN7.Core.Rpow`, `RieszN7.Basic`; definitions and lemmas, no certificates). The proofs are in
`RieszN7/Release/FullSolution.lean`, which imports `RieszN7.MainFull`.
Private, AI-written (2026-11-11).
AI-produced, not peer-reviewed; AI-reviewed 2026-11-12 (`plan_range/REVIEW_fable_range.md`).
-/

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

theorem riesz_seven_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x := by
  sorry

theorem riesz_seven_unique_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

end ThomsonN7Riesz
