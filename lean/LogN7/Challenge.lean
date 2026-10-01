import ThomsonGen.Preamble

/-!
# Logarithmic energy of 7 points on the sphere (challenge statement)

Among all configurations of 7 pairwise distinct unit vectors in `ℝ³`, the regular pentagonal
bipyramid minimises the logarithmic energy `∑_{i<j} −log ‖x i − x j‖`, uniquely up to an orthogonal
map of `ℝ³` and a relabelling of the points.

The definitions `R3`, `SphereConfig`, `cyl`, `pentBipyramid` (namespace `ThomsonN7`) are those of the Coulomb
formalisation, imported from `ThomsonGen/Preamble.lean`, which `regen.sh` regenerates from upstream
(huwngtran/thomson-n7-lean @ 25f2fa5) and checks against `ThomsonGen/scripts/generated.sha256`. `logEnergy` is the logarithmic
energy, adapted from upstream `coulombEnergy`; the statements follow upstream `thomson_seven` and `thomson_seven_unique`.
Injectivity in `SphereConfig` rules out coincident points (where Lean's `log 0 = 0`).
-/

open Real


namespace ThomsonN7Log

open ThomsonN7

/-- Logarithmic energy `∑_{i<j} −log ‖x i − x j‖`. -/
noncomputable def logEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, -Real.log ‖x i - x j‖

theorem thomson_seven_log :
    ∀ x ∈ SphereConfig 7, logEnergy pentBipyramid ≤ logEnergy x := by
  sorry

theorem thomson_seven_log_unique :
    ∀ x ∈ SphereConfig 7, logEnergy x = logEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

end ThomsonN7Log
