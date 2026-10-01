import LogN7.Main

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`logEnergy` ← `coulombEnergy`. -/

/-!
# Solution of `LogN7/Challenge.lean`

Same statements, same definitions: `ThomsonN7.R3/SphereConfig/cyl/pentBipyramid` are upstream's
preamble (`ThomsonGen.Preamble`; the challenge's copies of these four definitions are textually identical), and `ThomsonN7Log.logEnergy`
below is the challenge's definition verbatim (definitionally `LogN7.logEnergy`).
-/

open Real

namespace ThomsonN7Log

open ThomsonN7

/-- Logarithmic energy `∑_{i<j} −log ‖x i − x j‖`. -/
noncomputable def logEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, -Real.log ‖x i - x j‖

theorem thomson_seven_log :
    ∀ x ∈ SphereConfig 7, logEnergy pentBipyramid ≤ logEnergy x :=
  LogN7.thomson_seven_log

theorem thomson_seven_log_unique :
    ∀ x ∈ SphereConfig 7, logEnergy x = logEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  LogN7.thomson_seven_log_unique

end ThomsonN7Log
