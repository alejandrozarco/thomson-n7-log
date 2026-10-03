import Riesz2.Main

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`riesz2Energy` ← `coulombEnergy`. -/

/-!
# Solution of `Riesz2/Challenge.lean`

Same statements, same definitions: `ThomsonN7.R3/SphereConfig/cyl/pentBipyramid` come from the regenerated upstream
preamble `ThomsonGen.Preamble`, which `Riesz2/Challenge.lean` imports as well, and `ThomsonN7Riesz2.riesz2Energy` below
is the challenge's definition verbatim (definitionally `Riesz2.riesz2Energy`).
-/

open Real

namespace ThomsonN7Riesz2

open ThomsonN7

/-- Riesz `s = 2` energy `∑_{i<j} ‖x i - x j‖⁻²`. -/
noncomputable def riesz2Energy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (‖x i - x j‖ ^ 2)⁻¹

theorem riesz2_seven :
    ∀ x ∈ SphereConfig 7, riesz2Energy pentBipyramid ≤ riesz2Energy x :=
  Riesz2.riesz2_seven

theorem riesz2_seven_unique :
    ∀ x ∈ SphereConfig 7, riesz2Energy x = riesz2Energy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  Riesz2.riesz2_seven_unique

end ThomsonN7Riesz2
