import ThomsonGen.Preamble

/-!
# Riesz `s = 2` energy of 7 points on the sphere (challenge statement)

Among all configurations of 7 pairwise distinct unit vectors in `ℝ³`, the regular pentagonal
bipyramid minimises the Riesz `s = 2` energy `∑_{i<j} ‖x i − x j‖⁻²`, uniquely up to an orthogonal
map of `ℝ³` and a relabelling of the points.

The definitions `R3`, `SphereConfig`, `cyl`, `pentBipyramid` (namespace `ThomsonN7`) are those of the Coulomb
formalisation, imported from `ThomsonGen/Preamble.lean`, which `regen.sh` regenerates from upstream
(huwngtran/thomson-n7-lean @ 25f2fa5) and checks against `ThomsonGen/scripts/generated.sha256`. `riesz2Energy` is the
Riesz `s = 2` energy, adapted from upstream `coulombEnergy`; the statements follow upstream `thomson_seven` and
`thomson_seven_unique`.
-/

open Real

namespace ThomsonN7Riesz2

open ThomsonN7

/-- Riesz `s = 2` energy `∑_{i<j} ‖x i - x j‖⁻²`. -/
noncomputable def riesz2Energy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (‖x i - x j‖ ^ 2)⁻¹

theorem riesz2_seven :
    ∀ x ∈ SphereConfig 7, riesz2Energy pentBipyramid ≤ riesz2Energy x := by
  sorry

theorem riesz2_seven_unique :
    ∀ x ∈ SphereConfig 7, riesz2Energy x = riesz2Energy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

end ThomsonN7Riesz2
