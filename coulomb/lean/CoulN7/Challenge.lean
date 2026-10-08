import ThomsonGen.Preamble

/-!
# Coulomb energy of 7 points on the sphere (challenge statement)

Among all configurations of 7 pairwise distinct unit vectors in `ℝ³`, the regular pentagonal bipyramid minimises
the Coulomb energy `∑_{i<j} ‖x i − x j‖⁻¹`, uniquely up to an orthogonal map of `ℝ³` and a relabelling.

The definitions `R3`, `SphereConfig`, `cyl`, `pentBipyramid` and `coulombEnergy` (namespace `ThomsonN7`) are those
of the Coulomb formalisation huwngtran/thomson-n7-lean @ 25f2fa5, imported from `ThomsonGen/Preamble.lean`, which
`regen.sh` regenerates from upstream. The statements are upstream's `thomson_seven` and `thomson_seven_unique`.
This package checks them a second time with its own certificates (Case 1, five slabs, cap); the local lemma and
the generic machinery (ring rigidity, gauge, certificate soundness) are upstream's, regenerated.
-/

open Real

namespace ThomsonN7S1

open ThomsonN7

theorem coulomb_seven :
    ∀ x ∈ SphereConfig 7, coulombEnergy pentBipyramid ≤ coulombEnergy x := by
  sorry

theorem coulomb_seven_unique :
    ∀ x ∈ SphereConfig 7, coulombEnergy x = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

end ThomsonN7S1
