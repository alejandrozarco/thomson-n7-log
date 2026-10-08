import CoulN7.Main

/-!
# Solution of `CoulN7/Challenge.lean`

Same statements over the same definitions (`ThomsonN7.R3/SphereConfig/pentBipyramid/coulombEnergy` from the
regenerated upstream preamble `ThomsonGen.Preamble`), proved by `CoulN7.coulomb_seven(_unique)`.
-/

open Real

namespace ThomsonN7S1

open ThomsonN7

theorem coulomb_seven :
    ∀ x ∈ SphereConfig 7, coulombEnergy pentBipyramid ≤ coulombEnergy x :=
  CoulN7.coulomb_seven

theorem coulomb_seven_unique :
    ∀ x ∈ SphereConfig 7, coulombEnergy x = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  CoulN7.coulomb_seven_unique

end ThomsonN7S1
