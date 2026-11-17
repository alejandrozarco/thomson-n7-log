import RieszN7.Basic

/-!
# Comparator negative control 2 (must be REJECTED): extra axiom

The challenge statements, verbatim, "proved" from an added axiom `ThomsonN7Riesz.full_cheat : False` (no `sorry`).
The statements match, so the expected rejection is the axiom check (`full_cheat` is not among
`propext, Quot.sound, Classical.choice`). Private, AI-written (2026-11-11).
-/

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

axiom full_cheat : False

theorem riesz_seven_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x :=
  full_cheat.elim

theorem riesz_seven_unique_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  full_cheat.elim

end ThomsonN7Riesz
