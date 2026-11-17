import RieszN7.Basic

/-!
# Comparator negative control 2 (must be REJECTED): extra axiom

The challenge statements, verbatim, "proved" from an added axiom `ThomsonN7Riesz.core12_cheat : False` (no `sorry`).
The statements match, so the expected rejection is the axiom check (`core12_cheat` is not among
`propext, Quot.sound, Classical.choice`). Private, AI-written (2026-11-10).
-/

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

axiom core12_cheat : False

theorem riesz_seven_core (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x :=
  core12_cheat.elim

theorem riesz_seven_unique_core (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3 / 2) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  core12_cheat.elim

end ThomsonN7Riesz
