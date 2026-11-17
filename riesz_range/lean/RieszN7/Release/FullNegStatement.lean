import RieszN7.Basic

/-!
# Comparator negative control 1 (must be REJECTED): changed statement

`riesz_seven_range` is stated for `1 / 4 ≤ s` instead of `1 / 3 ≤ s`; everything else is as in the challenge. The proofs
are `sorry`. Comparator compares statements before it checks axioms, so the expected rejection is the statement
mismatch of `ThomsonN7Riesz.riesz_seven_range`. Private, AI-written (2026-11-11).
-/

open Real

namespace ThomsonN7Riesz

open ThomsonN7 RieszN7

theorem riesz_seven_range (s : ℝ) (hs : 1 / 4 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s pentBipyramid ≤ rieszEnergy s x := by
  sorry

theorem riesz_seven_unique_range (s : ℝ) (hs : 1 / 3 ≤ s ∧ s ≤ 7 / 4) :
    ∀ x ∈ SphereConfig 7, rieszEnergy s x = rieszEnergy s pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  sorry

end ThomsonN7Riesz
