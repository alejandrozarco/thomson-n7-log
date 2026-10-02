/-
LogN7/Main.lean — the log-energy theorem for N = 7.

  * `LocalMinAt φ₀ (11/2 · 1/1650)` (radius 1/300) from `LocalHandoff.pent_local_min_sup_log`;
  * `seven_of_specs` with the breakpoints of upstream `Final.a`;
  * transfer of `Main φ₀` to `logEnergy` (as for the Coulomb energy in upstream `thomson_seven(_unique)`).
-/
import LogN7.Case1.Claim
import LogN7.Cap.Spec
import LogN7.S9998.Spec
import LogN7.S9896.Spec
import LogN7.S9694.Spec
import LogN7.S9493.Spec
import LogN7.S9390.Spec
import LogLean.LocalHandoff

open Real

namespace LogN7

open ThomsonN7 ThomsonGen

/-- The breakpoints `a 0 < … < a 5 = -9/10` (same as upstream `Final.a`). -/
noncomputable def a : ℕ → ℝ
  | 0 => (-99 / 100 : ℝ)
  | 1 => (-49 / 50 : ℝ)
  | 2 => (-24 / 25 : ℝ)
  | 3 => (-47 / 50 : ℝ)
  | 4 => (-93 / 100 : ℝ)
  | _ => (-9 / 10 : ℝ)

def K : ℕ := 5

theorem hK : -9 / 10 ≤ a K := by norm_num [a, K]

theorem hslab : ∀ k, k < K → SlabSpec LogLean.Minor.phi (a k) (a (k + 1)) := by
  intro k hk
  unfold K at hk
  interval_cases k
  · exact S9998.spec
  · exact S9896.spec
  · exact S9694.spec
  · exact S9493.spec
  · exact S9390.spec

theorem hcap : CapSpec LogLean.Minor.phi (1 / 1650) (a 0) := Cap.spec

/-- Lemma L′ (radius `(11/2)·(1/1650) = 1/300`) in the generic form. -/
theorem localMinAt : LocalMinAt LogLean.Minor.phi (11 / 2 * (1 / 1650)) := by
  have h : (11 / 2 * (1 / 1650 : ℝ)) = 1 / 300 := by norm_num
  rw [h]
  intro z hz hzd
  rw [← logEnergy_eq_pairEnergy hz.1, ← logEnergy_eq_pairEnergy Base.pent_norm]
  exact LocalHandoff.pent_local_min_sup_log hz hzd

theorem main : ThomsonGen.Main LogLean.Minor.phi :=
  seven_of_specs LogLean.Minor.phi (τ₀ := 1 / 1650) (by norm_num) localMinAt Case1.claim a K hK
    hcap hslab

/-- **Log energy, N = 7 (minimality).** -/
theorem thomson_seven_log :
    ∀ x ∈ SphereConfig 7, logEnergy pentBipyramid ≤ logEnergy x := by
  intro x hx
  have h := main.1 x hx
  rwa [← logEnergy_eq_pairEnergy hx.1, ← logEnergy_eq_pairEnergy Base.pent_norm] at h

/-- **Log energy, N = 7 (uniqueness)** up to an orthogonal map and a relabelling. -/
theorem thomson_seven_log_unique :
    ∀ x ∈ SphereConfig 7, logEnergy x = logEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  intro x hx hE
  refine main.2 x hx ?_
  rw [← logEnergy_eq_pairEnergy hx.1, ← logEnergy_eq_pairEnergy Base.pent_norm]
  exact hE

end LogN7
