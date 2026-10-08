import CoulN7.Case1.Claim
import CoulN7.Cap.Spec
import CoulN7.S9998.Spec
import CoulN7.S9896.Spec
import CoulN7.S9694.Spec
import CoulN7.S9493.Spec
import CoulN7.S9390.Spec
import ThomsonGen.Loc2

/-!
# N = 7, Coulomb energy (s = 1): assembly

* `LocalMinAt φ₁ (11/2 · 1/165000)` (radius `1/30000`) from upstream's `Reg.pent_local_min_sup`
  (regenerated `ThomsonGen.Loc2`), transported along `coulombEnergy = pairEnergy φ₁` on unit vectors;
* `seven_of_specs` with the breakpoints of upstream `Final.a`, Case 1, the five slabs and the cap of this
  certificate chain (`numerics/n7_interval/`);
* transfer of `Main φ₁` to `coulombEnergy`.

Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`coulomb_seven`, `coulomb_seven_unique` ← `thomson_seven`, `thomson_seven_unique` (same statements; the proof here
goes through the certificate chain of this repository); `a`, `K` ← `Final.a`, `Final.K`.
-/

open Real

namespace CoulN7

open ThomsonN7 ThomsonGen

/-- The breakpoints `a 0 < … < a 5 = -9/10`. -/
noncomputable def a : ℕ → ℝ
  | 0 => (-99 / 100 : ℝ)
  | 1 => (-49 / 50 : ℝ)
  | 2 => (-24 / 25 : ℝ)
  | 3 => (-47 / 50 : ℝ)
  | 4 => (-93 / 100 : ℝ)
  | _ => (-9 / 10 : ℝ)

def K : ℕ := 5

theorem hK : -9 / 10 ≤ a K := by norm_num [a, K]

theorem hslab : ∀ k, k < K → SlabSpec Base.phi (a k) (a (k + 1)) := by
  intro k hk
  unfold K at hk
  interval_cases k
  · exact S9998.spec
  · exact S9896.spec
  · exact S9694.spec
  · exact S9493.spec
  · exact S9390.spec

theorem hcap : CapSpec Base.phi (1 / 165000) (a 0) := Cap.spec

/-- Upstream's tiny-ball local minimality (radius `(11/2)·(1/165000) = 1/30000`) in the generic form. -/
theorem localMinAt : LocalMinAt Base.phi (11 / 2 * (1 / 165000)) := by
  have h : (11 / 2 * (1 / 165000 : ℝ)) = 1 / 30000 := by norm_num
  rw [h]
  intro z hz hzd
  rw [← coulombEnergy_eq_pairEnergy hz.1, ← coulombEnergy_eq_pairEnergy Base.pent_norm]
  exact Reg.pent_local_min_sup hz hzd

theorem main : ThomsonGen.Main Base.phi :=
  seven_of_specs Base.phi (τ₀ := 1 / 165000) (by norm_num) localMinAt Case1.claim a K hK hcap hslab

/-- **Coulomb energy, N = 7 (minimality).** -/
theorem coulomb_seven :
    ∀ x ∈ SphereConfig 7, coulombEnergy pentBipyramid ≤ coulombEnergy x := by
  intro x hx
  have h := main.1 x hx
  rwa [← coulombEnergy_eq_pairEnergy hx.1, ← coulombEnergy_eq_pairEnergy Base.pent_norm] at h

/-- **Coulomb energy, N = 7 (uniqueness)** up to an orthogonal map and a relabelling. -/
theorem coulomb_seven_unique :
    ∀ x ∈ SphereConfig 7, coulombEnergy x = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  intro x hx hE
  refine main.2 x hx ?_
  rw [← coulombEnergy_eq_pairEnergy hx.1, ← coulombEnergy_eq_pairEnergy Base.pent_norm]
  exact hE

end CoulN7
