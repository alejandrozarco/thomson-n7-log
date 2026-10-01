/-
Riesz2/Final.lean — the two trusted theorems from the three cell specifications, via M0's
`ThomsonGen.seven_of_specs_sharp` (sharp cap: no tube width, no local lemma).

Breakpoints as for Coulomb/log: cap `⟪y 0, y 1⟫ ≤ -99/100`, slabs `[-99/100, -49/50]`, `[-49/50, -24/25]`,
`[-24/25, -47/50]`, `[-47/50, -93/100]`, `[-93/100, -9/10]`, Case 1 `≥ -9/10`.
`Riesz2.Main` supplies `hcase1`, `hcap`, `hslab` from the certificate modules.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* the breakpoint list above ← docstring of `Final.capspec_cap`.
-/
import ThomsonGen.Generic.Glue
import Riesz2.Sharp
import Riesz2.Basic

open Real

namespace Riesz2

open ThomsonN7 ThomsonN7.Base ThomsonGen
open Minor
open scoped InnerProductSpace

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

/-- `Main phi2` from Case 1, the sharp cap and the five slabs. -/
theorem main_of_specs (hcase1 : Case1Claim phi2) (hcap : CapSpecSharp phi2 (a 0))
    (hslab : ∀ k, k < K → SlabSpec phi2 (a k) (a (k + 1))) : ThomsonGen.Main phi2 :=
  seven_of_specs_sharp phi2 hcase1 a K hK hcap hslab

/-- **Riesz s = 2, N = 7: minimality.** For every configuration of 7 distinct unit vectors,
`E₂(P) ≤ E₂(x)` where `E₂ = ∑_{i<j} ‖x i - x j‖⁻²`. -/
theorem riesz2_seven_of_specs (hcase1 : Case1Claim phi2) (hcap : CapSpecSharp phi2 (a 0))
    (hslab : ∀ k, k < K → SlabSpec phi2 (a k) (a (k + 1))) :
    ∀ x ∈ SphereConfig 7, riesz2Energy pentBipyramid ≤ riesz2Energy x := by
  intro x hx
  have h := (main_of_specs hcase1 hcap hslab).1 x hx
  rwa [show pairEnergy phi2 x = riesz2Energy x from (riesz2Energy_eq_sum_phi2 hx.1).symm,
    show pairEnergy phi2 pentBipyramid = riesz2Energy pentBipyramid from
      (riesz2Energy_eq_sum_phi2 pent_norm).symm] at h

/-- **Riesz s = 2, N = 7: uniqueness** up to an orthogonal map and a relabelling. -/
theorem riesz2_seven_unique_of_specs (hcase1 : Case1Claim phi2) (hcap : CapSpecSharp phi2 (a 0))
    (hslab : ∀ k, k < K → SlabSpec phi2 (a k) (a (k + 1))) :
    ∀ x ∈ SphereConfig 7, riesz2Energy x = riesz2Energy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) := by
  intro x hx hE
  refine (main_of_specs hcase1 hcap hslab).2 x hx ?_
  rw [show pairEnergy phi2 x = riesz2Energy x from (riesz2Energy_eq_sum_phi2 hx.1).symm,
    show pairEnergy phi2 pentBipyramid = riesz2Energy pentBipyramid from
      (riesz2Energy_eq_sum_phi2 pent_norm).symm]
  exact hE

end Riesz2
