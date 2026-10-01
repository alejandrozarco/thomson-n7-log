/-
Riesz2/Main.lean — the two main theorems.

Inputs from the certificate modules:
  Riesz2.Case1.claim  : ThomsonGen.Case1Claim phi2                        (Case1/Claim.lean, Cert3 data)
  Riesz2.Cap.spec     : ThomsonGen.CapSpecSharp phi2 (-99/100)             (Cap/Spec.lean, TCert data + MinorCap)
  Riesz2.S9998.spec   : ThomsonGen.SlabSpec phi2 (-99/100) (-49/50)        (S9998/Spec.lean)
  Riesz2.S9896.spec   : ThomsonGen.SlabSpec phi2 (-49/50) (-24/25)
  Riesz2.S9694.spec   : ThomsonGen.SlabSpec phi2 (-24/25) (-47/50)
  Riesz2.S9493.spec   : ThomsonGen.SlabSpec phi2 (-47/50) (-93/100)
  Riesz2.S9390.spec   : ThomsonGen.SlabSpec phi2 (-93/100) (-9/10)

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `riesz2_seven` ← `thomson_seven`; `riesz2_seven_unique` ← `thomson_seven_unique`.
-/
import Riesz2.Final
import Riesz2.Case1.Claim
import Riesz2.Cap.Spec
import Riesz2.S9998.Spec
import Riesz2.S9896.Spec
import Riesz2.S9694.Spec
import Riesz2.S9493.Spec
import Riesz2.S9390.Spec

open Real

namespace Riesz2

open ThomsonN7 ThomsonN7.Base ThomsonGen
open Minor

theorem hslab : ∀ k, k < K → SlabSpec phi2 (a k) (a (k + 1)) := by
  intro k hk
  unfold K at hk
  interval_cases k
  · exact S9998.spec
  · exact S9896.spec
  · exact S9694.spec
  · exact S9493.spec
  · exact S9390.spec

theorem hcap : CapSpecSharp phi2 (a 0) := Cap.spec

/-- **Riesz s = 2, N = 7 (minimality).** Among all configurations of 7 distinct points on the unit
sphere, the pentagonal bipyramid minimises `∑_{i<j} ‖x i - x j‖⁻²`; the minimum is `41/4`. -/
theorem riesz2_seven :
    ∀ x ∈ SphereConfig 7, riesz2Energy pentBipyramid ≤ riesz2Energy x :=
  riesz2_seven_of_specs Case1.claim hcap hslab

/-- **Riesz s = 2, N = 7 (uniqueness).** Every minimiser is the pentagonal bipyramid up to an
orthogonal map of `ℝ³` and a relabelling. -/
theorem riesz2_seven_unique :
    ∀ x ∈ SphereConfig 7, riesz2Energy x = riesz2Energy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  riesz2_seven_unique_of_specs Case1.claim hcap hslab

end Riesz2
