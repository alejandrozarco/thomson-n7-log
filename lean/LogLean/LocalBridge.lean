import LogLean.LocalMain

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`cyl` and `pentBipyramid` restated from upstream `cyl`, `pentBipyramid`. -/

/-!
# LocalBridge: `Pbip = pentBipyramid` (the K-coordinates of the bipyramid are the trigonometric ones)

Upstream (`ThomsonN7/Solution.lean`) defines the bipyramid with `cyl 1 (2πk/5) 0` for the ring and the poles
`cyl 0 0 (±1)`.  Here `cos(2π/5) = (√5 − 1)/4`, `sin(2π/5) = α/4`, `cos(4π/5) = −(√5 + 1)/4`,
`sin(4π/5) = α(√5 − 1)/8` with `α = √(10 + 2√5)`, and the K-coordinates of `LocalFrames.Pdat` are exactly these
(the bridge to upstream's trigonometric atoms).  `pentBipyramid` is restated here verbatim so that this
file does not depend on the upstream olean; `Pbip_eq_pent` is the bridge.
-/

open Real LocalKel LocalFrames LocalGeom LocalMain

namespace LocalBridge

/-- upstream's `cyl` -/
noncomputable def cyl (ρ θ h : ℝ) : R3 := !₂[ρ * cos θ, ρ * sin θ, h]

/-- upstream's `pentBipyramid` (verbatim) -/
noncomputable def pentBipyramid : Fin 7 → R3 := fun i =>
  if (i : ℕ) < 5 then cyl 1 (2 * π * (i : ℕ) / 5) 0
  else if (i : ℕ) = 5 then cyl 0 0 1
  else cyl 0 0 (-1)

lemma sqrt5_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
lemma alpha_sq : alpha ^ 2 = 10 + 2 * √5 := by unfold alpha; rw [Real.sq_sqrt (by positivity)]
lemma alpha_pos : 0 < alpha := by unfold alpha; positivity

lemma cos_two_pi_div_five : cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h := Real.cos_pi_div_five
  have : cos (2 * π / 5) = 2 * cos (π / 5) ^ 2 - 1 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul]
  rw [this, h]; nlinarith [sqrt5_sq]

lemma sin_two_pi_div_five : sin (2 * π / 5) = alpha / 4 := by
  have hpos : 0 < sin (2 * π / 5) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsq : sin (2 * π / 5) ^ 2 = (alpha / 4) ^ 2 := by
    rw [Real.sin_sq, cos_two_pi_div_five]; nlinarith [sqrt5_sq, alpha_sq]
  have ha : 0 < alpha / 4 := by linarith [alpha_pos]
  exact (pow_left_inj₀ hpos.le ha.le two_ne_zero).mp hsq

lemma cos_four_pi_div_five : cos (4 * π / 5) = -(√5 + 1) / 4 := by
  have : cos (4 * π / 5) = 2 * cos (2 * π / 5) ^ 2 - 1 := by
    rw [show 4 * π / 5 = 2 * (2 * π / 5) by ring, Real.cos_two_mul]
  rw [this, cos_two_pi_div_five]; nlinarith [sqrt5_sq]

lemma sin_four_pi_div_five : sin (4 * π / 5) = alpha * (√5 - 1) / 8 := by
  have : sin (4 * π / 5) = 2 * sin (2 * π / 5) * cos (2 * π / 5) := by
    rw [show 4 * π / 5 = 2 * (2 * π / 5) by ring, Real.sin_two_mul]
  rw [this, sin_two_pi_div_five, cos_two_pi_div_five]; ring

/-- `√5 = (α² − 10)/2` -/
lemma sqrt5_eq : (√5 : ℝ) = (alpha ^ 2 - 10) / 2 := by rw [alpha_sq]; ring

/-- the ring angle `6π/5`: `cos = cos(4π/5)`, `sin = −sin(4π/5)` -/
lemma cos_six : cos (2 * π * 3 / 5) = cos (4 * π / 5) := by
  rw [show 2 * π * 3 / 5 = 2 * π - 4 * π / 5 by ring, Real.cos_two_pi_sub]
lemma sin_six : sin (2 * π * 3 / 5) = -sin (4 * π / 5) := by
  rw [show 2 * π * 3 / 5 = 2 * π - 4 * π / 5 by ring, Real.sin_two_pi_sub]
lemma cos_eight : cos (2 * π * 4 / 5) = cos (2 * π / 5) := by
  rw [show 2 * π * 4 / 5 = 2 * π - 2 * π / 5 by ring, Real.cos_two_pi_sub]
lemma sin_eight : sin (2 * π * 4 / 5) = -sin (2 * π / 5) := by
  rw [show 2 * π * 4 / 5 = 2 * π - 2 * π / 5 by ring, Real.sin_two_pi_sub]

/-- **The bridge**: the K-coordinate bipyramid is upstream's `pentBipyramid`. -/
theorem Pbip_eq_pent : Pbip = pentBipyramid := by
  funext i
  ext c
  rw [Pbip_apply]
  have h5 := sqrt5_eq
  fin_cases i <;> fin_cases c <;>
    simp [pentBipyramid, cyl, Pv, Pk, Pdat, Kel.ev] <;>
    (try simp only [show (2 : ℝ) * π * 2 / 5 = 4 * π / 5 by ring, cos_six, sin_six, cos_eight, sin_eight]) <;>
    (try simp only [cos_two_pi_div_five, sin_two_pi_div_five, cos_four_pi_div_five, sin_four_pi_div_five]) <;>
    (try simp only [h5]) <;>
    ring1

end LocalBridge
