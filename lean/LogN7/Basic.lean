
/-
LogN7/Basic.lean — the log energy, its kernel form, and E(P).

* `logEnergy x = ∑_{i<j} -log ‖x i - x j‖` (as in `LogN7/Challenge.lean`).
* On unit vectors `‖x - y‖² = 2 - 2⟪x, y⟫`, so `-log ‖x - y‖ = -½ log(2 - 2⟪x,y⟫) = φ₀ ⟪x,y⟫` with
  `φ₀ = LogLean.Minor.phi` (`Real.log` of the square; no distinctness needed, `log 0 = 0` on both sides).
* `pairEnergy φ₀ pentBipyramid = -(6 log 2 + 5/2 log 5)` (one pair at `-1`, ten at `0`, five each at
  `c1, c2`, and `(2 - 2c1)(2 - 2c2) = 5`), and its enclosure from `LogLean.Minor.log2_enc/log5_enc`.
`sum_Ioi_seven` and `inner_pent_ring` are copied from the Riesz s = 2 formalisation (`riesz2/lean/Riesz2/Basic.lean`).
-/
import ThomsonGen.Generic.Energy
import LogLean.MinorCore

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`logEnergy` ← `coulombEnergy`; `sum_Ioi_seven` ← `Reg.sum_Ioi_seven`. -/

open Real

namespace LogN7

open ThomsonN7 ThomsonN7.Base ThomsonGen

/-- Logarithmic energy `∑_{i<j} −log ‖x i − x j‖`. -/
noncomputable def logEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, -Real.log ‖x i - x j‖

lemma neg_log_norm_sub_eq_phi {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -Real.log ‖x - y‖ = LogLean.Minor.phi (inner ℝ x y) := by
  have hs : Real.log ‖x - y‖ = (1 / 2) * Real.log (‖x - y‖ ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  unfold LogLean.Minor.phi
  rw [hs, norm_sub_sq_of_unit hx hy]
  ring

/-- On unit vectors the log energy is `pairEnergy φ₀`. -/
theorem logEnergy_eq_pairEnergy {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    logEnergy x = pairEnergy LogLean.Minor.phi x := by
  unfold logEnergy pairEnergy
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    neg_log_norm_sub_eq_phi (hx i) (hx j)

/-- The 21 pairs of `Fin 7` (copy of `Riesz2.sum_Ioi_seven`). -/
lemma sum_Ioi_seven (f : Fin 7 → Fin 7 → ℝ) : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, f i j =
    f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 + f 0 6
    + f 1 2 + f 1 3 + f 1 4 + f 1 5 + f 1 6
    + f 2 3 + f 2 4 + f 2 5 + f 2 6
    + f 3 4 + f 3 5 + f 3 6
    + f 4 5 + f 4 6 + f 5 6 := by
  have hI : ∀ i : Fin 7, ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp only [hI, Fin.sum_univ_seven]
  simp
  ring

/-- Inner product of two ring points (copy of `Riesz2.inner_pent_ring`). -/
lemma inner_pent_ring {i j : Fin 7} (hi : (i : ℕ) < 5) (hj : (j : ℕ) < 5) :
    inner ℝ (pentBipyramid i) (pentBipyramid j) =
      cos (2 * π * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / 5) := by
  rw [pent_of_lt hi, pent_of_lt hj, inner_cyl]
  first
  | (simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
     rw [← cos_neg]; congr 1; ring)
  | (rw [← cos_neg]; simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
     congr 1; ring)
  | (simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, cos_sub]
     rw [← cos_neg, cos_neg]; simp only [cos_sub]; ring)

lemma phi_zero : LogLean.Minor.phi 0 = -(1 / 2) * Real.log 2 := by
  unfold LogLean.Minor.phi; norm_num

lemma phi_neg_one : LogLean.Minor.phi (-1) = -Real.log 2 := by
  unfold LogLean.Minor.phi
  rw [show (2 : ℝ) - 2 * -1 = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

lemma sqrt5_lt_three : √5 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- `φ₀(c₁) + φ₀(c₂) = -½ log 5`, from `(2 - 2c₁)(2 - 2c₂) = 5`. -/
lemma phi_c1_add_c2 : LogLean.Minor.phi c1 + LogLean.Minor.phi c2 = -(1 / 2) * Real.log 5 := by
  unfold LogLean.Minor.phi c1 c2
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs := sqrt5_lt_three
  have hs0 := Real.sqrt_nonneg 5
  have h1 : (0 : ℝ) < 2 - 2 * ((√5 - 1) / 4) := by linarith
  have h2 : (0 : ℝ) < 2 - 2 * (-(1 + √5) / 4) := by linarith
  have hp : (2 - 2 * ((√5 - 1) / 4)) * (2 - 2 * (-(1 + √5) / 4)) = (5 : ℝ) := by
    linear_combination (-1 / 4 : ℝ) * h5
  have hl := Real.log_mul h1.ne' h2.ne'
  rw [hp] at hl
  linarith

/-- **E(P)** for the log kernel: `pairEnergy φ₀ P = -(6 log 2 + 5/2 log 5) = -log(1600 √5)`. -/
theorem pairEnergy_pent :
    pairEnergy LogLean.Minor.phi pentBipyramid = -(6 * Real.log 2 + 5 / 2 * Real.log 5) := by
  unfold pairEnergy
  rw [sum_Ioi_seven]
  have i01 : inner ℝ (pentBipyramid 0) (pentBipyramid 1) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num
  have i04 : inner ℝ (pentBipyramid 0) (pentBipyramid 4) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_8pi5]; congr 1; norm_num <;> ring
  have i12 : inner ℝ (pentBipyramid 1) (pentBipyramid 2) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num <;> ring
  have i23 : inner ℝ (pentBipyramid 2) (pentBipyramid 3) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num <;> ring
  have i34 : inner ℝ (pentBipyramid 3) (pentBipyramid 4) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num <;> ring
  have i02 : inner ℝ (pentBipyramid 0) (pentBipyramid 2) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_4pi5]; congr 1; norm_num <;> ring
  have i03 : inner ℝ (pentBipyramid 0) (pentBipyramid 3) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_6pi5]; congr 1; norm_num <;> ring
  have i13 : inner ℝ (pentBipyramid 1) (pentBipyramid 3) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_4pi5]; congr 1; norm_num <;> ring
  have i14 : inner ℝ (pentBipyramid 1) (pentBipyramid 4) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_6pi5]; congr 1; norm_num <;> ring
  have i24 : inner ℝ (pentBipyramid 2) (pentBipyramid 4) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_4pi5]; congr 1; norm_num <;> ring
  rw [i01, i02, i03, i04, i12, i13, i14, i23, i24, i34,
    pent_inner_north (i := 0) (by decide), pent_inner_north (i := 1) (by decide),
    pent_inner_north (i := 2) (by decide), pent_inner_north (i := 3) (by decide),
    pent_inner_north (i := 4) (by decide), pent_inner_south (i := 0) (by decide),
    pent_inner_south (i := 1) (by decide), pent_inner_south (i := 2) (by decide),
    pent_inner_south (i := 3) (by decide), pent_inner_south (i := 4) (by decide),
    pent_inner_poles, phi_zero, phi_neg_one]
  linarith [phi_c1_add_c2]

/-- Upper enclosure of `E(P)` (to `3.2·10⁻²⁹`). -/
theorem pairEnergy_pent_le : pairEnergy LogLean.Minor.phi pentBipyramid ≤
    -(6 * (69314718055994530941723212145717 : ℝ) + 5 / 2 * 160943791243410037460075933322218) /
      10 ^ 32 := by
  rw [pairEnergy_pent]
  obtain ⟨a, -⟩ := LogLean.Minor.log2_enc
  obtain ⟨b, -⟩ := LogLean.Minor.log5_enc
  simp only [LogLean.Minor.l2, LogLean.Minor.l5, LogLean.Minor.DEN] at a b
  push_cast at a b
  rw [neg_div, neg_le_neg_iff, add_div]
  have e1 : 6 * (69314718055994530941723212145717 : ℝ) / 10 ^ 32 =
      6 * ((69314718055994530941723212145717 : ℝ) / 10 ^ 32) := by ring
  have e2 : 5 / 2 * (160943791243410037460075933322218 : ℝ) / 10 ^ 32 =
      5 / 2 * ((160943791243410037460075933322218 : ℝ) / 10 ^ 32) := by ring
  rw [e1, e2]
  linarith

end LogN7
