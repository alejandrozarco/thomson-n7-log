/-
LogPhi.lean — the fourth transcendental atom: a rational enclosure of
`log Φ`, `Φ = (1 + √5)/2`, of width ≤ 10⁻²⁵ (achieved: 1.54·10⁻²⁷).

Route: with `x = √5/5 = 1/√5` we have
  (1 + x)/(1 - x) = Φ²,   so   log Φ = ½ log((1+x)/(1-x)) = atanh x,
and `x^(2i+1) = x · 5⁻ⁱ`, so Mathlib's `Real.sum_range_le_log_div` /
`Real.log_div_le_sum_range_add` give
  x · S ≤ log Φ ≤ x · (S + (5/4)·5⁻³⁸),   S = Σ_{i<38} 5⁻ⁱ/(2i+1)  (a rational, 56 digits).
The series only involves base-5 rationals; √5 enters once, through a 33-digit bracket.
Also: `log(2 - 2cᵢ) = ½ log 5 ∓ log Φ` at the contact nodes `c₁,₂ = (-1 ± √5)/4` (Contact C).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset

namespace LogLean

/-- 33-digit bracket for `√5`. -/
theorem sqrt5_bounds :
    (223606797749978969640917366873127 : ℝ) / 10 ^ 32 ≤ √5 ∧
      √5 ≤ (223606797749978969640917366873128 : ℝ) / 10 ^ 32 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The base-5 partial sum `S = Σ_{i<38} 5⁻ⁱ/(2i+1)`, bracketed with the tail. -/
theorem S5_bounds :
    (107602235241001009722358308233216 : ℝ) / 10 ^ 32 ≤
        ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) ∧
      (∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1)) + ((1:ℝ)/5) ^ 38 * (5/4) ≤
        (107602235241001009722358308576815 : ℝ) / 10 ^ 32 := by
  constructor <;> norm_num [Finset.sum_range_succ]

/-- `(1 + x)/(1 - x) = Φ²` for `x = √5/5`. -/
theorem ratio_eq_phi_sq :
    (1 + √5 / 5) / (1 - √5 / 5) = ((1 + √5) / 2) ^ 2 := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs : √5 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hne : (1:ℝ) - √5 / 5 ≠ 0 := by linarith
  rw [div_eq_iff hne]
  linear_combination ((√5 - 3) / 20) * h5

/-- `log Φ = ½ log((1+x)/(1-x))`. -/
theorem logPhi_eq_atanh :
    Real.log ((1 + √5) / 2) = 1 / 2 * Real.log ((1 + √5 / 5) / (1 - √5 / 5)) := by
  rw [ratio_eq_phi_sq, Real.log_pow]; push_cast; ring

/-- `x^(2i+1)/(2i+1) = x · (5⁻ⁱ/(2i+1))` for `x = √5/5`. -/
theorem term_eq (i : ℕ) :
    (√5 / 5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) = √5 / 5 * (((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1)) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hx2 : (√5 / 5) ^ 2 = (1:ℝ) / 5 := by rw [div_pow, h5]; norm_num
  rw [pow_succ, pow_mul, hx2]; ring

/-- **`log Φ` to 1.54·10⁻²⁷.** -/
theorem logPhi_bounds :
    (481211825059603447497758913404 : ℝ) / 10 ^ 30 ≤ Real.log ((1 + √5) / 2) ∧
      Real.log ((1 + √5) / 2) ≤ (481211825059603447497758914942 : ℝ) / 10 ^ 30 := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ √5 := Real.sqrt_nonneg _
  have hs : √5 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hx0 : (0:ℝ) ≤ √5 / 5 := by positivity
  have hx1 : √5 / 5 < 1 := by linarith
  have hlo := Real.sum_range_le_log_div hx0 hx1 38
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 38
  rw [← logPhi_eq_atanh] at hlo hhi
  have hsum : ∑ i ∈ range 38, (√5 / 5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) =
      √5 / 5 * ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => term_eq i)
  have htail : (√5 / 5) ^ (2 * 38 + 1) / (1 - (√5 / 5) ^ 2) =
      √5 / 5 * (((1:ℝ)/5) ^ 38 * (5/4)) := by
    have hx2 : (√5 / 5) ^ 2 = (1:ℝ) / 5 := by rw [div_pow, h5]; norm_num
    rw [pow_succ, pow_mul, hx2]; ring
  rw [hsum] at hlo hhi
  rw [htail] at hhi
  obtain ⟨sl, sh⟩ := sqrt5_bounds
  obtain ⟨al, ah⟩ := S5_bounds
  set S := ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) with hS
  set T := ((1:ℝ)/5) ^ 38 * (5/4) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  clear_value S T
  constructor
  · -- x·S ≥ (s_lo/5)·A_lo ≥ L_lo
    have h1 : (223606797749978969640917366873127 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308233216 : ℝ) / 10 ^ 32) ≤ √5 / 5 * S := by
      apply mul_le_mul (by linarith) al (by norm_num) hx0
    have h2 : (481211825059603447497758913404 : ℝ) / 10 ^ 30 ≤
        (223606797749978969640917366873127 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308233216 : ℝ) / 10 ^ 32) := by norm_num
    linarith
  · have h1 : √5 / 5 * S + √5 / 5 * T ≤ (223606797749978969640917366873128 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308576815 : ℝ) / 10 ^ 32) := by
      rw [← mul_add]
      apply mul_le_mul (by linarith) ah (by linarith [al]) (by norm_num)
    have h2 : (223606797749978969640917366873128 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308576815 : ℝ) / 10 ^ 32) ≤
        (481211825059603447497758914942 : ℝ) / 10 ^ 30 := by norm_num
    linarith

theorem logPhi_width :
    (481211825059603447497758914942 : ℝ) / 10 ^ 30 - 481211825059603447497758913404 / 10 ^ 30 ≤
      1 / 10 ^ 25 := by norm_num

/-! ### The contact nodes `c₁ = (-1+√5)/4`, `c₂ = (-1-√5)/4` (roots of `4t²+2t-1`). -/

/-- `2 - 2c₁ = (5 - √5)/2 = √5/Φ`, so `log(2 - 2c₁) = ½ log 5 - log Φ`. -/
theorem log_two_sub_two_c1 :
    Real.log (2 - 2 * ((-1 + √5) / 4)) = Real.log 5 / 2 - Real.log ((1 + √5) / 2) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hs : √5 < 5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hphi : (0:ℝ) < (1 + √5) / 2 := by positivity
  have hpos : (0:ℝ) < 2 - 2 * ((-1 + √5) / 4) := by linarith
  have hprod : (2 - 2 * ((-1 + √5) / 4)) * ((1 + √5) / 2) = √5 := by
    linear_combination (-1 / 4) * h5
  have hl : Real.log (2 - 2 * ((-1 + √5) / 4)) + Real.log ((1 + √5) / 2) = Real.log 5 / 2 := by
    rw [← Real.log_mul hpos.ne' hphi.ne', hprod, Real.log_sqrt (by norm_num)]
  linarith

/-- `2 - 2c₂ = (5 + √5)/2 = √5·Φ`, so `log(2 - 2c₂) = ½ log 5 + log Φ`. -/
theorem log_two_sub_two_c2 :
    Real.log (2 - 2 * ((-1 - √5) / 4)) = Real.log 5 / 2 + Real.log ((1 + √5) / 2) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hphi : (0:ℝ) < (1 + √5) / 2 := by positivity
  have hprod : 2 - 2 * ((-1 - √5) / 4) = √5 * ((1 + √5) / 2) := by
    linear_combination (-1 / 2) * h5
  rw [hprod, Real.log_mul hs0.ne' hphi.ne', Real.log_sqrt (by norm_num)]

end LogLean
