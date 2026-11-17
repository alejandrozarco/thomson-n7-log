import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `RieszN7.Core.LogEnc` — rational enclosures of logarithms (LEAN_PLAN_range.md §3.0.8)

* `log2_enc`, `log54_enc`, `log5_enc`: copied from `numerics/n7_interval/lean/LogLean/MinorCore.lean` §2 (log
  formalisation, thomson-n7-log; statements written with the literals inlined instead of `l2/h2/DEN`).
* `sqrt5_bounds`, `logPhi_bounds`, `log_two_sub_two_c1/c2`: copied from `lean/LogLean/LogPhi.lean` (same project;
  namespace `LogLean` → `RieszN7`).  `c1 = (-1 + √5)/4`, `c2 = (-1 - √5)/4` are the inner products of the
  pentagonal bipyramid; `2 - 2c₁,₂ = (5 ∓ √5)/2`.
* new: `log_enc_of_series` (the `atanh` series of Mathlib, `Real.sum_range_le_log_div` /
  `Real.log_div_le_sum_range_add`, for any `u = (1+x)/(1-x)`, `0 ≤ x < 1`) and `log_enc_of_scaled`
  (`u·2^a = v·2^b`: `log u = log v + (b - a) log 2`), the two templates of the generated `Tables.LogTable`.
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Finset

namespace RieszN7

/-! ### Copied from `LogLean/MinorCore.lean` §2 -/

theorem log2_enc : (69314718055994530941723212145717 : ℝ) / 10 ^ 32 ≤ Real.log 2 ∧
    Real.log 2 ≤ (69314718055994530941723212145917 : ℝ) / 10 ^ 32 := by
  have hx0 : (0:ℝ) ≤ 1 / 3 := by norm_num
  have hx1 : (1:ℝ) / 3 < 1 := by norm_num
  have hlo := Real.sum_range_le_log_div hx0 hx1 32
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 32
  have harg : ((1:ℝ) + 1 / 3) / (1 - 1 / 3) = 2 := by norm_num
  rw [harg] at hlo hhi
  have e1 : (69314718055994530941723212145717 : ℝ) / 10 ^ 32 ≤
      2 * ∑ i ∈ Finset.range 32, ((1:ℝ)/3) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  have e2 : 2 * ((∑ i ∈ Finset.range 32, ((1:ℝ)/3) ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) +
      ((1:ℝ)/3) ^ (2 * 32 + 1) / (1 - ((1:ℝ)/3) ^ 2)) ≤ (69314718055994530941723212145917 : ℝ) / 10 ^ 32 := by
    norm_num [Finset.sum_range_succ]
  constructor <;> linarith

theorem log54_enc :
    (160943791243410037460075933322218 - 2 * 69314718055994530941723212145717 : ℝ) / 10 ^ 32
        ≤ Real.log (5 / 4) ∧
      Real.log (5 / 4) ≤ (160943791243410037460075933323018 - 2 * 69314718055994530941723212145917 : ℝ) / 10 ^ 32 := by
  have hx0 : (0:ℝ) ≤ 1 / 9 := by norm_num
  have hx1 : (1:ℝ) / 9 < 1 := by norm_num
  have hlo := Real.sum_range_le_log_div hx0 hx1 16
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 16
  have harg : ((1:ℝ) + 1 / 9) / (1 - 1 / 9) = 5 / 4 := by norm_num
  rw [harg] at hlo hhi
  have e1 : (160943791243410037460075933322218 - 2 * 69314718055994530941723212145717 : ℝ) / 10 ^ 32 ≤
      2 * ∑ i ∈ Finset.range 16, ((1:ℝ)/9) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  have e2 : 2 * ((∑ i ∈ Finset.range 16, ((1:ℝ)/9) ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) +
      ((1:ℝ)/9) ^ (2 * 16 + 1) / (1 - ((1:ℝ)/9) ^ 2)) ≤
      (160943791243410037460075933323018 - 2 * 69314718055994530941723212145917 : ℝ) / 10 ^ 32 := by
    norm_num [Finset.sum_range_succ]
  constructor <;> linarith

theorem log5_enc : (160943791243410037460075933322218 : ℝ) / 10 ^ 32 ≤ Real.log 5 ∧
    Real.log 5 ≤ (160943791243410037460075933323018 : ℝ) / 10 ^ 32 := by
  have e : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [← h4, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a, b⟩ := log2_enc
  obtain ⟨c, d⟩ := log54_enc
  rw [e]
  constructor <;> linarith

/-! ### Copied from `lean/LogLean/LogPhi.lean` -/

/-- 33-digit bracket for `√5`. -/
theorem sqrt5_bounds :
    (223606797749978969640917366873127 : ℝ) / 10 ^ 32 ≤ √5 ∧
      √5 ≤ (223606797749978969640917366873128 : ℝ) / 10 ^ 32 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem S5_bounds :
    (107602235241001009722358308233216 : ℝ) / 10 ^ 32 ≤
        ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) ∧
      (∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1)) + ((1:ℝ)/5) ^ 38 * (5/4) ≤
        (107602235241001009722358308576815 : ℝ) / 10 ^ 32 := by
  constructor <;> norm_num [Finset.sum_range_succ]

theorem ratio_eq_phi_sq :
    (1 + √5 / 5) / (1 - √5 / 5) = ((1 + √5) / 2) ^ 2 := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs : √5 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hne : (1:ℝ) - √5 / 5 ≠ 0 := by linarith
  rw [div_eq_iff hne]
  linear_combination ((√5 - 3) / 20) * h5

theorem logPhi_eq_atanh :
    Real.log ((1 + √5) / 2) = 1 / 2 * Real.log ((1 + √5 / 5) / (1 - √5 / 5)) := by
  rw [ratio_eq_phi_sq, Real.log_pow]; push_cast; ring

theorem term_eq (i : ℕ) :
    (√5 / 5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) = √5 / 5 * (((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1)) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hx2 : (√5 / 5) ^ 2 = (1:ℝ) / 5 := by rw [div_pow, h5]; norm_num
  rw [pow_succ, pow_mul, hx2]; ring

/-- `log Φ` to `1.54·10⁻²⁷`. -/
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
  · have h1 : (223606797749978969640917366873127 : ℝ) / 10 ^ 32 / 5 *
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

/-- `c₁ = (-1 + √5)/4 = cos(2π/5)`, `c₂ = (-1 - √5)/4 = cos(4π/5)`. -/
noncomputable def c1 : ℝ := (-1 + √5) / 4
noncomputable def c2 : ℝ := (-1 - √5) / 4

/-- `2 - 2c₁ = (5 - √5)/2 = √5/Φ`, so `log(2 - 2c₁) = ½ log 5 - log Φ`. -/
theorem log_two_sub_two_c1 :
    Real.log (2 - 2 * c1) = Real.log 5 / 2 - Real.log ((1 + √5) / 2) := by
  unfold c1
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
    Real.log (2 - 2 * c2) = Real.log 5 / 2 + Real.log ((1 + √5) / 2) := by
  unfold c2
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hphi : (0:ℝ) < (1 + √5) / 2 := by positivity
  have hprod : 2 - 2 * ((-1 - √5) / 4) = √5 * ((1 + √5) / 2) := by
    linear_combination (-1 / 2) * h5
  rw [hprod, Real.log_mul hs0.ne' hphi.ne', Real.log_sqrt (by norm_num)]

/-! ### New: templates for generated log enclosures -/

/-- The `atanh` series: for `u = (1+x)/(1-x)`, `0 ≤ x < 1`, the `n`-term partial sum and its tail bracket
`log u`; `lo`, `hi` are the (generated) rational bounds, each side one `norm_num`. -/
theorem log_enc_of_series {u x lo hi : ℝ} (n : ℕ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hu : (1 + x) / (1 - x) = u)
    (hlo : lo ≤ 2 * ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * (i:ℝ) + 1))
    (hhi : 2 * ((∑ i ∈ range n, x ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) + x ^ (2 * n + 1) / (1 - x ^ 2)) ≤ hi) :
    lo ≤ Real.log u ∧ Real.log u ≤ hi := by
  have h1 := Real.sum_range_le_log_div hx0 hx1 n
  have h2 := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [hu] at h1 h2
  constructor <;> linarith

/-- `u·2^a = v·2^b` (all positive) transports enclosures: `log u = log v + (b - a) log 2`. -/
theorem log_enc_of_scaled {u v lv hv : ℝ} (a b : ℕ) (hu : 0 < u) (hv0 : 0 < v)
    (heq : u * 2 ^ a = v * 2 ^ b) (hlv : lv ≤ Real.log v ∧ Real.log v ≤ hv) :
    lv + b * ((69314718055994530941723212145717 : ℝ) / 10 ^ 32) - a * ((69314718055994530941723212145917 : ℝ) / 10 ^ 32)
        ≤ Real.log u ∧
      Real.log u ≤ hv + b * ((69314718055994530941723212145917 : ℝ) / 10 ^ 32)
        - a * ((69314718055994530941723212145717 : ℝ) / 10 ^ 32) := by
  have e : Real.log u + a * Real.log 2 = Real.log v + b * Real.log 2 := by
    have := congrArg Real.log heq
    rw [Real.log_mul hu.ne' (by positivity), Real.log_mul hv0.ne' (by positivity), Real.log_pow,
      Real.log_pow] at this
    exact this
  obtain ⟨l1, l2⟩ := log2_enc
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0:ℝ) ≤ b := Nat.cast_nonneg b
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left l1 ha, mul_le_mul_of_nonneg_left l2 ha,
    mul_le_mul_of_nonneg_left l1 hb, mul_le_mul_of_nonneg_left l2 hb]

end RieszN7
