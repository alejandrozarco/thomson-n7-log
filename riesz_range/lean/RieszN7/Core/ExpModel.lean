import RieszN7.Core.Rpow
import RieszN7.Core.LogEnc

/-!
# `RieszN7.Core.ExpModel` — polynomial Taylor models in `s` (LEAN_PLAN_range.md §3.0.2)

For `v(s) = C · exp(-(s - s_m) L / 2)` (e.g. `c^(-s/2)` with `C = c^(-s_m/2)`, `L = log c`, `rpow_neg_half_split`) and
`|s - s_m| ≤ r`, from rational enclosures `|C - C₀| ≤ ε_C`, `|L - L₀| ≤ ε_L` (`L₀ ≥ 0`):

    |v(s) - C₀ Σ_{i<n} (-(s - s_m) L₀/2)^i / i!|
        ≤ ε_C·E + C₀·E·(r ε_L) + C₀·tail(r L₀/2, n),     E = Σ_{i<n} Y^i/i! + tail(Y, n),  Y = r (L₀ + ε_L)/2,

`tail(Y, n) = Y^n (n+1)/(n! n)` (`Real.exp_bound`; `Real.abs_exp_sub_one_le` for the `L`-error).  Each concrete
instance is one `norm_num`.  `model_mul`: products with a bounded factor (the affine slope-pin factors).
Unit test: `2^(-s/2)` on `[11/12, 23/24]`, `n = 5`, error `≤ 1.5·10⁻¹³` (`n = 4` would give `1.0·10⁻¹⁰`).
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Real Finset

namespace RieszN7

/-- `tail(Y, n) = Y^n (n+1)/(n! n)` (the `Real.exp_bound` remainder). -/
noncomputable def expTail (Y : ℝ) (n : ℕ) : ℝ := Y ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * (n : ℝ)))

/-- `Σ_{m<n} Y^m/m! + tail(Y, n)`, an upper bound of `exp Y` on `0 ≤ Y ≤ 1`. -/
noncomputable def expSer (Y : ℝ) (n : ℕ) : ℝ := (∑ m ∈ range n, Y ^ m / (m.factorial : ℝ)) + expTail Y n

theorem exp_le_expSer {Y : ℝ} (h0 : 0 ≤ Y) (h1 : Y ≤ 1) {n : ℕ} (hn : 0 < n) : exp Y ≤ expSer Y n := by
  have hb := Real.exp_bound (x := Y) (by rw [abs_of_nonneg h0]; exact h1) hn
  rw [abs_of_nonneg h0] at hb
  have := (abs_sub_le_iff.mp hb).1
  unfold expSer expTail
  linarith

theorem rpow_neg_half_split {c : ℝ} (hc : 0 < c) (s sm : ℝ) :
    c ^ (-(s / 2)) = c ^ (-(sm / 2)) * exp (-(s - sm) * Real.log c / 2) := by
  rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hc, ← Real.exp_add]
  congr 1; ring

/-- **The Taylor model of `C · exp(-(s - s_m) L/2)` from rational enclosures.** -/
theorem model_of_encl {C C0 εC L L0 εL r s sm : ℝ} (n : ℕ) (hn : 0 < n)
    (hC : |C - C0| ≤ εC) (hL : |L - L0| ≤ εL) (hs : |s - sm| ≤ r) (hC0 : 0 ≤ C0) (hL0 : 0 ≤ L0)
    (hY : r * (L0 + εL) / 2 ≤ 1) :
    |C * exp (-(s - sm) * L / 2) - C0 * ∑ i ∈ range n, (-(s - sm) * L0 / 2) ^ i / (i.factorial : ℝ)|
      ≤ εC * expSer (r * (L0 + εL) / 2) n + C0 * expSer (r * (L0 + εL) / 2) n * (r * εL)
        + C0 * expTail (r * L0 / 2) n := by
  set y := -(s - sm) * L / 2 with hy
  set y0 := -(s - sm) * L0 / 2 with hy0
  set Y := r * (L0 + εL) / 2 with hYdef
  have hr : 0 ≤ r := (abs_nonneg _).trans hs
  have hεL : 0 ≤ εL := (abs_nonneg _).trans hL
  have hεC : 0 ≤ εC := (abs_nonneg _).trans hC
  have hLabs : |L| ≤ L0 + εL := by
    have := abs_sub_abs_le_abs_sub L L0
    rw [abs_of_nonneg hL0] at this
    linarith
  have hyabs : |y| ≤ Y := by
    rw [hy, hYdef, show -(s - sm) * L / 2 = -((s - sm) * L) / 2 by ring, abs_div, abs_neg, abs_mul,
      abs_two]
    have := mul_le_mul hs hLabs (abs_nonneg _) hr
    linarith
  have hy0abs : |y0| ≤ r * L0 / 2 := by
    rw [hy0, show -(s - sm) * L0 / 2 = -((s - sm) * L0) / 2 by ring, abs_div, abs_neg, abs_mul,
      abs_two, abs_of_nonneg hL0]
    have := mul_le_mul_of_nonneg_right hs hL0
    linarith
  have hdy : |y - y0| ≤ r * εL / 2 := by
    rw [hy, hy0, show -(s - sm) * L / 2 - -(s - sm) * L0 / 2 = -((s - sm) * (L - L0)) / 2 by ring,
      abs_div, abs_neg, abs_mul, abs_two]
    have := mul_le_mul hs hL (abs_nonneg _) hr
    linarith
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hEb : exp Y ≤ expSer Y n := exp_le_expSer hY0 hY hn
  have hEpos : 0 ≤ expSer Y n := (exp_pos Y).le.trans hEb
  have hey : exp y ≤ expSer Y n := (exp_le_exp.mpr ((le_abs_self y).trans hyabs)).trans hEb
  have hy0Y : r * L0 / 2 ≤ Y := by rw [hYdef]; nlinarith
  have hey0 : exp y0 ≤ expSer Y n :=
    (exp_le_exp.mpr ((le_abs_self y0).trans (hy0abs.trans hy0Y))).trans hEb
  have h1 : |(C - C0) * exp y| ≤ εC * expSer Y n := by
    rw [abs_mul, abs_of_pos (exp_pos y)]
    exact mul_le_mul hC hey (exp_pos _).le hεC
  have h2 : |C0 * (exp y - exp y0)| ≤ C0 * expSer Y n * (r * εL) := by
    have e : exp y - exp y0 = exp y0 * (exp (y - y0) - 1) := by
      rw [mul_sub, ← Real.exp_add]; ring_nf
    have hd1 : |y - y0| ≤ 1 := by
      have : r * εL / 2 ≤ Y := by rw [hYdef]; nlinarith
      linarith
    have hx := Real.abs_exp_sub_one_le hd1
    rw [e, abs_mul, abs_mul, abs_of_nonneg hC0, abs_of_pos (exp_pos _)]
    have h3 : exp y0 * |exp (y - y0) - 1| ≤ expSer Y n * (2 * |y - y0|) :=
      mul_le_mul hey0 hx (abs_nonneg _) hEpos
    have h4 : expSer Y n * (2 * |y - y0|) ≤ expSer Y n * (r * εL) :=
      mul_le_mul_of_nonneg_left (by linarith) hEpos
    have h5 := h3.trans h4
    calc C0 * (exp y0 * |exp (y - y0) - 1|) ≤ C0 * (expSer Y n * (r * εL)) :=
          mul_le_mul_of_nonneg_left h5 hC0
      _ = C0 * expSer Y n * (r * εL) := by ring
  have h3 : |C0 * (exp y0 - ∑ i ∈ range n, y0 ^ i / (i.factorial : ℝ))| ≤ C0 * expTail (r * L0 / 2) n := by
    rw [abs_mul, abs_of_nonneg hC0]
    apply mul_le_mul_of_nonneg_left _ hC0
    have hy01 : |y0| ≤ 1 := hy0abs.trans (hy0Y.trans hY)
    refine (Real.exp_bound hy01 hn).trans ?_
    unfold expTail
    apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hy0abs n)
    positivity
  have e : C * exp y - C0 * ∑ i ∈ range n, y0 ^ i / (i.factorial : ℝ)
      = (C - C0) * exp y + C0 * (exp y - exp y0) + C0 * (exp y0 - ∑ i ∈ range n, y0 ^ i / (i.factorial : ℝ)) := by
    ring
  rw [e]
  calc _ ≤ |(C - C0) * exp y + C0 * (exp y - exp y0)|
        + |C0 * (exp y0 - ∑ i ∈ range n, y0 ^ i / (i.factorial : ℝ))| := abs_add_le _ _
    _ ≤ |(C - C0) * exp y| + |C0 * (exp y - exp y0)|
        + |C0 * (exp y0 - ∑ i ∈ range n, y0 ^ i / (i.factorial : ℝ))| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Products with a bounded factor (`ε ↦ A ε`). -/
theorem model_mul {v P a A ε : ℝ} (h : |v - P| ≤ ε) (ha : |a| ≤ A) : |a * v - a * P| ≤ A * ε := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul ha h (abs_nonneg _) ((abs_nonneg a).trans ha)

/-! ### Unit test: `2^(-s/2)` on `[11/12, 23/24]` (`s_m = 15/16`, `r = 1/48`), `n = 5` -/

/-- 25-digit enclosure of `2^(-15/32)`. -/
theorem two_rpow_15_32 :
    (7225904034885233100185031 : ℝ) / 10 ^ 25 ≤ (2 : ℝ) ^ (-((15 / 16 : ℝ) / 2)) ∧
      (2 : ℝ) ^ (-((15 / 16 : ℝ) / 2)) ≤ (7225904034885233100185032 : ℝ) / 10 ^ 25 := by
  have e : (2 : ℝ) ^ (-((15 / 16 : ℝ) / 2)) = (2 : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((32 : ℕ) : ℝ))) := by norm_num
  rw [e]
  exact ⟨rpow_lower_of_pow (by norm_num) (by norm_num) (by norm_num),
    rpow_upper_of_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

set_option profiler true in
set_option profiler.threshold 50 in
theorem test_model_two (s : ℝ) (h1 : 11 / 12 ≤ s) (h2 : s ≤ 23 / 24) :
    |(2 : ℝ) ^ (-(s / 2)) - (14451808069770466200370063 / (2 * 10 ^ 25)) *
        ∑ i ∈ range 5, (-(s - 15 / 16) * (69314718055994530941723212145817 / 10 ^ 32) / 2) ^ i
          / (i.factorial : ℝ)| ≤ 15 / 10 ^ 14 := by
  rw [rpow_neg_half_split (by norm_num : (0 : ℝ) < 2) s (15 / 16)]
  obtain ⟨c1, c2⟩ := two_rpow_15_32
  obtain ⟨l1, l2⟩ := log2_enc
  have hC : |(2 : ℝ) ^ (-((15 / 16 : ℝ) / 2)) - 14451808069770466200370063 / (2 * 10 ^ 25)|
      ≤ 1 / (2 * 10 ^ 25) := by
    rw [abs_le]; constructor <;> linarith
  have hL : |Real.log 2 - 69314718055994530941723212145817 / 10 ^ 32| ≤ 100 / 10 ^ 32 := by
    rw [abs_le]; constructor <;> linarith
  have hs : |s - 15 / 16| ≤ 1 / 48 := by rw [abs_le]; constructor <;> linarith
  refine (model_of_encl 5 (by norm_num) hC hL hs (by norm_num) (by norm_num) (by norm_num)).trans ?_
  norm_num [expSer, expTail, Finset.sum_range_succ, Nat.factorial]

end RieszN7
