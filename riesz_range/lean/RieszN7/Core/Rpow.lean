import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# `RieszN7.Core.Rpow` — the Riesz kernel `phiS s t = (2 - 2t)^(-s/2)` (LEAN_PLAN_range.md §3.0.1)

* `phiS`, `xt t = -log(2 - 2t)/2`, `phiS_eq_exp : phiS s t = exp (s * xt t)` for `t < 1`;
* monotonicity in `t` (`s ≥ 0`) and in `s` (increasing for `t > 1/2`, decreasing for `t ≤ 1/2`);
* rational-exponent enclosures `rpow_lower_of_pow` / `rpow_upper_of_pow`: for `u > 0`, `m > 0`,
  `ℓ^m u^p ≤ 1 ⇒ ℓ ≤ u^(-p/m)` and `1 ≤ U^m u^p ⇒ u^(-p/m) ≤ U` (each instance is one `norm_num` on integers);
* the normalised gauge `psi s t = (phiS s t - 1)/s` and `psi_mono_s_of_half_lt` (secant slopes of `exp`);
* unit test: 25-digit enclosure of `phiS (19/48) (-9/10) = (19/5)^(-19/96)`.
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Real

namespace RieszN7

/-- The Riesz kernel as a function of the inner product: `‖x - y‖^(-s) = (2 - 2⟪x,y⟫)^(-s/2)` on the sphere. -/
noncomputable def phiS (s t : ℝ) : ℝ := (2 - 2 * t) ^ (-(s / 2))

/-- log coordinate `xt t = -log(2 - 2t)/2` (positive iff `t > 1/2`). -/
noncomputable def xt (t : ℝ) : ℝ := -Real.log (2 - 2 * t) / 2

theorem phiS_eq_exp (s : ℝ) {t : ℝ} (ht : t < 1) : phiS s t = Real.exp (s * xt t) := by
  unfold phiS xt
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 1; ring

theorem phiS_pos (s : ℝ) {t : ℝ} (ht : t < 1) : 0 < phiS s t := by
  rw [phiS_eq_exp s ht]; exact Real.exp_pos _

theorem xt_mono {t t' : ℝ} (h : t ≤ t') (h' : t' < 1) : xt t ≤ xt t' := by
  unfold xt
  have : Real.log (2 - 2 * t') ≤ Real.log (2 - 2 * t) := Real.log_le_log (by linarith) (by linarith)
  linarith

theorem xt_pos_of_half_lt {t : ℝ} (h : 1 / 2 < t) (h' : t < 1) : 0 < xt t := by
  unfold xt
  have : Real.log (2 - 2 * t) < 0 := Real.log_neg (by linarith) (by linarith)
  linarith

theorem xt_nonpos_of_le_half {t : ℝ} (h : t ≤ 1 / 2) : xt t ≤ 0 := by
  unfold xt
  have : 0 ≤ Real.log (2 - 2 * t) := Real.log_nonneg (by linarith)
  linarith

theorem phiS_mono_t {s : ℝ} (hs : 0 ≤ s) {t t' : ℝ} (h : t ≤ t') (h' : t' < 1) :
    phiS s t ≤ phiS s t' := by
  rw [phiS_eq_exp s (lt_of_le_of_lt h h'), phiS_eq_exp s h']
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (xt_mono h h') hs)

theorem phiS_mono_s_of_half_lt {t : ℝ} (ht : 1 / 2 < t) (ht' : t < 1) {s s' : ℝ} (h : s ≤ s') :
    phiS s t ≤ phiS s' t := by
  rw [phiS_eq_exp s ht', phiS_eq_exp s' ht']
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (xt_pos_of_half_lt ht ht').le)

theorem phiS_anti_s_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) {s s' : ℝ} (h : s ≤ s') :
    phiS s' t ≤ phiS s t := by
  have ht' : t < 1 := by linarith
  rw [phiS_eq_exp s ht', phiS_eq_exp s' ht']
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right h (xt_nonpos_of_le_half ht))

/-! ### Rational-exponent enclosures -/

theorem rpow_neg_div_pow_mul {u : ℝ} (hu : 0 < u) (p : ℕ) {m : ℕ} (hm : 0 < m) :
    (u ^ (-((p : ℝ) / m))) ^ m * u ^ p = 1 := by
  rw [← Real.rpow_natCast (u ^ _) m, ← Real.rpow_mul hu.le]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have : -((p : ℝ) / m) * (m : ℝ) = -(p : ℝ) := by field_simp
  rw [this, Real.rpow_neg hu.le, Real.rpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ hu.ne')

/-- `ℓ^m u^p ≤ 1 ⇒ ℓ ≤ u^(-p/m)`. -/
theorem rpow_lower_of_pow {u ℓ : ℝ} (hu : 0 < u) {p m : ℕ} (hm : 0 < m)
    (h : ℓ ^ m * u ^ p ≤ 1) : ℓ ≤ u ^ (-((p : ℝ) / m)) := by
  by_contra hlt
  rw [not_le] at hlt
  have hy : 0 ≤ u ^ (-((p : ℝ) / m)) := (Real.rpow_pos_of_pos hu _).le
  have h1 : (u ^ (-((p : ℝ) / m))) ^ m < ℓ ^ m := pow_lt_pow_left₀ hlt hy hm.ne'
  have h2 := rpow_neg_div_pow_mul hu p hm
  have hup : 0 < u ^ p := pow_pos hu p
  have h3 := mul_lt_mul_of_pos_right h1 hup
  linarith

/-- `1 ≤ U^m u^p ⇒ u^(-p/m) ≤ U` (for `U ≥ 0`). -/
theorem rpow_upper_of_pow {u U : ℝ} (hu : 0 < u) (hU : 0 ≤ U) {p m : ℕ} (hm : 0 < m)
    (h : 1 ≤ U ^ m * u ^ p) : u ^ (-((p : ℝ) / m)) ≤ U := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : U ^ m < (u ^ (-((p : ℝ) / m))) ^ m := pow_lt_pow_left₀ hlt hU hm.ne'
  have h2 := rpow_neg_div_pow_mul hu p hm
  have hup : 0 < u ^ p := pow_pos hu p
  have h3 := mul_lt_mul_of_pos_right h1 hup
  linarith

/-- `phiS (p/q) t` as a rational power with denominator `2q`. -/
theorem phiS_rat (p q : ℕ) (t : ℝ) :
    phiS ((p : ℝ) / q) t = (2 - 2 * t) ^ (-((p : ℝ) / ((2 * q : ℕ) : ℝ))) := by
  unfold phiS; congr 1; push_cast; ring

/-- Irrational base: if `u ∈ [ulo, uhi]`, `0 < ulo`, `ℓ^m uhi^p ≤ 1` then `ℓ ≤ u^(-p/m)`. -/
theorem rpow_lower_of_pow_base {u ulo uhi ℓ : ℝ} (hlo : 0 < ulo) (h1 : ulo ≤ u) (h2 : u ≤ uhi)
    {p m : ℕ} (hm : 0 < m) (h : ℓ ^ m * uhi ^ p ≤ 1) : ℓ ≤ u ^ (-((p : ℝ) / m)) := by
  have hz : -((p : ℝ) / m) ≤ 0 := by
    have : (0 : ℝ) ≤ (p : ℝ) / m := by positivity
    linarith
  exact (rpow_lower_of_pow (by linarith) hm h).trans
    (Real.rpow_le_rpow_of_nonpos (by linarith) h2 hz)

/-- Irrational base: if `u ∈ [ulo, uhi]`, `0 < ulo`, `1 ≤ U^m ulo^p` then `u^(-p/m) ≤ U`. -/
theorem rpow_upper_of_pow_base {u ulo uhi U : ℝ} (hlo : 0 < ulo) (h1 : ulo ≤ u) (_h2 : u ≤ uhi)
    (hU : 0 ≤ U) {p m : ℕ} (hm : 0 < m) (h : 1 ≤ U ^ m * ulo ^ p) : u ^ (-((p : ℝ) / m)) ≤ U := by
  have hz : -((p : ℝ) / m) ≤ 0 := by
    have : (0 : ℝ) ≤ (p : ℝ) / m := by positivity
    linarith
  exact (Real.rpow_le_rpow_of_nonpos hlo h1 hz).trans (rpow_upper_of_pow hlo hU hm h)

/-! ### The normalised gauge `psi s t = (phiS s t - 1)/s` -/

noncomputable def psi (s t : ℝ) : ℝ := (phiS s t - 1) / s

theorem psi_eq_exp (s : ℝ) {t : ℝ} (ht : t < 1) : psi s t = (Real.exp (s * xt t) - 1) / s := by
  unfold psi; rw [phiS_eq_exp s ht]

/-- For `t > 1/2` (i.e. `xt t > 0`), `s ↦ psi s t` is increasing on `s > 0`: `(e^(sx) - 1)/s = x · slope`,
and the secant slopes of the convex `exp` from `0` increase. -/
theorem psi_mono_s_of_half_lt {t : ℝ} (ht : 1 / 2 < t) (ht' : t < 1) {s s' : ℝ} (hs : 0 < s)
    (h : s ≤ s') : psi s t ≤ psi s' t := by
  have hx := xt_pos_of_half_lt ht ht'
  have hs' : 0 < s' := lt_of_lt_of_le hs h
  have hne : s * xt t ≠ 0 := (mul_pos hs hx).ne'
  have hne' : s' * xt t ≠ 0 := (mul_pos hs' hx).ne'
  have key := convexOn_exp.secant_mono (a := 0) (x := s * xt t) (y := s' * xt t)
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) hne hne'
    (mul_le_mul_of_nonneg_right h hx.le)
  simp only [Real.exp_zero, sub_zero] at key
  rw [psi_eq_exp s ht', psi_eq_exp s' ht']
  have e1 : (Real.exp (s * xt t) - 1) / s = xt t * ((Real.exp (s * xt t) - 1) / (s * xt t)) := by
    field_simp
  have e2 : (Real.exp (s' * xt t) - 1) / s' = xt t * ((Real.exp (s' * xt t) - 1) / (s' * xt t)) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left key hx.le

/-! ### Unit test (LEAN_PLAN_range.md §6 Phase 1): `phiS (19/48) (-9/10) = (19/5)^(-19/96)` to 25 digits -/

set_option profiler true in
set_option profiler.threshold 50 in
theorem test_phiS_19_48 :
    (7678054017156850448482709 : ℝ) / 10 ^ 25 ≤ phiS (19 / 48) (-9 / 10) ∧
      phiS (19 / 48) (-9 / 10) ≤ (7678054017156850448482710 : ℝ) / 10 ^ 25 := by
  have e : phiS (19 / 48) (-9 / 10) = (19 / 5 : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((96 : ℕ) : ℝ))) := by
    unfold phiS; norm_num
  rw [e]
  constructor
  · exact rpow_lower_of_pow (by norm_num) (by norm_num) (by norm_num)
  · exact rpow_upper_of_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RieszN7
