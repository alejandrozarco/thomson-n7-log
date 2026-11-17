import RieszN7.Cells.MinorR

/-!
# The seven true pin functions of the cap family and their polynomial bounds in `s` (generic part)

check_capR.py's kernel data vector (B3/B4 of `plan_range/PHASE2_cap.md`):
`v(s) = (φ(0), φ'(0), φ(−1), Re φ(c₁), Im φ(c₁), Re φ'(c₁), Im φ'(c₁))`, `φ = phiS s`, Re/Im with respect to `ℚ(√5)`
(`x = Re + Im √5`), so `Re φ(c₁) = (φ(c₁) + φ(c₂))/2`, `Im φ(c₁) = (φ(c₁) − φ(c₂))/(2√5)` and likewise for `φ'`.
`pinV s k` is that vector with the **true** derivatives `φ'(c) = s φ(c)/(2 − 2c)` (`hasDeriv_zero/k1/k2`).

Bounds: from two-sided polynomial models of the four base values `φ(0), φ(−1), φ(c₁), φ(c₂)` (all over one
denominator `D`) and a rational enclosure `ρn/ρd ≤ √5 ≤ σn/ρd`, `pinLo/pinHi` build integer lists with
`peval (pinLo k) s / (20 ρd D) ≤ pinV s k ≤ peval (pinHi k) s / (20 ρd D)` for `s ≥ 0` (`pin_bounds`).
The per-piece instances are generated (`gen_range/gen_cap_pins.py`, modules `RieszN7.Cap.Pins.P<a>_<b>`).
Private, AI-written (Phase 2b, CAP-M fork, 2026-11-08), not reviewed.
-/

open Real LogLean.Minor

namespace RieszN7.Cap.Pins
open RieszN7

/-- The contacts written out (`ThomsonN7.Base.c1 = (√5 − 1)/4`, `c2 = −(1 + √5)/4` unfold to these). -/
noncomputable def k1 : ℝ := (√5 - 1) / 4
noncomputable def k2 : ℝ := -(1 + √5) / 4

/-- The seven pins as separate functions. -/
noncomputable def pin0 (s : ℝ) : ℝ := phiS s 0
noncomputable def pin1 (s : ℝ) : ℝ := s * phiS s 0 / 2
noncomputable def pin2 (s : ℝ) : ℝ := phiS s (-1)
noncomputable def pin3 (s : ℝ) : ℝ := (phiS s k1 + phiS s k2) / 2
noncomputable def pin4 (s : ℝ) : ℝ := (phiS s k1 - phiS s k2) / (2 * √5)
noncomputable def pin5 (s : ℝ) : ℝ := (s * phiS s k1 / (2 - 2 * k1) + s * phiS s k2 / (2 - 2 * k2)) / 2
noncomputable def pin6 (s : ℝ) : ℝ := (s * phiS s k1 / (2 - 2 * k1) - s * phiS s k2 / (2 - 2 * k2)) / (2 * √5)

/-- **The seven true pins** (index order of check_capR's `Pin`). -/
noncomputable def pinV (s : ℝ) : Fin 7 → ℝ := ![pin0 s, pin1 s, pin2 s, pin3 s, pin4 s, pin5 s, pin6 s]

theorem sqrt5_sq : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)

theorem sqrt5_pos : 0 < √5 := Real.sqrt_pos.mpr (by norm_num)

theorem k1_lt_one : k1 < 1 := by
  unfold k1; have h := sqrt5_bounds; linarith [h.2]

theorem k2_lt_one : k2 < 1 := by
  unfold k2; have := sqrt5_pos; linarith

theorem two_sub_k1 : 2 - 2 * k1 = (5 - √5) / 2 := by unfold k1; ring

theorem two_sub_k2 : 2 - 2 * k2 = (5 + √5) / 2 := by unfold k2; ring

theorem phiS_deriv_eq (s : ℝ) {c : ℝ} (hc : c < 1) : s * phiS (s + 2) c = s * phiS s c / (2 - 2 * c) := by
  rw [phiS_add_two s hc]; ring

/-- The derivative pins are the true derivatives of `t ↦ phiS s t` (B4). -/
theorem hasDeriv_zero (s : ℝ) : HasDerivAt (fun t => phiS s t) (pin1 s) 0 := by
  have h := hasDerivAt_phiS s (t := 0) (by norm_num)
  rw [phiS_deriv_eq s (by norm_num : (0 : ℝ) < 1)] at h
  convert h using 1
  unfold pin1; ring

theorem hasDeriv_k1 (s : ℝ) : HasDerivAt (fun t => phiS s t) (s * phiS s k1 / (2 - 2 * k1)) k1 := by
  have h := hasDerivAt_phiS s k1_lt_one
  rwa [phiS_deriv_eq s k1_lt_one] at h

theorem hasDeriv_k2 (s : ℝ) : HasDerivAt (fun t => phiS s t) (s * phiS s k2 / (2 - 2 * k2)) k2 := by
  have h := hasDerivAt_phiS s k2_lt_one
  rwa [phiS_deriv_eq s k2_lt_one] at h

/-! ### Closed forms with rational coefficients in `√5` -/

theorem inv_2s5 : (2 * √5)⁻¹ = √5 / 10 := by
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  linear_combination (1 / 5 : ℝ) * sqrt5_sq

theorem inv_u1 : (2 - 2 * k1)⁻¹ = (5 + √5) / 10 := by
  rw [two_sub_k1]
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  linear_combination (-1 / 20 : ℝ) * sqrt5_sq

theorem inv_u2 : (2 - 2 * k2)⁻¹ = (5 - √5) / 10 := by
  rw [two_sub_k2]
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  linear_combination (-1 / 20 : ℝ) * sqrt5_sq

theorem pin4_eq (s : ℝ) : pin4 s = √5 * (phiS s k1 - phiS s k2) / 10 := by
  unfold pin4; rw [div_eq_mul_inv, inv_2s5]; ring

theorem pin5_eq (s : ℝ) : pin5 s = s * ((5 + √5) * phiS s k1 + (5 - √5) * phiS s k2) / 20 := by
  unfold pin5; rw [div_eq_mul_inv _ (2 - 2 * k1), div_eq_mul_inv _ (2 - 2 * k2), inv_u1, inv_u2]; ring

theorem pin6_eq (s : ℝ) : pin6 s = s * ((√5 + 1) * phiS s k1 - (√5 - 1) * phiS s k2) / 20 := by
  unfold pin6
  rw [div_eq_mul_inv _ (2 * √5), div_eq_mul_inv _ (2 - 2 * k1), div_eq_mul_inv _ (2 - 2 * k2), inv_2s5, inv_u1,
    inv_u2]
  linear_combination (s * (phiS s k1 + phiS s k2) / 100) * sqrt5_sq

/-! ### Signs of the base values -/

theorem phiS_k1_nonneg (s : ℝ) : 0 ≤ phiS s k1 := (phiS_pos s k1_lt_one).le

theorem phiS_k2_nonneg (s : ℝ) : 0 ≤ phiS s k2 := (phiS_pos s k2_lt_one).le

/-- `φ(c₁) ≥ φ(c₂)` (`c₂ ≤ c₁`, increasing in `t`). -/
theorem phiS_k2_le_k1 {s : ℝ} (hs : 0 ≤ s) : phiS s k2 ≤ phiS s k1 := by
  apply phiS_mono_t hs _ k1_lt_one
  unfold k1 k2; have := sqrt5_pos; linarith

/-! ### The pin lists -/

/-- `0 :: l`, i.e. `s · l(s)`. -/
def xmul (l : List ℤ) : List ℤ := 0 :: l

theorem peval_xmul (l : List ℤ) (s : ℝ) : peval (xmul l) s = s * peval l s := by
  simp [xmul, peval]

/-- The base model lists (lower `L*`, upper `U*`, common denominator `D`) and the `√5` enclosure
`ρn/ρd ≤ √5 ≤ σn/ρd`. -/
structure Base where
  Lz : List ℤ
  Uz : List ℤ
  Lm : List ℤ
  Um : List ℤ
  LA : List ℤ
  UA : List ℤ
  LB : List ℤ
  UB : List ℤ
  ρn : ℕ
  σn : ℕ
  ρd : ℕ

def lo0 (b : Base) : List ℤ := pscale (20 * b.ρd) b.Lz
def hi0 (b : Base) : List ℤ := pscale (20 * b.ρd) b.Uz
def lo1 (b : Base) : List ℤ := xmul (pscale (10 * b.ρd) b.Lz)
def hi1 (b : Base) : List ℤ := xmul (pscale (10 * b.ρd) b.Uz)
def lo2 (b : Base) : List ℤ := pscale (20 * b.ρd) b.Lm
def hi2 (b : Base) : List ℤ := pscale (20 * b.ρd) b.Um
def lo3 (b : Base) : List ℤ := pscale (10 * b.ρd) (padd b.LA b.LB)
def hi3 (b : Base) : List ℤ := pscale (10 * b.ρd) (padd b.UA b.UB)
def lo4 (b : Base) : List ℤ := pscale (2 * b.ρn) (padd b.LA (pscale (-1) b.UB))
def hi4 (b : Base) : List ℤ := pscale (2 * b.σn) (padd b.UA (pscale (-1) b.LB))
def lo5 (b : Base) : List ℤ :=
  xmul (padd (pscale (5 * b.ρd + b.ρn) b.LA) (pscale (5 * (b.ρd : ℤ) - b.σn) b.LB))
def hi5 (b : Base) : List ℤ :=
  xmul (padd (pscale (5 * b.ρd + b.σn) b.UA) (pscale (5 * (b.ρd : ℤ) - b.ρn) b.UB))
def lo6 (b : Base) : List ℤ :=
  xmul (padd (pscale (b.ρn + b.ρd) b.LA) (pscale (-((b.σn : ℤ) - b.ρd)) b.UB))
def hi6 (b : Base) : List ℤ :=
  xmul (padd (pscale (b.σn + b.ρd) b.UA) (pscale (-((b.ρn : ℤ) - b.ρd)) b.LB))

/-- Lower and upper pin lists (denominator `20 ρd D`). -/
def pinLo (b : Base) : Fin 7 → List ℤ := ![lo0 b, lo1 b, lo2 b, lo3 b, lo4 b, lo5 b, lo6 b]
def pinHi (b : Base) : Fin 7 → List ℤ := ![hi0 b, hi1 b, hi2 b, hi3 b, hi4 b, hi5 b, hi6 b]

/-- Hypotheses of `pin_bounds` at one `s`: the eight base bounds over `D` (scaled form) and the `√5` enclosure. -/
structure BaseOK (b : Base) (D : ℕ) (s : ℝ) : Prop where
  hD : 0 < D
  hρd : 0 < b.ρd
  hρ : (b.ρn : ℝ) ≤ √5 * b.ρd
  hσ : √5 * b.ρd ≤ b.σn
  hσ5 : (b.σn : ℝ) ≤ 5 * b.ρd
  hρ1 : (b.ρd : ℝ) ≤ b.ρn
  z0 : peval b.Lz s ≤ D * phiS s 0
  z1 : D * phiS s 0 ≤ peval b.Uz s
  m0 : peval b.Lm s ≤ D * phiS s (-1)
  m1 : D * phiS s (-1) ≤ peval b.Um s
  A0 : peval b.LA s ≤ D * phiS s k1
  A1 : D * phiS s k1 ≤ peval b.UA s
  B0 : peval b.LB s ≤ D * phiS s k2
  B1 : D * phiS s k2 ≤ peval b.UB s

section bounds
variable {b : Base} {D : ℕ} {s : ℝ} (hs : 0 ≤ s) (h : BaseOK b D s)
include hs h

/-- Shorthand: `K = 20 ρd D`. -/
theorem b0 : peval (lo0 b) s ≤ 20 * b.ρd * D * pin0 s ∧ 20 * b.ρd * D * pin0 s ≤ peval (hi0 b) s := by
  have hρ : (0 : ℝ) ≤ 20 * b.ρd := by positivity
  simp only [lo0, hi0, peval_pscale, pin0]; push_cast
  constructor
  · have := mul_le_mul_of_nonneg_left h.z0 hρ; linarith
  · have := mul_le_mul_of_nonneg_left h.z1 hρ; linarith

theorem b1 : peval (lo1 b) s ≤ 20 * b.ρd * D * pin1 s ∧ 20 * b.ρd * D * pin1 s ≤ peval (hi1 b) s := by
  have hρ : (0 : ℝ) ≤ 10 * b.ρd * s := by positivity
  simp only [lo1, hi1, peval_xmul, peval_pscale, pin1]; push_cast
  constructor
  · have := mul_le_mul_of_nonneg_left h.z0 hρ; linarith
  · have := mul_le_mul_of_nonneg_left h.z1 hρ; linarith

theorem b2 : peval (lo2 b) s ≤ 20 * b.ρd * D * pin2 s ∧ 20 * b.ρd * D * pin2 s ≤ peval (hi2 b) s := by
  have hρ : (0 : ℝ) ≤ 20 * b.ρd := by positivity
  simp only [lo2, hi2, peval_pscale, pin2]; push_cast
  constructor
  · have := mul_le_mul_of_nonneg_left h.m0 hρ; linarith
  · have := mul_le_mul_of_nonneg_left h.m1 hρ; linarith

theorem b3 : peval (lo3 b) s ≤ 20 * b.ρd * D * pin3 s ∧ 20 * b.ρd * D * pin3 s ≤ peval (hi3 b) s := by
  have hρ : (0 : ℝ) ≤ 10 * b.ρd := by positivity
  simp only [lo3, hi3, peval_pscale, peval_padd, pin3]; push_cast
  constructor
  · have := mul_le_mul_of_nonneg_left (add_le_add h.A0 h.B0) hρ; linarith
  · have := mul_le_mul_of_nonneg_left (add_le_add h.A1 h.B1) hρ; linarith

theorem b4 : peval (lo4 b) s ≤ 20 * b.ρd * D * pin4 s ∧ 20 * b.ρd * D * pin4 s ≤ peval (hi4 b) s := by
  have hD : (0 : ℝ) ≤ D := by positivity
  have hAB : 0 ≤ D * (phiS s k1 - phiS s k2) := mul_nonneg hD (sub_nonneg.mpr (phiS_k2_le_k1 hs))
  have hρn : (0 : ℝ) ≤ 2 * b.ρn := by positivity
  have hσn : (0 : ℝ) ≤ 2 * b.σn := by positivity
  rw [pin4_eq]
  simp only [lo4, hi4, peval_pscale, peval_padd]; push_cast
  constructor
  · have e1 : peval b.LA s + -1 * peval b.UB s ≤ D * (phiS s k1 - phiS s k2) := by linarith [h.A0, h.B1]
    have e2 := mul_le_mul_of_nonneg_left e1 hρn
    have e3 := mul_le_mul_of_nonneg_right h.hρ hAB
    nlinarith
  · have e1 : D * (phiS s k1 - phiS s k2) ≤ peval b.UA s + -1 * peval b.LB s := by linarith [h.A1, h.B0]
    have e2 := mul_le_mul_of_nonneg_left e1 hσn
    have e3 := mul_le_mul_of_nonneg_right h.hσ hAB
    nlinarith

theorem b5 : peval (lo5 b) s ≤ 20 * b.ρd * D * pin5 s ∧ 20 * b.ρd * D * pin5 s ≤ peval (hi5 b) s := by
  have hD : (0 : ℝ) ≤ D := by positivity
  have hA : 0 ≤ D * phiS s k1 := mul_nonneg hD (phiS_k1_nonneg s)
  have hB : 0 ≤ D * phiS s k2 := mul_nonneg hD (phiS_k2_nonneg s)
  have h5 := sqrt5_pos
  have hρ := h.hρ; have hσ := h.hσ; have hσ5 := h.hσ5
  rw [pin5_eq]
  simp only [lo5, hi5, peval_xmul, peval_pscale, peval_padd]; push_cast
  constructor
  · -- (5ρd + ρn) LA + (5ρd − σn) LB ≤ ρd ((5+√5) DA + (5−√5) DB)
    have c1 := mul_le_mul_of_nonneg_left h.A0 (by positivity : (0 : ℝ) ≤ 5 * b.ρd + b.ρn)
    have c2 := mul_le_mul_of_nonneg_left h.B0 (by linarith : (0 : ℝ) ≤ 5 * b.ρd - b.σn)
    have c3 := mul_le_mul_of_nonneg_right hρ hA
    have c4 := mul_le_mul_of_nonneg_right hσ hB
    have key : (5 * b.ρd + b.ρn : ℝ) * peval b.LA s + (5 * b.ρd - b.σn) * peval b.LB s
        ≤ b.ρd * ((5 + √5) * (D * phiS s k1) + (5 - √5) * (D * phiS s k2)) := by nlinarith
    have := mul_le_mul_of_nonneg_left key hs
    nlinarith
  · have c1 := mul_le_mul_of_nonneg_left h.A1 (by positivity : (0 : ℝ) ≤ 5 * b.ρd + b.σn)
    have c2 := mul_le_mul_of_nonneg_left h.B1 (by nlinarith : (0 : ℝ) ≤ 5 * b.ρd - b.ρn)
    have c3 := mul_le_mul_of_nonneg_right hσ hA
    have c4 := mul_le_mul_of_nonneg_right hρ hB
    have key : b.ρd * ((5 + √5) * (D * phiS s k1) + (5 - √5) * (D * phiS s k2))
        ≤ (5 * b.ρd + b.σn : ℝ) * peval b.UA s + (5 * b.ρd - b.ρn) * peval b.UB s := by nlinarith
    have := mul_le_mul_of_nonneg_left key hs
    nlinarith

theorem b6 : peval (lo6 b) s ≤ 20 * b.ρd * D * pin6 s ∧ 20 * b.ρd * D * pin6 s ≤ peval (hi6 b) s := by
  have hD : (0 : ℝ) ≤ D := by positivity
  have hA : 0 ≤ D * phiS s k1 := mul_nonneg hD (phiS_k1_nonneg s)
  have hB : 0 ≤ D * phiS s k2 := mul_nonneg hD (phiS_k2_nonneg s)
  have h5 := sqrt5_pos
  have hρ := h.hρ; have hσ := h.hσ; have hρ1 := h.hρ1
  rw [pin6_eq]
  simp only [lo6, hi6, peval_xmul, peval_pscale, peval_padd]; push_cast
  constructor
  · have c1 := mul_le_mul_of_nonneg_left h.A0 (by positivity : (0 : ℝ) ≤ b.ρn + b.ρd)
    have c2 := mul_le_mul_of_nonneg_left h.B1 (by nlinarith : (0 : ℝ) ≤ b.σn - b.ρd)
    have c3 := mul_le_mul_of_nonneg_right hρ hA
    have c4 := mul_le_mul_of_nonneg_right hσ hB
    have key : (b.ρn + b.ρd : ℝ) * peval b.LA s + -((b.σn : ℝ) - b.ρd) * peval b.UB s
        ≤ b.ρd * ((√5 + 1) * (D * phiS s k1) - (√5 - 1) * (D * phiS s k2)) := by nlinarith
    have := mul_le_mul_of_nonneg_left key hs
    nlinarith
  · have c1 := mul_le_mul_of_nonneg_left h.A1 (by positivity : (0 : ℝ) ≤ b.σn + b.ρd)
    have c2 := mul_le_mul_of_nonneg_left h.B0 (by linarith : (0 : ℝ) ≤ b.ρn - b.ρd)
    have c3 := mul_le_mul_of_nonneg_right hσ hA
    have c4 := mul_le_mul_of_nonneg_right hρ hB
    have key : b.ρd * ((√5 + 1) * (D * phiS s k1) - (√5 - 1) * (D * phiS s k2))
        ≤ (b.σn + b.ρd : ℝ) * peval b.UA s + -((b.ρn : ℝ) - b.ρd) * peval b.LB s := by nlinarith
    have := mul_le_mul_of_nonneg_left key hs
    nlinarith

/-- **Pin bounds** (scaled form): `peval (pinLo b k) s ≤ 20 ρd D · pinV s k ≤ peval (pinHi b k) s`. -/
theorem pin_bounds (k : Fin 7) :
    peval (pinLo b k) s ≤ 20 * b.ρd * D * pinV s k ∧ 20 * b.ρd * D * pinV s k ≤ peval (pinHi b k) s := by
  fin_cases k
  exacts [b0 hs h, b1 hs h, b2 hs h, b3 hs h, b4 hs h, b5 hs h, b6 hs h]

/-- The interface for Step P: `|40 ρd D · pinV s k − peval (lo + hi) s| ≤ peval (hi − lo) s`. -/
theorem pin_abs (k : Fin 7) :
    |40 * b.ρd * D * pinV s k - peval (padd (pinLo b k) (pinHi b k)) s|
      ≤ peval (padd (pinHi b k) (pscale (-1) (pinLo b k))) s := by
  obtain ⟨h1, h2⟩ := pin_bounds hs h k
  rw [peval_padd, peval_padd, peval_pscale, abs_le]
  push_cast
  constructor <;> linarith

end bounds

end RieszN7.Cap.Pins
