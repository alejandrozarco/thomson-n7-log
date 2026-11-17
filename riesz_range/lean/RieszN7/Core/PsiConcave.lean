import RieszN7.Core.Rpow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# `RieszN7.Core.PsiConcave` — concavity of the normalised gauge in `s` for `t ≤ 1/2` (LEAN_PLAN_range.md §3.0.4)

For `x ≤ 0` the function `s ↦ (e^{s x} - 1)/s` is concave on `s > 0`: its second derivative is
`(e^y (y² - 2y + 2) - 2)/s³` with `y = s x ≤ 0`, and `e^y (y² - 2y + 2) ≤ 2` for `y ≤ 0` is
`z² + 2z + 2 ≤ 2 e^z` (`z = -y ≥ 0`, `Real.quadratic_le_exp_of_nonneg`).  Hence `psi s t = (phiS s t - 1)/s` is
concave in `s > 0` for `t ≤ 1/2` (`xt t ≤ 0`), and so is `psi s t - (α + β s)`; on `[a, b] ⊂ (0, ∞)` it is therefore
`≥` the smaller of its two end values (`psi_sub_affine_ge_min`): the cell condition (H) on `t ≤ 1/2` reduces to the
two nodes.
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Real

namespace RieszN7

theorem exp_mul_quad_le_two {y : ℝ} (hy : y ≤ 0) : Real.exp y * (y ^ 2 - 2 * y + 2) ≤ 2 := by
  have hz : 0 ≤ -y := by linarith
  have h1 := Real.quadratic_le_exp_of_nonneg hz
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp y := Real.exp_pos y
  have h3 := mul_le_mul_of_nonneg_left h1 hpos.le
  nlinarith

/-- `s ↦ (e^{s x} - 1)/s` is concave on `(0, ∞)` for `x ≤ 0`. -/
theorem expSec_concave {x : ℝ} (hx : x ≤ 0) :
    ConcaveOn ℝ (Set.Ioi 0) (fun s => (Real.exp (s * x) - 1) / s) := by
  have hE : ∀ s : ℝ, HasDerivAt (fun s => Real.exp (s * x)) (Real.exp (s * x) * x) s := fun s => by
    simpa using ((hasDerivAt_id s).mul_const x).exp
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
    (f' := fun s => (Real.exp (s * x) * x * s - (Real.exp (s * x) - 1)) / s ^ 2)
    (f'' := fun s => ((Real.exp (s * x) * x * x * s + Real.exp (s * x) * x - Real.exp (s * x) * x) * s ^ 2
        - (Real.exp (s * x) * x * s - (Real.exp (s * x) - 1)) * (2 * s)) / (s ^ 2) ^ 2)
  · intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hc : HasDerivAt (fun s => Real.exp (s * x) - 1) (Real.exp (s * x) * x) s :=
      HasDerivAt.sub_const 1 (hE s)
    have h1 : HasDerivAt (fun s => (Real.exp (s * x) - 1) / s)
        (((Real.exp (s * x) * x) * s - (Real.exp (s * x) - 1) * 1) / s ^ 2) s :=
      HasDerivAt.fun_div hc (hasDerivAt_id s) hs0
    exact h1.continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
    have hc : HasDerivAt (fun s => Real.exp (s * x) - 1) (Real.exp (s * x) * x) s :=
      HasDerivAt.sub_const 1 (hE s)
    have h1 : HasDerivAt (fun s => (Real.exp (s * x) - 1) / s)
        (((Real.exp (s * x) * x) * s - (Real.exp (s * x) - 1) * 1) / s ^ 2) s :=
      HasDerivAt.fun_div hc (hasDerivAt_id s) hs0
    rw [mul_one] at h1
    exact h1.hasDerivWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
    have hm : HasDerivAt (fun s => Real.exp (s * x) * x) (Real.exp (s * x) * x * x) s :=
      HasDerivAt.mul_const (hE s) x
    have ha : HasDerivAt (fun s => Real.exp (s * x) * x * s)
        (Real.exp (s * x) * x * x * s + Real.exp (s * x) * x * 1) s :=
      HasDerivAt.fun_mul hm (hasDerivAt_id s)
    have hc : HasDerivAt (fun s => Real.exp (s * x) - 1) (Real.exp (s * x) * x) s :=
      HasDerivAt.sub_const 1 (hE s)
    have hN : HasDerivAt (fun s => Real.exp (s * x) * x * s - (Real.exp (s * x) - 1))
        ((Real.exp (s * x) * x * x * s + Real.exp (s * x) * x * 1) - Real.exp (s * x) * x) s :=
      HasDerivAt.fun_sub ha hc
    have hD : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
      simpa using HasDerivAt.fun_pow (hasDerivAt_id s) 2
    have h := HasDerivAt.fun_div hN hD (pow_ne_zero 2 hs0)
    rw [mul_one] at h
    exact h.hasDerivWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    have hs' : 0 < s := Set.mem_Ioi.mp hs
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hb := exp_mul_quad_le_two (y := s * x) (by nlinarith)
    have e : (Real.exp (s * x) * x * x * s + Real.exp (s * x) * x - Real.exp (s * x) * x) * s ^ 2
        - (Real.exp (s * x) * x * s - (Real.exp (s * x) - 1)) * (2 * s)
        = s * (Real.exp (s * x) * ((s * x) ^ 2 - 2 * (s * x) + 2) - 2) := by ring
    rw [e]
    exact mul_nonpos_of_nonneg_of_nonpos hs'.le (by linarith)

/-- `s ↦ psi s t` is concave on `(0, ∞)` for `t ≤ 1/2`. -/
theorem psi_concave {t : ℝ} (ht : t ≤ 1 / 2) : ConcaveOn ℝ (Set.Ioi 0) (fun s => psi s t) := by
  have ht' : t < 1 := by linarith
  have e : (fun s => psi s t) = fun s => (Real.exp (s * xt t) - 1) / s :=
    funext fun s => psi_eq_exp s ht'
  rw [e]
  exact expSec_concave (xt_nonpos_of_le_half ht)

/-- A concave function minus an affine one is `≥` the smaller end value on `[a, b] ⊂ (0, ∞)`. -/
theorem concave_sub_affine_ge_min {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ioi 0) f) {a b s α β : ℝ}
    (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) :
    min (f a - (α + β * a)) (f b - (α + β * b)) ≤ f s - (α + β * s) := by
  rcases eq_or_lt_of_le (has.trans hsb) with hab | hab
  · have hs : s = a := le_antisymm (hab ▸ hsb) has
    subst hs
    exact min_le_left _ _
  set l := (s - a) / (b - a) with hl
  have hba : 0 < b - a := by linarith
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hba.le
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hba]; linarith
  have hsl : (1 - l) * a + l * b = s := by rw [hl]; field_simp; ring
  have hmem : ∀ y, a ≤ y → y ∈ Set.Ioi (0 : ℝ) := fun y hy => Set.mem_Ioi.mpr (lt_of_lt_of_le ha hy)
  have hc := hf.2 (hmem a le_rfl) (hmem b hab.le) (by linarith : 0 ≤ 1 - l) hl0 (by ring)
  simp only [smul_eq_mul] at hc
  rw [hsl] at hc
  have hm : min (f a - (α + β * a)) (f b - (α + β * b))
      ≤ (1 - l) * (f a - (α + β * a)) + l * (f b - (α + β * b)) := by
    rcases le_total (f a - (α + β * a)) (f b - (α + β * b)) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have e : (1 - l) * (f a - (α + β * a)) + l * (f b - (α + β * b))
      = (1 - l) * f a + l * f b - (α + β * ((1 - l) * a + l * b)) := by ring
  rw [e, hsl] at hm
  linarith

/-- **Condition (H) on `t ≤ 1/2` reduces to the two nodes.** -/
theorem psi_sub_affine_ge_min {t : ℝ} (ht : t ≤ 1 / 2) {a b s α β : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hsb : s ≤ b) :
    min (psi a t - (α + β * a)) (psi b t - (α + β * b)) ≤ psi s t - (α + β * s) :=
  concave_sub_affine_ge_min (psi_concave ht) ha has hsb

end RieszN7
