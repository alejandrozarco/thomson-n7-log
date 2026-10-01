/-
LogSeries.lean — odd Taylor lower bound for `-log(1-u)`.

Theorem: for every odd n and every real u < 1,
    ∑_{k=1}^{n} u^k / k ≤ -log(1-u).

Proof idea (as in the plan): let
    g(u) := -log(1-u) - S_n(u),   S_n(u) := ∑_{i=0}^{n-1} u^(i+1)/(i+1).
Then g(0) = 0 and g'(u) = u^n/(1-u) for all u ≠ 1. Since n is odd, u^n has the same
sign as u, and 1 - u > 0 on u < 1, so g' ≥ 0 on [0,1) and g' ≤ 0 on (-∞,0]. Hence g is
monotone increasing on [0,1) and monotone decreasing on (-∞,0], so g ≥ g(0) = 0 everywhere
on (-∞,1). This is self-contained (does not need Mathlib's `HasSum` machinery, which only
covers |u| < 1); it only uses elementary derivative combinators and the two mean-value
monotonicity lemmas `monotoneOn_of_hasDerivWithinAt_nonneg` / `antitoneOn_of_hasDerivWithinAt_nonpos`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Finset

namespace LogLean

/-- The degree-`n` truncated Taylor polynomial of `-log(1-u)` at `0`,
`S_n(u) = ∑_{i=0}^{n-1} u^(i+1)/(i+1) = ∑_{k=1}^{n} u^k/k`. -/
noncomputable def logTaylor (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, u ^ (i + 1) / ((i : ℝ) + 1)

/-- `g(u) := -log(1-u) - S_n(u)`. -/
noncomputable def logGap (n : ℕ) (u : ℝ) : ℝ :=
  -Real.log (1 - u) - logTaylor n u

@[simp] theorem logGap_zero (n : ℕ) : logGap n 0 = 0 := by
  simp [logGap, logTaylor]

/-- The derivative of the finite Taylor sum: `S_n'(y) = ∑_{i<n} y^i`. -/
theorem hasDerivAt_logTaylor (n : ℕ) (y : ℝ) :
    HasDerivAt (logTaylor n) (∑ i ∈ Finset.range n, y ^ i) y := by
  have h : HasDerivAt (logTaylor n)
      (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * y ^ i / ((i : ℝ) + 1)) y := by
    unfold logTaylor
    refine HasDerivAt.fun_sum (fun i _ => ?_)
    have hd := (hasDerivAt_pow (i + 1) y).div_const ((i : ℝ) + 1)
    simpa [Nat.add_sub_cancel, Nat.cast_add_one] using hd
  refine h.congr_deriv (Finset.sum_congr rfl (fun i _ => ?_))
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The derivative of `g` at any point `y ≠ 1`: `g'(y) = y^n / (1-y)`. -/
theorem hasDerivAt_logGap (n : ℕ) {y : ℝ} (hy : y ≠ 1) :
    HasDerivAt (logGap n) (y ^ n / (1 - y)) y := by
  have hne : (1 : ℝ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have h1 : HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (1 / (1 - y)) y := by
    have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1 : ℝ) / (1 - y)) y :=
      ((hasDerivAt_id y).const_sub (1 : ℝ)).log hne
    have hneg := hlog.fun_neg
    simpa [neg_div] using hneg
  have h2 := hasDerivAt_logTaylor n y
  have hsum : HasDerivAt (fun x => -Real.log (1 - x) - logTaylor n x)
      (1 / (1 - y) - ∑ i ∈ Finset.range n, y ^ i) y := h1.fun_sub h2
  show HasDerivAt (fun x => -Real.log (1 - x) - logTaylor n x) (y ^ n / (1 - y)) y
  refine hsum.congr_deriv ?_
  have hgeo : ∑ i ∈ Finset.range n, y ^ i = (y ^ n - 1) / (y - 1) := geom_sum_eq hy n
  rw [hgeo]
  field_simp
  ring

/-- **Key lemma**: for odd `n` and every real `u < 1`,
`∑_{k=1}^{n} u^k/k ≤ -log(1-u)`. -/
theorem sum_le_neg_log_one_sub {n : ℕ} (hn : Odd n) {u : ℝ} (hu : u < 1) :
    logTaylor n u ≤ -Real.log (1 - u) := by
  suffices h0 : 0 ≤ logGap n u by
    have heq : logTaylor n u + logGap n u = -Real.log (1 - u) := by unfold logGap; ring
    linarith
  by_cases hupos : 0 ≤ u
  · -- monotone increasing on [0,1)
    have hderiv : ∀ x ∈ interior (Set.Ico (0:ℝ) 1),
        HasDerivWithinAt (logGap n) (x ^ n / (1 - x)) (interior (Set.Ico (0:ℝ) 1)) x := by
      intro x hx
      rw [interior_Ico] at hx
      have hx2 : x < 1 := (Set.mem_Ioo.mp hx).2
      exact (hasDerivAt_logGap n (ne_of_lt hx2)).hasDerivWithinAt
    have hcont : ContinuousOn (logGap n) (Set.Ico (0:ℝ) 1) := by
      have h1 : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (Set.Ico (0:ℝ) 1) :=
        ((continuousOn_const.sub continuousOn_id).log
          (fun x hx => sub_ne_zero.mpr (fun h => by
            have hx2 : x < 1 := (Set.mem_Ico.mp hx).2
            have h' : (1:ℝ) = x := h
            linarith [h'.symm]))).neg
      have h2 : ContinuousOn (logTaylor n) (Set.Ico (0:ℝ) 1) := by
        unfold logTaylor
        exact continuousOn_finsetSum _ (fun i _ => (continuousOn_pow (i + 1)).div_const _)
      unfold logGap
      exact h1.sub h2
    have hnonneg : ∀ x ∈ interior (Set.Ico (0:ℝ) 1), 0 ≤ x ^ n / (1 - x) := by
      intro x hx
      rw [interior_Ico] at hx
      obtain ⟨hx1, hx2⟩ := Set.mem_Ioo.mp hx
      exact div_nonneg (pow_nonneg hx1.le n) (by linarith)
    have hmono : MonotoneOn (logGap n) (Set.Ico (0:ℝ) 1) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) hcont hderiv hnonneg
    have h0mem : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩
    have humem : u ∈ Set.Ico (0:ℝ) 1 := Set.mem_Ico.mpr ⟨hupos, hu⟩
    have hle := hmono h0mem humem hupos
    simpa using hle
  · -- antitone (decreasing) on (-∞,0]
    push Not at hupos
    have hderiv : ∀ x ∈ interior (Set.Iic (0:ℝ)),
        HasDerivWithinAt (logGap n) (x ^ n / (1 - x)) (interior (Set.Iic (0:ℝ))) x := by
      intro x hx
      rw [interior_Iic] at hx
      have hx0 : x < 0 := Set.mem_Iio.mp hx
      exact (hasDerivAt_logGap n (by intro h; rw [h] at hx0; exact absurd hx0 (by norm_num))).hasDerivWithinAt
    have hcont : ContinuousOn (logGap n) (Set.Iic (0:ℝ)) := by
      have h1 : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (Set.Iic (0:ℝ)) :=
        ((continuousOn_const.sub continuousOn_id).log
          (fun x hx => sub_ne_zero.mpr (fun h => by
            have hx0 : x ≤ 0 := Set.mem_Iic.mp hx
            have h' : (1:ℝ) = x := h
            linarith [h'.symm]))).neg
      have h2 : ContinuousOn (logTaylor n) (Set.Iic (0:ℝ)) := by
        unfold logTaylor
        exact continuousOn_finsetSum _ (fun i _ => (continuousOn_pow (i + 1)).div_const _)
      unfold logGap
      exact h1.sub h2
    have hnonpos : ∀ x ∈ interior (Set.Iic (0:ℝ)), x ^ n / (1 - x) ≤ 0 := by
      intro x hx
      rw [interior_Iic] at hx
      have hx0 : x < 0 := Set.mem_Iio.mp hx
      exact div_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos hn hx0.le) (by linarith)
    have hanti : AntitoneOn (logGap n) (Set.Iic (0:ℝ)) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0) hcont hderiv hnonpos
    have h0mem : (0:ℝ) ∈ Set.Iic (0:ℝ) := Set.mem_Iic.mpr (le_refl 0)
    have humem : u ∈ Set.Iic (0:ℝ) := Set.mem_Iic.mpr hupos.le
    have hge := hanti humem h0mem hupos.le
    simpa using hge

end LogLean
