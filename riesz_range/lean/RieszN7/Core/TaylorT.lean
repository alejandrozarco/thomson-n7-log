import RieszN7.Core.Rpow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# `RieszN7.Core.TaylorT` — Taylor minorants of `phiS s` in `t` (LEAN_PLAN_range.md §3.0.3)

All `t`-derivatives of `phiS s` are positive for `s ≥ 0`: `∂ₜ phiS s t = s · phiS (s+2) t`.  With
`c_k(s) = ∏_{i<k} (s + 2i) / k!` and a node `g < 1`,

    taylorT g n s t = phiS s g · Σ_{k ≤ n} c_k(s) ((t - g)/(2 - 2g))^k,

and the remainder `remT g n s t = phiS s t - taylorT g n s t` satisfies `∂ₜ remT g (n+1) s = s · remT g n (s+2)`
(since `(k+1) c_{k+1}(s) = s c_k(s+2)` and `phiS (s+2) g = phiS s g / (2 - 2g)`).  Induction on `n` with
`monotoneOn_of_deriv_nonneg` (no Lagrange remainder, no iterated derivatives) gives
* `phiS_ge_taylor_right`: `g ≤ t < 1 ⇒ taylorT g n s t ≤ phiS s t` (any `n`);
* `phiS_ge_taylor_odd`: `n` odd, `t < 1 ⇒ taylorT g n s t ≤ phiS s t` (both sides of `g`).
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Real Finset

namespace RieszN7

/-- `c_k(s) = ∏_{i<k} (s + 2i) / k!` (a polynomial in `s`). -/
noncomputable def cS (s : ℝ) (k : ℕ) : ℝ := (∏ i ∈ range k, (s + 2 * (i : ℝ))) / (k.factorial : ℝ)

theorem cS_zero (s : ℝ) : cS s 0 = 1 := by simp [cS]

theorem cS_succ_mul (s : ℝ) (j : ℕ) : cS s (j + 1) * ((j : ℝ) + 1) = s * cS (s + 2) j := by
  have hp : ∏ i ∈ range (j + 1), (s + 2 * (i : ℝ)) = s * ∏ i ∈ range j, (s + 2 + 2 * (i : ℝ)) := by
    rw [prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero]
    rw [mul_comm]
    congr 1
    exact prod_congr rfl fun i _ => by ring
  unfold cS
  rw [hp, Nat.factorial_succ]
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- `phiS (s+2) g = phiS s g / (2 - 2g)` for `g < 1`. -/
theorem phiS_add_two (s : ℝ) {g : ℝ} (hg : g < 1) : phiS (s + 2) g = phiS s g / (2 - 2 * g) := by
  have hu : 0 < 2 - 2 * g := by linarith
  unfold phiS
  rw [show -((s + 2) / 2) = -(s / 2) + (-1) by ring, Real.rpow_add hu, Real.rpow_neg_one]
  ring

/-- `∂ₜ phiS s t = s · phiS (s+2) t` for `t < 1`. -/
theorem hasDerivAt_phiS (s : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t => phiS s t) (s * phiS (s + 2) t) t := by
  have hu : 0 < 2 - 2 * t := by linarith
  have h1 : HasDerivAt (fun t : ℝ => 2 - 2 * t) (-2) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).const_sub (2 : ℝ)
  have h2 := h1.rpow_const (p := -(s / 2)) (Or.inl hu.ne')
  unfold phiS
  convert h2 using 1
  rw [show -((s + 2) / 2) = -(s / 2) - 1 by ring]
  ring

/-- The Taylor polynomial of `phiS s` at `g`, of order `n`, in the variable `t`. -/
noncomputable def taylorT (g : ℝ) (n : ℕ) (s t : ℝ) : ℝ :=
  phiS s g * ∑ k ∈ range (n + 1), cS s k * ((t - g) / (2 - 2 * g)) ^ k

theorem taylorT_at (g : ℝ) (n : ℕ) (s : ℝ) : taylorT g n s g = phiS s g := by
  unfold taylorT
  rw [sum_range_succ']
  simp [cS_zero]

theorem taylorT_zero (g : ℝ) (s t : ℝ) : taylorT g 0 s t = phiS s g := by
  simp [taylorT, cS_zero]

theorem hasDerivAt_taylorT (g : ℝ) (n : ℕ) (s : ℝ) (hg : g < 1) (t : ℝ) :
    HasDerivAt (fun t => taylorT g (n + 1) s t) (s * taylorT g n (s + 2) t) t := by
  set w := 2 - 2 * g with hw_def
  have hw : w ≠ 0 := by rw [hw_def]; intro h; linarith
  have hy : HasDerivAt (fun t : ℝ => (t - g) / w) (1 / w) t :=
    ((hasDerivAt_id t).sub_const g).div_const w
  have hk : ∀ k ∈ range (n + 1 + 1), HasDerivAt (fun t => cS s k * ((t - g) / w) ^ k)
      (cS s k * ((k : ℝ) * ((t - g) / w) ^ (k - 1) * (1 / w))) t :=
    fun k _ => (hy.fun_pow k).const_mul _
  have hT := (HasDerivAt.fun_sum hk).const_mul (phiS s g)
  unfold taylorT
  rw [← hw_def]
  convert hT using 1
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  rw [phiS_add_two s hg, ← hw_def, mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hc := cS_succ_mul s j
  push_cast
  have e : phiS s g * (cS s (j + 1) * (((j : ℝ) + 1) * ((t - g) / w) ^ j * (1 / w)))
      = phiS s g * (cS s (j + 1) * ((j : ℝ) + 1)) * ((t - g) / w) ^ j / w := by ring
  rw [e, hc]
  ring

/-- The remainder `phiS s t - taylorT g n s t`. -/
noncomputable def remT (g : ℝ) (n : ℕ) (s t : ℝ) : ℝ := phiS s t - taylorT g n s t

theorem remT_at (g : ℝ) (n : ℕ) (s : ℝ) : remT g n s g = 0 := by
  unfold remT; rw [taylorT_at]; ring

theorem remT_zero (g s t : ℝ) : remT g 0 s t = phiS s t - phiS s g := by
  unfold remT; rw [taylorT_zero]

theorem hasDerivAt_remT (g : ℝ) (n : ℕ) (s : ℝ) (hg : g < 1) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t => remT g (n + 1) s t) (s * remT g n (s + 2) t) t := by
  have h := (hasDerivAt_phiS s ht).sub (hasDerivAt_taylorT g n s hg t)
  unfold remT
  convert h using 1
  ring

/-- Right of the node: every remainder is `≥ 0` (`s ≥ 0`). -/
theorem remT_nonneg_right {g : ℝ} (hg : g < 1) :
    ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ∀ t, g ≤ t → t < 1 → 0 ≤ remT g n s t := by
  intro n
  induction n with
  | zero =>
    intro s hs t h1 h2
    rw [remT_zero]
    linarith [phiS_mono_t hs h1 h2]
  | succ n ih =>
    intro s hs t h1 h2
    have hmono : MonotoneOn (fun x => remT g (n + 1) s x) (Set.Ico g 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ico g 1)
      · intro x hx
        exact (hasDerivAt_remT g n s hg hx.2).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        exact (hasDerivAt_remT g n s hg hx.2).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        rw [(hasDerivAt_remT g n s hg hx.2).deriv]
        exact mul_nonneg hs (ih (s + 2) (by linarith) x hx.1.le hx.2)
    have h := hmono ⟨le_refl g, hg⟩ ⟨h1, h2⟩ h1
    simp only [remT_at] at h
    exact h

/-- Left of the node: `(-1)^(n+1) · remT g n s t ≥ 0` (`s ≥ 0`, `t ≤ g`). -/
theorem remT_sign_left {g : ℝ} (hg : g < 1) :
    ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ∀ t, t ≤ g → 0 ≤ (-1 : ℝ) ^ (n + 1) * remT g n s t := by
  intro n
  induction n with
  | zero =>
    intro s hs t h
    rw [remT_zero]
    have := phiS_mono_t hs h hg
    simp only [zero_add, pow_one]
    linarith
  | succ n ih =>
    intro s hs t h
    have hd : ∀ x, x < 1 → HasDerivAt (fun x => (-1 : ℝ) ^ (n + 1) * remT g (n + 1) s x)
        ((-1 : ℝ) ^ (n + 1) * (s * remT g n (s + 2) x)) x :=
      fun x hx => (hasDerivAt_remT g n s hg hx).const_mul _
    have hF : MonotoneOn (fun x => (-1 : ℝ) ^ (n + 1) * remT g (n + 1) s x) (Set.Iic g) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic g)
      · intro x hx
        exact (hd x (lt_of_le_of_lt hx hg)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        exact (hd x (lt_trans hx hg)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Iic] at hx
        rw [(hd x (lt_trans hx hg)).deriv]
        have := ih (s + 2) (by linarith) x hx.le
        rw [show (-1 : ℝ) ^ (n + 1) * (s * remT g n (s + 2) x)
            = s * ((-1 : ℝ) ^ (n + 1) * remT g n (s + 2) x) by ring]
        exact mul_nonneg hs this
    have h' := hF (Set.mem_Iic.mpr h) (Set.mem_Iic.mpr le_rfl) h
    simp only [remT_at, mul_zero] at h'
    have e : (-1 : ℝ) ^ (n + 1 + 1) * remT g (n + 1) s t
        = -((-1 : ℝ) ^ (n + 1) * remT g (n + 1) s t) := by ring
    rw [e]
    linarith

/-- **Taylor minorant, right of the node** (any order). -/
theorem phiS_ge_taylor_right {g : ℝ} (hg : g < 1) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) {t : ℝ}
    (h1 : g ≤ t) (h2 : t < 1) : taylorT g n s t ≤ phiS s t := by
  have := remT_nonneg_right hg n s hs t h1 h2
  unfold remT at this
  linarith

/-- **Taylor minorant, odd order, both sides of the node.** -/
theorem phiS_ge_taylor_odd {g : ℝ} (hg : g < 1) {n : ℕ} (hn : Odd n) {s : ℝ} (hs : 0 ≤ s) {t : ℝ}
    (ht : t < 1) : taylorT g n s t ≤ phiS s t := by
  rcases le_total g t with h | h
  · exact phiS_ge_taylor_right hg n hs h ht
  · have h' := remT_sign_left hg n s hs t h
    have e : (-1 : ℝ) ^ (n + 1) = 1 := by
      obtain ⟨k, rfl⟩ := hn
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
      norm_num
    rw [e, one_mul] at h'
    unfold remT at h'
    linarith

/-! ### Unit test: the order-3 minorant at `g = 0`, `s = 1/2`, evaluated at `t = 1/4` -/

example : taylorT 0 3 (1 / 2) (1 / 4) ≤ phiS (1 / 2) (1 / 4) :=
  phiS_ge_taylor_odd (by norm_num) ⟨1, by norm_num⟩ (by norm_num) (by norm_num)

end RieszN7
