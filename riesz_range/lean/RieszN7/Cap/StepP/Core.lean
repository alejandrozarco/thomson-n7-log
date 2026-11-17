import RieszN7.Cap.Lit.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# `RieszN7.Cap.StepP.Core` — the scalar Step P argument (one block, one vector, a piece `[a, b]` of `s`)

For a cap piece `[a, b]` the reduced family form of a block at a fixed vector is
`famV s v = (1 − λ) Q_a + λ Q_b + Σ_k (v_k − (1 − λ) va_k − λ vb_k) Q_k`, `λ = (s − a)/(b − a)`, with the node forms
`Q_a, Q_b`, the direction forms `Q_k` (`k < 7`), node pins `va, vb` and target pins `v` (`= V s`, the true pin
functions).  Replacing `v` by quintic models `P_k(s) = Σ_{i<6} p_{k,i} (s − s_m)^i` gives `Φ s`, which is affine in `s`
plus `Σ_k P_k(s) Q_k`; on a sub-interval `[t₀, t₂]` (chord identity, divided difference of a quintic)
`Φ s = θ₀ Φ t₀ + θ₂ Φ t₂ − (s − t₀)(t₂ − s) Σ_k (p_{k,2} + c_k) Q_k`, `|c_k| ≤ C_k = 3δ|p_{k,3}| + 6δ²|p_{k,4}| + 10δ³|p_{k,5}|`.
With `Σ_k p_{k,2} Q_k ≤ τ N` (Frobenius or LDL), `|Q_k| ≤ F_k N` (Frobenius) and sample margins `m_i N ≤ Φ t_i`
(LDL), `Φ s ≥ (min(m₀, m₂) − (t₂ − t₀)²/4 (τ + Σ C_k F_k)) N`, and `famV s (V s) ≥ Φ s − Σ_k ε_k F_k N` when
`|V_k s − P_k s| ≤ ε_k`.  Plain real algebra; no kernel evaluation.  Private, AI-written (Phase 2, CAP fork,
2026-11-08), not reviewed.
-/

namespace RieszN7.CapLit.StepP

open Finset

/-- The quintic model `Σ_{i<6} p_i (t − s_m)^i`. -/
noncomputable def pv (p : Fin 6 → ℝ) (sm t : ℝ) : ℝ :=
  p 0 + p 1 * (t - sm) + p 2 * (t - sm) ^ 2 + p 3 * (t - sm) ^ 3 + p 4 * (t - sm) ^ 4 + p 5 * (t - sm) ^ 5

/-- Complete homogeneous polynomials of degree 1, 2, 3 in three variables. -/
noncomputable def h1 (x y z : ℝ) : ℝ := x + y + z
noncomputable def h2 (x y z : ℝ) : ℝ := x * x + y * y + z * z + x * y + x * z + y * z
noncomputable def h3 (x y z : ℝ) : ℝ :=
  x * x * x + y * y * y + z * z * z + x * x * y + x * x * z + y * y * x + y * y * z + z * z * x + z * z * y + x * y * z

/-- The second divided difference `P[t₀, s, t₂]` of the quintic model (`u = t − s_m`). -/
noncomputable def dd (p : Fin 6 → ℝ) (x y z : ℝ) : ℝ := p 2 + p 3 * h1 x y z + p 4 * h2 x y z + p 5 * h3 x y z

/-- **Chord residual of a quintic.** -/
theorem pv_chord (p : Fin 6 → ℝ) (sm t0 s t2 : ℝ) (h : t0 ≠ t2) :
    pv p sm s = (t2 - s) / (t2 - t0) * pv p sm t0 + (s - t0) / (t2 - t0) * pv p sm t2
      - (s - t0) * (t2 - s) * dd p (t0 - sm) (s - sm) (t2 - sm) := by
  have hd : t2 - t0 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  field_simp
  simp only [pv, dd, h1, h2, h3]
  ring

theorem abs_mul_le_sq {x y δ : ℝ} (hx : |x| ≤ δ) (hy : |y| ≤ δ) : |x * y| ≤ δ ^ 2 := by
  rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_mul3_le {x y z δ : ℝ} (hx : |x| ≤ δ) (hy : |y| ≤ δ) (hz : |z| ≤ δ) : |x * y * z| ≤ δ ^ 3 := by
  rw [abs_mul, pow_succ]
  exact mul_le_mul (abs_mul_le_sq hx hy) hz (abs_nonneg _) (sq_nonneg _)

theorem dd_sub_le (p : Fin 6 → ℝ) {x y z δ : ℝ} (hx : |x| ≤ δ) (hy : |y| ≤ δ) (hz : |z| ≤ δ) :
    |dd p x y z - p 2| ≤ 3 * δ * |p 3| + 6 * δ ^ 2 * |p 4| + 10 * δ ^ 3 * |p 5| := by
  have e1 : |h1 x y z| ≤ 3 * δ := by
    unfold h1
    obtain ⟨a1, a2⟩ := abs_le.1 hx; obtain ⟨b1, b2⟩ := abs_le.1 hy; obtain ⟨c1, c2⟩ := abs_le.1 hz
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |h2 x y z| ≤ 6 * δ ^ 2 := by
    unfold h2
    obtain ⟨a1, a2⟩ := abs_le.1 (abs_mul_le_sq hx hx); obtain ⟨b1, b2⟩ := abs_le.1 (abs_mul_le_sq hy hy)
    obtain ⟨c1, c2⟩ := abs_le.1 (abs_mul_le_sq hz hz); obtain ⟨d1, d2⟩ := abs_le.1 (abs_mul_le_sq hx hy)
    obtain ⟨e1, e2⟩ := abs_le.1 (abs_mul_le_sq hx hz); obtain ⟨f1, f2⟩ := abs_le.1 (abs_mul_le_sq hy hz)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have e3 : |h3 x y z| ≤ 10 * δ ^ 3 := by
    unfold h3
    obtain ⟨a1, a2⟩ := abs_le.1 (abs_mul3_le hx hx hx); obtain ⟨b1, b2⟩ := abs_le.1 (abs_mul3_le hy hy hy)
    obtain ⟨c1, c2⟩ := abs_le.1 (abs_mul3_le hz hz hz); obtain ⟨d1, d2⟩ := abs_le.1 (abs_mul3_le hx hx hy)
    obtain ⟨e1, e2⟩ := abs_le.1 (abs_mul3_le hx hx hz); obtain ⟨f1, f2⟩ := abs_le.1 (abs_mul3_le hy hy hx)
    obtain ⟨g1, g2⟩ := abs_le.1 (abs_mul3_le hy hy hz); obtain ⟨k1, k2⟩ := abs_le.1 (abs_mul3_le hz hz hx)
    obtain ⟨l1, l2⟩ := abs_le.1 (abs_mul3_le hz hz hy); obtain ⟨m1, m2⟩ := abs_le.1 (abs_mul3_le hx hy hz)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have : dd p x y z - p 2 = p 3 * h1 x y z + p 4 * h2 x y z + p 5 * h3 x y z := by unfold dd; ring
  rw [this]
  calc |p 3 * h1 x y z + p 4 * h2 x y z + p 5 * h3 x y z|
      ≤ |p 3 * h1 x y z| + |p 4 * h2 x y z| + |p 5 * h3 x y z| := abs_add_three _ _ _
    _ ≤ |p 3| * (3 * δ) + |p 4| * (6 * δ ^ 2) + |p 5| * (10 * δ ^ 3) := by
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
    _ = _ := by ring

theorem C_nonneg (p : Fin 6 → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ 3 * δ * |p 3| + 6 * δ ^ 2 * |p 4| + 10 * δ ^ 3 * |p 5| := by
  have := abs_nonneg (p 3); have := abs_nonneg (p 4); have := abs_nonneg (p 5)
  positivity

/-- `−e F N ≤ c Q` from `|c| ≤ e`, `|Q| ≤ F N`. -/
theorem neg_le_mul {c e Q F N : ℝ} (hc : |c| ≤ e) (hQ : |Q| ≤ F * N) : -(e * F * N) ≤ c * Q := by
  have h1 : |c * Q| ≤ e * (F * N) := by
    rw [abs_mul]; exact mul_le_mul hc hQ (abs_nonneg _) ((abs_nonneg _).trans hc)
  have := (abs_le.1 h1).1
  linarith

/-! ### The family form along a piece -/

section Fam

variable (a b sm : ℝ) (va vb : Fin 7 → ℝ) (Qa Qb : ℝ) (Q : Fin 7 → ℝ)

/-- `λ(s) = (s − a)/(b − a)`. -/
noncomputable def lam (s : ℝ) : ℝ := (s - a) / (b - a)

/-- The family form at `s` with pins `v`. -/
noncomputable def famV (s : ℝ) (v : Fin 7 → ℝ) : ℝ :=
  (1 - lam a b s) * Qa + lam a b s * Qb + ∑ k, (v k - (1 - lam a b s) * va k - lam a b s * vb k) * Q k

/-- The model family form at `s`. -/
noncomputable def Phi (p : Fin 7 → Fin 6 → ℝ) (s : ℝ) : ℝ := famV a b va vb Qa Qb Q s fun k => pv (p k) sm s

/-- **Chord identity for the model family.** -/
theorem Phi_chord (p : Fin 7 → Fin 6 → ℝ) (hab : a ≠ b) (t0 s t2 : ℝ) (h : t0 ≠ t2) :
    Phi a b sm va vb Qa Qb Q p s = (t2 - s) / (t2 - t0) * Phi a b sm va vb Qa Qb Q p t0
      + (s - t0) / (t2 - t0) * Phi a b sm va vb Qa Qb Q p t2
      - (s - t0) * (t2 - s) * ∑ k, dd (p k) (t0 - sm) (s - sm) (t2 - sm) * Q k := by
  have hd : t2 - t0 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  simp only [Phi, famV]
  have hk : ∀ k, (pv (p k) sm s - (1 - lam a b s) * va k - lam a b s * vb k) * Q k
      = (t2 - s) / (t2 - t0) * ((pv (p k) sm t0 - (1 - lam a b t0) * va k - lam a b t0 * vb k) * Q k)
        + (s - t0) / (t2 - t0) * ((pv (p k) sm t2 - (1 - lam a b t2) * va k - lam a b t2 * vb k) * Q k)
        - (s - t0) * (t2 - s) * (dd (p k) (t0 - sm) (s - sm) (t2 - sm) * Q k) := by
    intro k
    rw [pv_chord (p k) sm t0 s t2 h]
    simp only [lam]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [lam]
  field_simp
  ring

/-- **The interval lemma.** On `[t₀, t₂] ⊆ [s_m − δ, s_m + δ]`: sample margins at the ends, `Σ p_{k,2} Q_k ≤ τ N`,
`|Q_k| ≤ F_k N` and the slack condition give `m N ≤ Φ s`. -/
theorem Phi_interval (p : Fin 7 → Fin 6 → ℝ) (hab : a ≠ b) {t0 t2 δ τ N m m0 m2 : ℝ} (F C : Fin 7 → ℝ)
    (ht : t0 < t2) (h0 : |t0 - sm| ≤ δ) (h2 : |t2 - sm| ≤ δ) (hN : 0 ≤ N) (hτ : 0 ≤ τ)
    (hF0 : ∀ k, 0 ≤ F k) (hF : ∀ k, |Q k| ≤ F k * N) (hW : ∑ k, p k 2 * Q k ≤ τ * N)
    (hm0 : m0 * N ≤ Phi a b sm va vb Qa Qb Q p t0) (hm2 : m2 * N ≤ Phi a b sm va vb Qa Qb Q p t2)
    (hC : ∀ k, 3 * δ * |p k 3| + 6 * δ ^ 2 * |p k 4| + 10 * δ ^ 3 * |p k 5| ≤ C k)
    (hsl : m ≤ min m0 m2 - (t2 - t0) ^ 2 / 4 * (τ + ∑ k, C k * F k))
    (s : ℝ) (hs : s ∈ Set.Icc t0 t2) :
    m * N ≤ Phi a b sm va vb Qa Qb Q p s := by
  obtain ⟨hs0, hs2⟩ := hs
  have hδs : |s - sm| ≤ δ := by
    rw [abs_le] at h0 h2 ⊢; exact ⟨by linarith, by linarith⟩
  rw [Phi_chord a b sm va vb Qa Qb Q p hab t0 s t2 ht.ne]
  set X := ∑ k, dd (p k) (t0 - sm) (s - sm) (t2 - sm) * Q k
  have hX : X ≤ (τ + ∑ k, C k * F k) * N := by
    have e : X = ∑ k, p k 2 * Q k + ∑ k, (dd (p k) (t0 - sm) (s - sm) (t2 - sm) - p k 2) * Q k := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, (dd (p k) (t0 - sm) (s - sm) (t2 - sm) - p k 2) * Q k ≤ ∑ k, C k * F k * N := by
      refine Finset.sum_le_sum fun k _ => ?_
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      have hCk : |dd (p k) (t0 - sm) (s - sm) (t2 - sm) - p k 2| ≤ C k :=
        le_trans (dd_sub_le (p k) h0 hδs h2) (hC k)
      rw [mul_assoc]
      exact mul_le_mul hCk (hF k) (abs_nonneg _) ((abs_nonneg _).trans hCk)
    rw [e, add_mul, Finset.sum_mul]
    linarith
  have hCF : 0 ≤ τ + ∑ k, C k * F k :=
    add_nonneg hτ (Finset.sum_nonneg fun k _ => mul_nonneg (le_trans (C_nonneg (p k) ((abs_nonneg _).trans h0)) (hC k))
      (hF0 k))
  set K := τ + ∑ k, C k * F k
  have hd : (0 : ℝ) < t2 - t0 := by linarith
  have hc0 : 0 ≤ (t2 - s) / (t2 - t0) := div_nonneg (by linarith) hd.le
  have hc2 : 0 ≤ (s - t0) / (t2 - t0) := div_nonneg (by linarith) hd.le
  have hsum : (t2 - s) / (t2 - t0) + (s - t0) / (t2 - t0) = 1 := by field_simp; ring
  have hA : min m0 m2 * N ≤ (t2 - s) / (t2 - t0) * Phi a b sm va vb Qa Qb Q p t0
      + (s - t0) / (t2 - t0) * Phi a b sm va vb Qa Qb Q p t2 := by
    calc min m0 m2 * N = (t2 - s) / (t2 - t0) * (min m0 m2 * N) + (s - t0) / (t2 - t0) * (min m0 m2 * N) := by
          rw [← add_mul, hsum, one_mul]
      _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (min_le_left _ _) hN).trans hm0) hc0)
          (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (min_le_right _ _) hN).trans hm2) hc2)
  have he0 : 0 ≤ (s - t0) * (t2 - s) := mul_nonneg (by linarith) (by linarith)
  have he : (s - t0) * (t2 - s) ≤ (t2 - t0) ^ 2 / 4 := by nlinarith [sq_nonneg (t2 + t0 - 2 * s)]
  have hB : (s - t0) * (t2 - s) * X ≤ (t2 - t0) ^ 2 / 4 * (K * N) :=
    (mul_le_mul_of_nonneg_left hX he0).trans (mul_le_mul_of_nonneg_right he (mul_nonneg hCF hN))
  have hC : m * N ≤ (min m0 m2 - (t2 - t0) ^ 2 / 4 * K) * N := mul_le_mul_of_nonneg_right hsl hN
  have e3 : (min m0 m2 - (t2 - t0) ^ 2 / 4 * K) * N = min m0 m2 * N - (t2 - t0) ^ 2 / 4 * (K * N) := by ring
  linarith

/-- **True pins.** `famV s v ≥ Φ s − Σ_k ε_k F_k N` when `|v_k − P_k(s)| ≤ ε_k` and `|Q_k| ≤ F_k N`. -/
theorem famV_ge (p : Fin 7 → Fin 6 → ℝ) (s : ℝ) (v ε F : Fin 7 → ℝ) {N : ℝ}
    (hv : ∀ k, |v k - pv (p k) sm s| ≤ ε k) (hF : ∀ k, |Q k| ≤ F k * N) :
    Phi a b sm va vb Qa Qb Q p s - (∑ k, ε k * F k) * N ≤ famV a b va vb Qa Qb Q s v := by
  have e : famV a b va vb Qa Qb Q s v - Phi a b sm va vb Qa Qb Q p s = ∑ k, (v k - pv (p k) sm s) * Q k := by
    simp only [Phi, famV]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h : -(∑ k, ε k * F k * N) ≤ ∑ k, (v k - pv (p k) sm s) * Q k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact neg_le_mul (hv k) (hF k)
  rw [Finset.sum_mul]
  linarith

/-- **Node sample at `a`:** `Φ a = Q_a + Σ_k (P_k(a) − va_k) Q_k`. -/
theorem Phi_a (p : Fin 7 → Fin 6 → ℝ) {N μ : ℝ} (η F : Fin 7 → ℝ)
    (hQa : μ * N ≤ Qa) (hη : ∀ k, |pv (p k) sm a - va k| ≤ η k) (hF : ∀ k, |Q k| ≤ F k * N) :
    (μ - ∑ k, η k * F k) * N ≤ Phi a b sm va vb Qa Qb Q p a := by
  have hl : lam a b a = 0 := by simp [lam]
  have e : Phi a b sm va vb Qa Qb Q p a = Qa + ∑ k, (pv (p k) sm a - va k) * Q k := by
    simp only [Phi, famV, hl]; congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have h : -(∑ k, η k * F k * N) ≤ ∑ k, (pv (p k) sm a - va k) * Q k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact neg_le_mul (hη k) (hF k)
  rw [e, sub_mul, Finset.sum_mul]
  linarith

/-- **Node sample at `b`.** -/
theorem Phi_b (p : Fin 7 → Fin 6 → ℝ) (hab : a ≠ b) {N μ : ℝ} (η F : Fin 7 → ℝ)
    (hQb : μ * N ≤ Qb) (hη : ∀ k, |pv (p k) sm b - vb k| ≤ η k) (hF : ∀ k, |Q k| ≤ F k * N) :
    (μ - ∑ k, η k * F k) * N ≤ Phi a b sm va vb Qa Qb Q p b := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hl : lam a b b = 1 := by simp [lam, div_self hba]
  have e : Phi a b sm va vb Qa Qb Q p b = Qb + ∑ k, (pv (p k) sm b - vb k) * Q k := by
    simp only [Phi, famV, hl]; congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  have h : -(∑ k, η k * F k * N) ≤ ∑ k, (pv (p k) sm b - vb k) * Q k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    exact neg_le_mul (hη k) (hF k)
  rw [e, sub_mul, Finset.sum_mul]
  linarith

end Fam

end RieszN7.CapLit.StepP
