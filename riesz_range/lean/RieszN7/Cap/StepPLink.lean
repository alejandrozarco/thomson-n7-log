import RieszN7.Cap.ERow
import RieszN7.Cap.LitLink
import RieszN7.Cap.StepP.Glue

/-!
# `RieszN7.Cap.StepPLink` — node pins as rationals (enzo glue for Step P)

The Step P modules use rational node pins `va, vb`; `capSharp_piece` needs the e-row components (`β₀ = H_B(0)`,
`α₀ = H_A(−1)`, `a₀ = (H_C(c₁) + H_C(c₂))/2`) of `va, vb` to be the node objects' actual pins.  `pinChkQ` is the
rational version of `pinChk` (one `ℤ[√5]` `decide` per node).  Private, AI-written (Phase 2, CAP fork, 2026-11-08),
not reviewed.
-/

open Real

namespace ThomsonN7.Cert.CapR
open ThomsonN7 ThomsonN7.Base ThomsonGen RieszN7.Qs5

/-- Rational pins `nA/dA`, `nB/dB`, `nC/dC` of an object. -/
def pinChkQ (c : TCertR) (nA : ℤ) (dA : ℕ) (nB : ℤ) (dB : ℕ) (nC : ℤ) (dC : ℕ) : Bool :=
  let C1 := at5 ptC1 c.HC
  let C2 := at5 ptC2 c.HC
  decide (0 < dA) && decide (0 < dB) && decide (0 < dC) &&
    decide ((at5 ptA c.HA).1 * dA = nA * c.Lam) && decide ((at5 ptA c.HA).2 = 0) &&
    decide ((at5 ptB c.HB).1 * dB = nB * c.Lam) && decide ((at5 ptB c.HB).2 = 0) &&
    decide ((C1.1 + C2.1) * dC = 2 * nC * c.Lam * 4 ^ c.HC.length) && decide (C1.2 + C2.2 = 0)

theorem pinQ_of_chk (c : TCertR) (nA : ℤ) (dA : ℕ) (nB : ℤ) (dB : ℕ) (nC : ℤ) (dC : ℕ) (hL : 0 < c.Lam)
    (h : pinChkQ c nA dA nB dB nC dC = true) :
    c.hdr.HAf (-1) = (nA : ℝ) / dA ∧ c.hdr.HBf 0 = (nB : ℝ) / dB ∧
      (c.hdr.HCf c1 + c.hdr.HCf c2) / 2 = (nC : ℝ) / dC := by
  simp only [pinChkQ, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdA, hdB⟩, hdC⟩, hA1⟩, hA2⟩, hB1⟩, hB2⟩, hC1⟩, hC2⟩ := h
  have hL' : (c.Lam : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hdA' : (dA : ℝ) ≠ 0 := by exact_mod_cast hdA.ne'
  have hdB' : (dB : ℝ) ≠ 0 := by exact_mod_cast hdB.ne'
  have hdC' : (dC : ℝ) ≠ 0 := by exact_mod_cast hdC.ne'
  have h4 : (4 : ℝ) ^ c.HC.length ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have r1 : (((at5 ptA c.HA).1 * dA : ℤ) : ℝ) = ((nA * c.Lam : ℤ) : ℝ) := by exact_mod_cast hA1
    have r2 : (((at5 ptA c.HA).2 : ℤ) : ℝ) = 0 := by exact_mod_cast hA2
    push_cast at r1 r2
    rw [evalA, div_eq_div_iff hL' hdA']; simp only [ev5]; rw [r2]; linear_combination r1
  · have r1 : (((at5 ptB c.HB).1 * dB : ℤ) : ℝ) = ((nB * c.Lam : ℤ) : ℝ) := by exact_mod_cast hB1
    have r2 : (((at5 ptB c.HB).2 : ℤ) : ℝ) = 0 := by exact_mod_cast hB2
    push_cast at r1 r2
    rw [evalB, div_eq_div_iff hL' hdB']; simp only [ev5]; rw [r2]; linear_combination r1
  · rw [evalC1, evalC2, ← add_div]
    have r1 : ((((at5 ptC1 c.HC).1 + (at5 ptC2 c.HC).1) * dC : ℤ) : ℝ)
        = ((2 * nC * c.Lam * 4 ^ c.HC.length : ℤ) : ℝ) := by exact_mod_cast hC1
    have r2 : (((at5 ptC1 c.HC).2 + (at5 ptC2 c.HC).2 : ℤ) : ℝ) = 0 := by exact_mod_cast hC2
    push_cast at r1 r2
    have hs : (ev5 (at5 ptC1 c.HC) + ev5 (at5 ptC2 c.HC)) * dC = 2 * nC * c.Lam * 4 ^ c.HC.length := by
      simp only [ev5]
      linear_combination r1 + Real.sqrt 5 * dC * r2
    rw [div_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero h4 hL') two_ne_zero) hdC']
    linear_combination hs

end ThomsonN7.Cert.CapR
