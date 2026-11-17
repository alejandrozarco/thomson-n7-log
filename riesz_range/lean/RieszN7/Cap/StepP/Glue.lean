import RieszN7.Cap.StepP.Main

/-!
# `RieszN7.Cap.StepP.Glue` — Step P statements in the bridge's form (light)

`qfn_lit`: the per-block Step P statement `0 ≤ Σ_j c_j qf r (mat_j) y` is the nonnegativity of the quadratic form of
`R_{ii'} = Σ_j c_j ent_j(i, i')` (the bridge's `QFnonneg`, unfolded); `psd_lit`: with the literals symmetric
(`symOK`), the matrix of `R` on `Fin r` is `PosSemidef` (kernel blocks).  Private, AI-written (Phase 2, CAP fork,
2026-11-08), not reviewed.
-/

namespace RieszN7.CapLit.StepP

open Finset

theorem qfn_lit (n : ℕ) (c : Fin 9 → ℝ) (B : Fin 9 → LB) (h : ∀ y, 0 ≤ ∑ j, c j * qf n (B j).mat y)
    (y : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range n, ∑ i' ∈ range n, y i * (∑ j, c j * ((B j).ent i i' : ℝ)) * y i' := by
  rw [qf_sum9]; exact h y

theorem psd_lit (r : ℕ) (c : Fin 9 → ℝ) (B : Fin 9 → LB) (hsym : ∀ j, symOK (B j) = true)
    (hr : ∀ j, (B j).r = r) (h : ∀ y, 0 ≤ ∑ j, c j * qf r (B j).mat y) :
    (Matrix.of fun i i' : Fin r => ∑ j, c j * ((B j).ent i i' : ℝ)).PosSemidef := by
  refine psd_of_qf r (fun i i' => ∑ j, c j * ((B j).ent i i' : ℝ)) ?_ (qfn_lit r c B h)
  intro i hi i' hi'
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ent_symm (B j) (hsym j) (by rw [hr]; exact hi) (by rw [hr]; exact hi')]

/-- Rescaling the coefficients: `Σ_j w_j / D_j · q_j = Σ_j w_j / Lt_j · q_j` when `D = Lt`. -/
theorem coef_eq (w D Lt : Fin 9 → ℝ) (q : Fin 9 → ℝ) (h : ∀ j, D j = Lt j) :
    ∑ j, w j / D j * q j = ∑ j, w j / Lt j * q j :=
  Finset.sum_congr rfl fun j _ => by rw [h j]

/-- From the Step P statement (scalings `Lt`, block literals `B'`) to the bridge's (scalings `D`, literals `B`). -/
theorem conv9 (n : ℕ) (w D Lt : Fin 9 → ℝ) (B B' : Fin 9 → LB) (hD : ∀ j, D j = Lt j) (hB : ∀ j, B j = B' j)
    (h : ∀ y, 0 ≤ ∑ j, w j / Lt j * qf n (B' j).mat y) (y : ℕ → ℝ) :
    0 ≤ ∑ j, w j / D j * qf n (B j).mat y := by
  simp only [hD, hB]; exact h y

end RieszN7.CapLit.StepP
