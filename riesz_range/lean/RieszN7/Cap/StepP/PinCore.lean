import RieszN7.Cap.StepP.Core
import RieszN7.Cap.Pins.Defs

/-!
# Step P: the true pins against the quintic models (generic part)

The capM pin interface (`RieszN7.Cap.Pins.P<a>_<b>.pins_abs`) bounds `|K·v_k(s) − Pm_k(s)| ≤ Pw_k(s)` with integer
polynomials `Pm_k`, `Pw_k` in `s` and `K = 40 ρd D`.  Step P uses the quintic models `pv (p k) sm s` centred at `s_m`.
Per piece and pin (`StepP.<Piece>.PinLink`): `Pm_k(s) = K (pv (p k) sm s + r_k(s − s_m))` exactly (`ring`), with the
remainder `r_k` (the Taylor terms of degree ≥ 6 and the rounding of `p` to the 2^-90 grid) bounded by
`hor (|r_k|) δ`, and `Pw_k(s) ≤ Pw_k^{abs}(b)` for `0 ≤ s ≤ b`; then `|v_k(s) − pv (p k) sm s| ≤ ε_k`
(`pin_link_of`).  Private, AI-written (Phase 2, CAP fork, 2026-11-08), not reviewed.
-/

open LogLean.Minor

namespace RieszN7.CapLit.StepP

/-- Horner evaluation of a real coefficient list (low degree first). -/
noncomputable def hor : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: L, u => c + u * hor L u

theorem hor_abs_le : ∀ (L : List ℝ) {u δ : ℝ}, |u| ≤ δ → |hor L u| ≤ hor (L.map fun c => |c|) δ
  | [], _, _, _ => by simp [hor]
  | c :: L, u, δ, hu => by
      have ih := hor_abs_le L hu
      have hn : 0 ≤ hor (L.map fun c => |c|) δ := le_trans (abs_nonneg _) ih
      simp only [List.map_cons, hor]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := mul_le_mul hu ih (abs_nonneg _) (le_trans (abs_nonneg _) hu)
      linarith

theorem peval_abs_bound : ∀ (L : List ℤ) {s R : ℝ}, 0 ≤ s → s ≤ R →
    |peval L s| ≤ peval (L.map fun c => |c|) R
  | [], _, _, _, _ => by simp [peval]
  | c :: L, s, R, h0, h1 => by
      have ih := peval_abs_bound L h0 h1
      have hn : 0 ≤ peval (L.map fun c => |c|) R := le_trans (abs_nonneg _) ih
      simp only [List.map_cons, peval]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg h0]
      have := mul_le_mul h1 ih (abs_nonneg _) (le_trans h0 h1)
      push_cast
      linarith

/-- One pin: from the capM bound `|K v − P| ≤ W`, `W ≤ A`, the exact split `P = K (q + r)` and `|r| ≤ ρ`. -/
theorem pin_link_of {K v P W A q r ρ ε : ℝ} (hK : 0 < K) (hp : |K * v - P| ≤ W) (hW : W ≤ A)
    (hid : P = K * (q + r)) (hr : |r| ≤ ρ) (hε : A / K + ρ ≤ ε) : |v - q| ≤ ε := by
  have e : v - q = (K * v - P) / K + r := by rw [hid]; field_simp; ring
  rw [e]
  have h1 : |(K * v - P) / K| ≤ A / K := by
    rw [abs_div, abs_of_pos hK]
    exact div_le_div_of_nonneg_right (hp.trans hW) hK.le
  calc |(K * v - P) / K + r| ≤ |(K * v - P) / K| + |r| := abs_add_le _ _
    _ ≤ A / K + ρ := add_le_add h1 hr
    _ ≤ ε := hε

end RieszN7.CapLit.StepP
