import RieszN7.Cap.StepP.Block
import Mathlib.Data.List.OfFn

/-!
# `RieszN7.Cap.StepP.Main` — the per-block Step P theorem in generator form

`blk_main`: a chain of sample points `a = t₀ < t₁ < … < t_n = b` with margins `m_i N ≤ Φ t_i` and the slack
conditions on every segment give `0 ≤ famV s V` on `[a, b]`.  The margins come from `node_margin` (the node's LDL
margin, `|P_k(a) − va_k| ≤ η_k`) and `sample_margin` (the LDL margin of the rounded integer combination
`Σ_j Ω_j G_j`, the rounding `|w_j/Λ̃_j − Ω_j/K| ≤ e_j` absorbed by Frobenius bounds `|G_j| ≤ FF_j N`); the `W` bound
from `w_bound` (Frobenius of `Σ_j Ω_j G_j`, same rounding).  `qf_lin_ofFn`/`qf_comb_ofFn` read the kernel-checked
integer combinations as sums over the 9 objects.  Private, AI-written (Phase 2, CAP fork, 2026-11-08), not reviewed.
-/

namespace RieszN7.CapLit.StepP

open Finset RieszN7.LDL

theorem cover_seg (t : ℕ → ℝ) : ∀ n, 0 < n → (∀ i < n, t i ≤ t (i + 1)) → ∀ s, t 0 ≤ s → s ≤ t n →
    ∃ i < n, t i ≤ s ∧ s ≤ t (i + 1)
  | 0, h, _, _, _, _ => absurd h (lt_irrefl 0)
  | n + 1, _, hm, s, h0, h1 => by
    by_cases hs : n ≠ 0 ∧ s ≤ t n
    · obtain ⟨i, hi, h⟩ := cover_seg t n (Nat.pos_of_ne_zero hs.1) (fun i hi => hm i (by omega)) s h0 hs.2
      exact ⟨i, by omega, h⟩
    · by_cases hn : n = 0
      · subst hn; exact ⟨0, by omega, h0, h1⟩
      · have : t n < s := by
          by_contra h; exact hs ⟨hn, not_lt.1 h⟩
        exact ⟨n, by omega, this.le, h1⟩

/-- **The per-block theorem** (a chain of segments). -/
theorem blk_main (a b sm : ℝ) (va vb : Fin 7 → ℝ) (Qa Qb : ℝ) (Q : Fin 7 → ℝ) (p : Fin 7 → Fin 6 → ℝ)
    (hab : a ≠ b) {δ τ N : ℝ} (F C ε : Fin 7 → ℝ) (n : ℕ) (hn : 0 < n) (t m : ℕ → ℝ)
    (ht0 : t 0 = a) (htn : t n = b) (hmono : ∀ i < n, t i < t (i + 1)) (hδ : ∀ i ≤ n, |t i - sm| ≤ δ)
    (hN : 0 ≤ N) (hτ : 0 ≤ τ) (hF0 : ∀ k, 0 ≤ F k) (hF : ∀ k, |Q k| ≤ F k * N) (hW : ∑ k, p k 2 * Q k ≤ τ * N)
    (hC : ∀ k, 3 * δ * |p k 3| + 6 * δ ^ 2 * |p k 4| + 10 * δ ^ 3 * |p k 5| ≤ C k)
    (hm : ∀ i ≤ n, m i * N ≤ Phi a b sm va vb Qa Qb Q p (t i))
    (hsl : ∀ i < n, 0 ≤ min (m i) (m (i + 1)) - (t (i + 1) - t i) ^ 2 / 4 * (τ + ∑ k, C k * F k)
      - ∑ k, ε k * F k)
    (s : ℝ) (hs : s ∈ Set.Icc a b) (V : Fin 7 → ℝ) (hV : ∀ k, |V k - pv (p k) sm s| ≤ ε k) :
    0 ≤ famV a b va vb Qa Qb Q s V := by
  obtain ⟨i, hi, h1, h2⟩ := cover_seg t n hn (fun i hi => (hmono i hi).le) s (ht0 ▸ hs.1) (htn ▸ hs.2)
  exact seg a b sm va vb Qa Qb Q p hab F C ε (hmono i hi) (hδ i hi.le) (hδ (i + 1) hi) hN hτ hF0 hF hW
    (hm i hi.le) (hm (i + 1) hi) hC (hsl i hi) s ⟨h1, h2⟩ V hV

/-- A margin of `G` is a margin of `G / L`. -/
theorem div_margin {c N G L : ℝ} (hL : 0 < L) (h : c * N ≤ G) : c / L * N ≤ G / L := by
  rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h hL.le

/-- A Frobenius bound of `G` is one of `G / L`. -/
theorem div_frob {FF N G L : ℝ} (hL : 0 < L) (h : |G| ≤ FF * N) : |G / L| ≤ FF / L * N := by
  rw [abs_div, abs_of_pos hL, div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h hL.le

/-- **Rounded combinations.** `|Σ_j c_j G_j − (Σ_j Ω_j G_j)/K| ≤ (Σ_j e_j FF_j) N`. -/
theorem lin_round {m : ℕ} (c Ω e FF G : Fin m → ℝ) {K N : ℝ} (hK : 0 < K)
    (he : ∀ j, |c j - Ω j / K| ≤ e j) (hG : ∀ j, |G j| ≤ FF j * N) :
    |∑ j, c j * G j - (∑ j, Ω j * G j) / K| ≤ (∑ j, e j * FF j) * N := by
  have e1 : ∑ j, c j * G j - (∑ j, Ω j * G j) / K = ∑ j, (c j - Ω j / K) * G j := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_assoc]
  exact mul_le_mul (he j) (hG j) (abs_nonneg _) ((abs_nonneg _).trans (he j))

/-- **Sample margin** from the LDL margin `c N ≤ Σ_j Ω_j G_j` of the rounded combination. -/
theorem sample_margin {m : ℕ} (w Lt Ω e FF G : Fin m → ℝ) {K N c : ℝ} (hK : 0 < K)
    (he : ∀ j, |w j / Lt j - Ω j / K| ≤ e j) (hG : ∀ j, |G j| ≤ FF j * N) (hL : c * N ≤ ∑ j, Ω j * G j) :
    (c / K - ∑ j, e j * FF j) * N ≤ ∑ j, w j / Lt j * G j := by
  have h := (abs_le.1 (lin_round (fun j => w j / Lt j) Ω e FF G hK he hG)).1
  have h2 : c / K * N ≤ (∑ j, Ω j * G j) / K := div_margin hK hL
  have e : (c / K - ∑ j, e j * FF j) * N = c / K * N - (∑ j, e j * FF j) * N := by ring
  linarith

/-- **The `W` bound** from a Frobenius bound `|Σ_j Ω_j G_j| ≤ FW N` of the rounded combination. -/
theorem w_bound {m : ℕ} (c Ω e FF G : Fin m → ℝ) {K N FW : ℝ} (hK : 0 < K)
    (he : ∀ j, |c j - Ω j / K| ≤ e j) (hG : ∀ j, |G j| ≤ FF j * N) (hW : |∑ j, Ω j * G j| ≤ FW * N) :
    ∑ j, c j * G j ≤ (FW / K + ∑ j, e j * FF j) * N := by
  have h := (abs_le.1 (lin_round c Ω e FF G hK he hG)).2
  have h2 : (∑ j, Ω j * G j) / K ≤ FW / K * N := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right ((le_abs_self _).trans hW) hK.le
  have e : (FW / K + ∑ j, e j * FF j) * N = FW / K * N + (∑ j, e j * FF j) * N := by ring
  linarith

/-- **The `W` bound** from an LDL margin `c N ≤ T N − Σ_j Ω_j G_j` (`0 ≤ c`). -/
theorem w_bound_ldl {m : ℕ} (cw Ω e FF G : Fin m → ℝ) {K N T c : ℝ} (hK : 0 < K) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (he : ∀ j, |cw j - Ω j / K| ≤ e j) (hG : ∀ j, |G j| ≤ FF j * N)
    (hL : c * N ≤ T * N - ∑ j, Ω j * G j) :
    ∑ j, cw j * G j ≤ (T / K + ∑ j, e j * FF j) * N := by
  have h := (abs_le.1 (lin_round cw Ω e FF G hK he hG)).2
  have h1 : ∑ j, Ω j * G j ≤ T * N := by nlinarith [mul_nonneg hc hN]
  have h2 : (∑ j, Ω j * G j) / K ≤ T / K * N := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1 hK.le
  have e : (T / K + ∑ j, e j * FF j) * N = T / K * N + (∑ j, e j * FF j) * N := by ring
  linarith

/-- An integer combination over `Fin m`, read through `qf`. -/
theorem qf_lin_ofFn {m : ℕ} (n : ℕ) (cs : List ℤ) (Ω : Fin m → ℤ) (B : Fin m → List (List ℤ)) (x : ℕ → ℝ) :
    qf n (lin cs (List.ofFn fun j => (Ω j, B j))) x = ∑ j, (Ω j : ℝ) * qf n (scl cs (B j)) x := by
  rw [qf_lin, List.map_ofFn, List.sum_ofFn]; rfl

theorem qf_comb_ofFn {m : ℕ} (n : ℕ) (cs : List ℤ) (Ω : Fin m → ℤ) (B : Fin m → List (List ℤ)) (c : ℤ)
    (x : ℕ → ℝ) :
    qf n (comb cs (List.ofFn fun j => (Ω j, B j)) c n) x
      = (c : ℝ) * nrm n x + ∑ j, (Ω j : ℝ) * qf n (scl cs (B j)) x := by
  rw [qf_comb, List.map_ofFn, List.sum_ofFn]; rfl

/-- `Φ t` as the weighted sum over the 9 objects (for `sample_margin`). -/
theorem Phi_eq_sum9 (a b sm : ℝ) (va vb : Fin 7 → ℝ) (p : Fin 7 → Fin 6 → ℝ) (G Lt : Fin 9 → ℝ) (t : ℝ) :
    Phi a b sm va vb (G 0 / Lt 0) (G 1 / Lt 1) (fun k => G k.succ.succ / Lt k.succ.succ) p t
      = ∑ j, wt (lam a b t) (fun k => pv (p k) sm t) va vb j / Lt j * G j := by
  rw [sum9_famV]; rfl

/-- The `W` coefficients over the 9 objects: `0, 0, p_{k,2}/Λ̃_{k+2}`. -/
noncomputable def cW (p : Fin 7 → Fin 6 → ℝ) (Lt : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![0, 0, p 0 2 / Lt 2, p 1 2 / Lt 3, p 2 2 / Lt 4, p 3 2 / Lt 5, p 4 2 / Lt 6, p 5 2 / Lt 7, p 6 2 / Lt 8]

theorem W_eq (p : Fin 7 → Fin 6 → ℝ) (G Lt : Fin 9 → ℝ) :
    ∑ k, p k 2 * (G k.succ.succ / Lt k.succ.succ) = ∑ j, cW p Lt j * G j := by
  conv_rhs => rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hk : ∀ k : Fin 7, cW p Lt k.succ.succ = p k 2 / Lt k.succ.succ := by
    intro k; fin_cases k <;> rfl
  have h0 : cW p Lt 0 = 0 := rfl
  have h1 : cW p Lt (Fin.succ 0) = 0 := rfl
  rw [h0, h1]
  simp only [hk, zero_mul, zero_add]
  exact Finset.sum_congr rfl fun k _ => by ring

end RieszN7.CapLit.StepP
