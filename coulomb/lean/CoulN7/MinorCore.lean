import LogLean.MinorCore

/-!
# Polynomial minorants of the Coulomb kernel `(√(2 - 2t))⁻¹`

For `t < 1` and a rational polynomial `G = Gn/Gd` (integer list `Gn`, `Gd > 0`):
  `Gd² - (2 - 2t)·Gn(t)² ≥ 0  ⇒  Gn(t)/Gd ≤ (√(2 - 2t))⁻¹`   (`le_phi_of_gap`).
Nonnegativity of the gap polynomial `gapPoly Gn Gd` on `[lo/D, hi/D)` is checked by a chain of Möbius
(Bernstein) pieces `[A/D, B/D)`, each with all coefficients `≥ 0` (`LogLean.Minor.mob_sound`,
`nnChainOK`). Every check is a `Bool` closed by `decide +kernel`.

Coercivity uses the same test for `G = H + k/m` (`shiftN`, `shiftD`): `H + k/m ≤ φ₁` gives `φ₁ - H ≥ k/m`.

The polynomial calculus (`peval`, `padd`, `pmul`, `homog`, `mob_sound`) is that of `LogLean.MinorCore`
(log formalisation; its §1–2 port upstream `CutOneD` / `Asm_Coerce` §A). Nothing here is copied from upstream.
-/

namespace CoulN7.Minor

open LogLean.Minor

/-- `Gd² - (2 - 2t)·Gn²` as an integer polynomial. -/
def gapPoly (Gn : List ℤ) (Gd : ℕ) : List ℤ :=
  padd [(Gd : ℤ) * Gd] (pneg (pmul [2, -2] (pmul Gn Gn)))

theorem peval_gapPoly (Gn : List ℤ) (Gd : ℕ) (t : ℝ) :
    peval (gapPoly Gn Gd) t = (Gd : ℝ) ^ 2 - (2 - 2 * t) * peval Gn t ^ 2 := by
  unfold gapPoly
  simp only [peval_padd, peval_pneg, peval_pmul, peval]
  push_cast
  ring

/-- **The kernel test.** `Gd² - (2-2t)·Gn(t)² ≥ 0` and `t < 1` give `Gn(t)/Gd ≤ (√(2-2t))⁻¹`. -/
theorem le_phi_of_gap (Gn : List ℤ) (Gd : ℕ) (hGd : 0 < Gd) {t : ℝ} (ht : t < 1)
    (h : 0 ≤ peval (gapPoly Gn Gd) t) : peval Gn t / Gd ≤ (√(2 - 2 * t))⁻¹ := by
  rw [peval_gapPoly] at h
  have hu : (0 : ℝ) < 2 - 2 * t := by linarith
  have hd : (0 : ℝ) < Gd := by exact_mod_cast hGd
  set g := peval Gn t / Gd with hg
  have hgsq : g ^ 2 ≤ 1 / (2 - 2 * t) := by
    rw [hg, div_pow, div_le_div_iff₀ (by positivity) hu]
    nlinarith
  rcases le_or_gt g 0 with hneg | hpos
  · exact hneg.trans (inv_nonneg.2 (Real.sqrt_nonneg _))
  · rw [← Real.sqrt_inv, ← one_div]
    calc g = √(g ^ 2) := (Real.sqrt_sq hpos.le).symm
      _ ≤ √(1 / (2 - 2 * t)) := Real.sqrt_le_sqrt hgsq

/-- Chain of Möbius pieces `[A/D, B/D)` covering `[l/D, r/D)`, all coefficients `≥ 0`. -/
def nnChainOK (q : List ℤ) (D : ℕ) : List (ℤ × ℤ) → ℤ → ℤ → Bool
  | [], l, r => decide (r ≤ l)
  | (A, B) :: ps, l, r =>
    (homog [A, B] [(D:ℤ), (D:ℤ)] q (q.length - 1)).all (fun c => decide (0 ≤ c)) &&
      decide (A ≤ l) && nnChainOK q D ps B r

theorem nnChain_sound (q : List ℤ) (D : ℕ) (hD : 0 < D) (ps : List (ℤ × ℤ)) :
    ∀ l r : ℤ, nnChainOK q D ps l r = true →
      ∀ t : ℝ, (l:ℝ) ≤ D * t → (D:ℝ) * t < r → 0 ≤ peval q t := by
  induction ps with
  | nil =>
    intro l r h t h0 h1
    simp only [nnChainOK, decide_eq_true_eq] at h
    have : (r:ℝ) ≤ l := by exact_mod_cast h
    linarith
  | cons p ps ih =>
    intro l r h t h0 h1
    obtain ⟨A, B⟩ := p
    simp only [nnChainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hA⟩, hrest⟩ := h
    by_cases hb : (D:ℝ) * t < B
    · have hAR : (A:ℝ) ≤ l := by exact_mod_cast hA
      exact mob_sound q A B D hD hc (by linarith) hb
    · exact ih B r hrest t (by linarith) h1

/-- **Class theorem.** A nonnegative chain for `gapPoly Gn Gd` on `[lo/D, hi/D)`, `hi ≤ D`, gives
`Gn/Gd ≤ (√(2-2t))⁻¹` there. -/
theorem le_phi_chain (Gn : List ℤ) (Gd D : ℕ) (ps : List (ℤ × ℤ)) (lo hi : ℤ) (hGd : 0 < Gd)
    (hD : 0 < D) (hhi : hi ≤ D) (hch : nnChainOK (gapPoly Gn Gd) D ps lo hi = true)
    {t : ℝ} (h0 : (lo:ℝ) ≤ D * t) (h1 : (D:ℝ) * t < hi) :
    peval Gn t / Gd ≤ (√(2 - 2 * t))⁻¹ := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have ht1 : t < 1 := by
    have : (hi:ℝ) ≤ D := by exact_mod_cast hhi
    have : (D:ℝ) * t < D * 1 := by linarith
    exact lt_of_mul_lt_mul_left this hDR.le
  exact le_phi_of_gap Gn Gd hGd ht1 (nnChain_sound _ D hD ps lo hi hch t h0 h1)

/-! ### Shifted minorants (coercivity) -/

/-- Numerator of `Hn/Hd + k/m`. -/
def shiftN (Hn : List ℤ) (Hd : ℕ) (k : ℤ) (m : ℕ) : List ℤ := padd (pscale (m:ℤ) Hn) [k * Hd]

theorem peval_shift (Hn : List ℤ) (Hd : ℕ) (k : ℤ) (m : ℕ) (hHd : 0 < Hd) (hm : 0 < m) (t : ℝ) :
    peval (shiftN Hn Hd k m) t / ((m * Hd : ℕ) : ℝ) = peval Hn t / Hd + k / m := by
  have hd : (0 : ℝ) < Hd := by exact_mod_cast hHd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold shiftN
  simp only [peval_padd, peval_pscale, peval]
  push_cast
  field_simp
  ring

/-- **Coercivity test.** A nonnegative chain for the gap polynomial of `H + k/m` on `[lo/D, hi/D)`
gives `φ₁ - H ≥ k/m` there. -/
theorem shift_le_phi_chain (Hn : List ℤ) (Hd : ℕ) (k : ℤ) (m D : ℕ) (ps : List (ℤ × ℤ)) (lo hi : ℤ)
    (hHd : 0 < Hd) (hm : 0 < m) (hD : 0 < D) (hhi : hi ≤ D)
    (hch : nnChainOK (gapPoly (shiftN Hn Hd k m) (m * Hd)) D ps lo hi = true)
    {t : ℝ} (h0 : (lo:ℝ) ≤ D * t) (h1 : (D:ℝ) * t < hi) :
    (k : ℝ) / m ≤ (√(2 - 2 * t))⁻¹ - peval Hn t / Hd := by
  have h := le_phi_chain (shiftN Hn Hd k m) (m * Hd) D ps lo hi (Nat.mul_pos hm hHd) hD hhi hch h0 h1
  rw [peval_shift Hn Hd k m hHd hm] at h
  linarith

end CoulN7.Minor
