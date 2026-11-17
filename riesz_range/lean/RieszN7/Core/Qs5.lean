import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `RieszN7.Core.Qs5` — polynomials over `ℤ[√5]` and Möbius/Bernstein positivity (LEAN_PLAN_range.md §3.0.6)

A coefficient is an integer pair `(x, y)` meaning `x + y√5` (`ev5`); a polynomial is a list of pairs, low degree first
(`peval5`).  The list operations `padd5 / pscale5 / pmul5 / ppow5 / homog5` are those of `LogLean.Minor` with pair
arithmetic, and `peval5_homog5` is `peval_homog` over `ℤ[√5]`.  The sign of `x + y√5` is decided **exactly** by integer
comparisons (`nonneg5`: `x, y ≥ 0`, or `x ≥ 0 ∧ 5y² ≤ x²`, or `y ≥ 0 ∧ x² ≤ 5y²`), so no `√5` enclosure is needed.
`mob5_sound`: all Möbius coefficients `≥ 0` ⇒ `q ≥ 0` on `[A/D, B/D)`.

Use (window of the C-class minorant at `c₁ = (√5 − 1)/4`): with `T = [(−1, 1), (4, 0)]`, `E = [(4, 0)]`,
`homog5 T E q m = 4^m · q(c₁ + δ)` is the exact Taylor shift to the variable `δ = t − c₁`; its coefficients 0 and 1 are the
pins `H(c₁)`, `H'(c₁)` (checked by `decide`), and dropping them is the exact division by `(t − c₁)²`.
Private prototype (Phase 1), AI-written, not reviewed.
-/

namespace RieszN7.Qs5

/-- `x + y √5`. -/
noncomputable def ev5 (a : ℤ × ℤ) : ℝ := (a.1 : ℝ) + (a.2 : ℝ) * Real.sqrt 5

def add5 (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 + b.1, a.2 + b.2)

def mul5 (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 * b.1 + 5 * (a.2 * b.2), a.1 * b.2 + a.2 * b.1)

theorem sqrt5_mul_self : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)

theorem ev5_add (a b : ℤ × ℤ) : ev5 (add5 a b) = ev5 a + ev5 b := by
  simp only [ev5, add5]; push_cast; ring

theorem ev5_mul (a b : ℤ × ℤ) : ev5 (mul5 a b) = ev5 a * ev5 b := by
  simp only [ev5, mul5]; push_cast
  linear_combination (-((a.2 : ℝ) * (b.2 : ℝ))) * sqrt5_mul_self

theorem ev5_zero : ev5 (0, 0) = 0 := by simp [ev5]

theorem ev5_one : ev5 (1, 0) = 1 := by simp [ev5]

theorem ev5_int (a : ℤ) : ev5 (a, 0) = a := by simp [ev5]

/-- Polynomial over `ℤ[√5]` evaluated at a real point. -/
noncomputable def peval5 : List (ℤ × ℤ) → ℝ → ℝ
  | [], _ => 0
  | a :: as, y => ev5 a + y * peval5 as y

def padd5 : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => add5 a b :: padd5 as bs

def pscale5 (c : ℤ × ℤ) (p : List (ℤ × ℤ)) : List (ℤ × ℤ) := p.map (mul5 c)

def pmul5 : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | [], _ => []
  | a :: as, q => padd5 (pscale5 a q) ((0, 0) :: pmul5 as q)

def ppow5 (p : List (ℤ × ℤ)) : ℕ → List (ℤ × ℤ)
  | 0 => [(1, 0)]
  | n + 1 => pmul5 p (ppow5 p n)

def homog5 (T E : List (ℤ × ℤ)) : List (ℤ × ℤ) → ℕ → List (ℤ × ℤ)
  | [], _ => []
  | c :: cs, m => padd5 (pscale5 c (ppow5 E m)) (pmul5 T (homog5 T E cs (m - 1)))

theorem peval5_padd5 (p q : List (ℤ × ℤ)) (y : ℝ) : peval5 (padd5 p q) y = peval5 p y + peval5 q y := by
  induction p generalizing q with
  | nil => simp [padd5, peval5]
  | cons a as ih =>
    cases q with
    | nil => simp [padd5, peval5]
    | cons b bs => simp only [padd5, peval5, ih, ev5_add]; ring

theorem peval5_pscale5 (c : ℤ × ℤ) (p : List (ℤ × ℤ)) (y : ℝ) :
    peval5 (pscale5 c p) y = ev5 c * peval5 p y := by
  induction p with
  | nil => simp [pscale5, peval5]
  | cons a as ih =>
    simp only [pscale5, List.map_cons, peval5, ev5_mul] at ih ⊢
    rw [ih]; ring

theorem peval5_pmul5 (p q : List (ℤ × ℤ)) (y : ℝ) : peval5 (pmul5 p q) y = peval5 p y * peval5 q y := by
  induction p with
  | nil => simp [pmul5, peval5]
  | cons a as ih =>
    simp only [pmul5, peval5_padd5, peval5_pscale5, peval5, ih, ev5_zero]; ring

theorem peval5_ppow5 (p : List (ℤ × ℤ)) (n : ℕ) (y : ℝ) : peval5 (ppow5 p n) y = peval5 p y ^ n := by
  induction n with
  | zero => simp [ppow5, peval5, ev5_one]
  | succ n ih => simp only [ppow5, peval5_pmul5, ih, pow_succ]; ring

theorem peval5_homog5 (T E : List (ℤ × ℤ)) (x : ℝ) (hE : peval5 E x ≠ 0) (q : List (ℤ × ℤ)) :
    ∀ m : ℕ, q.length ≤ m + 1 →
      peval5 (homog5 T E q m) x = peval5 E x ^ m * peval5 q (peval5 T x / peval5 E x) := by
  induction q with
  | nil => intro m _; simp [homog5, peval5]
  | cons c cs ih =>
    intro m hm
    simp only [List.length_cons] at hm
    rw [homog5.eq_2, peval5_padd5, peval5_pscale5, peval5_pmul5, peval5_ppow5, ih (m - 1) (by omega)]
    obtain ⟨u, hu⟩ : ∃ u, peval5 T x = peval5 E x * u := ⟨_, (mul_div_cancel₀ _ hE).symm⟩
    have hdiv : peval5 T x / peval5 E x = u := by rw [hu, mul_div_cancel_left₀ _ hE]
    rw [hdiv, hu]
    rcases m with _ | m'
    · have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp only [peval5]
      ring
    · simp only [Nat.add_sub_cancel, peval5]
      ring

/-! ### Exact sign decision -/

def nonneg5 (a : ℤ × ℤ) : Bool :=
  decide (0 ≤ a.1 ∧ 0 ≤ a.2) || decide (0 ≤ a.1 ∧ 5 * (a.2 * a.2) ≤ a.1 * a.1) ||
    decide (0 ≤ a.2 ∧ a.1 * a.1 ≤ 5 * (a.2 * a.2))

theorem nonneg5_sound (a : ℤ × ℤ) (h : nonneg5 a = true) : 0 ≤ ev5 a := by
  obtain ⟨x, y⟩ := a
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 := sqrt5_mul_self
  simp only [nonneg5, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [ev5]
  rcases h with (⟨hx, hy⟩ | ⟨hx, hxy⟩) | ⟨hy, hxy⟩
  · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
    positivity
  · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    have hxy' : (5 : ℝ) * ((y : ℝ) * y) ≤ (x : ℝ) * x := by exact_mod_cast hxy
    by_contra hneg
    rw [not_le] at hneg
    have hpos : 0 < (x : ℝ) - y * Real.sqrt 5 := by nlinarith
    have hprod := mul_neg_of_neg_of_pos hneg hpos
    have e : ((x : ℝ) + y * Real.sqrt 5) * ((x : ℝ) - y * Real.sqrt 5) = (x : ℝ) * x - 5 * ((y : ℝ) * y) := by
      linear_combination (-((y : ℝ) * y)) * hs2
    linarith
  · have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
    have hxy' : (x : ℝ) * x ≤ 5 * ((y : ℝ) * y) := by exact_mod_cast hxy
    by_contra hneg
    rw [not_le] at hneg
    have hys : 0 ≤ (y : ℝ) * Real.sqrt 5 := mul_nonneg hy' hs
    have hpos : 0 < (y : ℝ) * Real.sqrt 5 - x := by linarith
    have hprod := mul_neg_of_neg_of_pos hneg hpos
    have e : ((x : ℝ) + y * Real.sqrt 5) * ((y : ℝ) * Real.sqrt 5 - x) = 5 * ((y : ℝ) * y) - (x : ℝ) * x := by
      linear_combination ((y : ℝ) * y) * hs2
    linarith

def all5 (p : List (ℤ × ℤ)) : Bool := p.all nonneg5

theorem peval5_nonneg_of_all (p : List (ℤ × ℤ)) (h : all5 p = true) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ peval5 p x := by
  induction p with
  | nil => simp [peval5]
  | cons a as ih =>
    simp only [all5, List.all_cons, Bool.and_eq_true] at h
    simp only [peval5]
    exact add_nonneg (nonneg5_sound a h.1) (mul_nonneg hx (ih h.2))

/-- **Möbius positivity over `ℤ[√5]`.** -/
theorem mob5_sound (q : List (ℤ × ℤ)) (A B : ℤ) (D : ℕ) (hD : 0 < D)
    (hchk : all5 (homog5 [(A, 0), (B, 0)] [((D : ℤ), 0), ((D : ℤ), 0)] q (q.length - 1)) = true)
    {t : ℝ} (ht0 : (A : ℝ) ≤ D * t) (ht1 : (D : ℝ) * t < B) : 0 ≤ peval5 q t := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hden : 0 < (B : ℝ) - D * t := by linarith
  set x : ℝ := ((D : ℝ) * t - A) / (B - D * t) with hxdef
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hden.le
  have hx : x * ((B : ℝ) - D * t) = D * t - A := div_mul_cancel₀ _ hden.ne'
  have hE : peval5 [((D : ℤ), 0), ((D : ℤ), 0)] x = (D : ℝ) * (1 + x) := by
    simp only [peval5, ev5_int, Int.cast_natCast]; ring
  have hT : peval5 [(A, 0), (B, 0)] x = (A : ℝ) + B * x := by
    simp only [peval5, ev5_int]; ring
  have hEpos : 0 < (D : ℝ) * (1 + x) := by positivity
  have hratio : peval5 [(A, 0), (B, 0)] x / peval5 [((D : ℤ), 0), ((D : ℤ), 0)] x = t := by
    rw [hE, hT, div_eq_iff hEpos.ne']
    linear_combination hx
  have key := peval5_homog5 [(A, 0), (B, 0)] [((D : ℤ), 0), ((D : ℤ), 0)] x (by rw [hE]; exact hEpos.ne') q
    (q.length - 1) (by omega)
  rw [hratio] at key
  have h1 := peval5_nonneg_of_all _ hchk hx0
  rw [key, hE] at h1
  exact (mul_nonneg_iff_of_pos_left (pow_pos hEpos _)).mp h1

/-! ### Unit test: `(t − c₁)² ≥ 0` written over `ℤ[√5]`: `t² − 2c₁ t + c₁²`, `c₁² = (3 − √5)/8`; scaled by 8 -/

/-- `8 t² − 4(√5 − 1) t + (3 − √5)`. -/
def testQ : List (ℤ × ℤ) := [(3, -1), (4, -4), (8, 0)]

/-- Its Taylor shift at `c₁` (`T/E = c₁ + δ`) is `4² · 8 δ²` exactly: coefficients 0, 1 vanish (`decide`). -/
theorem testQ_shift : homog5 [(-1, 1), (4, 0)] [(4, 0)] testQ 2 = [(0, 0), (0, 0), (128, 0), (0, 0)] := by decide +kernel

/-- On `[0, 1)` (which contains `c₁`) the Möbius coefficients are not all `≥ 0`; on `[1, 2)` they are. -/
theorem testQ_bad : all5 (homog5 [(0, 0), (1, 0)] [(1, 0), (1, 0)] testQ 2) = false := by decide +kernel

theorem testQ_ok : all5 (homog5 [(1, 0), (2, 0)] [(1, 0), (1, 0)] testQ (testQ.length - 1)) = true := by
  decide +kernel

example (t : ℝ) (h0 : 1 ≤ t) (h1 : t < 2) : 0 ≤ peval5 testQ t :=
  mob5_sound testQ 1 2 1 (by norm_num) testQ_ok (by push_cast; linarith) (by push_cast; linarith)

end RieszN7.Qs5
