import RieszN7.Cap.Family
import RieszN7.Energy
import RieszN7.Core.Qs5

/-!
# The e-row of the cap family (LEAN_PLAN_range.md §3.2.3, E2): `E_s(P) ≤ e(family)` from per-object checks and pins

* `erowChk c` (kernel `Bool`, one `decide` per object): the object's `e`-row identity
  `e = H_A(−1) + 10 H_B(0) + 5 (H_C(c₁) + H_C(c₂))` over `ℤ[√5]` (`Qs5.homog5` evaluates each polynomial exactly at
  `−1`, `0`, `c₁ = (√5 − 1)/4`, `c₂ = −(1 + √5)/4`; the check compares rational and `√5` parts).
* `erowR_of_chk`: the check gives the identity for the object's real data `ef`, `HAf`, `HBf`, `HCf`.
* `efam_eq`: by linearity, the family satisfies the same identity for any real weights.
* `hE_of_pins`: with the family pins `H_A(−1) = φ_s(−1)`, `H_B(0) = φ_s(0)`, `H_C(c₁) + H_C(c₂) = φ_s(c₁) + φ_s(c₂)`,
  `E_s(P) = e(family)` (`RieszN7.pairEnergy_pent`), the `hE` input of `capSharp_of_family`.

Private, AI-written, not reviewed.
-/

open Real

namespace ThomsonN7.Cert.CapR

open ThomsonN7 ThomsonN7.Base ThomsonGen RieszN7.Qs5

/-- Integer coefficients as `ℤ[√5]` coefficients. -/
def lift5 (h : List ℤ) : List (ℤ × ℤ) := h.map fun a => (a, 0)

lemma peval5_lift5 (h : List ℤ) (x : ℝ) :
    peval5 (lift5 h) x = ∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * x ^ j := by
  induction h with
  | nil => simp [lift5, peval5]
  | cons a as ih =>
    simp only [lift5, List.map_cons] at ih ⊢
    rw [peval5, ih, List.length_cons, Finset.sum_range_succ', ev5_int]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)

lemma peval5_zero (L : List (ℤ × ℤ)) : peval5 L 0 = ev5 (L.headD (0, 0)) := by
  cases L with
  | nil => simp [peval5, ev5]
  | cons a as => simp [peval5]

/-- `peval5 (homog5 T E (lift5 h) n) 0 = E₀ⁿ · h(T₀/E₀)` for constant `T = [T₀]`, `E = [E₀]`, `n ≥ len h − 1`. -/
lemma homog5_const (T0 E0 : ℤ × ℤ) (hE : ev5 E0 ≠ 0) (h : List ℤ) (n : ℕ) (hn : h.length ≤ n + 1) :
    ev5 ((homog5 [T0] [E0] (lift5 h) n).headD (0, 0))
      = ev5 E0 ^ n * ∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * (ev5 T0 / ev5 E0) ^ j := by
  have hE' : peval5 [E0] 0 ≠ 0 := by simpa [peval5] using hE
  rw [← peval5_zero, peval5_homog5 [T0] [E0] 0 hE' (lift5 h) n (by simpa [lift5] using hn), peval5_lift5]
  simp [peval5]

/-- Evaluation points as `(T₀, E₀)`: `−1 = −1/1`, `0 = 0/1`, `c₁ = (−1 + √5)/4`, `c₂ = (−1 − √5)/4`. -/
def ptA : (ℤ × ℤ) × (ℤ × ℤ) := ((-1, 0), (1, 0))
def ptB : (ℤ × ℤ) × (ℤ × ℤ) := ((0, 0), (1, 0))
def ptC1 : (ℤ × ℤ) × (ℤ × ℤ) := ((-1, 1), (4, 0))
def ptC2 : (ℤ × ℤ) × (ℤ × ℤ) := ((-1, -1), (4, 0))

/-- `E₀ⁿ · h(T₀/E₀)` as an element of `ℤ[√5]`, `n = len h`. -/
def at5 (p : (ℤ × ℤ) × (ℤ × ℤ)) (h : List ℤ) : ℤ × ℤ := (homog5 [p.1] [p.2] (lift5 h) h.length).headD (0, 0)

/-- **The e-row check** of one object: with `n = len H_C` and `A = H_A(−1)`, `B = H_B(0)` (integers, scale 1),
`4ⁿ e = 4ⁿ (A + 10 B) + 5 (4ⁿ H_C(c₁) + 4ⁿ H_C(c₂))` in `ℤ[√5]` (rational and `√5` parts). -/
def erowChk (c : TCertR) : Bool :=
  let A := at5 ptA c.HA
  let B := at5 ptB c.HB
  let C1 := at5 ptC1 c.HC
  let C2 := at5 ptC2 c.HC
  let q : ℤ := 4 ^ c.HC.length
  decide (q * c.e = q * (A.1 + 10 * B.1) + 5 * (C1.1 + C2.1)) &&
    decide (0 = q * (A.2 + 10 * B.2) + 5 * (C1.2 + C2.2))

lemma ev5_ptA : ev5 ptA.1 / ev5 ptA.2 = -1 := by simp [ptA, ev5]
lemma ev5_ptB : ev5 ptB.1 / ev5 ptB.2 = 0 := by simp [ptB, ev5]
lemma ev5_ptC1 : ev5 ptC1.1 / ev5 ptC1.2 = c1 := by
  simp only [ptC1, ev5, c1]; push_cast; ring
lemma ev5_ptC2 : ev5 ptC2.1 / ev5 ptC2.2 = c2 := by
  simp only [ptC2, ev5, c2]; push_cast; ring

lemma polyR_sum (Lam : ℕ) (h : List ℤ) (x : ℝ) :
    polyR Lam h x = (∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * x ^ j) / Lam := rfl

/-- The e-row identity of one object, in real form. -/
def ERowR (c : TCertR) : Prop :=
  c.hdr.ef = c.hdr.HAf (-1) + 10 * c.hdr.HBf 0 + 5 * c.hdr.HCf c1 + 5 * c.hdr.HCf c2

theorem erowR_of_chk (c : TCertR) (h : erowChk c = true) : ERowR c := by
  simp only [erowChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have eA := homog5_const ptA.1 ptA.2 (by simp [ptA, ev5]) c.HA c.HA.length (by omega)
  have eB := homog5_const ptB.1 ptB.2 (by simp [ptB, ev5]) c.HB c.HB.length (by omega)
  have eC1 := homog5_const ptC1.1 ptC1.2 (by simp [ptC1, ev5]) c.HC c.HC.length (by omega)
  have eC2 := homog5_const ptC2.1 ptC2.2 (by simp [ptC2, ev5]) c.HC c.HC.length (by omega)
  rw [ev5_ptA] at eA
  rw [ev5_ptB] at eB
  rw [ev5_ptC1] at eC1
  rw [ev5_ptC2] at eC2
  have hA1 : ev5 ptA.2 = 1 := by simp [ptA, ev5]
  have hB1 : ev5 ptB.2 = 1 := by simp [ptB, ev5]
  have hC1 : ev5 ptC1.2 = 4 := by simp [ptC1, ev5]
  have hC2 : ev5 ptC2.2 = 4 := by simp [ptC2, ev5]
  rw [hA1, one_pow, one_mul] at eA
  rw [hB1, one_pow, one_mul] at eB
  rw [hC1] at eC1
  rw [hC2] at eC2
  -- the four values as `ℤ[√5]` elements
  change ev5 (at5 ptA c.HA) = _ at eA
  change ev5 (at5 ptB c.HB) = _ at eB
  change ev5 (at5 ptC1 c.HC) = _ at eC1
  change ev5 (at5 ptC2 c.HC) = _ at eC2
  unfold ERowR
  change (c.e : ℝ) / c.Lam = (∑ j ∈ Finset.range c.HA.length, (c.HA.getD j 0 : ℝ) * (-1) ^ j) / c.Lam
    + 10 * ((∑ j ∈ Finset.range c.HB.length, (c.HB.getD j 0 : ℝ) * 0 ^ j) / c.Lam)
    + 5 * ((∑ j ∈ Finset.range c.HC.length, (c.HC.getD j 0 : ℝ) * c1 ^ j) / c.Lam)
    + 5 * ((∑ j ∈ Finset.range c.HC.length, (c.HC.getD j 0 : ℝ) * c2 ^ j) / c.Lam)
  rw [← eA, ← eB]
  have key : (4 : ℝ) ^ c.HC.length * c.e = (4 : ℝ) ^ c.HC.length * (ev5 (at5 ptA c.HA) + 10 * ev5 (at5 ptB c.HB))
      + 5 * (ev5 (at5 ptC1 c.HC) + ev5 (at5 ptC2 c.HC)) := by
    have r1 : ((4 ^ c.HC.length * c.e : ℤ) : ℝ) = ((4 ^ c.HC.length * ((at5 ptA c.HA).1 + 10 * (at5 ptB c.HB).1)
      + 5 * ((at5 ptC1 c.HC).1 + (at5 ptC2 c.HC).1) : ℤ) : ℝ) := by exact_mod_cast h1
    have r2 : ((0 : ℤ) : ℝ) = ((4 ^ c.HC.length * ((at5 ptA c.HA).2 + 10 * (at5 ptB c.HB).2)
      + 5 * ((at5 ptC1 c.HC).2 + (at5 ptC2 c.HC).2) : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at r1 r2
    simp only [ev5]
    linear_combination r1 + Real.sqrt 5 * r2
  rw [eC1, eC2] at key
  have h4 : (4 : ℝ) ^ c.HC.length ≠ 0 := by positivity
  generalize (∑ j ∈ Finset.range c.HC.length, (c.HC.getD j 0 : ℝ) * c1 ^ j) = S1 at key ⊢
  generalize (∑ j ∈ Finset.range c.HC.length, (c.HC.getD j 0 : ℝ) * c2 ^ j) = S2 at key ⊢
  generalize ev5 (at5 ptA c.HA) = A at key ⊢
  generalize ev5 (at5 ptB c.HB) = B at key ⊢
  have key' : (c.e : ℝ) = A + 10 * B + 5 * S1 + 5 * S2 := by
    apply mul_left_cancel₀ h4
    linear_combination key
  rw [key']
  ring

/-! ### Pin values of one object (`H_A(−1)`, `H_B(0)`, `(H_C(c₁) + H_C(c₂))/2`) -/

lemma evalA (c : TCertR) : c.hdr.HAf (-1) = ev5 (at5 ptA c.HA) / c.Lam := by
  have e := homog5_const ptA.1 ptA.2 (by simp [ptA, ev5]) c.HA c.HA.length (by omega)
  rw [ev5_ptA, show ev5 ptA.2 = 1 by simp [ptA, ev5], one_pow, one_mul] at e
  change _ = ev5 (at5 ptA c.HA) / c.Lam
  rw [show ev5 (at5 ptA c.HA) = _ from e]
  rfl

lemma evalB (c : TCertR) : c.hdr.HBf 0 = ev5 (at5 ptB c.HB) / c.Lam := by
  have e := homog5_const ptB.1 ptB.2 (by simp [ptB, ev5]) c.HB c.HB.length (by omega)
  rw [ev5_ptB, show ev5 ptB.2 = 1 by simp [ptB, ev5], one_pow, one_mul] at e
  change _ = ev5 (at5 ptB c.HB) / c.Lam
  rw [show ev5 (at5 ptB c.HB) = _ from e]
  rfl

lemma evalC1 (c : TCertR) : c.hdr.HCf c1 = ev5 (at5 ptC1 c.HC) / (4 ^ c.HC.length * c.Lam) := by
  have e := homog5_const ptC1.1 ptC1.2 (by simp [ptC1, ev5]) c.HC c.HC.length (by omega)
  rw [ev5_ptC1, show ev5 ptC1.2 = 4 by simp [ptC1, ev5]] at e
  change _ = ev5 (at5 ptC1 c.HC) / (4 ^ c.HC.length * c.Lam)
  rw [show ev5 (at5 ptC1 c.HC) = _ from e, mul_div_mul_left _ _ (by positivity : (4 : ℝ) ^ c.HC.length ≠ 0)]
  rfl

lemma evalC2 (c : TCertR) : c.hdr.HCf c2 = ev5 (at5 ptC2 c.HC) / (4 ^ c.HC.length * c.Lam) := by
  have e := homog5_const ptC2.1 ptC2.2 (by simp [ptC2, ev5]) c.HC c.HC.length (by omega)
  rw [ev5_ptC2, show ev5 ptC2.2 = 4 by simp [ptC2, ev5]] at e
  change _ = ev5 (at5 ptC2 c.HC) / (4 ^ c.HC.length * c.Lam)
  rw [show ev5 (at5 ptC2 c.HC) = _ from e, mul_div_mul_left _ _ (by positivity : (4 : ℝ) ^ c.HC.length ≠ 0)]
  rfl

/-- **Pin check** of one object against integer targets `(dA, dB, dC)` (the directions' unit pins). -/
def pinChk (c : TCertR) (dA dB dC : ℤ) : Bool :=
  let C1 := at5 ptC1 c.HC
  let C2 := at5 ptC2 c.HC
  decide (at5 ptA c.HA = (dA * c.Lam, 0)) && decide (at5 ptB c.HB = (dB * c.Lam, 0)) &&
    decide (C1.1 + C2.1 = 2 * dC * c.Lam * 4 ^ c.HC.length) && decide (C1.2 + C2.2 = 0)

theorem pin_of_chk (c : TCertR) (dA dB dC : ℤ) (hL : 0 < c.Lam) (h : pinChk c dA dB dC = true) :
    c.hdr.HAf (-1) = dA ∧ c.hdr.HBf 0 = dB ∧ (c.hdr.HCf c1 + c.hdr.HCf c2) / 2 = dC := by
  simp only [pinChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hA, hB⟩, hC1⟩, hC2⟩ := h
  have hL' : (c.Lam : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h4 : (4 : ℝ) ^ c.HC.length ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [evalA, hA, div_eq_iff hL']; simp only [ev5]; push_cast; ring
  · rw [evalB, hB, div_eq_iff hL']; simp only [ev5]; push_cast; ring
  · rw [evalC1, evalC2, ← add_div]
    have r1 : (((at5 ptC1 c.HC).1 + (at5 ptC2 c.HC).1 : ℤ) : ℝ) = ((2 * dC * c.Lam * 4 ^ c.HC.length : ℤ) : ℝ) := by
      exact_mod_cast hC1
    have r2 : (((at5 ptC1 c.HC).2 + (at5 ptC2 c.HC).2 : ℤ) : ℝ) = 0 := by exact_mod_cast hC2
    push_cast at r1 r2
    have hs : ev5 (at5 ptC1 c.HC) + ev5 (at5 ptC2 c.HC) = 2 * dC * c.Lam * 4 ^ c.HC.length := by
      simp only [ev5]
      linear_combination r1 + Real.sqrt 5 * r2
    rw [hs, div_div, div_eq_iff (mul_ne_zero (mul_ne_zero h4 hL') two_ne_zero)]
    ring

section Family

variable {J : ℕ} (cf : Fin J → TCertR) (w : Fin J → ℝ)

theorem efam_eq (h : ∀ j, ERowR (cf j)) :
    efam cf w = HAfam cf w (-1) + 10 * HBfam cf w 0 + 5 * HCfam cf w c1 + 5 * HCfam cf w c2 := by
  simp only [efam, HAfam, HBfam, HCfam, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j]
  ring

/-- **`hE` of `capSharp_of_family` from the e-row and the family pins.** -/
theorem hE_of_pins (s : ℝ) (h : ∀ j, ERowR (cf j))
    (hA : HAfam cf w (-1) = RieszN7.phiS s (-1)) (hB : HBfam cf w 0 = RieszN7.phiS s 0)
    (hC : HCfam cf w c1 + HCfam cf w c2 = RieszN7.phiS s c1 + RieszN7.phiS s c2) :
    pairEnergy (RieszN7.phiS s) pentBipyramid ≤ efam cf w := by
  rw [RieszN7.pairEnergy_pent, efam_eq cf w h, hA, hB]
  linarith

end Family

end ThomsonN7.Cert.CapR
