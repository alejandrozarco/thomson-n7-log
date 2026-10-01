/-
Riesz2/MinorCore.lean — 1-D minorant machinery for the Riesz s = 2 kernel `phi2 t = 1/(2-2t)`
(lean/RIESZ2_LEAN_PLAN.md §3).

Everything is rational: for `t < 1` and `H = Hn/Hd`,
  `phi2 t - H t = (Hd - (2-2t) Hn(t)) / (Hd (2-2t))`.
The generator supplies integer lists `F`, `Qn` and `Qd > 0` with the EXACT identity
  `Qd · (Hd - (2-2t)·Hn) = Hd · F · Qn`   (checked in the kernel as a list of zeros, `gapId`),
so `phi2 t - H t = F(t)·Qn(t) / (Qd (2-2t))`.  `Qn > 0` on the range follows from a chain of Möbius
pieces whose Bernstein coefficients are all `≥ 0` with a positive head (`mob_pos`, `posChainOK`).
Then `H ≤ phi2`, with equality only where `F(t) = 0` (the exact contact set of the sharp cap).

§1 integer polynomials and §2 Möbius coefficients are ported from upstream `ThomsonN7/Solution.lean`
(blocks `CutOneD` and `Asm_Coerce` §A, huwngtran/thomson-n7-lean @ 25f2fa5) via `LogLean.MinorCore`
(same definitions and proofs).  Every check is a `Bool` closed by `decide +kernel`; no `native_decide`.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `peval_nonneg_of_all` ← `CutOneD.peval_eq_zero_of_all`.

`peval`, `padd`, `pscale`, `pneg`, `pmul`, `ppow` and their `peval_*` lemmas are upstream
`CutOneD.*` / `Glue.Coerce.*` declarations used unchanged; they are not stored here but
regenerated into `ThomsonGen/Verbatim/MinorPoly.lean` by `regen.sh`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import ThomsonGen.Verbatim.MinorPoly

open Finset

namespace Riesz2.Minor

/-! ## 1. Integer polynomials (upstream `CutOneD` / `Asm_Coerce` §A) -/

/-- All coefficients nonnegative ⇒ nonnegative on `[0, ∞)`. -/
theorem peval_nonneg_of_all (p : List ℤ) (h : p.all (fun c => decide (0 ≤ c)) = true) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ peval p x := by
  induction p with
  | nil => simp [peval]
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [peval]
    have ha : (0:ℝ) ≤ a := by exact_mod_cast h.1
    exact add_nonneg ha (mul_nonneg hx (ih h.2))

/-- Head coefficient positive, all others nonnegative. -/
def headPos : List ℤ → Bool
  | [] => false
  | c :: cs => decide (0 < c) && cs.all (fun c => decide (0 ≤ c))

/-- `headPos` ⇒ strictly positive on `[0, ∞)`. -/
theorem peval_pos_of_headPos (p : List ℤ) (h : headPos p = true) {x : ℝ} (hx : 0 ≤ x) :
    0 < peval p x := by
  cases p with
  | nil => simp [headPos] at h
  | cons c cs =>
    simp only [headPos, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [peval]
    have hc : (0:ℝ) < c := by exact_mod_cast h.1
    have := peval_nonneg_of_all cs h.2 hx
    nlinarith

/-! ## 2. Möbius (Bernstein) coefficients computed in the kernel

`homog T E q m = Σ_j q_j T^j E^(m-j)`.  With `T = A + B x`, `E = D (1 + x)`, the substitution
`t = (A + B x)/(D (1 + x))` maps `x ∈ [0, ∞)` onto `t ∈ [A/D, B/D)`, and
`homog T E q m = E^m · q(t)`; its coefficients are (scaled) Bernstein coefficients of `q` on
`[A/D, B/D]`.  All `≥ 0` ⇒ `q ≥ 0` on `[A/D, B/D)`; head `> 0` too ⇒ `q > 0` there. -/

def homog (T E : List ℤ) : List ℤ → ℕ → List ℤ
  | [], _ => []
  | c :: cs, m => padd (pscale c (ppow E m)) (pmul T (homog T E cs (m - 1)))

theorem peval_homog (T E : List ℤ) (x : ℝ) (hE : peval E x ≠ 0) (q : List ℤ) :
    ∀ m : ℕ, q.length ≤ m + 1 →
      peval (homog T E q m) x = peval E x ^ m * peval q (peval T x / peval E x) := by
  induction q with
  | nil => intro m _; simp [homog, peval]
  | cons c cs ih =>
    intro m hm
    rcases cs with _ | ⟨d, ds⟩
    · simp only [homog, peval_padd, peval_pscale, peval_pmul, peval_ppow, peval]
      ring
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
      have ih' := ih m' (by simp at hm ⊢; omega)
      rw [show homog T E (c :: d :: ds) (m' + 1) =
          padd (pscale c (ppow E (m' + 1))) (pmul T (homog T E (d :: ds) m')) from rfl]
      simp only [peval_padd, peval_pscale, peval_pmul, peval_ppow, ih']
      simp only [peval]
      rw [pow_succ]
      field_simp

/-- The Möbius substitution: `x = (Dt - A)/(B - Dt) ≥ 0`, `E(x) > 0`, `T(x)/E(x) = t`. -/
theorem mob_setup (A B : ℤ) (D : ℕ) (hD : 0 < D) {t : ℝ} (ht0 : (A:ℝ) ≤ D * t)
    (ht1 : (D:ℝ) * t < B) :
    ∃ x : ℝ, 0 ≤ x ∧ 0 < peval [(D:ℤ), (D:ℤ)] x ∧
      peval [A, B] x / peval [(D:ℤ), (D:ℤ)] x = t := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hden : 0 < (B:ℝ) - D * t := by linarith
  set x : ℝ := ((D:ℝ) * t - A) / (B - D * t) with hxdef
  have hx : 0 ≤ x := div_nonneg (by linarith) hden.le
  have hE : peval [(D:ℤ), (D:ℤ)] x = D * (1 + x) := by
    simp only [peval, mul_zero, add_zero]; push_cast; ring
  have hT : peval [A, B] x = A + B * x := by
    simp only [peval, mul_zero, add_zero]; ring
  have hEpos : 0 < peval [(D:ℤ), (D:ℤ)] x := by rw [hE]; exact mul_pos hDR (by linarith)
  refine ⟨x, hx, hEpos, ?_⟩
  rw [hE, hT, div_eq_iff (mul_pos hDR (by linarith)).ne', hxdef]
  field_simp
  ring

/-- **Möbius positivity** (nonnegative version). -/
theorem mob_sound (q : List ℤ) (A B : ℤ) (D : ℕ) (hD : 0 < D)
    (hchk : (homog [A, B] [(D:ℤ), (D:ℤ)] q (q.length - 1)).all (fun c => decide (0 ≤ c)) = true)
    {t : ℝ} (ht0 : (A:ℝ) ≤ D * t) (ht1 : (D:ℝ) * t < B) : 0 ≤ peval q t := by
  obtain ⟨x, hx, hEpos, hratio⟩ := mob_setup A B D hD ht0 ht1
  have key := peval_homog [A, B] [(D:ℤ), (D:ℤ)] x hEpos.ne' q (q.length - 1) (by omega)
  rw [hratio] at key
  have h1 := peval_nonneg_of_all _ hchk hx
  rw [key] at h1
  exact (mul_nonneg_iff_of_pos_left (pow_pos hEpos _)).mp h1

/-- **Möbius positivity** (strict version). -/
theorem mob_pos (q : List ℤ) (A B : ℤ) (D : ℕ) (hD : 0 < D)
    (hchk : headPos (homog [A, B] [(D:ℤ), (D:ℤ)] q (q.length - 1)) = true)
    {t : ℝ} (ht0 : (A:ℝ) ≤ D * t) (ht1 : (D:ℝ) * t < B) : 0 < peval q t := by
  obtain ⟨x, hx, hEpos, hratio⟩ := mob_setup A B D hD ht0 ht1
  have key := peval_homog [A, B] [(D:ℤ), (D:ℤ)] x hEpos.ne' q (q.length - 1) (by omega)
  rw [hratio] at key
  have h1 := peval_pos_of_headPos _ hchk hx
  rw [key] at h1
  exact (mul_pos_iff_of_pos_left (pow_pos hEpos _)).mp h1

/-! ## 3. Chains of positive pieces -/

/-- Chain of pieces `[A/D, B/D)` covering `[l/D, r/D)`, each with `headPos` Möbius coefficients. -/
def posChainOK (q : List ℤ) (D : ℕ) : List (ℤ × ℤ) → ℤ → ℤ → Bool
  | [], l, r => decide (r ≤ l)
  | (A, B) :: ps, l, r =>
    headPos (homog [A, B] [(D:ℤ), (D:ℤ)] q (q.length - 1)) && decide (A ≤ l) &&
      posChainOK q D ps B r

theorem posChain_sound (q : List ℤ) (D : ℕ) (hD : 0 < D) (ps : List (ℤ × ℤ)) :
    ∀ l r : ℤ, posChainOK q D ps l r = true →
      ∀ t : ℝ, (l:ℝ) ≤ D * t → (D:ℝ) * t < r → 0 < peval q t := by
  induction ps with
  | nil =>
    intro l r h t h0 h1
    simp only [posChainOK, decide_eq_true_eq] at h
    have : (r:ℝ) ≤ l := by exact_mod_cast h
    linarith
  | cons p ps ih =>
    intro l r h t h0 h1
    obtain ⟨A, B⟩ := p
    simp only [posChainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hA⟩, hrest⟩ := h
    by_cases hb : (D:ℝ) * t < B
    · have hAR : (A:ℝ) ≤ l := by exact_mod_cast hA
      exact mob_pos q A B D hD hc (by linarith) hb
    · exact ih B r hrest t (by linarith) h1

/-! ## 4. The kernel and the exact gap identity -/

/-- Riesz `s = 2` pair potential `phi2 t = 1/(2 - 2t)` (`= ‖x - y‖⁻²` for unit `x, y`). -/
noncomputable def phi2 (t : ℝ) : ℝ := 1 / (2 - 2 * t)

/-- The exact identity `Qd·(Hd - (2-2t)·Hn) = Hd·F·Qn`, as a list of zeros. -/
def gapId (Hn : List ℤ) (Hd : ℕ) (F Qn : List ℤ) (Qd : ℕ) : Bool :=
  (padd (pscale (Qd:ℤ) (padd [(Hd:ℤ)] (pneg (pmul [2, -2] Hn))))
    (pneg (pscale (Hd:ℤ) (pmul F Qn)))).all (· == 0)

theorem gap_eq (Hn : List ℤ) (Hd : ℕ) (F Qn : List ℤ) (Qd : ℕ) (hHd : 0 < Hd) (hQd : 0 < Qd)
    (hid : gapId Hn Hd F Qn Qd = true) {t : ℝ} (ht : t < 1) :
    phi2 t - peval Hn t / Hd = peval F t * peval Qn t / (Qd * (2 - 2 * t)) := by
  have h := peval_eq_zero_of_all _ hid t
  simp only [peval_padd, peval_pscale, peval_pneg, peval_pmul, peval, mul_zero, add_zero] at h
  push_cast at h
  have hHdR : (0:ℝ) < Hd := by exact_mod_cast hHd
  have hQdR : (0:ℝ) < Qd := by exact_mod_cast hQd
  have h2 : (0:ℝ) < 2 - 2 * t := by linarith
  unfold phi2
  rw [div_sub_div _ _ h2.ne' hHdR.ne', div_eq_div_iff (mul_pos h2 hHdR).ne' (mul_pos hQdR h2).ne']
  linear_combination (2 - 2 * t) * h

/-! ## 5. Class theorems -/

/-- **Sharp class theorem.** Identity + positive chain on `[lo/D, hi/D)` ⇒ `H ≤ phi2` there, with
equality only where `F t = 0`; needs `0 ≤ F t`. -/
theorem class_sharp (Hn : List ℤ) (Hd : ℕ) (F Qn : List ℤ) (Qd D : ℕ) (ps : List (ℤ × ℤ))
    (lo hi : ℤ) (hHd : 0 < Hd) (hQd : 0 < Qd) (hD : 0 < D) (hhi : hi ≤ D)
    (hid : gapId Hn Hd F Qn Qd = true) (hch : posChainOK Qn D ps lo hi = true)
    {t : ℝ} (h0 : (lo:ℝ) ≤ D * t) (h1 : (D:ℝ) * t < hi) (hF : 0 ≤ peval F t) :
    peval Hn t / Hd ≤ phi2 t ∧ (peval Hn t / Hd = phi2 t → peval F t = 0) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have ht1 : t < 1 := by
    have : (hi:ℝ) ≤ D := by exact_mod_cast hhi
    have : (D:ℝ) * t < D * 1 := by linarith
    exact lt_of_mul_lt_mul_left this hDR.le
  have hq := posChain_sound Qn D hD ps lo hi hch t h0 h1
  have hg := gap_eq Hn Hd F Qn Qd hHd hQd hid ht1
  have hQdR : (0:ℝ) < Qd := by exact_mod_cast hQd
  have h2 : (0:ℝ) < 2 - 2 * t := by linarith
  have hden : (0:ℝ) < Qd * (2 - 2 * t) := mul_pos hQdR h2
  constructor
  · have : 0 ≤ peval F t * peval Qn t / (Qd * (2 - 2 * t)) :=
      div_nonneg (mul_nonneg hF hq.le) hden.le
    linarith
  · intro heq
    have h0' : peval F t * peval Qn t / (Qd * (2 - 2 * t)) = 0 := by linarith
    rcases mul_eq_zero.mp (div_eq_zero_iff.mp h0' |>.resolve_right hden.ne') with h | h
    · exact h
    · exact absurd h hq.ne'

/-- **Plain class theorem** (`F = 1`): `H ≤ phi2` on `[lo/D, hi/D)`. -/
theorem class_le (Hn : List ℤ) (Hd : ℕ) (Qn : List ℤ) (Qd D : ℕ) (ps : List (ℤ × ℤ))
    (lo hi : ℤ) (hHd : 0 < Hd) (hQd : 0 < Qd) (hD : 0 < D) (hhi : hi ≤ D)
    (hid : gapId Hn Hd [1] Qn Qd = true) (hch : posChainOK Qn D ps lo hi = true)
    {t : ℝ} (h0 : (lo:ℝ) ≤ D * t) (h1 : (D:ℝ) * t < hi) :
    peval Hn t / Hd ≤ phi2 t :=
  (class_sharp Hn Hd [1] Qn Qd D ps lo hi hHd hQd hD hhi hid hch h0 h1
    (t := t) (by simp [peval])).1

/-- The class theorem on `[lo/D, 1)` (`hi = D`): the usual shape of the `B`/`C`/Case-1 minorants. -/
theorem class_le_one (Hn : List ℤ) (Hd : ℕ) (Qn : List ℤ) (Qd D : ℕ) (ps : List (ℤ × ℤ))
    (lo : ℤ) (hHd : 0 < Hd) (hQd : 0 < Qd) (hD : 0 < D)
    (hid : gapId Hn Hd [1] Qn Qd = true) (hch : posChainOK Qn D ps lo D = true)
    {t : ℝ} (h0 : (lo:ℝ) ≤ D * t) (h1 : t < 1) :
    peval Hn t / Hd ≤ phi2 t := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  exact class_le Hn Hd Qn Qd D ps lo D hHd hQd hD le_rfl hid hch (t := t) h0 (by push_cast; nlinarith)

/-- Evaluations of the contact factors. -/
theorem peval_FA (t : ℝ) : peval [1, 1] t = t + 1 := by
  simp only [peval]; push_cast; ring
theorem peval_FB (t : ℝ) : peval [0, 0, 0, 0, 1] t = t ^ 4 := by
  simp only [peval]; push_cast; ring
theorem peval_FC (t : ℝ) : peval [1, -4, -4, 16, 16] t = (4 * t ^ 2 + 2 * t - 1) ^ 2 := by
  simp only [peval]; push_cast; ring

/-- Cap class A on `[-1, hi/D)`: contact factor `t + 1`. -/
theorem capA_of (Hn : List ℤ) (Hd : ℕ) (Qn : List ℤ) (Qd D : ℕ) (ps : List (ℤ × ℤ)) (hi : ℤ)
    (hHd : 0 < Hd) (hQd : 0 < Qd) (hD : 0 < D) (hhi : hi ≤ D)
    (hid : gapId Hn Hd [1, 1] Qn Qd = true) (hch : posChainOK Qn D ps (-(D:ℤ)) hi = true)
    {t : ℝ} (h0 : -1 ≤ t) (h1 : (D:ℝ) * t < hi) :
    peval Hn t / Hd ≤ phi2 t ∧ (peval Hn t / Hd = phi2 t → t = -1) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have h := class_sharp Hn Hd [1, 1] Qn Qd D ps (-(D:ℤ)) hi hHd hQd hD hhi hid hch
    (t := t) (by push_cast; nlinarith) h1 (by rw [peval_FA]; linarith)
  refine ⟨h.1, fun he => ?_⟩
  have := h.2 he
  rw [peval_FA] at this
  linarith

/-- Cap class B on `[-1, 1)`: contact factor `t⁴`. -/
theorem capB_of (Hn : List ℤ) (Hd : ℕ) (Qn : List ℤ) (Qd D : ℕ) (ps : List (ℤ × ℤ))
    (hHd : 0 < Hd) (hQd : 0 < Qd) (hD : 0 < D)
    (hid : gapId Hn Hd [0, 0, 0, 0, 1] Qn Qd = true)
    (hch : posChainOK Qn D ps (-(D:ℤ)) D = true)
    {t : ℝ} (h0 : -1 ≤ t) (h1 : t < 1) :
    peval Hn t / Hd ≤ phi2 t ∧ (peval Hn t / Hd = phi2 t → t = 0) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have h := class_sharp Hn Hd [0, 0, 0, 0, 1] Qn Qd D ps (-(D:ℤ)) D hHd hQd hD le_rfl hid hch
    (t := t) (by push_cast; nlinarith) (by push_cast; nlinarith) (by rw [peval_FB]; positivity)
  refine ⟨h.1, fun he => ?_⟩
  have := h.2 he
  rw [peval_FB] at this
  exact pow_eq_zero_iff (by norm_num : (4:ℕ) ≠ 0) |>.mp this

/-- Cap class C on `[-1, 1)`: contact factor `(4t² + 2t - 1)²`. -/
theorem capC_of (Hn : List ℤ) (Hd : ℕ) (Qn : List ℤ) (Qd D : ℕ) (ps : List (ℤ × ℤ))
    (hHd : 0 < Hd) (hQd : 0 < Qd) (hD : 0 < D)
    (hid : gapId Hn Hd [1, -4, -4, 16, 16] Qn Qd = true)
    (hch : posChainOK Qn D ps (-(D:ℤ)) D = true)
    {t : ℝ} (h0 : -1 ≤ t) (h1 : t < 1) :
    peval Hn t / Hd ≤ phi2 t ∧ (peval Hn t / Hd = phi2 t → 4 * t ^ 2 + 2 * t - 1 = 0) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have h := class_sharp Hn Hd [1, -4, -4, 16, 16] Qn Qd D ps (-(D:ℤ)) D hHd hQd hD le_rfl hid hch
    (t := t) (by push_cast; nlinarith) (by push_cast; nlinarith) (by rw [peval_FC]; positivity)
  refine ⟨h.1, fun he => ?_⟩
  have := h.2 he
  rw [peval_FC] at this
  exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp this

end Riesz2.Minor
