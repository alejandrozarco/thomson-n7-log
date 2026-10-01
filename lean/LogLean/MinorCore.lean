/-
MinorCore.lean — generic 1-D minorant machinery for the log kernel.
  §1 odd-Taylor log lemma (copy of LogSeries.lean)       §2 log 2/3/5 enclosures (≤ 4·10⁻³⁰)
  §3 integer polynomials (upstream `CutOneD`/`Glue.Coerce`, regenerated: `ThomsonGen/Verbatim/LogMinor.lean`)
  §4 route C: kernel-computed Möbius/Bernstein coefficients   §5 log-Taylor minorant polynomial
  §6 φ and node constants   §7 pieces / chains / tail / class theorem   §8 route B (upstream BPiece)
Every piece check is a `Bool` closed by `decide +kernel`; no `native_decide`, no stored SOS data.
Assembled by lean/gen/assemble_core.py from gen/core_head.lean, LogSeries.lean and gen/core_tail.lean; the upstream
declarations of §3 and §8 were then replaced by the import of `ThomsonGen.Verbatim.LogMinor`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import ThomsonGen.Verbatim.LogMinor

open Finset

namespace LogLean.Minor

/-! ## 1. `Σ_{k≤n} u^k/k ≤ -log(1-u)` for odd `n`, `u < 1` (copy of `LogSeries.lean`) -/

noncomputable def logTaylor (n : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, u ^ (i + 1) / ((i : ℝ) + 1)

/-- `g(u) := -log(1-u) - S_n(u)`. -/
noncomputable def logGap (n : ℕ) (u : ℝ) : ℝ :=
  -Real.log (1 - u) - logTaylor n u

@[simp] theorem logGap_zero (n : ℕ) : logGap n 0 = 0 := by
  simp [logGap, logTaylor]

/-- The derivative of the finite Taylor sum: `S_n'(y) = ∑_{i<n} y^i`. -/
theorem hasDerivAt_logTaylor (n : ℕ) (y : ℝ) :
    HasDerivAt (logTaylor n) (∑ i ∈ Finset.range n, y ^ i) y := by
  have h : HasDerivAt (logTaylor n)
      (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * y ^ i / ((i : ℝ) + 1)) y := by
    unfold logTaylor
    refine HasDerivAt.fun_sum (fun i _ => ?_)
    have hd := (hasDerivAt_pow (i + 1) y).div_const ((i : ℝ) + 1)
    simpa [Nat.add_sub_cancel, Nat.cast_add_one] using hd
  refine h.congr_deriv (Finset.sum_congr rfl (fun i _ => ?_))
  have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- The derivative of `g` at any point `y ≠ 1`: `g'(y) = y^n / (1-y)`. -/
theorem hasDerivAt_logGap (n : ℕ) {y : ℝ} (hy : y ≠ 1) :
    HasDerivAt (logGap n) (y ^ n / (1 - y)) y := by
  have hne : (1 : ℝ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have h1 : HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (1 / (1 - y)) y := by
    have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1 : ℝ) / (1 - y)) y :=
      ((hasDerivAt_id y).const_sub (1 : ℝ)).log hne
    have hneg := hlog.fun_neg
    simpa [neg_div] using hneg
  have h2 := hasDerivAt_logTaylor n y
  have hsum : HasDerivAt (fun x => -Real.log (1 - x) - logTaylor n x)
      (1 / (1 - y) - ∑ i ∈ Finset.range n, y ^ i) y := h1.fun_sub h2
  show HasDerivAt (fun x => -Real.log (1 - x) - logTaylor n x) (y ^ n / (1 - y)) y
  refine hsum.congr_deriv ?_
  have hgeo : ∑ i ∈ Finset.range n, y ^ i = (y ^ n - 1) / (y - 1) := geom_sum_eq hy n
  rw [hgeo]
  field_simp
  ring

/-- **Key lemma**: for odd `n` and every real `u < 1`,
`∑_{k=1}^{n} u^k/k ≤ -log(1-u)`. -/
theorem sum_le_neg_log_one_sub {n : ℕ} (hn : Odd n) {u : ℝ} (hu : u < 1) :
    logTaylor n u ≤ -Real.log (1 - u) := by
  suffices h0 : 0 ≤ logGap n u by
    have heq : logTaylor n u + logGap n u = -Real.log (1 - u) := by unfold logGap; ring
    linarith
  by_cases hupos : 0 ≤ u
  · -- monotone increasing on [0,1)
    have hderiv : ∀ x ∈ interior (Set.Ico (0:ℝ) 1),
        HasDerivWithinAt (logGap n) (x ^ n / (1 - x)) (interior (Set.Ico (0:ℝ) 1)) x := by
      intro x hx
      rw [interior_Ico] at hx
      have hx2 : x < 1 := (Set.mem_Ioo.mp hx).2
      exact (hasDerivAt_logGap n (ne_of_lt hx2)).hasDerivWithinAt
    have hcont : ContinuousOn (logGap n) (Set.Ico (0:ℝ) 1) := by
      have h1 : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (Set.Ico (0:ℝ) 1) :=
        ((continuousOn_const.sub continuousOn_id).log
          (fun x hx => sub_ne_zero.mpr (fun h => by
            have hx2 : x < 1 := (Set.mem_Ico.mp hx).2
            have h' : (1:ℝ) = x := h
            linarith [h'.symm]))).neg
      have h2 : ContinuousOn (logTaylor n) (Set.Ico (0:ℝ) 1) := by
        unfold logTaylor
        exact continuousOn_finsetSum _ (fun i _ => (continuousOn_pow (i + 1)).div_const _)
      unfold logGap
      exact h1.sub h2
    have hnonneg : ∀ x ∈ interior (Set.Ico (0:ℝ) 1), 0 ≤ x ^ n / (1 - x) := by
      intro x hx
      rw [interior_Ico] at hx
      obtain ⟨hx1, hx2⟩ := Set.mem_Ioo.mp hx
      exact div_nonneg (pow_nonneg hx1.le n) (by linarith)
    have hmono : MonotoneOn (logGap n) (Set.Ico (0:ℝ) 1) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) hcont hderiv hnonneg
    have h0mem : (0:ℝ) ∈ Set.Ico (0:ℝ) 1 := Set.mem_Ico.mpr ⟨le_refl 0, one_pos⟩
    have humem : u ∈ Set.Ico (0:ℝ) 1 := Set.mem_Ico.mpr ⟨hupos, hu⟩
    have hle := hmono h0mem humem hupos
    simpa using hle
  · -- antitone (decreasing) on (-∞,0]
    push Not at hupos
    have hderiv : ∀ x ∈ interior (Set.Iic (0:ℝ)),
        HasDerivWithinAt (logGap n) (x ^ n / (1 - x)) (interior (Set.Iic (0:ℝ))) x := by
      intro x hx
      rw [interior_Iic] at hx
      have hx0 : x < 0 := Set.mem_Iio.mp hx
      exact (hasDerivAt_logGap n (by intro h; rw [h] at hx0; exact absurd hx0 (by norm_num))).hasDerivWithinAt
    have hcont : ContinuousOn (logGap n) (Set.Iic (0:ℝ)) := by
      have h1 : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (Set.Iic (0:ℝ)) :=
        ((continuousOn_const.sub continuousOn_id).log
          (fun x hx => sub_ne_zero.mpr (fun h => by
            have hx0 : x ≤ 0 := Set.mem_Iic.mp hx
            have h' : (1:ℝ) = x := h
            linarith [h'.symm]))).neg
      have h2 : ContinuousOn (logTaylor n) (Set.Iic (0:ℝ)) := by
        unfold logTaylor
        exact continuousOn_finsetSum _ (fun i _ => (continuousOn_pow (i + 1)).div_const _)
      unfold logGap
      exact h1.sub h2
    have hnonpos : ∀ x ∈ interior (Set.Iic (0:ℝ)), x ^ n / (1 - x) ≤ 0 := by
      intro x hx
      rw [interior_Iic] at hx
      have hx0 : x < 0 := Set.mem_Iio.mp hx
      exact div_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos hn hx0.le) (by linarith)
    have hanti : AntitoneOn (logGap n) (Set.Iic (0:ℝ)) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0) hcont hderiv hnonpos
    have h0mem : (0:ℝ) ∈ Set.Iic (0:ℝ) := Set.mem_Iic.mpr (le_refl 0)
    have humem : u ∈ Set.Iic (0:ℝ) := Set.mem_Iic.mpr hupos.le
    have hge := hanti humem h0mem hupos.le
    simpa using hge


/-! ## 2. Short rational enclosures of log 2, log 3, log 5 (denominator 10³², width 2·10⁻³⁰) -/

/-- common denominator of the log enclosures -/
def DEN : ℕ := 10 ^ 32
def l2 : ℤ := 69314718055994530941723212145717
def h2 : ℤ := 69314718055994530941723212145917
def l3 : ℤ := 109861228866810969139524523691952
def h3 : ℤ := 109861228866810969139524523692552
def l5 : ℤ := 160943791243410037460075933322218
def h5 : ℤ := 160943791243410037460075933323018

theorem log2_enc : (l2 : ℝ) / DEN ≤ Real.log 2 ∧ Real.log 2 ≤ (h2 : ℝ) / DEN := by
  have hx0 : (0:ℝ) ≤ 1 / 3 := by norm_num
  have hx1 : (1:ℝ) / 3 < 1 := by norm_num
  have hlo := Real.sum_range_le_log_div hx0 hx1 32
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 32
  have harg : ((1:ℝ) + 1 / 3) / (1 - 1 / 3) = 2 := by norm_num
  rw [harg] at hlo hhi
  have e1 : (l2 : ℝ) / DEN ≤ 2 * ∑ i ∈ Finset.range 32, ((1:ℝ)/3) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) := by
    norm_num [Finset.sum_range_succ, l2, DEN]
  have e2 : 2 * ((∑ i ∈ Finset.range 32, ((1:ℝ)/3) ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) +
      ((1:ℝ)/3) ^ (2 * 32 + 1) / (1 - ((1:ℝ)/3) ^ 2)) ≤ (h2 : ℝ) / DEN := by
    norm_num [Finset.sum_range_succ, h2, DEN]
  constructor <;> linarith

theorem log32_enc :
    (l3 - l2 : ℝ) / DEN ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ (h3 - h2 : ℝ) / DEN := by
  have hx0 : (0:ℝ) ≤ 1 / 5 := by norm_num
  have hx1 : (1:ℝ) / 5 < 1 := by norm_num
  have hlo := Real.sum_range_le_log_div hx0 hx1 22
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 22
  have harg : ((1:ℝ) + 1 / 5) / (1 - 1 / 5) = 3 / 2 := by norm_num
  rw [harg] at hlo hhi
  have e1 : (l3 - l2 : ℝ) / DEN ≤ 2 * ∑ i ∈ Finset.range 22, ((1:ℝ)/5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) := by
    norm_num [Finset.sum_range_succ, l3, l2, DEN]
  have e2 : 2 * ((∑ i ∈ Finset.range 22, ((1:ℝ)/5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) +
      ((1:ℝ)/5) ^ (2 * 22 + 1) / (1 - ((1:ℝ)/5) ^ 2)) ≤ (h3 - h2 : ℝ) / DEN := by
    norm_num [Finset.sum_range_succ, h3, h2, DEN]
  constructor <;> linarith

theorem log54_enc :
    (l5 - 2 * l2 : ℝ) / DEN ≤ Real.log (5 / 4) ∧ Real.log (5 / 4) ≤ (h5 - 2 * h2 : ℝ) / DEN := by
  have hx0 : (0:ℝ) ≤ 1 / 9 := by norm_num
  have hx1 : (1:ℝ) / 9 < 1 := by norm_num
  have hlo := Real.sum_range_le_log_div hx0 hx1 16
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 16
  have harg : ((1:ℝ) + 1 / 9) / (1 - 1 / 9) = 5 / 4 := by norm_num
  rw [harg] at hlo hhi
  have e1 : (l5 - 2 * l2 : ℝ) / DEN ≤ 2 * ∑ i ∈ Finset.range 16, ((1:ℝ)/9) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) := by
    norm_num [Finset.sum_range_succ, l5, l2, DEN]
  have e2 : 2 * ((∑ i ∈ Finset.range 16, ((1:ℝ)/9) ^ (2 * i + 1) / (2 * (i:ℝ) + 1)) +
      ((1:ℝ)/9) ^ (2 * 16 + 1) / (1 - ((1:ℝ)/9) ^ 2)) ≤ (h5 - 2 * h2 : ℝ) / DEN := by
    norm_num [Finset.sum_range_succ, h5, h2, DEN]
  constructor <;> linarith

theorem log3_enc : (l3 : ℝ) / DEN ≤ Real.log 3 ∧ Real.log 3 ≤ (h3 : ℝ) / DEN := by
  have e : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a, b⟩ := log2_enc
  obtain ⟨c, d⟩ := log32_enc
  have hD : (0:ℝ) < DEN := by unfold DEN; positivity
  rw [e]
  constructor
  · have : (l3 : ℝ) / DEN = (l2 : ℝ) / DEN + (l3 - l2 : ℝ) / DEN := by ring
    linarith
  · have : (h3 : ℝ) / DEN = (h2 : ℝ) / DEN + (h3 - h2 : ℝ) / DEN := by ring
    linarith

theorem log5_enc : (l5 : ℝ) / DEN ≤ Real.log 5 ∧ Real.log 5 ≤ (h5 : ℝ) / DEN := by
  have e : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [← h4, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  obtain ⟨a, b⟩ := log2_enc
  obtain ⟨c, d⟩ := log54_enc
  rw [e]
  constructor
  · have : (l5 : ℝ) / DEN = 2 * ((l2 : ℝ) / DEN) + (l5 - 2 * l2 : ℝ) / DEN := by ring
    linarith
  · have : (h5 : ℝ) / DEN = 2 * ((h2 : ℝ) / DEN) + (h5 - 2 * h2 : ℝ) / DEN := by ring
    linarith

/-! ## 3. Integer polynomials
`peval`, `padd`, `pscale`, `pneg`, `pmul`, `ppow`, their `peval_*` lemmas and `peval_eq_zero_of_all` are upstream
declarations (huwngtran/thomson-n7-lean @ 25f2fa5, `CutOneD` and `Glue.Coerce`) used unchanged; they are
regenerated into `ThomsonGen/Verbatim/LogMinor.lean` by `regen.sh` and imported above.
`peval_nonneg_of_all` below follows the induction of upstream `CutOneD.peval_eq_zero_of_all`. -/

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

/-! ## 4. Route C: Möbius (Bernstein) coefficients computed in the kernel

`homog T E q m = Σ_j q_j T^j E^(m-j)`.  With `T = A + B x`, `E = D (1 + x)`, the substitution
`t = (A + B x)/(D (1 + x))` maps `x ∈ [0, ∞)` onto `t ∈ [A/D, B/D)`, and
`homog T E q m = E^m · q(t)`; its coefficients are (scaled) Bernstein coefficients of `q` on
`[A/D, B/D]`.  All of them `≥ 0` ⇒ `q ≥ 0` on `[A/D, B/D)`.  No certificate data is stored. -/

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

/-- **Möbius positivity.** -/
theorem mob_sound (q : List ℤ) (A B : ℤ) (D : ℕ) (hD : 0 < D)
    (hchk : (homog [A, B] [(D:ℤ), (D:ℤ)] q (q.length - 1)).all (fun c => decide (0 ≤ c)) = true)
    {t : ℝ} (ht0 : (A:ℝ) ≤ D * t) (ht1 : (D:ℝ) * t < B) : 0 ≤ peval q t := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hden : 0 < (B:ℝ) - D * t := by linarith
  have hden' : (B:ℝ) - D * t ≠ 0 := hden.ne'
  set x : ℝ := ((D:ℝ) * t - A) / (B - D * t) with hxdef
  have hx : 0 ≤ x := div_nonneg (by linarith) hden.le
  have hE : peval [(D:ℤ), (D:ℤ)] x = D * (1 + x) := by
    simp only [peval, mul_zero, add_zero]; push_cast; ring
  have hT : peval [A, B] x = A + B * x := by
    simp only [peval, mul_zero, add_zero]; ring
  have hEpos : 0 < peval [(D:ℤ), (D:ℤ)] x := by rw [hE]; exact mul_pos hDR (by linarith)
  have hratio : peval [A, B] x / peval [(D:ℤ), (D:ℤ)] x = t := by
    rw [hE, hT, div_eq_iff (mul_pos hDR (by linarith)).ne', hxdef]
    field_simp
    ring
  have key := peval_homog [A, B] [(D:ℤ), (D:ℤ)] x hEpos.ne' q (q.length - 1) (by omega)
  rw [hratio] at key
  have h1 := peval_nonneg_of_all _ hchk hx
  rw [key] at h1
  exact (mul_nonneg_iff_of_pos_left (pow_pos hEpos _)).mp h1

/-! ## 5. The log-Taylor minorant polynomial -/

/-- `Σ_{k=1}^{n} (L/k) a^k R^(n-k)`. -/
def taylorPoly (a : List ℤ) (R L : ℤ) : ℕ → List ℤ
  | 0 => []
  | k + 1 => padd (pscale R (taylorPoly a R L k)) (pscale (L / ((k:ℤ) + 1)) (ppow a (k + 1)))

theorem peval_taylorPoly (a : List ℤ) (R L : ℤ) (hR : (R:ℝ) ≠ 0) (x : ℝ) (n : ℕ)
    (hL : ∀ k, k < n → ((k:ℤ) + 1) ∣ L) :
    peval (taylorPoly a R L n) x = L * R ^ n * logTaylor n (peval a x / R) := by
  induction n with
  | zero => simp [taylorPoly, peval, logTaylor]
  | succ k ih =>
    have hk : ((k:ℤ) + 1) ∣ L := hL k (by omega)
    have ih' := ih (fun j hj => hL j (by omega))
    have hs : logTaylor (k + 1) (peval a x / R) =
        logTaylor k (peval a x / R) + (peval a x / R) ^ (k + 1) / ((k:ℝ) + 1) := by
      simp only [logTaylor, Finset.sum_range_succ]
    simp only [taylorPoly, peval_padd, peval_pscale, peval_ppow, ih', hs]
    rw [Int.cast_div hk (by push_cast; positivity)]
    push_cast
    have hk1 : ((k:ℝ) + 1) ≠ 0 := by positivity
    rw [div_pow]
    field_simp
    ring

/-- `2 Ln Hd L R^n + Ld Hd Σ_k (L/k)(gd t - gn)^k R^(n-k) - 2 Ld L R^n Hn(t)` with `R = gd - gn`,
`L = n!`; equals `2 Ld Hd L R^n · (Ln/Ld + ½ T_n((t-g)/(1-g)) - Hn(t)/Hd)`, `g = gn/gd`. -/
def minorPoly (Hn : List ℤ) (Hd : ℕ) (gn : ℤ) (gd : ℕ) (Ln : ℤ) (Ld : ℕ) (n : ℕ) : List ℤ :=
  padd (padd [2 * Ln * (Hd:ℤ) * (n.factorial : ℤ) * ((gd:ℤ) - gn) ^ n]
      (pscale ((Ld:ℤ) * Hd) (taylorPoly [-gn, (gd:ℤ)] ((gd:ℤ) - gn) (n.factorial : ℤ) n)))
    (pscale (-(2 * (Ld:ℤ) * (n.factorial : ℤ) * ((gd:ℤ) - gn) ^ n)) Hn)

theorem minor_sound (Hn : List ℤ) (Hd : ℕ) (gn : ℤ) (gd : ℕ) (Ln : ℤ) (Ld : ℕ) (n : ℕ)
    (hHd : 0 < Hd) (hLd : 0 < Ld) (hg : gn < gd) {t : ℝ}
    (h : 0 ≤ peval (minorPoly Hn Hd gn gd Ln Ld n) t) :
    peval Hn t / Hd ≤ (Ln:ℝ) / Ld + 1 / 2 * logTaylor n ((gd * t - gn) / (gd - gn)) := by
  have hR : (0:ℝ) < (gd:ℝ) - gn := by
    have : ((gn:ℤ):ℝ) < ((gd:ℤ):ℝ) := by exact_mod_cast hg
    push_cast at this; linarith
  have hdvd : ∀ k, k < n → ((k:ℤ) + 1) ∣ (n.factorial : ℤ) := by
    intro k hk
    have := Nat.dvd_factorial (Nat.succ_pos k) (show k + 1 ≤ n by omega)
    exact_mod_cast Int.natCast_dvd_natCast.mpr this
  have hRne : (((gd:ℤ) - gn : ℤ) : ℝ) ≠ 0 := by push_cast; linarith
  have e := peval_taylorPoly [-gn, (gd:ℤ)] ((gd:ℤ) - gn) (n.factorial : ℤ) hRne t n hdvd
  have hlin : peval [-gn, (gd:ℤ)] t = (gd:ℝ) * t - gn := by
    simp only [peval, mul_zero, add_zero]; push_cast; ring
  have hRc : ((((gd:ℤ) - gn : ℤ)) : ℝ) = (gd:ℝ) - gn := by push_cast; ring
  rw [hlin, hRc] at e
  simp only [minorPoly, peval_padd, peval_pscale, e, peval, mul_zero, add_zero] at h
  push_cast at h
  have hHdR : (0:ℝ) < Hd := by exact_mod_cast hHd
  have hLdR : (0:ℝ) < Ld := by exact_mod_cast hLd
  have hHd0 : (Hd:ℝ) ≠ 0 := hHdR.ne'
  have hLd0 : (Ld:ℝ) ≠ 0 := hLdR.ne'
  have hF : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hK : (0:ℝ) < 2 * Ld * Hd * (n.factorial : ℝ) * ((gd:ℝ) - gn) ^ n := by positivity
  set T := logTaylor n (((gd:ℝ) * t - gn) / ((gd:ℝ) - gn))
  set P := peval Hn t
  have key : 0 ≤ (2 * Ld * Hd * (n.factorial : ℝ) * ((gd:ℝ) - gn) ^ n) *
      ((Ln:ℝ) / Ld + 1 / 2 * T - P / Hd) := by
    have : (2 * Ld * Hd * (n.factorial : ℝ) * ((gd:ℝ) - gn) ^ n) *
        ((Ln:ℝ) / Ld + 1 / 2 * T - P / Hd) =
        2 * Ln * Hd * (n.factorial : ℝ) * ((gd:ℝ) - gn) ^ n +
          Ld * Hd * ((n.factorial : ℝ) * ((gd:ℝ) - gn) ^ n * T) +
          -(2 * Ld * (n.factorial : ℝ) * ((gd:ℝ) - gn) ^ n) * P := by
      field_simp
      ring
    rw [this]; linarith
  have := (mul_nonneg_iff_of_pos_left hK).mp key
  linarith

/-! ## 6. The potential, node constants -/

/-- log pair potential `φ(t) = -½ log(2 - 2t)`. -/
noncomputable def phi (t : ℝ) : ℝ := -(1 / 2) * Real.log (2 - 2 * t)

/-- Taylor lower bound at a rational node `g = gn/gd < 1` (odd `n`, any `t < 1`). -/
theorem phi_ge_node {gn : ℤ} {gd : ℕ} (hgd : 0 < gd) (hg : gn < gd) {n : ℕ} (hn : Odd n) {t : ℝ}
    (ht : t < 1) :
    -(1 / 2) * Real.log (2 * (((gd:ℝ) - gn) / gd)) +
      1 / 2 * logTaylor n ((gd * t - gn) / (gd - gn)) ≤ phi t := by
  have hgdR : (0:ℝ) < gd := by exact_mod_cast hgd
  have hR : (0:ℝ) < (gd:ℝ) - gn := by
    have : ((gn:ℤ):ℝ) < ((gd:ℤ):ℝ) := by exact_mod_cast hg
    push_cast at this; linarith
  set u := ((gd:ℝ) * t - gn) / ((gd:ℝ) - gn) with hu
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hR]; nlinarith
  have hgd0 : (gd:ℝ) ≠ 0 := hgdR.ne'
  have hR0 : (gd:ℝ) - gn ≠ 0 := hR.ne'
  have hsplit : (2:ℝ) - 2 * t = 2 * (((gd:ℝ) - gn) / gd) * (1 - u) := by
    rw [hu]; field_simp; ring
  have h2r : (0:ℝ) < 2 * (((gd:ℝ) - gn) / gd) := by positivity
  have h1u : (0:ℝ) < 1 - u := by linarith
  have hlog : Real.log (2 - 2 * t) = Real.log (2 * (((gd:ℝ) - gn) / gd)) + Real.log (1 - u) := by
    rw [hsplit, Real.log_mul h2r.ne' h1u.ne']
  have hser := sum_le_neg_log_one_sub hn hu1
  unfold phi
  rw [hlog]
  linarith

/-- Node check: `2(1-g) = 2^a2 3^a3 5^a5 / (2^b2 3^b3 5^b5)` and
`2·DEN·Ln ≤ -Ld·(a2 h2 + a3 h3 + a5 h5 - b2 l2 - b3 l3 - b5 l5)`. -/
def nodeOK (gn : ℤ) (gd a2 a3 a5 b2 b3 b5 : ℕ) (Ln : ℤ) (Ld : ℕ) : Bool :=
  decide (2 * ((gd:ℤ) - gn) * (2 ^ b2 * 3 ^ b3 * 5 ^ b5) = (gd:ℤ) * (2 ^ a2 * 3 ^ a3 * 5 ^ a5)) &&
  decide (2 * (DEN:ℤ) * Ln ≤
    -((Ld:ℤ) * (a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5)))

theorem log_smooth (a2 a3 a5 : ℕ) :
    Real.log ((2:ℝ) ^ a2 * 3 ^ a3 * 5 ^ a5) = a2 * Real.log 2 + a3 * Real.log 3 + a5 * Real.log 5 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]

theorem Lnode_le {gn : ℤ} {gd a2 a3 a5 b2 b3 b5 : ℕ} {Ln : ℤ} {Ld : ℕ}
    (h : nodeOK gn gd a2 a3 a5 b2 b3 b5 Ln Ld = true) (hgd : 0 < gd) (hLd : 0 < Ld) :
    (Ln:ℝ) / Ld ≤ -(1 / 2) * Real.log (2 * (((gd:ℝ) - gn) / gd)) := by
  simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2'⟩ := h
  have hgdR : (0:ℝ) < gd := by exact_mod_cast hgd
  have hLdR : (0:ℝ) < Ld := by exact_mod_cast hLd
  have h1R : (2:ℝ) * ((gd:ℝ) - gn) * (2 ^ b2 * 3 ^ b3 * 5 ^ b5) =
      (gd:ℝ) * (2 ^ a2 * 3 ^ a3 * 5 ^ a5) := by exact_mod_cast h1
  have hden : (0:ℝ) < 2 ^ b2 * 3 ^ b3 * 5 ^ b5 := by positivity
  have hnum : (0:ℝ) < 2 ^ a2 * 3 ^ a3 * 5 ^ a5 := by positivity
  have e1 : 2 * (((gd:ℝ) - gn) / gd) = (2 ^ a2 * 3 ^ a3 * 5 ^ a5) / (2 ^ b2 * 3 ^ b3 * 5 ^ b5) := by
    rw [eq_div_iff hden.ne']
    field_simp
    linear_combination h1R
  rw [e1, Real.log_div hnum.ne' hden.ne', log_smooth, log_smooth]
  obtain ⟨a, b⟩ := log2_enc
  obtain ⟨c, d⟩ := log3_enc
  obtain ⟨e, f⟩ := log5_enc
  have hDEN : (0:ℝ) < DEN := by unfold DEN; positivity
  have h2R : 2 * (DEN:ℝ) * Ln ≤ -((Ld:ℝ) * (a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5)) := by
    exact_mod_cast h2'
  have hub : (a2:ℝ) * Real.log 2 + a3 * Real.log 3 + a5 * Real.log 5 -
      (b2 * Real.log 2 + b3 * Real.log 3 + b5 * Real.log 5) ≤
      (a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5 : ℝ) / DEN := by
    have p1 := mul_le_mul_of_nonneg_left b (Nat.cast_nonneg a2 : (0:ℝ) ≤ a2)
    have p2 := mul_le_mul_of_nonneg_left d (Nat.cast_nonneg a3 : (0:ℝ) ≤ a3)
    have p3 := mul_le_mul_of_nonneg_left f (Nat.cast_nonneg a5 : (0:ℝ) ≤ a5)
    have q1 := mul_le_mul_of_nonneg_left a (Nat.cast_nonneg b2 : (0:ℝ) ≤ b2)
    have q2 := mul_le_mul_of_nonneg_left c (Nat.cast_nonneg b3 : (0:ℝ) ≤ b3)
    have q3 := mul_le_mul_of_nonneg_left e (Nat.cast_nonneg b5 : (0:ℝ) ≤ b5)
    have : (a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5 : ℝ) / DEN =
        a2 * ((h2:ℝ) / DEN) + a3 * ((h3:ℝ) / DEN) + a5 * ((h5:ℝ) / DEN) -
        (b2 * ((l2:ℝ) / DEN) + b3 * ((l3:ℝ) / DEN) + b5 * ((l5:ℝ) / DEN)) := by ring
    rw [this]; linarith
  set X : ℝ := (a2 * h2 + a3 * h3 + a5 * h5 - b2 * l2 - b3 * l3 - b5 * l5 : ℝ)
  have hL : (Ln:ℝ) / Ld ≤ -X / (2 * DEN) := by
    rw [div_le_div_iff₀ hLdR (by positivity)]; linarith
  have : -X / (2 * DEN) = -(1 / 2) * (X / DEN) := by ring
  linarith

/-! ## 7. Pieces, chains, tail, class theorem (route C) -/

/-- A piece `[A/D, B/D)` with node `g = gn/gd` (`2(1-g) = 2^a·3^·5^ / 2^b·3^·5^`), order `n`, and
node constant `Ln/Ld ≤ φ(g)`. `D` is shared by the chain. -/
structure Piece where
  A : ℤ
  B : ℤ
  gn : ℤ
  gd : ℕ
  n : ℕ
  a2 : ℕ
  a3 : ℕ
  a5 : ℕ
  b2 : ℕ
  b3 : ℕ
  b5 : ℕ
  Ln : ℤ
  Ld : ℕ

def Piece.check (Hn : List ℤ) (Hd D : ℕ) (p : Piece) : Bool :=
  decide (0 < p.gd) && decide (p.gn < p.gd) && decide (0 < p.Ld) && p.n % 2 == 1 &&
  decide (p.B ≤ D) &&
  nodeOK p.gn p.gd p.a2 p.a3 p.a5 p.b2 p.b3 p.b5 p.Ln p.Ld &&
  (let q := minorPoly Hn Hd p.gn p.gd p.Ln p.Ld p.n
   (homog [p.A, p.B] [(D:ℤ), (D:ℤ)] q (q.length - 1)).all (fun c => decide (0 ≤ c)))

theorem Piece.sound (Hn : List ℤ) (Hd D : ℕ) (hHd : 0 < Hd) (hD : 0 < D) (p : Piece)
    (hc : p.check Hn Hd D = true) {t : ℝ} (h0 : (p.A:ℝ) ≤ D * t) (h1 : (D:ℝ) * t < p.B) :
    peval Hn t / Hd ≤ phi t := by
  simp only [Piece.check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hgd, hg⟩, hLd⟩, hn⟩, hBD⟩, hnode⟩, hmob⟩ := hc
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have ht1 : t < 1 := by
    have : (p.B:ℝ) ≤ D := by exact_mod_cast hBD
    have : (D:ℝ) * t < D * 1 := by linarith
    exact lt_of_mul_lt_mul_left this hDR.le
  have hq := mob_sound _ p.A p.B D hD hmob h0 h1
  have hodd : Odd p.n := Nat.odd_iff.mpr hn
  have s1 := minor_sound Hn Hd p.gn p.gd p.Ln p.Ld p.n hHd hLd hg hq
  have s2 := phi_ge_node hgd hg hodd ht1
  have s3 := Lnode_le hnode hgd hLd
  linarith

/-- Chain covering `[l/D, r/D)`. -/
def chainOK (Hn : List ℤ) (Hd D : ℕ) : List Piece → ℤ → ℤ → Bool
  | [], l, r => decide (r ≤ l)
  | p :: ps, l, r => p.check Hn Hd D && decide (p.A ≤ l) && chainOK Hn Hd D ps p.B r

theorem chain_sound (Hn : List ℤ) (Hd D : ℕ) (hHd : 0 < Hd) (hD : 0 < D) (ps : List Piece) :
    ∀ l r : ℤ, chainOK Hn Hd D ps l r = true →
      ∀ t : ℝ, (l:ℝ) ≤ D * t → (D:ℝ) * t < r → peval Hn t / Hd ≤ phi t := by
  induction ps with
  | nil =>
    intro l r h t h0 h1
    simp only [chainOK, decide_eq_true_eq] at h
    have : (r:ℝ) ≤ l := by exact_mod_cast h
    linarith
  | cons p ps ih =>
    intro l r h t h0 h1
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hA⟩, hrest⟩ := h
    by_cases hb : (D:ℝ) * t < p.B
    · have hAR : (p.A:ℝ) ≤ l := by exact_mod_cast hA
      exact Piece.sound Hn Hd D hHd hD p hc (by linarith) hb
    · exact ih p.B r hrest t (by linarith) h1

/-- Tail `[T0/D, 1)`: `φ` is increasing, `φ(T0/D) ≥ Ln/Ld ≥ H` there. -/
structure Tail where
  T0 : ℤ
  a2 : ℕ
  a3 : ℕ
  a5 : ℕ
  b2 : ℕ
  b3 : ℕ
  b5 : ℕ
  Ln : ℤ
  Ld : ℕ

def Tail.check (Hn : List ℤ) (Hd D : ℕ) (c : Tail) : Bool :=
  decide (c.T0 < D) && decide (0 < c.Ld) &&
  nodeOK c.T0 D c.a2 c.a3 c.a5 c.b2 c.b3 c.b5 c.Ln c.Ld &&
  (let q := padd [(Hd:ℤ) * c.Ln] (pscale (-(c.Ld:ℤ)) Hn)
   (homog [c.T0, (D:ℤ)] [(D:ℤ), (D:ℤ)] q (q.length - 1)).all (fun c => decide (0 ≤ c)))

theorem phi_mono {s t : ℝ} (hst : s ≤ t) (ht : t < 1) : phi s ≤ phi t := by
  unfold phi
  have : Real.log (2 - 2 * t) ≤ Real.log (2 - 2 * s) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

theorem Tail.sound (Hn : List ℤ) (Hd D : ℕ) (hHd : 0 < Hd) (hD : 0 < D) (c : Tail)
    (hc : c.check Hn Hd D = true) {t : ℝ} (h0 : (c.T0:ℝ) ≤ D * t) (h1 : t < 1) :
    peval Hn t / Hd ≤ phi t := by
  simp only [Tail.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hT, hLd⟩, hnode⟩, hmob⟩ := hc
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hHdR : (0:ℝ) < Hd := by exact_mod_cast hHd
  have hLdR : (0:ℝ) < c.Ld := by exact_mod_cast hLd
  have hq := mob_sound _ c.T0 (D:ℤ) D hD hmob h0 (by push_cast; nlinarith)
  simp only [peval_padd, peval_pscale, peval, mul_zero, add_zero] at hq
  push_cast at hq
  -- Hd·Ln - Ld·H(t) ≥ 0
  have hH : peval Hn t / Hd ≤ (c.Ln:ℝ) / c.Ld := by
    rw [div_le_div_iff₀ hHdR hLdR]; nlinarith
  have s3 := Lnode_le hnode hD hLd
  -- φ(T0/D) = -½ log(2(D - T0)/D)
  have hT0 : (c.T0:ℝ) / D ≤ t := by rw [div_le_iff₀ hDR]; linarith
  have hm := phi_mono hT0 h1
  have hphi : phi ((c.T0:ℝ) / D) = -(1 / 2) * Real.log (2 * (((D:ℝ) - c.T0) / D)) := by
    unfold phi
    rw [show (2:ℝ) - 2 * ((c.T0:ℝ) / D) = 2 * (((D:ℝ) - c.T0) / D) by field_simp]
  linarith

/-- **Class theorem**: chain on `[lo/D, T0/D)` + tail ⇒ `H ≤ φ` on `[lo/D, 1)`. -/
theorem class_sound (Hn : List ℤ) (Hd D : ℕ) (hHd : 0 < Hd) (hD : 0 < D) (ps : List Piece)
    (tl : Tail) (lo : ℤ) (hch : chainOK Hn Hd D ps lo tl.T0 = true) (htl : tl.check Hn Hd D = true)
    {t : ℝ} (h0 : (lo:ℝ) ≤ D * t) (h1 : t < 1) : peval Hn t / Hd ≤ phi t := by
  by_cases h : (D:ℝ) * t < tl.T0
  · exact chain_sound Hn Hd D hHd hD ps lo tl.T0 hch t h0 h
  · exact Tail.sound Hn Hd D hHd hD tl htl (by linarith) h1

/-! ## 8. Route B: upstream-style stored Bernstein coefficients (`BPiece`, from upstream
`Asm_Coerce` §A, huwngtran/thomson-n7-lean @ 25f2fa5), applied to the kernel-computed `minorPoly`. -/

-- `bernSum`, `bernSum_nonneg`, `BPiece`, `BPiece.diff`, `BPiece.check` and `BPiece.nonneg` are upstream
-- declarations (huwngtran/thomson-n7-lean @ 25f2fa5, `Glue.Coerce`), regenerated into `ThomsonGen/Verbatim/LogMinor.lean`.

/-- Route-B piece: the node data of a `Piece` plus stored Bernstein data `(Lam, β)` on `[A/D, B/D]`. -/
def Piece.checkB (Hn : List ℤ) (Hd D : ℕ) (p : Piece) (Lam : ℕ) (β : List ℕ) : Bool :=
  decide (0 < p.gd) && decide (p.gn < p.gd) && decide (0 < p.Ld) && p.n % 2 == 1 &&
  decide (p.B < D) &&
  nodeOK p.gn p.gd p.a2 p.a3 p.a5 p.b2 p.b3 p.b5 p.Ln p.Ld &&
  BPiece.check (minorPoly Hn Hd p.gn p.gd p.Ln p.Ld p.n) ⟨p.A, D, p.B, D, Lam, β⟩

theorem Piece.soundB (Hn : List ℤ) (Hd D : ℕ) (hHd : 0 < Hd) (hD : 0 < D) (p : Piece) (Lam : ℕ)
    (β : List ℕ) (hc : p.checkB Hn Hd D Lam β = true) {t : ℝ} (h0 : (p.A:ℝ) ≤ D * t)
    (h1 : (D:ℝ) * t ≤ p.B) : peval Hn t / Hd ≤ phi t := by
  simp only [Piece.checkB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hgd, hg⟩, hLd⟩, hn⟩, hBD⟩, hnode⟩, hb⟩ := hc
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have ht1 : t < 1 := by
    have : (p.B:ℝ) < D := by exact_mod_cast hBD
    have : (D:ℝ) * t < D * 1 := by linarith
    exact lt_of_mul_lt_mul_left this hDR.le
  have hq := BPiece.nonneg _ _ hb (y := t) (by simpa using h0) (by simpa using h1)
  have hodd : Odd p.n := Nat.odd_iff.mpr hn
  have s1 := minor_sound Hn Hd p.gn p.gd p.Ln p.Ld p.n hHd hLd hg hq
  have s2 := phi_ge_node hgd hg hodd ht1
  have s3 := Lnode_le hnode hgd hLd
  linarith

/-! ## 9. Slack polynomials, external node constants, coercivity (cap contacts) -/

/-- `m·Hn + Kn`, read over the denominator `Hd·m`: the polynomial `H + K`. -/
def addSlack (Hn : List ℤ) (m : ℕ) (Kn : List ℤ) : List ℤ := padd (pscale (m:ℤ) Hn) Kn

theorem peval_addSlack (Hn : List ℤ) (Hd m : ℕ) (Kn : List ℤ) (hHd : 0 < Hd) (hm : 0 < m) (t : ℝ) :
    peval (addSlack Hn m Kn) t / (Hd * m : ℕ) = peval Hn t / Hd + peval Kn t / (Hd * m : ℕ) := by
  have h1 : (0:ℝ) < Hd := by exact_mod_cast hHd
  have h2 : (0:ℝ) < m := by exact_mod_cast hm
  simp only [addSlack, peval_padd, peval_pscale]
  push_cast
  field_simp

/-- `Piece.check` without the 5-smooth node test (the node constant is then supplied as a
hypothesis, e.g. at the irrational-contact nodes `c̃`). -/
def Piece.checkCore (Hn : List ℤ) (Hd D : ℕ) (p : Piece) : Bool :=
  decide (0 < p.gd) && decide (p.gn < p.gd) && decide (0 < p.Ld) && p.n % 2 == 1 &&
  decide (p.B ≤ D) &&
  (let q := minorPoly Hn Hd p.gn p.gd p.Ln p.Ld p.n
   (homog [p.A, p.B] [(D:ℤ), (D:ℤ)] q (q.length - 1)).all (fun c => decide (0 ≤ c)))

theorem Piece.sound_of_node (Hn : List ℤ) (Hd D : ℕ) (hHd : 0 < Hd) (hD : 0 < D) (p : Piece)
    (hc : p.checkCore Hn Hd D = true)
    (hnode : (p.Ln:ℝ) / p.Ld ≤ -(1 / 2) * Real.log (2 * (((p.gd:ℝ) - p.gn) / p.gd)))
    {t : ℝ} (h0 : (p.A:ℝ) ≤ D * t) (h1 : (D:ℝ) * t < p.B) :
    peval Hn t / Hd ≤ phi t := by
  simp only [Piece.checkCore, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hgd, hg⟩, hLd⟩, hn⟩, hBD⟩, hmob⟩ := hc
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have ht1 : t < 1 := by
    have : (p.B:ℝ) ≤ D := by exact_mod_cast hBD
    have : (D:ℝ) * t < D * 1 := by linarith
    exact lt_of_mul_lt_mul_left this hDR.le
  have hq := mob_sound _ p.A p.B D hD hmob h0 h1
  have hodd : Odd p.n := Nat.odd_iff.mpr hn
  have s1 := minor_sound Hn Hd p.gn p.gd p.Ln p.Ld p.n hHd hLd hg hq
  have s2 := phi_ge_node hgd hg hodd ht1
  linarith

/-- quartic tube: `κ x⁴ ≤ f ≤ δ ≤ κ τ⁴ ⇒ |x| ≤ τ`. -/
theorem tube4 {κ f δ τ x : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) (h1 : κ * x ^ 4 ≤ f) (h2 : f ≤ δ)
    (h3 : δ ≤ κ * τ ^ 4) : |x| ≤ τ := by
  have h4 : x ^ 4 ≤ τ ^ 4 := le_of_mul_le_mul_left (by linarith) hκ
  have h5 : |x| ^ 4 ≤ τ ^ 4 := by
    rw [show |x| ^ 4 = x ^ 4 by rw [← abs_pow, abs_of_nonneg (by positivity)]]; exact h4
  exact (pow_le_pow_iff_left₀ (abs_nonneg x) hτ (by norm_num)).mp h5

/-- quadratic tube: `κ x² ≤ f ≤ δ ≤ κ τ² ⇒ |x| ≤ τ`. -/
theorem tube2 {κ f δ τ x : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) (h1 : κ * x ^ 2 ≤ f) (h2 : f ≤ δ)
    (h3 : δ ≤ κ * τ ^ 2) : |x| ≤ τ := by
  have h4 : x ^ 2 ≤ τ ^ 2 := le_of_mul_le_mul_left (by linarith) hκ
  have h5 : |x| ^ 2 ≤ τ ^ 2 := by rw [sq_abs]; exact h4
  exact (pow_le_pow_iff_left₀ (abs_nonneg x) hτ (by norm_num)).mp h5

end LogLean.Minor
