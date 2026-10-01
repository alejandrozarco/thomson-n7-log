import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import ThomsonGen.Verbatim.LogLocal

/-!
# LocalKel: the number field K = ℚ(α), α = √(10 + 2√5) = 4 sin 72°, shared by the Lemma L′ modules

`Kel` = 4 rationals in the power basis of α with α⁴ = 20α² − 80; evaluation `ev` at a real `a`; rational
enclosures on a rational α-box (`lo`/`hi`/`aub`); the real `alpha` with its box and minimal polynomial;
the diagonal-dominance lemma for quadratic forms (`qform_dd_nonneg`, upstream, regenerated: see below).
Factored out of the template of `LocalCert.lean` and of `LocalGamma1.lean`.
-/

open Finset

namespace LocalKel

/-! ## Generic part: the number field K = ℚ(α), α⁴ = 20α² − 80 -/

/-- An element `c0 + c1 α + c2 α² + c3 α³` of K. -/
structure Kel where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ
  c3 : ℚ
  deriving DecidableEq

namespace Kel

def zero : Kel := ⟨0, 0, 0, 0⟩
def ofQ (q : ℚ) : Kel := ⟨q, 0, 0, 0⟩
def add (x y : Kel) : Kel := ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c3 + y.c3⟩
def sub (x y : Kel) : Kel := ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2, x.c3 - y.c3⟩
def smul (q : ℚ) (x : Kel) : Kel := ⟨q * x.c0, q * x.c1, q * x.c2, q * x.c3⟩
/-- Product, reduced with α⁴ = 20α² − 80, α⁵ = 20α³ − 80α, α⁶ = 320α² − 1600. -/
def mul (x y : Kel) : Kel :=
  ⟨x.c0 * y.c0 - 80 * (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1) - 1600 * (x.c3 * y.c3),
   (x.c0 * y.c1 + x.c1 * y.c0) - 80 * (x.c2 * y.c3 + x.c3 * y.c2),
   (x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0) + 20 * (x.c1 * y.c3 + x.c2 * y.c2 + x.c3 * y.c1)
     + 320 * (x.c3 * y.c3),
   (x.c0 * y.c3 + x.c1 * y.c2 + x.c2 * y.c1 + x.c3 * y.c0) + 20 * (x.c2 * y.c3 + x.c3 * y.c2)⟩

/-- Evaluation at a real `a` (the power-basis polynomial; no relation needed). -/
noncomputable def ev (x : Kel) (a : ℝ) : ℝ := (x.c0 : ℝ) + x.c1 * a + x.c2 * a ^ 2 + x.c3 * a ^ 3

lemma ev_ofQ (q : ℚ) (a : ℝ) : (ofQ q).ev a = q := by simp [ev, ofQ]

lemma ev_add (x y : Kel) (a : ℝ) : (add x y).ev a = x.ev a + y.ev a := by
  simp only [ev, add]; push_cast; ring

lemma ev_sub (x y : Kel) (a : ℝ) : (sub x y).ev a = x.ev a - y.ev a := by
  simp only [ev, sub]; push_cast; ring

lemma ev_smul (q : ℚ) (x : Kel) (a : ℝ) : (smul q x).ev a = q * x.ev a := by
  simp only [ev, smul]; push_cast; ring

lemma ev_mul (x y : Kel) {a : ℝ} (ha : a ^ 4 = 20 * a ^ 2 - 80) :
    (mul x y).ev a = x.ev a * y.ev a := by
  simp only [ev, mul]; push_cast
  linear_combination (-((x.c1 : ℝ) * y.c3 + (x.c2 : ℝ) * y.c2 + (x.c3 : ℝ) * y.c1
    + ((x.c2 : ℝ) * y.c3 + (x.c3 : ℝ) * y.c2) * a + (x.c3 : ℝ) * y.c3 * (a ^ 2 + 20))) * ha

/-! ### Rational enclosures on a box `l ≤ a ≤ h` (`0 ≤ l`) -/

def mn (u v : ℚ) : ℚ := if u ≤ v then u else v
def mx (u v : ℚ) : ℚ := if u ≤ v then v else u

lemma mn_le (u v : ℚ) : mn u v ≤ u ∧ mn u v ≤ v := by
  unfold mn; split_ifs with h
  · exact ⟨le_rfl, h⟩
  · push Not at h; exact ⟨h.le, le_rfl⟩

lemma le_mx (u v : ℚ) : u ≤ mx u v ∧ v ≤ mx u v := by
  unfold mx; split_ifs with h
  · exact ⟨h, le_rfl⟩
  · push Not at h; exact ⟨le_rfl, h.le⟩

def lo (x : Kel) (l h : ℚ) : ℚ :=
  x.c0 + mn (x.c1 * l) (x.c1 * h) + mn (x.c2 * l ^ 2) (x.c2 * h ^ 2) + mn (x.c3 * l ^ 3) (x.c3 * h ^ 3)
def hi (x : Kel) (l h : ℚ) : ℚ :=
  x.c0 + mx (x.c1 * l) (x.c1 * h) + mx (x.c2 * l ^ 2) (x.c2 * h ^ 2) + mx (x.c3 * l ^ 3) (x.c3 * h ^ 3)
/-- Upper bound for `|ev|`. -/
def aub (x : Kel) (l h : ℚ) : ℚ := mx (x.hi l h) (-(x.lo l h))

lemma term_lo (c l h : ℚ) (k : ℕ) {a : ℝ} (hl : 0 ≤ (l : ℝ)) (hla : (l : ℝ) ≤ a) (hah : a ≤ h) :
    ((mn (c * l ^ k) (c * h ^ k) : ℚ) : ℝ) ≤ c * a ^ k := by
  have h1 : (l : ℝ) ^ k ≤ a ^ k := pow_le_pow_left₀ hl hla k
  have h2 : a ^ k ≤ (h : ℝ) ^ k := pow_le_pow_left₀ (hl.trans hla) hah k
  obtain ⟨m1, m2⟩ := mn_le (c * l ^ k) (c * h ^ k)
  have m1' : ((mn (c * l ^ k) (c * h ^ k) : ℚ) : ℝ) ≤ (c : ℝ) * (l : ℝ) ^ k := by exact_mod_cast m1
  have m2' : ((mn (c * l ^ k) (c * h ^ k) : ℚ) : ℝ) ≤ (c : ℝ) * (h : ℝ) ^ k := by exact_mod_cast m2
  rcases le_total 0 c with h0 | h0
  · exact m1'.trans (mul_le_mul_of_nonneg_left h1 (by exact_mod_cast h0))
  · exact m2'.trans (mul_le_mul_of_nonpos_left h2 (by exact_mod_cast h0))

lemma term_hi (c l h : ℚ) (k : ℕ) {a : ℝ} (hl : 0 ≤ (l : ℝ)) (hla : (l : ℝ) ≤ a) (hah : a ≤ h) :
    (c : ℝ) * a ^ k ≤ ((mx (c * l ^ k) (c * h ^ k) : ℚ) : ℝ) := by
  have h1 : (l : ℝ) ^ k ≤ a ^ k := pow_le_pow_left₀ hl hla k
  have h2 : a ^ k ≤ (h : ℝ) ^ k := pow_le_pow_left₀ (hl.trans hla) hah k
  obtain ⟨m1, m2⟩ := le_mx (c * l ^ k) (c * h ^ k)
  have m1' : (c : ℝ) * (l : ℝ) ^ k ≤ ((mx (c * l ^ k) (c * h ^ k) : ℚ) : ℝ) := by exact_mod_cast m1
  have m2' : (c : ℝ) * (h : ℝ) ^ k ≤ ((mx (c * l ^ k) (c * h ^ k) : ℚ) : ℝ) := by exact_mod_cast m2
  rcases le_total 0 c with h0 | h0
  · exact (mul_le_mul_of_nonneg_left h2 (by exact_mod_cast h0)).trans m2'
  · exact (mul_le_mul_of_nonpos_left h1 (by exact_mod_cast h0)).trans m1'

lemma lo_le_ev (x : Kel) {l h : ℚ} {a : ℝ} (hl : 0 ≤ (l : ℝ)) (hla : (l : ℝ) ≤ a) (hah : a ≤ h) :
    ((x.lo l h : ℚ) : ℝ) ≤ x.ev a := by
  have t1 := term_lo x.c1 l h 1 hl hla hah
  have t2 := term_lo x.c2 l h 2 hl hla hah
  have t3 := term_lo x.c3 l h 3 hl hla hah
  simp only [pow_one] at t1
  unfold lo ev; push_cast; linarith

lemma ev_le_hi (x : Kel) {l h : ℚ} {a : ℝ} (hl : 0 ≤ (l : ℝ)) (hla : (l : ℝ) ≤ a) (hah : a ≤ h) :
    x.ev a ≤ ((x.hi l h : ℚ) : ℝ) := by
  have t1 := term_hi x.c1 l h 1 hl hla hah
  have t2 := term_hi x.c2 l h 2 hl hla hah
  have t3 := term_hi x.c3 l h 3 hl hla hah
  simp only [pow_one] at t1
  unfold hi ev; push_cast; linarith

lemma abs_ev_le (x : Kel) {l h : ℚ} {a : ℝ} (hl : 0 ≤ (l : ℝ)) (hla : (l : ℝ) ≤ a) (hah : a ≤ h) :
    |x.ev a| ≤ ((x.aub l h : ℚ) : ℝ) := by
  have e1 := lo_le_ev x hl hla hah
  have e2 := ev_le_hi x hl hla hah
  obtain ⟨m1, m2⟩ := le_mx (x.hi l h) (-(x.lo l h))
  have m1' : ((x.hi l h : ℚ) : ℝ) ≤ ((x.aub l h : ℚ) : ℝ) := by unfold aub; exact_mod_cast m1
  have m2' : (-(x.lo l h : ℚ) : ℝ) ≤ ((x.aub l h : ℚ) : ℝ) := by unfold aub; exact_mod_cast m2
  rw [abs_le]; constructor <;> linarith

end Kel

/-! ### Quadratic forms
`qform_dd_nonneg` (upstream `Cert.qform_dd_nonneg`) and `list_sum_range_map` (upstream `Cert.Blk.list_sum_range_map`)
are upstream lemmas (huwngtran/thomson-n7-lean @ 25f2fa5) used unchanged; they are regenerated into
`ThomsonGen/Verbatim/LogLocal.lean` by `regen.sh` and imported above. -/

lemma qf_rank1 (u z : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, z i * (u i * u j) * z j = (∑ i ∈ range n, u i * z i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## The real α, its box and its minimal polynomial -/

/-- Rational box for α = √(10 + 2√5). -/
def aLo : ℚ := 190211303259/50000000000
def aHi : ℚ := 380422606519/100000000000

noncomputable def alpha : ℝ := √(10 + 2 * √5)

-- `sqrt5_lo`, `sqrt5_hi`: upstream `Reg.sqrt5_lo`, `Reg.sqrt5_hi` (huwngtran/thomson-n7-lean @ 25f2fa5),
-- regenerated into `ThomsonGen/Verbatim/LogLocal.lean`.

lemma alpha_box : (aLo : ℝ) ≤ alpha ∧ alpha ≤ aHi := by
  have h5 := sqrt5_lo
  have h6 := sqrt5_hi
  constructor
  · unfold alpha
    rw [Real.le_sqrt (by norm_num [aLo]) (by positivity)]
    norm_num [aLo]; linarith
  · unfold alpha
    rw [Real.sqrt_le_left (by norm_num [aHi])]
    norm_num [aHi]; linarith

lemma alpha_minpoly : alpha ^ 4 = 20 * alpha ^ 2 - 80 := by
  have h1 : alpha ^ 2 = 10 + 2 * √5 := by
    unfold alpha; rw [Real.sq_sqrt (by positivity)]
  have h2 : (√5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (alpha ^ 2 - 10 + 2 * √5) * h1 + 4 * h2


lemma aLo_nonneg : (0 : ℝ) ≤ (aLo : ℝ) := by norm_num [aLo]

/-- `|x.ev α| ≤ x.aub aLo aHi`. -/
lemma Kel.abs_ev_alpha_le (x : Kel) : |x.ev alpha| ≤ ((x.aub aLo aHi : ℚ) : ℝ) :=
  Kel.abs_ev_le x aLo_nonneg alpha_box.1 alpha_box.2

lemma Kel.ev_mul_alpha (x y : Kel) : (Kel.mul x y).ev alpha = x.ev alpha * y.ev alpha :=
  Kel.ev_mul x y alpha_minpoly

end LocalKel
