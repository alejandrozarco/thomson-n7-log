import LogLean.LocalFrames
import LogLean.LocalBomb
import LogLean.LogSeries
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr

/-!
# LocalGeom: geometry of the chart at the bipyramid

Points are `V = Fin 3 → ℝ` with the explicit dot product; the bipyramid `Pv` and the frames `E1v E2v` are the
K-valued data of `LocalFrames` evaluated at `alpha`.  For a configuration `y : ℕ → V` of unit vectors this file
provides
* the chart: `ν = ⟪y,P⟫ − 1`, frame coordinates `tco`, tangent part `tv`, `r² = |t|²`, `(1+ν)² + r² = 1`,
  `|h|² = −2ν` (L1); the remainder bound `0 ≥ ν − n̂(r²) ≥ −CE r⁸` (T3);
* the gauge: `Σ Pᵢ ⊗ yᵢ` symmetric ⇒ `⟪r_c, x⟫ = 0` for the three rotation fields; `w ⊥ ker`, `|x|² = |w|² + |s|²` (L2);
* per pair: `⟪yᵢ,yⱼ⟫ < 1` on the ball (L5), the atom bounds of `LocalAtom.Hyp`, and the **pair inequality**
  `−½ log|yᵢ−yⱼ|² ≥ −½ log|Pᵢ−Pⱼ|² + W ℓ + T6_g(atoms) − K_g R⁷` (L3, L4 via `LogSeries`, L7/L10 via `LocalAtom`);
* the criticality collapse `Σ_{i<j} W_ij ℓ_ij = Σ μᵢ νᵢ` and the pole point terms (L3, L6);
* the atom polynomials of `LocalFrames` evaluated at the local coordinates are the real atoms.
-/

namespace LocalGeom
open LocalKel LocalSP LocalAtom LocalFrames LocalBomb Finset

abbrev V := Fin 3 → ℝ

def dot (u v : V) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

lemma dot_comm (u v : V) : dot u v = dot v u := by unfold dot; ring

/-- Cauchy–Schwarz (Lagrange identity). -/
lemma cs (u v : V) : dot u v ^ 2 ≤ dot u u * dot v v := by
  unfold dot
  nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0), sq_nonneg (u 0 * v 2 - u 2 * v 0), sq_nonneg (u 1 * v 2 - u 2 * v 1)]

lemma dot_self_nonneg (u : V) : 0 ≤ dot u u := by
  unfold dot; nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1), mul_self_nonneg (u 2)]

lemma abs_le_of_sq_le {x b : ℝ} (hb : 0 ≤ b) (h : x ^ 2 ≤ b ^ 2) : |x| ≤ b := by
  have : |x| ≤ |b| := sq_le_sq.mp h
  rwa [abs_of_nonneg hb] at this

/-! ## The frames as real vectors -/

noncomputable def Pv (i : ℕ) : V := fun k => (Pk i k).ev alpha
noncomputable def E1v (i : ℕ) : V := fun k => (E1k i k).ev alpha
noncomputable def E2v (i : ℕ) : V := fun k => (E2k i k).ev alpha

lemma ev_dotK (u v : ℕ → Kel) :
    (dotK u v).ev alpha = dot (fun k : Fin 3 => (u k).ev alpha) (fun k : Fin 3 => (v k).ev alpha) := by
  simp only [dotK, Kel.ev_add, Kel.ev_mul_alpha, dot, Fin.val_zero, Fin.val_one, Fin.val_two]; ring

/-- the frame facts of `frameOK`, for one point. -/
lemma frame_facts {i : ℕ} (hi : i < 7) :
    dot (Pv i) (Pv i) = 1 ∧ dot (E1v i) (E1v i) = 1 ∧ dot (E2v i) (E2v i) = 1 ∧
    dot (Pv i) (E1v i) = 0 ∧ dot (Pv i) (E2v i) = 0 ∧ dot (E1v i) (E2v i) = 0 ∧
    ∀ k l : Fin 3, Pv i k * Pv i l + E1v i k * E1v i l + E2v i k * E2v i l = if k = l then 1 else 0 := by
  have h := frameOK_true
  simp only [frameOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h i hi
  have e : ∀ c : Kel, ∀ q : ℚ, c = Kel.ofQ q → c.ev alpha = q := fun c q hc => by rw [hc, Kel.ev_ofQ]
  have e0 : ∀ c : Kel, c = Kel.zero → c.ev alpha = 0 := fun c hc => by rw [hc]; simp [Kel.ev, Kel.zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := e _ _ h1; rw [ev_dotK] at this; push_cast at this; exact this
  · have := e _ _ h2; rw [ev_dotK] at this; push_cast at this; exact this
  · have := e _ _ h3; rw [ev_dotK] at this; push_cast at this; exact this
  · have := e0 _ h4; rw [ev_dotK] at this; exact this
  · have := e0 _ h5; rw [ev_dotK] at this; exact this
  · have := e0 _ h6; rw [ev_dotK] at this; exact this
  · intro k l
    have hkl := h7 k (Fin.isLt k) l (Fin.isLt l)
    have := congrArg (Kel.ev · alpha) hkl
    simp only [Kel.ev_add, Kel.ev_mul_alpha, Kel.ev_ofQ] at this
    simp only [Pv, E1v, E2v]
    by_cases hkl' : k = l
    · have hv : (k : ℕ) = l := congrArg Fin.val hkl'
      rw [if_pos hv] at this; rw [if_pos hkl']; push_cast at this; linarith
    · have hv : (k : ℕ) ≠ l := fun h => hkl' (Fin.ext h)
      rw [if_neg hv] at this; rw [if_neg hkl']; push_cast at this; linarith

/-- completeness of the frame: `v = ⟪v,P⟫P + ⟪v,E1⟫E1 + ⟪v,E2⟫E2`. -/
lemma complete {i : ℕ} (hi : i < 7) (v : V) (k : Fin 3) :
    v k = dot v (Pv i) * Pv i k + dot v (E1v i) * E1v i k + dot v (E2v i) * E2v i k := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := frame_facts hi
  have h0 := h7 k 0
  have h1 := h7 k 1
  have h2 := h7 k 2
  unfold dot
  fin_cases k <;> simp at h0 h1 h2 ⊢ <;> linear_combination (-v 0) * h0 + (-v 1) * h1 + (-v 2) * h2

/-! ## The chart -/

variable (y : ℕ → V)

noncomputable def nu (i : ℕ) : ℝ := dot (y i) (Pv i) - 1
noncomputable def x1 (i : ℕ) : ℝ := dot (y i) (E1v i)
noncomputable def x2 (i : ℕ) : ℝ := dot (y i) (E2v i)
/-- the 14 frame coordinates `x_{2i} = ⟪yᵢ,E1ᵢ⟫`, `x_{2i+1} = ⟪yᵢ,E2ᵢ⟫`. -/
noncomputable def tco (p : ℕ) : ℝ := if p % 2 = 0 then x1 y (p / 2) else x2 y (p / 2)
/-- the tangent part `tᵢ = x_{2i} E1ᵢ + x_{2i+1} E2ᵢ`. -/
noncomputable def tv (i : ℕ) : V := fun k => x1 y i * E1v i k + x2 y i * E2v i k
noncomputable def r2 (i : ℕ) : ℝ := x1 y i ^ 2 + x2 y i ^ 2
/-- `hᵢ = yᵢ − Pᵢ` -/
noncomputable def hv (i : ℕ) : V := fun k => y i k - Pv i k

lemma tco_even (i : ℕ) : tco y (2 * i) = x1 y i := by simp [tco]
lemma tco_odd (i : ℕ) : tco y (2 * i + 1) = x2 y i := by
  simp only [tco]
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  simp [h1, h2]

lemma decomp {i : ℕ} (hi : i < 7) (k : Fin 3) : y i k = (1 + nu y i) * Pv i k + tv y i k := by
  have := complete hi (y i) k
  simp only [nu, tv, x1, x2]; linarith

lemma hv_eq {i : ℕ} (hi : i < 7) (k : Fin 3) : hv y i k = nu y i * Pv i k + tv y i k := by
  simp only [hv]; rw [decomp y hi k]; ring

lemma dot_tv_P {i : ℕ} (hi : i < 7) : dot (tv y i) (Pv i) = 0 := by
  obtain ⟨-, -, -, h4, h5, -, -⟩ := frame_facts hi
  simp only [dot, tv] at *
  linear_combination x1 y i * h4 + x2 y i * h5

lemma dot_tv_tv {i : ℕ} (hi : i < 7) : dot (tv y i) (tv y i) = r2 y i := by
  obtain ⟨-, h2, h3, -, -, h6, -⟩ := frame_facts hi
  simp only [dot, tv, r2] at *
  linear_combination x1 y i ^ 2 * h2 + x2 y i ^ 2 * h3 + 2 * x1 y i * x2 y i * h6

lemma unit_rel {i : ℕ} (hi : i < 7) (hy : dot (y i) (y i) = 1) : (1 + nu y i) ^ 2 + r2 y i = 1 := by
  obtain ⟨h1, -, -, -, -, -, -⟩ := frame_facts hi
  have ht := dot_tv_P y hi
  have htt := dot_tv_tv y hi
  have e : dot (y i) (y i) = (1 + nu y i) ^ 2 * dot (Pv i) (Pv i) + 2 * (1 + nu y i) * dot (tv y i) (Pv i)
      + dot (tv y i) (tv y i) := by
    simp only [dot]; rw [decomp y hi 0, decomp y hi 1, decomp y hi 2]; ring
  rw [hy, h1, ht, htt] at e; linarith

lemma hv_norm {i : ℕ} (hi : i < 7) (hy : dot (y i) (y i) = 1) : dot (hv y i) (hv y i) = -2 * nu y i := by
  obtain ⟨h1, -, -, -, -, -, -⟩ := frame_facts hi
  simp only [dot, hv, nu] at *
  linear_combination hy + h1

lemma r2_nonneg (i : ℕ) : 0 ≤ r2 y i := by unfold r2; positivity

lemma r2_eq_sq (i : ℕ) : r2 y i = tco y (2 * i) ^ 2 + tco y (2 * i + 1) ^ 2 := by
  rw [tco_even, tco_odd]; rfl

/-- `Σ_{p<14} x_p² = Σ_{i<7} r²ᵢ` -/
lemma sum_sq_tco : ∑ p ∈ range 14, tco y p ^ 2 = ∑ i ∈ range 7, r2 y i := by
  simp [Finset.sum_range_succ, r2_eq_sq]; ring

section ball
variable (hy : ∀ k, k < 7 → dot (y k) (y k) = 1)
  (hball : ∑ k ∈ range 7, dot (hv y k) (hv y k) ≤ (1 / 100) ^ 2)
include hy hball

lemma hv_le {i : ℕ} (hi : i < 7) : dot (hv y i) (hv y i) ≤ (1 / 100) ^ 2 :=
  (Finset.single_le_sum (f := fun k => dot (hv y k) (hv y k)) (fun k _ => dot_self_nonneg _)
    (Finset.mem_range.2 hi)).trans hball

/-- On the ball: `−ρ²/2 ≤ ν ≤ 0`, `r² ≤ −2ν`, `r² ≤ ρ²`. -/
lemma chart_bounds {i : ℕ} (hi : i < 7) :
    -1 / 20000 ≤ nu y i ∧ nu y i ≤ 0 ∧ r2 y i ≤ -2 * nu y i ∧ r2 y i ≤ (1 / 100) ^ 2 := by
  have h1 := unit_rel y hi (hy i hi)
  have h2 := hv_norm y hi (hy i hi)
  have h3 := r2_nonneg y i
  have hb := hv_le y hy hball hi
  have hr : r2 y i ≤ -2 * nu y i := by nlinarith
  refine ⟨by linarith, by nlinarith, hr, by linarith⟩

/-- `Σ r²ᵢ ≤ ρ²` -/
lemma sum_r2_le : ∑ i ∈ range 7, r2 y i ≤ (1 / 100) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) hball
  have := chart_bounds y hy hball (Finset.mem_range.1 hi)
  rw [hv_norm y (Finset.mem_range.1 hi) (hy i (Finset.mem_range.1 hi))]; linarith

end ball

/-! ## The chart remainder `e = ν − n̂(r²)` (T3) -/

/-- `0 ≥ ν − n̂(x) ≥ −CE x⁴` from `(1+ν)² + x = 1`, `0 ≤ x ≤ ρ²`, `ν ≥ −ρ²/2`. -/
lemma e_bounds {x ν : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10000) (hrel : (1 + ν) ^ 2 + x = 1)
    (hν : -1 / 20000 ≤ ν) : ν - nhat x ≤ 0 ∧ -(CE : ℝ) * x ^ 4 ≤ ν - nhat x := by
  have hce : (CE : ℝ) = 391 / 10000 := by norm_num [CE]
  rw [hce]
  have hn : nhat x = -x / 2 - x ^ 2 / 8 - x ^ 3 / 16 := nhat_eq x
  have hx2 : x ^ 2 ≤ 1 / 10000 * x := by nlinarith
  have hx3 : x ^ 3 ≤ 1 / 10000 * x ^ 2 := by nlinarith
  have hx4 : 0 ≤ x ^ 4 := by positivity
  set e := ν - nhat x with he
  -- the key identity: e (e + 2(1 + n̂)) = −q, q = x⁴(20 + 4x + x²)/256
  have key : e * (e + 2 * (1 + nhat x)) = -(x ^ 4 * (20 + 4 * x + x ^ 2) / 256) := by
    rw [he, hn]; linear_combination hrel
  have hnh : nhat x ≤ 0 := by rw [hn]; nlinarith
  have hD : 19 / 10 ≤ e + 2 * (1 + nhat x) := by rw [he, hn]; nlinarith
  have hq0 : 0 ≤ x ^ 4 * (20 + 4 * x + x ^ 2) / 256 := by positivity
  have he0 : e ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < e * (e + 2 * (1 + nhat x)) := mul_pos hpos (by linarith)
    linarith
  refine ⟨he0, ?_⟩
  have hs : (20 + 4 * x + x ^ 2) / 256 ≤ 391 / 10000 * (e + 2 * (1 + nhat x)) := by
    rw [he, hn]; nlinarith
  have hq : x ^ 4 * (20 + 4 * x + x ^ 2) / 256 ≤ 391 / 10000 * x ^ 4 * (e + 2 * (1 + nhat x)) := by
    have := mul_le_mul_of_nonneg_left hs hx4
    linarith
  have hDpos : 0 < e + 2 * (1 + nhat x) := by linarith
  by_contra hneg
  push Not at hneg
  have : (-e - 391 / 10000 * x ^ 4) * (e + 2 * (1 + nhat x)) > 0 := mul_pos (by linarith) hDpos
  nlinarith

/-! ## Gauge (L2): the rotation fields -/

/-- `e_c × P` as a real vector -/
noncomputable def crossV (c : ℕ) (P : V) : V :=
  if c = 0 then ![0, -P 2, P 1] else if c = 1 then ![P 2, 0, -P 0] else ![-P 1, P 0, 0]

lemma ev_crossK (c : ℕ) (hc : c < 3) (i : ℕ) (k : Fin 3) : (crossK c (Pk i) k).ev alpha = crossV c (Pv i) k := by
  interval_cases c <;> fin_cases k <;> simp [crossK, crossV, Pv, Kel.ev, Kel.sub, Kel.zero] <;> push_cast <;> ring

/-- the rotation-field coordinates reconstruct `e_c × Pᵢ`. -/
lemma rot_vec {i c : ℕ} (hi : i < 7) (hc : c < 3) (k : Fin 3) :
    (Kd (2 * i) c).ev alpha * E1v i k + (Kd (2 * i + 1) c).ev alpha * E2v i k = crossV c (Pv i) k := by
  have h := rotOK_true
  simp only [rotOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := congrArg (Kel.ev · alpha) (h i hi c hc k (Fin.isLt k))
  simp only [Kel.ev_add, Kel.ev_mul_alpha] at this
  rw [← ev_crossK c hc]; simpa [E1v, E2v] using this

lemma sum_range_14_pairs (f : ℕ → ℝ) : ∑ p ∈ range 14, f p = ∑ i ∈ range 7, (f (2 * i) + f (2 * i + 1)) := by
  simp [Finset.sum_range_succ]; ring

/-- **Gauge ⇒ x ⊥ rotation fields.** -/
theorem gauge_rot (hg : ∀ a b : Fin 3, ∑ i ∈ range 7, Pv i a * y i b = ∑ i ∈ range 7, Pv i b * y i a)
    {c : ℕ} (hc : c < 3) : ∑ p ∈ range 14, (Kd p c).ev alpha * tco y p = 0 := by
  rw [sum_range_14_pairs]
  have step : ∀ i ∈ range 7, (Kd (2 * i) c).ev alpha * tco y (2 * i) + (Kd (2 * i + 1) c).ev alpha * tco y (2 * i + 1)
      = dot (y i) (crossV c (Pv i)) := by
    intro i hi
    rw [tco_even, tco_odd]
    have h0 := rot_vec (i := i) (Finset.mem_range.1 hi) hc 0
    have h1 := rot_vec (i := i) (Finset.mem_range.1 hi) hc 1
    have h2 := rot_vec (i := i) (Finset.mem_range.1 hi) hc 2
    simp only [x1, x2, dot]
    linear_combination y i 0 * h0 + y i 1 * h1 + y i 2 * h2
  rw [Finset.sum_congr rfl step]
  interval_cases c
  · have e : ∀ i ∈ range 7, dot (y i) (crossV 0 (Pv i)) = -(Pv i 2 * y i 1) + Pv i 1 * y i 2 := by
      intro i _; simp [dot, crossV]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_neg_distrib, hg 1 2]; ring
  · have e : ∀ i ∈ range 7, dot (y i) (crossV 1 (Pv i)) = Pv i 2 * y i 0 + -(Pv i 0 * y i 2) := by
      intro i _; simp [dot, crossV]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_neg_distrib, hg 0 2]; ring
  · have e : ∀ i ∈ range 7, dot (y i) (crossV 2 (Pv i)) = -(Pv i 1 * y i 0) + Pv i 0 * y i 1 := by
      intro i _; simp [dot, crossV]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_neg_distrib, hg 0 1]; ring

/-! ### The soft coordinates and `w` -/

/-- `ŝ_α[p]` (α = 0, 1) -/
noncomputable def sh (al p : ℕ) : ℝ := (Kd p (3 + al)).ev alpha
noncomputable def sig (al : ℕ) : ℝ := (2 / 5) * ∑ p ∈ range 14, sh al p * tco y p
noncomputable def wco (p : ℕ) : ℝ := tco y p - sig y 0 * sh 0 p - sig y 1 * sh 1 p

lemma ksum_ev (l : List Kel) : (ksum l).ev alpha = (l.map fun c => c.ev alpha).sum := by
  induction l with
  | nil => simp [ksum, Kel.ev, Kel.zero]
  | cons c l ih =>
    simp only [ksum, List.foldr_cons] at ih ⊢
    rw [Kel.ev_add, ih]; simp

/-- the Gram matrix of the kernel vectors: `diag (9/2, 9/2, 5, 5/2, 5/2)` -/
lemma gram_fact {b b' : ℕ} (hb : b < 5) (hb' : b' < 5) :
    ∑ p ∈ range 14, (Kd p b).ev alpha * (Kd p b').ev alpha = if b = b' then (gram b : ℝ) else 0 := by
  have h := gramOK_true
  simp only [gramOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := congrArg (Kel.ev · alpha) (h b hb b' hb')
  rw [ksum_ev, List.map_map, Kel.ev_ofQ] at this
  have e : ((List.range 14).map ((fun c : Kel => c.ev alpha) ∘ fun p => (Kd p b).mul (Kd p b'))).sum
      = ∑ p ∈ range 14, (Kd p b).ev alpha * (Kd p b').ev alpha := by
    rw [list_sum_range_map]; simp [Kel.ev_mul_alpha]
  rw [e] at this; rw [this]
  split_ifs <;> simp

lemma sh_dot_sh {al be : ℕ} (hal : al < 2) (hbe : be < 2) :
    ∑ p ∈ range 14, sh al p * sh be p = if al = be then 5 / 2 else 0 := by
  have := gram_fact (b := 3 + al) (b' := 3 + be) (by omega) (by omega)
  simp only [sh]; rw [this]
  interval_cases al <;> interval_cases be <;> simp [gram] <;> norm_num

lemma rot_dot_sh {c al : ℕ} (hc : c < 3) (hal : al < 2) : ∑ p ∈ range 14, (Kd p c).ev alpha * sh al p = 0 := by
  have := gram_fact (b := c) (b' := 3 + al) (by omega) (by omega)
  simp only [sh]; rw [this, if_neg (by omega)]

/-- `w ⊥ ker`: the five kernel components of `w` vanish (given the gauge). -/
theorem w_ker (hg : ∀ a b : Fin 3, ∑ i ∈ range 7, Pv i a * y i b = ∑ i ∈ range 7, Pv i b * y i a)
    {b : ℕ} (hb : b < 5) : ∑ p ∈ range 14, (Kd p b).ev alpha * wco y p = 0 := by
  have e : ∑ p ∈ range 14, (Kd p b).ev alpha * wco y p
      = ∑ p ∈ range 14, (Kd p b).ev alpha * tco y p - sig y 0 * ∑ p ∈ range 14, (Kd p b).ev alpha * sh 0 p
        - sig y 1 * ∑ p ∈ range 14, (Kd p b).ev alpha * sh 1 p := by
    simp only [wco, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [e]
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · rw [gauge_rot y hg hb3, rot_dot_sh hb3 (by norm_num), rot_dot_sh hb3 (by norm_num)]; ring
  · obtain ⟨al, hal, rfl⟩ : ∃ al, al < 2 ∧ b = 3 + al := ⟨b - 3, by omega, by omega⟩
    have h0 : ∑ p ∈ range 14, (Kd p (3 + al)).ev alpha * sh 0 p = if al = 0 then 5 / 2 else 0 := by
      have := sh_dot_sh hal (be := 0) (by norm_num); simpa [sh] using this
    have h1 : ∑ p ∈ range 14, (Kd p (3 + al)).ev alpha * sh 1 p = if al = 1 then 5 / 2 else 0 := by
      have := sh_dot_sh hal (be := 1) (by norm_num); simpa [sh] using this
    rw [h0, h1]
    simp only [sig, sh]
    interval_cases al <;> simp <;> ring

/-- `|x|² = |w|² + (5/2)(σ₀² + σ₁²)`. -/
theorem norm_split (hg : ∀ a b : Fin 3, ∑ i ∈ range 7, Pv i a * y i b = ∑ i ∈ range 7, Pv i b * y i a) :
    ∑ p ∈ range 14, tco y p ^ 2 = ∑ p ∈ range 14, wco y p ^ 2 + (5 / 2) * (sig y 0 ^ 2 + sig y 1 ^ 2) := by
  have e : ∀ p ∈ range 14, tco y p ^ 2 = wco y p ^ 2 + 2 * sig y 0 * ((Kd p 3).ev alpha * wco y p)
      + 2 * sig y 1 * ((Kd p 4).ev alpha * wco y p) + sig y 0 ^ 2 * (sh 0 p * sh 0 p)
      + 2 * sig y 0 * sig y 1 * (sh 0 p * sh 1 p) + sig y 1 ^ 2 * (sh 1 p * sh 1 p) := by
    intro p _
    have : tco y p = wco y p + sig y 0 * sh 0 p + sig y 1 * sh 1 p := by simp only [wco]; ring
    rw [this]; simp only [sh]; ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [w_ker y hg (b := 3) (by norm_num), w_ker y hg (b := 4) (by norm_num),
    sh_dot_sh (al := 0) (be := 0) (by norm_num) (by norm_num),
    sh_dot_sh (al := 0) (be := 1) (by norm_num) (by norm_num),
    sh_dot_sh (al := 1) (be := 1) (by norm_num) (by norm_num)]
  simp; ring

/-! ## Pair geometry (L3–L5, atom bounds) -/

section pair
variable {i j : ℕ} (hi : i < 7) (hj : j < 7) (hij : i ≠ j)
include hi hj hij

/-- `⟪Pᵢ,Pⱼ⟫ = g_ij` (class data), `inv (1 − g) = 1`, `2W = inv`, `g ≤ 31/100`, `1 − g² ≤ sg²`, `sg ≥ 0`. -/
lemma pair_consts :
    dot (Pv i) (Pv j) = (gof i j).ev alpha ∧ (invof i j).ev alpha * (1 - (gof i j).ev alpha) = 1 ∧
    2 * (Wof i j).ev alpha = (invof i j).ev alpha ∧ (gof i j).ev alpha ≤ 31 / 100 ∧
    1 - (gof i j).ev alpha ^ 2 ≤ ((clof i j).bC : ℝ) ^ 2 ∧ (0 : ℝ) ≤ (clof i j).bC := by
  have h := pairOK_true
  simp only [pairOK, List.all_eq_true, List.mem_range] at h
  have h' := h i hi j hj
  rw [if_neg hij] at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (Kel.ev · alpha) h1; rw [ev_dotK] at this; exact this
  · have := congrArg (Kel.ev · alpha) h2
    simpa [Kel.ev_mul_alpha, Kel.ev_sub, Kel.ev_ofQ] using this
  · have := congrArg (Kel.ev · alpha) h3
    simpa [Kel.ev_mul_alpha, Kel.ev_ofQ] using this
  · have := Kel.ev_le_hi (gof i j) aLo_nonneg alpha_box.1 alpha_box.2
    have h4' := (Rat.cast_le (K := ℝ)).mpr h4
    push_cast at h4'
    exact this.trans h4'
  · have hh := Kel.ev_le_hi ((Kel.ofQ 1).sub ((gof i j).mul (gof i j))) aLo_nonneg alpha_box.1 alpha_box.2
    rw [Kel.ev_sub, Kel.ev_mul_alpha, Kel.ev_ofQ] at hh
    have h5' : (((Kel.ofQ 1).sub ((gof i j).mul (gof i j))).hi aLo aHi : ℝ) ≤ ((clof i j).bC : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr h5.1
      push_cast at this; exact this
    have := hh.trans h5'
    push_cast at this ⊢; nlinarith [this]
  · have := (Rat.cast_le (K := ℝ)).mpr h5.2
    push_cast at this; exact this

/-- the class check of the pair -/
lemma pair_check : checkClass (clof i j) (gof i j) (Wof i j) (invof i j) (T6of i j) (Kof i j) = true := by
  have hc := clsIdx_lt hi hj hij
  have e : ∀ n, n < 4 → clsIdx i j = n →
      checkClass (clof i j) (gof i j) (Wof i j) (invof i j) (T6of i j) (Kof i j) = true := by
    intro n hn hn'
    simp only [clof, gof, Wof, invof, T6of, Kof, hn']
    interval_cases n
    · exact check_adj
    · exact check_diag
    · exact check_pole
    · exact check_pp
  exact e _ hc rfl

omit hij in
lemma clof_fields : ((clof i j).bA : ℝ) = (SQ2 : ℝ) * (clof i j).bC ∧ ((clof i j).bB : ℝ) = 1 / 2 ∧
    ((clof i j).ce : ℝ) = CE := by
  have hc := clsIdx_le hi hj
  have e : ∀ n, n ≤ 4 → clsIdx i j = n → ((clof i j).bA : ℝ) = (SQ2 : ℝ) * (clof i j).bC ∧
      ((clof i j).bB : ℝ) = 1 / 2 ∧ ((clof i j).ce : ℝ) = CE := by
    intro n hn hn'
    simp only [clof, hn']
    interval_cases n <;> simp [cl_adj, cl_diag, cl_pole, cl_pp] <;> norm_num
  exact e _ hc rfl

/-- the atoms of the pair -/
noncomputable def Cat (i j : ℕ) : ℝ := dot (Pv i) (tv y j)
noncomputable def Cpat (i j : ℕ) : ℝ := dot (tv y i) (Pv j)
noncomputable def Bat (i j : ℕ) : ℝ := dot (tv y i) (tv y j)
noncomputable def Rij (i j : ℕ) : ℝ := Real.sqrt (r2 y i + r2 y j)

omit hi hj hij in
lemma Rij_sq (i j : ℕ) : Rij y i j ^ 2 = r2 y i + r2 y j :=
  Real.sq_sqrt (add_nonneg (r2_nonneg y i) (r2_nonneg y j))

omit hi hj hij in
lemma Rij_nonneg (i j : ℕ) : 0 ≤ Rij y i j := Real.sqrt_nonneg _

/-- `⟪yᵢ,yⱼ⟫ = g + ℓ + hh` with `ℓ = A + g(νᵢ+νⱼ)`, `hh = B + νⱼC′ + νᵢC + gνᵢνⱼ`. -/
lemma inner_expand :
    dot (y i) (y j) = (gof i j).ev alpha + ((Cat y i j + Cpat y i j + (gof i j).ev alpha * (nu y i + nu y j))
      + (Bat y i j + nu y j * Cpat y i j + nu y i * Cat y i j + (gof i j).ev alpha * nu y i * nu y j)) := by
  obtain ⟨hg, -, -, -, -, -⟩ := pair_consts hi hj hij
  have e : dot (y i) (y j) = (1 + nu y i) * (1 + nu y j) * dot (Pv i) (Pv j) + (1 + nu y i) * dot (Pv i) (tv y j)
      + (1 + nu y j) * dot (tv y i) (Pv j) + dot (tv y i) (tv y j) := by
    simp only [dot]; rw [decomp y hi 0, decomp y hi 1, decomp y hi 2, decomp y hj 0, decomp y hj 1, decomp y hj 2]
    ring
  rw [e, hg]; simp only [Cat, Cpat, Bat]; ring

/-- `ℓ_ij = ⟪Pᵢ,hⱼ⟫ + ⟪hᵢ,Pⱼ⟫`. -/
lemma ell_eq : Cat y i j + Cpat y i j + (gof i j).ev alpha * (nu y i + nu y j)
    = dot (Pv i) (hv y j) + dot (hv y i) (Pv j) := by
  obtain ⟨hg, -, -, -, -, -⟩ := pair_consts hi hj hij
  have e1 : dot (Pv i) (hv y j) = nu y j * dot (Pv i) (Pv j) + dot (Pv i) (tv y j) := by
    simp only [dot]; rw [hv_eq y hj 0, hv_eq y hj 1, hv_eq y hj 2]; ring
  have e2 : dot (hv y i) (Pv j) = nu y i * dot (Pv i) (Pv j) + dot (tv y i) (Pv j) := by
    simp only [dot]; rw [hv_eq y hi 0, hv_eq y hi 1, hv_eq y hi 2]; ring
  rw [e1, e2, hg]; simp only [Cat, Cpat]; ring

variable (hy : ∀ k, k < 7 → dot (y k) (y k) = 1)
  (hball : ∑ k ∈ range 7, dot (hv y k) (hv y k) ≤ (1 / 100) ^ 2)
include hy hball

/-- `⟪yᵢ,yⱼ⟫ < 1` on the ball (L5). -/
lemma inner_lt_one : dot (y i) (y j) < 1 := by
  obtain ⟨hg, -, -, hg31, -, -⟩ := pair_consts hi hj hij
  obtain ⟨hPi, -, -, -, -, -, -⟩ := frame_facts hi
  obtain ⟨hPj, -, -, -, -, -, -⟩ := frame_facts hj
  have e : dot (y i) (y j) = dot (Pv i) (Pv j) + dot (Pv i) (hv y j) + dot (hv y i) (Pv j) + dot (hv y i) (hv y j) := by
    simp only [dot, hv]; ring
  have hbi := hv_le y hy hball hi
  have hbj := hv_le y hy hball hj
  have c1 : dot (Pv i) (hv y j) ≤ 1 / 100 := by
    have := cs (Pv i) (hv y j); rw [hPi] at this
    nlinarith [dot_self_nonneg (hv y j)]
  have c2 : dot (hv y i) (Pv j) ≤ 1 / 100 := by
    have := cs (hv y i) (Pv j); rw [hPj] at this
    nlinarith [dot_self_nonneg (hv y i)]
  have c3 : dot (hv y i) (hv y j) ≤ (1 / 100) ^ 2 := by
    have := cs (hv y i) (hv y j)
    have h1 := dot_self_nonneg (hv y i)
    have h2 := dot_self_nonneg (hv y j)
    nlinarith [mul_le_mul hbi hbj h2 (by norm_num)]
  rw [e, hg]; linarith

lemma Rij_le : Rij y i j ≤ (rho : ℝ) := by
  have hR2 := Rij_sq y i j
  have hR0 := Rij_nonneg y i j
  have hs := sum_r2_le y hy hball
  have h2 : r2 y i + r2 y j ≤ ∑ k ∈ range 7, r2 y k := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {i, j}) (t := range 7) (f := r2 y)
      (by intro k hk; simp at hk; rcases hk with rfl | rfl <;> simp [hi, hj]) (fun k _ _ => r2_nonneg y k)
    rwa [Finset.sum_pair hij] at this
  have hrho : (rho : ℝ) = 1 / 100 := by norm_num [rho]
  rw [hrho]
  refine abs_le_of_sq_le (by norm_num) ?_ |>.trans' (le_abs_self _)
  rw [hR2]; linarith

/-- the atom bounds of `LocalAtom.Hyp` for the pair -/
lemma pair_hyp :
    Hyp (clof i j) (Cat y i j + Cpat y i j) (Bat y i j) (Cat y i j) (Cpat y i j) (r2 y i) (r2 y j) (Rij y i j) alpha := by
  obtain ⟨hg, -, -, -, hsg, hsg0⟩ := pair_consts hi hj hij
  obtain ⟨hA, hB, hce⟩ := clof_fields hi hj
  obtain ⟨hPi, -, -, -, -, -, -⟩ := frame_facts hi
  obtain ⟨hPj, -, -, -, -, -, -⟩ := frame_facts hj
  have hR2 := Rij_sq y i j
  have hR0 := Rij_nonneg y i j
  have hri := r2_nonneg y i
  have hrj := r2_nonneg y j
  have hti := dot_tv_P y hi
  have htj := dot_tv_P y hj
  have htti := dot_tv_tv y hi
  have httj := dot_tv_tv y hj
  set sg : ℝ := ((clof i j).bC : ℝ) with hsgdef
  set g : ℝ := (gof i j).ev alpha with hgdef
  have hC2 : Cat y i j ^ 2 ≤ sg ^ 2 * r2 y j := by
    set u : V := fun k => Pv i k - g * Pv j k with hu
    have e1 : Cat y i j = dot u (tv y j) := by
      have h1 : dot u (tv y j) = dot (Pv i) (tv y j) - g * dot (tv y j) (Pv j) := by
        simp only [dot, hu]; ring
      rw [h1, htj]; simp [Cat]
    have e2 : dot u u = 1 - g ^ 2 := by
      have h1 : dot u u = dot (Pv i) (Pv i) - 2 * g * dot (Pv i) (Pv j) + g ^ 2 * dot (Pv j) (Pv j) := by
        simp only [dot, hu]; ring
      rw [h1, hPi, hPj, hg]; ring
    have := cs u (tv y j)
    rw [e2, httj] at this; rw [e1]
    nlinarith [mul_le_mul_of_nonneg_right hsg hrj]
  have hCp2 : Cpat y i j ^ 2 ≤ sg ^ 2 * r2 y i := by
    set u : V := fun k => Pv j k - g * Pv i k with hu
    have e1 : Cpat y i j = dot (tv y i) u := by
      have h1 : dot (tv y i) u = dot (tv y i) (Pv j) - g * dot (tv y i) (Pv i) := by
        simp only [dot, hu]; ring
      rw [h1, hti]; simp [Cpat]
    have e2 : dot u u = 1 - g ^ 2 := by
      have h1 : dot u u = dot (Pv j) (Pv j) - 2 * g * dot (Pv i) (Pv j) + g ^ 2 * dot (Pv i) (Pv i) := by
        simp only [dot, hu]; ring
      rw [h1, hPi, hPj, hg]; ring
    have := cs (tv y i) u
    rw [e2, htti] at this; rw [e1]
    nlinarith [mul_le_mul_of_nonneg_right hsg hri]
  have hB2 : Bat y i j ^ 2 ≤ r2 y i * r2 y j := by
    have := cs (tv y i) (tv y j); rwa [htti, httj] at this
  have hsgR : 0 ≤ sg * Rij y i j := mul_nonneg hsg0 hR0
  have hSQ2 : (2 : ℝ) ≤ (SQ2 : ℝ) ^ 2 := by norm_num [SQ2]
  have hSQ0 : (0 : ℝ) ≤ (SQ2 : ℝ) := by norm_num [SQ2]
  refine ⟨?_, ?_, ?_, ?_, hri, ?_, hrj, ?_, hR0, Rij_le y hi hj hij hy hball, ?_, ?_, hsg0, ?_,
    alpha_box.1, alpha_box.2, alpha_minpoly⟩
  · rw [hA]
    refine abs_le_of_sq_le (by positivity) ?_
    have : (Cat y i j + Cpat y i j) ^ 2 ≤ 2 * (Cat y i j ^ 2 + Cpat y i j ^ 2) := by
      nlinarith [sq_nonneg (Cat y i j - Cpat y i j)]
    calc (Cat y i j + Cpat y i j) ^ 2 ≤ 2 * (sg ^ 2 * (r2 y i + r2 y j)) := by linarith
      _ = 2 * (sg ^ 2 * Rij y i j ^ 2) := by rw [hR2]
      _ ≤ (SQ2 : ℝ) ^ 2 * (sg ^ 2 * Rij y i j ^ 2) := by gcongr
      _ = ((SQ2 : ℝ) * sg * Rij y i j) ^ 2 := by ring
  · rw [hB]
    refine abs_le_of_sq_le (by positivity) ?_
    calc Bat y i j ^ 2 ≤ r2 y i * r2 y j := hB2
      _ ≤ ((r2 y i + r2 y j) / 2) ^ 2 := by nlinarith [sq_nonneg (r2 y i - r2 y j)]
      _ = (1 / 2 * Rij y i j ^ 2) ^ 2 := by rw [hR2]; ring
  · refine abs_le_of_sq_le hsgR ?_
    calc Cat y i j ^ 2 ≤ sg ^ 2 * r2 y j := hC2
      _ ≤ sg ^ 2 * (r2 y i + r2 y j) := by gcongr; linarith
      _ = (sg * Rij y i j) ^ 2 := by rw [← hR2]; ring
  · refine abs_le_of_sq_le hsgR ?_
    calc Cpat y i j ^ 2 ≤ sg ^ 2 * r2 y i := hCp2
      _ ≤ sg ^ 2 * (r2 y i + r2 y j) := by gcongr; linarith
      _ = (sg * Rij y i j) ^ 2 := by rw [← hR2]; ring
  · rw [hR2]; linarith
  · rw [hR2]; linarith
  · rw [hA]; exact mul_nonneg hSQ0 hsg0
  · rw [hB]; norm_num
  · rw [hce]; norm_num [CE]

/-- `|eᵢ| ≤ CE R⁸` for the chart remainder of point `i` (any `i < 7`), with `R = R_ij`. -/
lemma e_le {k : ℕ} (hk : k < 7) (hkR : r2 y k ≤ Rij y i j ^ 2) :
    |nu y k - nhat (r2 y k)| ≤ (CE : ℝ) * Rij y i j ^ 8 := by
  have hb := chart_bounds y hy hball hk
  have hrel := unit_rel y hk (hy k hk)
  obtain ⟨e1, e2⟩ := e_bounds (r2_nonneg y k) (by linarith [hb.2.2.2]) hrel hb.1
  have hce : (0 : ℝ) ≤ CE := by norm_num [CE]
  have h4 : r2 y k ^ 4 ≤ (Rij y i j ^ 2) ^ 4 := pow_le_pow_left₀ (r2_nonneg y k) hkR 4
  rw [abs_le]
  constructor
  · calc -((CE : ℝ) * Rij y i j ^ 8) = -(CE : ℝ) * (Rij y i j ^ 2) ^ 4 := by ring
      _ ≤ -(CE : ℝ) * r2 y k ^ 4 := by nlinarith
      _ ≤ _ := e2
  · have : (0 : ℝ) ≤ CE * Rij y i j ^ 8 := by positivity
    linarith

/-- **The pair inequality** (L3–L5 + atom level):
`−½ log|yᵢ−yⱼ|² ≥ −½ log|Pᵢ−Pⱼ|² + W ℓ + T6_g(atoms) − K_g R⁷`. -/
theorem pair_lower :
    -(1 / 2) * Real.log (dot (y i - y j) (y i - y j))
      ≥ -(1 / 2) * Real.log (dot (Pv i - Pv j) (Pv i - Pv j))
        + (Wof i j).ev alpha * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j))
        + evT6 (T6of i j) (Cat y i j + Cpat y i j) (Bat y i j) (Cat y i j) (Cpat y i j) (r2 y i) (r2 y j) alpha
        - (Kof i j : ℝ) * Rij y i j ^ 7 := by
  obtain ⟨hg, hinv, hW, hg31, -, -⟩ := pair_consts hi hj hij
  obtain ⟨hPi, -, -, -, -, -, -⟩ := frame_facts hi
  obtain ⟨hPj, -, -, -, -, -, -⟩ := frame_facts hj
  have hyi := hy i hi
  have hyj := hy j hj
  set gR := (gof i j).ev alpha with hgR
  set WR := (Wof i j).ev alpha with hWR
  set invR := (invof i j).ev alpha with hinvR
  set A := Cat y i j + Cpat y i j with hAdef
  set B := Bat y i j with hBdef
  set C := Cat y i j with hCdef
  set Cp := Cpat y i j with hCpdef
  set νi := nu y i with hνi
  set νj := nu y j with hνj
  set ℓ := A + gR * (νi + νj) with hℓ
  set hh := B + νj * Cp + νi * C + gR * νi * νj with hhh
  set u := invR * (ℓ + hh) with hu
  have hexp : dot (y i) (y j) = gR + (ℓ + hh) := inner_expand y hi hj hij
  have hlt : dot (y i) (y j) < 1 := inner_lt_one y hi hj hij hy hball
  have e1 : dot (y i - y j) (y i - y j) = 2 - 2 * dot (y i) (y j) := by
    simp only [dot, Pi.sub_apply] at *; linear_combination hyi + hyj
  have e2 : dot (Pv i - Pv j) (Pv i - Pv j) = 2 - 2 * gR := by
    simp only [dot, Pi.sub_apply] at *; linear_combination hPi + hPj - 2 * hg
  have hg1 : 0 < 1 - gR := by linarith
  have hfac : 2 - 2 * dot (y i) (y j) = (2 - 2 * gR) * (1 - u) := by
    rw [hexp, hu]; linear_combination (2 * (ℓ + hh)) * hinv
  have hu1 : 0 < 1 - u := by
    have hprod : 0 < (2 - 2 * gR) * (1 - u) := by rw [← hfac]; linarith
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 2 - 2 * gR) hneg
    linarith
  have hlog : Real.log (dot (y i - y j) (y i - y j)) = Real.log (2 - 2 * gR) + Real.log (1 - u) := by
    rw [e1, hfac, Real.log_mul (by linarith) (by linarith)]
  -- ψ ≥ ψ₅ (LogSeries, n = 5)
  have hT := LogLean.sum_le_neg_log_one_sub (n := 5) (by decide) (by linarith : u < 1)
  have hT' : u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 ≤ -Real.log (1 - u) := by
    have e : LogLean.logTaylor 5 u = u + u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5 := by
      simp only [LogLean.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; ring
    rwa [e] at hT
  -- the atom level
  have hyp := pair_hyp y hi hj hij hy hball
  have hR2 := Rij_sq y i j
  have hei := e_le y hi hj hij hy hball hi (by rw [hR2]; linarith [r2_nonneg y j])
  have hej := e_le y hi hj hij hy hball hj (by rw [hR2]; linarith [r2_nonneg y i])
  have hcl := clof_fields hi hj
  rw [← hcl.2.2] at hei hej
  have hcb := class_bound hyp (gof i j) (Wof i j) (invof i j) (T6of i j) (Kof i j) (pair_check hi hj hij) hei hej
  have eνi : nhat (r2 y i) + (nu y i - nhat (r2 y i)) = νi := by ring
  have eνj : nhat (r2 y j) + (nu y j - nhat (r2 y j)) = νj := by ring
  rw [eνi, eνj] at hcb
  have hPhi := PhiR_eq gR WR invR A B C Cp νi νj
  have hlow := (abs_le.1 hcb).1
  -- assemble
  rw [hlog, e2]
  have hWu : (1 / 2) * u = WR * (ℓ + hh) := by rw [hu]; linear_combination (-(1 / 2) * (ℓ + hh)) * hW
  have hell : ℓ = dot (Pv i) (hv y j) + dot (hv y i) (Pv j) := ell_eq y hi hj hij
  rw [← hell]
  have : PhiR gR WR invR A B C Cp νi νj = WR * hh + (1 / 2) * (u ^ 2 / 2 + u ^ 3 / 3 + u ^ 4 / 4 + u ^ 5 / 5) := by
    rw [hPhi] <;> (simp only [hu, hℓ, hhh]; ring)
  linarith [hT', hlow, hWu, this]

end pair

/-! ## Criticality collapse and the pole terms (L3, L6) -/

/-- `W_ij` as reals (zero diagonal) -/
noncomputable def Wr (i j : ℕ) : ℝ := (Wtab i j).ev alpha
noncomputable def mur (i : ℕ) : ℝ := (muk i).ev alpha

lemma Wr_eq {i j : ℕ} (hij : i ≠ j) : Wr i j = (Wof i j).ev alpha := by simp [Wr, Wtab, hij]

lemma Wr_symm {i j : ℕ} (hi : i < 7) (hj : j < 7) : Wr i j = Wr j i := by
  simp only [Wr]; rw [Wtab_sym hi hj]

lemma crit_real {i : ℕ} (hi : i < 7) (k : Fin 3) :
    ∑ j ∈ range 7, Wr i j * Pv j k = mur i * Pv i k := by
  have h := critOK_true
  simp only [critOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := congrArg (Kel.ev · alpha) (h i hi k (Fin.isLt k))
  rw [ksum_ev, List.map_map, Kel.ev_mul_alpha] at this
  have e : ((List.range 7).map ((fun c : Kel => c.ev alpha) ∘ fun j => (Wtab i j).mul (Pk j k))).sum
      = ∑ j ∈ range 7, Wr i j * Pv j k := by
    rw [list_sum_range_map]; simp [Kel.ev_mul_alpha, Wr, Pv]
  rw [e] at this; rw [this]; rfl

/-- `Σ_{i<j} W_ij (⟪Pᵢ,hⱼ⟫ + ⟪hᵢ,Pⱼ⟫) = Σᵢ μᵢ νᵢ` -/
theorem crit_sum :
    ∑ i ∈ range 7, ∑ j ∈ range 7, (if i < j then Wr i j * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j)) else 0)
      = ∑ i ∈ range 7, mur i * nu y i := by
  -- symmetrise
  have step1 : ∀ i ∈ range 7, ∀ j ∈ range 7,
      (if i < j then Wr i j * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j)) else 0)
        = (if i < j then Wr i j * dot (hv y i) (Pv j) else 0) + (if i < j then Wr j i * dot (hv y j) (Pv i) else 0) := by
    intro i hi j hj
    split_ifs
    · rw [Wr_symm (Finset.mem_range.1 hi) (Finset.mem_range.1 hj), dot_comm (Pv i) (hv y j)]; ring
    · ring
  simp only [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (step1 i hi), Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then Wr j i * dot (hv y j) (Pv i) else 0)]
  rw [← Finset.sum_add_distrib]
  have step2 : ∀ i ∈ range 7, (∑ j ∈ range 7, (if i < j then Wr i j * dot (hv y i) (Pv j) else 0))
      + (∑ j ∈ range 7, (if j < i then Wr i j * dot (hv y i) (Pv j) else 0))
      = ∑ j ∈ range 7, Wr i j * dot (hv y i) (Pv j) := by
    intro i hi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : i < j
    · rw [if_pos h1, if_neg (by omega)]; ring
    · by_cases h2 : j < i
      · rw [if_neg h1, if_pos h2]; ring
      · have : i = j := by omega
        subst this
        simp [Wr, Wtab, Kel.ev, Kel.zero]
  rw [Finset.sum_congr rfl step2]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have c0 := crit_real hi' 0
  have c1 := crit_real hi' 1
  have c2 := crit_real hi' 2
  have e : ∑ j ∈ range 7, Wr i j * dot (hv y i) (Pv j)
      = hv y i 0 * ∑ j ∈ range 7, Wr i j * Pv j 0 + hv y i 1 * ∑ j ∈ range 7, Wr i j * Pv j 1
        + hv y i 2 * ∑ j ∈ range 7, Wr i j * Pv j 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dot]; ring
  rw [e, c0, c1, c2]
  obtain ⟨hPi, -, -, -, -, -, -⟩ := frame_facts hi'
  simp only [nu, hv, dot] at hPi ⊢
  linear_combination (-(mur i)) * hPi

lemma mur_val (i : ℕ) : mur i = if i < 5 then 0 else -1 / 4 := by
  simp only [mur, muk]; split_ifs <;> simp [Kel.ev, Kel.zero, Kel.ofQ] <;> norm_num

/-- `Σᵢ μᵢ νᵢ = −¼(ν₅ + ν₆)` -/
lemma mu_sum : ∑ i ∈ range 7, mur i * nu y i = -(1 / 4) * (nu y 5 + nu y 6) := by
  simp [Finset.sum_range_succ, mur_val]; ring

/-- pole point terms: `−¼ν ≥ r²/8 + r⁴/32` -/
lemma pole_term (hy : ∀ k, k < 7 → dot (y k) (y k) = 1)
    (hball : ∑ k ∈ range 7, dot (hv y k) (hv y k) ≤ (1 / 100) ^ 2) {i : ℕ} (hi : i < 7) :
    r2 y i / 8 + r2 y i ^ 2 / 32 ≤ -(1 / 4) * nu y i := by
  have hb := chart_bounds y hy hball hi
  have hrel := unit_rel y hi (hy i hi)
  obtain ⟨e1, -⟩ := e_bounds (r2_nonneg y i) (by linarith [hb.2.2.2]) hrel hb.1
  rw [nhat_eq] at e1
  have := r2_nonneg y i
  nlinarith [pow_nonneg this 3]

/-! ## The atom polynomials of `LocalFrames` at the local coordinates -/

section atoms
variable {i j : ℕ} (hi : i < 7) (hj : j < 7)

lemma loc_vals : loc (tco y) i j 0 = x1 y i ∧ loc (tco y) i j 1 = x2 y i ∧ loc (tco y) i j 2 = x1 y j
    ∧ loc (tco y) i j 3 = x2 y j := by
  simp [loc, tco_even, tco_odd]

omit hi hj in
lemma ev_atC : ev (atC i j) (loc (tco y) i j) alpha = Cat y i j := by
  obtain ⟨-, -, l2, l3⟩ := loc_vals y (i := i) (j := j)
  simp only [atC, ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mono.ev, pow_zero, pow_one,
    one_mul, mul_one, l2, l3, ev_dotK, Cat, dot, tv]
  simp only [Pv, E1v, E2v]; ring

omit hi hj in
lemma ev_atCp : ev (atCp i j) (loc (tco y) i j) alpha = Cpat y i j := by
  obtain ⟨l0, l1, -, -⟩ := loc_vals y (i := i) (j := j)
  simp only [atCp, ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mono.ev, pow_zero, pow_one,
    one_mul, mul_one, l0, l1, ev_dotK, Cpat, dot, tv]
  simp only [Pv, E1v, E2v]; ring

omit hi hj in
lemma ev_atA : ev (atA i j) (loc (tco y) i j) alpha = Cat y i j + Cpat y i j := by
  obtain ⟨l0, l1, l2, l3⟩ := loc_vals y (i := i) (j := j)
  simp only [atA, ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mono.ev, pow_zero, pow_one,
    one_mul, mul_one, l0, l1, l2, l3, ev_dotK, Cat, Cpat, dot, tv]
  simp only [Pv, E1v, E2v]; ring

omit hi hj in
lemma ev_atB : ev (atB i j) (loc (tco y) i j) alpha = Bat y i j := by
  obtain ⟨l0, l1, l2, l3⟩ := loc_vals y (i := i) (j := j)
  simp only [atB, ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mono.ev, pow_zero, pow_one,
    one_mul, mul_one, l0, l1, l2, l3, ev_dotK, Bat, dot, tv]
  simp only [Pv, E1v, E2v]; ring

omit hi hj in
lemma ev_atRi : ev atRi (loc (tco y) i j) alpha = r2 y i := by
  obtain ⟨l0, l1, -, -⟩ := loc_vals y (i := i) (j := j)
  simp [atRi, ev, Mono.ev, l0, l1, Kel.ev_ofQ, r2]; ring

omit hi hj in
lemma ev_atRj : ev atRj (loc (tco y) i j) alpha = r2 y j := by
  obtain ⟨-, -, l2, l3⟩ := loc_vals y (i := i) (j := j)
  simp [atRj, ev, Mono.ev, l2, l3, Kel.ev_ofQ, r2]; ring

end atoms

end LocalGeom
