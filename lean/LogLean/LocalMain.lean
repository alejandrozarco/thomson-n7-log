import Mathlib
import LogLean.LocalGeom
import LogLean.LocalGlobal
import LogLean.LocalPairsA
import LogLean.LocalPairsB
import LogLean.LocalPairsC
import LogLean.LocalScalar

/-!
# LocalMain: Lemma L′ (the quartic local lemma for the log energy at the pentagonal bipyramid)

Assembly of `LocalGeom` (chart, gauge, pair inequality), `LocalPairs*` (the 21 pair identities), `LocalGlobal`
(the (σ, w) expansion and the Bombieri bounds), `LocalCert` ((C′)), `LocalGamma1` (γ₁) and `LocalScalar`
(the scalar argument).

Main results (`R3 = EuclideanSpace ℝ (Fin 3)`, `Pbip` the bipyramid with coordinates in K = ℚ(α)):
* `Lprime`: for unit `y` with the gauge condition and `Σ‖yᵢ − Pᵢ‖² ≤ (1/100)²`,
  `0.0268 |w|² + 0.0200 |s|⁴ ≤ logEnergy y − logEnergy Pbip`;
* `Lprime_nonneg`, `Lprime_eq`: `logEnergy Pbip ≤ logEnergy y`, with equality only for `y = Pbip`;
* `pent_local_min_sup_log`: the handoff form at sup radius `1/300` (the gauge step `exists_gauge` is taken as a
  hypothesis here; `LocalHandoff.lean` discharges it).
-/

open LocalKel LocalSP LocalAtom LocalFrames LocalBomb LocalGeom LocalGlobal LocalGlobData LocalPairData Finset

namespace LocalMain

/-! ## The energy in the `ℕ`-indexed chart world -/

/-- `Σ_{i<j} −½ log |yᵢ − yⱼ|²` -/
noncomputable def Ey (y : ℕ → V) : ℝ :=
  ∑ i ∈ range 7, ∑ j ∈ range 7, if i < j then -(1 / 2) * Real.log (dot (y i - y j) (y i - y j)) else 0

lemma sum_pairs_eq (f : ℕ → ℕ → ℝ) :
    ∑ i ∈ range 7, ∑ j ∈ range 7, (if i < j then f i j else 0) = (pairsL.map fun ij => f ij.1 ij.2).sum := by
  simp [Finset.sum_range_succ, pairsL] <;> ring

lemma mem_pairsL {i j : ℕ} (hi : i < 7) (hj : j < 7) (hij : i < j) : (i, j) ∈ pairsL := by
  interval_cases i <;> interval_cases j <;> first | omega | decide

/-- the 21 pair identities, packaged -/
lemma pair_id {i j : ℕ} (hij : (i, j) ∈ pairsL) :
    checkEq6 (T6of i j) (atA i j) (atB i j) (atC i j) (atCp i j) atRi atRj (pij i j) = true := by
  simp only [pairsL, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [LocalPairs.check01, LocalPairs.check02, LocalPairs.check03, LocalPairs.check04, LocalPairs.check05,
    LocalPairs.check06, LocalPairs.check12, LocalPairs.check13, LocalPairs.check14, LocalPairs.check15,
    LocalPairs.check16, LocalPairs.check23, LocalPairs.check24, LocalPairs.check25, LocalPairs.check26,
    LocalPairs.check34, LocalPairs.check35, LocalPairs.check36, LocalPairs.check45, LocalPairs.check46,
    LocalPairs.check56]

lemma Kd_eq_cert (p b : ℕ) : LocalFrames.Kd p b = LocalCert.Kd p b := rfl
lemma Kd_eq_gamma (p b : ℕ) : LocalFrames.Kd p b = LocalGamma1.Kd p b := rfl

/-- `K = B₅ + B₆ρ + K₇ρ²` -/
def K7pp : ℚ := 851804 / 10000
def KK : ℚ := 369252 / 100000

/-- `X² ≤ B·u²`, `B ≤ c²` ⇒ `|X| ≤ c·u` -/
lemma abs_bound {X B c u t : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (ht : t = u ^ 2) (hX : X ^ 2 ≤ B * t)
    (hB : B ≤ c ^ 2) : |X| ≤ c * u := by
  refine abs_le_of_sq_le (mul_nonneg hc hu) ?_
  rw [ht] at hX
  nlinarith [mul_le_mul_of_nonneg_right hB (sq_nonneg u)]

/-- the CQ step: `CQ22 a²b² + CQ13 ab³ + C04 b⁴ ≤ CQ (a² + b²) b²` -/
lemma cq_step {a b : ℝ} :
    (CQ22 : ℝ) * a ^ 2 * b ^ 2 + (CQ13 : ℝ) * a * b ^ 3 + (C04 : ℝ) * b ^ 4 ≤ (CQ : ℝ) * (a ^ 2 + b ^ 2) * b ^ 2 := by
  have key : 0 ≤ ((CQ : ℝ) - CQ22) * a ^ 2 - (CQ13 : ℝ) * a * b + ((CQ : ℝ) - C04) * b ^ 2 := by
    norm_num [CQ, CQ22, CQ13, C04]
    nlinarith [sq_nonneg (2 * ((5200491 / 1000000 : ℝ) - 51506243 / 15625000) * a - (2032803893 / 500000000) * b),
      sq_nonneg b]
  nlinarith [mul_nonneg key (sq_nonneg b)]

section core
variable (y : ℕ → V)
  (hy : ∀ k, k < 7 → dot (y k) (y k) = 1)
  (hg : ∀ a b : Fin 3, ∑ i ∈ range 7, Pv i a * y i b = ∑ i ∈ range 7, Pv i b * y i a)
  (hball : ∑ k ∈ range 7, dot (hv y k) (hv y k) ≤ (1 / 100) ^ 2)
include hy hg hball

omit hy hg hball in
/-- the `(σ, w)` coordinates as one function -/
noncomputable def zc (k : ℕ) : ℝ := if k = 0 then sig y 0 else if k = 1 then sig y 1 else wco y (k - 2)

omit hy hg hball in
lemma zc_w (p : ℕ) : zc y (2 + p) = wco y p := by
  simp only [zc, if_neg (show 2 + p ≠ 0 by omega), if_neg (show 2 + p ≠ 1 by omega), Nat.add_sub_cancel_left]
omit hy hg hball in
lemma zc_0 : zc y 0 = sig y 0 := by simp [zc]
omit hy hg hball in
lemma zc_1 : zc y 1 = sig y 1 := by simp [zc]

omit hy hg hball in
lemma tco_eq_xsub (p : ℕ) (hp : p < 14) : tco y p = xsub (zc y) p := by
  simp only [xsub, zc_0, zc_1, zc_w, wco, sh, Nat.add_zero, Nat.reduceAdd]; ring

omit hy hg hball in
/-- `Σ_{k<4} loc_k² = r²ᵢ + r²ⱼ` -/
lemma loc_sq (i j : ℕ) : ∑ k ∈ range 4, loc (tco y) i j k ^ 2 = r2 y i + r2 y j := by
  simp [Finset.sum_range_succ, loc, r2_eq_sq] <;> ring

/-- the pair sum of the pair inequalities: `Ey y − Ey Pv ≥ Σ_{i<j} (W ℓ + T6(atoms) − K R⁷)` -/
lemma energy_step :
    (pairsL.map fun ij => Wr ij.1 ij.2 * (dot (Pv ij.1) (hv y ij.2) + dot (hv y ij.1) (Pv ij.2))).sum
      + (pairsL.map fun ij => ev (pij ij.1 ij.2) (loc (tco y) ij.1 ij.2) alpha).sum
      - (pairsL.map fun ij => (Kof ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 7).sum
      ≤ Ey y - Ey Pv := by
  have step : ∀ i ∈ range 7, ∀ j ∈ range 7,
      (if i < j then -(1 / 2) * Real.log (dot (Pv i - Pv j) (Pv i - Pv j))
          + Wr i j * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j))
          + ev (pij i j) (loc (tco y) i j) alpha - (Kof i j : ℝ) * Rij y i j ^ 7 else 0)
        ≤ (if i < j then -(1 / 2) * Real.log (dot (y i - y j) (y i - y j)) else 0) := by
    intro i hi j hj
    split_ifs with hij
    · have hi' := Finset.mem_range.1 hi
      have hj' := Finset.mem_range.1 hj
      have hne : i ≠ j := by omega
      have hp := pair_lower y hi' hj' hne hy hball
      have hid := eq_of_checkEq6 (x := loc (tco y) i j) alpha_minpoly _ _ _ _ _ _ _ _ (pair_id (mem_pairsL hi' hj' hij))
      rw [ev_atA, ev_atB, ev_atC, ev_atCp, ev_atRi, ev_atRj] at hid
      rw [← hid, Wr_eq hne]
      linarith
    · exact le_rfl
  have hsum := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => step i hi j hj
  have e : ∀ i ∈ range 7, ∀ j ∈ range 7,
      (if i < j then -(1 / 2) * Real.log (dot (Pv i - Pv j) (Pv i - Pv j))
          + Wr i j * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j))
          + ev (pij i j) (loc (tco y) i j) alpha - (Kof i j : ℝ) * Rij y i j ^ 7 else 0)
        = (if i < j then -(1 / 2) * Real.log (dot (Pv i - Pv j) (Pv i - Pv j)) else 0)
          + (if i < j then Wr i j * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j)) else 0)
          + (if i < j then ev (pij i j) (loc (tco y) i j) alpha else 0)
          - (if i < j then (Kof i j : ℝ) * Rij y i j ^ 7 else 0) := by
    intro i _ j _; split_ifs <;> ring
  simp only [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (e i hi), Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hsum
  simp only [sum_pairs_eq] at hsum
  unfold Ey
  simp only [sum_pairs_eq]
  linarith

/-- the criticality collapse plus the pole terms -/
lemma W_step :
    (1 / 8) * (tco y 10 ^ 2 + tco y 11 ^ 2 + tco y 12 ^ 2 + tco y 13 ^ 2)
      + (1 / 32) * ((tco y 10 ^ 2 + tco y 11 ^ 2) ^ 2 + (tco y 12 ^ 2 + tco y 13 ^ 2) ^ 2)
      ≤ (pairsL.map fun ij => Wr ij.1 ij.2 * (dot (Pv ij.1) (hv y ij.2) + dot (hv y ij.1) (Pv ij.2))).sum := by
  have hs := sum_pairs_eq (fun i j => Wr i j * (dot (Pv i) (hv y j) + dot (hv y i) (Pv j)))
  try simp only at hs
  rw [← hs, crit_sum, mu_sum]
  have h5 := pole_term y hy hball (i := 5) (by norm_num)
  have h6 := pole_term y hy hball (i := 6) (by norm_num)
  have e5 : r2 y 5 = tco y 10 ^ 2 + tco y 11 ^ 2 := r2_eq_sq y 5
  have e6 : r2 y 6 = tco y 12 ^ 2 + tco y 13 ^ 2 := r2_eq_sq y 6
  rw [e5] at h5; rw [e6] at h6
  linarith

/-- the pair polynomials summed: degrees 2–4 give `F₂ + F₃ + F₄ − poles`, degrees 5–6 stay per pair -/
lemma T_step :
    (pairsL.map fun ij => ev (pij ij.1 ij.2) (loc (tco y) ij.1 ij.2) alpha).sum
      = ev F2 (tco y) alpha + ev F3 (tco y) alpha + ev F4 (tco y) alpha
        - (1 / 8) * (tco y 10 ^ 2 + tco y 11 ^ 2 + tco y 12 ^ 2 + tco y 13 ^ 2)
        - (1 / 32) * ((tco y 10 ^ 2 + tco y 11 ^ 2) ^ 2 + (tco y 12 ^ 2 + tco y 13 ^ 2) ^ 2)
        + (pairsL.map fun ij => ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha
            + ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha).sum := by
  obtain ⟨h2, h3, h4⟩ := F_sum (x := tco y) alpha_minpoly
  have e : ∀ ij : ℕ × ℕ, ev (pij ij.1 ij.2) (loc (tco y) ij.1 ij.2) alpha
      = ev (pijd ij.1 ij.2 2) (loc (tco y) ij.1 ij.2) alpha + ev (pijd ij.1 ij.2 3) (loc (tco y) ij.1 ij.2) alpha
        + ev (pijd ij.1 ij.2 4) (loc (tco y) ij.1 ij.2) alpha
        + (ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha + ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha) := by
    intro ij; simp only [pij, ev_merge]; ring
  simp only [e, List.sum_map_add]
  rw [h2, h3, h4]; ring

/-- the degree 5–6 pair parts and the atom tails: `≥ −K T⁵` -/
lemma R_step (T : ℝ) (hT0 : 0 ≤ T) (hT2 : T ^ 2 = ∑ i ∈ range 7, r2 y i) (hTρ : T ≤ 1 / 100) :
    -((KK : ℝ) * T ^ 5) ≤
      (pairsL.map fun ij => ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha
          + ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha).sum
        - (pairsL.map fun ij => (Kof ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 7).sum := by
  -- per pair: p₅ + p₆ − K R⁷ ≥ −(B₅ T³ + B₆ T⁴ + K T⁵) R²
  have per : ∀ ij ∈ pairsL,
      -(((B5b ij.1 ij.2 : ℝ) * T ^ 3 + (B6b ij.1 ij.2 : ℝ) * T ^ 4 + (Kof ij.1 ij.2 : ℝ) * T ^ 5)
          * (r2 y ij.1 + r2 y ij.2))
        ≤ ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha + ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha
          - (Kof ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 7 := by
    intro ij hij
    obtain ⟨b5, b6, p5, p6⟩ := pair_bomb hij (loc (tco y) ij.1 ij.2)
    rw [loc_sq] at b5 b6
    have hR2 := Rij_sq y ij.1 ij.2
    have hR0 := Rij_nonneg y ij.1 ij.2
    have hio : ij.1 < ij.2 ∧ ij.2 < 7 := by
      have := pairsL_ok; simp only [List.all_eq_true, decide_eq_true_eq] at this; exact this ij hij
    have hRT : Rij y ij.1 ij.2 ≤ T := by
      refine abs_le_of_sq_le hT0 ?_ |>.trans' (le_abs_self _)
      rw [hR2, hT2]
      have := Finset.sum_le_sum_of_subset_of_nonneg (s := {ij.1, ij.2}) (t := range 7) (f := r2 y)
        (by intro k hk; simp at hk; rcases hk with rfl | rfl <;> simp <;> omega) (fun k _ _ => r2_nonneg y k)
      rwa [Finset.sum_pair (by omega)] at this
    have hK0 : (0 : ℝ) ≤ Kof ij.1 ij.2 := by
      have hq : (0 : ℚ) ≤ Kof ij.1 ij.2 := by
        unfold Kof; split <;> norm_num [K_adj, K_diag, K_pole, K_pp]
      exact_mod_cast hq
    have a5 : -((B5b ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 5) ≤ ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha := by
      have hsq : (ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha) ^ 2
          ≤ ((B5b ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 5) ^ 2 := by
        rw [← hR2] at b5
        calc _ ≤ (B5b ij.1 ij.2 : ℝ) ^ 2 * (Rij y ij.1 ij.2 ^ 2) ^ 5 := b5
          _ = _ := by ring
      exact (abs_le.1 (abs_le_of_sq_le (mul_nonneg p5 (pow_nonneg hR0 5)) hsq)).1
    have a6 : -((B6b ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 6) ≤ ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha := by
      have hsq : (ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha) ^ 2
          ≤ ((B6b ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 6) ^ 2 := by
        rw [← hR2] at b6
        calc _ ≤ (B6b ij.1 ij.2 : ℝ) ^ 2 * (Rij y ij.1 ij.2 ^ 2) ^ 6 := b6
          _ = _ := by ring
      exact (abs_le.1 (abs_le_of_sq_le (mul_nonneg p6 (pow_nonneg hR0 6)) hsq)).1
    have r5 : Rij y ij.1 ij.2 ^ 5 ≤ T ^ 3 * (r2 y ij.1 + r2 y ij.2) := by
      rw [← hR2]; have := pow_le_pow_left₀ hR0 hRT 3; nlinarith [pow_nonneg hR0 2]
    have r6 : Rij y ij.1 ij.2 ^ 6 ≤ T ^ 4 * (r2 y ij.1 + r2 y ij.2) := by
      rw [← hR2]; have := pow_le_pow_left₀ hR0 hRT 4; nlinarith [pow_nonneg hR0 2]
    have r7 : Rij y ij.1 ij.2 ^ 7 ≤ T ^ 5 * (r2 y ij.1 + r2 y ij.2) := by
      rw [← hR2]; have := pow_le_pow_left₀ hR0 hRT 5; nlinarith [pow_nonneg hR0 2]
    nlinarith [mul_le_mul_of_nonneg_left r5 p5, mul_le_mul_of_nonneg_left r6 p6, mul_le_mul_of_nonneg_left r7 hK0]
  -- sum, then the row-maximum bounds
  have hsum := List.sum_le_sum per
  have hsplit : (pairsL.map fun ij => ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha
      + ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha - (Kof ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 7).sum
      = (pairsL.map fun ij => ev (pijd ij.1 ij.2 5) (loc (tco y) ij.1 ij.2) alpha
          + ev (pijd ij.1 ij.2 6) (loc (tco y) ij.1 ij.2) alpha).sum
        - (pairsL.map fun ij => (Kof ij.1 ij.2 : ℝ) * Rij y ij.1 ij.2 ^ 7).sum := by
    simp only [pairsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have r0 : ∀ i, 0 ≤ r2 y i := r2_nonneg y
  have row5 : (pairsL.map fun ij => (B5b ij.1 ij.2 : ℝ) * (r2 y ij.1 + r2 y ij.2)).sum
      ≤ (B5pp : ℝ) * ∑ i ∈ range 7, r2 y i := by
    simp only [pairsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, B5b, B5Tab, B5pp, List.getD_cons_zero, List.getD_cons_succ]
    push_cast
    linarith [r0 0, r0 1, r0 2, r0 3, r0 4, r0 5, r0 6]
  have row6 : (pairsL.map fun ij => (B6b ij.1 ij.2 : ℝ) * (r2 y ij.1 + r2 y ij.2)).sum
      ≤ (B6pp : ℝ) * ∑ i ∈ range 7, r2 y i := by
    simp only [pairsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, B6b, B6Tab, B6pp, List.getD_cons_zero, List.getD_cons_succ]
    push_cast
    linarith [r0 0, r0 1, r0 2, r0 3, r0 4, r0 5, r0 6]
  have row7 : (pairsL.map fun ij => (Kof ij.1 ij.2 : ℝ) * (r2 y ij.1 + r2 y ij.2)).sum
      ≤ (K7pp : ℝ) * ∑ i ∈ range 7, r2 y i := by
    simp only [pairsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Finset.sum_range_succ,
      Finset.sum_range_zero, Kof, clsIdx, clsTab, List.getD_cons_zero, List.getD_cons_succ, K7pp,
      K_adj, K_diag, K_pole, K_pp]
    push_cast
    linarith [r0 0, r0 1, r0 2, r0 3, r0 4, r0 5, r0 6]
  have hneg : (pairsL.map fun ij => -(((B5b ij.1 ij.2 : ℝ) * T ^ 3 + (B6b ij.1 ij.2 : ℝ) * T ^ 4
      + (Kof ij.1 ij.2 : ℝ) * T ^ 5) * (r2 y ij.1 + r2 y ij.2))).sum
      = -(T ^ 3 * (pairsL.map fun ij => (B5b ij.1 ij.2 : ℝ) * (r2 y ij.1 + r2 y ij.2)).sum
        + T ^ 4 * (pairsL.map fun ij => (B6b ij.1 ij.2 : ℝ) * (r2 y ij.1 + r2 y ij.2)).sum
        + T ^ 5 * (pairsL.map fun ij => (Kof ij.1 ij.2 : ℝ) * (r2 y ij.1 + r2 y ij.2)).sum) := by
    simp only [pairsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  rw [hsplit] at hsum
  rw [hneg] at hsum
  have hT3 : 0 ≤ T ^ 3 := by positivity
  have hT4 : 0 ≤ T ^ 4 := by positivity
  have hT5 : 0 ≤ T ^ 5 := by positivity
  have hK : (B5pp : ℝ) + (B6pp : ℝ) * (1 / 100) + (K7pp : ℝ) * (1 / 100) ^ 2 ≤ KK := by
    norm_num [B5pp, B6pp, K7pp, KK]
  have hT2' : ∑ i ∈ range 7, r2 y i = T ^ 2 := hT2.symm
  rw [hT2'] at row5 row6 row7
  have hT6 : T ^ 6 ≤ (1 / 100) * T ^ 5 := by nlinarith
  have hT7 : T ^ 7 ≤ (1 / 100) ^ 2 * T ^ 5 := by nlinarith [pow_le_pow_left₀ hT0 hTρ 2]
  have hB5 : (0 : ℝ) ≤ B5pp := by norm_num [B5pp]
  have hB6 : (0 : ℝ) ≤ B6pp := by norm_num [B6pp]
  have hK7 : (0 : ℝ) ≤ K7pp := by norm_num [K7pp]
  nlinarith [mul_le_mul_of_nonneg_left row5 hT3, mul_le_mul_of_nonneg_left row6 hT4,
    mul_le_mul_of_nonneg_left row7 hT5, mul_le_mul_of_nonneg_left hT6 hB6, mul_le_mul_of_nonneg_left hT7 hK7,
    mul_le_mul_of_nonneg_right hK hT5]

set_option maxHeartbeats 2000000 in
/-- **Lemma L′ in the chart** -/
theorem Lprime_core :
    (268 / 10000 : ℝ) * ∑ p ∈ range 14, wco y p ^ 2 + (200 / 10000 : ℝ) * ((25 / 4) * (sig y 0 ^ 2 + sig y 1 ^ 2) ^ 2)
      ≤ Ey y - Ey Pv := by
  -- norms
  set a := Real.sqrt ((5 / 2) * ((sig y 0) ^ 2 + (sig y 1) ^ 2)) with ha
  set b := Real.sqrt (∑ p ∈ range 14, wco y p ^ 2) with hb
  set T := Real.sqrt (∑ p ∈ range 14, tco y p ^ 2) with hT
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (5 / 2) * ((sig y 0) ^ 2 + (sig y 1) ^ 2) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = ∑ p ∈ range 14, wco y p ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun p _ => sq_nonneg _)
  have hT2 : T ^ 2 = ∑ p ∈ range 14, tco y p ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun p _ => sq_nonneg _)
  have hTab : T ^ 2 = a ^ 2 + b ^ 2 := by rw [hT2, norm_split y hg, ha2, hb2]; ring
  have hTr : T ^ 2 = ∑ i ∈ range 7, r2 y i := by rw [hT2, sum_sq_tco]
  have hTρ : T ≤ 1 / 100 := by
    have := sum_r2_le y hy hball
    refine abs_le_of_sq_le (by norm_num) ?_ |>.trans' (le_abs_self _)
    rw [hTr]; exact this
  -- w ⊥ ker
  have hker : ∀ c ∈ range 5, ∑ p ∈ range 14, (LocalCert.Kd p c).ev alpha * wco y p = 0 := by
    intro c hc
    simp only [← Kd_eq_cert]
    exact w_ker y hg (Finset.mem_range.1 hc)
  have hkerG : ∀ c ∈ range 5, ∑ p ∈ range 14, (LocalGamma1.Kd p c).ev alpha * wco y p = 0 := by
    intro c hc
    simp only [← Kd_eq_gamma]
    exact w_ker y hg (Finset.mem_range.1 hc)
  -- the expansions
  have hx : ∀ p, p < 14 → tco y p = xsub (zc y) p := fun p hp => tco_eq_xsub y p hp
  have hF2 : ev F2 (tco y) alpha = ev F2 (xsub (zc y)) alpha := ev_congr F2 14 len2 hx
  have hF3 : ev F3 (tco y) alpha = ev F3 (xsub (zc y)) alpha := ev_congr F3 14 len3 hx
  have hF4 : ev F4 (tco y) alpha = ev F4 (xsub (zc y)) alpha := by
    have hl := len4c; simp only [Bool.and_eq_true] at hl
    simp only [F4, ev_merge, ev_congr _ 14 hl.1.1.1 hx, ev_congr _ 14 hl.1.1.2 hx, ev_congr _ 14 hl.1.2 hx,
      ev_congr _ 14 hl.2 hx]
  have e2 := F2_exp (zc y)
  have e3 := F3_exp (zc y)
  have e4 := F4_exp (zc y)
  simp only [zc_w, zc_0, zc_1] at e2 e3 e4
  -- (C′)
  have hC := LocalCert.Cprime (wco y) (sig y 0) (sig y 1) hker
  -- the coupling block γ₁
  have hG := LocalGamma1.coupling_bound_a (sig y 0) (sig y 1) a ha0 ha2 (wco y) hkerG
  simp only [LocalGamma1.Qf] at hG
  -- the Bombieri blocks
  have hwsq : wsq (zc y) = b ^ 2 := by simp only [wsq, zc_w]; exact hb2.symm
  have hσ : (zc y) 0 ^ 2 + (zc y) 1 ^ 2 = (2 / 5) * a ^ 2 := by rw [zc_0, zc_1, ha2]; ring
  have b3 := bomb_F3w (zc y)
  have b4 := bomb_F4w (zc y)
  have b41 := bomb_D41 (zc y)
  have b42 := bomb_D42 (zc y)
  have b43 := bomb_D43t (zc y)
  rw [hwsq] at b3 b4 b41 b42 b43
  rw [hσ] at b41 b42 b43
  have hG2 : |ev G3_0 (zc y) alpha| ≤ (G2b : ℝ) * b ^ 3 :=
    abs_bound (by norm_num [G2b]) (pow_nonneg hb0 3) (by ring) b3 (by norm_num [G2b])
  have hC04 : |ev G4_0 (zc y) alpha| ≤ (C04 : ℝ) * b ^ 4 :=
    abs_bound (by norm_num [C04]) (pow_nonneg hb0 4) (by ring) b4 (by norm_num [C04])
  have h41 : |evDP D41 (zc y) alpha| ≤ (CQ13 : ℝ) * (a * b ^ 3) :=
    abs_bound (B := (c13 : ℝ) * (2 / 5)) (by norm_num [CQ13]) (mul_nonneg ha0 (pow_nonneg hb0 3)) rfl
      (b41.trans (le_of_eq (by ring))) (by norm_num [c13, CQ13])
  have h42 : |evDP D42 (zc y) alpha| ≤ (CQ22 : ℝ) * (a ^ 2 * b ^ 2) :=
    abs_bound (B := (c22 : ℝ) * (4 / 25)) (by norm_num [CQ22]) (mul_nonneg (pow_nonneg ha0 2) (pow_nonneg hb0 2)) rfl
      (b42.trans (le_of_eq (by ring))) (by norm_num [c22, CQ22])
  have h43 : |evDP D43t (zc y) alpha| ≤ (D1x4 : ℝ) * (a ^ 3 * b) :=
    abs_bound (B := (c6 : ℝ) * (8 / 125)) (by norm_num [D1x4]) (mul_nonneg (pow_nonneg ha0 3) hb0) rfl
      (b43.trans (le_of_eq (by ring))) (by norm_num [c6, D1x4])
  -- the kernel components of ∇F₄(s) vanish against w
  have hproj : ∑ c ∈ range 5, ev (qb c) (zc y) alpha * ∑ p ∈ range 14, (LocalFrames.Kd p c).ev alpha * wco y p = 0 :=
    Finset.sum_eq_zero fun c hc => by rw [w_ker y hg (Finset.mem_range.1 hc)]; ring
  rw [hproj] at e4
  -- the quadratic form conventions of `Cprime`/`Qf`
  have qH : ∑ p ∈ range 14, ∑ q ∈ range 14, (LocalCert.Hd p q).ev alpha * (wco y p * wco y q)
      = ∑ p ∈ range 14, ∑ q ∈ range 14, wco y p * (LocalCert.Hd p q).ev alpha * wco y q :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have qA : ∀ al, ∑ p ∈ range 14, ∑ q ∈ range 14, (LocalGamma1.Ad al p q).ev alpha * (wco y p * wco y q)
      = ∑ p ∈ range 14, ∑ q ∈ range 14, wco y p * (LocalGamma1.Ad al p q).ev alpha * wco y q := fun al =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have qG : (sig y 0) ^ 2 * ∑ p ∈ range 14, (LocalCert.Gd p 0).ev alpha * wco y p
      + (sig y 0) * (sig y 1) * ∑ p ∈ range 14, (LocalCert.Gd p 1).ev alpha * wco y p
      + (sig y 1) ^ 2 * ∑ p ∈ range 14, (LocalCert.Gd p 2).ev alpha * wco y p
      = ∑ p ∈ range 14, wco y p * ∑ k ∈ range 3, (LocalCert.Gd p k).ev alpha * LocalCert.msig (sig y 0) (sig y 1) k := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Finset.sum_range_succ, LocalCert.msig] <;> ring
  rw [qH] at e2
  rw [qA 0, qA 1, qG] at e3
  -- the CQ step
  have hCQ := cq_step (a := a) (b := b)
  -- assemble the energy lower bound
  have hE := energy_step y hy hg hball
  have hWs := W_step y hy hg hball
  have hTs := T_step y hy hg hball
  have hRs := R_step y hy hg hball T hT0 hTr hTρ
  have hE' : ev F2 (tco y) alpha + ev F3 (tco y) alpha + ev F4 (tco y) alpha - (KK : ℝ) * T ^ 5 ≤ Ey y - Ey Pv := by
    linarith
  rw [hF2, hF3, hF4, e2, e3, e4] at hE'
  -- the scalar argument
  have ha4 : a ^ 4 = (25 / 4) * ((sig y 0) ^ 2 + (sig y 1) ^ 2) ^ 2 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha2]; ring
  have hP : (1 / 16) * b ^ 2 + (29 / 500) * a ^ 4
      - (3 * ((LocalGamma1.G1x3 : ℝ) / 3) * a * b ^ 2 + (G2b : ℝ) * b ^ 3 + 4 * ((D1x4 : ℝ) / 4) * a ^ 3 * b
        + (CQ : ℝ) * (a ^ 2 + b ^ 2) * b ^ 2 + (KK : ℝ) * T ^ 5) ≤ Ey y - Ey Pv := by
    rw [ha4]
    rw [← hb2] at hC hG
    have l1 := (abs_le.1 hG).1
    have l2 := (abs_le.1 hG2).1
    have l3 := (abs_le.1 hC04).1
    have l4 := (abs_le.1 h41).1
    have l5 := (abs_le.1 h42).1
    have l6 := (abs_le.1 h43).1
    linarith
  have := LocalScalar.scalar_param ha0 hb0 hT0 hTab hTρ (G1 := (LocalGamma1.G1x3 : ℝ) / 3) (G2 := G2b)
    (D1 := (D1x4 : ℝ) / 4) (CQ := CQ) (KK := KK) (cw := 268 / 10000) (cs := 200 / 10000)
    (by norm_num [LocalGamma1.G1x3]) (by norm_num [G2b]) (by norm_num [D1x4]) (by norm_num [CQ]) (by norm_num [KK])
    le_rfl le_rfl le_rfl le_rfl le_rfl
    (by norm_num [LocalGamma1.G1x3, G2b, D1x4, CQ, KK]) (by norm_num [D1x4, KK]) hP
  rw [hb2, ha4] at this
  linarith

/-- **Equality case in the chart**: `Ey y = Ey Pv` forces `y = Pv`. -/
theorem Lprime_core_eq (heq : Ey y = Ey Pv) : ∀ i, i < 7 → y i = Pv i := by
  have h := Lprime_core y hy hg hball
  rw [heq, sub_self] at h
  have hw : ∑ p ∈ range 14, wco y p ^ 2 = 0 := by
    have h1 : 0 ≤ ∑ p ∈ range 14, wco y p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
    have h2 : 0 ≤ (sig y 0 ^ 2 + sig y 1 ^ 2) ^ 2 := by positivity
    nlinarith
  have hs : sig y 0 ^ 2 + sig y 1 ^ 2 = 0 := by
    have h1 : 0 ≤ ∑ p ∈ range 14, wco y p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
    have h2 : 0 ≤ sig y 0 ^ 2 + sig y 1 ^ 2 := by positivity
    have h3 : (sig y 0 ^ 2 + sig y 1 ^ 2) ^ 2 = 0 := by nlinarith
    exact pow_eq_zero_iff (by norm_num) |>.1 h3
  have hx : ∑ p ∈ range 14, tco y p ^ 2 = 0 := by rw [norm_split y hg, hw, hs]; ring
  have hr : ∀ i ∈ range 7, r2 y i = 0 := by
    have := sum_sq_tco y
    rw [hx] at this
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => r2_nonneg y i).1 this.symm
  intro i hi
  have hri := hr i (Finset.mem_range.2 hi)
  have hx1 : x1 y i = 0 := by unfold r2 at hri; nlinarith [sq_nonneg (x1 y i), sq_nonneg (x2 y i)]
  have hx2 : x2 y i = 0 := by unfold r2 at hri; nlinarith [sq_nonneg (x1 y i), sq_nonneg (x2 y i)]
  have hν : nu y i = 0 := by
    have h1 := unit_rel y hi (hy i hi)
    obtain ⟨h2a, h2b, -, -⟩ := chart_bounds y hy hball hi
    rw [hri] at h1
    nlinarith
  funext k
  rw [decomp y hi k]
  simp [tv, hx1, hx2, hν]

end core

/-! ## The statement in `R3 = EuclideanSpace ℝ (Fin 3)` -/

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- the bipyramid with coordinates in K -/
noncomputable def Pbip : Fin 7 → R3 := fun i => !₂[Pv i 0, Pv i 1, Pv i 2]

/-- Logarithmic energy `∑_{i<j} −log ‖x i − x j‖` (as in `LogN7/Challenge.lean`). -/
noncomputable def logEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, -Real.log ‖x i - x j‖

/-- `Fin 7 → R3` read as `ℕ → V` -/
noncomputable def toV (y : Fin 7 → R3) : ℕ → V := fun k => if h : k < 7 then (fun c => y ⟨k, h⟩ c) else 0

lemma toV_apply (y : Fin 7 → R3) (i : Fin 7) (c : Fin 3) : toV y i c = y i c := by
  simp [toV, i.isLt]

lemma Pbip_apply (i : Fin 7) (c : Fin 3) : Pbip i c = Pv i c := by
  simp only [Pbip]; fin_cases c <;> rfl

lemma toV_Pbip : ∀ k, k < 7 → toV Pbip k = Pv k := by
  intro k hk; funext c; simp [toV, hk, Pbip_apply]

lemma norm_sq_eq_dot (v : R3) : ‖v‖ ^ 2 = dot (fun c => v c) (fun c => v c) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [dot, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, pow_two]

lemma norm_sub_sq (y : Fin 7 → R3) (i j : Fin 7) :
    ‖y i - y j‖ ^ 2 = dot (toV y i - toV y j) (toV y i - toV y j) := by
  rw [norm_sq_eq_dot]
  simp [dot, toV_apply, Pi.sub_apply]

lemma norm_sub_P_sq (y : Fin 7 → R3) (i : Fin 7) : ‖y i - Pbip i‖ ^ 2 = dot (hv (toV y) i) (hv (toV y) i) := by
  rw [norm_sq_eq_dot]
  simp [dot, hv, toV_apply, Pbip_apply]

/-- `logEnergy` in the chart world (for unit `y` with `⟪yᵢ,yⱼ⟫ < 1`, i.e. distinct points) -/
lemma logEnergy_eq (y : Fin 7 → R3) (hpos : ∀ i j : Fin 7, i < j → 0 < dot (toV y i - toV y j) (toV y i - toV y j)) :
    logEnergy y = Ey (toV y) := by
  unfold logEnergy Ey
  have e1 : ∀ i : Fin 7, ∑ j ∈ Finset.Ioi i, -Real.log ‖y i - y j‖
      = ∑ j : Fin 7, if (i : ℕ) < (j : ℕ) then -(1 / 2) * Real.log (dot (toV y i - toV y j) (toV y i - toV y j))
          else 0 := by
    intro i
    rw [← Finset.sum_filter]
    have : Finset.Ioi i = Finset.univ.filter fun j : Fin 7 => (i : ℕ) < (j : ℕ) := by
      ext j; simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.lt_def
    rw [this]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i < j := Fin.lt_def.2 (Finset.mem_filter.1 hj).2
    have h := hpos i j hij
    rw [← norm_sub_sq] at h ⊢
    have hn : 0 < ‖y i - y j‖ := by nlinarith [norm_nonneg (y i - y j)]
    rw [Real.log_pow]; push_cast; ring
  simp only [e1]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range 7,
      if i < j then -(1 / 2) * Real.log (dot (toV y i - toV y j) (toV y i - toV y j)) else 0) 7]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j =>
      if (i : ℕ) < j then -(1 / 2) * Real.log (dot (toV y i - toV y j) (toV y i - toV y j)) else 0) 7]

/-- the hypotheses in the two worlds -/
lemma hyps_toV (y : Fin 7 → R3) (hy : ∀ i, ‖y i‖ = 1)
    (hg : ∀ a b : Fin 3, ∑ i, Pbip i a * y i b = ∑ i, Pbip i b * y i a)
    (hρ : ∑ i, ‖y i - Pbip i‖ ^ 2 ≤ (1 / 100) ^ 2) :
    (∀ k, k < 7 → dot (toV y k) (toV y k) = 1) ∧
    (∀ a b : Fin 3, ∑ i ∈ range 7, Pv i a * toV y i b = ∑ i ∈ range 7, Pv i b * toV y i a) ∧
    ∑ k ∈ range 7, dot (hv (toV y) k) (hv (toV y) k) ≤ (1 / 100) ^ 2 := by
  refine ⟨fun k hk => ?_, fun a b => ?_, ?_⟩
  · have := norm_sq_eq_dot (y ⟨k, hk⟩)
    rw [hy, one_pow] at this
    simp only [toV, dif_pos hk]
    exact this.symm
  · have := hg a b
    simp only [Pbip_apply] at this
    rw [← Fin.sum_univ_eq_sum_range (fun i => Pv i a * toV y i b) 7,
      ← Fin.sum_univ_eq_sum_range (fun i => Pv i b * toV y i a) 7]
    simpa [toV_apply] using this
  · rw [← Fin.sum_univ_eq_sum_range (fun k => dot (hv (toV y) k) (hv (toV y) k)) 7]
    refine le_trans (le_of_eq ?_) hρ
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_sub_P_sq]

lemma pos_pairs (y : Fin 7 → R3) (hy : ∀ k, k < 7 → dot (toV y k) (toV y k) = 1)
    (hball : ∑ k ∈ range 7, dot (hv (toV y) k) (hv (toV y) k) ≤ (1 / 100) ^ 2) :
    ∀ i j : Fin 7, i < j → 0 < dot (toV y i - toV y j) (toV y i - toV y j) := by
  intro i j hij
  have hne : (i : ℕ) ≠ j := fun h => absurd (Fin.ext h) (ne_of_lt hij)
  have hlt := inner_lt_one (toV y) i.isLt j.isLt hne hy hball
  have hi := hy i i.isLt
  have hj := hy j j.isLt
  have e : dot (toV y i - toV y j) (toV y i - toV y j) = 2 - 2 * dot (toV y i) (toV y j) := by
    simp only [dot, Pi.sub_apply] at *; linarith
  rw [e]; linarith

lemma pos_pairs_P : ∀ i j : Fin 7, i < j → 0 < dot (toV Pbip i - toV Pbip j) (toV Pbip i - toV Pbip j) := by
  intro i j hij
  have hne : (i : ℕ) ≠ j := fun h => absurd (Fin.ext h) (ne_of_lt hij)
  obtain ⟨hg, -, -, hg31, -, -⟩ := pair_consts (i := i) (j := j) i.isLt j.isLt hne
  obtain ⟨hPi, -, -, -, -, -, -⟩ := frame_facts (i := i) i.isLt
  obtain ⟨hPj, -, -, -, -, -, -⟩ := frame_facts (i := j) j.isLt
  rw [toV_Pbip i i.isLt, toV_Pbip j j.isLt]
  have e : dot (Pv i - Pv j) (Pv i - Pv j) = 2 - 2 * dot (Pv i) (Pv j) := by
    simp only [dot, Pi.sub_apply] at *; linarith
  rw [e, hg]; linarith

/-- the soft and stiff coordinates of `y` (design §1) -/
noncomputable def sigR (y : Fin 7 → R3) (al : ℕ) : ℝ := sig (toV y) al
noncomputable def wcoR (y : Fin 7 → R3) (p : ℕ) : ℝ := wco (toV y) p

/-- **Lemma L′** (log, Lean form): `0.0268 |w|² + 0.0200 |s|⁴ ≤ E(y) − E(P)`. -/
theorem Lprime {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1)
    (hg : ∀ a b : Fin 3, ∑ i, Pbip i a * y i b = ∑ i, Pbip i b * y i a)
    (hρ : ∑ i, ‖y i - Pbip i‖ ^ 2 ≤ (1 / 100) ^ 2) :
    (268 / 10000 : ℝ) * ∑ p ∈ range 14, wcoR y p ^ 2
      + (200 / 10000 : ℝ) * ((25 / 4) * (sigR y 0 ^ 2 + sigR y 1 ^ 2) ^ 2)
      ≤ logEnergy y - logEnergy Pbip := by
  obtain ⟨h1, h2, h3⟩ := hyps_toV y hy hg hρ
  rw [logEnergy_eq y (pos_pairs y h1 h3), logEnergy_eq Pbip pos_pairs_P]
  have hE : Ey (toV Pbip) = Ey Pv := by
    unfold Ey
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [toV_Pbip i (Finset.mem_range.1 hi), toV_Pbip j (Finset.mem_range.1 hj)]
  rw [hE]
  exact Lprime_core (toV y) h1 h2 h3

/-- `E(P) ≤ E(y)` under the same hypotheses -/
theorem Lprime_nonneg {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1)
    (hg : ∀ a b : Fin 3, ∑ i, Pbip i a * y i b = ∑ i, Pbip i b * y i a)
    (hρ : ∑ i, ‖y i - Pbip i‖ ^ 2 ≤ (1 / 100) ^ 2) : logEnergy Pbip ≤ logEnergy y := by
  have h := Lprime hy hg hρ
  have h1 : 0 ≤ ∑ p ∈ range 14, wcoR y p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have h2 : 0 ≤ (sigR y 0 ^ 2 + sigR y 1 ^ 2) ^ 2 := by positivity
  linarith

/-- **Equality case**: `E(y) = E(P)` forces `y = Pbip`. -/
theorem Lprime_eq {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1)
    (hg : ∀ a b : Fin 3, ∑ i, Pbip i a * y i b = ∑ i, Pbip i b * y i a)
    (hρ : ∑ i, ‖y i - Pbip i‖ ^ 2 ≤ (1 / 100) ^ 2) (heq : logEnergy y = logEnergy Pbip) : y = Pbip := by
  obtain ⟨h1, h2, h3⟩ := hyps_toV y hy hg hρ
  rw [logEnergy_eq y (pos_pairs y h1 h3), logEnergy_eq Pbip pos_pairs_P] at heq
  have hE : Ey (toV Pbip) = Ey Pv := by
    unfold Ey
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [toV_Pbip i (Finset.mem_range.1 hi), toV_Pbip j (Finset.mem_range.1 hj)]
  rw [hE] at heq
  have hall := Lprime_core_eq (toV y) h1 h2 h3 heq
  funext i
  ext c
  have := congrFun (hall i i.isLt) c
  rw [toV_apply] at this
  rw [this, Pbip_apply]

/-! ## The handoff form (sup radius 1/300) -/

lemma logEnergy_isometry (g : R3 ≃ₗᵢ[ℝ] R3) (y : Fin 7 → R3) : logEnergy (fun i => g (y i)) = logEnergy y := by
  unfold logEnergy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_sub, g.norm_map]

/-- **Handoff** (the gauge step `exists_gauge` of the upstream Coulomb proof is a hypothesis here;
`LocalHandoff.lean` discharges it): every unit configuration within sup distance `1/300` of the bipyramid has at least its
energy, with equality only on `O(3)·P`. -/
theorem pent_local_min_sup_log
    (gauge : ∀ y : Fin 7 → R3, ∃ g : R3 ≃ₗᵢ[ℝ] R3,
      (∀ a b : Fin 3, ∑ i, Pbip i a * (g (y i)) b = ∑ i, Pbip i b * (g (y i)) a) ∧
      ∑ i, ‖g (y i) - Pbip i‖ ^ 2 ≤ ∑ i, ‖y i - Pbip i‖ ^ 2)
    {z : Fin 7 → R3} (hz : ∀ i, ‖z i‖ = 1) (hclose : ∀ i, ‖z i - Pbip i‖ ≤ 1 / 300) :
    logEnergy Pbip ≤ logEnergy z ∧
      (logEnergy z = logEnergy Pbip → ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, z i = g (Pbip i)) := by
  obtain ⟨g, hg1, hg2⟩ := gauge z
  set y : Fin 7 → R3 := fun i => g (z i) with hydef
  have hy : ∀ i, ‖y i‖ = 1 := fun i => by rw [hydef]; simp [g.norm_map, hz]
  have hρ : ∑ i, ‖y i - Pbip i‖ ^ 2 ≤ (1 / 100) ^ 2 := by
    refine hg2.trans ?_
    calc ∑ i, ‖z i - Pbip i‖ ^ 2 ≤ ∑ _i : Fin 7, (1 / 300 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hclose i) 2
      _ = 7 * (1 / 300) ^ 2 := by simp
      _ ≤ (1 / 100) ^ 2 := by norm_num
  have hEy : logEnergy y = logEnergy z := logEnergy_isometry g z
  refine ⟨?_, fun heq => ?_⟩
  · rw [← hEy]; exact Lprime_nonneg hy hg1 hρ
  · have := Lprime_eq hy hg1 hρ (by rw [hEy, heq])
    refine ⟨g.symm, fun i => ?_⟩
    have hi := congrFun this i
    simp only [hydef] at hi
    rw [← hi]; simp

end LocalMain

#print axioms LocalMain.Lprime
#print axioms LocalMain.Lprime_eq
#print axioms LocalMain.pent_local_min_sup_log
