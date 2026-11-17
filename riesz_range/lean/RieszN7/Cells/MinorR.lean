import RieszN7.Core.Bern2
import RieszN7.Core.TaylorT
import RieszN7.Core.PsiConcave
import RieszN7.Core.ExpModel

/-!
# `RieszN7.Cells.MinorR` — kernel-computed minorant boxes for the cell pieces (LEAN_PLAN_range.md §3.1.3)

Hand-written generic module (Phase 2a, 2026-11-07; private, AI-written, not reviewed).

* **Horner lists.** `hor f c j r` (1-D) and `hor2 f c j r` (2-D) are integer polynomials computed by the kernel with
  `peval (hor f c j r) = c^r (j+1)…(j+r) · horR (peval ∘ f) c j r`, where `horR fr c j 0 = 1`,
  `horR fr c j (r+1) = 1 + fr j / (c (j+1)) · horR fr c (j+1) r`.  `horR_eq_sum` gives the sum form
  `Σ_{k ≤ r} (Π_{i<k} fr (j+i)) / (c^k Π_{i<k} (j+1+i))`.
  - Taylor polynomial of `phiS` at `g` (`fr j = (s + 2j)(t − g)`, `c = 2 − 2g`): `horR … 0 n = Σ_k cS s k y^k`
    (`taylor_eq_horR`), so `phiS s t ≥ phiS s g · horR …` for `t ≥ g` (`phiS_ge_horR`).
  - exponential series (`fr j = z`): `horR … 0 r = Σ_{i ≤ r} z^i / i!` (`expsum_eq_horR`).
* **Boxes.** `box2_sound`: one `bern2OK` decide of the kernel-built polynomial
  `cA · M(s) · V(s,t) − cB · Hq(s,t)` gives `Hq/DH ≤ phiS s t` on a box `[s₀,s₁] × [t₀,t₁)` with `t₀ ≥ g`, from a lower
  model `M ≤ phiS · g` in `s`.  `box1_sound`: the same at a fixed rational `s = p/q` (node chains), one 1-D Möbius decide.
* **Models.** `model_lower_pos` / `model_lower_neg`: lower polynomial models of `c^(-s/2)` on an s-interval (from
  `ExpModel.model_of_encl`; `log c ≥ 0` resp. `≤ 0`), packaged as integer lists.  `model_upper_pos`: upper model.
* **Concavity region.** `interp_le_of_nodes`: for `t ≤ 1/2`, node facts at `s = a, b` give the interpolated minorant
  for all `s ∈ [a, b]` (`psi_sub_affine_ge_min`).
-/

open Finset LogLean.Minor RieszN7.Bern2

namespace RieszN7.MinorR

/-! ## 1. Horner recursion, real side -/

/-- `Π_{i<r} (j+1+i)` as a natural number. -/
def rf (j r : ℕ) : ℕ := ∏ i ∈ range r, (j + 1 + i)

theorem rf_succ (j r : ℕ) : rf j (r + 1) = (j + 1) * rf (j + 1) r := by
  unfold rf
  rw [prod_range_succ']
  simp only [add_zero]
  rw [mul_comm]
  congr 1
  exact prod_congr rfl fun i _ => by ring

theorem rf_pos (j r : ℕ) : 0 < rf j r := by
  unfold rf; exact prod_pos fun i _ => by omega

theorem rf_zero_eq_factorial (r : ℕ) : rf 0 r = r.factorial := by
  induction r with
  | zero => rfl
  | succ r ih => unfold rf at ih ⊢; rw [prod_range_succ, ih, Nat.factorial_succ]; ring

/-- Real Horner value. -/
noncomputable def horR (fr : ℕ → ℝ) (c : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | j, r + 1 => 1 + fr j / (c * ((j : ℝ) + 1)) * horR fr c (j + 1) r

theorem horR_eq_sum (fr : ℕ → ℝ) (c : ℝ) (hc : c ≠ 0) :
    ∀ r j, horR fr c j r =
      ∑ k ∈ range (r + 1), (∏ i ∈ range k, fr (j + i)) / (c ^ k * (rf j k : ℝ)) := by
  intro r
  induction r with
  | zero => intro j; simp [horR, rf]
  | succ r ih =>
    intro j
    rw [horR, ih (j + 1), sum_range_succ' _ (r + 1)]
    simp only [prod_range_zero, pow_zero, rf, Nat.cast_one, mul_one, div_one]
    rw [add_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    have hp : ∏ i ∈ range (k + 1), fr (j + i) = fr j * ∏ i ∈ range k, fr (j + 1 + i) := by
      rw [prod_range_succ']; simp only [add_zero]; rw [mul_comm]
      congr 1; exact prod_congr rfl fun i _ => by ring_nf
    have hq : (∏ i ∈ range (k + 1), (j + 1 + i) : ℕ) = (j + 1) * ∏ i ∈ range k, (j + 1 + 1 + i) := by
      rw [prod_range_succ']; simp only [add_zero]; rw [mul_comm]
      congr 1; exact prod_congr rfl fun i _ => by ring
    rw [hp, hq]
    push_cast
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hr : (∏ i ∈ range k, ((j : ℝ) + 1 + 1 + (i : ℝ))) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => by positivity
    field_simp
    ring

theorem horR_pos (fr : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ j, 0 ≤ fr j) :
    ∀ r j, 1 ≤ horR fr c j r := by
  intro r
  induction r with
  | zero => intro j; simp [horR]
  | succ r ih =>
    intro j
    rw [horR]
    have h1 : 0 ≤ fr j / (c * ((j : ℝ) + 1)) := div_nonneg (hf j) (by positivity)
    nlinarith [ih (j + 1)]

/-! ## 2. Horner recursion, integer lists -/

/-- 1-D Horner list: `[c^(r+1) rf j (r+1)] + f j · hor (j+1) r`. -/
def hor (f : ℕ → List ℤ) (c : ℤ) : ℕ → ℕ → List ℤ
  | _, 0 => [1]
  | j, r + 1 => padd [c ^ (r + 1) * (rf j (r + 1) : ℤ)] (pmul (f j) (hor f c (j + 1) r))

theorem peval_hor (f : ℕ → List ℤ) (c : ℤ) (hc : (c : ℝ) ≠ 0) (x : ℝ) :
    ∀ r j, peval (hor f c j r) x
      = (c : ℝ) ^ r * (rf j r : ℝ) * horR (fun i => peval (f i) x) c j r := by
  intro r
  induction r with
  | zero => intro j; simp [hor, horR, rf, peval]
  | succ r ih =>
    intro j
    rw [hor, peval_padd, peval_pmul, ih (j + 1), horR, rf_succ]
    simp only [peval, mul_zero, add_zero]
    push_cast
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- 2-D Horner list. -/
def hor2 (f : ℕ → List (List ℤ)) (c : ℤ) : ℕ → ℕ → List (List ℤ)
  | _, 0 => [[1]]
  | j, r + 1 => padd2 [[c ^ (r + 1) * (rf j (r + 1) : ℤ)]] (mul2 (f j) (hor2 f c (j + 1) r))

theorem peval2_const (a : ℤ) (s t : ℝ) : peval2 [[a]] s t = a := by
  simp [peval2, peval]

theorem peval2_hor2 (f : ℕ → List (List ℤ)) (c : ℤ) (hc : (c : ℝ) ≠ 0) (s t : ℝ) :
    ∀ r j, peval2 (hor2 f c j r) s t
      = (c : ℝ) ^ r * (rf j r : ℝ) * horR (fun i => peval2 (f i) s t) c j r := by
  intro r
  induction r with
  | zero => intro j; simp [hor2, horR, rf, peval2_const]
  | succ r ih =>
    intro j
    rw [hor2, peval2_padd2, peval2_mul2, ih (j + 1), horR, rf_succ, peval2_const]
    push_cast
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-! ## 3. The Taylor minorant in Horner form -/

/-- Taylor multiplier `(s + 2j)(gd t − gn)` (2-D). -/
def tmul2 (gn : ℤ) (gd : ℕ) (j : ℕ) : List (List ℤ) := outer [2 * (j : ℤ), 1] [-gn, (gd : ℤ)]

theorem peval2_tmul2 (gn : ℤ) (gd : ℕ) (j : ℕ) (s t : ℝ) :
    peval2 (tmul2 gn gd j) s t = (s + 2 * j) * (gd * t - gn) := by
  simp only [tmul2, peval2_outer, peval]; push_cast; ring

/-- Taylor multiplier at the fixed rational `s = p/q` (times `q`): `(p + 2jq)(gd t − gn)` (1-D). -/
def tmul1 (p q : ℕ) (gn : ℤ) (gd : ℕ) (j : ℕ) : List ℤ :=
  pscale ((p : ℤ) + 2 * (j : ℤ) * q) [-gn, (gd : ℤ)]

theorem peval_tmul1 (p q : ℕ) (gn : ℤ) (gd : ℕ) (j : ℕ) (t : ℝ) :
    peval (tmul1 p q gn gd j) t = ((p : ℝ) + 2 * j * q) * (gd * t - gn) := by
  simp only [tmul1, peval_pscale, peval]; push_cast; ring

/-- `Σ_{k≤n} cS s k y^k` with `y = (t − g)/(2 − 2g)` equals the Horner value with `fr j = (s+2j)(t − g)`. -/
theorem taylor_eq_horR (g : ℝ) (hg : g < 1) (n : ℕ) (s t : ℝ) :
    ∑ k ∈ range (n + 1), cS s k * ((t - g) / (2 - 2 * g)) ^ k
      = horR (fun j => (s + 2 * j) * (t - g)) (2 - 2 * g) 0 n := by
  have hc : (2 - 2 * g) ≠ 0 := by intro h; linarith
  rw [horR_eq_sum _ _ hc]
  refine sum_congr rfl fun k _ => ?_
  rw [rf_zero_eq_factorial]
  unfold cS
  simp only [zero_add]
  rw [prod_mul_distrib, prod_const, card_range, div_pow]
  field_simp

/-- **The Taylor minorant, Horner form.** -/
theorem phiS_ge_horR {g : ℝ} (hg : g < 1) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (h1 : g ≤ t) (h2 : t < 1) :
    phiS s g * horR (fun j => (s + 2 * j) * (t - g)) (2 - 2 * g) 0 n ≤ phiS s t := by
  have := phiS_ge_taylor_right hg n hs h1 h2
  unfold taylorT at this
  rwa [taylor_eq_horR g hg n s t] at this

theorem horR_taylor_pos {g : ℝ} (hg : g < 1) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (h1 : g ≤ t) :
    1 ≤ horR (fun j => (s + 2 * j) * (t - g)) (2 - 2 * g) 0 n :=
  horR_pos _ _ (by linarith) (fun j => mul_nonneg (by positivity) (by linarith)) n 0

/-- The 2-D Taylor list: `peval2 = (2gd − 2gn)^n n! · Σ_k cS s k y^k`. -/
def tayl2 (gn : ℤ) (gd : ℕ) (n : ℕ) : List (List ℤ) := hor2 (tmul2 gn gd) (2 * gd - 2 * gn) 0 n

theorem peval2_tayl2 (gn : ℤ) (gd : ℕ) (hgd : 0 < gd) (hg : gn < gd) (n : ℕ) (s t : ℝ) :
    peval2 (tayl2 gn gd n) s t
      = ((2 * gd - 2 * gn : ℤ) : ℝ) ^ n * (n.factorial : ℝ)
        * horR (fun j => (s + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) 0 n := by
  have hgdR : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hc : ((2 * gd - 2 * gn : ℤ) : ℝ) ≠ 0 := by
    have : (gn : ℝ) < gd := by exact_mod_cast hg
    push_cast; intro h; linarith
  unfold tayl2
  rw [peval2_hor2 _ _ hc, rf_zero_eq_factorial]
  congr 1
  -- rescale the Horner value: c = gd (2 − 2g), fr j = gd (s+2j)(t − g)
  have key : ∀ r j, horR (fun i => peval2 (tmul2 gn gd i) s t) ((2 * gd - 2 * gn : ℤ) : ℝ) j r
      = horR (fun j => (s + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) j r := by
    intro r
    induction r with
    | zero => intro j; simp [horR]
    | succ r ih =>
      intro j
      rw [horR, horR, ih (j + 1), peval2_tmul2]
      congr 2
      push_cast
      field_simp
  exact key n 0

/-- The 1-D Taylor list at `s = p/q`: `peval = (q (2gd − 2gn))^n n! · Σ_k cS (p/q) k y^k`. -/
def tayl1 (p q : ℕ) (gn : ℤ) (gd : ℕ) (n : ℕ) : List ℤ :=
  hor (tmul1 p q gn gd) ((q : ℤ) * (2 * gd - 2 * gn)) 0 n

theorem peval_tayl1 (p q : ℕ) (hq : 0 < q) (gn : ℤ) (gd : ℕ) (hgd : 0 < gd) (hg : gn < gd) (n : ℕ) (t : ℝ) :
    peval (tayl1 p q gn gd n) t
      = (((q : ℤ) * (2 * gd - 2 * gn) : ℤ) : ℝ) ^ n * (n.factorial : ℝ)
        * horR (fun j => ((p : ℝ) / q + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) 0 n := by
  have hgdR : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (((q : ℤ) * (2 * gd - 2 * gn) : ℤ) : ℝ) ≠ 0 := by
    have : (gn : ℝ) < gd := by exact_mod_cast hg
    push_cast; intro h
    have : (q : ℝ) * (2 * gd - 2 * gn) > 0 := mul_pos hqR (by linarith)
    linarith
  unfold tayl1
  rw [peval_hor _ _ hc, rf_zero_eq_factorial]
  congr 1
  have key : ∀ r j, horR (fun i => peval (tmul1 p q gn gd i) t) (((q : ℤ) * (2 * gd - 2 * gn) : ℤ) : ℝ) j r
      = horR (fun j => ((p : ℝ) / q + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) j r := by
    intro r
    induction r with
    | zero => intro j; simp [horR]
    | succ r ih =>
      intro j
      rw [horR, horR, ih (j + 1), peval_tmul1]
      congr 2
      push_cast
      field_simp
  exact key n 0

/-! ## 4. Boxes -/

/-- A polynomial in `s` as a bivariate list (constant in `t`). -/
def col (m : List ℤ) : List (List ℤ) := m.map (fun c => [c])

theorem peval2_col (m : List ℤ) (s t : ℝ) : peval2 (col m) s t = peval m s := by
  induction m with
  | nil => simp [col, peval2, peval]
  | cons c cs ih => simp only [col, List.map_cons, peval2, peval] at ih ⊢; rw [ih]; ring

/-- The polynomial checked on a 2-D box: `cA · M(s) · V(s,t) − cB · Hq(s,t)`. -/
def boxPoly (mq : List ℤ) (gn : ℤ) (gd n : ℕ) (hq : List (List ℤ)) (cA cB : ℕ) : List (List ℤ) :=
  padd2 ((mul2 (col mq) (tayl2 gn gd n)).map (pscale (cA : ℤ))) (hq.map (pscale (-(cB : ℤ))))

theorem peval2_boxPoly (mq : List ℤ) (gn : ℤ) (gd n : ℕ) (hq : List (List ℤ)) (cA cB : ℕ) (s t : ℝ) :
    peval2 (boxPoly mq gn gd n hq cA cB) s t
      = cA * (peval mq s * peval2 (tayl2 gn gd n) s t) - cB * peval2 hq s t := by
  unfold boxPoly
  rw [peval2_padd2, peval2_map_pscale, peval2_map_pscale, peval2_mul2, peval2_col]
  push_cast; ring

/-- **2-D box.** -/
theorem box2_sound (mq : List ℤ) (Dm : ℕ) (gn : ℤ) (gd n : ℕ) (hq : List (List ℤ)) (DH cA cB : ℕ)
    (As Bs : ℤ) (Ds : ℕ) (At Bt : ℤ) (Dt : ℕ) (mt : ℕ)
    (hgd : 0 < gd) (hg : gn < gd) (hDm : 0 < Dm) (hDH : 0 < DH) (hcB : 0 < cB) (hDs : 0 < Ds) (hDt : 0 < Dt)
    (hAB : As < Bs) (hAs : 0 ≤ As) (hgt : gn * Dt ≤ At * gd) (hBt : Bt ≤ Dt)
    (hK : (cA : ℤ) * Dm * ((2 * gd - 2 * gn) ^ n * n.factorial) = cB * DH)
    (hchk : bern2OK As Bs Ds At Bt Dt mt (boxPoly mq gn gd n hq cA cB) = true)
    (hM : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → peval mq s / Dm ≤ phiS s (gn / gd)) :
    ∀ s t, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → (At : ℝ) / Dt ≤ t → t < (Bt : ℝ) / Dt →
      peval2 hq s t / DH ≤ phiS s t := by
  intro s t hs0 hs1 ht0 ht1
  have hgdR : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hDtR : (0 : ℝ) < Dt := by exact_mod_cast hDt
  have hDsR : (0 : ℝ) < Ds := by exact_mod_cast hDs
  have hgR : (gn : ℝ) / gd < 1 := by
    rw [div_lt_one hgdR]; exact_mod_cast hg
  have hsnn : 0 ≤ s := le_trans (div_nonneg (by exact_mod_cast hAs) hDsR.le) hs0
  have hgt' : (gn : ℝ) / gd ≤ t := by
    refine le_trans ?_ ht0
    rw [div_le_div_iff₀ hgdR hDtR]; exact_mod_cast hgt
  have ht1' : t < 1 := by
    refine lt_of_lt_of_le ht1 ?_
    rw [div_le_one hDtR]; exact_mod_cast hBt
  have hP := bern2_sound As Bs Ds At Bt Dt mt _ hDs hDt hAB hchk hs0 hs1 ht0 ht1
  rw [peval2_boxPoly, peval2_tayl2 gn gd hgd hg] at hP
  set T := horR (fun j => (s + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) 0 n with hT
  have hT1 : 1 ≤ T := horR_taylor_pos hgR n hsnn hgt'
  have hKR : (cA : ℝ) * Dm * ((((2 * gd - 2 * gn : ℤ) : ℝ)) ^ n * n.factorial) = cB * DH := by
    exact_mod_cast hK
  have hM' := hM s hs0 hs1
  have hphi := phiS_ge_horR hgR n hsnn hgt' ht1'
  have hDmR : (0 : ℝ) < Dm := by exact_mod_cast hDm
  have hDHR : (0 : ℝ) < DH := by exact_mod_cast hDH
  have hcBR : (0 : ℝ) < cB := by exact_mod_cast hcB
  -- cB · Hq ≤ cB · DH · (M/Dm) · T
  have e : (cA : ℝ) * (peval mq s * ((((2 * gd - 2 * gn : ℤ) : ℝ)) ^ n * n.factorial * T))
      = cB * (DH * (peval mq s / Dm * T)) := by
    rw [← mul_assoc (cB : ℝ), ← hKR]; field_simp
  have h2 : peval2 hq s t ≤ DH * (peval mq s / Dm * T) := by
    refine le_of_mul_le_mul_left ?_ hcBR
    linarith
  have h3 : peval mq s / Dm * T ≤ phiS s (gn / gd) * T :=
    mul_le_mul_of_nonneg_right hM' (by linarith)
  rw [div_le_iff₀ hDHR]
  nlinarith

/-- **1-D box at a fixed rational `s = p/q`** (node chains). -/
def boxPoly1 (ln : ℕ) (p q : ℕ) (gn : ℤ) (gd n : ℕ) (h : List ℤ) (cA cB : ℕ) : List ℤ :=
  padd (pscale ((cA : ℤ) * ln) (tayl1 p q gn gd n)) (pscale (-(cB : ℤ)) h)

theorem box1_sound (ln ld : ℕ) (p q : ℕ) (gn : ℤ) (gd n : ℕ) (h : List ℤ) (DH cA cB : ℕ)
    (At Bt : ℤ) (Dt : ℕ) (hq : 0 < q) (hgd : 0 < gd) (hg : gn < gd) (hld : 0 < ld) (hDH : 0 < DH)
    (hcB : 0 < cB) (hDt : 0 < Dt) (hgt : gn * Dt ≤ At * gd) (hBt : Bt ≤ Dt)
    (hK : (cA : ℤ) * (((q : ℤ) * (2 * gd - 2 * gn)) ^ n * n.factorial) * ld = cB * DH)
    (hchk : (homog [At, Bt] [(Dt : ℤ), (Dt : ℤ)] (boxPoly1 ln p q gn gd n h cA cB)
      ((boxPoly1 ln p q gn gd n h cA cB).length - 1)).all (fun c => decide (0 ≤ c)) = true)
    (hl : (ln : ℝ) / ld ≤ phiS ((p : ℝ) / q) (gn / gd)) :
    ∀ t, (At : ℝ) / Dt ≤ t → t < (Bt : ℝ) / Dt → peval h t / DH ≤ phiS ((p : ℝ) / q) t := by
  intro t ht0 ht1
  have hgdR : (0 : ℝ) < gd := by exact_mod_cast hgd
  have hDtR : (0 : ℝ) < Dt := by exact_mod_cast hDt
  have hgR : (gn : ℝ) / gd < 1 := by
    rw [div_lt_one hgdR]; exact_mod_cast hg
  have hsnn : 0 ≤ (p : ℝ) / q := by positivity
  have hgt' : (gn : ℝ) / gd ≤ t := by
    refine le_trans ?_ ht0
    rw [div_le_div_iff₀ hgdR hDtR]; exact_mod_cast hgt
  have ht1' : t < 1 := by
    refine lt_of_lt_of_le ht1 ?_
    rw [div_le_one hDtR]; exact_mod_cast hBt
  have hA : (At : ℝ) ≤ Dt * t := by rw [div_le_iff₀ hDtR] at ht0; linarith
  have hB : (Dt : ℝ) * t < Bt := by rw [lt_div_iff₀ hDtR] at ht1; linarith
  have hP := mob_sound _ At Bt Dt hDt hchk hA hB
  unfold boxPoly1 at hP
  rw [peval_padd, peval_pscale, peval_pscale, peval_tayl1 p q hq gn gd hgd hg] at hP
  set T := horR (fun j => ((p : ℝ) / q + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) 0 n with hT
  have hT1 : 1 ≤ T := horR_taylor_pos hgR n hsnn hgt'
  have hKR : (cA : ℝ) * ((((q : ℤ) * (2 * gd - 2 * gn) : ℤ) : ℝ) ^ n * n.factorial) * ld = cB * DH := by
    exact_mod_cast hK
  have hphi := phiS_ge_horR hgR n hsnn hgt' ht1'
  have hldR : (0 : ℝ) < ld := by exact_mod_cast hld
  have hDHR : (0 : ℝ) < DH := by exact_mod_cast hDH
  have hcBR : (0 : ℝ) < cB := by exact_mod_cast hcB
  have e : ((cA : ℝ) * ln) * ((((q : ℤ) * (2 * gd - 2 * gn) : ℤ) : ℝ) ^ n * n.factorial * T)
      = cB * (DH * ((ln : ℝ) / ld * T)) := by
    rw [← mul_assoc (cB : ℝ), ← hKR]; field_simp
  have h2 : peval h t ≤ DH * ((ln : ℝ) / ld * T) := by
    refine le_of_mul_le_mul_left ?_ hcBR
    push_cast at hP e
    linarith
  have h3 : (ln : ℝ) / ld * T ≤ phiS ((p : ℝ) / q) (gn / gd) * T := mul_le_mul_of_nonneg_right hl (by linarith)
  rw [div_le_iff₀ hDHR]
  nlinarith

/-- Chaining two half-open ranges. -/
theorem cover_ico {P : ℝ → Prop} {a b c : ℝ} (h1 : ∀ t, a ≤ t → t < b → P t) (h2 : ∀ t, b ≤ t → t < c → P t) :
    ∀ t, a ≤ t → t < c → P t := by
  intro t ha hc
  rcases lt_or_ge t b with h | h
  · exact h1 t ha h
  · exact h2 t h hc

/-! ## 5. Models of `c^(-s/2)` in `s` -/

theorem horR_rescale (fr : ℕ → ℝ) (c a : ℝ) (ha : a ≠ 0) :
    ∀ r j, horR (fun i => a * fr i) (a * c) j r = horR fr c j r := by
  intro r
  induction r with
  | zero => intro j; simp [horR]
  | succ r ih =>
    intro j
    rw [horR, horR, ih (j + 1)]
    congr 2
    field_simp

/-- `Σ_{i<n} z^i/i!` as a Horner value (`c = 1`, constant multiplier). -/
theorem expsum_eq_horR (z : ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), z ^ i / (i.factorial : ℝ) = horR (fun _ => z) 1 0 n := by
  rw [horR_eq_sum _ _ one_ne_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [rf_zero_eq_factorial, prod_const, card_range, one_pow, one_mul]

/-- The exponential-series list: `peval = (kd md)^n n! · Σ_{i ≤ n} (kn (md s − mn)/(kd md))^i / i!`. -/
def expl (kn : ℤ) (kd : ℕ) (mn : ℤ) (md : ℕ) (n : ℕ) : List ℤ :=
  hor (fun _ => [-(kn * mn), kn * md]) ((kd : ℤ) * md) 0 n

theorem peval_expl (kn : ℤ) (kd : ℕ) (mn : ℤ) (md : ℕ) (hkd : 0 < kd) (hmd : 0 < md) (n : ℕ) (s : ℝ) :
    peval (expl kn kd mn md n) s
      = ((kd : ℝ) * md) ^ n * (n.factorial : ℝ)
        * ∑ i ∈ range (n + 1), ((kn : ℝ) / kd * (s - mn / md)) ^ i / (i.factorial : ℝ) := by
  have hkdR : (0 : ℝ) < kd := by exact_mod_cast hkd
  have hmdR : (0 : ℝ) < md := by exact_mod_cast hmd
  have hc : (((kd : ℤ) * md : ℤ) : ℝ) ≠ 0 := by push_cast; positivity
  unfold expl
  rw [peval_hor _ _ hc, rf_zero_eq_factorial, expsum_eq_horR]
  push_cast
  congr 1
  have := horR_rescale (fun _ => (kn : ℝ) / kd * (s - mn / md)) 1 ((kd : ℝ) * md) (by positivity) n 0
  rw [mul_one] at this
  rw [← this]
  congr 1
  funext i
  simp only [peval, mul_zero, add_zero]
  push_cast
  field_simp
  ring

/-- Model list: `C0n · expl ± εn`. -/
def mlist (C0n : ℕ) (εn : ℤ) (kn : ℤ) (kd : ℕ) (mn : ℤ) (md : ℕ) (n : ℕ) : List ℤ :=
  padd (pscale (C0n : ℤ) (expl kn kd mn md n)) [εn]

theorem peval_mlist (C0n : ℕ) (εn : ℤ) (kn : ℤ) (kd : ℕ) (mn : ℤ) (md : ℕ) (hkd : 0 < kd) (hmd : 0 < md)
    (n : ℕ) (s : ℝ) :
    peval (mlist C0n εn kn kd mn md n) s
      = C0n * (((kd : ℝ) * md) ^ n * (n.factorial : ℝ)
        * ∑ i ∈ range (n + 1), ((kn : ℝ) / kd * (s - mn / md)) ^ i / (i.factorial : ℝ)) + εn := by
  unfold mlist
  rw [peval_padd, peval_pscale, peval_expl kn kd mn md hkd hmd]
  simp [peval]

/-- Real model bound, `log c ≥ 0` side: `C0 Σ_{i<N} (−(s−sm) L0/2)^i/i! − ε ≤ c^(−s/2)`. -/
theorem model_real_pos {c : ℝ} (hc : 0 < c) {sm r C0 εC L0 εL ε : ℝ} (N : ℕ) (hN : 0 < N)
    (hC : |c ^ (-(sm / 2)) - C0| ≤ εC) (hL : |Real.log c - L0| ≤ εL) (hC0 : 0 ≤ C0) (hL0 : 0 ≤ L0)
    (hY : r * (L0 + εL) / 2 ≤ 1)
    (hε : εC * expSer (r * (L0 + εL) / 2) N + C0 * expSer (r * (L0 + εL) / 2) N * (r * εL)
      + C0 * expTail (r * L0 / 2) N ≤ ε) {s : ℝ} (hs : |s - sm| ≤ r) :
    |c ^ (-(s / 2)) - C0 * ∑ i ∈ range N, (-(s - sm) * L0 / 2) ^ i / (i.factorial : ℝ)| ≤ ε := by
  rw [rpow_neg_half_split hc s sm]
  exact (model_of_encl N hN hC hL hs hC0 hL0 hY).trans hε

/-- Real model bound, `log c ≤ 0` side (`L0` encloses `−log c`). -/
theorem model_real_neg {c : ℝ} (hc : 0 < c) {sm r C0 εC L0 εL ε : ℝ} (N : ℕ) (hN : 0 < N)
    (hC : |c ^ (-(sm / 2)) - C0| ≤ εC) (hL : |-Real.log c - L0| ≤ εL) (hC0 : 0 ≤ C0) (hL0 : 0 ≤ L0)
    (hY : r * (L0 + εL) / 2 ≤ 1)
    (hε : εC * expSer (r * (L0 + εL) / 2) N + C0 * expSer (r * (L0 + εL) / 2) N * (r * εL)
      + C0 * expTail (r * L0 / 2) N ≤ ε) {s : ℝ} (hs : |s - sm| ≤ r) :
    |c ^ (-(s / 2)) - C0 * ∑ i ∈ range N, ((s - sm) * L0 / 2) ^ i / (i.factorial : ℝ)| ≤ ε := by
  have hs' : |(2 * sm - s) - sm| ≤ r := by
    rw [show (2 * sm - s) - sm = -(s - sm) by ring, abs_neg]; exact hs
  have h := model_of_encl N hN hC hL hs' hC0 hL0 hY
  have e1 : c ^ (-(sm / 2)) * Real.exp (-(2 * sm - s - sm) * -Real.log c / 2) = c ^ (-(s / 2)) := by
    rw [rpow_neg_half_split hc s sm]; congr 2; ring
  have e2 : ∀ i : ℕ, (-(2 * sm - s - sm) * L0 / 2) ^ i = ((s - sm) * L0 / 2) ^ i := fun i => by
    congr 1; ring
  rw [e1] at h
  simp only [e2] at h
  exact h.trans hε

/-! ## 6. The interpolated minorant and the concavity region -/

/-- `H(s,t) = 1 + s(b−s)/(a(b−a)) (H_a t − 1) + s(s−a)/(b(b−a)) (H_b t − 1)` (the family `S0 + s[(1−λ)Ĉ_a + λĈ_b]`). -/
noncomputable def Hint (a b : ℝ) (Ha Hb : ℝ → ℝ) (s t : ℝ) : ℝ :=
  1 + s * (b - s) / (a * (b - a)) * (Ha t - 1) + s * (s - a) / (b * (b - a)) * (Hb t - 1)

theorem Hint_le_of_nodes {a b : ℝ} (ha : 0 < a) (hab : a < b) {Ha Hb : ℝ → ℝ} {s t : ℝ} (hs0 : a ≤ s)
    (hs1 : s ≤ b) (ht : t ≤ 1 / 2) (hA : Ha t ≤ phiS a t) (hB : Hb t ≤ phiS b t) :
    Hint a b Ha Hb s t ≤ phiS s t := by
  have hb : 0 < b := ha.trans hab
  have hs : 0 < s := lt_of_lt_of_le ha hs0
  have hba : 0 < b - a := by linarith
  set β0 := -(Ha t - 1) / (a * (b - a)) + (Hb t - 1) / (b * (b - a)) with hβ0
  set α0 := b * (Ha t - 1) / (a * (b - a)) - a * (Hb t - 1) / (b * (b - a)) with hα0
  have key := psi_sub_affine_ge_min (α := α0) (β := β0) ht ha hs0 hs1
  have ea : α0 + β0 * a = (Ha t - 1) / a := by rw [hα0, hβ0]; field_simp; ring
  have eb : α0 + β0 * b = (Hb t - 1) / b := by rw [hα0, hβ0]; field_simp; ring
  have es : s * (α0 + β0 * s) = Hint a b Ha Hb s t - 1 := by rw [hα0, hβ0, Hint]; field_simp; ring
  have pa : 0 ≤ psi a t - (α0 + β0 * a) := by
    rw [ea, psi, sub_nonneg]; exact div_le_div_of_nonneg_right (by linarith) ha.le
  have pb : 0 ≤ psi b t - (α0 + β0 * b) := by
    rw [eb, psi, sub_nonneg]; exact div_le_div_of_nonneg_right (by linarith) hb.le
  have hmin := le_trans (le_min pa pb) key
  rw [psi, sub_nonneg, le_div_iff₀ hs] at hmin
  nlinarith

/-- The kernel list of `DH · Hint` with `a = an/ad`, `b = bn/bd`, `H_a = peval ha / La`, `H_b = peval hb / Lb`. -/
def hinterp (an ad bn bd : ℕ) (ha : List ℤ) (La : ℕ) (hb : List ℤ) (Lb : ℕ) : List (List ℤ) :=
  let Δ : ℤ := (bn : ℤ) * ad - (an : ℤ) * bd
  let Dα : ℤ := an * Δ
  let Dβ : ℤ := bn * Δ
  padd2 [[Dα * Dβ * La * Lb]]
    (padd2 ((outer [0, (bn : ℤ) * ad ^ 2, -((bd : ℤ) * ad ^ 2)] (padd ha [-(La : ℤ)])).map (pscale (Dβ * Lb)))
      ((outer [0, -((an : ℤ) * bd ^ 2), (ad : ℤ) * bd ^ 2] (padd hb [-(Lb : ℤ)])).map (pscale (Dα * La))))

/-- Its scale `Dα Dβ La Lb` (natural number; `an bd < bn ad`). -/
def hden (an ad bn bd La Lb : ℕ) : ℕ := an * (bn * ad - an * bd) * (bn * (bn * ad - an * bd)) * La * Lb

theorem peval2_hinterp (an ad bn bd : ℕ) (ha : List ℤ) (La : ℕ) (hb : List ℤ) (Lb : ℕ) (han : 0 < an)
    (had : 0 < ad) (hbd : 0 < bd) (hlt : an * bd < bn * ad) (hLa : 0 < La) (hLb : 0 < Lb) (s t : ℝ) :
    peval2 (hinterp an ad bn bd ha La hb Lb) s t / hden an ad bn bd La Lb
      = Hint ((an : ℝ) / ad) ((bn : ℝ) / bd) (fun t => peval ha t / La) (fun t => peval hb t / Lb) s t := by
  have hbn : 0 < bn := by
    rcases Nat.eq_zero_or_pos bn with h | h
    · subst h; simp at hlt
    · exact h
  have hΔ : ((bn * ad - an * bd : ℕ) : ℝ) = (bn : ℝ) * ad - an * bd := by
    rw [Nat.cast_sub hlt.le]; push_cast; ring
  have hΔpos : (0 : ℝ) < (bn : ℝ) * ad - an * bd := by
    have : ((an * bd : ℕ) : ℝ) < ((bn * ad : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at this; linarith
  have hanR : (0 : ℝ) < an := by exact_mod_cast han
  have hbnR : (0 : ℝ) < bn := by exact_mod_cast hbn
  have hadR : (0 : ℝ) < ad := by exact_mod_cast had
  have hbdR : (0 : ℝ) < bd := by exact_mod_cast hbd
  have hLaR : (0 : ℝ) < La := by exact_mod_cast hLa
  have hLbR : (0 : ℝ) < Lb := by exact_mod_cast hLb
  have hba : (bn : ℝ) / bd - an / ad ≠ 0 := by
    rw [div_sub_div _ _ hbdR.ne' hadR.ne']
    exact div_ne_zero (by nlinarith) (by positivity)
  unfold hinterp hden Hint
  simp only [peval2_padd2, peval2_map_pscale, peval2_outer, peval2_const, peval_padd, peval]
  push_cast
  rw [hΔ]
  field_simp
  ring

/-! ## 7. Model lists from enclosures (the per-instance inputs are `norm_num` facts) -/

/-- Enclosure of a rational-exponent power from the two `2q`-th-power inequalities. -/
theorem encl_abs {u ℓ U : ℝ} (hu : 0 < u) (p m : ℕ) (hm : 0 < m) (hℓ : ℓ ^ m * u ^ p ≤ 1) (hU0 : 0 ≤ U)
    (hU : 1 ≤ U ^ m * u ^ p) : |u ^ (-((p : ℝ) / m)) - ℓ| ≤ U - ℓ := by
  have h1 := rpow_lower_of_pow hu hm hℓ
  have h2 := rpow_upper_of_pow hu hU0 hm hU
  rw [abs_le]; constructor <;> linarith

/-- The same with an irrational base enclosed by `[ulo, uhi]`. -/
theorem encl_abs_base {u ulo uhi ℓ U : ℝ} (hlo : 0 < ulo) (h1 : ulo ≤ u) (h2 : u ≤ uhi) (p m : ℕ) (hm : 0 < m)
    (hℓ : ℓ ^ m * uhi ^ p ≤ 1) (hU0 : 0 ≤ U) (hU : 1 ≤ U ^ m * ulo ^ p) : |u ^ (-((p : ℝ) / m)) - ℓ| ≤ U - ℓ := by
  have a1 := rpow_lower_of_pow_base hlo h1 h2 hm hℓ
  have a2 := rpow_upper_of_pow_base hlo h1 h2 hU0 hm hU
  rw [abs_le]; constructor <;> linarith

theorem rpow_sm_half (u : ℝ) (mn md : ℕ) : u ^ (-(((mn : ℝ) / md) / 2)) = u ^ (-((mn : ℝ) / ((2 * md : ℕ) : ℝ))) := by
  congr 1; push_cast; ring

/-- The common scale of a model list. -/
def mden (C0d kd md N : ℕ) : ℕ := C0d * ((kd * md) ^ N * N.factorial)

theorem peval_mlist_div (C0n C0d : ℕ) (εn : ℤ) (kn : ℤ) (kd mn md N : ℕ) (hC0d : 0 < C0d) (hkd : 0 < kd)
    (hmd : 0 < md) (s : ℝ) :
    peval (mlist C0n εn kn kd mn md N) s / (mden C0d kd md N : ℝ)
      = (C0n : ℝ) / C0d * ∑ i ∈ range (N + 1), ((kn : ℝ) / kd * (s - mn / md)) ^ i / (i.factorial : ℝ)
        + εn / (mden C0d kd md N : ℝ) := by
  rw [peval_mlist C0n εn kn kd mn md hkd hmd]
  have : ((mn : ℤ) : ℝ) = (mn : ℝ) := by push_cast; rfl
  have hC : (0 : ℝ) < C0d := by exact_mod_cast hC0d
  have hk : (0 : ℝ) < kd := by exact_mod_cast hkd
  have hm : (0 : ℝ) < md := by exact_mod_cast hmd
  unfold mden
  push_cast
  field_simp

/-- **Lower model, `log u ≤ 0`** (`u = 2 − 2 t₀ ≤ 1`; `2kn/kd` encloses `−log u`). -/
theorem mlist_lower_neg {t0 u : ℝ} (hu : 2 - 2 * t0 = u) (hu0 : 0 < u) (C0n C0d εn kn kd mn md N : ℕ)
    (hC0d : 0 < C0d) (hkd : 0 < kd) (hmd : 0 < md) {εC εL r : ℝ}
    (hC : |u ^ (-((mn : ℝ) / ((2 * md : ℕ) : ℝ))) - C0n / C0d| ≤ εC)
    (hL : |-Real.log u - 2 * kn / kd| ≤ εL)
    (hY : r * (2 * kn / kd + εL) / 2 ≤ 1)
    (hε : εC * expSer (r * (2 * kn / kd + εL) / 2) (N + 1)
        + C0n / C0d * expSer (r * (2 * kn / kd + εL) / 2) (N + 1) * (r * εL)
        + C0n / C0d * expTail (r * (2 * kn / kd) / 2) (N + 1) ≤ εn / (mden C0d kd md N : ℝ)) :
    ∀ s : ℝ, |s - (mn : ℝ) / md| ≤ r → peval (mlist C0n (-(εn : ℤ)) kn kd mn md N) s / (mden C0d kd md N : ℝ) ≤ phiS s t0 := by
  intro s hs
  have hC' : |u ^ (-(((mn : ℝ) / md) / 2)) - C0n / C0d| ≤ εC := by rw [rpow_sm_half]; exact hC
  have h := model_real_neg hu0 (N + 1) (Nat.succ_pos N) hC' hL (by positivity) (by positivity) hY hε hs
  rw [peval_mlist_div C0n C0d _ kn kd mn md N hC0d hkd hmd]
  have hphi : phiS s t0 = u ^ (-(s / 2)) := by unfold phiS; rw [hu]
  rw [hphi]
  have e : ∀ i : ℕ, ((s - mn / md) * (2 * kn / kd) / 2) ^ i = ((kn : ℝ) / kd * (s - mn / md)) ^ i := fun i => by
    congr 1; ring
  simp only [e] at h
  have := (abs_le.mp h).1
  push_cast
  rw [neg_div]
  linarith

/-- **Lower model, `log u ≥ 0`** (`2kn/kd` encloses `log u`). -/
theorem mlist_lower_pos {t0 u : ℝ} (hu : 2 - 2 * t0 = u) (hu0 : 0 < u) (C0n C0d εn kn kd mn md N : ℕ)
    (hC0d : 0 < C0d) (hkd : 0 < kd) (hmd : 0 < md) {εC εL r : ℝ}
    (hC : |u ^ (-((mn : ℝ) / ((2 * md : ℕ) : ℝ))) - C0n / C0d| ≤ εC)
    (hL : |Real.log u - 2 * kn / kd| ≤ εL)
    (hY : r * (2 * kn / kd + εL) / 2 ≤ 1)
    (hε : εC * expSer (r * (2 * kn / kd + εL) / 2) (N + 1)
        + C0n / C0d * expSer (r * (2 * kn / kd + εL) / 2) (N + 1) * (r * εL)
        + C0n / C0d * expTail (r * (2 * kn / kd) / 2) (N + 1) ≤ εn / (mden C0d kd md N : ℝ)) :
    ∀ s : ℝ, |s - (mn : ℝ) / md| ≤ r →
      peval (mlist C0n (-(εn : ℤ)) (-(kn : ℤ)) kd mn md N) s / (mden C0d kd md N : ℝ) ≤ phiS s t0 := by
  intro s hs
  have hC' : |u ^ (-(((mn : ℝ) / md) / 2)) - C0n / C0d| ≤ εC := by rw [rpow_sm_half]; exact hC
  have h := model_real_pos hu0 (N + 1) (Nat.succ_pos N) hC' hL (by positivity) (by positivity) hY hε hs
  rw [peval_mlist_div C0n C0d _ _ kd mn md N hC0d hkd hmd]
  have hphi : phiS s t0 = u ^ (-(s / 2)) := by unfold phiS; rw [hu]
  rw [hphi]
  have e : ∀ i : ℕ, (-(s - mn / md) * (2 * kn / kd) / 2) ^ i = ((((-(kn : ℤ)) : ℤ) : ℝ) / kd * (s - mn / md)) ^ i :=
    fun i => by congr 1; push_cast; ring
  simp only [e] at h
  have := (abs_le.mp h).1
  simp only [Int.cast_neg, Int.cast_natCast, neg_div, neg_mul] at this ⊢
  linarith

/-- **Upper model, `log u ≥ 0`.** -/
theorem mlist_upper_pos {t0 u : ℝ} (hu : 2 - 2 * t0 = u) (hu0 : 0 < u) (C0n C0d εn kn kd mn md N : ℕ)
    (hC0d : 0 < C0d) (hkd : 0 < kd) (hmd : 0 < md) {εC εL r : ℝ}
    (hC : |u ^ (-((mn : ℝ) / ((2 * md : ℕ) : ℝ))) - C0n / C0d| ≤ εC)
    (hL : |Real.log u - 2 * kn / kd| ≤ εL)
    (hY : r * (2 * kn / kd + εL) / 2 ≤ 1)
    (hε : εC * expSer (r * (2 * kn / kd + εL) / 2) (N + 1)
        + C0n / C0d * expSer (r * (2 * kn / kd + εL) / 2) (N + 1) * (r * εL)
        + C0n / C0d * expTail (r * (2 * kn / kd) / 2) (N + 1) ≤ εn / (mden C0d kd md N : ℝ)) :
    ∀ s : ℝ, |s - (mn : ℝ) / md| ≤ r →
      phiS s t0 ≤ peval (mlist C0n (εn : ℤ) (-(kn : ℤ)) kd mn md N) s / (mden C0d kd md N : ℝ) := by
  intro s hs
  have hC' : |u ^ (-(((mn : ℝ) / md) / 2)) - C0n / C0d| ≤ εC := by rw [rpow_sm_half]; exact hC
  have h := model_real_pos hu0 (N + 1) (Nat.succ_pos N) hC' hL (by positivity) (by positivity) hY hε hs
  rw [peval_mlist_div C0n C0d _ _ kd mn md N hC0d hkd hmd]
  have hphi : phiS s t0 = u ^ (-(s / 2)) := by unfold phiS; rw [hu]
  rw [hphi]
  have e : ∀ i : ℕ, (-(s - mn / md) * (2 * kn / kd) / 2) ^ i = ((((-(kn : ℤ)) : ℤ) : ℝ) / kd * (s - mn / md)) ^ i :=
    fun i => by congr 1; push_cast; ring
  simp only [e] at h
  have := (abs_le.mp h).2
  simp only [Int.cast_neg, Int.cast_natCast, neg_div, neg_mul] at this ⊢
  linarith

/-! ## 8. Condition (E): `E_s(P) < e(s)` by one Bernstein decide in `s` -/

/-- `cE · He − Σ c_k · M_k − 1` (bivariate lists of `t`-degree 0). -/
def ePoly (he : List (List ℤ)) (cE : ℕ) (m1 m2 m3 m4 : List ℤ) (c1 c2 c3 c4 : ℕ) : List (List ℤ) :=
  padd2 (he.map (pscale (cE : ℤ)))
    (padd2 ((col m1).map (pscale (-(c1 : ℤ))))
      (padd2 ((col m2).map (pscale (-(c2 : ℤ))))
        (padd2 ((col m3).map (pscale (-(c3 : ℤ)))) (padd2 ((col m4).map (pscale (-(c4 : ℤ)))) [[-1]]))))

theorem energy_lt (he : List (List ℤ)) (DHe cE : ℕ) (m1 m2 m3 m4 : List ℤ) (D1 D2 D3 D4 c1 c2 c3 c4 Z : ℕ)
    (As Bs : ℤ) (Ds : ℕ) (hDs : 0 < Ds) (hAB : As < Bs) (hDHe : 0 < DHe) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (hD3 : 0 < D3) (hD4 : 0 < D4) (hZ : 0 < Z)
    (hcE : (cE : ℤ) * DHe = 21 * Z) (hc1 : (c1 : ℤ) * D1 = 1 * Z) (hc2 : (c2 : ℤ) * D2 = 10 * Z)
    (hc3 : (c3 : ℤ) * D3 = 5 * Z) (hc4 : (c4 : ℤ) * D4 = 5 * Z)
    (hchk : bern2OK As Bs Ds 0 1 1 0 (ePoly he cE m1 m2 m3 m4 c1 c2 c3 c4) = true)
    {f1 f2 f3 f4 : ℝ → ℝ}
    (h1 : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → f1 s ≤ peval m1 s / D1)
    (h2 : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → f2 s ≤ peval m2 s / D2)
    (h3 : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → f3 s ≤ peval m3 s / D3)
    (h4 : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → f4 s ≤ peval m4 s / D4) :
    ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds →
      f1 s + 10 * f2 s + 5 * f3 s + 5 * f4 s < 21 * (peval2 he s 0 / DHe) := by
  intro s hs0 hs1
  have hP := bern2_sound As Bs Ds 0 1 1 0 _ hDs one_pos hAB hchk hs0 hs1 (t := 0) (by norm_num) (by norm_num)
  simp only [ePoly, peval2_padd2, peval2_map_pscale, peval2_col, peval2_const] at hP
  have hZR : (0 : ℝ) < Z := by exact_mod_cast hZ
  have e0 : (cE : ℝ) * DHe = 21 * Z := by exact_mod_cast hcE
  have e1 : (c1 : ℝ) * D1 = 1 * Z := by exact_mod_cast hc1
  have e2 : (c2 : ℝ) * D2 = 10 * Z := by exact_mod_cast hc2
  have e3 : (c3 : ℝ) * D3 = 5 * Z := by exact_mod_cast hc3
  have e4 : (c4 : ℝ) * D4 = 5 * Z := by exact_mod_cast hc4
  have hD1R : (0 : ℝ) < D1 := by exact_mod_cast hD1
  have hD2R : (0 : ℝ) < D2 := by exact_mod_cast hD2
  have hD3R : (0 : ℝ) < D3 := by exact_mod_cast hD3
  have hD4R : (0 : ℝ) < D4 := by exact_mod_cast hD4
  have hDeR : (0 : ℝ) < DHe := by exact_mod_cast hDHe
  have k0 : (cE : ℝ) * peval2 he s 0 = Z * (21 * (peval2 he s 0 / DHe)) := by
    field_simp; linear_combination (peval2 he s 0) * e0
  have k1 : (c1 : ℝ) * peval m1 s = Z * (1 * (peval m1 s / D1)) := by
    field_simp; linear_combination (peval m1 s) * e1
  have k2 : (c2 : ℝ) * peval m2 s = Z * (10 * (peval m2 s / D2)) := by
    field_simp; linear_combination (peval m2 s) * e2
  have k3 : (c3 : ℝ) * peval m3 s = Z * (5 * (peval m3 s / D3)) := by
    field_simp; linear_combination (peval m3 s) * e3
  have k4 : (c4 : ℝ) * peval m4 s = Z * (5 * (peval m4 s / D4)) := by
    field_simp; linear_combination (peval m4 s) * e4
  push_cast at hP
  have hb := h1 s hs0 hs1
  have hb2 := h2 s hs0 hs1
  have hb3 := h3 s hs0 hs1
  have hb4 := h4 s hs0 hs1
  have hpos : 0 < Z * (21 * (peval2 he s 0 / DHe) - (peval m1 s / D1 + 10 * (peval m2 s / D2)
      + 5 * (peval m3 s / D3) + 5 * (peval m4 s / D4))) := by nlinarith
  have := (mul_pos_iff_of_pos_left hZR).mp hpos
  linarith

end RieszN7.MinorR
