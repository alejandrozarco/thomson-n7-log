import RieszN7.Cap.Min.CoreBox
import RieszN7.Cap.ERow
import RieszN7.Cap.Pins.Defs

/-!
# `RieszN7.Cap.Min.Core` -- generic lemmas of the cap Step M (LEAN_PLAN_range.md §3.2.4, row I)

For a cap piece `s ∈ [a, b]` the family is `H_X(t) = Σ_j w_j h_{X,j}(t) / Λ_j` (9 objects, `w = wts λ v va vb`).
Step M proves `H_X ≤ φ_s` with exact contacts (`t = −1` for `A`, `0` for `B`, `c₁, c₂` for `C`):
* away from the contacts: `H_X ≤ F_X(s,t)/D_F + E_X < φ_s` (`famP`, the family bound, and a right-Taylor box
  `box2m_sound`, the `MinorR.box2_sound` argument with a polynomial multiplier `P(s) ≥ 0`);
* on a window `[α, β] ∋ c`: `f = φ_s − H_X` has `f(c) = f'(c) = 0` (family pins, `pin7Chk`) and `f'' > 0`
  (`win2`), resp. `f(−1) = 0` and `f' > 0` (`win1`); `f''` and `f'` are bounded through the same box lemma
  (`φ_s' = s φ_{s+2}`, `φ_s'' = s (s+2) φ_{s+4} = s (s+2) φ_s / (2 − 2t)²`).

Private, AI-written (CAP-M fork, 2026-11-08), not reviewed.
-/

open Real Finset LogLean.Minor RieszN7.Bern2 RieszN7.MinorR

namespace RieszN7.Cap.Min
open RieszN7 ThomsonN7 ThomsonN7.Cert ThomsonN7.Cert.CapR ThomsonGen RieszN7.Qs5

theorem polyR_eq (Lam : ℕ) (h : List ℤ) (x : ℝ) : polyR Lam h x = peval h x / Lam := by
  rw [polyR_sum, sum_getD_eq_peval]

/-! ## 2. Families -/

/-- `Σ_j w_j · sel(c_j)(t) / Λ_j`. -/
noncomputable def famP (cf : Fin 9 → TCertR) (w : Fin 9 → ℝ) (sel : TCertR → List ℤ) (t : ℝ) : ℝ :=
  ∑ j, w j * (peval (sel (cf j)) t / (cf j).Lam)

theorem HAfam_eq (cf : Fin 9 → TCertR) (w : Fin 9 → ℝ) (t : ℝ) : HAfam cf w t = famP cf w TCertR.HA t := by
  unfold HAfam famP
  refine sum_congr rfl fun j _ => ?_
  rw [show (cf j).hdr.HAf t = polyR (cf j).Lam (cf j).HA t from rfl, polyR_eq]

theorem HBfam_eq (cf : Fin 9 → TCertR) (w : Fin 9 → ℝ) (t : ℝ) : HBfam cf w t = famP cf w TCertR.HB t := by
  unfold HBfam famP
  refine sum_congr rfl fun j _ => ?_
  rw [show (cf j).hdr.HBf t = polyR (cf j).Lam (cf j).HB t from rfl, polyR_eq]

theorem HCfam_eq (cf : Fin 9 → TCertR) (w : Fin 9 → ℝ) (t : ℝ) : HCfam cf w t = famP cf w TCertR.HC t := by
  unfold HCfam famP
  refine sum_congr rfl fun j _ => ?_
  rw [show (cf j).hdr.HCf t = polyR (cf j).Lam (cf j).HC t from rfl, polyR_eq]

theorem hasDerivAt_famP (cf : Fin 9 → TCertR) (w : Fin 9 → ℝ) (sel : TCertR → List ℤ) (t : ℝ) :
    HasDerivAt (famP cf w sel) (famP cf w (fun c => pder (sel c)) t) t := by
  have h : ∀ j ∈ (univ : Finset (Fin 9)), HasDerivAt (fun y => w j * (peval (sel (cf j)) y / (cf j).Lam))
      (w j * (peval (pder (sel (cf j))) t / (cf j).Lam)) t :=
    fun j _ => ((hasDerivAt_peval _ t).div_const _).const_mul _
  have h2 := HasDerivAt.sum h
  unfold famP
  convert h2 using 1
  funext y
  simp

/-- The piece weights `(1 − λ, λ, ρ₀, …, ρ₆)` (the same expression as each piece's `Inst.wts`). -/
noncomputable def wtsG (lam : ℝ) (v va vb : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![1 - lam, lam, v 0 - (1 - lam) * va 0 - lam * vb 0, v 1 - (1 - lam) * va 1 - lam * vb 1,
    v 2 - (1 - lam) * va 2 - lam * vb 2, v 3 - (1 - lam) * va 3 - lam * vb 3, v 4 - (1 - lam) * va 4 - lam * vb 4,
    v 5 - (1 - lam) * va 5 - lam * vb 5, v 6 - (1 - lam) * va 6 - lam * vb 6]

/-- The family sum of 9 explicit values. -/
theorem sum_wtsG (lam : ℝ) (v va vb : Fin 7 → ℝ) (x0 x1 d0 d1 d2 d3 d4 d5 d6 : ℝ) :
    ∑ j, wtsG lam v va vb j * (![x0, x1, d0, d1, d2, d3, d4, d5, d6] : Fin 9 → ℝ) j
      = (1 - lam) * x0 + lam * x1 + (v 0 - (1 - lam) * va 0 - lam * vb 0) * d0
        + (v 1 - (1 - lam) * va 1 - lam * vb 1) * d1 + (v 2 - (1 - lam) * va 2 - lam * vb 2) * d2
        + (v 3 - (1 - lam) * va 3 - lam * vb 3) * d3 + (v 4 - (1 - lam) * va 4 - lam * vb 4) * d4
        + (v 5 - (1 - lam) * va 5 - lam * vb 5) * d5 + (v 6 - (1 - lam) * va 6 - lam * vb 6) * d6 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wtsG, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-- A family value `famP` written through its 9 object values. -/
theorem famP_vec (cf : Fin 9 → TCertR) (w : Fin 9 → ℝ) (sel : TCertR → List ℤ) (t : ℝ) (x : Fin 9 → ℝ)
    (hx : ∀ j, peval (sel (cf j)) t / (cf j).Lam = x j) :
    famP cf w sel t = ∑ j, w j * x j := by
  unfold famP; exact sum_congr rfl fun j _ => by rw [hx j]

/-! ## 3. The family bound -/

/-- `|Σ w_j p_j − Σ ω_j p_j| ≤ Σ ε_j M_j`. -/
theorem fam_dev (w ω p ε M : Fin 9 → ℝ) (hw : ∀ j, |w j - ω j| ≤ ε j) (hp : ∀ j, |p j| ≤ M j) :
    |∑ j, w j * p j - ∑ j, ω j * p j| ≤ ∑ j, ε j * M j := by
  rw [← sum_sub_distrib]
  refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun j _ => ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_mul (hw j) (hp j) (abs_nonneg _) (le_trans (abs_nonneg _) (hw j))

/-- `Σ_i u_i(s) r_i(t)` as one bivariate list. -/
def fsumL : List (List ℤ × List ℤ) → List (List ℤ)
  | [] => []
  | p :: ps => padd2 (outer p.1 p.2) (fsumL ps)

theorem peval2_fsumL (ps : List (List ℤ × List ℤ)) (s t : ℝ) :
    peval2 (fsumL ps) s t = (ps.map fun p => peval p.1 s * peval p.2 t).sum := by
  induction ps with
  | nil => simp [fsumL, peval2]
  | cons p ps ih => simp [fsumL, peval2_padd2, peval2_outer, ih]

/-- The bivariate list of `Σ_j W_j(s) · (c_j sel(c_j))(t)`. -/
def fbuild (cf : Fin 9 → TCertR) (sel : TCertR → List ℤ) (W : Fin 9 → List ℤ) (c : Fin 9 → ℤ) :
    List (List ℤ) :=
  fsumL ((List.finRange 9).map fun j => (W j, pscale (c j) (sel (cf j))))

theorem peval2_fbuild (cf : Fin 9 → TCertR) (sel : TCertR → List ℤ) (W : Fin 9 → List ℤ) (c : Fin 9 → ℤ)
    (Ω Lc : ℕ) (hΩ : 0 < Ω) (hLc : 0 < Lc) (hc : ∀ j, (c j : ℝ) * (cf j).Lam = Lc) (hL : ∀ j, 0 < (cf j).Lam)
    (s t : ℝ) :
    peval2 (fbuild cf sel W c) s t / ((Ω : ℝ) * Lc)
      = ∑ j, peval (W j) s / Ω * (peval (sel (cf j)) t / (cf j).Lam) := by
  unfold fbuild
  rw [peval2_fsumL, List.map_map, ← Fin.sum_univ_def, Finset.sum_div]
  refine sum_congr rfl fun j _ => ?_
  simp only [Function.comp, peval_pscale]
  have hLj : (0 : ℝ) < (cf j).Lam := by exact_mod_cast hL j
  have hΩ' : (0 : ℝ) < Ω := by exact_mod_cast hΩ
  have hLc' : (0 : ℝ) < Lc := by exact_mod_cast hLc
  have hcj := hc j
  have hcj0 : (c j : ℝ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hcj; linarith
  rw [← hcj]
  field_simp

/-! ## 4. Exact pins of one object (`ℤ[√5]` evaluation, `ERow.at5`) -/

theorem at5_eval (p : (ℤ × ℤ) × (ℤ × ℤ)) (h : List ℤ) (hE : ev5 p.2 ≠ 0) :
    ev5 (at5 p h) = ev5 p.2 ^ h.length * peval h (ev5 p.1 / ev5 p.2) := by
  unfold at5
  rw [homog5_const p.1 p.2 hE h h.length (by omega), sum_getD_eq_peval]

/-- Value at a rational point `T₀/1`. -/
theorem evalR (p : (ℤ × ℤ) × (ℤ × ℤ)) (hp : p.2 = (1, 0)) (h : List ℤ) (L d : ℕ) (a : ℤ) (hL : 0 < L)
    (hd : 0 < d) (h1 : (d : ℤ) * (at5 p h).1 = a * L) (h2 : (at5 p h).2 = 0) :
    peval h (ev5 p.1 / ev5 p.2) / L = a / d := by
  have hE : ev5 p.2 = 1 := by rw [hp]; simp [ev5]
  have e := at5_eval p h (by rw [hE]; norm_num)
  rw [show ev5 p.2 ^ h.length = 1 by rw [hE, one_pow], one_mul] at e
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1' : (d : ℝ) * (at5 p h).1 = a * L := by exact_mod_cast h1
  have h2' : ((at5 p h).2 : ℝ) = 0 := by exact_mod_cast h2
  have ev : ev5 (at5 p h) = (at5 p h).1 := by simp only [ev5, h2', zero_mul, add_zero]
  rw [← e, ev, div_eq_div_iff hLR.ne' hdR.ne']
  linarith

/-- Value at `(T₀)/4` with `T₀ ∈ ℤ[√5]` (`c₁`, `c₂`). -/
theorem evalC (p : (ℤ × ℤ) × (ℤ × ℤ)) (hp : p.2 = (4, 0)) (h : List ℤ) (L d : ℕ) (a b : ℤ) (hL : 0 < L)
    (hd : 0 < d) (h1 : (d : ℤ) * (at5 p h).1 = 4 ^ h.length * L * a)
    (h2 : (d : ℤ) * (at5 p h).2 = 4 ^ h.length * L * b) :
    peval h (ev5 p.1 / ev5 p.2) / L = a / d + √5 * (b / d) := by
  have hE : ev5 p.2 = 4 := by rw [hp]; simp [ev5]
  have e := at5_eval p h (by rw [hE]; norm_num)
  rw [show ev5 p.2 ^ h.length = 4 ^ h.length by rw [hE]] at e
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : (0 : ℝ) < 4 ^ h.length := by positivity
  have h1' : (d : ℝ) * (at5 p h).1 = 4 ^ h.length * L * a := by exact_mod_cast h1
  have h2' : (d : ℝ) * (at5 p h).2 = 4 ^ h.length * L * b := by exact_mod_cast h2
  have key : (d : ℝ) * ev5 (at5 p h) = 4 ^ h.length * L * (a + √5 * b) := by
    simp only [ev5]; linear_combination h1' + √5 * h2'
  rw [e] at key
  field_simp
  have : (d : ℝ) * peval h (ev5 p.1 / ev5 p.2) = L * (a + √5 * b) := by
    have h4' : (4 : ℝ) ^ h.length ≠ 0 := h4.ne'
    apply mul_left_cancel₀ h4'
    linear_combination key
  linear_combination this

/-- The seven pins of one object, against targets `n k / den` (Re/Im parts at `c₁`; `c₂` is the conjugate). -/
def pin7Chk (c : TCertR) (n : Fin 7 → ℤ) (den : ℕ) : Bool :=
  let L : ℤ := c.Lam
  let d : ℤ := den
  let q : ℤ := 4 ^ c.HC.length
  let q' : ℤ := 4 ^ (pder c.HC).length
  (decide (d * (at5 ptB c.HB).1 = n 0 * L) && decide ((at5 ptB c.HB).2 = 0)) &&
  (decide (d * (at5 ptB (pder c.HB)).1 = n 1 * L) && decide ((at5 ptB (pder c.HB)).2 = 0)) &&
  (decide (d * (at5 ptA c.HA).1 = n 2 * L) && decide ((at5 ptA c.HA).2 = 0)) &&
  (decide (d * (at5 ptC1 c.HC).1 = q * L * n 3) && decide (d * (at5 ptC1 c.HC).2 = q * L * n 4)) &&
  (decide (d * (at5 ptC2 c.HC).1 = q * L * n 3) && decide (d * (at5 ptC2 c.HC).2 = q * L * (-n 4))) &&
  (decide (d * (at5 ptC1 (pder c.HC)).1 = q' * L * n 5) && decide (d * (at5 ptC1 (pder c.HC)).2 = q' * L * n 6)) &&
  (decide (d * (at5 ptC2 (pder c.HC)).1 = q' * L * n 5) &&
    decide (d * (at5 ptC2 (pder c.HC)).2 = q' * L * (-n 6)))

/-- **Object pins.** -/
structure Pins7 (c : TCertR) (n : Fin 7 → ℤ) (den : ℕ) : Prop where
  B0 : peval c.HB 0 / c.Lam = n 0 / den
  B1 : peval (pder c.HB) 0 / c.Lam = n 1 / den
  A0 : peval c.HA (-1) / c.Lam = n 2 / den
  C1 : peval c.HC ThomsonN7.Base.c1 / c.Lam = n 3 / den + √5 * (n 4 / den)
  C2 : peval c.HC ThomsonN7.Base.c2 / c.Lam = n 3 / den - √5 * (n 4 / den)
  D1 : peval (pder c.HC) ThomsonN7.Base.c1 / c.Lam = n 5 / den + √5 * (n 6 / den)
  D2 : peval (pder c.HC) ThomsonN7.Base.c2 / c.Lam = n 5 / den - √5 * (n 6 / den)

theorem pins7_of_chk (c : TCertR) (n : Fin 7 → ℤ) (den : ℕ) (hL : 0 < c.Lam) (hd : 0 < den)
    (h : pin7Chk c n den = true) : Pins7 c n den := by
  simp only [pin7Chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, ⟨d1, d2⟩⟩, ⟨a1, a2⟩⟩, ⟨c11, c12⟩⟩, ⟨c21, c22⟩⟩, ⟨e11, e12⟩⟩, ⟨e21, e22⟩⟩ := h
  have pB : ev5 ptB.1 / ev5 ptB.2 = 0 := ev5_ptB
  have pA : ev5 ptA.1 / ev5 ptA.2 = -1 := ev5_ptA
  have pC1 : ev5 ptC1.1 / ev5 ptC1.2 = ThomsonN7.Base.c1 := ev5_ptC1
  have pC2 : ev5 ptC2.1 / ev5 ptC2.2 = ThomsonN7.Base.c2 := ev5_ptC2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := evalR ptB rfl c.HB c.Lam den (n 0) hL hd (by exact_mod_cast b1) b2
    rwa [pB] at this
  · have := evalR ptB rfl (pder c.HB) c.Lam den (n 1) hL hd (by exact_mod_cast d1) d2
    rwa [pB] at this
  · have := evalR ptA rfl c.HA c.Lam den (n 2) hL hd (by exact_mod_cast a1) a2
    rwa [pA] at this
  · have := evalC ptC1 rfl c.HC c.Lam den (n 3) (n 4) hL hd (by exact_mod_cast c11) (by exact_mod_cast c12)
    rwa [pC1] at this
  · have := evalC ptC2 rfl c.HC c.Lam den (n 3) (-n 4) hL hd (by exact_mod_cast c21) (by exact_mod_cast c22)
    rw [pC2] at this; rw [this]; push_cast; ring
  · have := evalC ptC1 rfl (pder c.HC) c.Lam den (n 5) (n 6) hL hd (by exact_mod_cast e11)
      (by exact_mod_cast e12)
    rwa [pC1] at this
  · have := evalC ptC2 rfl (pder c.HC) c.Lam den (n 5) (-n 6) hL hd (by exact_mod_cast e21)
      (by exact_mod_cast e22)
    rw [pC2] at this; rw [this]; push_cast; ring

end RieszN7.Cap.Min
