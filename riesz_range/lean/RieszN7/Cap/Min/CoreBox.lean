import RieszN7.Cells.MinorR

/-!
# `RieszN7.Cap.Min.CoreBox` -- generic lemmas of the cap Step M without object imports

`pder` (derivative lists), absolute bounds (`peval_abs_le`, `hev`), `(2 − 2t)^m` (`uq`), the right-Taylor box with
a multiplier `P(s) ≥ 0` (`box2m_sound`), the window lemmas (`win1`, `win2`) and `φ_s'' = s (s+2) φ_s/(2 − 2t)²`.
See `RieszN7.Cap.Min.Core` for the family side.  Private, AI-written (CAP-M fork, 2026-11-08), not reviewed.
-/

open Real Finset LogLean.Minor RieszN7.Bern2 RieszN7.MinorR

namespace RieszN7.Cap.Min
open RieszN7

/-! ## 1. Integer polynomials: `polyR`, derivative lists, absolute bounds -/

theorem sum_getD_eq_peval (h : List ℤ) (x : ℝ) :
    ∑ j ∈ range h.length, (h.getD j 0 : ℝ) * x ^ j = peval h x := by
  induction h with
  | nil => simp [peval]
  | cons a as ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, peval]
    rw [← ih, mul_sum, add_comm]
    congr 1
    exact sum_congr rfl (fun j _ => by rw [pow_succ]; ring)

/-- The derivative of an integer polynomial: `(a + y q(y))' = q(y) + y q'(y)`. -/
def pder : List ℤ → List ℤ
  | [] => []
  | _ :: as => padd as (0 :: pder as)

theorem hasDerivAt_peval (l : List ℤ) (x : ℝ) :
    HasDerivAt (fun y => peval l y) (peval (pder l) x) x := by
  induction l with
  | nil => simpa [peval, pder] using hasDerivAt_const x (0 : ℝ)
  | cons a as ih =>
    have h := ((hasDerivAt_id x).mul ih).const_add (a : ℝ)
    simp only [peval, pder, peval_padd]
    convert h using 1 <;> simp

theorem peval_abs_le (z : List ℤ) {y R : ℝ} (hy : |y| ≤ R) :
    |peval z y| ≤ peval (z.map (fun c => |c|)) R := by
  have hR : 0 ≤ R := le_trans (abs_nonneg y) hy
  induction z with
  | nil => simp [peval]
  | cons a as ih =>
    simp only [List.map_cons, peval]
    have h1 : |(a : ℝ) + y * peval as y| ≤ |(a : ℝ)| + |y| * |peval as y| := by
      rw [← abs_mul]; exact abs_add_le _ _
    have h2 : |y| * |peval as y| ≤ R * peval (as.map (fun c => |c|)) R :=
      mul_le_mul hy ih (abs_nonneg _) hR
    push_cast
    linarith

theorem peval_one (l : List ℤ) : peval l 1 = ((l.sum : ℤ) : ℝ) := by
  induction l with
  | nil => simp [peval]
  | cons a as ih => simp [peval, ih]

/-- `|p(t)| ≤ Σ |p_i|` on `|t| ≤ 1`. -/
theorem peval_abs_le_one (z : List ℤ) {t : ℝ} (ht : |t| ≤ 1) (M : ℤ) (hM : (z.map (fun c => |c|)).sum ≤ M) :
    |peval z t| ≤ M := by
  have h := peval_abs_le z ht
  rw [peval_one] at h
  exact le_trans h (by exact_mod_cast hM)

/-- `D^len · p(B/D)` as an integer. -/
def hev : List ℤ → ℤ → ℤ → ℤ
  | [], _, _ => 0
  | a :: as, B, D => a * D ^ (as.length + 1) + B * hev as B D

theorem hev_eq (z : List ℤ) (B D : ℤ) (hD : (D : ℝ) ≠ 0) :
    (D : ℝ) ^ z.length * peval z (B / D) = hev z B D := by
  induction z with
  | nil => simp [peval, hev]
  | cons a as ih =>
    simp only [List.length_cons, peval, hev]
    push_cast
    rw [← ih, pow_succ]
    field_simp

/-! ## 5. Right-Taylor box with a multiplier `P(s) ≥ 0` -/

/-- `(2 − 2t)^m` as a bivariate list. -/
def uq : ℕ → List (List ℤ)
  | 0 => [[1]]
  | m + 1 => mul2 [[2, -2]] (uq m)

theorem peval2_uq (m : ℕ) (s t : ℝ) : peval2 (uq m) s t = (2 - 2 * t) ^ m := by
  induction m with
  | zero => simp [uq, peval2, peval]
  | succ m ih =>
    rw [uq, peval2_mul2, ih, pow_succ]
    simp [peval2, peval]; ring

/-- **Box with multiplier.** As `MinorR.box2_sound`, with `cA · P(s) · M(s) · T(s,t) − cB · hq(s,t) ≥ 0`: then
`hq / DH ≤ P(s) · φ_s(t)` on the box (`P ≥ 0` there). -/
theorem box2m_sound (P mq : List ℤ) (Dm : ℕ) (gn : ℤ) (gd n : ℕ) (hq : List (List ℤ)) (DH cA cB : ℕ)
    (As Bs : ℤ) (Ds : ℕ) (At Bt : ℤ) (Dt : ℕ) (mt : ℕ)
    (hgd : 0 < gd) (hg : gn < gd) (hDm : 0 < Dm) (hDH : 0 < DH) (hcB : 0 < cB) (hDs : 0 < Ds) (hDt : 0 < Dt)
    (hAB : As < Bs) (hAs : 0 ≤ As) (hgt : gn * Dt ≤ At * gd) (hBt : Bt ≤ Dt)
    (hK : (cA : ℤ) * Dm * ((2 * gd - 2 * gn) ^ n * n.factorial) = cB * DH)
    (hchk : bern2OK As Bs Ds At Bt Dt mt (boxPoly (pmul P mq) gn gd n hq cA cB) = true)
    (hP : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → 0 ≤ peval P s)
    (hM : ∀ s, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → peval mq s / Dm ≤ phiS s (gn / gd)) :
    ∀ s t, (As : ℝ) / Ds ≤ s → s ≤ (Bs : ℝ) / Ds → (At : ℝ) / Dt ≤ t → t < (Bt : ℝ) / Dt →
      peval2 hq s t / DH ≤ peval P s * phiS s t := by
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
  have hPq := bern2_sound As Bs Ds At Bt Dt mt _ hDs hDt hAB hchk hs0 hs1 ht0 ht1
  rw [peval2_boxPoly, peval2_tayl2 gn gd hgd hg, peval_pmul] at hPq
  set T := horR (fun j => (s + 2 * j) * (t - gn / gd)) (2 - 2 * (gn / gd)) 0 n with hT
  have hT1 : 1 ≤ T := horR_taylor_pos hgR n hsnn hgt'
  have hKR : (cA : ℝ) * Dm * ((((2 * gd - 2 * gn : ℤ) : ℝ)) ^ n * n.factorial) = cB * DH := by
    exact_mod_cast hK
  have hM' := hM s hs0 hs1
  have hP' := hP s hs0 hs1
  have hphi := phiS_ge_horR hgR n hsnn hgt' ht1'
  have hDmR : (0 : ℝ) < Dm := by exact_mod_cast hDm
  have hDHR : (0 : ℝ) < DH := by exact_mod_cast hDH
  have hcBR : (0 : ℝ) < cB := by exact_mod_cast hcB
  have e : (cA : ℝ) * (peval P s * peval mq s * ((((2 * gd - 2 * gn : ℤ) : ℝ)) ^ n * n.factorial * T))
      = cB * (DH * (peval P s * (peval mq s / Dm) * T)) := by
    rw [← mul_assoc (cB : ℝ), ← hKR]; field_simp
  have h2 : peval2 hq s t ≤ DH * (peval P s * (peval mq s / Dm) * T) := by
    refine le_of_mul_le_mul_left ?_ hcBR
    linarith
  have h3 : peval P s * (peval mq s / Dm) * T ≤ peval P s * (phiS s (gn / gd) * T) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM' (by linarith)) hP'
  have h4 : peval P s * (phiS s (gn / gd) * T) ≤ peval P s * phiS s t :=
    mul_le_mul_of_nonneg_left hphi hP'
  rw [div_le_iff₀ hDHR]
  nlinarith

/-! ## 6. Windows -/

theorem cont_of_deriv {f f' : ℝ → ℝ} {S : Set ℝ} (hf : ∀ x ∈ S, HasDerivAt f (f' x) x) : ContinuousOn f S :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt

/-- `f' > 0` on `[α, β]` and `f(α) = 0`: `f ≥ 0` on `[α, β]`, zero only at `α`. -/
theorem win1 {f f' : ℝ → ℝ} {α β : ℝ} (hf : ∀ x ∈ Set.Icc α β, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Icc α β, 0 < f' x) (h0 : f α = 0) :
    ∀ t ∈ Set.Icc α β, 0 ≤ f t ∧ (f t = 0 → t = α) := by
  have hmono : StrictMonoOn f (Set.Icc α β) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc α β) (cont_of_deriv hf) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hf x (Set.Ioo_subset_Icc_self hx)).deriv]
    exact hpos x (Set.Ioo_subset_Icc_self hx)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; exact ⟨h0.ge, fun _ => rfl⟩
  · have := hmono ⟨le_refl α, le_trans ht.1 ht.2⟩ ht h
    rw [h0] at this
    exact ⟨this.le, fun h' => absurd h' this.ne'⟩

/-- `f'' > 0` on `[α, β] ∋ c`, `f(c) = f'(c) = 0`: `f ≥ 0` on `[α, β]`, zero only at `c`. -/
theorem win2 {f f' f'' : ℝ → ℝ} {α β c : ℝ} (hαc : α ≤ c) (hcβ : c ≤ β)
    (hf : ∀ x ∈ Set.Icc α β, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Set.Icc α β, HasDerivAt f' (f'' x) x)
    (hpos : ∀ x ∈ Set.Icc α β, 0 < f'' x) (h0 : f c = 0) (h1 : f' c = 0) :
    ∀ t ∈ Set.Icc α β, 0 ≤ f t ∧ (f t = 0 → t = c) := by
  -- `f'` is strictly increasing, negative left of `c`, positive right of `c`
  have hm' : StrictMonoOn f' (Set.Icc α β) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc α β) (cont_of_deriv hf') fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hf' x (Set.Ioo_subset_Icc_self hx)).deriv]
    exact hpos x (Set.Ioo_subset_Icc_self hx)
  have hcI : c ∈ Set.Icc α β := ⟨hαc, hcβ⟩
  have hR : StrictMonoOn f (Set.Icc c β) := by
    have hsub : Set.Icc c β ⊆ Set.Icc α β := Set.Icc_subset_Icc hαc le_rfl
    refine strictMonoOn_of_deriv_pos (convex_Icc c β) (cont_of_deriv fun x hx => hf x (hsub hx))
      fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hf x (hsub (Set.Ioo_subset_Icc_self hx))).deriv, ← h1]
    exact hm' hcI (hsub (Set.Ioo_subset_Icc_self hx)) hx.1
  have hL : StrictAntiOn f (Set.Icc α c) := by
    have hsub : Set.Icc α c ⊆ Set.Icc α β := Set.Icc_subset_Icc le_rfl hcβ
    refine strictAntiOn_of_deriv_neg (convex_Icc α c) (cont_of_deriv fun x hx => hf x (hsub hx))
      fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hf x (hsub (Set.Ioo_subset_Icc_self hx))).deriv, ← h1]
    exact hm' (hsub (Set.Ioo_subset_Icc_self hx)) hcI hx.2
  intro t ht
  rcases lt_trichotomy t c with h | h | h
  · have := hL ⟨ht.1, h.le⟩ ⟨hαc, le_rfl⟩ h
    rw [h0] at this
    exact ⟨this.le, fun h' => absurd h' this.ne'⟩
  · subst h; exact ⟨h0.ge, fun _ => rfl⟩
  · have := hR ⟨le_rfl, hcβ⟩ ⟨h.le, ht.2⟩ h
    rw [h0] at this
    exact ⟨this.le, fun h' => absurd h' this.ne'⟩

/-! ## 7. Derivatives of `φ_s` in `t` -/

theorem phiS_add_four (s : ℝ) {t : ℝ} (ht : t < 1) : phiS (s + 2 + 2) t = phiS s t / (2 - 2 * t) ^ 2 := by
  rw [phiS_add_two (s + 2) ht, phiS_add_two s ht, pow_two, div_div]

theorem hasDerivAt_phiS1 (s : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t => s * phiS (s + 2) t) (s * ((s + 2) * phiS (s + 2 + 2) t)) t :=
  (hasDerivAt_phiS (s + 2) ht).const_mul s

/-! ## 8. Small evaluations -/

theorem peval2_mul2_uq (m : ℕ) (F : List (List ℤ)) (s t : ℝ) :
    peval2 (mul2 (uq m) F) s t = (2 - 2 * t) ^ m * peval2 F s t := by
  rw [peval2_mul2, peval2_uq]

theorem peval_P0 (s : ℝ) : peval [1] s = 1 := by simp only [peval]; push_cast; ring
theorem peval_P1 (s : ℝ) : peval [0, 1] s = s := by simp only [peval]; push_cast; ring
theorem peval_P2 (s : ℝ) : peval [0, 2, 1] s = s * (s + 2) := by simp only [peval]; push_cast; ring

theorem P1_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ peval [0, 1] s := by rw [peval_P1]; exact hs
theorem P2_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ peval [0, 2, 1] s := by rw [peval_P2]; positivity
theorem P0_nonneg (s : ℝ) : 0 ≤ peval [1] s := by rw [peval_P0]; norm_num

end RieszN7.Cap.Min
