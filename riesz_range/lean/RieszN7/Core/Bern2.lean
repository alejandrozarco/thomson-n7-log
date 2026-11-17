import LogLean.MinorCore

/-!
# `RieszN7.Core.Bern2` — bivariate Bernstein positivity, computed in the kernel (LEAN_PLAN_range.md §3.0.5)

A bivariate integer polynomial is a list of `t`-polynomials indexed by the power of `s`:
`q = [q₀, q₁, …]`, `peval2 q s t = Σ_i s^i · peval q_i t`.  With the Möbius maps
`s = (A_s + B_s y)/(D_s (1 + y))`, `t = (A_t + B_t x)/(D_t (1 + x))` (`x, y ∈ [0, ∞)`),

    homog2 q = Σ_i T_s(y)^i E_s(y)^(m_s - i) ⊗ homog T_t E_t q_i m_t  =  E_s(y)^(m_s) E_t(x)^(m_t) · P(s, t)

(`peval2_homog2`; `homog` is `LogLean.Minor.homog`, applied in `t` to every `s`-coefficient), so all its
coefficients `≥ 0` ⇒ `P ≥ 0` on `[A_s/D_s, B_s/D_s) × [A_t/D_t, B_t/D_t)` (`bern2_sound_ico`), and by continuity
in `s` on the box closed in `s` (`bern2_sound`).  The Bernstein coefficients are never stored: the kernel
computes them (`decide +kernel` on `bern2OK`).  Python mirror: `gen_range/bern2.py` (same list semantics).
Private prototype (Phase 1), AI-written, not reviewed.
-/

open LogLean.Minor

namespace RieszN7.Bern2

/-- `peval2 q s t = Σ_i s^i · peval q_i t`. -/
def peval2 : List (List ℤ) → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | r :: rs, s, t => peval r t + s * peval2 rs s t

def padd2 : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => padd a b :: padd2 as bs

/-- `u(s) · r(t)`. -/
def outer (u r : List ℤ) : List (List ℤ) := u.map (fun c => pscale c r)

/-- `u(s) · b(s, t)`. -/
def smul2 : List ℤ → List (List ℤ) → List (List ℤ)
  | [], _ => []
  | c :: cs, b => padd2 (b.map (pscale c)) ([] :: smul2 cs b)

theorem peval2_padd2 (p q : List (List ℤ)) (s t : ℝ) :
    peval2 (padd2 p q) s t = peval2 p s t + peval2 q s t := by
  induction p generalizing q with
  | nil => simp [padd2, peval2]
  | cons a as ih =>
    cases q with
    | nil => simp [padd2, peval2]
    | cons b bs => simp only [padd2, peval2, ih, peval_padd]; ring

theorem peval2_outer (u r : List ℤ) (s t : ℝ) : peval2 (outer u r) s t = peval u s * peval r t := by
  induction u with
  | nil => simp [outer, peval2, peval]
  | cons c cs ih =>
    simp only [outer, List.map_cons, peval2, peval, peval_pscale] at ih ⊢
    rw [ih]; ring

theorem peval2_map_pscale (c : ℤ) (b : List (List ℤ)) (s t : ℝ) :
    peval2 (b.map (pscale c)) s t = c * peval2 b s t := by
  induction b with
  | nil => simp [peval2]
  | cons r rs ih =>
    simp only [List.map_cons, peval2, peval_pscale, ih]; ring

theorem peval2_smul2 (u : List ℤ) (b : List (List ℤ)) (s t : ℝ) :
    peval2 (smul2 u b) s t = peval u s * peval2 b s t := by
  induction u with
  | nil => simp [smul2, peval2, peval]
  | cons c cs ih =>
    simp only [smul2, peval2_padd2, peval2_map_pscale, peval2, peval, ih]; ring

/-- Product of bivariate polynomials. -/
def mul2 : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], _ => []
  | r :: rs, q => padd2 (q.map (pmul r)) ([] :: mul2 rs q)

theorem peval2_map_pmul (r : List ℤ) (b : List (List ℤ)) (s t : ℝ) :
    peval2 (b.map (pmul r)) s t = peval r t * peval2 b s t := by
  induction b with
  | nil => simp [peval2]
  | cons c cs ih =>
    simp only [List.map_cons, peval2, peval_pmul, ih]; ring

theorem peval2_mul2 (p q : List (List ℤ)) (s t : ℝ) :
    peval2 (mul2 p q) s t = peval2 p s t * peval2 q s t := by
  induction p with
  | nil => simp [mul2, peval2]
  | cons r rs ih =>
    simp only [mul2, peval2_padd2, peval2_map_pmul, peval2, peval, ih]; ring

/-- `homog2 Ts Es Tt Et mt q m = Σ_i Ts^i Es^(m-i) ⊗ homog Tt Et q_i mt`. -/
def homog2 (Ts Es Tt Et : List ℤ) (mt : ℕ) : List (List ℤ) → ℕ → List (List ℤ)
  | [], _ => []
  | c :: cs, m =>
    padd2 (outer (ppow Es m) (homog Tt Et c mt)) (smul2 Ts (homog2 Ts Es Tt Et mt cs (m - 1)))

theorem peval2_homog2 (Ts Es Tt Et : List ℤ) (mt : ℕ) (y x : ℝ) (hEs : peval Es y ≠ 0)
    (hEt : peval Et x ≠ 0) (q : List (List ℤ)) (hq : ∀ r ∈ q, r.length ≤ mt + 1) :
    ∀ m : ℕ, q.length ≤ m + 1 →
      peval2 (homog2 Ts Es Tt Et mt q m) y x
        = peval Es y ^ m * peval Et x ^ mt * peval2 q (peval Ts y / peval Es y) (peval Tt x / peval Et x) := by
  induction q with
  | nil => intro m _; simp [homog2, peval2]
  | cons c cs ih =>
    intro m hm
    have hc : c.length ≤ mt + 1 := hq c List.mem_cons_self
    have hcs : ∀ r ∈ cs, r.length ≤ mt + 1 := fun r hr => hq r (List.mem_cons_of_mem c hr)
    simp only [List.length_cons] at hm
    rw [homog2.eq_2, peval2_padd2, peval2_outer, peval2_smul2, peval_ppow,
      peval_homog Tt Et x hEt c mt hc, ih hcs (m - 1) (by omega)]
    obtain ⟨u, hu⟩ : ∃ u, peval Ts y = peval Es y * u := ⟨_, (mul_div_cancel₀ _ hEs).symm⟩
    have hdiv : peval Ts y / peval Es y = u := by rw [hu, mul_div_cancel_left₀ _ hEs]
    rw [hdiv, hu]
    rcases m with _ | m'
    · have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp only [peval2]
      ring
    · simp only [Nat.add_sub_cancel, peval2]
      ring

/-- all entries `≥ 0`. -/
def all2 (b : List (List ℤ)) : Bool := b.all (fun r => r.all (fun c => decide (0 ≤ c)))

theorem peval2_nonneg_of_all2 (b : List (List ℤ)) (h : all2 b = true) {y x : ℝ} (hy : 0 ≤ y)
    (hx : 0 ≤ x) : 0 ≤ peval2 b y x := by
  induction b with
  | nil => simp [peval2]
  | cons r rs ih =>
    simp only [all2, List.all_cons, Bool.and_eq_true] at h
    simp only [peval2]
    exact add_nonneg (peval_nonneg_of_all r h.1 hx) (mul_nonneg hy (ih h.2))

/-- The kernel check on the box `[As/Ds, Bs/Ds] × [At/Dt, Bt/Dt)`. -/
def bern2OK (As Bs : ℤ) (Ds : ℕ) (At Bt : ℤ) (Dt : ℕ) (mt : ℕ) (q : List (List ℤ)) : Bool :=
  q.all (fun r => decide (r.length ≤ mt + 1)) &&
    all2 (homog2 [As, Bs] [(Ds : ℤ), (Ds : ℤ)] [At, Bt] [(Dt : ℤ), (Dt : ℤ)] mt q (q.length - 1))

theorem mob_point (A B : ℤ) (D : ℕ) (hD : 0 < D) {t : ℝ} (ht0 : (A : ℝ) ≤ D * t) (ht1 : (D : ℝ) * t < B) :
    ∃ x : ℝ, 0 ≤ x ∧ 0 < peval [(D : ℤ), (D : ℤ)] x ∧
      peval [A, B] x / peval [(D : ℤ), (D : ℤ)] x = t := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hden : 0 < (B : ℝ) - D * t := by linarith
  set x : ℝ := ((D : ℝ) * t - A) / (B - D * t) with hxdef
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hden.le
  have hx : x * ((B : ℝ) - D * t) = D * t - A := div_mul_cancel₀ _ hden.ne'
  have hE : peval [(D : ℤ), (D : ℤ)] x = (D : ℝ) * (1 + x) := by
    simp only [peval, Int.cast_natCast]; ring
  have hT : peval [A, B] x = (A : ℝ) + B * x := by
    simp only [peval]; ring
  have hEpos : 0 < (D : ℝ) * (1 + x) := by positivity
  refine ⟨x, hx0, by rw [hE]; exact hEpos, ?_⟩
  rw [hE, hT, div_eq_iff hEpos.ne']
  linear_combination hx

/-- **Bernstein positivity on a half-open box.** -/
theorem bern2_sound_ico (As Bs : ℤ) (Ds : ℕ) (At Bt : ℤ) (Dt : ℕ) (mt : ℕ) (q : List (List ℤ))
    (hDs : 0 < Ds) (hDt : 0 < Dt) (hchk : bern2OK As Bs Ds At Bt Dt mt q = true) {s t : ℝ}
    (hs0 : (As : ℝ) ≤ Ds * s) (hs1 : (Ds : ℝ) * s < Bs) (ht0 : (At : ℝ) ≤ Dt * t) (ht1 : (Dt : ℝ) * t < Bt) :
    0 ≤ peval2 q s t := by
  simp only [bern2OK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hlen, hall⟩ := hchk
  obtain ⟨y, hy, hEy, hsy⟩ := mob_point As Bs Ds hDs hs0 hs1
  obtain ⟨x, hx, hEx, htx⟩ := mob_point At Bt Dt hDt ht0 ht1
  have key := peval2_homog2 [As, Bs] [(Ds : ℤ), (Ds : ℤ)] [At, Bt] [(Dt : ℤ), (Dt : ℤ)] mt y x hEy.ne'
    hEx.ne' q hlen (q.length - 1) (by omega)
  rw [hsy, htx] at key
  have h1 := peval2_nonneg_of_all2 _ hall hy hx
  rw [key] at h1
  exact (mul_nonneg_iff_of_pos_left (mul_pos (pow_pos hEy _) (pow_pos hEx _))).mp h1

theorem continuous_peval (p : List ℤ) : Continuous (peval p) := by
  induction p with
  | nil => exact continuous_const
  | cons a as ih =>
    show Continuous (fun y => (a : ℝ) + y * peval as y)
    exact continuous_const.add (continuous_id.mul ih)

theorem continuous_peval2_s (q : List (List ℤ)) (t : ℝ) : Continuous (fun s => peval2 q s t) := by
  induction q with
  | nil => exact continuous_const
  | cons r rs ih =>
    show Continuous (fun s => peval r t + s * peval2 rs s t)
    exact continuous_const.add (continuous_id.mul ih)

/-- **Bernstein positivity on a box closed in `s`, half-open in `t`.** -/
theorem bern2_sound (As Bs : ℤ) (Ds : ℕ) (At Bt : ℤ) (Dt : ℕ) (mt : ℕ) (q : List (List ℤ))
    (hDs : 0 < Ds) (hDt : 0 < Dt) (hAB : As < Bs) (hchk : bern2OK As Bs Ds At Bt Dt mt q = true) {s t : ℝ}
    (hs0 : (As : ℝ) / Ds ≤ s) (hs1 : s ≤ (Bs : ℝ) / Ds) (ht0 : (At : ℝ) / Dt ≤ t) (ht1 : t < (Bt : ℝ) / Dt) :
    0 ≤ peval2 q s t := by
  have hDsR : (0 : ℝ) < Ds := by exact_mod_cast hDs
  have hDtR : (0 : ℝ) < Dt := by exact_mod_cast hDt
  have ht0' : (At : ℝ) ≤ Dt * t := by rw [div_le_iff₀ hDtR] at ht0; linarith
  have ht1' : (Dt : ℝ) * t < Bt := by rw [lt_div_iff₀ hDtR] at ht1; linarith
  have hsub : Set.Ico ((As : ℝ) / Ds) ((Bs : ℝ) / Ds) ⊆ {s | 0 ≤ peval2 q s t} := by
    intro s' hs'
    have a0 : (As : ℝ) ≤ Ds * s' := by have := hs'.1; rw [div_le_iff₀ hDsR] at this; linarith
    have a1 : (Ds : ℝ) * s' < Bs := by have := hs'.2; rw [lt_div_iff₀ hDsR] at this; linarith
    exact bern2_sound_ico As Bs Ds At Bt Dt mt q hDs hDt hchk a0 a1 ht0' ht1'
  have hcl : IsClosed {s | 0 ≤ peval2 q s t} := isClosed_le continuous_const (continuous_peval2_s q t)
  have hne : (As : ℝ) / Ds ≠ (Bs : ℝ) / Ds := by
    have : (As : ℝ) < Bs := by exact_mod_cast hAB
    exact ne_of_lt (div_lt_div_of_pos_right this hDsR)
  have hc := closure_minimal hsub hcl
  rw [closure_Ico hne] at hc
  exact hc ⟨hs0, hs1⟩

/-! ### Unit test: `P(s, t) = 1 - s t` is `≥ 0` on `[0, 1] × [0, 1)` (Möbius coefficients `1 + x + y`) -/

def testP : List (List ℤ) := [[1], [0, -1]]

theorem testP_ok : bern2OK 0 1 1 0 1 1 1 testP = true := by decide +kernel

example (s t : ℝ) (h1 : 0 ≤ s) (h2 : s ≤ 1) (h3 : 0 ≤ t) (h4 : t < 1) : 0 ≤ peval2 testP s t :=
  bern2_sound 0 1 1 0 1 1 1 testP (by norm_num) (by norm_num) (by norm_num) testP_ok
    (by norm_num [h1]) (by norm_num [h2]) (by norm_num [h3]) (by norm_num [h4])

end RieszN7.Bern2
