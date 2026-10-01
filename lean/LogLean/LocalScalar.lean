import Mathlib

/-!
# LocalScalar: the scalar argument of Lemma L′ (`local/LOCAL_LEMMA.md` §3′;
`check_local_rigorous.py` steps 9.2 / 9.3)

Variables: `a = |s|`, `b = |w|`, `T = |t| = √(a² + b²) ≤ ρ = 1/100`, `E = E(y) − E(P)`.
Input (all certified upstream of this file):
* (C′) (`LocalCert.Cprime`): ½⟨w,Hw⟩ + 3C(s,s,w) + Q(s) ≥ (1/16) b² + (29/500) a⁴;
* error blocks (L8): |3C(s,w,w)| ≤ 3γ₁ab², |C(w,w,w)| ≤ γ₂b³, |4D(s,s,s,w)| ≤ 4δ₁a³b,
  |6D(s,s,w,w) + 4D(s,w,w,w) + D(w,w,w,w)| ≤ c_q(a²+b²)b²;
* remainder (L9, L10): R₅ ≥ −K T⁵;
* certified rational upper bounds γ₁ ≤ 0.387896, γ₂ ≤ 1.319021, δ₁ ≤ 0.147314, c_q ≤ 4.203074,
  K ≤ 3.22942 (check_local_rigorous.txt steps 4, 5, 7).
Output: E ≥ 0.0342 b² + 0.0227 a⁴ (exact coefficients 0.0342998…, 0.0227595…).
The constants enter only through their upper bounds (every monomial they multiply is ≥ 0).
-/

namespace LocalScalar

/-- **Scalar core of Lemma L′.** Constants are real parameters bounded by the certified rationals. -/
theorem scalar_core {a b T E γ₁ γ₂ δ₁ cq K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) (hTab : T ^ 2 = a ^ 2 + b ^ 2) (hTρ : T ≤ 1 / 100)
    (hγ₁' : γ₁ ≤ 48487 / 125000)
    (hγ₂' : γ₂ ≤ 1319021 / 1000000)
    (hδ₁' : δ₁ ≤ 73657 / 500000)
    (hcq' : cq ≤ 2101537 / 500000)
    (hK' : K ≤ 161471 / 50000)
    (hP : (1 / 16) * b ^ 2 + (29 / 500) * a ^ 4
        - (3 * γ₁ * a * b ^ 2 + γ₂ * b ^ 3 + 4 * δ₁ * a ^ 3 * b + cq * (a ^ 2 + b ^ 2) * b ^ 2
          + K * T ^ 5) ≤ E) :
    (342 / 10000) * b ^ 2 + (227 / 10000) * a ^ 4 ≤ E := by
  have hρ0 : (0 : ℝ) ≤ 1 / 100 := by norm_num
  -- a, b ≤ ρ and T² ≤ ρ²
  have hT2 : T ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hT hTρ 2
  have ha2 : a ^ 2 ≤ (1 / 100) ^ 2 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ (1 / 100) ^ 2 := by nlinarith [sq_nonneg a]
  have haρ : a ≤ 1 / 100 := by nlinarith
  have hbρ : b ≤ 1 / 100 := by nlinarith
  have hab2 : 0 ≤ a * b ^ 2 := by positivity
  have hb2' : 0 ≤ b ^ 2 := sq_nonneg b
  have ha2b : 0 ≤ a ^ 2 * b := by positivity
  -- 3γ₁ab² ≤ 3·G1·ρ·b²
  have e1 : 3 * γ₁ * a * b ^ 2 ≤ 3 * (48487 / 125000) * (1 / 100) * b ^ 2 := by
    have h1 : γ₁ * (a * b ^ 2) ≤ (48487 / 125000) * (a * b ^ 2) := mul_le_mul_of_nonneg_right hγ₁' hab2
    have h2 : a * b ^ 2 ≤ (1 / 100) * b ^ 2 := mul_le_mul_of_nonneg_right haρ hb2'
    linarith
  -- γ₂b³ ≤ G2·ρ·b²
  have e2 : γ₂ * b ^ 3 ≤ (1319021 / 1000000) * (1 / 100) * b ^ 2 := by
    have h0 : 0 ≤ b ^ 3 := by positivity
    have h1 : γ₂ * b ^ 3 ≤ (1319021 / 1000000) * b ^ 3 := mul_le_mul_of_nonneg_right hγ₂' h0
    have h2 : b ^ 3 ≤ (1 / 100) * b ^ 2 := by
      have := mul_le_mul_of_nonneg_right hbρ hb2'
      linarith
    linarith
  -- c_q(a²+b²)b² ≤ CQ·ρ²·b²
  have e3 : cq * (a ^ 2 + b ^ 2) * b ^ 2 ≤ (2101537 / 500000) * (1 / 100) ^ 2 * b ^ 2 := by
    have h0 : 0 ≤ (a ^ 2 + b ^ 2) * b ^ 2 := by positivity
    have h1 : cq * ((a ^ 2 + b ^ 2) * b ^ 2) ≤ (2101537 / 500000) * ((a ^ 2 + b ^ 2) * b ^ 2) :=
      mul_le_mul_of_nonneg_right hcq' h0
    have h2 : (a ^ 2 + b ^ 2) * b ^ 2 ≤ (1 / 100) ^ 2 * b ^ 2 := by
      rw [← hTab]; exact mul_le_mul_of_nonneg_right hT2 hb2'
    linarith
  -- 4δ₁a³b ≤ 4δ₁ρa²b ≤ 2·D1·ρ(a⁴ + b²)
  have e4 : 4 * δ₁ * a ^ 3 * b ≤ 2 * (73657 / 500000) * (1 / 100) * (a ^ 4 + b ^ 2) := by
    have h0 : 0 ≤ a ^ 3 * b := by positivity
    have h1 : δ₁ * (a ^ 3 * b) ≤ (73657 / 500000) * (a ^ 3 * b) := mul_le_mul_of_nonneg_right hδ₁' h0
    have h2 : a ^ 3 * b ≤ (1 / 100) * (a ^ 2 * b) := by
      have := mul_le_mul_of_nonneg_right haρ ha2b
      linarith
    have h3 : 2 * (a ^ 2 * b) ≤ a ^ 4 + b ^ 2 := by linarith [sq_nonneg (a ^ 2 - b)]
    linarith
  -- K T⁵ ≤ K·ρ(a⁴ + 2ρ²b²)
  have e5 : K * T ^ 5 ≤ (161471 / 50000) * (1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2) := by
    have hT4 : T ^ 4 ≤ a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2 := by
      have h1 : T ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by rw [← hTab]; ring
      have h2 : b ^ 2 * (2 * a ^ 2 + b ^ 2) ≤ b ^ 2 * (2 * (1 / 100) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hb2'; linarith
      linarith
    have hT5 : T ^ 5 ≤ (1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2) := by
      have h0 : 0 ≤ T ^ 4 := by positivity
      have h1 : T ^ 5 = T * T ^ 4 := by ring
      rw [h1]
      calc T * T ^ 4 ≤ (1 / 100) * T ^ 4 := mul_le_mul_of_nonneg_right hTρ h0
        _ ≤ (1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2) := mul_le_mul_of_nonneg_left hT4 hρ0
    have h0 : 0 ≤ T ^ 5 := by positivity
    have h1 : K * T ^ 5 ≤ (161471 / 50000) * T ^ 5 := mul_le_mul_of_nonneg_right hK' h0
    linarith
  -- collect: coefficients 0.0342998… ≥ 0.0342 and 0.0227595… ≥ 0.0227 (exact rationals)
  have ha4 : 0 ≤ a ^ 4 := by positivity
  linarith

/-- **Parametric scalar core.** Same argument with symbolic constant bounds `G1 G2 D1 CQ KK ≥ 0` and
target coefficients `cw, cs` satisfying the two exact coefficient inequalities of steps 9.2 / 9.3
(ρ = 1/100, A = 1). Any certified set of constants closes L′ by `norm_num` on `hcw`, `hcs`. -/
theorem scalar_param {a b T E γ₁ γ₂ δ₁ cq K G1 G2 D1 CQ KK cw cs : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) (hTab : T ^ 2 = a ^ 2 + b ^ 2) (hTρ : T ≤ 1 / 100)
    (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) (hD1 : 0 ≤ D1) (hCQ : 0 ≤ CQ) (hKK : 0 ≤ KK)
    (hγ₁' : γ₁ ≤ G1) (hγ₂' : γ₂ ≤ G2) (hδ₁' : δ₁ ≤ D1) (hcq' : cq ≤ CQ) (hK' : K ≤ KK)
    (hcw : cw ≤ 1 / 16 - (3 * G1 + G2) * (1 / 100) - CQ * (1 / 100) ^ 2 - 2 * KK * (1 / 100) ^ 3
      - 2 * D1 * (1 / 100))
    (hcs : cs ≤ 29 / 500 - KK * (1 / 100) - 2 * D1 * (1 / 100))
    (hP : (1 / 16) * b ^ 2 + (29 / 500) * a ^ 4
        - (3 * γ₁ * a * b ^ 2 + γ₂ * b ^ 3 + 4 * δ₁ * a ^ 3 * b + cq * (a ^ 2 + b ^ 2) * b ^ 2
          + K * T ^ 5) ≤ E) :
    cw * b ^ 2 + cs * a ^ 4 ≤ E := by
  have hρ0 : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have hT2 : T ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hT hTρ 2
  have ha2 : a ^ 2 ≤ (1 / 100) ^ 2 := by nlinarith [sq_nonneg b]
  have hb2 : b ^ 2 ≤ (1 / 100) ^ 2 := by nlinarith [sq_nonneg a]
  have haρ : a ≤ 1 / 100 := by nlinarith
  have hbρ : b ≤ 1 / 100 := by nlinarith
  have hb2' : 0 ≤ b ^ 2 := sq_nonneg b
  have ha4 : 0 ≤ a ^ 4 := by positivity
  have hab2 : 0 ≤ a * b ^ 2 := by positivity
  have ha2b : 0 ≤ a ^ 2 * b := by positivity
  have e1 : 3 * γ₁ * a * b ^ 2 ≤ 3 * G1 * ((1 / 100) * b ^ 2) := by
    have h1 : γ₁ * (a * b ^ 2) ≤ G1 * (a * b ^ 2) := mul_le_mul_of_nonneg_right hγ₁' hab2
    have h2 : G1 * (a * b ^ 2) ≤ G1 * ((1 / 100) * b ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haρ hb2') hG1
    linarith
  have e2 : γ₂ * b ^ 3 ≤ G2 * ((1 / 100) * b ^ 2) := by
    have h0 : 0 ≤ b ^ 3 := by positivity
    have h1 : γ₂ * b ^ 3 ≤ G2 * b ^ 3 := mul_le_mul_of_nonneg_right hγ₂' h0
    have h3 : b ^ 3 ≤ (1 / 100) * b ^ 2 := by
      have := mul_le_mul_of_nonneg_right hbρ hb2'
      linarith
    have h2 : G2 * b ^ 3 ≤ G2 * ((1 / 100) * b ^ 2) := mul_le_mul_of_nonneg_left h3 hG2
    linarith
  have e3 : cq * (a ^ 2 + b ^ 2) * b ^ 2 ≤ CQ * ((1 / 100) ^ 2 * b ^ 2) := by
    have h0 : 0 ≤ (a ^ 2 + b ^ 2) * b ^ 2 := by positivity
    have h1 : cq * ((a ^ 2 + b ^ 2) * b ^ 2) ≤ CQ * ((a ^ 2 + b ^ 2) * b ^ 2) :=
      mul_le_mul_of_nonneg_right hcq' h0
    have h3 : (a ^ 2 + b ^ 2) * b ^ 2 ≤ (1 / 100) ^ 2 * b ^ 2 := by
      rw [← hTab]; exact mul_le_mul_of_nonneg_right hT2 hb2'
    have h2 : CQ * ((a ^ 2 + b ^ 2) * b ^ 2) ≤ CQ * ((1 / 100) ^ 2 * b ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hCQ
    linarith
  have e4 : 4 * δ₁ * a ^ 3 * b ≤ 2 * D1 * ((1 / 100) * (a ^ 4 + b ^ 2)) := by
    have h0 : 0 ≤ a ^ 3 * b := by positivity
    have h1 : δ₁ * (a ^ 3 * b) ≤ D1 * (a ^ 3 * b) := mul_le_mul_of_nonneg_right hδ₁' h0
    have h2 : a ^ 3 * b ≤ (1 / 100) * (a ^ 2 * b) := by
      have := mul_le_mul_of_nonneg_right haρ ha2b
      linarith
    have h3 : 2 * (a ^ 2 * b) ≤ a ^ 4 + b ^ 2 := by linarith [sq_nonneg (a ^ 2 - b)]
    have h4 : 2 * (a ^ 3 * b) ≤ (1 / 100) * (a ^ 4 + b ^ 2) := by linarith
    have h5 : D1 * (2 * (a ^ 3 * b)) ≤ D1 * ((1 / 100) * (a ^ 4 + b ^ 2)) :=
      mul_le_mul_of_nonneg_left h4 hD1
    linarith
  have e5 : K * T ^ 5 ≤ KK * ((1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2)) := by
    have hT4 : T ^ 4 ≤ a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2 := by
      have h1 : T ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by rw [← hTab]; ring
      have h2 : b ^ 2 * (2 * a ^ 2 + b ^ 2) ≤ b ^ 2 * (2 * (1 / 100) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hb2'; linarith
      linarith
    have hT5 : T ^ 5 ≤ (1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2) := by
      have h0 : 0 ≤ T ^ 4 := by positivity
      have h1 : T ^ 5 = T * T ^ 4 := by ring
      rw [h1]
      calc T * T ^ 4 ≤ (1 / 100) * T ^ 4 := mul_le_mul_of_nonneg_right hTρ h0
        _ ≤ (1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2) := mul_le_mul_of_nonneg_left hT4 hρ0
    have h0 : 0 ≤ T ^ 5 := by positivity
    have h1 : K * T ^ 5 ≤ KK * T ^ 5 := mul_le_mul_of_nonneg_right hK' h0
    have h2 : KK * T ^ 5 ≤ KK * ((1 / 100) * (a ^ 4 + 2 * (1 / 100) ^ 2 * b ^ 2)) :=
      mul_le_mul_of_nonneg_left hT5 hKK
    linarith
  have f1 : cw * b ^ 2 ≤ (1 / 16 - (3 * G1 + G2) * (1 / 100) - CQ * (1 / 100) ^ 2
      - 2 * KK * (1 / 100) ^ 3 - 2 * D1 * (1 / 100)) * b ^ 2 := mul_le_mul_of_nonneg_right hcw hb2'
  have f2 : cs * a ^ 4 ≤ (29 / 500 - KK * (1 / 100) - 2 * D1 * (1 / 100)) * a ^ 4 :=
    mul_le_mul_of_nonneg_right hcs ha4
  linarith

/-- The "Lean-cheap" constants of Lemma L′ (no projectors / no ONB of W):
γ₁ ≤ 0.387896 (penalty-PSD op-norm on W), γ₂ ≤ √5 ≤ 2.236068 (‖F₃‖_B² = 5 on ℝ¹⁴),
δ₁ ≤ 0.064044 (|g − Π_S g|, float probe), c_q ≤ 5.2006 (unprojected norms, float probe), K ≤ 3.22942.
Gives E ≥ 0.0266 b² + 0.0244 a⁴. -/
theorem scalar_cheap {a b T E γ₁ γ₂ δ₁ cq K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) (hTab : T ^ 2 = a ^ 2 + b ^ 2) (hTρ : T ≤ 1 / 100)
    (hγ₁' : γ₁ ≤ 48487 / 125000) (hγ₂' : γ₂ ≤ 2236068 / 1000000) (hδ₁' : δ₁ ≤ 64044 / 1000000)
    (hcq' : cq ≤ 52006 / 10000) (hK' : K ≤ 161471 / 50000)
    (hP : (1 / 16) * b ^ 2 + (29 / 500) * a ^ 4
        - (3 * γ₁ * a * b ^ 2 + γ₂ * b ^ 3 + 4 * δ₁ * a ^ 3 * b + cq * (a ^ 2 + b ^ 2) * b ^ 2
          + K * T ^ 5) ≤ E) :
    (266 / 10000) * b ^ 2 + (244 / 10000) * a ^ 4 ≤ E :=
  scalar_param ha hb hT hTab hTρ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hγ₁' hγ₂' hδ₁' hcq' hK' (by norm_num) (by norm_num) hP

/-- The checker's constants through the parametric core (cross-check of `scalar_core`). -/
example {a b T E γ₁ γ₂ δ₁ cq K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) (hTab : T ^ 2 = a ^ 2 + b ^ 2) (hTρ : T ≤ 1 / 100)
    (hγ₁' : γ₁ ≤ 48487 / 125000) (hγ₂' : γ₂ ≤ 1319021 / 1000000) (hδ₁' : δ₁ ≤ 73657 / 500000)
    (hcq' : cq ≤ 2101537 / 500000) (hK' : K ≤ 161471 / 50000)
    (hP : (1 / 16) * b ^ 2 + (29 / 500) * a ^ 4
        - (3 * γ₁ * a * b ^ 2 + γ₂ * b ^ 3 + 4 * δ₁ * a ^ 3 * b + cq * (a ^ 2 + b ^ 2) * b ^ 2
          + K * T ^ 5) ≤ E) :
    (342 / 10000) * b ^ 2 + (227 / 10000) * a ^ 4 ≤ E :=
  scalar_param ha hb hT hTab hTρ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hγ₁' hγ₂' hδ₁' hcq' hK' (by norm_num) (by norm_num) hP

/-- **Lemma L′, scalar form with the error terms split as in §2 / L8.**
`E ≥ X2 + X3a + X3b + X4a + X4b + R` is the decomposition 𝒫 = F₂ + F₃ + F₄ + R₅ with
X2 = ½⟨w,Hw⟩ + 3C(s,s,w) + Q(s), X3a = 3C(s,w,w), X3b = C(w,w,w), X4a = 4D(s,s,s,w),
X4b = 6D(s,s,w,w) + 4D(s,w,w,w) + D(w,w,w,w), R = R₅ (and C(s,s,s) = 0). -/
theorem Lprime_scalar {a b T E X2 X3a X3b X4a X4b R : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T) (hTab : T ^ 2 = a ^ 2 + b ^ 2) (hTρ : T ≤ 1 / 100)
    (hE : X2 + X3a + X3b + X4a + X4b + R ≤ E)
    (h2 : (1 / 16) * b ^ 2 + (29 / 500) * a ^ 4 ≤ X2)
    (h3a : |X3a| ≤ 3 * (48487 / 125000) * a * b ^ 2)
    (h3b : |X3b| ≤ (1319021 / 1000000) * b ^ 3)
    (h4a : |X4a| ≤ 4 * (73657 / 500000) * a ^ 3 * b)
    (h4b : |X4b| ≤ (2101537 / 500000) * (a ^ 2 + b ^ 2) * b ^ 2)
    (hR : -((161471 / 50000) * T ^ 5) ≤ R) :
    (342 / 10000) * b ^ 2 + (227 / 10000) * a ^ 4 ≤ E := by
  refine scalar_core (γ₁ := 48487 / 125000) (γ₂ := 1319021 / 1000000) (δ₁ := 73657 / 500000)
    (cq := 2101537 / 500000) (K := 161471 / 50000) ha hb hT hTab hTρ
    le_rfl le_rfl le_rfl le_rfl le_rfl ?_
  have := neg_abs_le X3a
  have := neg_abs_le X3b
  have := neg_abs_le X4a
  have := neg_abs_le X4b
  linarith

/-- **Equality case (L13, scalar part).** Under the hypotheses of `Lprime_scalar`, `E ≥ 0`, and
`E ≤ 0` forces `a = 0` and `b = 0` (hence t = 0, hence y = P by the chart, L1). -/
theorem Lprime_nonneg_eq {a b E : ℝ}
    (hL : (342 / 10000) * b ^ 2 + (227 / 10000) * a ^ 4 ≤ E) :
    0 ≤ E ∧ (E ≤ 0 → a = 0 ∧ b = 0) := by
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have ha4 : 0 ≤ a ^ 4 := by positivity
  refine ⟨by linarith, fun hE => ⟨?_, ?_⟩⟩
  · have : a ^ 4 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  · have : b ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.1 this

end LocalScalar

#print axioms LocalScalar.Lprime_scalar
#print axioms LocalScalar.Lprime_nonneg_eq
#print axioms LocalScalar.scalar_cheap
