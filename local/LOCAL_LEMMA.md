# Quartic local lemma for the log energy at the pentagonal bipyramid

This replaces upstream `local_ineq` / `pent_local_min` (PAPER.md §7.2 step 5). That lemma says
E − E(P) ≥ c|y − P|², which is false for the log kernel. The replacement is a centre-manifold
("complete the square") inequality with a quartic term in the soft pucker directions.

"Upstream" and "PAPER.md" refer to the Coulomb proof, https://github.com/huwngtran/thomson-n7-lean, `paper/PAPER.md`.
The constants were first computed with exploratory mpmath scripts (40–50 digits) that are not included here; some
sentences below still refer to them (marked "exploratory").

**Rigorous status.** Every constant in the log proof chain is re-derived with enclosures by
`check_local_rigorous.py` (output `../verification/check_local_rigorous.txt`, **45/45 PASS**, about 1.5 min on one
core). It has no project imports, and no constant of the proof chain is taken from floating point. Floating-point
eigensolvers only propose certificate parameters (the shift c of the γ₁ bound, the roundings of the PSD matrices);
each proposal is then certified as follows:
- exact arithmetic in K = Q(α), α = √(10+2√5) = 4 sin 72° (sympy), for P, the frames, μ_i, the Taylor polynomial
  of the minorant to degree 6, H, its kernel, the projectors, the coupling, Q, Q_eff, κ² and the Bombieri norms;
- arb balls (python-flint, 320 bits) for anything that needs a square root: the orthonormal bases (ball
  Gram–Schmidt of exact data), the block tensor norms, √(1−g²), N(ρ) = 1−√(1−ρ²) and the majorant tail;
- exact LDLᵀ over Q, applied to a dyadic rounding with a rigorous Frobenius bound on the rounding error, for the
  PSD certificates (the op-norm bound for γ₁ and the Lean-form certificate of §3′);
- exact `Fraction` arithmetic for the scalar arguments of §3 and §3′, using rational upper bounds read off the balls.

§9 lists the steps. The Riesz-2 constants (§7) have **not** been redone this way; they are still mpmath floats.

## 0. Results

| quantity | log (s=0) | Riesz s=2 |
|---|---|---|
| Hessian spectrum on W (9-dim), in the convention F₂ = ½⟨w,Hw⟩ | 3/4 (×2), 9/4 (×2), 3 (×5) | (27−√105)/8 ≈ 2.0941 (×2), 4, 9/2 (×2), (27+√105)/8 (×2), 9 (×2) |
| λ_W | **3/4** | 2.09413 |
| pure cubic C(s,s,s) | **0**, forced by symmetry (exact polynomial identity) | 0 |
| quartic Q(s) on S | (13/40)\|s\|⁴, isotropic | (19/20)\|s\|⁴ |
| coupling c(s)=C(s,s,·)∈W, with \|c(s)\| = γ\|s\|² | γ² = 23/480 | γ² = 35/96 |
| **Q_eff = Q − (9/2)⟨c,H_W⁻¹c⟩** | **(1/10)\|s\|⁴** (exact, isotropic) | **(18/65)\|s\|⁴** |
| naive Q − 9γ²/(2λ_W) | 3/80 = 0.0375 > 0 | 0.1666 > 0 |
| κ = \|w*(s)\|/\|s\|², with w* = −3H_W⁻¹c(s) | √(67/120) = 0.74722 | √(805/1352) = 0.77163 |
| certified radius, ℓ² tangent norm (Bombieri route, §4b) | max ≈ 0.01795 (float, not certified); **stated at 1/100** | max ≈ 0.00837; stated at 1/200 |
| certified radius (pure-majorant route, §4a) | max ≈ 0.00336; stated at 1/400 | max ≈ 0.00190; stated at 1/600 |
| lower bound at the stated radius (Lemma L, §3) | E − E(P) ≥ **0.2015\|v\|² + 0.0454\|s\|⁴** (certified with enclosures) | ≥ 0.4722\|v\|² + 0.1130\|s\|⁴ (floats only) |
| Lean form (Lemma L′, §3′), same radius | E − E(P) ≥ **0.0342\|w\|² + 0.0227\|s\|⁴** (certified) | — |
| sup-norm radius (upstream shape) | **1/300**, compared with upstream's 1/30000 | 1/530 |
| Gram window τ the cap must deliver | **τ ≤ 1/1650** | τ ≤ 1/2915 |

- Log: 3/4, 13/40, 23/480, 1/10 and 67/120 are now **proved exactly** (polynomial identities over Q(α), steps 2–3 of
  `check_local_rigorous.py`). The Riesz-2 values 19/20, 35/96 and 18/65 still only match to more than 38 digits.
- (Exploratory, float.) The optimisation that relaxes w reproduces the coefficient 0.10. On spheres |t| = r in T the
  minimum of E − E(P)/r⁴ is 0.1023 at r = 0.01, 0.0971 at r = 0.1 and 0.048 at r = 0.45, and it
  stays positive throughout (float64 minimisation, not certified). Numerically, the basin is therefore much larger
than the certified radius; only the radius 1/100 is certified.

At the stated radius the scalar argument of §3 closes. The resulting sup-norm radius 1/300 is 100 times upstream's 1/30000.

The cost moves to the cap certificate (§6). The soft mode moves the pole–ring inner products at
first order. So H_B must osculate φ to third order at t = 0, and B-class coercivity scales as
τ ≈ (δ/κ₄)^{1/4} with κ₄ ≤ 1/6.

For τ = 1/1650 the certificate slack must therefore satisfy **δ ≲ κ₄τ⁴ ≤ 2.2·10⁻¹⁴**.

## 1. Coordinates and an exact identity (no derivative bounds on log needed)

**Setting.** Label the ring points 0..4 at angles 2πk/5, the north pole 5 and the south pole 6.
Write g_ij = ⟨P_i,P_j⟩ ∈ {c₁, c₂, 0, −1}, with c₁ = cos 72° and c₂ = cos 144°.
The kernel is φ(t) = −½ log(2−2t), with W_ij = φ'(g_ij) = 1/(2(1−g_ij)).
P is critical: Σ_j W_ij P_j = μ_i P_i, with μ_ring = c₁/(1−c₁) + c₂/(1−c₂) = 1/√5 − 1/√5 = **0** and μ_pole = **−1/4**.

**Chart.** Assume ⟨y_i,P_i⟩ > 0, which holds whenever ‖y_i − P_i‖ < √2. Set
t_i := y_i − ⟨y_i,P_i⟩P_i ⊥ P_i and ν_i := ⟨y_i,P_i⟩ − 1 = −½‖h_i‖², where h_i = y_i − P_i = t_i + ν_iP_i.
Then y_i = √(1−|t_i|²) P_i + t_i and |t_i| ≤ ‖h_i‖.

**Gauge.** The upstream condition (`exists_gauge`) is that Σ P_i ⊗ y_i is symmetric. This is exactly
h ⊥ {(AP_i)_i : A ∈ so(3)}. Normal vectors are automatically orthogonal to these rotation fields,
so the gauge is equivalent to t ⊥ so(3)·P.

T is the resulting 11-dimensional space (14 tangent dimensions minus 3 rotations), with norm
|t|² = Σ|t_i|² ≤ Σ‖h_i‖². Split T = S ⊕ W orthogonally:
- S = span(s₁,s₂). Here s₁ is the ring-vertical field √(2/5)·cos(4πk/5)·e_z at ring point k, and s₂ is the same with sin.
- W is the 9-dimensional orthogonal complement of S in T.
- The certificates (§2 step 3, §3′, §8.3) and `check_local_rigorous.py` use the **unnormalised** fields
  ŝ_α = √(5/2)·s_α, i.e. ŝ₁ = cos(4πk/5)·e_z and ŝ₂ = sin(4πk/5)·e_z at ring point k, with |ŝ_α|² = 5/2. In these
  coordinates s = σ₁ŝ₁ + σ₂ŝ₂, so |s|² = (5/2)|σ|² and |s|⁴ = (25/4)|σ|⁴.

H·s = 0 holds as vectors in R¹⁴ (numerically < 1e-40), so S is exactly the kernel of the Hessian on T.

**Exact identity.** Let u_ij := (⟨y_i,y_j⟩ − g_ij)/(1 − g_ij) and ψ(u) := −log(1−u) − u. Then

  E(y) − E(P) = Σ_i μ_i ν_i + Σ_{i<j} [ W_ij ⟨h_i,h_j⟩ + ½ ψ(u_ij) ].    (1)

This follows from φ(g+τ) − φ(g) = −½log(1−u). The linear part Σ W_ij(⟨P_i,h_j⟩+⟨h_i,P_j⟩) collapses by
criticality to Σ μ_iν_i. It is the log analogue of upstream `sum_W_tau` and `energy_ge_cubic`.

**Polynomial minorant.** Let ψ₅(u) := u²/2 + u³/3 + u⁴/4 + u⁵/5. Then ψ(u) ≥ ψ₅(u) for **all** u < 1:
the difference vanishes at 0 and has derivative u⁵/(1−u), so it decreases for u < 0 and increases for u > 0.

Hence E(y) − E(P) ≥ 𝒫(t), the right-hand side of (1) with ψ replaced by ψ₅. The dropped part is
Σ_{k≥6} u^k/k, which is of order t⁶. Therefore 𝒫 has the *same* Taylor polynomial as E through
order 5 in t.

Truncating at degree 3, as upstream does for Coulomb, would lose the u⁴/4 terms and give the wrong
quartic. Degree 5 is the minimal valid odd truncation.

The point terms: ring points have μ = 0. For the poles, μν = −¼(√(1−r²)−1) has a degree-≥5 remainder
that is ≥ 0, so it can be dropped.

## 2. Taylor data on S ⊕ W (log)

Write 𝒫(t) = F₂ + F₃ + F₄ + R₅, with F₂ = ½⟨w,Hw⟩, F₃ = C(t,t,t) and F₄ = D(t,t,t,t) symmetric tensors.

**Symmetry.** The C₅ rotation acts on S as rotation by 4π/5, because cos(4πk/5+θ) shifts θ by 4π/5.
Write a = s₁ + i s₂. The monomials a³, a²ā, a⁴ and a³ā are not invariant.
- Therefore **C(s,s,s) ≡ 0**, and every C₅-invariant quartic on S is a multiple of |s|⁴.
- Q(s) = (13/40)|s|⁴.
- s⊗s = |a|² ⊕ a². The coupling c(s)_k = C(s,s,e_k) lives only in the H-eigenspaces for 3/4
  (squared weight 49/1440) and for 3 (squared weight 1/72). So |c(s)|² = (23/480)|s|⁴ exactly.

**Completing the square.** Let w*(s) = −3H_W⁻¹c(s) and v = w − w*(s). Then

  ½⟨w,Hw⟩ + 3C(s,s,w) + Q(s) = ½⟨v,Hv⟩ + Q_eff(s),
  Q_eff = 13/40 − (9/2)(49/1440·4/3 + 1/72·1/3) = 13/40 − 9/40 = **1/10**   (times |s|⁴).

The naive operator-norm version, ½λ_W b² − 3γa²b + Q ≥ (13/40 − 9γ²/(2λ_W))a⁴ = (3/80)a⁴, also
stays positive but loses a factor of 2.7. Lemma L (§3) uses the exact square. It is an identity over Q(α), with
w*(s) = −H_W⁻¹G_W(s), G_W = Π_W∇F₃(s) = 3c(s); `check_local_rigorous.py` step 3 verifies it as a polynomial
identity in σ (s = σ₁ŝ₁ + σ₂ŝ₂, unnormalised fields of §1), together with H·(H_W⁻¹G_W) = G_W, |c|² = (23/480)|s|⁴ and |w*|² = (67/120)|s|⁴.
A PSD certificate with rational margins does **not** prove this identity; it proves the weaker |w|²-form that
Lemma L′ (§3′) uses. That is the form planned for Lean (§8.3).

**Tensor norms used for the error terms.** Here a = |s| and b = |w|. All values below are **certified
upper bounds** (steps 4–5 of `check_local_rigorous.py`).
- The block norms are Frobenius norms of the restricted blocks. Their squares are **exact rationals**. They are
  computed basis-free over Q(α) as ⟨T, T ×₁ Π₁ ⋯ ×_d Π_d⟩ with the exact projectors Π_S and Π_W (step 4.5):
  - ‖C_sww‖² = 65/108 and ‖C_www‖² = 1879/1080;
  - ‖D_sssw‖² = 25/1152 and ‖D_ssww‖² = 455641/1166400;
  - ‖D_swww‖² = 208051/777600 and ‖D_wwww‖² = 47417897/13996800.

  They are cross-checked by ball tensors in a ball-Gram–Schmidt orthonormal basis of S ⊕ W (radii ≈ 1e−90).
- γ₁ = √(Σ_α‖C(e_α,·,·)|_W‖²_op), which is sharper than the Frobenius norm ‖C_sww‖_F ≤ 0.775792.
  - Each operator norm is ≤ c = 0.27428359. This is certified by showing c·I ∓ C(e_α,·,·)|_W ≻ 0 via exact LDLᵀ over Q
    of the 2⁻⁶⁴-rounded 9×9 matrix, shifted by the Frobenius norm of the rounding error (≤ 1.1e−19).
  - Hence γ₁ ≤ √2·c ≤ 0.387896.
  - (Numerically ‖C(e_α,·,·)|_W‖²_op = 65/864 for both α, so γ₁² = 65/432 and ‖C_sww‖²_F = 8·65/864. A float scan
    suggests that sup_{|s|=1}‖C(s,·,·)|_W‖ = 0.274284 is isotropic. A certificate over the circle would lower γ₁ by
    a factor √2. This is not needed.)
- The old values 1.319020 and 0.517257 were roundings *down*; the certified bounds are 1.319021 and 0.517258.

| term | bound (certified) |
|---|---|
| 3C(s,w,w) | 3γ₁ab², γ₁ ≤ 0.387896 |
| C(w,w,w) | γ₂b³, γ₂ ≤ 1.319021 |
| 4D(s,s,s,w) | 4δ₁a³b, δ₁ ≤ 0.147314 |
| 6D(s,s,w,w) + 4D(s,w,w,w) + D(w,w,w,w) | ≤ c_q (a²+b²) b², with δ₂,δ₃,δ₄ ≤ 0.625011, 0.517258, 1.840589 and c_q = 4.203074 ≥ λ_max[[6δ₂,2δ₃],[2δ₃,δ₄]] (exact 2×2 test on the rational bounds) |

## 3. The inequality (log): statement and scalar proof

**Lemma L (log).** Let y ∈ (S²)⁷ satisfy the upstream gauge condition and Σ_i‖y_i−P_i‖² ≤ ρ², with ρ = 1/100.
Let t, s = Π_S t, w = Π_W t and v = w − w*(s) be as above. Then

  E(y) − E(P) ≥ 0.2015 |v|² + 0.0454 |s|⁴.

In particular E(y) ≥ E(P), with equality iff s = 0 and v = 0, that is iff t = 0, that is iff y = P.

**Proof.** Let a = |s|, x = |v| and b = |w|. Then a, b ≤ |t| ≤ ρ, b ≤ x + κa², and b² ≤ (1+η)x² + (1+1/η)κ²a⁴.

§1 and §2 give 𝒫 ≥ (λ_W/2)x² + a⁴/10 − Err, where

  Err = 3γ₁ab² + γ₂b³ + 4δ₁a³b + c_q(a²+b²)b² + K(a²+b²)^{5/2}.

Bound the pieces as follows:
- 3γ₁ab² + γ₂b³ ≤ (3γ₁+γ₂)ρ b².
- c_q(a²+b²)b² ≤ c_qρ² b².
- K(a²+b²)^{5/2} ≤ Kρ(a⁴ + 2ρ²b²).
- 4δ₁a³b ≤ 4δ₁κρ a⁴ + 2δ₁ρ(A a⁴ + x²/A).

Take A = 1/16 and η = 4. The constants are the certified rational upper bounds of §2 and §4b:
- γ₁ ≤ 0.387896, γ₂ ≤ 1.319021, δ₁ ≤ 0.147314 and c_q ≤ 4.203074;
- K = B₅ + B₆ρ + K₇ρ² ≤ 3.22942 at ρ = 1/100;
- κ ≤ 0.747218, κ² = 67/120, λ_W = 3/4 and Q_eff = 1/10 (exact).

Then, in exact rational arithmetic (step 8 of `check_local_rigorous.py`):
- The b² coefficient is β_b = (3γ₁+γ₂)ρ + c_qρ² + 2Kρ³ ≤ 0.0252539.
- The x² error is 5β_b + 32δ₁ρ < 3/8, which leaves **0.201590 ≥ 0.2015**.
- The a⁴ error is Kρ + 4δ₁κρ + δ₁ρ/8 + (5/4)κ²β_b < 1/10, which leaves **0.0454935… ≥ 0.0454**. ∎

The printed coefficients in this section and in §3′ are decimal roundings (6 digits, the checker's output format)
of exact rationals; what is checked is the exact inequality against the stated constant. Exact values:
0.2015902388… and 0.0454935434…

**Fallback.** Replace γ₁ by the Frobenius bound ‖C_sww‖_F ≤ 0.775792, which needs no operator-norm certificate.
With the same A and η the lemma still closes, with 0.143406|v|² + 0.037372|s|⁴ (step 8.4).

Every step is a scalar inequality between monomials in (a, b, x, ρ), which suits nlinarith.
An exploratory search over A and η with bisection on ρ indicates that the same argument works up to ρ ≈ 0.01795
(this maximal radius comes from the float constants and has not been re-certified). At that radius Kρ ≈ 0.06 and the
b²-terms ≈ 0.032 exhaust the budget of 1/10.

## 3′. Lean form: the same bound in (|w|, |s|) without the exact square

A Lean-checkable PSD certificate with rational margins cannot reproduce the exact square: that is an identity over
Q(α) involving w*(s). What it proves instead is a bound in the variables a = |s| and b = |w|. The scalar argument
therefore has to be redone in (a, b), with no x = |v|.

**Certificate (C′).** For all w ∈ W and s ∈ S,

  ½⟨w,Hw⟩ + 3C(s,s,w) + (13/40)|s|⁴ ≥ ε|w|² + q′|s|⁴,  with ε = 1/16 and q′ = 29/500 = 0.058.

Take m = (σ₁², σ₁σ₂, σ₂²), where s = σ₁ŝ₁ + σ₂ŝ₂ with the unnormalised fields ŝ_α of §1 (|ŝ_α|² = 5/2). Then:
- |s|⁴ = (25/4) mᵀG_θm, with G_θ = [[1,0,θ],[0,2−2θ,0],[θ,0,1]]; this holds for every θ, because m₂² = m₁m₃;
- 3C(s,s,w) = ⟨Γ_W m, w⟩, where Γ_W = Π_W∇F₃ (a 14×3 matrix over Q(α)).

(C′) is implied by (not equivalent to) the positive definiteness of the 17×17 matrix

  M = [[½H − εΠ_W + Π_ker, ½Γ_W], [½Γ_Wᵀ, (13/40 − q′)(25/4)G_θ]]   (θ = −4999/5000).

The implication is one-way because M ≻ 0 is a statement for all (z, m) ∈ R¹⁴ × R³, whereas the m arising from s
satisfies m₂² = m₁m₃. The Π_ker term makes the w-block definite on the kernel directions, which are harmless since only z = w ∈ W matters.
Step 9.1 of the checker certifies M ≻ 0 by exact LDLᵀ over Q of the 2⁻⁶⁴ dyadic rounding, shifted by the rounding
error (≤ 1.8e−19). The float λ_min is 2.7e−4 and the minimum pivot is 6.0e−4.

For comparison, for ε = 1/16 the exact optimum is q′ < 13/40 − (9/2)[(49/1440)/(3/4−2ε) + (1/72)/(3−2ε)] = 0.058261.

**Lemma L′ (log, Lean form).** Under the hypotheses of Lemma L,

  E(y) − E(P) ≥ 0.0342 |w|² + 0.0227 |s|⁴,

with equality iff y = P.

**Proof.** By §1, (C′), §2 and §4b, 𝒫 ≥ εb² + q′a⁴ − Err, with Err as in §3. As before:
- 3γ₁ab² + γ₂b³ + c_q(a²+b²)b² + K|t|⁵ ≤ β_b b² + Kρ a⁴;
- 4δ₁a³b ≤ 4δ₁ρa²b ≤ 2δ₁ρ(A a⁴ + b²/A), with A = 1.

Hence:
- the b² coefficient is ε − β_b − 2δ₁ρ = 0.034300 ≥ 0.0342;
- the a⁴ coefficient is q′ − Kρ − 2δ₁ρ = 0.022760 ≥ 0.0227.

These are steps 9.2 and 9.3, in exact rationals. The bound vanishes only at s = 0, w = 0, i.e. t = 0. ∎

Lemma L′ gives exactly what the handoff (§6) uses: E ≥ E(P) on the ℓ² ball of radius 1/100, with equality only at
P. So the sup radius 1/300 and the Gram window τ ≤ 1/1650 are unchanged. Lemma L′ can therefore replace Lemma L in
the formal proof. Lemma L remains the sharper paper statement.

## 4. The remainder R₅ (degree ≥ 5 in t)

There are no derivative bounds on log: after (1) and ψ ≥ ψ₅, R₅ is the tail of explicit per-pair
analytic functions. f_ij(t_i,t_j) = W_ij⟨h_i,h_j⟩ + ½ψ₅(u_ij) depends only on the four coordinates of
(t_i,t_j). Let R_ij = (r_i² + r_j²)^{1/2}, where r_i = |t_i|.

**(a) Pure majorant (simplest for Lean).** Replace each ingredient by a majorant in R, with nonnegative
coefficients bounding each homogeneous part:
- |t_i|, |t_j| ≤ R.
- ν_i, ν_j and ν_i+ν_j are bounded by N(R) = 1−√(1−R²).
- |⟨t_i,t_j⟩| ≤ R²/2.
- |⟨P_i,t_j⟩| ≤ √(1−g²)·r_j.
- |ℓ_ij| ≤ √2·√(1−g²)·R.
- HH = R²/2 + 2√(1−g²)RN + |g|N².
- U = (√2√(1−g²)R + |g|N + HH)/(1−g).
- F = W·HH + ½ψ₅(U).

The degree-≥5 part of f_ij is then bounded by F(R) − [F]_{≤4}(R) ≤ K_ij(ρ)R⁵. The ratio increases in R,
so evaluating at R = ρ suffices.

Summing uses Σ_{i<j}K_ij R_ij⁵ ≤ |t|³ Σ_i r_i² Σ_j K_ij, which gives R₅ ≥ −K|t|⁵ with
K = max_i Σ_{j≠i} K_ij. The per-pair K_ij are 10.77 (adjacent ring pair), 0.279 (ring diagonal),
2.83 (pole–ring) and ≈ 0 (pole–pole). In total **K = 27.76**, which gives ρ ≤ 0.00336.

**(b) Exact degree 5 and 6 plus a majorant tail (used for Lemma L).**
- Compute the global homogeneous parts 𝒫₅ and 𝒫₆ as exact polynomials in the 14 tangent coordinates.
- Bound them by the Bombieri norm, |p(x)| ≤ ‖p‖_B|x|^d with ‖p‖_B² = Σ c_m² m!/d!. The squares are exact rationals
  (step 6): **B₅² = 7801/800** and **B₆² = 2857757/28800**, so B₅ ≤ 3.12270 and B₆ ≤ 9.961309.
- Bound the tail of degree ≥ 7 with (a) started at degree 7. In arb balls (step 7), with √(1−g²) and
  N(ρ) = 1 − √(1−ρ²) enclosed and exact series coefficients, K₇ ≤ 70.9738 at ρ = 1/100.
  - The subtraction F(ρ) − [F]_{≤6}(ρ) cancels about 8 digits; this is harmless at 320 bits.
  - Route (a) at ρ = 1/100 gives K ≤ 28.175 (not used).

So K = B₅ + B₆ρ + K₇ρ² ≤ **3.22942** at ρ = 1/100.

This remainder bound avoids any reference to the 5th derivatives of −log(distance): everything is
finite polynomial algebra plus √(1−r²).

## 5. Numerical sanity checks (exploratory, 50 digits; script not included)

Test points are random gauge-fixed t ∈ T with |t| = r for r ∈ {ρ/10, ρ/2, ρ, 2ρ, 5ρ}. The radius is the tangent
norm |t|, not the chordal norm (Σ‖y_i − P_i‖²)^{1/2} of Lemma L; since |t| ≤ ‖y − P‖, a point with |t| = ρ can lie
slightly outside the lemma's ball. Half have
uniform directions. The other half are soft-biased: t = s + w*(s) + ε·v̂ with ε ∈ {0, 0.01, 0.1, 1}·a².

- No violations: E > E(P) everywhere, and E − E(P) ≥ the certified bound 0.2015x² + 0.0454a⁴ inside ρ.
- The minimum ratio of E − E(P) to the bound is **≈ 1.861** (an earlier version of this note said 2.20).
  - It is approached along the λ_W = 3/4 eigenspace of W, with s = 0 (so v = w). There E − E(P) = (3/8)|v|² + O(|v|³),
    so the ratio tends to (3/8)/0.2015 = 1.8610 as |t| → 0. `check_local_rigorous.py` step 11 finds 1.86104 at |t| = 10⁻³.
  - An independent adversarial Nelder–Mead search over the closed ball found 1.8608.
  - The exploratory sampling did not probe pure-W directions adversarially. Its 2.20 is the value **on the centre manifold**
    (v = 0), where E − E(P) = 0.1000a⁴ and the ratio is 0.1/0.0454 = 2.2026.
- For Riesz-2 the minimum ratio is 2.45, with E − E(P) = 0.27692a⁴.
- A float64 BFGS minimisation on spheres in T (§0) finds positivity up to r = 0.45 (numerical, not certified).

## 6. How it plugs into the cap (PAPER.md §7.2) and what the cap must now deliver

- **Steps 1–3** (slack ≤ δ, coercivity, pentagon rigidity) are unchanged.
- **Step 4** (`localGram_of_localMinAt`) turns a Gram window w into the coordinate radius (11/2)w.
- **Step 5:** `pent_local_min_sup` becomes "every z with ‖z_i−P_i‖ ≤ 1/300 has E(z) ≥ E(P), with equality only on O(3)·P".
  - The proof is the same as upstream: `exists_gauge` reduces the ℓ² distance, √7/300 = 0.00882 ≤ 1/100, and then Lemma L applies.
    Lemma L′ (§3′) works equally well, since only positivity and the equality case are used. The handoff constants are
    checked exactly in step 10.
  - `pent_local_min` needs the equality clause only from Lemma L's strict positivity.
- Therefore the Gram window must be **τ ≤ (1/300)/5.5 = 1/1650** (upstream: 1/165000), with ring rigidity needing τ ≤ 1/10. Other routes give different windows:
  - maximal (b) radius (ℓ² 0.01795, sup 0.00678; float, not certified): τ ≈ 1/810;
  - pure-majorant route (a) at ρ = 1/400 (sup radius 1/1100): τ = 1/6050.

**Warning: the coercivity is quartic in class B.** Along the soft mode the pole–ring inner products
move at first order: t_B = ±z_k, with Σ_B t_B⁴ = 0.6a⁴. Meanwhile E − e ≈ 0.1a⁴ + (E(P) − e).
A sharp typed bound therefore forces φ − H_B = O(t⁴) at 0, so H_B matches φ through the third
derivative. This matches the numerical observation that the typed cap bound is sharp at degree 12 but not at degree 10. It also forces
κ₄ := inf(φ − H_B)/t⁴ ≤ 0.1/0.6 = **1/6**.

Coercivity φ − H_B ≤ δ ⇒ |t| ≤ τ then requires **δ ≤ κ₄τ⁴**:
- τ = 1/1650: δ ≲ 2.2·10⁻¹⁴·(6κ₄);
- τ = 1/810 (maximal radius): δ ≲ 3.9·10⁻¹³·(6κ₄);
- τ = 1/6050 (route a): δ ≲ 1.2·10⁻¹⁶·(6κ₄), which is below upstream's δ = 5·10⁻¹⁶. So route (a) is too weak and (b) is needed.

Classes A and C have generic quadratic contact, τ ≈ √(δ/κ₂). They are harmless.

Every factor gained in the local radius buys its 4th power in δ. A larger certified basin is
therefore the cheapest lever. Numerically (float, not certified) the basin reaches |t| ≳ 0.45, and an interval branch-and-bound
local lemma at ρ = 0.1 would give τ ≈ 1/145 and allow δ ≈ 4·10⁻¹⁰·(6κ₄).

The certificate itself must still be exact: e ≤ E(P) = −log(1600√5), with E(P) − e ≤ δ.

## 7. Riesz s = 2 (kernel 1/(2−2t))

The same proof works verbatim:
- W = 1/(2(1−g)²), μ_ring = 2/5 and μ_pole = −1/8.
- φ(g+τ) − φ(g) − Wτ = u²/(2(1−g)(1−u)) ≥ (u² + u³ + u⁴ + u⁵)/(2(1−g)), because the remainder u⁶/(1−u) ≥ 0.
- The ring point terms have μ > 0, so their degree-≥6 remainder is kept in B₆ and K₇.

The constants are in §0:
- λ_W = (27−√105)/8, Q = 19/20, γ² = 35/96 and **Q_eff = 18/65**;
- tensor norms γ₁ = 1.0560, γ₂ = 7.536, δ₁ = 0.5539 and c_q = 19.80;
- B₅ = 23.39, B₆ = 70.27 and K₇ = 423.8 (at ρ = 1/200).

The results:
- **Lemma L₂:** at ℓ² radius 1/200, E − E(P) ≥ 0.4722|v|² + 0.1130|s|⁴. The certified maximum is 0.00837.
- Sup radius 1/530, so τ ≤ 1/2915. B-class coercivity has κ₄ ≤ (18/65)/0.6 ≈ 0.46.

## 8. Notes for a Lean port (not carried out)

1. **(1) and ψ ≥ ψ₅.** Generalise `sum_W_tau` and `energy_ge_cubic`. The inequality
   −log(1−u) ≥ u + … + u⁵/5 follows by monotonicity of the difference, or from Mathlib's `Real.log` series bounds.
2. **The chart without √.** Take t_i := h_i − ⟨P_i,h_i⟩P_i and ν_i = −½‖h_i‖². The √ appears only in
   the majorant N(R). For Lean, replace N(R) by an explicit tail bound: its coefficients are
   ≤ 1/2, so N − R²/2 − R⁴/8 ≤ R⁶/(2(1−R²)).
3. **The Taylor data and the quadratic step.** H, the cubic and quartic
   parts, Π_S = s₁s₁ᵀ + s₂s₂ᵀ = (2/5)(ŝ₁ŝ₁ᵀ + ŝ₂ŝ₂ᵀ), Π_ker and Π_W = I − Π_ker all have entries in Q(α), i.e. they are polynomials
   in the atoms √5 and α = 4 sin 72°. Handle them as upstream does, with `Fq` and `atoms_inBox`.
   - **Do not** try to certify the exact square of §2: it is an identity over Q(α) and gives the |v|²-form.
     Formalise **Lemma L′ (§3′)** instead, whose variables are |w| and |s|, the same variables the certificate controls.
   - The quadratic step is certificate (C′): M ≻ 0 for the explicit 17×17 matrix of §3′. Here ε = 1/16, q′ = 29/500
     and θ = −4999/5000 are rational.
     - Lean checks an LDLᵀ of a dyadic rounding M̃ (step 9.1 uses 2⁻⁶⁴), plus entrywise enclosures
       |M − M̃|_ij ≤ r_ij obtained from the atom boxes, plus the Frobenius shift ‖r‖_F.
     - The margin is λ_min ≈ 2.7e−4. So entry enclosures of about 10⁻⁶ suffice, and the dyadics can be much shorter
       than 2⁻⁶⁴.
   - The error blocks need only the six **rational** Frobenius squares of §2 (65/108, 1879/1080, 25/1152,
     455641/1166400, 208051/777600, 47417897/13996800), together with Cauchy–Schwarz.
     - Lean proves each as a finite sum identity over Q(α), or proves an upper bound directly.
     - With γ₁ ← ‖C_sww‖_F no operator-norm certificate is needed. Lemma L′ still closes, with
       0.0226|w|² + 0.0227|s|⁴ (step 9.4).
     - The optional op-norm route: c·Π_W ∓ Π_W C(s_α,·,·)Π_W + Π_ker ⪰ 0 (14×14, same technique) gives
       0.0342|w|² + 0.0227|s|⁴.
   - c_q is a 2×2 PSD test on rationals.
4. **The remainder.** Route (a) is closest to upstream `Dpair_lower`: 21 per-pair scalar bounds, but
   it is too weak for the cap (§6). Route (b) needs the Bombieri inequality for two explicit
   14-variable forms of degree 5 and 6. Alternatively, apply per-pair Bombieri to the 4-variable
   pieces: 21 small polynomials with 56 and 84 coefficients. The constants get slightly worse
   (log: 3.58 and 10.07 instead of 3.12 and 9.96).
5. **The final step** is the scalar argument of §3′ in (a, b, ρ). Every inequality is between monomials, with
   rational coefficients listed in `../verification/check_local_rigorous.txt`, which suits nlinarith. The |v|-form Lemma L (§3) stays the
   paper statement. Its only extra inputs are the exact identities of step 3 (Q_eff = 1/10, κ² = 67/120, λ_W = 3/4).

## 9. Rigorous checker `check_local_rigorous.py` (log): what each step certifies

Run it with `OMP_NUM_THREADS=1 python3 local/check_local_rigorous.py`. The output is in
`../verification/check_local_rigorous.txt`: **45/45 PASS, ALL_PASS**.

| step | content | method |
|---|---|---|
| 0 | P on S², orthonormal frames; criticality Σ_j W_ijP_j = μ_iP_i with μ_ring = 0, μ_pole = −1/4 | exact, K = Q(α) |
| 1 | identity (1): Σ W_ijℓ_ij = Σ μ_iν_i; minorant 𝒫 to degree 6 (2188 monomials); no linear terms | exact |
| 2 | H r = 0, H s = 0; kernel independent; charpoly(H) = λ⁵(λ−3)⁵(4λ−9)²(4λ−3)²/256 ⇒ λ_W = 3/4; Π_ker exact projector | exact |
| 3 | C(s,s,s) ≡ 0; Q = 13/40; \|c\|² = (23/480)\|s\|⁴; exact square Q_eff = 1/10; κ² = 67/120; κ ≤ 0.747218 | exact polynomial identities in σ |
| 4 | γ₂, δ₁–δ₄ upper bounds (balls); exact rational Frobenius squares; c_q ≤ 4.203074 | arb + exact |
| 5 | ‖C(e_α,·,·)\|_W‖_op ≤ 0.27428359 (α = 1, 2) ⇒ γ₁ ≤ 0.387896 | exact LDLᵀ over Q with rounding shift |
| 6 | B₅² = 7801/800, B₆² = 2857757/28800 | exact |
| 7 | K₇ ≤ 70.9738 (ρ = 1/100), K ≤ 3.22942; pole tails ≥ 0 | arb |
| 8 | Lemma L: 0.2015902… ≥ 0.2015 and 0.0454935… ≥ 0.0454; Frobenius fallback 0.143406 / 0.037372 | exact rationals |
| 9 | (C′) 17×17 PD; Lemma L′: 0.034300 ≥ 0.0342 and 0.022760 ≥ 0.0227; fallback 0.022663 | exact LDLᵀ + rationals |
| 10 | 7(1/300)² ≤ (1/100)²; (11/2)·(1/1650) = 1/300 and 1/1650 ≤ 1/10; ρ² < 2; min\|P_i−P_j\| > 2ρ | exact / arb |
| 11 | sanity (not proof): E(P) = −log(1600√5); ratio 1.86104 along λ_W-eigendirections; centre manifold (E−E(P))/a⁴ = 0.09999 | mpmath 50 digits |

Not machine-checked (paper-level):
- ψ ≥ ψ₅ for u < 1;
- the coefficientwise-majorant lemma for f_ij, and the summation Σ K_ij R_ij⁷ ≤ K₇|t|⁷;
- the Bombieri inequality;
- the gauge and chart facts.
