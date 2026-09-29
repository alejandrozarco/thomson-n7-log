# Method

This note describes the structure of the argument, which parts the scripts in this repository check, and which
parts are taken from the proof of the Coulomb case without being machine-checked here.

## Setting

For unit vectors x, y ∈ S² put t = ⟨x, y⟩; then −log‖x − y‖ = φ(t) with φ(t) = −½ log(2 − 2t). For seven points,
E(x) = Σ_{i<j} φ(t_ij), t_ij = ⟨x_i, x_j⟩. P is the regular pentagonal bipyramid (two poles, a regular pentagon on the
equator). Its pairwise distances have product 1600√5, so E(P) = −log(1600√5). Inner products at P: −1 (pole–pole),
0 (pole–ring, class B), c₁ = cos 72° and c₂ = cos 144° (ring–ring, class C).

The statement the argument is aimed at: E(x) ≥ E(P) for all seven distinct points on S², with equality only for images of
P under O(3) and relabelling. For Riesz s-energies with s ∈ [0, 2] (s = 0 being the logarithmic energy) this was
conjectured by Nerattini, Brauchart and Kiessling [NBK, eq. (29)], who also describe the branching of a C₂ family at s = 0
and s = 2 (for s = 2 they credit Melnyk, Knop and Smith [MKS]). Armentano et al. [A+] characterise the logarithmic
critical configurations of seven points on S² that contain an antipodal pair.

The argument follows the proof of the Coulomb case (Riesz s = 1) in [C], which is formalised in Lean 4 and explained in
`paper/PAPER.md` of that repository (cited below as PAPER §n). That proof uses three-point semidefinite bounds as in
[KLT] and a cap/stability argument. The kernel φ is replaced by the logarithmic one. All certificates here were computed for the logarithmic kernel;
the kernel-independent deductions are taken over.

## Structure

Let m = min_{i<j} t_ij.

**Case 1: m ≥ −9/10.** An untyped three-point certificate of degree 10 (PAPER §5) consists of a univariate polynomial
H with H ≤ φ on [−9/10, 1), a number e, positive definite kernel matrices, and sums of squares with the multipliers of
PAPER §5.2. Via Lemma 4.1 and identity (2) of PAPER §5.1 it gives Σ_{i<j} H(t_ij) ≥ e, hence E(x) ≥ e. The certificate
has e − E(P) = +5.0·10⁻⁴.

**Case 2: m < −9/10.** Relabel so that (0, 1) is a pair with minimal inner product (PAPER §6.4). The range of t₀₁ is
split at the breakpoints used for the Coulomb case, −1 ≤ −99/100 < −49/50 < −24/25 < −47/50 < −93/100 < −9/10.

* **Slabs** t₀₁ ∈ [a_k, a_{k+1}]: typed three-point certificates (PAPER §6) with minorants H_A ≤ φ on [a_k, a_{k+1}] and
  H_B, H_C ≤ φ on [a_k, 1). Each gives E(x) ≥ e > E(P). Degrees and margins e − E(P):

  | slab | degree | e − E(P) |
  |---|---|---|
  | [−99/100, −49/50] | 10 | +2.0·10⁻⁴ |
  | [−49/50, −24/25] | 10 | +5.0·10⁻⁵ |
  | [−24/25, −47/50] | 12 | +5.0·10⁻⁵ |
  | [−47/50, −93/100] | 12 | +2.0·10⁻⁵ |
  | [−93/100, −9/10] | 12 | +3.0·10⁻⁵ |

  (The margins are targets chosen before rounding, not optima. At degree 10 the float SDP for the last three slabs was
  infeasible even at margin 0.)

* **Cap** t₀₁ ∈ [−1, −99/100], which contains P. The typed certificate (degree 12) is sharp at P: e < E(P) with
  E(P) − e = 7.29·10⁻¹⁷. The minorants touch φ at the inner products of P: H_A at −1 (with slope), H_C at c₁ and c₂
  (first-order contact) and H_B at 0 with contact of order three (H_B and φ agree in value up to η and in the first three
  derivatives). The cap is closed as in PAPER §7.2, with the last step replaced:
  1. If E(y) ≤ E(P), then every term (φ − H_cls)(t_ij) is at most δ := 10⁻¹⁶ ≥ E(P) − e.
  2. *Coercivity:* (φ − H_X)(t) ≤ δ forces t to lie within τ_X of the corresponding inner product of P, with
     τ_B ≈ 4.3·10⁻⁴, τ_C ≈ 2.5·10⁻⁷, τ_A ≈ 6.6·10⁻¹⁴, all ≤ τ := 1/1650. Because of the flat mode below, the B-contact is
     quartic, so τ_B scales like δ^{1/4}.
  3. *Ring rigidity:* with τ ≤ 1/10 the ring–ring inner products form a pentagon/pentagram pattern, so the Gram matrix of
     y is entrywise within τ of that of a relabelled P (PAPER §7.2 step 3, `ring_pentagon`).
  4. *Gram window to coordinates:* a Gram window τ gives coordinate distance (11/2)τ = 1/300 in the sup norm
     (PAPER §7.2 step 4, `localGram_of_localMinAt`).
  5. *Local lemma* (`local/LOCAL_LEMMA.md`), replacing PAPER §7.2 step 5: after gauge fixing, and for
     Σ‖y_i − P_i‖² ≤ (1/100)² (which contains the sup ball of radius 1/300, since √7/300 < 1/100),
     E(y) − E(P) ≥ 0.0342|w|² + 0.0227|s|⁴ (Lemma L′), where s is the component of the tangent displacement in the
     two-dimensional flat direction and w its complement. Hence E(y) ≥ E(P), with equality only at y = P.

**The flat mode.** Along the ring displacement z_k ∝ cos(4πk/5) (or sin), k = 0..4 (the "k = 2 pucker"), the second
derivative of the Riesz s-energy at P vanishes at s = 0 and at s = 2. Consequently the quadratic local inequality used in
the Coulomb proof (`local_ineq`: E − E(P) ≥ c‖y − P‖²) is false for the logarithmic energy. The local lemma instead
completes the square in the complementary directions and uses the quartic term on the flat directions, whose effective
coefficient is Q_eff = 1/10 (exact). For the same reason H_B must have third-order contact with φ at 0, and the cap
needed degree 12 (at degree 10 the float optimum was 1.4·10⁻⁴ below E(P)).

## What the scripts check

| step | script | arithmetic |
|---|---|---|
| Case 1 and slab certificates: multipliers as required, all kernel and Gram blocks positive definite, polynomial identities coefficient by coefficient, constraint (6), e − E(P) > 0 | `checkers/check_cell.py` | exact rationals; E(P) at 60 digits (mpmath) |
| minorants H ≤ φ on the whole ranges (Case 1, slabs), with φ − H > 10⁻⁷ | `checkers/check_minorant_cell.py` | arb balls, 256 bits, bisection covering each interval, monotonicity near t = 1 |
| cap certificate: multipliers, PSD of all (facially reduced) blocks, identities, constraint (6), exact contact conditions of H_A, H_B, H_C at the inner products of P, e ≤ E(P) | `checkers/check_cert.py` | exact rationals and Q(√5); E(P) at 60 digits |
| cap minorants H ≤ φ, contact windows, coercivity radii τ_X ≤ 1/1650 for δ = 10⁻¹⁶, E(P) − e < δ | `checkers/check_minorant.py` | arb balls, 256 bits; the final τ formulas are evaluated in double precision from certified lower bounds (τ_B = 0.71 · 1/1650) |
| all of the above, assembled into the coverage table | `checkers/make_coverage.py` → `COVERAGE.md` | — |
| local lemma: identity (1), Taylor data over Q(√(10+2√5)), Hessian spectrum and kernel, C(s,s,s) = 0, Q_eff = 1/10, tensor-norm and remainder bounds, the 17×17 PSD certificate, the scalar inequalities of Lemmas L and L′, the handoff constants (radius 1/100 ⇐ 1/300 ⇐ τ = 1/1650) | `local/check_local_rigorous.py` (45 checks) | sympy exact, arb 320 bits, exact LDLᵀ over Q, Fractions |
| flat mode at s = 0 and s = 2 | `soft_mode/verify_soft_mode.py` | numerical: 40-digit central second difference (h = 10⁻⁸) at s ∈ {0, 0.5, 1, 1.5, 2, 2.5}. For s = 0 the exact statement (H·s = 0) is step 2 of `check_local_rigorous.py` |

`check_cell.py` also evaluates the global identities of PAPER §5.1/§6.3 on random configurations, as a guard against
errors in transcribing the model; this is a sanity test, not part of the certificate check.

## What is not checked here

These steps are paper-level. They are taken from the Coulomb proof [C] (PAPER §4–7), where they are proved in Lean for
the Coulomb kernel. Their arguments do not depend on the kernel beyond the stated hypotheses, but they have not been
re-proved or formalised for the logarithmic kernel:

* three-point positivity (PAPER Lemma 4.1) and the identities (2) and (6) that turn a certificate into Σ H ≥ e
  (PAPER §5.1, §6.2–6.3);
* the minimal-pair reduction and the covering/gluing of Case 1, the slabs and the cap (PAPER §6.4, §7);
* the cap deduction steps 1–4 above (termwise slack, coercivity ⇒ Gram window, ring rigidity `ring_pentagon`,
  `localGram_of_localMinAt`) and the gauge fixing `exists_gauge`;
* in the local lemma: ψ(u) ≥ ψ₅(u) for u < 1, the coefficientwise majorant lemma for the degree ≥ 7 tail, the Bombieri
  inequality, and the chart/gauge facts (listed in `local/LOCAL_LEMMA.md` §9).

The Riesz s = 2 constants in `local/LOCAL_LEMMA.md` §7 are floating-point values only, and no s = 2 certificates are
included. `verify_soft_mode.py` is a numerical computation.

Nothing here has been refereed. The computations are certificates for the steps listed in the table above, not a proof
of the full statement.

## References

* [NBK] R. Nerattini, J. S. Brauchart, M. K.-H. Kiessling, "Magic" numbers in Smale's 7th problem, arXiv:1307.2834
  (J. Stat. Phys.). Conjecture: eq. (29).
* [MKS] T. W. Melnyk, O. Knop, W. R. Smith, Extreme arrangements of points and unit charges on a sphere: equilibrium
  configurations revisited, Can. J. Chem. 55 (1977), doi:10.1139/v77-246.
* [A+] Armentano, Bentancur, Carrasco, Fiori, Valdés, Velasco, Characterization of logarithmic Fekete critical
  configurations of at most six points in all dimensions, arXiv:2502.10152.
* [KLT] Kryvonos, Liehr, Taylor, Energy minimization for eight points on the sphere, arXiv:2609.22077.
* [C] Lean 4 proof of the Coulomb case N = 7, https://github.com/huwngtran/thomson-n7-lean (snapshot of 2026-09-27,
  commit 25f2fa5), with `paper/PAPER.md`.
* [TZ] J. Tooby-Smith, A. Zughaid, Thomson-N-8-Warrant, https://github.com/jstoobysmith/Thomson-N-8-Warrant (Lean 4
  development whose approach [C] follows).
