# capR: the N = 7 cap certificate on an interval of exponents s (work package E; 2026-11-06, private)

Design note plus prototype measurements, written by an AI agent. Nothing here is reviewed; the prototype is float
only. Notation as in ../capS/NOTES.md: cap cell t01 in [-1, -99/100], degree 12, value-only face, kernel
phi_s(t) = (2 - 2t)^(-s/2), contacts t in {-1, 0, c1, c2}, certificate C = (F', B', H_A, H_B, H_C, psi_Ba, psi_Cb,
c_alpha, c_beta, e) with nV = 39454 unknowns.

## 0. Summary

* The chord argument of the task statement is right, and the prototype reproduces it to four digits: the linear
  interpolant of two node certificates overshoots phi_s at the contacts by exactly (h^2/8) v''(s) (7.6e-4 at H_B(0)
  for h = 1/4), which the sharp cap cannot absorb (it would need h ~ 1e-7). Refinement: the overshoot is in all seven
  pins (values and slopes), and it also destroys the double zero of phi - H at the contacts, so H <= phi fails outright,
  not only the energy gap.
* Verdict (a): **works, and is the recommended method.** The cap identities are linear and homogeneous in C and do not
  involve s; s enters only through the 7-vector v(s) of kernel data at the contacts, through H <= phi_s, and through
  e = E_s(P). The certificate family
      C(s) = (1 - lambda) C_a + lambda C_b + sum_k rho_k(s) C_k,   rho(s) = v(s) - [(1 - lambda) v~_a + lambda v~_b]
  (C_a, C_b exact node certificates with rational pins v~, C_k seven fixed exact "pin response" directions with
  L(C_k) = 0, Pin(C_k) = e_k) satisfies the identities exactly and has pins v(s) and e = E_s(P) **exactly for every s**.
  Only PSD and H <= phi_s have to be checked on the piece, and both reduce to the chord-plus-remainder bound used in
  localS. The correction term is O(h^2) with a fixed sign, and the measured cost is small: with min-Frobenius directions,
  the rigorous per-block bound gives piece widths h = 0.091 (nodes 1/2, 3/4) and 0.116 (nodes 3/4, 1); the minorant
  and contact-curvature conditions allow the same h ~ 0.08-0.1 at nodes solved with curvature floors.
* Verdict (b): a certificate polynomial in s with exact contact at every s is impossible (2^(-s/2) is not a
  polynomial), and an inexact contact needs E_s(P) - e(s) <~ 3e-16 for the coercivity window tau = 1e-6, which no
  practical degree reaches. Reparametrised by v it becomes (a) with s-dependent C_k(s), which gains nothing because the
  C_k are already s-independent. A joint Bernstein solve (as in cellsS) would need 2-4x the 6 GB of one cap solve.
* Verdict (c): the affine family is the reformulation "kernel enters only through 7 scalars": identities and sharpness
  are checked symbolically (exactly, once, for C_a, C_b, C_k). PSD and H <= phi cannot be made symbolic, since they
  must hold along a transcendental curve, but the chord-plus-remainder bound turns them into finitely many exact PSD
  checks and explicit ball-arithmetic bounds. Blocks cannot be made s-independent: with fixed blocks, the pins can only
  move along the block-free shift (H += const, e += 21 const), one of the 7 directions. The measurement shows that the
  four value pins are individually almost block-free (|B_k| 1e-7 .. 3e-5); the cost sits in the slope pins and in the
  Galois-odd part b0 of the C contacts (|B_k| 0.05 .. 0.26).
* Cost: one node solve per ~0.09 of s (15 min on the workstation, 6 GB, Clarabel fragile), node rounding and checks as now, plus
  a cheap piece check. [1/4, 7/4] ~ 18 nodes, ~10 machine hours; [1/10, 19/10] ~ 27 nodes if the margins hold up near
  the ends (unknown).

## 1. Structure of the cap certificate in s

From ../capS/round_capS.py and check_capS.py (prototype: affine_cap.py `build`):

* L x = 0: the three polynomial identities lambda_T = sum g_r z^T B_r z (3 x 455 coefficient rows) and the e-row
  e = H_A(-1) + 10 H_B(0) + 10 Re H_C(c1) (this is "e = alpha0 + 10 beta0 + 10 a0" of round_capS, made homogeneous).
  Coefficients are rational and do not depend on s. Rank 1355 of 1366 + 7 rows.
* Pin x = v: 7 rows, v = (beta0, beta1, alpha0, a0, b0, x1, y1) = (H_B(0), H_B'(0), H_A(-1), Re/Im H_C(c1),
  Re/Im H_C'(c1)) in Q(sqrt5) coordinates. The kernel data: beta0 = 2^(-s/2), beta1 = s 2^(-s/2 - 1), alpha0 = 2^(-s),
  a0 +- b0 sqrt5 = (2 - 2c_{1,2})^(-s/2), x1 +- y1 sqrt5 = s (2 - 2c_{1,2})^(-s/2 - 1). All are (s-linear) x exp(-sL/2),
  convex or nearly so. check_capR computes v''(s_m) and sup |v'''| per piece in arb, so no global constant enters.
  For orientation only: max_k |v_k''| <= 0.34 on [1/2, 3/2], <= 0.382 on [1/3, 7/4] and <= 0.405 on [1/4, 19/10],
  each attained by alpha0 = 2^-s at the lower end ((ln 2)^2 2^-s); max |v'''| <= 0.236, 0.265, 0.281 on the same ranges.
  (Corrected 2026-11-07: this line used to say "max |v''| on [1/4, 19/10] is 0.34", which holds only for s >= 1/2.
  REVIEW_ext_fable.md M1; numbers from ../ext/fix_M1_vbound.py.)
* Inequalities: all F', B' PSD; H_A <= phi_s on [-1, -99/100], H_B, H_C <= phi_s on [-1, 1).
* With the pins at v(s) the certificate is sharp: e = E_s(P). The chain (coercivity delta = 1e-16 >= E(P) - e = 0,
  windows tau, local lemma) is unchanged.

## 2. The method

Fix once: exact rational C_1..C_7 with L(C_k) = 0, Pin(C_k) = e_k (float min-norm solve as in the prototype, round to
2^-80, exact pivot solve on the row basis exactly as round_capS does for a certificate, then verify every row exactly;
no PSD required). Their blocks B_{k,blk} are the only new objects.

For a piece [a, b], h = b - a, lambda = (s - a)/h, nodes C_a, C_b exact (pins v~_a, v~_b dyadic with |v~ - v| <= 2^-58,
as produced by round_capS), define C(s) as in the summary. Then, for every s in [a, b]:

1. **Identities and (6)**: exact, because L is linear and L(C_a) = L(C_b) = L(C_k) = 0.
2. **Pins and sharpness**: Pin(C(s)) = (1 - lambda) v~_a + lambda v~_b + rho(s) = v(s), hence H(c; s) = phi_s(c),
   H'(c; s) = phi_s'(c) at the contacts, and e(s) = E_s(P). (Checked symbolically: Pin(C_k) = e_k, and the e-row.)
3. **PSD**: by the mean-value form of the linear interpolation error, rho_k(s) = -lambda(1 - lambda)(h^2/2) v_k''(xi_k)
   with xi_k in [a, b] (plus the dyadic pin error <= 2^-58). Write w = v''(s_m), s_m the midpoint, B_w = sum_k w_k B_k,
   and |v_k''(xi) - w_k| <= (h/2) max_[a,b] |v_k'''|. Then per block
      B_blk(s) >= [ min(mu_a, mu_b) - (h^2/8) ( lambda_max(B_{w,blk}) + (h/2) sum_k max|v_k'''| ||B_{k,blk}||_2 ) ] I.
   Checked by: B_{a,blk} >= mu I and B_{b,blk} >= mu I exactly (the existing LDL^T + diagonally-dominant-remainder
   certificate already gives this with mu = the DD slack: 2.4e-6 at s = 1/2, 3.8e-6 at 3/4, 5.1e-6 at 1);
   lambda_max(B_w) <= tau by an arb LDL of tau I - B_w (w is irrational; B_w is an arb matrix; check_localS has the
   routine); ||B_k||_2 <= ||B_k||_F exactly; max |v'''| by arb with s a ball. The sign matters: rho <= 0 for convex v_k,
   so only the positive part of B_w costs.
4. **Minorant, away from the contact windows**: for fixed t, g_t(s) := phi_s(t) - sum_k v_k(s) H_k(t) is explicit and
   smooth, and f(t, s) = phi_s(t) - H(t; s) = g_t(s) - (1 - lambda) H^_a(t) - lambda H^_b(t) with s-free H^ polynomials,
   so f(t, s) >= min(f(t, a), f(t, b)) - (h^2/8) max_[a,b] |d^2 g_t/ds^2|, d^2 g_t/ds^2 = (L_t/2)^2 phi_s(t) -
   sum_k v_k''(s) H_k(t), L_t = ln(2 - 2t). f(t, a), f(t, b) are the node margins (arb, with t a ball, as check_coercS
   does now); the remainder is one arb evaluation per t-ball with s a ball over [a, b]. Adaptive bisection in t.
5. **Minorant on the contact windows and coercivity**: f(c, s) = f_t(c, s) = 0 exactly by 2., so f >= 0 on |t - c| <= r
   follows from f_tt(t, s) >= 2K there (A: f_t(t, s) >= K_A on [-1, -0.998]), and the same chord-plus-remainder bound
   applies to f_tt (the kernel part (L/2)^2 phi'' and sum v_k'' H_k'' in arb over the window x piece). The windows
   tau(s) <= 1e-6 then follow as in check_coercS with delta = 1e-16 (f'' >= 6e-4 at floored nodes gives tau_B = 5.8e-7).
6. Everything else (K6-K9, local lemma uniform on [0.05, 1.92] from localS) is unchanged.

Why this implies the cap bound for all s in the piece: for each fixed s, C(s) is a three-point cap certificate for
phi_s in the sense of check_capS (identities exact, blocks PSD, minorants valid, e = E_s(P)); the chain from there to
"E_s(z) > E_s(P) for z != P in the cap" is the single-s chain with delta = 1e-16.

## 3. Measurements (affine_cap.py; logs measure.log, minorant.log, optimise.log)

Nodes: exact certificates at s = 1/2 (no floors, EXCL), 3/4 (floors 3e-4), 1 (cap1, floors). Residuals of L x and of
the pins are 1e-15. Reduced-block minimum eigenvalues 4.9e-6, 7.7e-6, 1.0e-5 (DD slacks 2.4e-6, 3.8e-6, 5.1e-6).

Directions (min-Frobenius over the blocks, h's free): max_blk ||B_k||_2 = (1e-7, 5.7e-2, 3e-5, 2e-7, 2.6e-1, 4.6e-2,
1.1e-1) for (beta0, beta1, alpha0, a0, b0, x1, y1). The value pins are nearly block-free (the block-free shift), the
slopes and b0 are not. Combined B_w for w = v''(s_m): lambda_max 2.7e-3 .. 4.4e-3, lambda_min -0.9e-2 .. -1.5e-2, the
largest blocks FR1-FR3, FP1-FP3 (kernel blocks), not the SOS blocks.

| quantity | nodes 1/2, 3/4 (h = 1/4) | nodes 3/4, 1 (h = 1/4) |
|---|---|---|
| chord pin overshoot at midpoint (measured / h^2 v''/8) | 7.560e-4 / 7.560e-4 at beta0 | 6.930e-4 / 6.930e-4 |
| min eig along chord only (pins wrong) | 4.9e-6 .. 7.7e-6 | 7.7e-6 .. 1.0e-5 |
| min eig chord + correction, worst s (block) | -6.9e-6 at s = 0.625 (FR3) | -3.2e-6 at s = 0.875 (FR3) |
| loss at midpoint, measured / global bound (h^2/8) lmax(B_w) | 1.3e-5 / 3.3e-5 | 1.2e-5 / 2.9e-5 |
| rigorous per-block width h_max (step 3, incl. cubic term) | **0.091** (FR2; FR1 0.096, FR3 0.098) | **0.116** (FR2) |
| same with block-reweighted directions (1/sqrt(mu_blk)) | 0.098 | 0.122 |
| minorant: node margin outside windows, H_A at t = -0.99 | 5.0e-7 (1/2), 9.4e-7 (3/4) | 1.3e-6 (1) |
| h_max from minorant (step 4), H_A / H_B / H_C | 0.081 / 0.049 (s = 1/2, unfloored) / 0.20 | 0.10-0.11 / 0.083-0.089 / 0.27-0.33 |
| h_max from contact curvature (step 5), f''_B(0) | 0.041 (s = 1/2 unfloored), 0.25 (3/4) | 0.25 (3/4, 1) |
| corrected chord at h = 1/4: f''_B(0), min f outside windows | f'' 1.7e-5 .. 9.8e-4; H_C min f -9.7e-7 at s = 0.6 | f'' >= 6.2e-4; all min f > 0 |

So at h = 1/4 the corrected chord fails (PSD by -7e-6, the H_C minorant by -1e-6 near t = -0.79 where the node margin is
3.6e-7), and the h^2 scaling of both losses puts the limit at h ~ 0.09-0.12 (rigorous bound) or ~0.12-0.15 (measured),
for nodes with margins mu ~ 4e-6 and floors. The three conditions (PSD, H_B minorant at t ~ -0.3 where the node margin
is 2.5e-6 against |d^2 g/ds^2| ~ 2.7e-3, H_A margin at -99/100) bind at about the same h; none is a wall.

Observation worth keeping: sum_k v_k(s) H_k(t) tracks phi_s(t) in s. Its s-curvature mismatch |d^2 g_t/ds^2| is
~3e-3 at t = -0.3 against (L_t/2)^2 phi = 0.17 for the kernel alone, because the min-norm directions move H almost like
the kernel. That is why the minorant survives with margins of only 1e-6.

Quadratic variant (three nodes, Lagrange): at h = 1/4 spacing the interpolant plus cubic correction stays PSD on all
of [1/2, 1] (min eig >= 3.1e-6), but its Bernstein middle control block has min eig -4e-2 (11 of 38 blocks), so the
cheap PSD certificate fails and de Casteljau subdivision (~400 pieces of exact LDL) would be needed. The three nodes
are also not on one smooth solution path (1/2 is unfloored). Not recommended; the gain in node count is at most ~2x.

## 4. Piece width, cost, reachable interval

Width: h = 0.09 at mu ~ 4e-6 (node DD slack), scaling like sqrt(mu). With a `margin` of ~5e-6 in the node solves
(the sdp_capS option; profile margin * min(1, (d/0.05)^4)) and floors 3e-4, the minorant side allows h ~ 0.1 as well.
Nodes at s = k/12 (h = 0.0833) are a natural grid; nodes need not be rational for the method (the piece check is arb),
but round_capS and check_capS want rational s with small denominator.

Per node (shared by two pieces): Clarabel solve on the workstation ~15 min, 6 GB, 1 thread, queued behind the cap agent and the
SAT campaign; rounding ~3 min (laptop, heavy lock); check_capS + check_coercS ~5-10 min. ~50 % of the solves so far ended
in NumericalError; the affine family does not change that (and the floors are needed, so the unfloored fallback is
not available). Once: 7 directions, 7 exact pivot solves of 1355 x 1355 (~3 min each on the laptop) or one solve with 7
right-hand sides.
Per piece: check_capR.py (to be written): exact mu for the two nodes (free, from the DD slack), arb LDL for
lambda_max(B_w) on 38 blocks (seconds), ||B_k||_F exact (seconds), 2-D minorant and curvature by adaptive bisection in
t with s a ball (minutes, like check_coercS).

| interval | nodes (h ~ 0.083) | machine time | condition |
|---|---|---|---|
| [1/4, 7/4] | 19 at k/12 | ~10 h (2/3 workstation queue) | mu(s) >= 4e-6 after rounding on the whole interval (known: 5e-6 .. 1.3e-5 at 0.5, 0.75, 1, 1.75 float) |
| [1/10, 19/10] | ~27 (denser at the ends) | ~15 h | mu near the ends unknown; if mu ~ 1e-6 there, h ~ 0.045 |

What limits [a, b]: not the method but the single-s ingredients. (i) mu(s) -> 0 at both ends (soft face conditions
become necessary; no data below 0.5 or above 1.75), width ~ sqrt(mu). (ii) The local lemma (localS) covers [0.05, 1.92]
at tau = 1e-6, and tau_max(s) ~ s, ~ (2 - s) at the ends, so the floors must grow there (f'' >= 2 delta / tau^2).
(iii) The cells (package C) must be covered on the same interval. (iv) Solver success at each node. The theorem's
[a, b] is the union of certified pieces, so the campaign can simply stop where the solves stop working.

## 5. Risks and open points

* Node solves: NumericalError at s = 1/4, 1.5 so far; needs the workstation runs (3/2, 5/4, 7/4, 1/4) to finish. Without
  floors the piece width halves (s = 1/2 node: curvature limit 0.041, minorant 0.049).
* The rigorous bound uses ||B_k||_2 <= ||B_k||_F (up to 9x loose for 83 x 83 blocks) in the cubic term only; the
  quadratic term uses lambda_max(B_w) directly. Fine at h ~ 0.09; the cubic term is ~15 % of the budget there.
* Better directions: the one-sided SDP  min tau s.t. B_w(C) <= tau I, L(C) = 0, Pin(C) = w  could make lambda_max(B_w)
  much smaller (the shift direction shows that pin motion can be nearly block-free; -w in the cone of "H-energy
  certificates with P sharp" is plausible since P is a critical point of every pair kernel by symmetry). This is one
  cap-sized SDP (6 GB) per w, or one for a representative w since v''(s) changes direction slowly. If lambda_max <= 0,
  the h^2 term disappears and h is set by the cubic term and the minorant (~0.2). Worth one workstation run, not required.
  Block reweighting of the least-squares (cheap) gained only 8 % before the weighted system became unsolvable.
* The node pins are dyadic *below* phi (round_capS); in the family the pins are exact, so e(s) = E_s(P) and delta can
  be anything >= 0. Keep delta = 1e-16 so the written chain (K2-K4, K6-K9) applies verbatim.
* Exactness of the C_k: they must satisfy L(C_k) = 0 exactly after rounding; the pivot structure of round_capS applies
  unchanged (same matrix, different right-hand side). Their H_k reach |H_k| ~ 4.7 on [-1, 1), which is harmless.
* Not addressed here: Lean. The affine family is a finite object (2 nodes + 7 directions per piece) and the checks are
  the same kind as the single-s ones, so the Lean port would follow the s = 1 route with s as a variable in a bounded
  interval; the arb bounds become interval lemmas.

## 6. Next concrete steps

1. Exact directions: capR/round_dirs.py = round_capS's pivot solve with right-hand sides e_1..e_7 (laptop, heavy lock,
   ~20 min); store cert_dir_k.json; exact re-check of L and Pin rows.
2. capR/check_capR.py: the piece check of section 2 (arb; reuse check_coercS's bisection and check_localS's arb LDL).
   Test it on the pieces [1/2, 3/4] and [3/4, 1] (expected: FAIL at h = 1/4 with the measured numbers above).
3. Two floored nodes at distance ~0.08 (e.g. s = 11/12 and 1, or 3/4 and 5/6) on the workstation, `mu` mode with floors 3e-4 and
   margin 5e-6, EXCL; round; run check_capR on the piece. This is the end-to-end test of the method.
4. Then the campaign on k/12 nodes outward from s = 1, as far as the solves and mu(s) allow; package C (slabs) on the
   same interval.
5. Optional: the one-sided direction SDP on the workstation for w = v''(1).

## 7. Checker results

* Exact directions (round_dirs.py): rank 1355, 7 right-hand sides, max pivot change 1.8e-9 vs float, all 1373 rows
  exact; 3 min under the heavy lock.
* **Negative control, [3/4, 1] (h = 1/4), check_capR_negctrl_3_4_1.txt: PIECE_FAIL as required**, in 110 s.
  Exact part passes (identities of the 9 objects, e-row, Pin(C_k) = e_k, node DD slacks 3.84e-6 and 5.09e-6, pin
  error 3.5e-18). Node margins certified by arb LDL^T of R - mu I: min over blocks 7.44e-6 (the DD slack is a weak
  proxy for the smallest eigenvalue). P: min block slack -3.44e-5 (FR2: mu 7.58e-6, lambda_max(R_w) 3.75e-3, cubic
  1.3e-2; FR1 -3.00e-5, FR3 -2.82e-5), i.e. a loss of (h^2/8)(lambda_max + (h/2) cubic) ~ 4.2e-5 -- the prototype's
  prediction. M: the B-window curvature bound is -3.07e-5 (f_B'' ~ 6.2e-4 at the nodes against (h^2/8) * 8e-2 ~
  6e-4 of s-curvature), so the minorant part fails too at this h (the 1-D estimate h_max(curv) ~ 0.25 of section 3
  ignored the Taylor-in-s terms; the rigorous bound is tighter). Both losses scale with h^2: at h = 1/12 they are
  4.7e-6 (< 7.4e-6 margin) and 7e-5 (<< 6e-4), so [11/12, 1] is expected to pass if its nodes have similar margins.

* **Positive control, [1, 1 + 10^-6], check_capR_posctrl_1_1e-6.txt: PIECE_OK**, in 115 s. The second node is a
  pseudo-node (pseudo_node.py): C_b = C_1 + sum_k d_k C_k with dyadic d_k ~ v_k(s_b) - Pin(C_1)_k, PSD data by float
  LDL + exact DD remainder (10.5 MB). Certified margins 9.87e-6, P slack +9.87e-6 (A_B1), windows f_B'' >= 6.19e-4,
  f_C'' >= 3.31e-3, f_A' >= 5.04e-3; outside the windows f > delta with 64/129/181 bisection pieces; near 1 OK;
  tau_B, tau_C, tau_A <= 1e-6 decided exactly. So the checker can output PIECE_OK, every code path runs on real
  certificates, and the cap bound holds for all s in [1, 1 + 10^-6] (a theorem, if a tiny one).
  Caveat seen here: the cap1 s = 1 node (no minorant margin) has f_B ~ 6e-10 just outside the B window (|t| ~ 0.056,
  the "tight region" of section 3), which a piece of width 1/12 cannot absorb ((h^2/8)|g''| ~ 2e-7 there). Factory
  nodes with the 5e-6 margin profile have f >= 7.9e-6 at |t| = 0.056; alternatively widen the window (env RB) where
  f'' > 0 holds beyond 0.05, which the checker certifies rather than assumes.
* **First real pieces, [11/12, 1] and [1, 13/12] (factory nodes, capS/NOTES.md section 7; outputs in
  pieces/, summary pieces/SUMMARY.md): PIECE_FAIL, on PSD only** (115 s and 113 s). Exact part OK; windows
  f_B'' >= 3.43e-3 / 3.41e-3, f_C'' >= 3.67e-3, f_A' >= 2.1e-3; outside the windows f > delta (B: 3.2e-7 and 1.7e-8,
  C: 1.8e-8 and 2.1e-10 -- the 5e-6 margin profile of the factory nodes handles the tight region near |t| ~ 0.056);
  tau_B = 2.4e-7, tau_C = 2.3e-7, tau_A = 4.7e-14, all <= 1e-6 exactly. P: certified node margins only 3.05e-7 and
  4.96e-7 (the factory's SYM solves unfold to mineig_orig 3.2e-7 / 6.7e-7; the old nodes had 7.7e-6 .. 1e-5), so the
  predicted loss (h^2/8)(lambda_max(R_w) + cubic) ~ 2e-6 .. 3.6e-6 at FR2 gives slacks -1.70e-6 and -3.43e-7; the
  G_B1..6 blocks (mu 3e-7 .. 5e-7) are next. Widest piece by the bound: h = 0.061 and 0.074 (1/12 = 0.083).
  Remedies (NODES_WANTED.md): the factory should maximise the margin in the original reduced coordinates
  (orthonormal symmetry basis); with 1e-5 margins the 1/12 pieces pass with ~ +4e-6 slack. Otherwise midpoint nodes
  23/24 and 25/24 are predicted to pass with thin slacks (+1.9e-7 .. +2.3e-6).
  The method itself is confirmed on real nodes: every s-dependent condition other than PSD passes at h = 1/12 with
  margins of 1e-7 .. 1e-3, and the PSD deficit is exactly the node-margin issue the prototype identified.

## Files

| file | what |
|---|---|
| affine_cap.py | prototype: `build` (float system L, Pin -> sys_D12.npz, 1373 x 39454, nnz 3.2e5), `measure` (directions, norms, PSD along the curve, quadratic variant -> measure.json, directions.npz), `minorant` (margin profiles, needed margins, contact curvature along s, Bernstein P_1 -> minorant.json), `optimise` (per-block rigorous width, reweighting) |
| measure.log, minorant.log, optimise.log | the runs quoted above (laptop, 1 thread, nice 19, < 1 GB, ~10 s / 2 s / 90 s) |
| round_dirs.py -> cert_dirs_D12.json (30 MB, gitignored like the certificates) | the seven exact directions C_k: float directions rounded to 2^-80, exact pivot solve (1355 x 1355, 7 right-hand sides, 3 min under the heavy lock), all 1373 rows re-verified exactly (round_dirs.log) |
| check_capR.py | the self-contained rigorous piece checker of section 2 (statement in its docstring); `check_capR.py CERT_a CERT_b cert_dirs_D12.json a b [delta] [TAU_DEN]`, exit 0 iff PIECE_OK |
| check_capR_*.txt | checker outputs: negative control [3/4, 1] (h = 1/4, must fail), positive control [1, 1 + 1e-6], end-to-end pieces |
| pseudo_node.py -> cert_cap_s1000001_1000000_D12_pseudo.json | node certificate at s_a + eta from a node at s_a via the affine family (positive control; no solve) |
| NODES_WANTED.md | node specification and wish list for the node factory (capS/) |
| jobR.sh, pipeR.sh (not included) | capR's own node pipeline on the workstation (<build>/capR; sdp.lock + guarded.sh, MemAvailable >= 9 GB gate), used for s = 11/12 |
