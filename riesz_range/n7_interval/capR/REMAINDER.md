# capR: the s-remainder of the PSD step, and whether a sharper bound is worth it (2026-11-07; private, not reviewed)

AI-written assessment. Measurements below are float (numpy) on the real certificates, not proofs; the script is
`measure_remainder.py` in the session scratchpad (2 s, < 300 MB; reads capS/cert_cap_s{11_12,1_1,13_12,3_2}_D12.json.gz
and capR/cert_dirs_D12.json). Notation as in check_capR.py's docstring.

## 1. The current bound and why the k/12 pieces fail

For a block R and a piece [a, b], h = b - a, lambda = (s - a)/h,
    R(s) = (1 - lambda) R_a + lambda R_b + sum_k rho_k(s) R_k,   rho_k(s) = v_k(s) - (1 - lambda) v~_{a,k} - lambda v~_{b,k},
    rho_k(s) = -lambda (1 - lambda) (h^2/2) v_k''(xi_k) + delta_k(s),   |delta_k| <= eps_k ~ 2^-58.
check_capR.py (P step, around line 495) certifies, with w = v''(s_m), tau >= lambda_max(R_w), F_k >= ||R_k||_2 (Frobenius),
M3_k >= sup |v_k'''|:
    slack = min(mu_a, mu_b) - (h^2/8) ( tau + (h/2) sum_k M3_k F_k ) - sum_k eps_k F_k.                        (W)
This is a Weyl bound: it charges the worst eigen-direction of R_w against the worst eigen-direction of the chord.
Numbers (worst block FR2, h = 1/12): tau = 3.6e-3, so (h^2/8) tau = 3.1e-6; cubic term 4.2e-7; node margins 1.83e-6
([11/12, 1]) and 3.0e-6 ([1, 13/12]); slacks -1.71e-6 and -4.0e-7.

**Measured reality.** Along the actual path R(s) (float, lambda = 1/8 ... 7/8):

| piece | min mu | (W) slack | actual min lambda_min(R(s)) | midpoint drop (FR2) | Weyl h^2 term | ratio |
|---|---|---|---|---|---|---|
| [11/12, 1], h = 1/12 | 1.85e-6 | -1.65e-6 (checker -1.71e-6) | **+1.02e-6** | 3.8e-7 | 3.1e-6 | 8.3 |
| [1, 13/12], h = 1/12 | 3.09e-6 | -3.0e-7 (checker -4.0e-7) | **+2.18e-6** | 4.2e-7 | 3.0e-6 | 7.1 |
| [11/12, 13/12], h = 1/6 (skipping node 1) | 1.85e-6 | -1.4e-5 | -2.6e-6 (indefinite) | 3.0e-6 | 1.2e-5 | 4.2 |
| [13/12, 3/2], h = 5/12 | 4.09e-6 | -1.1e-4 | -2.9e-5 | | | |

So both k/12 pieces are in fact PSD along the whole piece with margin ~1e-6, and the h^2 Weyl term overestimates the
real loss by a factor 7-8 (the perturbation's top eigenvector is nearly orthogonal to the chord's bottom eigenvector).
The second derivative of the actual block path is already exact in (W): R''(s) = sum_k v_k''(s) R_k, since the chord is
affine. The looseness is in Weyl, not in the derivative bound. h = 1/6 is genuinely indefinite at these margins, so no
bound can rescue it: the real limit for mu ~ 2e-6 nodes is h between 1/12 and 1/6.

## 2. Options assessed

(a) **Sub-divided chord (recommended).** Split [a, b] into n sub-intervals s_i = a + i h/n, d = h/n. On [s_i, s_{i+1}],
theta = (s - s_i)/d, since the chord and the affine part of rho are affine in s,
    R(s) = (1 - theta) R(s_i) + theta R(s_{i+1}) + sum_k [v_k(s) - (1 - theta) v_k(s_i) - theta v_k(s_{i+1})] R_k,
and the bracket is -theta(1 - theta)(d^2/2) v_k''(xi_k), xi_k in [s_i, s_{i+1}]. Hence for all s in [a, b]
    R(s) >= [ min_i m_i - (h^2/(8 n^2)) ( tau + (h/2) sum_k M3_k F_k ) ] I,                                    (S_n)
where m_i <= lambda_min(R(s_i)) is certified by an arb LDL^T of R(s_i) - m_i I (R(s_i) is a ball matrix: exact R_a, R_b, R_k,
arb rho_k(s_i); s_i rational), tau and M3 as now (w and M3 over the whole piece, so the cubic term keeps h/2; with per-sub-
interval w_i it becomes d/2, which is immaterial). The pin-error term disappears because R(s_i) is built with the exact v~.
n = 1 is (W). Measured slacks (float, same tau and M3 as the checker):

| piece | (W) | (S_2) | (S_4) | prism bound (b) |
|---|---|---|---|---|
| [11/12, 1] | -1.65e-6 | +3.9e-7 | **+9.2e-7** | +4.7e-7 |
| [1, 13/12] | -3.0e-7 | +1.55e-6 | **+2.06e-6** | +1.7e-6 |
| [11/12, 13/12] (h = 1/6) | -1.4e-5 | -5.5e-6 | -3.2e-6 | -3.8e-6 |

Cost: n + 1 arb LDLs per block (38 blocks, size <= 83; the checker already does 2-5 per block in ~15 s), so n = 4 adds
about 30-60 s per piece. Adaptive: n = 1, 2, 4, 8, 16 until slack > 0. Implementation: ~40 lines inside the P loop of
check_capR.py (build R(s_i) with `vdata(0, s_i)`, reuse `cert_margin`'s bisection on the ball matrix, replace `mu[nm]`
by min_i m_i and h by h/n in the h^2 factor; record `nsub` and the sample margins in `P_blocks`; update the P paragraph of
the docstring with the derivation above). No solver change, no new nodes.

(b) **Prism (6-corner) bound, exact in the second derivative.** Peano form: rho_k(s) = int_a^b K(s, sigma) v_k''(sigma) dsigma
with K <= 0, int K = -lambda(1 - lambda) h^2/2 =: -c, so sum_k rho_k R_k = -c * avg_sigma R_{v''(sigma)} + (pin term).
Writing v''(sigma) = (1 - theta) v''(a) + theta v''(b) + eta, |eta_k| <= (h^2/8) M4_k, the family is
    R(s) = (1 - lambda) R_a + lambda R_b - c_1 R_{w_a} - c_2 R_{w_b} + (error),  c_1, c_2 >= 0, c_1 + c_2 <= h^2/8,
affine in (lambda, c_1, c_2) over a prism with 6 vertices; lambda_min is concave, so
    slack = min{ mu_a, mu_b, lambda_min(R_j - (h^2/8) R_{w_j'}) : j, j' in {a, b} } - (h^2/8)^2 sum_k M4_k F_k - sum_k eps_k F_k.
Four extra LDLs per block, no first-order cubic term. Measured: +4.7e-7 / +1.7e-6, i.e. a little weaker than (S_4) here
(the prism relaxes the parabola c <= lambda(1 - lambda) h^2/2 to the rectangle). Clean but not better; keep as a note.

(c) **Quadratic-in-s interpolant with a solved third node.** A solved midpoint node C_m is not on the chord's path, so the
Lagrange weights (negative on half the piece) destroy PSD-by-convexity; DESIGN.md 3 measured Bernstein middle control
blocks at -4e-2, needing ~1e2-1e3 de Casteljau sub-pieces. A *pseudo* third node C_m = (C_a + C_b)/2 + sum_k d_k C_k is
exactly the present family (the quadratic through it equals chord + 4 lambda(1 - lambda) sum d_k C_k), so it changes
nothing. Verdict: no.

(d) **Structure of rho_k and convexity of the kernel in s.** All v_k are convex or concave with fixed sign on (0, 2)
(beta0 = 2^(-s/2), alpha0 = 2^(-s), a0 convex; beta1, b0, x1, y1 concave; sign changes only at s = 4/ln 2 > 2), so the
correction is one-sided: R(s) = chord - c(s) R_{v''} with c >= 0. (b) is the exact use of this; the other use is in the
choice of directions: a one-sided SDP  min t s.t. sgn(v_k'') R_k(C) <= t I, L(C) = 0, Pin(C) = e_k  (7 SYM solves,
~2 GB / ~5 min each on the laptop now, plus round_dirs) would make the correction help instead of hurt if t <= 0 is
feasible (plausible but unproven, DESIGN.md 5). That removes the h^2 term entirely, leaving the cubic and minorant
terms (h ~ 0.2). It is the lever for the ends of the range (mu(s) -> 0), not for [1/2, 3/2].

(e) **Different parametrisation.** Interpolating linearly in q = 2^(-s/2) (or any single pin) makes one v_k affine but
not the other six (different exponents L_t); the h^2 coefficient shrinks by at most ~2 while s(q) becomes transcendental
in every checker. Not worth it against the factor 7-8 of (a).

(f) **Taylor models in s, as in Kryvonos-Liehr-Taylor (N = 8, arXiv:2609.22077, Certificates_All_s/).** What their
replay checker does (finite/kernel/verify_interval.py, cells.json): per closed cell [c - w, c + w] (on [0, 2.1]: w = 1/10,
i.e. width 0.2; degree 12; Taylor order 8; "balance unit"), the entire certificate is a Taylor polynomial in s of order 8
with a uniform remainder, found as a numerical "witness" and corrected by an enclosed approximate inverse of the
Taylor-model-valued constraint system (Neumann iteration, q < 1); the moving contact set of X(a_s) is a root model
(`root.a_enclosure`); PSD of each block B(s) is certified by Lemma 6.3, ||P B(s) P^T - I|| <= delta < 1, with delta the sum
over the Taylor coefficients of the preconditioned block norms plus the remainder, i.e. a coefficient-wise Weyl-type
bound; equality off the contact set is excluded by positive lower bounds on three "forbidden triples". Their cells need
one witness solve each (several GB) and a heavy exact replay per cell. Comparison with our design:
  * They cannot have exact contact for all s (the candidate moves with s), so their equalities carry a remainder that the
    PSD slack must absorb. Our cap contact set is fixed (P), and the affine family makes identities, pins and e(s) = E_s(P)
    exact for every real s; only PSD and H <= phi are uniform-in-s conditions. On this point our design is already the
    stronger one, and their machinery offers nothing to copy.
  * Their width (0.2 on [0, 2]) against our 1/12 comes from solving for the whole polynomial-in-s certificate (order 8)
    in one SDP per cell, which is the cellsS Bernstein approach (ii-b) applied to the cap. DESIGN.md 0(b) rejected a
    polynomial-in-s cap certificate because exact contact is impossible, but that objection is removed by combining it
    with the affine pin correction: C(s) = sum_j b_j(lambda) C_j + sum_k rho_k(s) C_k with Bernstein controls C_j and the
    Taylor/Bernstein remainder rho = O(h^(m+1)). The cost is a joint SDP with (m + 1) x the variables of one cap solve
    (with SYM: ~2 GB x (m + 1)^1.5 ... roughly 6-10 GB at m = 2-3, workstation only, Clarabel fragility unknown) and a PSD check
    along s that is again (S_n)-type or de Casteljau. Expected gain: pieces ~0.2-0.25 wide, i.e. ~5 pieces for [1/2, 3/2]
    instead of 12 nodes; but each piece costs more than 3 node solves and the memory does not fit the laptop. Net machine
    time is not better; the engineering is a week. Not recommended before the range lands.
  * Their PSD criterion is weaker than (S_n) for the same information (it is Weyl applied coefficient-wise); nothing to
    adopt there. Their "balance" (energy rescaled by (s/center)(3/2)^((s-center)/2)) is our normalised gauge.
  * Their tail argument (Hessian positivity at a threshold, monotone in s) does not apply: the PBP's range ends at s = 2
    (ring mode soft), and nothing beyond [0, 2] is claimed here.

## 3. Recommendation

**Implement (a) now, in check_capR.py, before more nodes are solved.** Reasons:
1. It is ~40 lines and ~1-2 h of agent time, with no new solves, and converts the two existing FAIL pieces into PIECE_OK
   (predicted slacks +0.9e-6 and +2.1e-6 at n = 4; also [13/12, 3/2] stays FAIL, correctly). Negative control: the
   h = 1/6 piece must still fail (actual min -2.6e-6).
2. It keeps the factory on the k/12 grid: 9 more nodes for [1/2, 3/2] (7/12, 2/3, 3/4, 5/6, 7/6, 5/4, 4/3, 17/12, 1/2)
   instead of 21 on k/24, at ~30 min wall each, i.e. ~6 h saved; and check_capS's Sturm cost grows steeply with the
   denominator (1 - u^p H^(2q): degree 299 at q = 12, 599 at q = 24; ~3 min per minorant at q = 12), so k/24 nodes also
   check much more slowly.
3. The real limit of the method at a node margin mu is then the *actual* lambda_min of the family (h_max roughly
   sqrt(8) ~ 2.8x the (W) value), which matters most where mu(s) is small (the ends of [0, 2], and the unfloored or
   low-margin nodes). Beyond [1/2, 3/2] the next lever is (d) (one-sided directions), then an (S_n)-type sub-sampling of
   the minorant step M (its remainder (h^2/8) G_t is the same chord bound and is already the binding condition at
   h = 1/12: min f outside the B window 5e-8). Both after the range lands.
Bound to implement, written out: for each block and n in (1, 2, 4, 8, 16),
    slack_n = min_{0 <= i <= n} m_i - (h^2 / (8 n^2)) ( tau + (h/2) sum_k M3_k F_k ),   m_i <= lambda_min(R(s_i)) by arb LDL^T,
    R(s_i) = (1 - i/n) R_a + (i/n) R_b + sum_k rho_k(s_i) R_k,   rho_k(s_i) = v_k(s_i) - (1 - i/n) v~_{a,k} - (i/n) v~_{b,k},
PSD of the block on the piece iff slack_n > 0 for some n (the first n that passes is recorded). Everything else in
check_capR.py (E, M, K) stays as it is.
