# cellsS: non-cap cells of the N = 7 case split for Riesz s in an interval (work package C; private, not reviewed)

2026-11-06. Computer output plus an argument written by an AI agent. Nothing here has been reviewed.
Cells: Case 1 (all t >= -9/10, D10) and the five slabs t01 in [-0.99,-0.98] D10, [-0.98,-0.96] D10,
[-0.96,-0.94] D12, [-0.94,-0.93] D12, [-0.93,-0.90] D12. The cap is not covered here.

## 1. Pointwise certificates at s = 1/2 and s = 3/2 (task 1): ALL_OK

Same pipeline as cells1 (float mu-mode solve, round_cell.py exact rounding, check_cell.py exact identities +
Bareiss PD + random-configuration sanity, check_minorant_cell.py ball-arithmetic minorants, phi_s = exp(-s/2 ln u)
in arb). E_s(P) is computed in arb. The slab float solutions are the existing ../sol/slab_*_ks{0.5,1.5}_mu.npz
(target 1e-5, ETA 1e-6, from ../slabs_mu.log); only Case 1 was solved again (mu mode).

| cell | D | e - E_{1/2}(P) | e - E_{3/2}(P) |
|---|---|---|---|
| Case 1 | 10 | 4.0e-4 | 5.0e-4 |
| slab [-0.99,-0.98] | 10 | 1.0e-5 | 1.0e-5 |
| slab [-0.98,-0.96] | 10 | 1.0e-5 | 1.0e-5 |
| slab [-0.96,-0.94] | 12 | 1.0e-5 | 1.0e-5 |
| slab [-0.94,-0.93] | 12 | 1.0e-5 | 1.0e-5 |
| slab [-0.93,-0.90] | 12 | 1.0e-5 | 1.0e-5 |

check_cell: CHECK_CELL ALL_OK (12/12: identities EXACT, all blocks PD, e > E_s(P) in arb, sanity ok).
check_minorant_cell: MINORANT ALL_OK (phi_s - H > 1e-7 certified on every range). Files: certs_pt/,
logs/check_cell_pt.txt, logs/minorant_pt.txt.

## 2. Why the certificate is cheap to make s-dependent

The cell identities (Case 1: slack = sum g z^T B z; slabs: lambda_A, lambda_B, lambda_Gamma and (6)) are linear
and homogeneous in the certificate C = (H's, e, c_alpha, c_beta, psi's, F's, B's), with coefficients that do not
depend on s. s enters only through (H) H <= phi_s on the minorant ranges and (E) e > E_s(P). So:
- any linear combination of exact certificates satisfies the identities exactly, and a combination with
  nonnegative weights keeps every F and B block positive definite;
- the shift S0 = (H = 1, e = 21, c_alpha = 1/5, c_beta = 1/2, everything else 0) has all identity LHS = 0, so
  C <-> Chat = (C - S0)/s is a change to the **normalised gauge**
  psi_s(t) = (phi_s(t) - 1)/s = (e^{sx} - 1)/s, x = -ln(u)/2,  Ehat_s(P) = (E_s(P) - 21)/s.
  psi_0 = -ln(u)/2 is the log kernel, so s -> 0 is regular in this gauge.
- d^2 psi_s/ds^2 = x^3 int_0^1 r^2 e^{sxr} dr is <= 0 for t <= 1/2 (u >= 1). The minorants are tight only there,
  so s-interpolation costs nothing on the minorant side. Ehat_s(P) is concave, |Ehat''| = 0.68 (s = 0), 0.56 (1/2),
  0.46 (1), 0.37 (3/2), 0.32 (1.9), 0.30 (2). In the plain gauge E_s(P)'' = 2.97 / 2.29 / 1.77 at
  s = 1/2 / 1 / 3/2, and the curvature then lands on the minorant constraints. That is about 5x worse at s = 1.

Certificate at s in [a, b]: C(s) = S0 + s * Chat(s), with Chat(s) = sum_k b_k(lambda) Chat_k (lambda = (s-a)/(b-a))
and b_k >= 0 the Bernstein basis. Degree 1 is linear interpolation between two node certificates. Identities and
PD hold for every s automatically. Only (H) and (E) have to be checked, on [a, b] x range and on [a, b].

## 3. Approaches and numbers

Margins m(s) = max e - E_s(P) (float maxe, ETA = 0) for Case 1: 8.0e-4 (s = 1/2), 1.745e-3 (1), 2.27e-3 (3/2),
1.94e-3 (2). In the normalised gauge, m/s = 1.6e-3, 1.75e-3, 1.5e-3, 0.97e-3, which is nearly flat.
Slabs: maxe fails in Clarabel for every slab, also with an eigenvalue floor (MU0). Margin by mu-mode target scan,
slab [-0.99,-0.98] at s = 1: mu(1e-5) = 7.8e-7, mu(1e-4) = 7.0e-7, mu(1e-3) = -3.4e-8, so m ~ 9.6e-4. The other four
slabs are known only to clear 1e-5 at s = 1/2, 1, 3/2, 2 (mu > 0). Their second-target solves were cut off, see §5.

**(i) piecewise, H <= min(phi_a, phi_b), e >= E_a(P)** (Case 1 at a = 1, float maxe):
b - a = 1e-4: margin 1.23e-3; 3e-4: 1.9e-4; 1e-3: -3.4e-3. The loss is first order, |dE_s(P)/ds| (b - a) with
|E'| = 6.5 / 5.2 / 4.2 at s = 1/2 / 1 / 3/2. Max width is about 3.4e-4 for Case 1 and about 2e-4 for a slab with
m ~ 1e-3. That means about 3000-5000 pieces per cell for [1/2, 3/2]. **Not viable.**

**(ii-a) linear interpolation (degree 1), independent node solves, normalised gauge** (sdp_cellS.py with GW):
each node certificate carries the chord-gap margins of check_piece.py:
e = E_s(P) + s (w^2/8) max|Ehat''| + target, and H <= phi_s - s (w^2/8) x^3 e^{(s+w)x}/3 on t <= 0.8
(H <= 1 + s psi_{s-w} above). The loss is second order: w_max ~ sqrt(8 (m/s) / |Ehat''|), which gives
0.15 (s = 1/2), 0.175 (1), 0.18 (3/2) for Case 1 and about 0.13 for slab [-0.99,-0.98] at s = 1.
Check of the estimate: Case 1 at s = 1 with w = 0.15 has float e - E(P) = 1.737e-3 against a needed 1.365e-3.
- **Done end to end, rigorous:** Case 1 on [1/2, 3/2] with 9 nodes s = 1/2 + k/8 (w = 1/8, target 2e-5, ETA 1e-6).
  All 9 nodes round to exact certificates (ALL_OK, e - E_s(P) = 6.0e-4 ... 1.16e-3, mu = 2.7e-7 ... 1.7e-6), and
  check_piece.py gives PIECE_OK for all 8 pieces in 3-4 s each (logs/check_piece_case1.txt).
  So **Case 1 is certified for every s in [1/2, 3/2]** (identities exact, PD exact at the nodes, (H) and (E) by
  ball arithmetic). Cost: 9 x ~35 s solve + ~2 s rounding.

**(ii-b) polynomial in s: one joint SDP over Bernstein control certificates** (sdp_bern.py), Case 1, [1/2, 3/2],
float, objective tau = min_s s (ehat(s) - Ehat_s(P)) (plain units):

| m | tau | time (2 threads) |
|---|---|---|
| 1 (joint linear) | -5.8e-2 (matches 0.46/8: the chord loss) | 157 s |
| 2 | -2.7e-4 | 190 s |
| 3 | **+7.8e-4** (about the pointwise margin at s = 1/2) | 307 s |

- **Done end to end, rigorous:** m = 3, mu mode (tau = 3e-4, ETA = 1e-5, 25 s-points x full t-grid for H):
  mu = 9.2e-7, 696 s, RSS 1.8 GB. The 4 control certificates round exactly (residual 1e-11 absorbed, PD by
  Bareiss), and check_bern.py with 200 s-sub-intervals gives BERN_OK in 19 s (logs/check_bern_case1.txt).
  So **one cubic-in-s certificate covers Case 1 on all of [1/2, 3/2]**.
- (ii-c) Interpolating independent float solutions at Chebyshev nodes was not tried. SDP solutions are not unique
  in s (they are interior points chosen by the solver), so the interpolant's blocks need not stay PSD. The
  Bernstein joint solve gets PSD for free and is strictly better, so (ii-c) was dropped.

Not obtained (runs terminated by the 16:39 interruption and the laptop restart, then no heavy slot): slab
[-0.99,-0.98] Bernstein m = 3 (maxm had already failed at tol 1e-10, like every slab maxe; the mu-mode run was cut);
Case 1 m = 4 on [1/10, 19/10] (RSS reached 3.4 GB at start, above the new 3 GB limit); second-target margins of the
other four slabs at s = 1; end-range margins (s = 1/10, 19/10).

## 4. Recommended design and cost

**Production: degree-1 (linear) node certificates in the normalised gauge (ii-a).** It reuses the single-s
pipeline unchanged except for two margin terms. Memory is that of one single-s solve. The exact checks are the
existing ones, plus check_piece.py (seconds per piece). Adjacent pieces share nodes. Proven on Case 1.
Estimated node counts (w = 1/8 where the margin allows; the slab widths are an extrapolation from one slab at one s):

| interval | nodes per cell | solves (6 cells) | laptop time, 1 thread (Case 1 ~1 min, D10 slab ~3 min, D12 slab ~15 min, guesses x2 the 2-thread times) |
|---|---|---|---|
| [1/2, 3/2] | 9 (Case 1 done) | 45 more | ~ 9 x (2 x 3 + 3 x 15) min ~ 7.5 h |
| [1/10, 19/10] | ~15-16 | ~ 90 | ~ 13-14 h |

Risk: if a slab's margin is near 1e-4 instead of ~1e-3, its width drops to ~0.04 (25 nodes per unit s, ~3x
the cost for that slab). First measure the four slab margins (one extra mu solve each at s = 1, then at the ends).
The mu-target scan is needed because maxe fails on slabs.

**Upgrade: Bernstein m = 3 (ii-b)**, one joint solve per cell per unit of s. On Case 1 this is ~12 min / 1.8 GB
instead of 9 x 1 min. The gain is in the checking and storage (4 control certs instead of 9 nodes), not in solve
time. For D12 slabs the joint SDP is about 4x a D12 single solve plus the semi-infinite rows (25 x 3 minorants x
~10^4 t-points, dense in (m+1)(D+1) unknowns). That will exceed 3 GB unless the minorant rows are assembled as one
sparse matrix (they are currently built as cvxpy sums) and the t-grid is thinned. Not recommended before that
engineering is done.

**Ends.** The cells show no breakdown on [1/2, 2] in the normalised gauge (Case 1 m/s within a factor 2, |Ehat''|
bounded). Toward s -> 0 the normalised gauge is regular: a node at s = 0 is a log-kernel certificate with the same
margins, and the linear lemma holds on [0, b]. So (0, b] could be covered from the log certificate plus one node at
b. That is not implemented: sdp_cellS.py has no GW path for KER = 0, and check_piece.py requires a > 0. Slab mu at
target 1e-5 is smallest at s = 1/2 (2.8e-7 to 8.6e-7) and largest at s = 2 (1e-6 to 3.4e-6). This hints that
plain-unit slab margins shrink as s -> 0, but no margin was measured below 1/2. The expected end-point degeneracy
(bifurcation at s -> 2, degeneracy at s -> 0) belongs to the cap and the local lemma, not to these cells. This is an
expectation, not a measurement.

## 5. Files

- sdp_cellS.py: single-s solve, RIESZ_S = p/q, GW (node width margins), PIECE_B (approach (i)), MU0.
- sdp_bern.py: joint Bernstein solve. round_bern.py: splits it into control points and rounds them (kernel label "hat").
- round_cell.py, check_cell.py, check_minorant_cell.py: copies of cells1 with kernel "riesz:p/q" (and "hat").
- check_piece.py: rigorous degree-1 piece check. check_bern.py: rigorous Bernstein check.
- certs_pt/ (task 1), certs_lin/ (Case 1 nodes, [1/2, 3/2]), certs_bern/ (Case 1 m = 3 controls), sol/, logs/.
- results.jsonl: every solve line, plus the check summaries.
- run_*.sh: the queues that were run. heavy.sh: wrapper for the new shared-laptop rules (lock, load < 10, one
  thread, 3 GB RSS watchdog). Not used yet. NOTE: there is no `flock` binary on this laptop (not on PATH, not in
  /opt/homebrew/bin), so the lock needs fcntl.flock from Python or a brew install.

## 6. Evening 2026-11-06: s = 3/4 complete, slab margins, revised cost (shared-laptop rules: lock, 1 thread, <= 3 GB)

**Memory.** A single-s D12 slab solve does not fit in 3 GB. The watchdog (hjob.sh) stopped it at 3.5-3.9 GB during
the Clarabel setup / KKT factorisation. cvxpy canonicalisation alone is 0.4 GB (PROFILE_BUILD=1), and
chordal_decomposition_enable = false and direct_solve_method = faer do not change the peak. **D10 is enough for the
three former D12 slabs at s = 1** (mu at target 1e-5: 6.7e-7, 7.0e-7, 2.7e-7; 1.37 GB, about 3 min single-thread),
except that [-0.93,-0.90] at D10 is weak at s = 1/2 (margin 5.9e-5). **Split it at -0.915**: at s = 1/2 the halves
have margins 2.3e-4 ([-0.93,-0.915]) and 7.8e-4 ([-0.915,-0.90]). The slab cover of t01 in [-0.99,-0.90] is now
six D10 slabs. A sub-cell's margin is >= the whole cell's margin, since the certificate of the cell is valid on the
sub-cell.

**Slab margins** (mu-mode target scans, D10, ETA 1e-6; m = zero crossing of mu(T), which is close to linear:
three-point check on [-0.99,-0.98] at s = 1). Table in logs/margins_table.txt; w(60%) = sqrt(8*0.6*(m/s)/|Ehat''|):

| slab | m(1/2) | m(1) | m(3/2) | w(60%) at 1/2, 1, 3/2 |
|---|---|---|---|---|
| [-0.99,-0.98] | ? (Clarabel panic at T = 2e-4) | 9.6e-4 | 1.3e-3 | ?, 0.100, 0.107 |
| [-0.98,-0.96] | 3.5e-4 | 9.8e-4 | 1.4e-3 | 0.077, 0.101, 0.110 |
| [-0.96,-0.94] | 2.2e-4 | 8.1e-4 | 1.25e-3 | 0.061, 0.092, 0.104 |
| [-0.94,-0.93] | 2.4e-4 | 8.5e-4 | 1.46e-3 | 0.064, 0.095, 0.112 |
| [-0.93,-0.90] whole | 5.9e-5 | 3.4e-4 | 3.7e-4 | 0.032, 0.060, 0.056 |
| [-0.93,-0.915] | 2.3e-4 | >= 3.4e-4 | >= 3.7e-4 | 0.063, -, - |
| [-0.915,-0.90] | 7.8e-4 | >= 3.4e-4 | >= 3.7e-4 | 0.115, -, - |

In the normalised gauge, slab margins m/s fall by about 2x from s = 1 to s = 1/2 (Case 1: flat). So s = 1/2 is the
binding end of [1/2, 3/2].

**s = 3/4 complete (exact).** Case 1: certs_lin node (w = 1/8), e - E = 8.0e-4. Six D10 slabs as interpolation
nodes of the 1/16-grid (GW = 1/16, target 2e-5): e - E_{3/4}(P) = 2.10e-4 each (the chord margin 1.9e-4 + 2e-5),
mu = 2.3e-7 ... 9.1e-7, RSS <= 1.2 GB. check_cell (with sanity): CHECK_CELL ALL_OK, 7/7. check_minorant_cell:
MINORANT ALL_OK. Files certs_pt/cert_*_s3o4_*.json, logs/check_cell_s34.txt, logs/minorant_s34.txt.
Case 1 at s = 5/4 is also complete (certs_lin node, e - E = 1.08e-3, both checks OK).

**Revised design for [1/2, 3/2]** (linear interpolation, all cells D10): Case 1 done (w = 1/8, 9 nodes).
Slabs: w = 1/16 on [1/2, 1] and 1/12 on [1, 3/2]; the node at s = 1 takes GW = 1/12. That is 15 nodes per slab,
90 slab nodes in all. Done: 6 (s = 3/4). Queued (run_next.sh): 6 at s = 5/4 (GW = 1/12). Remaining after that: 78.
Cost: about 3 min single-thread per D10 slab node (observed about 6 min wall when interleaved with the cap agent
on the lock), plus 10 s rounding and 4 s check_piece. That is about **4 h laptop compute, roughly 6-8 h wall**.
Risks: [-0.99,-0.98] at s = 1/2 not measured (best mu of all slabs at 1e-5, so probably fine); [-0.93,-0.915] on
[1, 3/2] needs m >= 4e-4 for w = 1/12 (known >= 3.4e-4). If a node solve has mu < 0, halve the local width
(adds nodes only in that stretch).
[1/10, 19/10]: not sizeable yet. Slab margins below s = 1/2 are unmeasured, and the normalised margin is shrinking
toward small s. The pointwise s = 1/4 solves in run_next.sh (target 1e-5) are the first data point. If m/s halves
again by s = 1/4, widths of about 1/32 there mean about 25 more nodes per slab for [1/10, 1/2] alone.

## 7. 2026-11-07: slabs on [1/2, 3/2] complete; cells coverage CELLS_RANGE_OK

**Done (rigorous, not reviewed).** All 90 slab nodes of the section 6 design exist and pass: 12 earlier (s = 3/4 w = 1/16,
s = 5/4 w = 1/12, certs_pt/) and 78 new ones (certs_range/), six D10 slabs x 15 nodes (1/16-grid on [1/2, 1], 1/12-grid on
[1, 3/2], GW = largest adjacent piece width). Each node: mu-mode solve (target 2e-5), exact rounding (round_cell.py), and
check_cell.py with sanity (CHECK_CELL ALL_OK). New-node mu = 5.0e-8 (slab [-0.96,-0.94] at s = 1/2, the smallest) up to
1.6e-6. **No node failed and no piece failed, so no refinement was needed.** The binding end s = 1/2 passed for all six
slabs at w = 1/16, including [-0.99,-0.98] (mu 1.9e-7; it had not been measured before) and [-0.93,-0.915]. At s = 3/2
with w = 1/12, [-0.93,-0.915] needs e - E = 5.2e-4 and passed with mu 4.2e-7.
check_piece.py: 84 slab pieces + 8 Case 1 pieces (certs_lin/, re-run), all PIECE_OK, 1691 s of checking in all. The
smallest E margin is 1.33e-5 in hat units (= target/s at the upper node of [17/12, 3/2]). The H lower bounds are >= 1e-8,
which is the acceptance threshold NEED of the adaptive bisection (it is not the true margin).
Wall time: 00:18 - 06:01 on 2026-11-07 (5.7 h, slot B, about 4.3 min per node including the round, check and piece steps).

**Coverage.** check_range_cover.py reads range_pieces.jsonl. It checks the certificate sha256s, the kinds, and the exact cell
bounds and kernels from the certificate JSONs. It sweeps each cell over [1/2, 3/2] with exact rationals, and on every one
of the 16 elementary s-intervals it checks that Case 1 (cut -9/10) plus the slabs (bounds from the certificates' `cell`
fields) cover t01 in [-99/100, -9/10] (RANGE_ASSEMBLY.md C2). Result: CELLS_RANGE_OK. With --recheck it also re-runs
check_piece on all 92 pieces from the certificate files (logs/range_cover_recheck.txt).
Not covered here: the cap t01 < -99/100 (package E), and the S0 self-test of RANGE_ASSEMBLY.md G5.

Files: range_driver.py (queue driver: restartable, refines locally on failure, reads the slot from .heavy_slot, stops
on STOP_RANGE), run_range.sh, check_range_cover.py, RANGE_TABLE.md (generated), range_state.json, range_nodes.jsonl,
range_pieces.jsonl, certs_range/ (78 node certificates), logs/range.log.
