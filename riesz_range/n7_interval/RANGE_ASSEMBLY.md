# N = 7, Riesz s in [1/3, 7/4]: assembly of the range warrant (2026-11-07; private; core [1/2, 3/2] AI-reviewed in REVIEW_range_fable.md, extension to [1/3, 1/2] and [3/2, 7/4] AI-reviewed in REVIEW_ext_fable.md; not peer reviewed)

Written by an AI agent from the files in this directory (PLAN_range.md, STATUS_range.md, localS/, cellsS/, capS/, capR/,
the s = 1 chain cells1/, cap1/, STATUS_s1.md, and PROOF_LEDGER.md sections T, R, K, L). Computer-assisted warrant, AI-produced,
not peer reviewed, not a proof claim, no priority claim (LITERATURE_range.md: the direct precedents are Kryvonos-Liehr-Taylor's
all-s N = 8 proof and Schwartz's N = 5 interpolation theorem). Every checker named below is Python (fmpq exact / arb balls),
AI-written, unreviewed.

## 1. Statement

Notation. S^2 the unit sphere in R^3; for x = (x_1, ..., x_7) in (S^2)^7 and real s > 0
    E_s(x) = sum_{i<j} |x_i - x_j|^(-s) = sum_{i<j} phi_s(<x_i, x_j>),   phi_s(t) = (2 - 2t)^(-s/2),
with the convention E_s(x) = +infinity if two points coincide (t = 1). P = the regular pentagonal bipyramid (poles +-e_z, ring
of five at angles 2 pi k/5), E_s(P) = phi_s(-1) + 10 phi_s(0) + 5 phi_s(c1) + 5 phi_s(c2), c1 = (-1 + sqrt5)/4, c2 = (-1 - sqrt5)/4.

**Claim R.** For every real s in the closed interval [1/3, 7/4] and every x in (S^2)^7: E_s(x) >= E_s(P), with equality if
and only if x = g P o sigma for some g in O(3) and sigma in S_7.

Scope and history. The warrant was first assembled and reviewed for the core [1/2, 3/2] (REVIEW_range_fable.md, recheck
of all 207 pieces; `python3 range_check.py` -> RANGE_OK [1/2, 3/2]). It was then extended by 60 new pieces (53 cell, 7
cap; no checker changed) to [1/3, 7/4] (`python3 range_check.py --range 1/3 7/4` -> RANGE_OK for routes local and exact,
267 used pieces; REVIEW_ext_fable.md: no FATAL / SERIOUS finding). Both statements are kept: [1/2, 3/2] is the reviewed
core with the larger margins, [1/3, 7/4] the current claim. The ends are closed: the cap, Case 1 and every slab have
node certificates exactly at s = 1/3 and s = 7/4, and the local cover [1/20, 48/25] contains both. Limits, not part of
the claim: below 1/3 the cap formulation is infeasible at s = 1/4 (float probe, EXTENSION_sizing.md; a formulation
change is needed); above 7/4 nothing was attempted (the local lemma at tau = 10^-6 holds up to about s = 1.93,
REVIEW_ext_fable.md N3).

Quantifier structure: the s-quantifier is the outermost. The warrant is a finite collection of certified pieces, each a
statement "for all s in [a, b] (real s, not only rational)" about one component of the fixed-s argument, plus the finite
bookkeeping that the pieces cover [1/3, 7/4] component by component and fit together (section 4). Nothing is interpolated
*between* pieces: at each s, one piece per component suffices, and pieces may overlap or use different node certificates.

## 2. The fixed-s argument (what is glued)

Case split as in the published log / s = 1 / s = 2 chains (ledger R1-R3, T4-T8, K1-K10, L), with phi_s in place of phi:

1. **Minimal pair (R1, kernel-free).** If some t_ij = 1, E_s(x) = +inf > E_s(P). Otherwise relabel so that
   t01 = m := min_{i<j} t_ij in [-1, 1).
2. **Case split (R2, kernel-free).** m >= -9/10 (Case 1); or m in [a_k, a_{k+1}] for one of the slabs that tile
   [-99/100, -9/10] (closed intervals; the tiling may depend on s, see 4.C2); or m in [-1, -99/100] (cap). Boundary values
   belong to both neighbours; any one certificate suffices.
3. **Case 1 (T4).** A Case 1 certificate for phi_s with cut a = -9/10 gives E_s(x) >= e_1(s) > E_s(P). No equality possible.
4. **Slab (R3, T5, T6, T8).** A slab certificate for phi_s on [lo, hi] (multipliers of T6, minorants H_A on [lo, hi],
   H_B, H_C on [lo, 1)) gives, for every x with t01 in [lo, hi] and all t_ij >= t01: E_s(x) >= e_k(s) > E_s(P).
5. **Cap (K1-K10, L).** A cap certificate C(s) for phi_s on [-1, -99/100] with e(s) <= E_s(P) + delta, PSD blocks, exact
   identities and (6), minorants H_A <= phi_s on [-1, -99/100], H_B, H_C <= phi_s on [-1, 1), and coercivity windows tau
   (f_X := phi_s - H_X <= delta implies the pair is within tau of its contact: t01 within tau_A of -1, pole-ring within
   tau_B of 0, ring-ring within tau_C of c1 or c2) gives, for every cap configuration y with t01 = m:
   - E_s(y) = sum phi_s(t_ij) >= sum H_cls(t_ij) >= e(s) (T8, T5). In the affine family of capR e(s) = E_s(P) exactly,
     so E_s(y) >= E_s(P) outright (a single-s rounded certificate would only give E_s(y) >= E_s(P) - delta);
   - if E_s(y) <= E_s(P): every f_X(t_ij) <= E_s(P) - e(s) <= delta (K1), so every pair is within tau of its contact
     (K2-K4); K6 (ring rigidity, tau <= 1/10) gives sigma in S_7 with |<y_i, y_j> - <P_sigma i, P_sigma j>| <= tau;
     K7 gives g in O(3) with ||g y_i - P_sigma i|| <= (11/2) tau (sup norm); K9 gives the l2 bound
     |z - P| <= r := sqrt7 (11/2) tau for z = g y o sigma^-1 ... (relabelled); K8 (gauge) gives g' with
     sum_i P_i (g' z_i)^T symmetric and |g' z - P| <= |z - P| <= r; the local lemma L (localS) says E_s(z') > E_s(P) for
     every gauge-fixed unit z' with 0 < |z' - P| <= r. Hence z' = P, i.e. y is in the orbit of P. **Route 1.**
   - **Route 2 (exact sharpness; available only for the affine family).** With e(s) = E_s(P) exactly, K1 gives
     sum_{i<j} f(t_ij) <= E_s(y) - E_s(P) <= 0 with every term >= 0, so f(t_ij) = 0 for every pair. check_capR certifies
     f > delta >= 0 outside the windows and f >= (m/2)(t - c)^2 (resp. f >= m_A (t + 1)) on them with f(c) = f'(c) = 0
     exactly, so f(t) = 0 only at the contacts: every pair sits exactly at its contact. K6 with tau = 0 gives
     Gram(y) = Gram(P o sigma), hence y = g P o sigma (Gram determines a configuration up to O(3); this is K7 with w = 0).
     Route 2 needs no local lemma, no K8/K9, and no tau-compatibility. It is not the written chain of the s = 1 warrant
     (there e < E(P) by 7e-17), so it is recorded as an option; range_check supports both (section 7).
6. **Conclusion at s.** Every x has E_s(x) >= E_s(P); equality forces the cap case with y in the orbit (3., 4. are strict).

Kernel-dependent inputs at s (all others are kernel-free and reused verbatim from the log ledger, status (b)/(c) there):
S2 (phi_s(t) = |x - y|^(-s) for unit vectors; phi_s -> +inf at t -> 1), the certificates themselves (identities, PSD,
H <= phi_s on the ranges incl. t -> 1, sign of e - E_s(P)), the coercivity constants, and the local lemma (criticality of
P holds for every s by the D_5h symmetry argument; the Hessian, |M|_F, C3 are s-dependent).

## 3. The certified objects (one row per component; "piece statement" = what one checker run certifies for all s in [a, b])

| component | checker | piece statement (all s in [a, b]) | certified now | files |
|---|---|---|---|---|
| Case 1, a = -9/10, D10 | cellsS/check_piece.py (nodes certs_lin/, w = 1/8) | identities exact and blocks PD at the nodes (check_cell), (E) e(s) > E_s(P), (H) H(s, .) <= phi_s on [-9/10, 1) for C(s) = S0 + s[(1-lambda) Chat_a + lambda Chat_b] | core: 8 pieces [1/2 + k/8, 1/2 + (k+1)/8], PIECE_OK; plus one cubic Bernstein certificate on [1/2, 3/2], BERN_OK (check_bern.py, 4 controls, NSUB 200). Extension: 5 pieces [1/3, 5/12], [5/12, 1/2], [3/2, 19/12], [19/12, 5/3], [5/3, 7/4] (range_driver_ext.py). 22 used pieces (the 8 core pieces are recorded twice) | cellsS/logs/check_piece_case1.txt, check_bern_case1.txt, range_pieces.jsonl |
| six slabs [-99/100,-49/50], [-49/50,-24/25], [-24/25,-47/50], [-47/50,-93/100], [-93/100,-183/200], [-183/200,-9/10], D10 | cellsS/check_piece.py (nodes certs_range/, GW = piece width) | same as Case 1 with the slab ranges (H_A on [lo, hi], H_B, H_C on [lo, 1)) | core [1/2, 3/2] for all six: 90 nodes (w = 1/16 on [1/2, 1], 1/12 on [1, 3/2]), 14 PIECE_OK pieces per slab, 84 in all (range_driver.py). Extension [1/3, 1/2] and [3/2, 7/4]: 48 pieces (range_driver_ext.py): the three middle slabs on a 1/48 grid on [1/3, 5/12] and 1/24 on [5/12, 1/2] (9 new each, with the three upper pieces), the other three on 1/24 (7 new each); [3/2, 7/4] on 19/12, 5/3, 7/4. Now 21 / 21 / 23 / 23 / 23 / 21 pieces, 132 in all (CELLS_RANGE_OK on [1/3, 7/4] in ext/cells_cover_ext.txt) | cellsS/range_pieces.jsonl, cellsS/RANGE_TABLE.md, RANGE_TABLE_ext*.md |
| cap [-1, -99/100], D12, value-only face | capR/check_capR.py (two factory nodes + 7 exact directions) | E1-E4 exact; P (PSD of every reduced block of C(s)); M (minorants, window curvatures); K (tau_X <= 1/TAU_DEN decided exactly), e(s) = E_s(P) exactly | core [1/2, 3/2]: 27 PIECE_OK reports (NSUB = 4 sampled chord bound, one-sided minorant remainder), nodes on the k/12 grid on [7/12, 3/2] plus 1/2, 13/24, 17/24, 23/24, 25/24 (some intervals certified twice, in capR/pieces/ and capR/pieces_nsub/; 29 used after the recheck); thinnest P slack 2.98e-7 on [7/12, 2/3]. Extension: 7 pieces on the nodes 1/3, 3/8, 5/12, 11/24, 1/2 and 3/2, 19/12, 5/3, 7/4 (5/3 and up with --phicap profiles); thinnest P slack 2.59e-7 on [1/3, 3/8] (via the sampled chord bound; the Weyl bound alone fails there), 8.9e-7 on [3/8, 5/12], 7.6e-6 on [5/3, 7/4]. 36 used pieces; TAU_DEN = 10^6 everywhere | capR/pieces/, capR/pieces_nsub/, capR/RESULTS.md |
| local lemma, r = sqrt7 (11/2) tau | localS/check_localS.py cover2q (chord + remainder in the 8 kernel values; exact rational endpoints and tau) | for gauge-fixed unit z, 0 < |z - P| <= r: E_s(z) > E_s(P) (G > 0 on the piece) | [1/2, 3/2] at tau = 10^-6 exactly: 15 pieces, all LOCAL_OK; [1/20, 48/25] (contains [1/3, 7/4]): 62 pieces, all LOCAL_OK; 77 used | localS/cover2q_1o2_3o2_tau1e-6.jsonl, cover2q_1o20_48o25_tau1e-6.jsonl |
| kernel-free glue K6-K9, R1-R2, T1-T3, T5-T6 | Lean (log development) / ledger | independent of s | done (ledger status (b)/(c)) | PROOF_LEDGER.md |

## 4. Compatibility conditions (what range_check must verify; all exact rational arithmetic)

- **C1 Coverage.** For each component X in {case1, slab_1..slab_6 (as a family, see C2), cap, local}: the union of the
  closed s-intervals of its OK pieces contains the claimed range ([1/2, 3/2] for the core, [1/3, 7/4] now). Endpoints
  included: pieces [a, b] are closed, so adjacent pieces sharing an endpoint cover it twice, and the range ends must each
  be covered by some closed piece (this needs nodes AT 1/2 and 3/2, resp. 1/3 and 7/4, for the cap and every slab).
- **C2 Tiling at every s.** Let B be the set of all piece endpoints of all cell components; on each elementary interval J
  between consecutive points of B, the cells with an OK piece containing J must contain Case 1 with cut exactly -9/10 and
  slabs whose [lo, hi] (read from the node certificates' `cell` fields, not from file names) can be chained
  lo_1 = -99/100, hi_k = lo_{k+1}, hi_last = -9/10 (extra overlapping slabs are harmless). The cap cell is hard-coded
  [-1, -99/100] in check_capR (multipliers of T6); range_check asserts the three boundary values -1 < -99/100 < -9/10.
  The tiling may differ between elementary intervals (five-slab at some s, six-slab at others).
- **C3 tau compatibility (Route 1 only).** On every elementary interval J: the cap piece covering J decided
  tau_A, tau_B, tau_C <= 1/TAU_DEN (field `tau` in its report) and the local piece covering J was run with
  tau_local >= 1/TAU_DEN (from the cover2 file name `cover2_a_b_tau<tau>.jsonl`; the piece records do not store tau).
  Also 1/TAU_DEN <= 1/10 (K6) and r = sqrt7 (11/2) tau_local is what check_localS uses (hard-coded; assert by reading
  the source line or by re-running one piece). Route 2 drops C3 and the local component.
- **C4 delta.** check_capR's delta is only used as the "outside windows f > delta" threshold and in tau; any delta >= 0 is
  sound because e(s) = E_s(P) exactly. range_check records delta and TAU_DEN per cap piece; no condition beyond C3.
- **C5 Same s at both ends of a piece and same cell.** check_piece asserts kind, cell, D equal and 0 < a < b;
  check_capR asserts same face and multipliers. range_check re-reads a, b from the reports and the node certificates'
  `kernel` ("riesz:p/q") / `s` fields and requires them to agree with the piece endpoints.
- **C6 Freshness.** Each report must have been produced by the current checker from the current inputs. Since
  2026-11-07 (review S1) this is decided by sha256: every checker records in its report the sha256 of its own source
  (and of the modules it relies on) and of every input file, and range_check compares them with the current files
  (8.14). Reports without these hashes fall back to the old rule (report newer than every input it names and than
  the checker script) and are flagged. `--recheck` re-runs and regenerates the reports.
- **C7 Float endpoints (local).** cover2 stores piece endpoints as Python floats; consecutive pieces reuse the same float,
  and sball() parses repr(float) as a decimal. range_check converts endpoints with Fraction(str(x)) (the decimal the checker
  saw), never Fraction(float(x)).

Where monotonicity / convexity of phi_s in s enters (and where it does not): the main interpolation in s (cells: normalised
gauge chord; cap: affine family chord; local lemma: chord in the 8 kernel values) uses second-derivative bounds, i.e.
convexity/concavity: psi_s(t) = (phi_s - 1)/s concave in s for t <= 1/2 (cells, (H) costs nothing there) and convex for
t > 1/2 (Gmax term); E_s(P) convex in s (cells (E), Ehat concave); v(s) = kernel data at the contacts (cap P and M
steps), whose second and third s-derivatives check_capR computes per piece in arb (w = v''(s_m) at the midpoint, M3 =
sup |v'''| over the piece's s-ball); no global constant enters. For orientation only: max_k |v_k''| <= 0.34 on
[1/2, 3/2], but <= 0.382 on [1/3, 7/4] (attained by alpha0 = 2^-s at s = 1/3: (ln 2)^2 2^(-1/3) = 0.3813) and <= 0.405
on [1/4, 2] ((ln 2)^2 2^(-1/4) = 0.4040); max |v'''| <= 0.265 on [1/3, 7/4] (ext/fix_M1_vbound.py: check_capR.vdata on
1000 arb sub-intervals; REVIEW_ext_fable.md M1). An earlier version of this sentence said |v''| <= 0.34 without a range,
which is false below s = 1/2. Monotonicity of phi_s in s (increasing for t > 1/2, i.e. u < 1) is used only (i) in check_piece's
"mono" bound and near-1 bound on [T1, 1) and (ii) in check_capR's near-1 bound phi_s(t) >= phi_a(t) for s >= a. The
piecewise min(phi_a, phi_b) approach (PLAN_range.md) is not used anywhere. Monotonicity of E_s(P) in s is not used.

Near P vs far from P: "far" is handled in Gram space by the cells (E >= e > E_s(P)) and by the cap's minorant margins
outside the contact windows (f > delta); "near" is Gram-near (every pair within tau of its contact), transported to
configuration space by K6-K9 (sigma, g, gauge; l2 radius r), and closed by the local lemma (Route 1) or by exact contact
(Route 2). The local lemma's radius is in the l2 norm on R^21 after relabelling and gauge; the gauge does not increase it (K8).

## 5. Gaps and hidden assumptions, ranked by severity

| # | severity | gap / assumption | what closes it |
|---|---|---|---|
Status 2026-11-07 (after review REVIEW_range_fable.md): G1-G5 are **closed**: the cap, the six slabs and Case 1 are
certified on [1/2, 3/2] (section 3, 6), the first cap piece starts at a floored node at exactly s = 1/2 with
TAU_DEN = 10^6 (G3), range_check checks the tiling per elementary interval (G4) and `--selftest` checks L(S0) = 0
with negative controls (G5). The table below is the pre-coverage analysis of 2026-11-07 00:30, kept for the record;
G6-G10 still apply as written.

| G1 | closed (was blocking: coverage) | No cap piece is certified on [1/2, 3/2]; the two k/12 pieces fail PSD by 1.7e-6 / 4e-7 because the chord-plus-Weyl remainder (h^2/8)(tau_blk + ...) ~ 3.5e-6 exceeds the node margins 1.8e-6 / 3.0e-6. | capR/REMAINDER.md: sub-divided chord bound in check_capR (no new solves; predicted slack +0.9e-6, +2.1e-6 for the two pieces), then pieces on the k/12 grid (nodes 7/12, 2/3, 3/4, 5/6, 7/6, 5/4, 4/3, 17/12, 1/2 still needed, 9 solves) or on the k/24 grid as queued (21 more). Endpoint nodes at exactly 1/2 and 3/2 are required (3/2 exists; 1/2 must be a floored node, see G3). |
| G2 | closed (was blocking: coverage) | No slab piece is certified: 12 of 90 planned nodes exist, no check_piece run on slabs yet. The slab nodes at the range ends must be six-slab D10 certificates with GW >= the adjacent piece width (the existing 1/2 and 3/2 slab certificates are five-slab, w = 0: unusable as nodes). Binding margin: [-93/100, -183/200] at s = 1/2 (2.3e-4; w(60%) = 0.063, so 1/16 is tight), and [-99/100, -49/50] at 1/2 unmeasured (Clarabel panic). | Run the slab factory (cellsS/run_next.sh style, ~3 min single-thread per node, 78 nodes) and check_piece on every adjacent pair; halve the local width where a node has mu < 0. If the [-99/100,-49/50] node at 1/2 fails, split that slab too (sub-cells inherit margins). |
| G3 | closed (was high: compatibility) | The only cap certificate at s = 1/2 is unfloored: tau_B = 3.5e-6 > 1e-6, so a piece [1/2, 1/2 + h] built on it fails K at TAU_DEN = 10^6; with TAU_DEN = 250000 the local lemma must cover tau = 4e-6 on that piece (pointwise tau_max(1/2) = 4.3e-6: thin, and not yet certified on an interval). | Preferred: floored, margin-5e-6 node at exactly s = 1/2 (queued last in capS/queue_nodes.txt; move it up). Fallback: run `check_localS.py cover2 0.5 <b> 4e-6` for the first cap piece and let range_check verify C3 per elementary interval. Or use Route 2, which removes C3. |
| G4 | closed (was medium: bookkeeping) | Tiling per s is not checked anywhere: cellsS/results.jsonl check_piece lines carry "cell": "case1" or a dict; slab pieces will be identified by their node certificates' `cell` fields; five- and six-slab tilings coexist in certs_pt/. | range_check C2 (section 7); refuse file-name-based cell identification. |
| G5 | closed (was medium: soundness hygiene) | The normalised-gauge shift S0 = (H = 1, e = 21, c_alpha = 1/5, c_beta = 1/2, blocks 0) is asserted to satisfy all cell identities with LHS 0 (cellsS/NOTES.md 2, check_piece docstring). The family C(s) has S0-coefficient 1 - s[(1-lambda)/a + lambda/b] != 0, so L(S0) = 0 is load-bearing and is not verified by any checker run. | One exact run of check_cell's identity routine on S0 for the Case 1 multiplier set and for a slab multiplier set (seconds); add it to range_check as a fixed self-test. |
| G6 | medium (hygiene) | localS pieces: check_piece() does not re-check criticality of P (only check() does, pointwise); criticality for all s rests on the symmetry argument (ledger L / check_local1 step 1). The chord constants use the s-ball (correct). Piece endpoints are floats (C7). | Accept the symmetry argument (it is kernel-free given grad_i F(P) invariant under the stabiliser); optionally add the tangential-gradient ball test at both piece ends. Parse endpoints as decimals. |
| G7 | low (hygiene) | check_cell's e > E_s(P) is decided in arb (`e_gt_EP`); the reported margin string is mpmath. check_capR's near-1 bound uses up(|v_k|) * up(|H_k|) (sound since up() is the absolute upper bound). The "outside windows f > delta" threshold uses the binary64 delta = 1e-16 (slightly below 10^-16) consistently with the exact tau decision; harmless. | None needed; note in the write-up. |
| G8 | low (statement) | Coincident points: the checkers assume t_ij < 1 (S2); the statement must either exclude coincident points or use E = +inf. | State the convention (section 1). |
| G9 | low (scope) | Lean: nothing of the range is formalised; the capR/cellsS/localS checkers are new and unreviewed; the K6-K9 Lean lemmas were only used with the log kernel in the chain (kernel-free statements). | external AI review of RANGE_ASSEMBLY.md + the three piece checkers (single run each, per the review budget); Lean later along the s = 1 route with s a bounded variable (capR/DESIGN.md 5). |
| G10 | info | Route 2 (exact sharpness) makes the local lemma redundant for the cap. If adopted it should be reviewed as a change to the written chain, since K1 is currently stated with delta = 1e-16 and the local lemma. | Decide the route; range_check takes `--route {local,exact}`. |

Not gaps (checked): the chord bounds in all three checkers are of the same form f(s) >= min(f(a), f(b)) - (h^2/8) sup|f''|
applied to affine-in-s families, with all constants evaluated with s as a ball; the cap family's identities, (6), pins and
e(s) = E_s(P) are exact for every real s by linearity (E1-E3); pieces are independent (no continuity of certificates
across piece boundaries is needed); window radii in check_capR are free parameters (only f'' > 0 / f' > 0 on the window
is used); K6 needs tau <= 1/10 only.

## 6. Coverage snapshot

### 6a. [1/3, 7/4] (2026-11-07 evening; RANGE_CHECK_OUTPUT_ext.txt, RANGE_RECHECK_OUTPUT_ext.txt, REVIEW_ext_fable.md)

`python3 range_check.py --range 1/3 7/4`: RANGE_OK for routes local and exact; 267 used pieces, all authenticated by
sha256. The plain run still gives RANGE_OK [1/2, 3/2] (the inventory is the same; range_check counts used pieces of
any range).

| component | certified s-intervals | used pieces | missing for [1/3, 7/4] |
|---|---|---|---|
| Case 1 (cut -9/10) | [1/3, 7/4] | 22 (13 linear pieces in range_pieces.jsonl, the 8 core ones again in logs/check_piece_case1.txt, 1 Bernstein on [1/2, 3/2]) | nothing |
| slab_1..6 | [1/3, 7/4] each | 21 + 21 + 23 + 23 + 23 + 21 = 132 | nothing |
| cap | [1/3, 7/4] | 36 (29 core + 7 extension) | nothing |
| local (tau = 10^-6 exactly) | [1/20, 48/25] | 77 (15 + 62) | nothing |

The 60 extension pieces (53 cell, 7 cap) were re-run once from their inputs (`--recheck-new ext/pre_ext/range_check.json`,
60/60 OK, 0 verdict changes); the 207 core pieces are byte-identical to the state after the 06:59-08:29 recheck
(REVIEW_ext_fable.md section 4, item 5). Note: the JSON inventories of these runs predate the per-piece recheck status
of 8.16, so a future `--recheck-new` against them re-runs every piece (conservative).

### 6b. [1/2, 3/2] (2026-11-07, after the from-scratch recheck; RANGE_CHECK_OUTPUT.txt, RANGE_RECHECK_OUTPUT.txt)

| component | certified s-intervals | used pieces | missing for [1/2, 3/2] |
|---|---|---|---|
| Case 1 (cut -9/10) | [1/2, 3/2] | 17 (8 linear pieces, recorded twice: cellsS/logs/check_piece_case1.txt and range_pieces.jsonl; plus the Bernstein certificate, fresh again after the recheck) | nothing |
| slab_1..6 | [1/2, 3/2] each | 14 per slab, 84 | nothing |
| cap | [1/2, 3/2] | 29 (the 27 of 06:28 plus the two two-sided NSUB = 4 reports [11/12, 1], [1, 13/12] that were stale before) | nothing |
| local (tau = 10^-6 exactly) | [1/2, 3/2] (and [1/20, 48/25]) | 77 | nothing |

Recheck 2026-11-07 06:59-08:29 (`range_check.py --recheck`, slot A, 5384 s): 207 pieces re-run from their input
files, 207 OK, 0 verdict changes; every report field common to the old and new report is identical except the
spelling "1/1" -> "1" of the endpoint s = 1 in 8 cap reports. All 207 used pieces of the following plain run are
authenticated by sha256 (0 by the mtime fallback); RANGE_OK for routes local and exact; `--selftest` 55/55.

Superseded snapshot (2026-11-07 00:30): Case 1 and local complete, slabs and cap none.

## 7. Specification of range_check.py (top level; to be written by an Opus agent)

Location: numerics/n7_interval/range_check.py. Pure Python 3 + fractions (+ optional python-flint only in `--selftest`);
reads reports, never solves. Exit 0 iff RANGE_OK. Light (< 5 s without `--recheck`).

Inputs (all paths relative to numerics/n7_interval; overridable by flags):
- `--range 1/2 3/2` (rationals; default these).
- `--route local|exact` (default `local` = Route 1; `exact` = Route 2, skips the local component and C3).
- Cells: every JSON report of cellsS/check_piece.py and check_bern.py. Sources, in order: (a) files given with
  `--cell-report FILE` (JSON or JSONL; a report is a dict with keys `PIECE_OK` or `BERN_OK`); (b) cellsS/results.jsonl
  lines with `"check" in {"check_piece", "check_bern"}`; (c) cellsS/logs/check_piece_*.txt / check_bern_*.txt.
  For each OK report: s-interval from `s_range` (strings -> Fraction); kind and cell from the first node certificate
  named in `certs` (resolved in certs_lin/, certs_pt/, certs_bern/; the certificate JSON has `kind` in {"case1","slab"},
  `cell` = {"a": "-9/10"} or {"lo": "...", "hi": "..."}, `kernel` = "riesz:p/q" or "hat"); require the node certificate's
  s to equal the piece endpoint (check_piece) or, for Bernstein, require the report's `s_range` and the control files'
  `kernel` == "hat". If a report lacks `certs`, it is ignored with a warning (never trust `cell` strings like "case1").
- Cap: every capR/pieces/check_capR_*.txt: extract the JSON block (regex as in run_pieces.sh), require `PIECE_OK`,
  take `a`, `b`, `tau` (string "1/N"), `delta`, `nodes` (paths). Verify the node files exist and their `s` fields
  (or "coulomb" -> 1) equal a and b. Verify the cap window is [-1, -99/100] by reading one node's `cell`/multiplier
  data if present, else record "cap cell hard-coded in check_capR.py" (assert the string `fmpq(-99, 100)` occurs in
  check_capR.py; hygiene only).
- Local (route local): every localS/cover2_*_tau*.jsonl; tau from the file name (regex `tau([0-9.e-]+)\.jsonl`); pieces
  with `LOCAL_OK` true and no `FAILED`; endpoints via Fraction(str(x)); require the pieces of one file to chain
  (next.lo == prev.hi) and record tau per piece. Assert the constant 11/2 and sqrt(7) in check_localS.py
  (`r = arb(7).sqrt() * arb(11) / 2 * arb(tau)`) by a source grep (hygiene).
- Freshness (C6): for every used report, `mtime(report) > mtime(each named input)` and `> mtime(checker script)`;
  else the piece is dropped with reason "stale". `--no-freshness` disables.

Algorithm:
1. Build interval lists: case1: [(a, b)], slab: [(a, b, lo, hi)], cap: [(a, b, TAU_DEN, delta)], local: [(a, b, tau)].
2. Union/coverage (C1) per component with Fractions: sort, merge closed intervals (merge when next.a <= cur.b), report
   the uncovered parts of [1/2, 3/2] as maximal open/closed gaps.
3. Elementary intervals: B = sorted set of all endpoints of all pieces of all components within [1/2, 3/2] plus 1/2, 3/2.
   For each J = [B_i, B_{i+1}] (and separately for each point B_i, since a point can be covered by a piece ending there):
   - case1 covered by some piece with cut == -9/10;
   - slab tiling (C2): collect (lo, hi) of slab pieces containing J; greedy chain from -99/100 to -9/10 using exact
     equality of endpoints; fail if the chain does not reach -9/10;
   - cap covered;
   - route local: local covered, and for every (cap piece, local piece) pair covering J: 1/TAU_DEN <= tau_local and
     1/TAU_DEN <= 1/10.
   The point check at B_i is implied by the interval checks of the two adjacent J's (closed pieces), but implement it
   explicitly to avoid an off-by-one at 1/2 and 3/2.
4. `--selftest` (needs python-flint, seconds): (i) L(S0) = 0 for the Case 1 and slab multiplier sets (G5) via
   cellsS/check_cell.py's identity code on a synthetic certificate with H = 1, e = 21, c_alpha = 1/5, c_beta = 1/2,
   zero blocks; (ii) re-run one local piece and one cell piece from scratch and compare with the stored report.
5. `--recheck`: re-run every underlying checker through ../heavy_lock.py (hours: check_capR ~2 min per piece,
   check_piece ~4 s, cover2 ~1 min); default off.

Output: a human-readable table (component, certified union, gaps) followed by either the single line `RANGE_OK [1/2, 3/2]
route=<local|exact>` or lines `UNCOVERED <component> [<lo>, <hi>]` (one per maximal gap; `<component>` in
{case1, slabs, cap, local, slab_tiling, tau_compat, stale}) and a final `RANGE_FAIL`. Also write range_check.json with
the full piece inventory (which report certified which interval) so that a reviewer can replay any single piece.

Pseudo-signature of the core:

    def cover(pieces: list[tuple[Fraction, Fraction]], lo, hi) -> list[tuple[Fraction, Fraction]]   # gaps
    def tiling_ok(slabs: list[tuple[lo, hi]]) -> bool          # chain -99/100 -> -9/10 by exact endpoint equality
    def elementary(B) -> list[tuple[Fraction, Fraction]]
    main(): parse -> inventory -> C1 per component -> C2/C3 per elementary interval -> print -> exit code

Acceptance test for the implementer: with today's files the script must print UNCOVERED for slabs on all of [1/2, 3/2]
and for cap on all of [1/2, 3/2], and nothing for case1 and local; after marking the two capR pieces as OK by hand in a
copy it must report cap gaps [1/2, 11/12] and [13/12, 3/2] and, with `--route local`, no tau_compat line (both at 1e-6).

## 8. Implementation notes (range_check.py, 2026-11-07; AI-written, not reviewed)

Decisions where section 7 did not fit the files, or where a literal reading would be unsound:

1. **(Superseded for the default run by item 12; still applies to `--local-legacy`.) Legacy local tau is read as
   the binary float (default), not the decimal of the file name.** check_localS.py does
   `tau = float(sys.argv[4])` and `r = ... * arb(tau)`, so the local lemma is certified for tau_local = float(1e-06) =
   4722366482869645/4722366482869645213696, which is 4.5e-23 *below* 10^-6. check_capR decides tau_X <= 1/TAU_DEN =
   10^-6 exactly. So C3 (1/TAU_DEN <= tau_local) fails exactly, by 4.5e-23: range_check prints
   `UNCOVERED tau_compat` wherever a cap piece is certified. `--tau-reading decimal` gives the spec's reading (no
   tau_compat line). Cheap fixes, none run: cap pieces with TAU_DEN = 1000001, or a cover2 run at tau = 1.000001e-06,
   or check_localS reading tau as arb("1e-6") / fmpq. The acceptance test in section 7 assumed the decimal reading.
2. **Legacy local endpoints (C7, `--local-legacy` only):** default decimal (Fraction(str), as specified). The source shows the checker uses the
   decimal only for the s-ball of the remainder constants (`sball(repr(s0), repr(s1))`); the chord nodes and h use the
   binary floats (`lam_point(arb(s0))`, `arb(s1) - arb(s0)`). `--local-endpoints strict` takes the intersection of the
   decimal and binary intervals. Strict on cover2_0.5_1.5 alone leaves 14 slivers of width ~1e-17 at internal
   endpoints such as 0.5950000000000001; with all five cover2 files the overlaps close them. Hygiene item for G6.
3. **Extra cell source:** cellsS/range_pieces.jsonl (range_driver.py) is read as source (d). Its records carry
   certificate paths and sha256; a matching sha256 replaces the certificate mtime test. The cellsS/results.jsonl
   check_piece / check_bern lines have no `certs`, so they are ignored with one WARN line (spec rule).
4. **Certificate lookup:** a basename present in several certificate directories is accepted only if all copies are
   byte-identical (cert_case1_s3o4 / s5o4 are in certs_lin/ and certs_pt/, and they are identical).
   certs_range/ (range_driver nodes) is searched as well.
5. **Exact node checks must be recorded:** a check_piece report counts only if it has `node_<cert>` entries with
   ALL_OK for both certificates (check_piece's skip_exact=True would leave them out). A check_bern report counts only
   with `controls_identities_PD` true. check_capR: PIECE_OK and every sub-flag present (E1_E2_E4, E3_pins, P_ok, M_ok,
   K_ok) and all tau_ok_exact flags true.
6. **Tiling (C2):** the union of the closed slabs has to cover [-99/100, cut], starting at -99/100. Overlapping slabs
   are accepted (a slab certificate covers every m in its [lo, hi]), so exact endpoint equality is not required. Case
   1 counts with any cut in (-99/100, 0) and the slabs then have to reach that cut. Today only the cut -9/10 occurs,
   which is the spec's rule. When no slab reports exist at all the line is `UNCOVERED slabs`; when slab pieces exist
   but do not tile, it is `UNCOVERED slab_tiling`, with the reach.
7. **tau_compat (C3):** one compatible (cap piece, local piece) pair per elementary interval suffices, not every pair
   (pieces are independent; at each s one piece per component is enough). It is reported only where both the cap
   and local are covered.
8. **Gap notation:** gaps are printed with exact open/closed ends, e.g. `UNCOVERED cap [1/2, 11/12)` (11/12 itself is
   covered). Points and the open intervals between consecutive endpoints are checked separately, so the range ends
   and shared endpoints get no off-by-one.
9. **Freshness (C6):** the run start is estimated as (report end) - time_s - 2 s. The end is the file mtime, or the
   `time` stamp of range_pieces.jsonl, which is the minute floor of the end and so a safe lower bound. Inputs and the
   checker scripts must predate that start. Scripts checked: check_piece / check_bern together with check_cell,
   check_minorant_cell and ../hp/check_cert; check_capR.py; check_localS.py. For JSONL logs with several records the
   file mtime is the end time of the last record only, so the test is heuristic there; the inventory marks it.
   cover2 files carry no run time, so for them the test is plain mtime order. Consequences today:
   check_bern_case1.txt is stale, because check_bern.py was saved 0.24 s before that run's clock started. It is
   redundant: the 8 linear Case 1 pieces cover. The capR/pieces reports before 00:40 are stale because check_capR.py
   was edited at 00:40:01 (the NSUB extension, documented as unchanged for NSUB = 1). Recording a sha256 of the
   checker in every report would make this exact. Note also that a fresh git clone resets mtimes, so this rule is
   meaningless on a clone: use `--recheck` there. (Since item 14 this rule is only the flagged fallback for reports
   without provenance hashes; the consequences listed here describe the reports of 2026-11-07 before the recheck.)
10. **Cap directories:** capR/pieces/ and capR/pieces_nsub/; capR/pieces/v1/ is not scanned (superseded). A report
    file without a JSON block (still running) is listed as NOT_OK. Node certificates are resolved relative to
    numerics/n7_interval/ (as run_pieces.sh / watch_pieces.sh call check_capR); their `s` (or coulomb -> 1), cell
    [-1, -99/100] and D = 12 are verified.
11. **Self-test:** `--selftest` (< 1 s, light) covers:
    - G5 with negative controls: the LHS of all identities vanishes for S0, through check_cell.lhs_polys at D = 10
      and 12 with zero blocks. For slabs, S0 needs psi = 0 and c_gamma = 1, which (6) then fixes, and (6) holds.
    - the coverage, tiling and tau engine on synthetic pieces.
    - the sha256 freshness rule (item 14) on synthetic files in a temporary directory: matching hashes fresh;
      changed checker, changed input, unrecorded input stale; no provenance -> flagged mtime fallback.
    - the section 7 acceptance test in memory, updated to the present inventory (review M4): the cap component is
      replaced by the two k/12 capR reports with PIECE_OK / P_ok flipped (files untouched). Result: cap gaps
      [1/2, 11/12) and (13/12, 3/2]; case1 and local covered; the slab / slab_tiling gaps equal those of the run
      with the real cap reports (computed, not hard-coded; empty today); tau_compat: none with the decimal reading,
      [11/12, 13/12] with the binary reading. Freshness is off in this test. (The old expectation "slabs uncovered
      on [1/2, 3/2]" was the state of 00:30 and made the self-test fail once the slab pieces existed.)

    The re-run part of item 4(ii), one cell piece and one local piece re-run from scratch, is behind
    `--selftest-rerun`, and the full re-run is behind `--recheck`. Both go through ../heavy_lock.py and have not been
    run. No check needs an SDP.

12. **Exact local files (cover2q, 2026-11-07 00:50).** check_localS.py now has a `cover2q` mode. It takes exact
    rational piece endpoints, written as "p/q" strings, and an exact Fraction tau, which enters r as
    arb(num)/arb(den) through qarb. range_check reads `localS/cover2q_*_tau*.jsonl` by default:
    - endpoints are exact Fractions; a non-"p/q" endpoint drops the piece;
    - tau is taken exactly from the file name (token "1e-6" -> 1/1000000; "o" -> "/");
    - the float `cover2_*` files are read only with `--local-legacy`. `--tau-reading` and `--local-endpoints`
      apply to them only.

    Source checks: check_piece's r line uses `qarb(tau)`, qarb maps a Fraction to arb(num)/arb(den), and the
    cover2q main parses a, b, tau as Fractions. With cover2q_1o2_3o2 and cover2q_1o20_48o25 (tau = 10^-6 exactly)
    C3 passes exactly against the cap's TAU_DEN = 10^6, so items 1 and 2 no longer affect the default run.
    The legacy cover2 files are now stale anyway, because check_localS.py was modified after they were written.
    The shift in check_localS.check_piece is rigorous: the nodes are certified with `arb(lam) + shift`, where
    `shift = eps.upper()` is an arb (the exact upper endpoint of the remainder ball), so no binary64 rounding enters.
    `eps_f = float(eps.upper())` is only the value printed in the report. (An earlier version of this note described
    the shift as `arb(lam + shift)` rounded to nearest; that was not the code, review M5.)
13. **Checker hashes.** range_check.json records `checkers`: the sha256 and mtime of every checker script the
    freshness rule relies on (check_piece, check_bern, check_cell, check_minorant_cell, ../hp/check_cert,
    check_capR, check_localS). Each run compares them with the previous range_check.json and prints a
    `CHECKER_CHANGED <path>` line for every script whose hash changed, else one NOTE line. This is information
    only; freshness of a report is decided by the hashes the report itself carries (item 14).
14. **Hash-authenticated reports (review S1, 2026-11-07).** Every piece checker that range_check relies on embeds a
    `provenance` object in its report:
    - capR/check_capR.py: sha256 of check_capR.py; name, path and sha256 of the two node certificates and of the
      directions file; argv, the command line, cwd; the effective settings NSUB, M_TWOSIDED, NWIN, N0, MAXDEPTH,
      RB, RC, RA and the precision; python and flint versions; start time. The hashes are taken before the inputs
      are read.
    - cellsS/check_piece.py (check()): sha256 of check_piece.py and of the modules it relies on (check_cell.py,
      check_minorant_cell.py, ../hp/check_cert.py, read from the loaded modules' files); both certificates; argv,
      command line, cwd and the call parameters (T1, skip_exact). cellsS/check_bern.py the same, with check_piece.py
      among the modules and the NSUB of the call. Node margin profiles are not inputs of any check and are not hashed.
    - localS/check_localS.py (check_piece(), hence every cover2q record): sha256 of check_localS.py (it has no input
      files), argv / command line / cwd and the call (s0, s1, tau, exact).
    range_check.py (`hash_auth`): a report with provenance is fresh iff the sha256 it records for every file in
    SCRIPTS[checker] (the checker and its modules, matched by file name) equals the current file's, and its recorded
    (name, sha256) pairs of the inputs equal those of the inputs range_check resolves itself (node files named in the
    cap report, certificates named in the cell report; same number of inputs). A mismatch drops the piece as
    `stale (sha256): ...`. Reports without provenance fall back to the mtime rule of item 9; such used pieces are
    counted in a `NOTE authentication` line and listed per file as `NOHASH` lines. `--no-freshness` switches both
    off. cellsS/check_range_cover.py applies the same comparison to the range_pieces.jsonl reports.
    `--recheck` re-runs every piece that would be used if its report were fresh (report OK, bookkeeping sound, only
    staleness problems), with the settings the report records (NSUB from P_nsub, M_TWOSIDED from M_remainder, window
    radii; defaults are refused if the report's windows differ and it records no settings), through heavy_lock.py,
    one at a time. Each new report is written back into the file it came from, in the same format (cap: the whole
    check_capR output; range_pieces.jsonl: the record with the new `report`, `PIECE_OK`, `time`, `previous_time`;
    logs/check_piece_*.txt and cover2q files: the line of that piece), after the original file was copied to
    pre_recheck/<time>/<relative path> (never deleted). Every recheck line compares the stored and the new report:
    verdict, and the numeric fields present in both (time_s, provenance, paths excluded). After the loop the
    inventory is read back from disk, so the verdict of a `--recheck` run is that of the regenerated, hash-carrying
    reports, and a following plain run sees only those for the used pieces. A crashed re-run writes a NOT_OK record
    (with `error`) instead of keeping the old report.
15. **Review hygiene items M1-M3 (2026-11-07).** M1: check_capR.py combines bounds over several balls with `lo_min`
    (exact smallest lower endpoint; a non-finite endpoint gives -inf) and `hi_max` (largest upper endpoint), not
    with min()/max() on arb (python-flint 0.6.0 compares overlapping balls as neither smaller nor larger, so min()
    kept its first argument): P step running minimum, the two node bounds in lower_bound, the cover minima, the
    window minima mB, mC, mA, the B and C segment minima, the pin error eps_k and the near-1 maximum. G^+ keeps a
    NaN upper bound instead of replacing it by 0. The other checkers already compared by `.lower()` or over floats
    / exact endpoints (comments added). M2: check_capR.load_object asserts exact symmetry of every reduced block of
    the nodes and of the seven directions (`blocks_symmetric`, report field `M2_blocks_symmetric`, part of E1_E2_E4);
    check_cell's bareiss_pd already tests symmetry. Both changes only make the checkers stricter. Before/after on
    [7/12, 2/3] (cap, thinnest piece) and slab [-93/100, -183/200] on [1/2, 9/16]: identical verdicts and identical
    report numbers (473 resp. 32 common fields, 0 differences). M3 (ball midpoints in the mean-value radii) is not
    changed: the evaluation balls contain the true midpoint and width, and the mean-value form is centred at the
    true midpoint, so no rad(mid) term is missing (comment in lower_bound).
16. **Review hygiene items M2-M4 of REVIEW_ext_fable.md (2026-11-07 evening; glue only, no checker changed).**
    - M2, recorded call vs record. A cover2q record counts only if its `provenance.call` was made by
      check_localS.check_piece with `exact: true` and with s0, s1, tau equal (as Fractions) to the record's endpoints
      and to the tau of the file name. A record without `provenance.call` is dropped. A contradicting record is
      dropped, a `PROVENANCE_MISMATCH` line is printed, and the run ends in RANGE_FAIL even if the remaining pieces
      cover the range; this applies to any OK-claiming record, inside the requested range or not, because a
      contradiction means a renamed or hand-assembled file. For cap reports the same applies to `provenance.argv`:
      a, b and TAU_DEN, as check_capR was called, must equal the report's a, b and tau. This is a weaker test there,
      since the checker writes a, b, tau into the report from its own arguments. Reports without provenance
      (mtime fallback) have nothing to compare. The legacy float cover2 files (`--local-legacy`) are not
      cross-checked.
    - M3, range_check's own identity. Every run prints `NOTE range_check.py sha256 <hash>` with the python and
      python-flint versions of the run, plus the versions recorded by the used reports. A WARN is printed if the
      used reports record more than one version pair. The JSON records `range_check` (path, sha256, python, flint)
      and `report_versions`. Against the previous JSON (`--json-out`), a changed range_check.py sha256, a changed
      run version or a changed report-version set prints a WARN line. A WARN does not fail the run: the verdict is
      decided by the reports and the code that runs now, so a changed engine is a reason to re-read the output, not
      evidence against it. Failing would make every legitimate change of range_check.py (this one included) end in
      RANGE_FAIL.
    - M4, what `--recheck-new` may skip. Every piece in the JSON now carries `report_sha256`: the sha256 of the cap
      report text, or of the canonical JSON of the record. It also carries `rechecked`, the label of the --recheck
      run that re-ran it OK, or null. The top level has `piece_recheck_status: true`. A piece is skipped only if the
      baseline lists it (same source, record, a, b) as `used`, with a non-null `rechecked`, and with a
      `report_sha256` equal to the current report's. A baseline without `piece_recheck_status` cannot show which
      pieces were re-run, so nothing is skipped: this covers every JSON written before this change, including
      ext/pre_ext/range_check.json and range_check.json. A plain run carries `rechecked` forward from the previous
      JSON for byte-identical reports, so the recheck record survives later plain runs. A NOTE line counts the used
      pieces with a recorded recheck.
    - Selftest: 22 new cases (77 in all), with negative controls. A cover2q file produced at tau = 10^-6 and
      renamed to tau1e-5 is dropped. Added to the real files, it turns RANGE_OK into RANGE_FAIL with nothing
      uncovered. Also dropped: call.exact false, a wrong call.s1, cap argv with a wrong b or TAU_DEN. For M3: a
      doctored previous JSON gives three WARN lines and still RANGE_OK. For M4, these are re-run: a baseline piece
      listed but not rechecked, a rechecked piece whose report changed, a listed but unused piece, and every piece
      of a legacy baseline.
