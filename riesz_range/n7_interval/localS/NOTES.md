# Work package B: second-order local lemma across s (2026-11-06)

`check_localS.py` = `../cap1/check_local1.py` with general s (ball arithmetic, 256 bits). Statement as there: for
gauge-fixed unit z with 0 < |z - P| <= r = sqrt7 (11/2) tau, E_s(z) > E_s(P).

Pointwise (`grid_tau1e-6.jsonl`, tau = 1e-6):

| s | lambda_S | tau_max (largest tau the argument covers) | OK at tau = 1e-6 |
|---|---|---|---|
| 0.01 | 1.8e-6 | 1.3e-7 | no |
| 0.05 | 4.4e-5 | 6.4e-7 | yes |
| 0.1 | 1.7e-4 | 1.2e-6 | yes |
| 0.5 | 3.5e-3 | 4.3e-6 | yes |
| 1 | 9.2e-3 | 4.9e-6 | yes (= check_local1.py) |
| 1.5 | 1.0e-2 | 3.2e-6 | yes |
| 1.9 | 3.1e-3 | 7.1e-7 | yes |
| 1.95 | 1.6e-3 | 3.6e-7 | no |

lambda_S ~ s^2 as s -> 0 and ~ (2 - s) as s -> 2 (the flat ring mode of the log and s = 2 cases); tau_max ~ s and
~ (2 - s). So at the ends the local lemma needs ever smaller coercivity windows from the cap.

Uniform on intervals (`cover2`, chord + remainder, see the docstring): M(s) is linear in the 8 values phi_s^(m)(t_k),
so B(s) = Pi_S M Pi_S is the chord between the piece ends plus an error <= (h^2/8) sum max|f''| |B_k|_F.
Results at tau = 1e-6, all pieces certified:

| interval | pieces | file |
|---|---|---|
| [0.5, 1.5] | 15 | cover2_0.5_1.5_tau1e-06.jsonl |
| [0.1, 1.9] | 44 | cover2_0.1_1.9_tau1e-06.jsonl |
| [0.05, 1.92] | 62 | cover2_0.05_1.92_tau1e-06.jsonl |
| [0.03, ...] | fails at 0.03 (tau too large there) | |

So the local step is not the bottleneck for a range inside about [0.05, 1.92]; the cap coercivity windows (tau(s))
and the cells decide the range. Not reviewed. Not in Lean.

Exact cover (2026-11-07, `cover2q`): piece endpoints and tau are exact rationals (arb(num)/arb(den)), so the certified
statement is for the closed rational intervals as written and tau = 10^-6 exactly (the float `cover2` runs certify
float(1e-6), 4.5e-23 below 10^-6, and float endpoints; flagged by range_check.py). Results, both ALL_OK in seconds:
[1/2, 3/2] 15 pieces (cover2q_1o2_3o2_tau1e-6.jsonl); [1/20, 48/25] 62 pieces (cover2q_1o20_48o25_tau1e-6.jsonl).
