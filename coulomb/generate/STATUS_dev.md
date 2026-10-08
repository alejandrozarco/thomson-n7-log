# N = 7, Coulomb (s = 1): independent certificate chain (2026-10-07; private, not reviewed)

Same case split as the published log / s = 2 warrant (Case 1 at -9/10, five slabs, cap [-1, -99/100]).

| piece | file | check | result |
|---|---|---|---|
| Case 1, D10 | cells1/certs/cert_case1_coulomb_D10.json | check_cell.py, check_minorant_cell.py | e - E(P) = 5e-4, ALL_OK |
| slabs 1-5 (D10, D10, D12, D12, D12) | cells1/certs/cert_slab_*_coulomb_D*.json | same | e - E(P) = 1e-5 each, ALL_OK |
| cap, D12, value-only face | cap1/cert_cap_coulomb_D12.json | check_cap1.py | identities exact, PSD exact, minorants exact (Sturm), E(P) - e = 7.3e-17 <= 1e-16 |
| coercivity (K2-K4) | cap1/check_coerc1.py | arb + exact decision | phi - H <= 1e-16 => |t - touch| <= tau = 1e-6 (tau_B 8.7e-7, tau_C 6.6e-7, tau_A 2.6e-14) |
| local lemma (replaces K10 / L) | cap1/check_local1.py | arb | E(z) > E(P) for gauge-fixed unit z, 0 < |z - P| <= r = sqrt7 (11/2) 1e-6; lambda_S >= 0.00919, G = 0.0041 > 0 |

Kernel-free steps K6 (ring rigidity, tau <= 1/10), K7 (factor 11/2), K8 (gauge), K9 (sup -> l2) as for log.
Differences from log: no soft (pucker) face conditions (infeasible at s = 1); quadratic contact at 0 and c1,2 with
dyadic slopes (mismatch <= 1.2e-20, handled in the coercivity bound); second-order local lemma (P nondegenerate at s = 1).
Not done: independent review, Lean. Hung Tran's Coulomb result (upstream, unlicensed) is a different, earlier proof.
