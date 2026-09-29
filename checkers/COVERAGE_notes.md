
## How the cells cover the configuration space

* **Case 1**: every configuration with all t_ij >= -9/10. The certificate gives sum_{i<j} H(t_ij) >= e
  (untyped three-point bound, PAPER.md §5, cut a = -9/10). With H <= phi on [-9/10, 1) this gives E(x) >= e > E(P).
* **Case 2**: min t_ij < -9/10. Relabel so that (0,1) is a pair with minimal inner product. Then t01 lies in the
  cap [-1, -99/100] or in one of the five slabs, whose union is [-99/100, -9/10]; consecutive slabs share their
  endpoints. On a slab [lo, hi] the typed bound (PAPER.md §6) gives sum_{i<j} H_cls(ij)(t_ij) >= e; with H_A <= phi on
  [lo, hi] and H_B, H_C <= phi on [lo, 1) this gives E(x) >= e > E(P).
* **Cap**: e < E(P) by construction (the bound is sharp at P), so the cap certificate alone does not exclude
  anything. It is combined with the minorant contact data (coercivity), ring rigidity and the local lemma; see METHOD.md.

## What the checkers verify

* `check_cell.py` (exact rationals): the SOS multipliers are the ones the cell requires; every kernel block and
  every SOS Gram block is positive definite (Sylvester criterion, fraction-free Bareiss elimination); the
  polynomial identities hold coefficient by coefficient; constraint (6) holds (slabs); e - E(P) > 0 at 60 digits.
  The typed lambda polynomials are taken from `check_cert.py:lam_polys`. As a guard against transcription
  errors in the model of PAPER.md §5.1/§6.3, it also evaluates the global identities on random 7-point
  configurations (Sigma_all computed independently from the root form of Lemma 4.1); this test is not part of
  the certificate.
* `check_minorant_cell.py` (arb, 256 bits): phi - H > 1e-7 on each whole interval, by mean-value bisection with
  exact rational endpoints on [lo, 1 - 2^-20] and monotonicity of phi on [1 - 2^-20, 1).
* `check_cert.py` / `check_minorant.py`: the same for the cap, plus the exact contact conditions of the minorants
  at the touching points of P and the coercivity windows (see METHOD.md).
* Not checked by these scripts: the paper-level deductions (Lemma 4.1, identities (2)/(6), the minimal-pair
  reduction, the gluing of the cells, and for the cap the rigidity and local steps other than those in
  `local/check_local_rigorous.py`).

## Coulomb calibration certificate

`certificates/cells/calib_case1_coulomb_D10.json` is a Case-1 certificate (cut -9/10, D = 10) for the Coulomb kernel
(Riesz s = 1) produced by the same pipeline, with e - E(P) = +1.0e-3. It is not part of the log case split; it is
included as a consistency check of the pipeline on the kernel for which a formal proof exists (upstream reports a
Case-1 margin of +3.2e-4). It is checked separately (`verification/check_cell_coulomb_calib.txt`).
