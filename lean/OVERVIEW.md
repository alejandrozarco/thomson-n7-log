# Overview of the Lean formalisation

This note explains the structure of the Lean 4 code in this directory. It is written for readers who know Lean and
Mathlib. Paths are relative to `lean/`. Upstream names refer to the Coulomb formalisation
[huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) at commit `25f2fa5`, file
`formal/lean/ThomsonN7/Solution.lean`, namespace `ThomsonN7`.

AI models wrote this code and this note (see [`../AI_DISCLOSURE.md`](../AI_DISCLOSURE.md)). The proof is checked by
the Lean kernel; section 5 lists the build records. No human has read the proof in full, and it is not peer
reviewed. In the terminology of the Lean community it is a *warrant*, not a human-readable proof.

## 1. The statement

`LogN7/Challenge.lean` states two theorems with `sorry`. `LogN7/Solution.lean` proves the same two statements over
the same definitions.

```lean
-- namespace ThomsonN7Log
noncomputable def logEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, -Real.log ‖x i - x j‖

theorem thomson_seven_log :
    ∀ x ∈ SphereConfig 7, logEnergy pentBipyramid ≤ logEnergy x

theorem thomson_seven_log_unique :
    ∀ x ∈ SphereConfig 7, logEnergy x = logEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i))
```

`R3`, `SphereConfig`, `cyl` and `pentBipyramid` are upstream's definitions. They are in `ThomsonGen/Preamble.lean`,
which `regen.sh` regenerates from upstream (section 5). `R3` is `EuclideanSpace ℝ (Fin 3)`. `SphereConfig n` is the
set of injective maps `Fin n → R3` with unit values. `pentBipyramid` puts points `0..4` on the equator at angles
$`2\pi k/5`$, point `5` at the north pole and point `6` at the south pole. Injectivity excludes coincident points,
where `Real.log 0 = 0` would apply.

## 2. Proof architecture

For unit vectors, $`-\log\lVert x-y\rVert = \varphi(\langle x,y\rangle)`$ with $`\varphi(t) = -\tfrac12\log(2-2t)`$
(`LogLean.Minor.phi`). So $`E(x) = \sum_{i \lt j}\varphi(t_{ij})`$ with $`t_{ij} = \langle x_i,x_j\rangle`$, and
$`E(P) = -\log(1600\sqrt5)`$. The argument follows the upstream Coulomb proof with the kernel $`\varphi`$ replaced.

**Case split.** Relabel so that $`t_{01}`$ is the smallest inner product.
- *Case 1*: all $`t_{ij} \ge -9/10`$.
- *Five slabs*: $`t_{01}`$ in $`[-99/100,-49/50]`$, $`[-49/50,-24/25]`$, $`[-24/25,-47/50]`$, $`[-47/50,-93/100]`$,
  $`[-93/100,-9/10]`$.
- *The cap*: $`t_{01} \in [-1,-99/100]`$. It contains $`P`$.

**Certificates.** Each cell has a three-point semidefinite certificate: minorant polynomials $`H`$ (one for Case 1;
$`H_A, H_B, H_C`$ by pair class otherwise), a number $`e`$, packed PSD blocks and SOS multipliers. The certificate
gives $`\sum_{i \lt j} H_{\mathrm{cls}(i,j)}(t_{ij}) \ge e`$. Its checks are `Bool` functions (PSD by $`LDL^\top`$
plus a diagonally dominant remainder; polynomial identities by Kronecker substitution). Each check is closed by
`decide +kernel`. Upstream soundness lemmas (`ThreePoint.typed7_bound`, `Cert.TCert.sound_lo`) turn the checks into
the bound.

**Minorants.** Separate theorems show $`H \le \varphi`$ on the range of each class. Then $`E(x) \ge e`$. For Case 1
and the slabs, $`e > E(P)`$, so $`E(x) > E(P)`$ on those cells.

**The cap.** The cap certificate has $`E(P) - e \le \delta = 10^{-16}`$, with $`e \lt E(P)`$. The argument for
$`E(y) \le E(P)`$ continues:
1. *Slack*: every term $`(\varphi - H_{\mathrm{cls}})(t_{ij})`$ is at most $`\delta`$.
2. *Coercivity*: $`\varphi - H_X \le \delta`$ forces $`t`$ within $`\tau = 1/1650`$ of an inner product of $`P`$
   ($`-1`$ for class A, $`0`$ for B, $`\cos 72^\circ`$ or $`\cos 144^\circ`$ for C).
3. *Ring rigidity*: for $`\tau \le 1/10`$ the Gram matrix of $`y`$ is entrywise within $`\tau`$ of that of a
   relabelled $`P`$ (upstream `T4.ring_rigid`).
4. *Gram window to coordinates*: some $`g \in O(3)`$ gives $`\lVert g y_i - P_i\rVert \le (11/2)\tau = 1/300`$
   (upstream `GV.exists_iso_close`).
5. *Local lemma*: within sup distance $`1/300`$ of $`P`$, $`E \ge E(P)`$, with equality only on $`O(3)\cdot P`$.

**Assembly.** `ThomsonGen.seven_of_specs` combines Case 1, the five `SlabSpec`, the `CapSpec` and the local
statement `LocalMinAt φ (11/2 · τ₀)` into `ThomsonGen.Main φ`. `LogN7/Main.lean` instantiates it with
`φ = LogLean.Minor.phi` and $`\tau_0 = 1/1650`$, and rewrites `pairEnergy φ` as `logEnergy` on unit vectors.

## 3. Map from steps to modules

| step | module(s) | key declarations |
|---|---|---|
| $`E`$ as a sum of $`\varphi`$; value $`E(P)`$ | `LogN7/Basic.lean` | `LogN7.logEnergy_eq_pairEnergy`, `LogN7.pairEnergy_pent`, `LogN7.pairEnergy_pent_le` |
| kernel-generic energy and local statements | `ThomsonGen/Generic/Energy.lean` | `ThomsonGen.pairEnergy`, `Main`, `LocalMinAt`, `localMinAt_of_sq`, `localGram_of_localMinAt` |
| case split and gluing | `ThomsonGen/Generic/Glue.lean` | `exists_minpair_perm`, `exists_cell`, `Case1Claim`, `SlabSpec`, `CapSpec`, `capSpec_sound`, `seven_of_specs` |
| rational log bounds, minorant calculus | `LogLean/LogSeries.lean`, `LogLean/MinorCore.lean` | `sum_le_neg_log_one_sub`, `phi_ge_node`, `log2_enc`, `mob_sound`, `Piece.sound`, `chain_sound`, `Tail.sound`, `tube2`, `tube4` |
| $`H \le \varphi`$ per cell; cap coercivity | `LogN7/Minor/MinorCase1.lean`, `LogN7/Minor/MinorSlab*.lean`, `LogN7/Minor/MinorCap.lean` | `CellCase1.HH_le_phi`, `CellSlab9998.HA_le_phi` (etc.), `Cap.capA`, `Cap.capB`, `Cap.capC` |
| certificate + minorants → cell statement | `LogN7/Bridge.lean` | `LogN7.case1Claim_of_cert3`, `LogN7.slabSpec_of_minor`, `LogN7.capSpec_of_minorN` |
| Case 1 | `LogN7/Case1/` | `LogN7.Case1.r2c1_cf_ok`, `LogN7.Case1.claim` |
| slabs | `LogN7/S9998/` … `LogN7/S9390/` | `LogN7.S9998.spec` … `LogN7.S9390.spec` |
| cap certificate | `LogN7/Cap/`, `ThomsonGen/Cert/NBlk.lean`, `ThomsonGen/Cert/NBlkCap.lean`, `ThomsonGen/Cert/Split.lean` | `LogN7.tc_cap_meta`, `Cert.TCertN.sound_lo`, `ThomsonGen.capSpec_of_tcertN`, `LogN7.Cap.spec` |
| ring rigidity, Gram window | `ThomsonGen/Generic/Glue.lean`, `ThomsonGen/Generic/Energy.lean` | `tubeRigid_of_le`, `cap_of_typed_tube`, `localGram_of_localMinAt` |
| local lemma L′ | `LogLean/Local*.lean` (table below) | `LocalMain.Lprime`, `LocalMain.Lprime_nonneg`, `LocalMain.Lprime_eq` |
| hand-off to the cap | `LogLean/LocalHandoff.lean`, `LogLean/LocalBridge.lean` | `LocalHandoff.pent_local_min_sup_log`, `LocalBridge.Pbip_eq_pent` |
| assembly | `LogN7/Main.lean`, `LogN7/Solution.lean` | `LogN7.hcap`, `LogN7.hslab`, `LogN7.localMinAt`, `LogN7.main`, `LogN7.thomson_seven_log`, `LogN7.thomson_seven_log_unique` |

The local lemma in detail (section 4.4 explains the mathematics):

| ingredient | module(s) | key declarations |
|---|---|---|
| the field $`K = \mathbb{Q}(\alpha)`$, $`\alpha = \sqrt{10+2\sqrt5}`$; sparse polynomials over $`K`$ | `LocalKel`, `LocalSP` | `LocalSP.ev_eq_of_eqPoly`, `LocalSP.eq_of_checkEq6` |
| $`P`$, tangent frames, kernel vectors, criticality, as exact data | `LocalFrames` | `LocalFrames.frameOK_true`, `LocalFrames.critOK_true` |
| chart, gauge, pair inequality ($`-\log(1-u) \ge u + \dots + u^5/5`$) | `LocalGeom`, `LogSeries` | `LocalGeom.gauge_rot`, `LocalGeom.w_ker`, `LocalGeom.norm_split`, `LocalGeom.pair_lower`, `LocalGeom.crit_sum` |
| tail majorant of degree $`\ge 7`$, one check per pair class | `LocalAtom` | `LocalAtom.class_bound`, `LocalAtom.check_adj`, `LocalAtom.bound_adj` |
| Taylor data: 21 pair identities, global $`(\sigma,w)`$ expansion | `LocalPairData`, `LocalPairsA`–`C`, `LocalGlobData`, `LocalGlobA`–`E`, `LocalGlobal` | `LocalPairs.check01`, `LocalGlobal.F2_exp`, `LocalGlobal.F3_exp`, `LocalGlobal.F4_exp` |
| Bombieri bounds | `LocalBomb`, `LocalGlobal` | `LocalBomb.bombieri`, `LocalGlobal.bomb_F3w`, `LocalGlobal.pair_bomb` |
| quadratic certificate (C′), coupling bound | `LocalCert`, `LocalGamma1` | `LocalCert.certOK_true`, `LocalCert.Cprime`, `LocalGamma1.coupling_bound` |
| scalar argument | `LocalScalar` | `LocalScalar.scalar_param` |
| assembly of L′ | `LocalMain` | `LocalMain.Lprime_core`, `LocalMain.Lprime`, `LocalMain.pent_local_min_sup_log` |

## 4. New relative to the Coulomb proof, and reused

**Reused unchanged** (regenerated, not stored): the certificate machinery (packed blocks, `Blk.ok`, the typed
three-point identity, Kronecker evaluation), the Case 1 statistics, ring rigidity `T4.ring_rigid`, the chart lemma
`GV.exists_iso_close`, the gauge lemma `Reg.exists_gauge`, and the statement definitions. None of these mentions the
kernel.

**Adapted** (stored, each with an attribution comment naming the upstream declaration): the glue lemmas, the
local-statement transport, `capSpec_of_tcertN` and a few small lemmas. The full list is in `README.md`, section
Upstream code.

### 4.1 Kernel-generic refactor (`ThomsonGen/Generic/`)

Upstream glue is stated for `coulombEnergy` and hard-codes the tube width $`1/165000`$. `Energy.lean` defines
`pairEnergy φ x = ∑_{i<j} φ ⟪x i, x j⟫` for any `φ : ℝ → ℝ`. `Glue.lean` restates the gluing with the kernel `φ`,
the tube width `τ₀` and the local statement `LocalMinAt φ (11/2 · τ₀)` as parameters. The proofs use only the sum
form, $`O(3)`$ and $`S_7`$ invariance, and the kernel-free upstream lemmas.

### 4.2 Rational log bounds and the minorant calculus (`LogLean/LogSeries.lean`, `LogLean/MinorCore.lean`)

`sum_le_neg_log_one_sub`: for odd $`n`$ and all $`u \lt 1`$, $`\sum_{k=1}^n u^k/k \le -\log(1-u)`$. The proof is by
monotonicity of the difference, not by Mathlib's series. `MinorCore.lean` uses it to prove $`H \le \varphi`$ on an
interval split into pieces `[A/D, B/D)`:
- each `Piece` has a rational node $`g`$ with $`2(1-g)`$ a product of powers of 2, 3 and 5, and a lower bound for
  $`\varphi(g)`$ from rational enclosures of $`\log 2, \log 3, \log 5`$ (`log2_enc`, `log3_enc`, `log5_enc`);
- `phi_ge_node` bounds $`\varphi`$ below by that constant plus a Taylor polynomial in $`(t-g)/(1-g)`$;
- the difference with $`H`$ is an integer polynomial; `mob_sound` shows it is nonnegative on the piece from the signs of
  its coefficients after a Möbius change of variable;
- a `Tail` covers $`[T_0/D, 1)`$ by monotonicity of $`\varphi`$.

Each piece check is a `Bool` closed by `decide +kernel`. For coercivity on the cap, the same checks are applied to
$`H`$ plus a term $`\kappa(t+1)`$, $`\kappa t^4`$ or $`\kappa(t-c)^2`$ near the contact points of classes A, B and C,
and to $`H`$ plus $`2\cdot10^{-16}`$ away from them. `tube4` (class B) and `tube2` (class C) then give the window.
For example, `Cap.capB` checks $`H_B + t^4/1000 \le \varphi`$ on $`[-1/20, 1/20]`$.

### 4.3 Facially reduced cap blocks and per-block splitting (`ThomsonGen/Cert/`)

The cap certificate is tight at $`P`$, so its PSD blocks are singular. Upstream `Blk.ok` cannot certify a singular
block. `NBlk.lean` stores each block as $`N B' N^\top`$ with an integer basis $`N`$ and a positive definite reduced
block $`B'`$. $`B'`$ is checked as upstream; the expanded block is computed in the kernel and fed to the upstream
identity checks. The only new fact is positivity by congruence (`NBlk.qf_expand_nonneg`,
`NBlk.fmat_psd_expand`). `TCertN.sound_lo` is the resulting soundness lemma, and `NBlkCap.lean` turns it into a
`CapSpec`. `Split.lean` (`TCert.checkMeta_of_parts`, `hybChk_of_parts`) checks the same Booleans one block at a time,
to keep each `decide +kernel` within memory. The cap check modules (`LogN7/Cap/ChkS*.lean`) go further and check one
row per declaration.

### 4.4 The quartic local lemma L′ (`LogLean/Local*.lean`)

*Why it is needed.* At $`P`$ the Hessian of $`E`$ on the 14-dimensional tangent space of $`(S^2)^7`$ has a
5-dimensional kernel: three rotation fields and two ring fields $`s_1, s_2`$. Along $`s_1`$ (resp. $`s_2`$) ring
point $`k`$ moves along the polar axis by $`\cos(4\pi k/5)`$ (resp. $`\sin(4\pi k/5)`$). Gauge fixing removes the
rotations but not $`s_1, s_2`$. Upstream `Reg.local_ineq` gives $`E - E(P) \ge 10^{-3}\sum_i\lVert y_i - P_i\rVert^2`$
for the Coulomb energy on a gauge-fixed ball. The analogous quadratic inequality is false for the log energy, because
the excess along $`s`$ is of fourth order. The kernel and its dimension are checked exactly by
`../local/check_local_rigorous.py` (step 2), outside Lean. The Lean proof does not need them as a theorem: the five
kernel vectors enter as data (`LocalFrames.Kd`).

*Statement.* `LocalMain.Lprime`: for unit $`y`$ with $`\sum_i P_i y_i^\top`$ symmetric (the gauge) and
$`\sum_i\lVert y_i - P_i\rVert^2 \le (1/100)^2`$,

```math
E(y) - E(P) \ge 0.0268\,\lVert w\rVert^2 + 0.0200\,\lVert s\rVert^4 ,
```

where $`s`$ and $`w`$ are the components of the tangent displacement in $`\mathrm{span}(s_1,s_2)`$ and in its
complement $`W`$ in the gauge-fixed tangent space. In the Lean statement, $`\lVert s\rVert^4`$ is
`(25/4) * (sigR y 0 ^ 2 + sigR y 1 ^ 2) ^ 2` and $`\lVert w\rVert^2`$ is `∑ p ∈ range 14, wcoR y p ^ 2`. The Python
checker certifies the constants 0.0342 and 0.0227 for the same lemma. The Lean constants are smaller because some
error terms are bounded more coarsely (for example the cubic constant `LocalGlobData.G2b` ≈ 2.236, against 1.319021
in Python).

*Proof outline.*
1. *Chart* (`LocalGeom`): $`y_i = (1+\nu_i)P_i + t_i`$ with $`t_i \perp P_i`$, in exact tangent frames over $`K`$.
2. *Pair inequality* (`LocalGeom.pair_lower`): each pair term is bounded below using
   $`-\log(1-u) \ge u + u^2/2 + \dots + u^5/5`$ (`LogLean.sum_le_neg_log_one_sub`). The linear terms collapse by
   criticality of $`P`$ (`crit_sum`).
3. *Tail majorant* (`LocalAtom`): per pair class, the part of degree $`\ge 7`$ is at most $`K_g R^7`$. One
   `decide +kernel` per class.
4. *Taylor data over $`K`$*: the degree-2 to 6 parts are explicit polynomials with coefficients in $`K`$. The pair
   identities (`LocalPairs*`) and the $`(\sigma, w)`$ expansion (`LocalGlob*`) are `decide +kernel` checks.
5. *Bombieri bound* (`LocalBomb.bombieri`): $`|p(x)| \le \lVert p\rVert_B\,|x|^d`$, in squared form, for the
   degree-5 and degree-6 parts and for some error blocks.
6. *Quadratic certificate* (`LocalCert.Cprime`): a $`17\times17`$ matrix over $`K`$ is shown PSD by an exact
   $`LDL^\top`$ plus a diagonally dominant remainder. It gives
   $`\tfrac12\langle w,Hw\rangle + 3C(s,s,w) + \tfrac{13}{40}\lVert s\rVert^4 \ge \tfrac1{16}\lVert w\rVert^2 + \tfrac{29}{500}\lVert s\rVert^4`$
   for $`w \in W`$.
7. *Scalar argument* (`LocalScalar.scalar_param`): an inequality in $`a = \lVert s\rVert`$,
   $`b = \lVert w\rVert`$ and $`T \le 1/100`$, closed by `nlinarith`.
8. *Hand-off* (`LocalHandoff.pent_local_min_sup_log`): `Reg.exists_gauge` gives the gauge without increasing the
   $`\ell^2`$ distance, and sup distance $`1/300`$ gives $`\ell^2`$ distance $`\sqrt7/300 \lt 1/100`$. The result is
   `LocalMinAt φ (1/300)`.

The flat directions also shape the cap. Along $`s`$ the pole–ring inner products move at first order. So
$`H_B`$ must agree with $`\varphi`$ at $`0`$ through the third derivative, and class-B coercivity is quartic. The cap
certificate has degree 12 for this reason.

## 5. Trust surface

- **The statement file.** `LogN7/Challenge.lean` (37 lines) imports only `ThomsonGen.Preamble`. `LogN7/Solution.lean`
  restates `logEnergy` and both theorems, because it cannot import a file that declares the same names. Apart from
  the proof terms, the two files are identical from `namespace ThomsonN7Log` on.
- **Definitions regenerated from upstream.** `regen.sh` clones upstream at commit `25f2fa5`, checks the sha256 of
  `Solution.lean`, splits it, and checks all 20 generated modules against `ThomsonGen/scripts/generated.sha256`.
  `ThomsonGen/Preamble.lean` holds `R3`, `SphereConfig`, `cyl` and `pentBipyramid`. A reader has to check these
  upstream definitions as part of the statement.
- **Axioms.** `LogN7/Check/Axioms.lean` runs `#print axioms` on both theorems. On the recorded build it reports
  `[propext, Classical.choice, Quot.sound]`. No stored file uses `native_decide`, and only `Challenge.lean` contains
  `sorry`. Every certificate check is reduced by the kernel (`decide +kernel`), which uses the kernel's built-in
  `Nat` arithmetic. `maxHeartbeats` and `maxRecDepth` are raised in some files; this affects elaboration only.
- **Generated data.** The certificate data in `LogN7/*/Data*.lean` and in the `Local*` data modules was emitted by
  the scripts in `gen_log/` and `gen/`. The scripts are not trusted: the kernel checks the data.
- **What was checked, and by whom.**
  - The Lean kernel: a clean build in dependency order of the version before the upstream-code changes (154 modules,
    2026-10-01, `../verification/lean/build_2026-10-01_pre_scrub.tsv`). The clean build of the current version
    (157 modules) is in progress (`README.md`, Build test).
  - `scripts/second-kernel.sh` re-checks an export with nanoda. No record of a run is included.
  - Separate read-only AI instances (Claude Opus 5.5, Claude Fable 5.1, gpt-6-astra) reviewed the work
    (`../AI_DISCLOSURE.md`). AI reviews are not peer review.
  - No human expert has checked the proof.

## 6. Where to start

1. `LogN7/Challenge.lean`: the statement.
2. `LogN7/Main.lean`: the assembly (76 lines). It shows every input of `seven_of_specs`.
3. `ThomsonGen/Generic/Glue.lean`: `Case1Claim`, `SlabSpec`, `CapSpec` and `seven_of_specs`, i.e. what each cell
   must deliver.
4. `LogN7/Cap/Spec.lean` with `LogN7/Bridge.lean` (`capSpec_of_minorN`) and `LogN7/Minor/MinorCap.lean`: how the
   cap certificate, the minorants and coercivity become a `CapSpec`.
5. `LogLean/LocalMain.lean` (statement of `Lprime` and the module header), then `LogLean/LocalHandoff.lean`.

Background: `../METHOD.md` (structure of the argument), `../local/LOCAL_LEMMA.md` (the local lemma on paper),
`README.md` (modules, upstream code, build).
