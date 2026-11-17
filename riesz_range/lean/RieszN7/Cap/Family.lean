import RieszN7.Cap.TCertR
import ThomsonGen.Generic.Glue

/-!
# The real-family bridge `capSharp_of_family` (LEAN_PLAN_range.md §3.2.3, risk R3)

A cap piece certifies, for every `s` in a rational interval, the certificate family
`C(s) = Σ_j w_j(s) C_j`.  Here `C_j` are finitely many `TCertR` objects (two nodes and seven pin-response
directions) that share the cut, the degrees, the face bases `N`, the monomial bases `z` and the multiplier codes
`g`; the weights are `w = (1 − λ, λ, ρ_1, …, ρ_7)` (real, of either sign).  This module proves, for **fixed real
weights** `w : Fin J → ℝ`:

* the three slacks `lamA`, `lamB`, `lamG` of `ThreePoint` are linear (homogeneous) in the certificate data
  (`lamA_fsum`, `lamB_fsum`, `lamG_fsum`; checked against the definitions in `ThomsonGen/Typed.lean`);
* from the objects' kernel identities (`TCertR.chkA/B/G`, i.e. `idA_ev`, …), the family slack is
  `Σ_r g_r · Yᵀ (Σ_j w_j/c_j R_{r,j}) Y` with the shared `g_r`, `Y = Nᵀ z`, so it is nonnegative on the cut as soon as
  every reduced family block `Σ_j (w_j / c_j) R_{r,j}` has a nonnegative quadratic form (`famA_nonneg`, …);
* the family's kernel blocks `Σ_j w_j F_{k,j}` are PSD by congruence when the reduced family blocks are PSD
  (`famF_psd`);
* hence the typed bound for the family (`family_bound`) and, with the energy comparison `E_φ(P) ≤ e` and the three
  minorant facts with exact contacts, `CapSpecSharp φ a0` (`capSharp_of_family`).

The PSD inputs are exactly what the piece module `Cap.P<a>_<b>.PSD` (Step P, §3.2.2) has to provide, and the
energy/minorant inputs are the pins/e-row (E2/E3) and Step M (§3.2.4).

Private working module (2026-11-08), AI-written, not reviewed.
-/

open Real
open scoped RealInnerProductSpace Matrix

namespace ThomsonN7.Cert.CapR

open ThomsonN7 Kron Kron.Ex ThreePoint

/-! ## 1. Linearity of the three slacks and of `Sk` -/

section Lin

variable {ι : Type*} [DecidableEq ι]

lemma lamA_fsum (s : Finset ι) (w : ι → ℝ) (SP SR : ι → ℝ → ℝ → ℝ → ℝ) (HA ψ : ι → ℝ → ℝ)
    (cal : ι → ℝ) (u v t : ℝ) :
    lamA (fun a b c => ∑ i ∈ s, w i * SP i a b c) (fun a b c => ∑ i ∈ s, w i * SR i a b c)
        (fun x => ∑ i ∈ s, w i * HA i x) (fun x => ∑ i ∈ s, w i * ψ i x) (∑ i ∈ s, w i * cal i) u v t
      = ∑ i ∈ s, w i * lamA (SP i) (SR i) (HA i) (ψ i) (cal i) u v t := by
  induction s using Finset.induction_on with
  | empty => simp [lamA, gm]
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    rw [← ih]
    simp only [lamA, gm]
    ring

lemma lamB_fsum (s : Finset ι) (w : ι → ℝ) (SP SR : ι → ℝ → ℝ → ℝ → ℝ) (HB ψa ψc : ι → ℝ → ℝ)
    (cbe : ι → ℝ) (u v t : ℝ) :
    lamB (fun a b c => ∑ i ∈ s, w i * SP i a b c) (fun a b c => ∑ i ∈ s, w i * SR i a b c)
        (fun x => ∑ i ∈ s, w i * HB i x) (fun x => ∑ i ∈ s, w i * ψa i x)
        (fun x => ∑ i ∈ s, w i * ψc i x) (∑ i ∈ s, w i * cbe i) u v t
      = ∑ i ∈ s, w i * lamB (SP i) (SR i) (HB i) (ψa i) (ψc i) (cbe i) u v t := by
  induction s using Finset.induction_on with
  | empty => simp [lamB, gm]
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    rw [← ih]
    simp only [lamB, gm]
    ring

lemma lamG_fsum (s : Finset ι) (w : ι → ℝ) (SR : ι → ℝ → ℝ → ℝ → ℝ) (HC ψc : ι → ℝ → ℝ)
    (cga : ι → ℝ) (u v t : ℝ) :
    lamG (fun a b c => ∑ i ∈ s, w i * SR i a b c) (fun x => ∑ i ∈ s, w i * HC i x)
        (fun x => ∑ i ∈ s, w i * ψc i x) (∑ i ∈ s, w i * cga i) u v t
      = ∑ i ∈ s, w i * lamG (SR i) (HC i) (ψc i) (cga i) u v t := by
  induction s using Finset.induction_on with
  | empty => simp [lamG, gm]
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    rw [← ih]
    simp only [lamG, gm]
    ring

lemma Sk_fsum (K : ℕ) (m : ℕ → ℕ) (s : Finset ι) (w : ι → ℝ)
    (F : ι → (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (u v t : ℝ) :
    Sk K m (fun k => ∑ i ∈ s, w i • F i k) u v t = ∑ i ∈ s, w i * Sk K m (F i) u v t := by
  induction s using Finset.induction_on with
  | empty => simp [Sk, matDot]
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    rw [← ih]
    simp only [Sk, matDot, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring

end Lin

/-! ## 2. Finset algebra for the congruence -/

/-- `xᵀ (n R nᵀ) x = Yᵀ R Y`, `Y = nᵀ x`, for a real middle matrix (the real-valued form of `NBlk.qf_eent`). -/
lemma qf_congr (m r : ℕ) (n : ℕ → ℕ → ℝ) (R : ℕ → ℕ → ℝ) (x : ℕ → ℝ) :
    ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m,
        x a * (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, n a i * R i j * n c j) * x c
      = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
          (∑ a ∈ Finset.range m, n a i * x a) * R i j * (∑ c ∈ Finset.range m, n c j * x c) := by
  have lhs : ∀ a c, x a * (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, n a i * R i j * n c j) * x c
      = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, x a * (n a i * R i j * n c j) * x c := by
    intro a c
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  have rhs : ∀ i j, (∑ a ∈ Finset.range m, n a i * x a) * R i j * (∑ c ∈ Finset.range m, n c j * x c)
      = ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m, x a * (n a i * R i j * n c j) * x c := by
    intro i j
    rw [Finset.sum_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  simp only [lhs, rhs]
  exact NBlk.sum4_comm fun a c i j => x a * (n a i * R i j * n c j) * x c

/-- Pulling a weighted sum over objects inside a double sum. -/
lemma fam_swap {ι : Type*} (s : Finset ι) (r : ℕ) (cw : ι → ℝ) (Y Z : ℕ → ℝ) (E : ι → ℕ → ℕ → ℝ) :
    ∑ j ∈ s, cw j * ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, Y i * E j i i' * Z i'
      = ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, Y i * (∑ j ∈ s, cw j * E j i i') * Z i' := by
  calc ∑ j ∈ s, cw j * ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, Y i * E j i i' * Z i'
      = ∑ j ∈ s, ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, cw j * (Y i * E j i i' * Z i') := by
        simp only [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range r, ∑ j ∈ s, ∑ i' ∈ Finset.range r, cw j * (Y i * E j i i' * Z i') :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, ∑ j ∈ s, cw j * (Y i * E j i i' * Z i') :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- A list sum as a sum over the index range. -/
lemma list_sum_map_range {α : Type*} (S : List α) (d : α) (f : α → ℝ) :
    (S.map f).sum = ∑ r ∈ Finset.range S.length, f (S.getD r d) := by
  induction S with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-! ## 3. The quadratic form of one reduced SOS block -/

/-- The monomial vector pushed through the face basis: `Y_i = Σ_a N_{a i} z_a(u,v,t)`. -/
noncomputable def Yv (N : List (List ℤ)) (zs : List (ℕ × ℕ × ℕ)) (u v t : ℝ) (i : ℕ) : ℝ :=
  ∑ a ∈ Finset.range zs.length, (((N.getD a []).getD i 0 : ℤ) : ℝ) * zval zs u v t a

/-- **The block form, on the reduced side, as a real quadratic form** (wf gives the shape facts). -/
lemma qf_tblkR (s : TBlkR) (hwf : s.wf = true) (u v t : ℝ) :
    (sqfF s.nb.expand s.z).ev u v t
      = ∑ i ∈ Finset.range s.nb.r, ∑ j ∈ Finset.range s.nb.r,
          Yv s.nb.N s.z u v t i * (s.nb.inner.ent s.nb.r i j : ℝ) * Yv s.nb.N s.z u v t j := by
  obtain ⟨-, -, -, hlen, hrows, -⟩ := TBlkR.wf_parts hwf
  rw [ev_sqfF, ev_sqfE]
  have h1 : ∑ q ∈ Finset.range s.z.length, (s.nb.expand.dq q : ℝ)
      * (∑ a ∈ Finset.range s.z.length, (s.nb.expand.lq q a : ℝ) * zval s.z u v t a) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [NBlk.dq_expand]
    simp
  have h2 : ∑ a ∈ Finset.range s.z.length, ∑ c ∈ Finset.range s.z.length,
      zval s.z u v t a * (s.nb.expand.del a c : ℝ) * zval s.z u v t c
      = ∑ a ∈ Finset.range s.z.length, ∑ c ∈ Finset.range s.z.length,
        zval s.z u v t a * (s.nb.eent a c : ℝ) * zval s.z u v t c := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
    simp only [Blk.del, NBlk.expand]
    rw [NBlk.getD_expandΔ s.nb hrows (by have := Finset.mem_range.1 ha; omega)
      (by have := Finset.mem_range.1 hc; omega)]
  rw [h1, h2, zero_add, NBlk.qf_eent]
  rfl

/-! ## 4. Per-object identities in real form -/

namespace TCertR

variable (cf : TCertR)

lemma hdr_Lam : cf.hdr.Lam = cf.Lam := rfl
lemma hdr_dd : cf.hdr.dd = cf.dd := rfl

/-- `mA · 5Λ · lamA(object) = Σ_r g_r · q_r` (the kernel identity `idA`, evaluated). -/
lemma idA_real (hL : 0 < cf.Lam) (hA : cf.chkA = true) (u v t : ℝ) :
    (cf.mA : ℝ) * (5 * cf.Lam * lamA (Sk cf.hdr.K cf.hdr.m cf.hdr.FPm) (Sk cf.hdr.K cf.hdr.m cf.hdr.FRm)
        cf.hdr.HAf cf.hdr.ψBaf cf.hdr.calf u v t)
      = ((cf.SA.map (tblkRE cf.an cf.ad cf.bn cf.bd)).map fun e => e.ev u v t).sum := by
  have h0 := cf.idA_ev hA u v t
  simp only [idA, idTR, TCert.FA, ev_sub, ev_smul, ev_sumE, TCert.SPE, TCert.SRE,
    ev_lamAE cf.hdr.K cf.hdr.m cf.hdr.Lam cf.hdr.blkP cf.hdr.blkR hL] at h0
  push_cast at h0
  change (cf.hdr.mA : ℝ) * (5 * (cf.hdr.Lam : ℝ) * lamA (Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam
      (cf.hdr.blkP k))) (Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam (cf.hdr.blkR k)))
      (polyR cf.hdr.Lam cf.hdr.HA) (polyR cf.hdr.Lam cf.hdr.ψBa) ((cf.hdr.cal : ℝ) / cf.hdr.Lam) u v t) = _
  linear_combination h0

lemma idB_real (hL : 0 < cf.Lam) (hB : cf.chkB = true) (u v t : ℝ) :
    (cf.mB : ℝ) * (4 * cf.Lam * lamB (Sk cf.hdr.K cf.hdr.m cf.hdr.FPm) (Sk cf.hdr.K cf.hdr.m cf.hdr.FRm)
        cf.hdr.HBf cf.hdr.ψBaf cf.hdr.ψCbf cf.hdr.cbef u v t)
      = ((cf.SB.map (tblkRE cf.an cf.ad 1 1)).map fun e => e.ev u v t).sum := by
  have h0 := cf.idB_ev hB u v t
  simp only [idB, idTR, TCert.FB, ev_sub, ev_smul, ev_sumE, TCert.SPE, TCert.SRE,
    ev_lamBE cf.hdr.K cf.hdr.m cf.hdr.Lam cf.hdr.blkP cf.hdr.blkR hL] at h0
  push_cast at h0
  change (cf.hdr.mB : ℝ) * (4 * (cf.hdr.Lam : ℝ) * lamB (Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam
      (cf.hdr.blkP k))) (Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam (cf.hdr.blkR k)))
      (polyR cf.hdr.Lam cf.hdr.HB) (polyR cf.hdr.Lam cf.hdr.ψBa) (polyR cf.hdr.Lam cf.hdr.ψCb)
      ((cf.hdr.cbe : ℝ) / cf.hdr.Lam) u v t) = _
  linear_combination h0

lemma idG_real (hL : 0 < cf.Lam) (hG : cf.chkG = true) (u v t : ℝ) :
    (cf.mG : ℝ) * (30 * cf.Lam * lamG (Sk cf.hdr.K cf.hdr.m cf.hdr.FRm) cf.hdr.HCf cf.hdr.ψCbf
        ((cf.hdr.ef + 2 * Sk cf.hdr.K cf.hdr.m cf.hdr.FPm 1 1 1 + 5 * Sk cf.hdr.K cf.hdr.m cf.hdr.FRm 1 1 1
          - 5 * cf.hdr.calf - 20 * cf.hdr.cbef) / 10) u v t)
      = ((cf.SG.map (tblkRE cf.an cf.ad 1 1)).map fun e => e.ev u v t).sum := by
  have h0 := cf.idG_ev hG u v t
  simp only [idG, idTR, TCert.FG, ev_sub, ev_smul, ev_sumE, TCert.SPE, TCert.SRE,
    ev_lamGE cf.hdr.K cf.hdr.m cf.hdr.Lam cf.hdr.blkP cf.hdr.blkR hL] at h0
  push_cast at h0
  change (cf.hdr.mG : ℝ) * (30 * (cf.hdr.Lam : ℝ) * lamG (Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam
      (cf.hdr.blkR k))) (polyR cf.hdr.Lam cf.hdr.HC) (polyR cf.hdr.Lam cf.hdr.ψCb)
      (((cf.hdr.e : ℝ) / cf.hdr.Lam + 2 * Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam
        (cf.hdr.blkP k)) 1 1 1 + 5 * Sk cf.hdr.K cf.hdr.m (fun k => fmat (cf.hdr.m k) cf.hdr.Lam
        (cf.hdr.blkR k)) 1 1 1 - 5 * ((cf.hdr.cal : ℝ) / cf.hdr.Lam)
        - 20 * ((cf.hdr.cbe : ℝ) / cf.hdr.Lam)) / 10) u v t) = _
  linear_combination h0

lemma wf_of_chk {Fx : Ex} {an : ℤ} {ad : ℕ} {bn : ℤ} {bd : ℕ} {S : List TBlkR}
    (h : hybChkR Fx an ad bn bd S = true) : ∀ s ∈ S, s.wf = true := by
  simp only [hybChkR, Bool.and_eq_true] at h
  exact fun s hs => List.all_eq_true.mp h.1 s hs

end TCertR

/-! ## 5. The family -/

/-- The shape of a reduced SOS block that all objects share: codes, monomials, face basis, rank. -/
def shp (s : TBlkR) : List ℕ × List (ℕ × ℕ × ℕ) × List (List ℤ) × ℕ := (s.g, s.z, s.nb.N, s.nb.r)

/-- Default block (for `getD`). -/
def tbDefault : TBlkR := ⟨[], [], TCertN.nbEmpty, 0⟩

/-- The shape of a kernel block that all objects share: face basis and rank. -/
def shpF (nb : NBlk) : List (List ℤ) × ℕ := (nb.N, nb.r)

section Family

variable {J : ℕ} (cf : Fin J → TCertR) (w : Fin J → ℝ)

/-- Real block matrices of an object, over the common kernel sizes `dd + 1 − k`. -/
noncomputable def FPo (dd : ℕ) (j : Fin J) (k : ℕ) : Matrix (Fin (dd + 1 - k)) (Fin (dd + 1 - k)) ℝ :=
  fmat (dd + 1 - k) (cf j).Lam ((cf j).hdr.blkP k)

noncomputable def FRo (dd : ℕ) (j : Fin J) (k : ℕ) : Matrix (Fin (dd + 1 - k)) (Fin (dd + 1 - k)) ℝ :=
  fmat (dd + 1 - k) (cf j).Lam ((cf j).hdr.blkR k)

/-- The family's kernel blocks `Σ_j w_j F_{k,j}`. -/
noncomputable def FPfam (dd : ℕ) (k : ℕ) : Matrix (Fin (dd + 1 - k)) (Fin (dd + 1 - k)) ℝ :=
  ∑ j, w j • FPo cf dd j k

noncomputable def FRfam (dd : ℕ) (k : ℕ) : Matrix (Fin (dd + 1 - k)) (Fin (dd + 1 - k)) ℝ :=
  ∑ j, w j • FRo cf dd j k

/-- The family's polynomials and constants. -/
noncomputable def HAfam (x : ℝ) : ℝ := ∑ j, w j * (cf j).hdr.HAf x
noncomputable def HBfam (x : ℝ) : ℝ := ∑ j, w j * (cf j).hdr.HBf x
noncomputable def HCfam (x : ℝ) : ℝ := ∑ j, w j * (cf j).hdr.HCf x
noncomputable def ψBafam (x : ℝ) : ℝ := ∑ j, w j * (cf j).hdr.ψBaf x
noncomputable def ψCbfam (x : ℝ) : ℝ := ∑ j, w j * (cf j).hdr.ψCbf x
noncomputable def efam : ℝ := ∑ j, w j * (cf j).hdr.ef
noncomputable def calfam : ℝ := ∑ j, w j * (cf j).hdr.calf
noncomputable def cbefam : ℝ := ∑ j, w j * (cf j).hdr.cbef

/-- The weights of the three identities, `w_j / (m_X,j · c_X · Λ_j)` (`c_A = 5`, `c_B = 4`, `c_G = 30`). -/
noncomputable def wA (j : Fin J) : ℝ := w j / ((cf j).mA * 5 * (cf j).Lam)
noncomputable def wB (j : Fin J) : ℝ := w j / ((cf j).mB * 4 * (cf j).Lam)
noncomputable def wG (j : Fin J) : ℝ := w j / ((cf j).mG * 30 * (cf j).Lam)

/-- **The reduced family blocks** whose quadratic forms Step P certifies nonnegative:
`Σ_j (w_j / (m_X,j c_X Λ_j)) · ent(B′_{r,j})` for the `r`-th SOS block of type `X`. -/
noncomputable def redS (S : Fin J → List TBlkR) (wX : Fin J → ℝ) (r : ℕ) (i i' : ℕ) : ℝ :=
  ∑ j, wX j * (((S j).getD r tbDefault).nb.inner.ent ((S j).getD r tbDefault).nb.r i i' : ℝ)

/-- The reduced family kernel blocks `Σ_j (w_j / Λ_j) · ent(B′_{k,j})`. -/
noncomputable def redF (L : Fin J → List NBlk) (r k : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i i' => ∑ j, w j / (cf j).Lam *
    (((L j).getD k TCertN.nbEmpty).inner.ent ((L j).getD k TCertN.nbEmpty).r i i' : ℝ)

/-- Quadratic-form nonnegativity of an `ℕ`-indexed real matrix on `range r`. -/
def QFnonneg (r : ℕ) (R : ℕ → ℕ → ℝ) : Prop :=
  ∀ y : ℕ → ℝ, 0 ≤ ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, y i * R i i' * y i'

/-! ### The SOS side -/

/-- **The family's SOS sum is a sum of `g_r ·` (reduced family forms).** Inputs: every object's list has the shared
shapes `L`; every block is well formed. -/
lemma fam_sos_eq (S : Fin J → List TBlkR) (wX : Fin J → ℝ) (L : List (List ℕ × List (ℕ × ℕ × ℕ) ×
      List (List ℤ) × ℕ)) (hshape : ∀ j, (S j).map shp = L) (hwf : ∀ j, ∀ s ∈ S j, s.wf = true)
    (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (u v t : ℝ) :
    ∑ j, wX j * (((S j).map (tblkRE an ad bn bd)).map fun e => e.ev u v t).sum
      = ∑ r ∈ Finset.range L.length, (gT an ad bn bd (L.getD r (shp tbDefault)).1).ev u v t *
          ∑ i ∈ Finset.range (L.getD r (shp tbDefault)).2.2.2,
            ∑ i' ∈ Finset.range (L.getD r (shp tbDefault)).2.2.2,
              Yv (L.getD r (shp tbDefault)).2.2.1 (L.getD r (shp tbDefault)).2.1 u v t i *
                redS S wX r i i' * Yv (L.getD r (shp tbDefault)).2.2.1 (L.getD r (shp tbDefault)).2.1 u v t i' := by
  -- each object's sum over its blocks, by index
  have hlen : ∀ j, (S j).length = L.length := fun j => by rw [← hshape j, List.length_map]
  have hsh : ∀ j r, shp ((S j).getD r tbDefault) = L.getD r (shp tbDefault) := by
    intro j r
    rw [← hshape j, List.getD_map]
  have hobj : ∀ j, (((S j).map (tblkRE an ad bn bd)).map fun e => e.ev u v t).sum
      = ∑ r ∈ Finset.range L.length, (gT an ad bn bd (L.getD r (shp tbDefault)).1).ev u v t *
          ∑ i ∈ Finset.range (L.getD r (shp tbDefault)).2.2.2,
            ∑ i' ∈ Finset.range (L.getD r (shp tbDefault)).2.2.2,
              Yv (L.getD r (shp tbDefault)).2.2.1 (L.getD r (shp tbDefault)).2.1 u v t i *
                (((S j).getD r tbDefault).nb.inner.ent ((S j).getD r tbDefault).nb.r i i' : ℝ) *
                Yv (L.getD r (shp tbDefault)).2.2.1 (L.getD r (shp tbDefault)).2.1 u v t i' := by
    intro j
    rw [List.map_map, list_sum_map_range _ tbDefault, hlen j]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hmem : (S j).getD r tbDefault ∈ S j := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen j]; exact Finset.mem_range.1 hr)]
      exact List.getElem_mem _
    have hq := qf_tblkR _ (hwf j _ hmem) u v t
    have h1 := hsh j r
    have hg : ((S j).getD r tbDefault).g = (L.getD r (shp tbDefault)).1 := congrArg Prod.fst h1
    have hz : ((S j).getD r tbDefault).z = (L.getD r (shp tbDefault)).2.1 :=
      congrArg (fun p => p.2.1) h1
    have hN : ((S j).getD r tbDefault).nb.N = (L.getD r (shp tbDefault)).2.2.1 :=
      congrArg (fun p => p.2.2.1) h1
    have hr' : ((S j).getD r tbDefault).nb.r = (L.getD r (shp tbDefault)).2.2.2 :=
      congrArg (fun p => p.2.2.2) h1
    rw [← hg, ← hz, ← hN, ← hr']
    simp only [Function.comp_apply, tblkRE, ev_mul]
    rw [hq]
  simp only [hobj, redS, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Nonnegativity of the family's SOS sum on the cut**, from the reduced family forms. -/
lemma fam_sos_nonneg (S : Fin J → List TBlkR) (wX : Fin J → ℝ) (L : List (List ℕ × List (ℕ × ℕ × ℕ) ×
      List (List ℤ) × ℕ)) (hshape : ∀ j, (S j).map shp = L) (hwf : ∀ j, ∀ s ∈ S j, s.wf = true)
    (hpsd : ∀ r < L.length, QFnonneg (L.getD r (shp tbDefault)).2.2.2 (redS S wX r))
    (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) {u v t : ℝ} (hg : GramCut an ad u v t)
    (hb : (bd : ℝ) * u ≤ bn) :
    0 ≤ ∑ j, wX j * (((S j).map (tblkRE an ad bn bd)).map fun e => e.ev u v t).sum := by
  rw [fam_sos_eq S wX L hshape hwf an ad bn bd u v t]
  refine Finset.sum_nonneg fun r hr => mul_nonneg (gT_nonneg an ad bn bd _ hg hb) ?_
  exact hpsd r (Finset.mem_range.1 hr) _

/-! ### The kernel blocks: PSD by congruence -/

/-- `M_{ac} = Σ_{i,i'<r} n_{ai} R_{ii'} n_{ci'}` is PSD when `R` (an `ℕ`-indexed real matrix, PSD on `range r`) is. -/
lemma psd_of_congr (m r : ℕ) (n : ℕ → ℕ → ℝ) (R : ℕ → ℕ → ℝ)
    (hR : (Matrix.of fun i i' : Fin r => R i i').PosSemidef) (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ a c : Fin m, M a c = ∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, n a i * R i i' * n c i') :
    M.PosSemidef := by
  have hsym : ∀ i i', i < r → i' < r → R i i' = R i' i := by
    intro i i' hi hi'
    have := hR.isHermitian.apply ⟨i', hi'⟩ ⟨i, hi⟩
    simpa [Matrix.of_apply] using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun a c => ?_
    simp only [star_trivial, hM]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun i' hi' => ?_
    rw [hsym i' i (Finset.mem_range.1 hi') (Finset.mem_range.1 hi)]
    ring
  · intro x
    set x' : ℕ → ℝ := fun a => if ha : a < m then x ⟨a, ha⟩ else 0 with hx'
    have hx'' : ∀ a : Fin m, x' a = x a := fun a => by simp [hx', a.2]
    set Y : ℕ → ℝ := fun i => ∑ a ∈ Finset.range m, n a i * x' a with hY
    have h1 : star x ⬝ᵥ M *ᵥ x = ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m,
        x' a * (∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, n a i * R i i' * n c i') * x' c := by
      rw [← sum_fin_eq_range m (fun a c => x' a *
        (∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, n a i * R i i' * n c i') * x' c)]
      simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, hM, hx'']
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      ring
    have h2 : (∑ i ∈ Finset.range r, ∑ i' ∈ Finset.range r, Y i * R i i' * Y i')
        = star (fun i : Fin r => Y i) ⬝ᵥ (Matrix.of fun i i' : Fin r => R i i') *ᵥ (fun i : Fin r => Y i) := by
      rw [← sum_fin_eq_range r (fun i i' => Y i * R i i' * Y i')]
      simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
      ring
    have h3 := hR.dotProduct_mulVec_nonneg (fun i : Fin r => Y i)
    rw [← h2] at h3
    rw [h1, qf_congr]
    exact h3

/-- The entries of an expanded kernel block of a well-formed `NBlk`, as a congruence. -/
lemma fmat_expand_apply {mk : ℕ} (Lam : ℕ) {nb : NBlk} (hg : nb.Good mk) (a c : Fin mk) :
    fmat mk Lam nb.expand a c = (∑ i ∈ Finset.range nb.r, ∑ i' ∈ Finset.range nb.r,
      (nb.n a i : ℝ) * (nb.inner.ent nb.r i i' : ℝ) * (nb.n c i' : ℝ)) / Lam := by
  simp only [fmat, Matrix.of_apply]
  rw [NBlk.ent_expand hg a.2 c.2, NBlk.cast_eent]

/-- **The family's kernel block `Σ_j w_j F_{k,j}` is PSD** when the reduced family block `Σ_j (w_j/Λ_j) B′_{k,j}` is
(shared face basis `N_k` and rank `rr`; `L j` is the object's list of reduced kernel blocks). -/
lemma famF_psd (mk k : ℕ) (L : Fin J → List NBlk) (NN : List (List ℤ)) (rr : ℕ)
    (hsh : ∀ j, shpF ((L j).getD k TCertN.nbEmpty) = (NN, rr))
    (hgood : ∀ j, ((L j).getD k TCertN.nbEmpty).Good mk)
    (hR : (redF cf w L rr k).PosSemidef)
    (F : Fin J → Matrix (Fin mk) (Fin mk) ℝ)
    (hF : ∀ j, F j = fmat mk (cf j).Lam ((L j).getD k TCertN.nbEmpty).expand) :
    (∑ j, w j • F j).PosSemidef := by
  have hN : ∀ j, ((L j).getD k TCertN.nbEmpty).N = NN := fun j => by
    have := hsh j; simp only [shpF, Prod.mk.injEq] at this; exact this.1
  have hr : ∀ j, ((L j).getD k TCertN.nbEmpty).r = rr := fun j => by
    have := hsh j; simp only [shpF, Prod.mk.injEq] at this; exact this.2
  refine psd_of_congr mk rr (fun a i => (((NN.getD a []).getD i 0 : ℤ) : ℝ))
    (fun i i' => ∑ j, w j / (cf j).Lam *
      (((L j).getD k TCertN.nbEmpty).inner.ent ((L j).getD k TCertN.nbEmpty).r i i' : ℝ)) hR _ ?_
  intro a c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hF, fmat_expand_apply _ (hgood _)]
  rw [← fam_swap Finset.univ rr (fun j => w j / (cf j).Lam) (fun i => (((NN.getD a []).getD i 0 : ℤ) : ℝ))
    (fun i' => (((NN.getD c []).getD i' 0 : ℤ) : ℝ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [NBlk.n, hN j, hr j]
  ring

/-! ### The typed bound for the family -/

lemma Sk_dd (c : TCert) {dd : ℕ} (h : c.dd = dd) (bl : ℕ → Blk) :
    Sk (dd + 1) (fun k => dd + 1 - k) (fun k => fmat (dd + 1 - k) c.Lam (bl k))
      = Sk c.K c.m (fun k => fmat (c.m k) c.Lam (bl k)) := by
  subst h; rfl

lemma lin5 {ι : Type*} [DecidableEq ι] (s : Finset ι) (w e P R c b : ι → ℝ) :
    ((∑ i ∈ s, w i * e i) + 2 * (∑ i ∈ s, w i * P i) + 5 * (∑ i ∈ s, w i * R i)
        - 5 * (∑ i ∈ s, w i * c i) - 20 * (∑ i ∈ s, w i * b i)) / 10
      = ∑ i ∈ s, w i * ((e i + 2 * P i + 5 * R i - 5 * c i - 20 * b i) / 10) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    rw [← ih]
    ring

/-- The shared data of the objects of a family. -/
structure Shared (dd : ℕ) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ)
    (LA LB LG : List (List ℕ × List (ℕ × ℕ × ℕ) × List (List ℤ) × ℕ)) (LP LR : List (List (List ℤ) × ℕ))
    (c : TCertR) : Prop where
  dd : c.dd = dd
  an : c.an = an
  ad : c.ad = ad
  bn : c.bn = bn
  bd : c.bd = bd
  SA : c.SA.map shp = LA
  SB : c.SB.map shp = LB
  SG : c.SG.map shp = LG
  FP : c.FP.map shpF = LP
  FR : c.FR.map shpF = LR

lemma checkPos_parts (c : TCertR) (h : c.checkPos = true) :
    0 < c.Lam ∧ 0 < c.ad ∧ 0 < c.bd ∧ 0 < c.mA ∧ 0 < c.mB ∧ 0 < c.mG := by
  simp only [TCertR.checkPos, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

lemma blkP_eq' (c : TCertR) {k : ℕ} (hk : k < c.dd + 1) :
    c.hdr.blkP k = (c.FP.getD k TCertN.nbEmpty).expand :=
  TCertN.blkP_eq c.toN hk

lemma blkR_eq' (c : TCertR) {k : ℕ} (hk : k < c.dd + 1) :
    c.hdr.blkR k = (c.FR.getD k TCertN.nbEmpty).expand :=
  TCertN.blkR_eq c.toN hk

section Bound

variable {dd : ℕ} {an : ℤ} {ad : ℕ} {bn : ℤ} {bd : ℕ}
  {LA LB LG : List (List ℕ × List (ℕ × ℕ × ℕ) × List (List ℤ) × ℕ)} {LP LR : List (List (List ℤ) × ℕ)}

/-- The family's kernel blocks are PSD. -/
lemma famP_psd (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j))
    (hgP : ∀ k < dd + 1, ((LP.getD k (shpF TCertN.nbEmpty)).1.all fun row =>
      decide (row.length ≤ (LP.getD k (shpF TCertN.nbEmpty)).2)) = true ∧
      dd + 1 - k ≤ (LP.getD k (shpF TCertN.nbEmpty)).1.length)
    (hPF : ∀ k < dd + 1,
      (redF cf w (fun j => (cf j).FP) (LP.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef) :
    ∀ k, k < dd + 1 → (FPfam cf w dd k).PosSemidef := by
  intro k hk
  have hsj : ∀ j, shpF ((cf j).FP.getD k TCertN.nbEmpty) = LP.getD k (shpF TCertN.nbEmpty) := by
    intro j; rw [← (hsh j).FP, List.getD_map]
  refine famF_psd cf w (dd + 1 - k) k (fun j => (cf j).FP) (LP.getD k (shpF TCertN.nbEmpty)).1
    (LP.getD k (shpF TCertN.nbEmpty)).2 hsj ?_ (hPF k hk) (fun j => FPo cf dd j k) ?_
  · intro j
    have hN : ((cf j).FP.getD k TCertN.nbEmpty).N = (LP.getD k (shpF TCertN.nbEmpty)).1 :=
      congrArg Prod.fst (hsj j)
    have hr : ((cf j).FP.getD k TCertN.nbEmpty).r = (LP.getD k (shpF TCertN.nbEmpty)).2 :=
      congrArg Prod.snd (hsj j)
    obtain ⟨hrows, hlen⟩ := hgP k hk
    refine ⟨fun row hrow => ?_, ?_⟩
    · rw [hN] at hrow
      rw [hr]
      simpa using List.all_eq_true.mp hrows row hrow
    · rw [hN]; exact hlen
  · intro j
    simp only [FPo]
    rw [blkP_eq' (cf j) (by rw [(hsh j).dd]; exact hk)]

lemma famR_psd (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j))
    (hgR : ∀ k < dd + 1, ((LR.getD k (shpF TCertN.nbEmpty)).1.all fun row =>
      decide (row.length ≤ (LR.getD k (shpF TCertN.nbEmpty)).2)) = true ∧
      dd + 1 - k ≤ (LR.getD k (shpF TCertN.nbEmpty)).1.length)
    (hRF : ∀ k < dd + 1,
      (redF cf w (fun j => (cf j).FR) (LR.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef) :
    ∀ k, k < dd + 1 → (FRfam cf w dd k).PosSemidef := by
  intro k hk
  have hsj : ∀ j, shpF ((cf j).FR.getD k TCertN.nbEmpty) = LR.getD k (shpF TCertN.nbEmpty) := by
    intro j; rw [← (hsh j).FR, List.getD_map]
  refine famF_psd cf w (dd + 1 - k) k (fun j => (cf j).FR) (LR.getD k (shpF TCertN.nbEmpty)).1
    (LR.getD k (shpF TCertN.nbEmpty)).2 hsj ?_ (hRF k hk) (fun j => FRo cf dd j k) ?_
  · intro j
    have hN : ((cf j).FR.getD k TCertN.nbEmpty).N = (LR.getD k (shpF TCertN.nbEmpty)).1 :=
      congrArg Prod.fst (hsj j)
    have hr : ((cf j).FR.getD k TCertN.nbEmpty).r = (LR.getD k (shpF TCertN.nbEmpty)).2 :=
      congrArg Prod.snd (hsj j)
    obtain ⟨hrows, hlen⟩ := hgR k hk
    refine ⟨fun row hrow => ?_, ?_⟩
    · rw [hN] at hrow
      rw [hr]
      simpa using List.all_eq_true.mp hrows row hrow
    · rw [hN]; exact hlen
  · intro j
    simp only [FRo]
    rw [blkR_eq' (cf j) (by rw [(hsh j).dd]; exact hk)]

lemma Sk_FPo (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j)) (j : Fin J) :
    Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j) = Sk (cf j).hdr.K (cf j).hdr.m (cf j).hdr.FPm :=
  Sk_dd (cf j).hdr (hsh j).dd (cf j).hdr.blkP

lemma Sk_FRo (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j)) (j : Fin J) :
    Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) = Sk (cf j).hdr.K (cf j).hdr.m (cf j).hdr.FRm :=
  Sk_dd (cf j).hdr (hsh j).dd (cf j).hdr.blkR

lemma Sk_FPfam (u v t : ℝ) : Sk (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd) u v t
    = ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j) u v t :=
  Sk_fsum (dd + 1) (fun k => dd + 1 - k) Finset.univ w (fun j => FPo cf dd j) u v t

lemma Sk_FRfam (u v t : ℝ) : Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd) u v t
    = ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) u v t :=
  Sk_fsum (dd + 1) (fun k => dd + 1 - k) Finset.univ w (fun j => FRo cf dd j) u v t

/-- **α-slack of the family is nonnegative on the cap cut.** -/
lemma famA_nonneg (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j))
    (hpos : ∀ j, (cf j).checkPos = true) (hA : ∀ j, (cf j).chkA = true)
    (hPA : ∀ r < LA.length, QFnonneg (LA.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (cf j).SA) (wA cf w) r))
    (had : 0 < ad) {u v t : ℝ} (hg : GramOK u v t) (hu : (an : ℝ) / ad ≤ u) (hu' : u ≤ (bn : ℝ) / bd)
    (hbd : 0 < bd) (hv : (an : ℝ) / ad ≤ v) (ht : (an : ℝ) / ad ≤ t) :
    0 ≤ lamA (Sk (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd))
      (Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd)) (HAfam cf w) (ψBafam cf w) (calfam cf w) u v t := by
  have hgc := TCert.gramCut_of_le' an ad had hg hu hv ht
  have hb : (bd : ℝ) * u ≤ bn := by
    have hbd' : (0 : ℝ) < bd := by exact_mod_cast hbd
    have := (le_div_iff₀ hbd').1 hu'
    linarith
  have e1 : Sk (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd)
      = fun a b c => ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j) a b c :=
    funext fun a => funext fun b => funext fun c => Sk_FPfam cf w a b c
  have e2 : Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd)
      = fun a b c => ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) a b c :=
    funext fun a => funext fun b => funext fun c => Sk_FRfam cf w a b c
  rw [e1, e2]
  change 0 ≤ lamA _ _ (fun x => ∑ j, w j * (cf j).hdr.HAf x) (fun x => ∑ j, w j * (cf j).hdr.ψBaf x)
    (∑ j, w j * (cf j).hdr.calf) u v t
  rw [lamA_fsum]
  have key : ∀ j, w j * lamA (Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j))
      (Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j)) (cf j).hdr.HAf (cf j).hdr.ψBaf (cf j).hdr.calf u v t
      = wA cf w j * ((((cf j).SA.map (tblkRE an ad bn bd)).map fun e => e.ev u v t).sum) := by
    intro j
    obtain ⟨hL, -, -, hmA, -, -⟩ := checkPos_parts (cf j) (hpos j)
    have hid := (cf j).idA_real hL (hA j) u v t
    rw [(hsh j).an, (hsh j).ad, (hsh j).bn, (hsh j).bd] at hid
    rw [Sk_FPo cf hsh j, Sk_FRo cf hsh j, wA, ← hid]
    have hL' : (0 : ℝ) < (cf j).Lam := by exact_mod_cast hL
    have hm' : (0 : ℝ) < (cf j).mA := by exact_mod_cast hmA
    field_simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  exact fam_sos_nonneg (fun j => (cf j).SA) (wA cf w) LA (fun j => (hsh j).SA)
    (fun j => TCertR.wf_of_chk (hA j)) hPA an ad bn bd hgc hb

/-- **β-slack of the family is nonnegative on the cut.** -/
lemma famB_nonneg (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j))
    (hpos : ∀ j, (cf j).checkPos = true) (hB : ∀ j, (cf j).chkB = true)
    (hPB : ∀ r < LB.length, QFnonneg (LB.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (cf j).SB) (wB cf w) r))
    (had : 0 < ad) {u v t : ℝ} (hg : GramOK u v t) (hu : (an : ℝ) / ad ≤ u)
    (hv : (an : ℝ) / ad ≤ v) (ht : (an : ℝ) / ad ≤ t) :
    0 ≤ lamB (Sk (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd))
      (Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd)) (HBfam cf w) (ψBafam cf w) (ψCbfam cf w)
      (cbefam cf w) u v t := by
  have hgc := TCert.gramCut_of_le' an ad had hg hu hv ht
  have hb : ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) := by
    have := TCert.le_one_of_gramOK hg
    simpa using this
  have e1 : Sk (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd)
      = fun a b c => ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j) a b c :=
    funext fun a => funext fun b => funext fun c => Sk_FPfam cf w a b c
  have e2 : Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd)
      = fun a b c => ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) a b c :=
    funext fun a => funext fun b => funext fun c => Sk_FRfam cf w a b c
  rw [e1, e2]
  change 0 ≤ lamB _ _ (fun x => ∑ j, w j * (cf j).hdr.HBf x) (fun x => ∑ j, w j * (cf j).hdr.ψBaf x)
    (fun x => ∑ j, w j * (cf j).hdr.ψCbf x) (∑ j, w j * (cf j).hdr.cbef) u v t
  rw [lamB_fsum]
  have key : ∀ j, w j * lamB (Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j))
      (Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j)) (cf j).hdr.HBf (cf j).hdr.ψBaf (cf j).hdr.ψCbf
      (cf j).hdr.cbef u v t
      = wB cf w j * ((((cf j).SB.map (tblkRE an ad 1 1)).map fun e => e.ev u v t).sum) := by
    intro j
    obtain ⟨hL, -, -, -, hmB, -⟩ := checkPos_parts (cf j) (hpos j)
    have hid := (cf j).idB_real hL (hB j) u v t
    rw [(hsh j).an, (hsh j).ad] at hid
    rw [Sk_FPo cf hsh j, Sk_FRo cf hsh j, wB, ← hid]
    have hL' : (0 : ℝ) < (cf j).Lam := by exact_mod_cast hL
    have hm' : (0 : ℝ) < (cf j).mB := by exact_mod_cast hmB
    field_simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  exact fam_sos_nonneg (fun j => (cf j).SB) (wB cf w) LB (fun j => (hsh j).SB)
    (fun j => TCertR.wf_of_chk (hB j)) hPB an ad 1 1 hgc hb

/-- **γ-slack of the family is nonnegative on the cut.** -/
lemma famG_nonneg (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j))
    (hpos : ∀ j, (cf j).checkPos = true) (hG : ∀ j, (cf j).chkG = true)
    (hPG : ∀ r < LG.length, QFnonneg (LG.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (cf j).SG) (wG cf w) r))
    (had : 0 < ad) {u v t : ℝ} (hg : GramOK u v t) (hu : (an : ℝ) / ad ≤ u)
    (hv : (an : ℝ) / ad ≤ v) (ht : (an : ℝ) / ad ≤ t) :
    0 ≤ lamG (Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd)) (HCfam cf w) (ψCbfam cf w)
      ((efam cf w + 2 * Sk (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd) 1 1 1
        + 5 * Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd) 1 1 1
        - 5 * calfam cf w - 20 * cbefam cf w) / 10) u v t := by
  have hgc := TCert.gramCut_of_le' an ad had hg hu hv ht
  have hb : ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) := by
    have := TCert.le_one_of_gramOK hg
    simpa using this
  rw [Sk_FPfam cf w 1 1 1, Sk_FRfam cf w 1 1 1]
  have e2 : Sk (dd + 1) (fun k => dd + 1 - k) (FRfam cf w dd)
      = fun a b c => ∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) a b c :=
    funext fun a => funext fun b => funext fun c => Sk_FRfam cf w a b c
  rw [e2]
  change 0 ≤ lamG _ (fun x => ∑ j, w j * (cf j).hdr.HCf x) (fun x => ∑ j, w j * (cf j).hdr.ψCbf x)
    (((∑ j, w j * (cf j).hdr.ef) + 2 * (∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j) 1 1 1)
      + 5 * (∑ j, w j * Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) 1 1 1)
      - 5 * (∑ j, w j * (cf j).hdr.calf) - 20 * (∑ j, w j * (cf j).hdr.cbef)) / 10) u v t
  rw [lin5, lamG_fsum]
  have key : ∀ j, w j * lamG (Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j)) (cf j).hdr.HCf
      (cf j).hdr.ψCbf (((cf j).hdr.ef + 2 * Sk (dd + 1) (fun k => dd + 1 - k) (FPo cf dd j) 1 1 1
        + 5 * Sk (dd + 1) (fun k => dd + 1 - k) (FRo cf dd j) 1 1 1 - 5 * (cf j).hdr.calf
        - 20 * (cf j).hdr.cbef) / 10) u v t
      = wG cf w j * ((((cf j).SG.map (tblkRE an ad 1 1)).map fun e => e.ev u v t).sum) := by
    intro j
    obtain ⟨hL, -, -, -, -, hmG⟩ := checkPos_parts (cf j) (hpos j)
    have hid := (cf j).idG_real hL (hG j) u v t
    rw [(hsh j).an, (hsh j).ad] at hid
    rw [Sk_FPo cf hsh j, Sk_FRo cf hsh j, wG, ← hid]
    have hL' : (0 : ℝ) < (cf j).Lam := by exact_mod_cast hL
    have hm' : (0 : ℝ) < (cf j).mG := by exact_mod_cast hmG
    field_simp
  rw [Finset.sum_congr rfl fun j _ => key j]
  exact fam_sos_nonneg (fun j => (cf j).SG) (wG cf w) LG (fun j => (hsh j).SG)
    (fun j => TCertR.wf_of_chk (hG j)) hPG an ad 1 1 hgc hb

end Bound

end Family

/-! ## 6. The bridge -/

open ThomsonGen ThomsonN7.Base in
/-- **`capSharp_of_family`.** Real weights `w` on `J` cap objects that share the cut `[an/ad, bn/bd]` with
`an/ad = −1`, the degrees and all face/monomial/multiplier data, whose kernel identities hold
(`chkA/B/G`, `checkPos`), whose reduced family blocks are PSD (kernel blocks) resp. have nonnegative quadratic forms
(SOS blocks), give the sharp cap specification for any kernel `φ` once `E_φ(P) ≤ e(family)` and the three
minorant facts with exact contacts hold for the family polynomials. -/
theorem capSharp_of_family (φ : ℝ → ℝ) {J : ℕ} (cf : Fin J → TCertR) (w : Fin J → ℝ)
    {dd : ℕ} {an : ℤ} {ad : ℕ} {bn : ℤ} {bd : ℕ}
    {LA LB LG : List (List ℕ × List (ℕ × ℕ × ℕ) × List (List ℤ) × ℕ)} {LP LR : List (List (List ℤ) × ℕ)}
    (hsh : ∀ j, Shared dd an ad bn bd LA LB LG LP LR (cf j))
    (hpos : ∀ j, (cf j).checkPos = true)
    (hA : ∀ j, (cf j).chkA = true) (hB : ∀ j, (cf j).chkB = true) (hG : ∀ j, (cf j).chkG = true)
    (had : 0 < ad) (hbd : 0 < bd) (hlo : (an : ℝ) / ad = -1)
    (hgP : ∀ k < dd + 1, ((LP.getD k (shpF TCertN.nbEmpty)).1.all fun row =>
      decide (row.length ≤ (LP.getD k (shpF TCertN.nbEmpty)).2)) = true ∧
      dd + 1 - k ≤ (LP.getD k (shpF TCertN.nbEmpty)).1.length)
    (hgR : ∀ k < dd + 1, ((LR.getD k (shpF TCertN.nbEmpty)).1.all fun row =>
      decide (row.length ≤ (LR.getD k (shpF TCertN.nbEmpty)).2)) = true ∧
      dd + 1 - k ≤ (LR.getD k (shpF TCertN.nbEmpty)).1.length)
    (hPF : ∀ k < dd + 1,
      (redF cf w (fun j => (cf j).FP) (LP.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hRF : ∀ k < dd + 1,
      (redF cf w (fun j => (cf j).FR) (LR.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hPA : ∀ r < LA.length, QFnonneg (LA.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (cf j).SA) (wA cf w) r))
    (hPB : ∀ r < LB.length, QFnonneg (LB.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (cf j).SB) (wB cf w) r))
    (hPG : ∀ r < LG.length, QFnonneg (LG.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (cf j).SG) (wG cf w) r))
    (hE : pairEnergy φ pentBipyramid ≤ efam cf w)
    (hHA : ∀ t, -1 ≤ t → t ≤ (bn : ℝ) / bd →
      HAfam cf w t ≤ φ t ∧ (HAfam cf w t = φ t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 → HBfam cf w t ≤ φ t ∧ (HBfam cf w t = φ t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      HCfam cf w t ≤ φ t ∧ (HCfam cf w t = φ t → t = c1 ∨ t = c2)) :
    CapSpecSharp φ ((bn : ℝ) / bd) := by
  refine ⟨HAfam cf w, HBfam cf w, HCfam cf w, fun y hy hle _ => hE.trans ?_, hHA, hHB, hHC⟩
  have hu1 : ∀ i j, -1 ≤ inner ℝ (y i) (y j) := fun i j => neg_one_le_inner_of_unit (hy.1 i) (hy.1 j)
  refine typed7_cls3_lo (dd + 1) (fun k => dd + 1 - k) (FPfam cf w dd) (FRfam cf w dd)
    (famP_psd cf w hsh hgP hPF) (famR_psd cf w hsh hgR hRF) (HAfam cf w) (HBfam cf w) (HCfam cf w)
    (ψBafam cf w) (ψCbfam cf w) (efam cf w) (calfam cf w) (cbefam cf w) (-1) ((bn : ℝ) / bd) (-1)
    ?_ ?_ ?_ y hy (hu1 0 1) hle (fun i j _ => hu1 i j)
  · intro u v t hg hu hu' hv ht
    exact famA_nonneg cf w hsh hpos hA hPA had hg (by rw [hlo]; exact hu) hu' hbd (by rw [hlo]; exact hv)
      (by rw [hlo]; exact ht)
  · intro u v t hg hu hv ht
    exact famB_nonneg cf w hsh hpos hB hPB had hg (by rw [hlo]; exact hu) (by rw [hlo]; exact hv)
      (by rw [hlo]; exact ht)
  · intro u v t hg hu hv ht
    exact famG_nonneg cf w hsh hpos hG hPG had hg (by rw [hlo]; exact hu) (by rw [hlo]; exact hv)
      (by rw [hlo]; exact ht)

end ThomsonN7.Cert.CapR
