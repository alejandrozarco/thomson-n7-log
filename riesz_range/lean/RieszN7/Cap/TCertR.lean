import ThomsonGen.Cert.NBlk

/-!
# `TCertR`: identity checks of facially reduced typed certificates without expansion (LEAN_PLAN_range.md §3.2.1, F1)

A cap object of the s-range family (24 nodes, 7 pin-response directions) is a facially reduced typed certificate:
every SOS block is `N · B′ · Nᵀ` with an integer basis `N` (`m × r`, shared by all objects) and a reduced block
`B′` (`r × r`, packed `LDLᵀ + Δ`).  For the family route only the three **identities** of each object are needed
(PSD is certified per piece for the interpolated family, §3.2.2), so this module checks

    mA · 5Λ · lamA  =  Σ_r gT_r · zᵀ (N_r ent(B′_r) N_rᵀ) z        (and the B, G analogues)

by upstream's hybrid Kronecker method (`hybChk`), with the quadratic form of every expanded block evaluated on the
**reduced side**: at the Kronecker point `P_a = 2^(w · code_a)`,

    Pᵀ (N E Nᵀ) P = yᵀ E y = Σ_q d_q (l_q · y)² + yᵀ Δ y,      y = Nᵀ P   (`fqRed`, `fqRed_spec`).

The kernel never forms `N E Nᵀ` (`NBlk.expandΔ`); the block polynomial `sqfF nb.expand z` occurs only in proofs.
The analytic `ℓ¹` bound of the identity needs a bound on the expanded entries: `|(N E Nᵀ)_{ac}| ≤ nL² · entB`
with `nL` a stored bound on the row `ℓ¹` norms of `N` (checked by `wf`) and `entB` the bound on `|E_ij|` implied by
the packed field widths (`ent_natAbs_le`, `expandΔ_natAbs_le`).

* `hybChkR`, `hybChkR_sound`: upstream `hybChk`/`hybChk_sound` over `TBlkR` (same Kronecker width/degree recipe,
  same `Ex.ev_eq_zero_of_kev`).
* `TCertR`: upstream `TCert` fields with `NBlk` F-blocks (expanded by the kernel: m ≤ 7) and `TBlkR` SOS blocks;
  `hdr` is the expanded F-part as an upstream `TCert` with empty SOS lists, so `hdr.FA/FB/FG` and the upstream
  evaluation lemmas (`ev_lamAE`, …) apply verbatim; `idA_ev`/`idB_ev`/`idG_ev` are the real identities.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`hybChkR` ← `Cert.hybChk`, `hybChkR_sound` ← `Cert.hybChk_sound`, `TBlkR.l1_le` ← `Cert.TBlk.l1_le`,
`TCertR.idA_ev` ← `Cert.TCert.idA_ev`.  Private working module (2026-11-07), AI-written, not reviewed.
-/

open Real

namespace ThomsonN7

open Kron Kron.Ex

namespace Cert

open ThreePoint

namespace CapR

/-! ## Elementary bounds -/

lemma natAbs_getD_le {l : List ℤ} {M : ℕ} (h : ∀ x ∈ l, x.natAbs ≤ M) (i : ℕ) :
    (l.getD i 0).natAbs ≤ M := by
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; simp

lemma natAbs_getD2_le {L : List (List ℤ)} {M : ℕ} (h : ∀ row ∈ L, ∀ x ∈ row, x.natAbs ≤ M)
    (q i : ℕ) : ((L.getD q []).getD i 0).natAbs ≤ M := by
  rcases lt_or_ge q L.length with hq | hq
  · rw [List.getD_eq_getElem _ _ hq]; exact natAbs_getD_le (h _ (List.getElem_mem hq)) i
  · rw [List.getD_eq_default _ _ hq]; simp

lemma abs_getD_le {l : List ℤ} {M : ℕ} (h : ∀ x ∈ l, x.natAbs ≤ M) (i : ℕ) :
    |l.getD i 0| ≤ (M : ℤ) := by
  rw [← Int.natCast_natAbs]; exact_mod_cast natAbs_getD_le h i

lemma abs_getD2_le {L : List (List ℤ)} {M : ℕ} (h : ∀ row ∈ L, ∀ x ∈ row, x.natAbs ≤ M)
    (q i : ℕ) : |(L.getD q []).getD i 0| ≤ (M : ℤ) := by
  rw [← Int.natCast_natAbs]; exact_mod_cast natAbs_getD2_le h q i

/-- `Σ_{i<r} |l_i| ≤ Σ |l|` (missing entries count as `0`). -/
lemma sum_abs_getD_le : ∀ (l : List ℤ) (r : ℕ),
    ∑ i ∈ Finset.range r, |l.getD i 0| ≤ (l.map fun x : ℤ => |x|).sum
  | [], r => by simp
  | a :: as, 0 => by
    simp only [Finset.range_zero, Finset.sum_empty, List.map_cons, List.sum_cons]
    exact add_nonneg (abs_nonneg a) (List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg y)
  | a :: as, r + 1 => by
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    have := sum_abs_getD_le as r
    linarith

lemma natAbs_sum_cast : ∀ (l : List ℤ), (((l.map Int.natAbs).sum : ℕ) : ℤ) = (l.map fun x : ℤ => |x|).sum
  | [] => by simp
  | a :: as => by
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add, Int.natCast_natAbs, natAbs_sum_cast as]

/-! ## The bound on the entries of `ent(B′)` -/

/-- Bound on `|ent(B′)_{ij}|` from the packed field widths. -/
def entB (nb : NBlk) : ℕ := nb.r * (2 ^ (nb.Bd - 1) * (2 ^ (nb.Bl - 1) * 2 ^ (nb.Bl - 1))) + 2 ^ (nb.BD - 1)

lemma ent_abs_le (nb : NBlk) (hd : 0 < nb.Bd) (hl : 0 < nb.Bl) (hD : 0 < nb.BD) (i j : ℕ) :
    |nb.inner.ent nb.r i j| ≤ (entB nb : ℤ) := by
  have Hd : ∀ x ∈ nb.inner.d, x.natAbs ≤ 2 ^ (nb.Bd - 1) := unpackI_natAbs_le nb.Bd hd _ _
  have Hl : ∀ row ∈ nb.inner.l, ∀ x ∈ row, x.natAbs ≤ 2 ^ (nb.Bl - 1) :=
    unpackM_natAbs_le nb.Bl nb.r hl _ _
  have HD : ∀ row ∈ nb.inner.Δ, ∀ x ∈ row, x.natAbs ≤ 2 ^ (nb.BD - 1) :=
    unpackM_natAbs_le nb.BD nb.r hD _ _
  unfold Blk.ent
  rw [Blk.list_sum_range_map]
  refine (abs_add_le _ _).trans ?_
  unfold entB
  push_cast
  refine add_le_add ?_ (abs_getD2_le HD i j)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ Finset.range nb.r, |nb.inner.dq q * nb.inner.lq q i * nb.inner.lq q j|
      ≤ (2 : ℤ) ^ (nb.Bd - 1) * ((2 : ℤ) ^ (nb.Bl - 1) * (2 : ℤ) ^ (nb.Bl - 1)) := by
    intro q _
    rw [abs_mul, abs_mul, mul_assoc]
    have h1 := abs_getD_le Hd q
    have h2 := abs_getD2_le Hl q i
    have h3 := abs_getD2_le Hl q j
    push_cast at h1 h2 h3
    exact mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity)) (by positivity)
      (by positivity)
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-! ## Typed SOS blocks given only by their reduced data -/

/-- A typed SOS block: multiplier codes `g`, monomial basis `z`, facially reduced Gram block `nb`, and a bound
`nL` on the `ℓ¹` norms of the rows of `nb.N`. -/
structure TBlkR where
  g : List ℕ
  z : List (ℕ × ℕ × ℕ)
  nb : NBlk
  nL : ℕ

namespace TBlkR

/-- Well-formedness: positive widths, one row of `N` per monomial, rows of length `≤ r` and `ℓ¹` norm `≤ nL`. -/
def wf (s : TBlkR) : Bool :=
  decide (0 < s.nb.Bd) && decide (0 < s.nb.Bl) && decide (0 < s.nb.BD) &&
    decide (s.nb.N.length = s.z.length) &&
    s.nb.N.all (fun row => decide (row.length ≤ s.nb.r) && decide ((row.map Int.natAbs).sum ≤ s.nL))

/-- Bound on the entries of the expanded remainder `N ent(B′) Nᵀ`. -/
def MD (s : TBlkR) : ℕ := s.nL * s.nL * entB s.nb

/-- Analytic bound on the `ℓ¹` norm of the quadratic form of the expanded block. -/
def l1B (s : TBlkR) : ℕ := s.z.length * (s.z.length * s.MD)

lemma wf_parts {s : TBlkR} (h : s.wf = true) :
    0 < s.nb.Bd ∧ 0 < s.nb.Bl ∧ 0 < s.nb.BD ∧ s.nb.N.length = s.z.length ∧
      (∀ row ∈ s.nb.N, row.length ≤ s.nb.r) ∧
      (∀ row ∈ s.nb.N, (row.map Int.natAbs).sum ≤ s.nL) := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun row hr => (h5 row hr).1, fun row hr => (h5 row hr).2⟩

/-- **Entries of the kernel-free expansion are bounded by `nL² · entB`.** -/
lemma expandΔ_natAbs_le {s : TBlkR} (h : s.wf = true) :
    ∀ row ∈ s.nb.expand.Δ, ∀ x ∈ row, x.natAbs ≤ s.MD := by
  obtain ⟨hd, hl, hD, -, hN, hL⟩ := wf_parts h
  intro row hrow x hx
  simp only [NBlk.expand, NBlk.expandΔ, NBlk.matMulT, NBlk.matMul, List.map_map, List.mem_map,
    Function.comp_apply] at hrow
  obtain ⟨ra, hra, rfl⟩ := hrow
  simp only [List.mem_map] at hx
  obtain ⟨rc, hrc, rfl⟩ := hx
  have hE := NBlk.entMat_bounds s.nb
  have hra' := hN ra hra
  have hrc' := hN rc hrc
  -- dot (vecMat ra E) rc as a double sum
  rw [NBlk.dot_eq_sum s.nb.r _ _ (NBlk.length_vecMat_le s.nb.r _ _ hE.2) hrc']
  have key : ∀ j, (NBlk.vecMat ra (NBlk.entMat s.nb.inner)).getD j 0
      = ∑ i ∈ Finset.range s.nb.r, ra.getD i 0 * s.nb.inner.ent s.nb.r i j := by
    intro j
    rw [NBlk.getD_vecMat s.nb.r _ _ hra' hE.1 j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [NBlk.getD_entMat s.nb.r s.nb.inner s.nb.inner_d_length.le s.nb.inner_l_length.le]
  simp only [key]
  have hent := ent_abs_le s.nb hd hl hD
  have hsa := sum_abs_getD_le ra s.nb.r
  have hsc := sum_abs_getD_le rc s.nb.r
  have hLa : (ra.map fun x : ℤ => |x|).sum ≤ (s.nL : ℤ) := by
    rw [← natAbs_sum_cast]; exact_mod_cast hL ra hra
  have hLc : (rc.map fun x : ℤ => |x|).sum ≤ (s.nL : ℤ) := by
    rw [← natAbs_sum_cast]; exact_mod_cast hL rc hrc
  have hbound : |∑ j ∈ Finset.range s.nb.r,
        (∑ i ∈ Finset.range s.nb.r, ra.getD i 0 * s.nb.inner.ent s.nb.r i j) * rc.getD j 0|
      ≤ (s.nL : ℤ) * s.nL * entB s.nb := by
    calc _ ≤ ∑ j ∈ Finset.range s.nb.r,
          (∑ i ∈ Finset.range s.nb.r, |ra.getD i 0| * (entB s.nb : ℤ)) * |rc.getD j 0| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hent i j) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range s.nb.r, |ra.getD i 0|) * (entB s.nb : ℤ)
            * ∑ j ∈ Finset.range s.nb.r, |rc.getD j 0| := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ (s.nL : ℤ) * (entB s.nb : ℤ) * s.nL := by
          have h0 : (0 : ℤ) ≤ ∑ i ∈ Finset.range s.nb.r, |ra.getD i 0| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          have h0' : (0 : ℤ) ≤ ∑ j ∈ Finset.range s.nb.r, |rc.getD j 0| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hE0 : (0 : ℤ) ≤ entB s.nb := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hsa.trans hLa) hE0) (hsc.trans hLc) h0'
            (by positivity)
      _ = _ := by ring
  have : ((∑ j ∈ Finset.range s.nb.r,
        (∑ i ∈ Finset.range s.nb.r, ra.getD i 0 * s.nb.inner.ent s.nb.r i j) * rc.getD j 0).natAbs
        : ℤ) ≤ ((s.MD : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; unfold MD; push_cast; exact hbound
  exact_mod_cast this

lemma l1_le (s : TBlkR) (h : s.wf = true) : (sqfF s.nb.expand s.z).l1 ≤ s.l1B := by
  have := l1_sqfF_le s.nb.expand s.z 0 0 s.MD (by simp [NBlk.expand]) (by simp [NBlk.expand])
    (expandΔ_natAbs_le h)
  unfold l1B
  simpa using this

end TBlkR

/-- The polynomial `g · (zᵀ (N ent(B′) Nᵀ) z)` of a reduced typed block (never evaluated by the kernel). -/
def tblkRE (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (s : TBlkR) : Ex :=
  mul (gT an ad bn bd s.g) (sqfF s.nb.expand s.z)

lemma l1_tblkRE_le (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (s : TBlkR) (h : s.wf = true) :
    (tblkRE an ad bn bd s).l1 ≤ (gT an ad bn bd s.g).l1 * s.l1B := by
  rw [tblkRE, Ex.l1]
  exact Nat.mul_le_mul_left _ (s.l1_le h)

lemma degK_tblkRE_le (k : ℕ) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (s : TBlkR) :
    degK k (tblkRE an ad bn bd s) ≤ degK k (gT an ad bn bd s.g) + 2 * mxs k s.z := by
  rw [tblkRE, degK]
  have := degK_sqfF_le k s.nb.expand s.z
  omega

/-! ## The reduced-side evaluator -/

/-- `Σ_q d_q (l_q · y)²` along the lists `d`, `l`. -/
def sqSum (y : List ℤ) : List ℤ → List (List ℤ) → ℤ
  | dq :: ds, lq :: ls => dq * NBlk.dot lq y * NBlk.dot lq y + sqSum y ds ls
  | _, _ => 0

/-- The reduced quadratic form `yᵀ ent(B′) y`. -/
def qfRed (b : Blk) (y : List ℤ) : ℤ := sqSum y b.d b.l + NBlk.dot (NBlk.vecMat y b.Δ) y

/-- The Kronecker value of the quadratic form of the expanded block, computed on the reduced side:
`y = Nᵀ P` with `P` the Kronecker weights of the monomials. -/
def fqRed (w D : ℕ) (s : TBlkR) : ℤ :=
  qfRed s.nb.inner (NBlk.vecMat ((weights w D s.z).map fun p : ℕ => (p : ℤ)) s.nb.N)

lemma sqSum_eq (y : List ℤ) : ∀ (d : List ℤ) (l : List (List ℤ)) (n : ℕ), d.length ≤ n →
    sqSum y d l = ∑ q ∈ Finset.range n, d.getD q 0 * NBlk.dot (l.getD q []) y
      * NBlk.dot (l.getD q []) y
  | [], l, n, _ => by simp [sqSum]
  | dq :: ds, [], n, _ => by
    simp only [sqSum, List.getD_nil]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [NBlk.dot]
  | dq :: ds, lq :: ls, 0, h => by simp at h
  | dq :: ds, lq :: ls, n + 1, h => by
    rw [Finset.sum_range_succ', sqSum, sqSum_eq y ds ls n (by simp at h; omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- `qfRed` is the reduced quadratic form `Σ_{ij} y_i ent_{ij} y_j`. -/
lemma qfRed_eq (nb : NBlk) (y : List ℤ) (hy : y.length ≤ nb.r) :
    (qfRed nb.inner y : ℝ) = ∑ i ∈ Finset.range nb.r, ∑ j ∈ Finset.range nb.r,
      (y.getD i 0 : ℝ) * (nb.inner.ent nb.r i j : ℝ) * (y.getD j 0 : ℝ) := by
  have hl : ∀ row ∈ nb.inner.l, row.length = nb.r := fun row h =>
    NBlk.mem_unpackM_length _ _ _ _ row h
  have hΔ : ∀ row ∈ nb.inner.Δ, row.length = nb.r := fun row h =>
    NBlk.mem_unpackM_length _ _ _ _ row h
  have hΔl : nb.inner.Δ.length = nb.r := NBlk.length_unpackM _ _ _ _
  have hdot : ∀ q, NBlk.dot (nb.inner.l.getD q []) y
      = ∑ i ∈ Finset.range nb.r, nb.inner.lq q i * y.getD i 0 := by
    intro q
    have hlen : (nb.inner.l.getD q []).length ≤ nb.r := by
      rcases lt_or_ge q nb.inner.l.length with hq | hq
      · rw [List.getD_eq_getElem _ _ hq]; exact (hl _ (List.getElem_mem hq)).le
      · rw [List.getD_eq_default _ _ hq]; simp
    rw [NBlk.dot_eq_sum nb.r _ _ hlen hy]
    rfl
  have hvm : ∀ j, (NBlk.vecMat y nb.inner.Δ).getD j 0
      = ∑ i ∈ Finset.range nb.r, y.getD i 0 * nb.inner.del i j := fun j =>
    NBlk.getD_vecMat nb.r y nb.inner.Δ hy hΔl.le j
  have hvml : (NBlk.vecMat y nb.inner.Δ).length ≤ nb.r :=
    NBlk.length_vecMat_le nb.r _ _ fun row h => (hΔ row h).le
  unfold qfRed
  rw [sqSum_eq y _ _ nb.r nb.inner_d_length.le, NBlk.dot_eq_sum nb.r _ _ hvml hy]
  simp only [hdot, hvm]
  push_cast
  simp only [Blk.ent, Blk.list_sum_range_map]
  push_cast
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · -- the LDLᵀ part
    have lhs : ∀ q, ((nb.inner.dq q : ℤ) : ℝ) *
          (∑ i ∈ Finset.range nb.r, (nb.inner.lq q i : ℝ) * (y.getD i 0 : ℝ)) *
          (∑ i ∈ Finset.range nb.r, (nb.inner.lq q i : ℝ) * (y.getD i 0 : ℝ))
        = ∑ i ∈ Finset.range nb.r, ∑ j ∈ Finset.range nb.r,
            (y.getD i 0 : ℝ) * ((nb.inner.dq q : ℝ) * nb.inner.lq q i * nb.inner.lq q j)
              * (y.getD j 0 : ℝ) := by
      intro q
      rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hd : ∀ q, (nb.inner.dq q : ℝ) = ((nb.inner.d.getD q 0 : ℤ) : ℝ) := fun q => rfl
    simp only [← hd, lhs]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]

lemma getD_mapCast (l : List ℕ) (a : ℕ) : (l.map fun p : ℕ => (p : ℤ)).getD a 0 = ((l.getD a 0 : ℕ) : ℤ) := by
  rcases lt_or_ge a l.length with ha | ha
  · rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getD_eq_getElem _ _ ha]; simp
  · rw [List.getD_eq_default _ _ (by simpa using ha), List.getD_eq_default _ _ ha]; simp

/-- **`fqRed` computes the Kronecker value of the quadratic form of the expanded block.** -/
lemma fqRed_spec (w D : ℕ) (s : TBlkR) (h : s.wf = true) :
    fqRed w D s = (sqfF s.nb.expand s.z).kev w D := by
  obtain ⟨-, -, -, hlen, hN, -⟩ := TBlkR.wf_parts h
  have hg : s.nb.Good s.z.length := ⟨hN, hlen.ge⟩
  apply Int.cast_injective (α := ℝ)
  rw [kev_sqfF, sqfVal]
  -- the expanded side
  have hq0 : ∀ q, s.nb.expand.dq q = 0 := NBlk.dq_expand s.nb
  simp only [hq0, zero_mul, Finset.sum_const_zero, zero_add]
  push_cast
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => by
    rw [NBlk.del_expand hg (Finset.mem_range.1 ha) (Finset.mem_range.1 hc)]]
  have hx := NBlk.qf_eent s.z.length s.nb (fun a => ((kw w D s.z a : ℤ) : ℝ))
  rw [hx]
  -- the reduced side
  set P := (weights w D s.z).map fun p : ℕ => (p : ℤ) with hP
  have hPl : P.length = s.z.length := by simp [hP, weights_length]
  have hPa : ∀ a < s.z.length, P.getD a 0 = kw w D s.z a := by
    intro a ha
    rw [hP, getD_mapCast, getD_weights w D s.z a ha]
  have hy : ∀ i, (NBlk.vecMat P s.nb.N).getD i 0
      = ∑ a ∈ Finset.range s.z.length, kw w D s.z a * s.nb.n a i := by
    intro i
    rw [NBlk.getD_vecMat s.z.length P s.nb.N hPl.le hlen.le i]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hPa a (Finset.mem_range.1 ha)]
    rfl
  have hyl : (NBlk.vecMat P s.nb.N).length ≤ s.nb.r := NBlk.length_vecMat_le _ _ _ hN
  unfold fqRed
  rw [← hP, qfRed_eq s.nb _ hyl]
  simp only [hy]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-! ## The hybrid Kronecker check over reduced blocks -/

/-- The identity tree `Fx − Σ g · Q` (never evaluated by the kernel). -/
def idTR (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : Ex :=
  sub Fx (sumE (S.map (tblkRE an ad bn bd)))

def idLR (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : ℕ :=
  Fx.l1 + (S.map fun s => (gT an ad bn bd s.g).l1 * s.l1B).sum

def idDegR (k : ℕ) (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : ℕ :=
  max (degK k Fx) ((S.map fun s => degK k (gT an ad bn bd s.g) + 2 * mxs k s.z).foldr max 0)

def hybWR (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : ℕ :=
  Nat.log2 (idLR Fx an ad bn bd S) + 1

def hybDR (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : ℕ :=
  max (idDegR 0 Fx an ad bn bd S) (max (idDegR 1 Fx an ad bn bd S) (idDegR 2 Fx an ad bn bd S)) + 1

/-- The Kronecker value of the identity, block forms evaluated on the reduced side. -/
def hybValR (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : ℤ :=
  Fx.kev (hybWR Fx an ad bn bd S) (hybDR Fx an ad bn bd S)
    - (S.map fun s => (gT an ad bn bd s.g).kev (hybWR Fx an ad bn bd S) (hybDR Fx an ad bn bd S)
        * fqRed (hybWR Fx an ad bn bd S) (hybDR Fx an ad bn bd S) s).sum

/-- The hybrid Kronecker check over reduced blocks. -/
def hybChkR (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) : Bool :=
  S.all TBlkR.wf && decide (hybValR Fx an ad bn bd S = 0)

theorem hybChkR_sound (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR)
    (h : hybChkR Fx an ad bn bd S = true) (u v t : ℝ) :
    (idTR Fx an ad bn bd S).ev u v t = 0 := by
  simp only [hybChkR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hwf, hval⟩ := h
  have hwf' : ∀ s ∈ S, s.wf = true := fun s hs => List.all_eq_true.mp hwf s hs
  have hdeg : ∀ k, degK k (idTR Fx an ad bn bd S) ≤ idDegR k Fx an ad bn bd S := by
    intro k
    have h1 : degK k (sumE (S.map (tblkRE an ad bn bd)))
        ≤ (S.map fun s => degK k (gT an ad bn bd s.g) + 2 * mxs k s.z).foldr max 0 :=
      degK_sumE_map k _ _ S fun s _ => degK_tblkRE_le k an ad bn bd s
    rw [idTR, degK_sub, idDegR]
    exact max_le_max le_rfl h1
  have hl1 : (idTR Fx an ad bn bd S).l1 ≤ idLR Fx an ad bn bd S := by
    have h1 : (sumE (S.map (tblkRE an ad bn bd))).l1
        ≤ (S.map fun s => (gT an ad bn bd s.g).l1 * s.l1B).sum :=
      l1_sumE_map _ _ S fun s hs => l1_tblkRE_le an ad bn bd s (hwf' s hs)
    rw [idTR, l1_sub, idLR]
    omega
  have hk : (idTR Fx an ad bn bd S).kev (hybWR Fx an ad bn bd S) (hybDR Fx an ad bn bd S) = 0 := by
    have hmap : (S.map fun s => (tblkRE an ad bn bd s).kev (hybWR Fx an ad bn bd S)
          (hybDR Fx an ad bn bd S))
        = S.map fun s => (gT an ad bn bd s.g).kev (hybWR Fx an ad bn bd S)
            (hybDR Fx an ad bn bd S) * fqRed (hybWR Fx an ad bn bd S) (hybDR Fx an ad bn bd S) s := by
      refine List.map_congr_left fun s hs => ?_
      rw [tblkRE, Ex.kev, fqRed_spec _ _ s (hwf' s hs)]
    rw [idTR, kev_sub, kev_sumE_map, hmap]
    exact hval
  refine Ex.ev_eq_zero_of_kev _ (hybWR Fx an ad bn bd S) (hybDR Fx an ad bn bd S) ?_ ?_ ?_ ?_ hk u v t
  · rw [← degK_zero]
    have := hdeg 0
    simp only [hybDR]
    omega
  · rw [← degK_one]
    have := hdeg 1
    simp only [hybDR]
    omega
  · rw [← degK_two]
    have := hdeg 2
    simp only [hybDR]
    omega
  · exact lt_of_le_of_lt hl1 Nat.lt_log2_self

/-- `hybChkR` from its parts, so that a certificate module can check it with one kernel `decide` per block
(memory: the kernel's caches are per declaration).  Same pattern as `ThomsonGen.Cert.hybChk_of_parts`. -/
theorem hybChkR_of_parts (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkR) (W D : ℕ) (vF : ℤ)
    (vs : List ℤ) (hwf : S.all TBlkR.wf = true)
    (hW : hybWR Fx an ad bn bd S = W) (hD : hybDR Fx an ad bn bd S = D)
    (hF : Fx.kev W D = vF)
    (hS : S.map (fun s => (gT an ad bn bd s.g).kev W D * fqRed W D s) = vs)
    (hsum : vF - vs.sum = 0) : hybChkR Fx an ad bn bd S = true := by
  unfold hybChkR hybValR
  rw [hW, hD, hF, hS, hwf, hsum]
  simp

/-! ## Certificates -/

/-- A cap object: upstream `TCert` fields with facially reduced F-blocks (`NBlk`, expanded by the kernel) and
reduced typed SOS blocks (`TBlkR`, never expanded). -/
structure TCertR where
  dd : ℕ
  Lam : ℕ
  an : ℤ
  ad : ℕ
  bn : ℤ
  bd : ℕ
  e : ℤ
  cal : ℤ
  cbe : ℤ
  HA : List ℤ
  HB : List ℤ
  HC : List ℤ
  ψBa : List ℤ
  ψCb : List ℤ
  FP : List NBlk
  FR : List NBlk
  mA : ℕ
  mB : ℕ
  mG : ℕ
  SA : List TBlkR
  SB : List TBlkR
  SG : List TBlkR

namespace TCertR

variable (cf : TCertR)

/-- The F-part as a facially reduced certificate with no SOS blocks. -/
def toN : TCertN :=
  ⟨cf.dd, cf.Lam, cf.an, cf.ad, cf.bn, cf.bd, cf.e, cf.cal, cf.cbe, cf.HA, cf.HB, cf.HC, cf.ψBa, cf.ψCb,
    cf.FP, cf.FR, cf.mA, cf.mB, cf.mG, [], [], []⟩

/-- The expanded F-part as an upstream `TCert` (empty SOS lists): `hdr.FA/FB/FG` are the left-hand sides of
the three identities. -/
def hdr : TCert := cf.toN.toTCert

def idA : Ex := idTR cf.hdr.FA cf.an cf.ad cf.bn cf.bd cf.SA
def idB : Ex := idTR cf.hdr.FB cf.an cf.ad 1 1 cf.SB
def idG : Ex := idTR cf.hdr.FG cf.an cf.ad 1 1 cf.SG

def chkA : Bool := hybChkR cf.hdr.FA cf.an cf.ad cf.bn cf.bd cf.SA
def chkB : Bool := hybChkR cf.hdr.FB cf.an cf.ad 1 1 cf.SB
def chkG : Bool := hybChkR cf.hdr.FG cf.an cf.ad 1 1 cf.SG

/-- Positivity of the scalings (cheap). -/
def checkPos : Bool :=
  decide (0 < cf.Lam) && decide (0 < cf.ad) && decide (0 < cf.bd) &&
  decide (0 < cf.mA) && decide (0 < cf.mB) && decide (0 < cf.mG) &&
  decide (cf.FP.length = cf.dd + 1) && decide (cf.FR.length = cf.dd + 1)

theorem idA_ev (h : cf.chkA = true) (u v t : ℝ) : cf.idA.ev u v t = 0 :=
  hybChkR_sound _ _ _ _ _ _ h u v t

theorem idB_ev (h : cf.chkB = true) (u v t : ℝ) : cf.idB.ev u v t = 0 :=
  hybChkR_sound _ _ _ _ _ _ h u v t

theorem idG_ev (h : cf.chkG = true) (u v t : ℝ) : cf.idG.ev u v t = 0 :=
  hybChkR_sound _ _ _ _ _ _ h u v t

end TCertR

end CapR
end Cert
end ThomsonN7
