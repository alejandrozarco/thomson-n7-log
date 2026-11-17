import RieszN7.Cap.Family
import RieszN7.Cap.Lit.Base

/-!
# `RieszN7.Cap.LitLink` — the objects' reduced blocks are their light literals (B1, option (b))

A cap object stores every reduced block with zero pivots (`ent = 0 · LDLᵀ + Δ`, the trivial decomposition) and its
remainder literal `xD` defined in the light module `RieszN7/Cap/<Obj>/Lit.lean`.  `nbOK nb b` checks (kernel, cheap:
literal equalities and `r` zero pivots) that the `NBlk` `nb` is the literal record `b`; then
`nb.inner.ent nb.r i j = b.ent i j` for all `i j` (`ent_of_nbOK`, generic, proved once).  `objOK c o` lifts this to a
whole `TCertR` and its `Obj` record (scalings `Λ, m_A, m_B, m_G` and all block lists), and `redS_eq`/`redF_eq` rewrite
the bridge's reduced family blocks (`Cap.Family`) into the literal form used by the Mac-class Step P modules.
Private, AI-written (Phase 2, CAP fork, 2026-11-08), not reviewed.
-/

open Real

namespace RieszN7.CapLit

open ThomsonN7 ThomsonN7.Cert ThomsonN7.Cert.CapR

theorem uI_eq (B : ℕ) : ∀ n x, uI B n x = unpackI B n x
  | 0, _ => rfl
  | n + 1, x => by simp only [uI, unpackI, uI_eq B n]

theorem uM_eq (B cols : ℕ) : ∀ rows x, uM B cols rows x = unpackM B cols rows x
  | 0, _ => rfl
  | rows + 1, x => by simp only [uM, unpackM, uI_eq, uM_eq B cols rows]

/-- The block `nb` is the literal `b`: same size, width and remainder literal, all pivots zero. -/
def nbOK (nb : NBlk) (b : LB) : Bool :=
  nb.r == b.r && nb.BD == b.B && nb.xD == b.x && (unpackI nb.Bd nb.r nb.xd).all (· == 0)

theorem getD_zero_of_all {l : List ℤ} (h : l.all (· == 0) = true) (q : ℕ) : l.getD q 0 = 0 := by
  rcases lt_or_ge q l.length with hq | hq
  · rw [List.getD_eq_getElem _ _ hq]
    have := List.all_eq_true.1 h _ (List.getElem_mem hq)
    simpa using this
  · rw [List.getD_eq_default _ _ hq]

/-- **The link:** a checked block's `ent` is the literal's entry. -/
theorem ent_of_nbOK {nb : NBlk} {b : LB} (h : nbOK nb b = true) (i j : ℕ) :
    nb.inner.ent nb.r i j = b.ent i j := by
  simp only [nbOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hr, hB⟩, hx⟩, hz⟩ := h
  have h0 : ((List.range nb.r).map fun q =>
      nb.inner.dq q * nb.inner.lq q i * nb.inner.lq q j).sum = 0 := by
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hv
    simp only [Blk.dq, NBlk.inner, mkBlk]
    rw [getD_zero_of_all hz q]; ring
  rw [Blk.ent, h0, zero_add]
  simp only [Blk.del, NBlk.inner, mkBlk, LB.ent, LDL.ent, LB.mat_eq, uM_eq, hr, hB, hx]

/-- A list of blocks is the list of literals. -/
def nbsOK : List NBlk → List LB → Bool
  | [], [] => true
  | nb :: L, b :: O => nbOK nb b && nbsOK L O
  | _, _ => false

theorem ent_nbEmpty (i j : ℕ) : TCertN.nbEmpty.inner.ent TCertN.nbEmpty.r i j = 0 := by
  simp [TCertN.nbEmpty, NBlk.inner, mkBlk, Blk.ent, Blk.del, unpackM]

theorem ent_default (i j : ℕ) : (default : LB).ent i j = 0 := by
  show LDL.ent (uMS 1 0 0 0) i j = 0
  simp [uMS, LDL.ent]

theorem ent_of_nbsOK : ∀ (L : List NBlk) (O : List LB), nbsOK L O = true → ∀ k i j,
    (L.getD k TCertN.nbEmpty).inner.ent (L.getD k TCertN.nbEmpty).r i j = (O.getD k default).ent i j
  | [], [], _, k, i, j => by simp only [List.getD_nil]; rw [ent_nbEmpty, ent_default]
  | nb :: L, b :: O, h, k, i, j => by
    simp only [nbsOK, Bool.and_eq_true] at h
    rcases k with _ | k
    · simp only [List.getD_cons_zero]; exact ent_of_nbOK h.1 i j
    · simp only [List.getD_cons_succ]; exact ent_of_nbsOK L O h.2 k i j
  | [], _ :: _, h, _, _, _ => by simp [nbsOK] at h
  | _ :: _, [], h, _, _, _ => by simp [nbsOK] at h

/-- A `TCertR` is the literal record `o`. -/
def objOK (c : TCertR) (o : Obj) : Bool :=
  c.Lam == o.Lam && c.mA == o.mA && c.mB == o.mB && c.mG == o.mG &&
    nbsOK (c.SA.map (·.nb)) o.SA && nbsOK (c.SB.map (·.nb)) o.SB && nbsOK (c.SG.map (·.nb)) o.SG &&
    nbsOK c.FP o.FP && nbsOK c.FR o.FR

structure ObjFacts (c : TCertR) (o : Obj) : Prop where
  Lam : c.Lam = o.Lam
  mA : c.mA = o.mA
  mB : c.mB = o.mB
  mG : c.mG = o.mG
  SA : nbsOK (c.SA.map (·.nb)) o.SA = true
  SB : nbsOK (c.SB.map (·.nb)) o.SB = true
  SG : nbsOK (c.SG.map (·.nb)) o.SG = true
  FP : nbsOK c.FP o.FP = true
  FR : nbsOK c.FR o.FR = true

theorem objFacts {c : TCertR} {o : Obj} (h : objOK c o = true) : ObjFacts c o := by
  simp only [objOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem ent_sos {S : List TBlkR} {O : List LB} (h : nbsOK (S.map (·.nb)) O = true) (k i j : ℕ) :
    (S.getD k tbDefault).nb.inner.ent (S.getD k tbDefault).nb.r i j = (O.getD k default).ent i j := by
  have e : (S.getD k tbDefault).nb = (S.map (·.nb)).getD k TCertN.nbEmpty := by
    rw [show TCertN.nbEmpty = tbDefault.nb from rfl, List.getD_map]
  rw [e]
  exact ent_of_nbsOK _ _ h k i j

/-! ### The bridge's reduced family blocks in literal form -/

/-- `redS` of the bridge, for objects with literal records `o`, as a sum over the literals' entries. -/
theorem redS_eq {J : ℕ} (cf : Fin J → TCertR) (o : Fin J → Obj) (hf : ∀ j, ObjFacts (cf j) (o j)) (w : Fin J → ℝ)
    (r i i' : ℕ) :
    redS (fun j => (cf j).SA) (wA cf w) r i i'
        = ∑ j, w j / ((o j).mA * 5 * (o j).Lam) * (((o j).SA.getD r default).ent i i' : ℝ) ∧
      redS (fun j => (cf j).SB) (wB cf w) r i i'
        = ∑ j, w j / ((o j).mB * 4 * (o j).Lam) * (((o j).SB.getD r default).ent i i' : ℝ) ∧
      redS (fun j => (cf j).SG) (wG cf w) r i i'
        = ∑ j, w j / ((o j).mG * 30 * (o j).Lam) * (((o j).SG.getD r default).ent i i' : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold redS wA
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ent_sos (hf j).SA, (hf j).mA, (hf j).Lam]
  · unfold redS wB
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ent_sos (hf j).SB, (hf j).mB, (hf j).Lam]
  · unfold redS wG
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ent_sos (hf j).SG, (hf j).mG, (hf j).Lam]

/-- `redF` of the bridge in literal form. -/
theorem redF_eq {J : ℕ} (cf : Fin J → TCertR) (o : Fin J → Obj) (hf : ∀ j, ObjFacts (cf j) (o j)) (w : Fin J → ℝ)
    (r k : ℕ) (i i' : Fin r) :
    redF cf w (fun j => (cf j).FP) r k i i'
        = ∑ j, w j / (o j).Lam * (((o j).FP.getD k default).ent i i' : ℝ) ∧
      redF cf w (fun j => (cf j).FR) r k i i'
        = ∑ j, w j / (o j).Lam * (((o j).FR.getD k default).ent i i' : ℝ) := by
  refine ⟨?_, ?_⟩
  · unfold redF
    simp only [Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ent_of_nbsOK _ _ (hf j).FP k i i', (hf j).Lam]
  · unfold redF
    simp only [Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ent_of_nbsOK _ _ (hf j).FR k i i', (hf j).Lam]

end RieszN7.CapLit
