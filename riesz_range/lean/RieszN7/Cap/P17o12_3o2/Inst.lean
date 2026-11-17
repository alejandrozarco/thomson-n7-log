import RieszN7.Cap.Family
import RieszN7.Cap.ERow
import RieszN7.Cap.N17o12.ChkA
import RieszN7.Cap.N17o12.ChkB
import RieszN7.Cap.N17o12.ChkG
import RieszN7.Cap.N17o12.ChkPos
import RieszN7.Cap.N3o2.ChkA
import RieszN7.Cap.N3o2.ChkB
import RieszN7.Cap.N3o2.ChkG
import RieszN7.Cap.N3o2.ChkPos
import RieszN7.Cap.Dir0.ChkA
import RieszN7.Cap.Dir0.ChkB
import RieszN7.Cap.Dir0.ChkG
import RieszN7.Cap.Dir0.ChkPos
import RieszN7.Cap.Dir1.ChkA
import RieszN7.Cap.Dir1.ChkB
import RieszN7.Cap.Dir1.ChkG
import RieszN7.Cap.Dir1.ChkPos
import RieszN7.Cap.Dir2.ChkA
import RieszN7.Cap.Dir2.ChkB
import RieszN7.Cap.Dir2.ChkG
import RieszN7.Cap.Dir2.ChkPos
import RieszN7.Cap.Dir3.ChkA
import RieszN7.Cap.Dir3.ChkB
import RieszN7.Cap.Dir3.ChkG
import RieszN7.Cap.Dir3.ChkPos
import RieszN7.Cap.Dir4.ChkA
import RieszN7.Cap.Dir4.ChkB
import RieszN7.Cap.Dir4.ChkG
import RieszN7.Cap.Dir4.ChkPos
import RieszN7.Cap.Dir5.ChkA
import RieszN7.Cap.Dir5.ChkB
import RieszN7.Cap.Dir5.ChkG
import RieszN7.Cap.Dir5.ChkPos
import RieszN7.Cap.Dir6.ChkA
import RieszN7.Cap.Dir6.ChkB
import RieszN7.Cap.Dir6.ChkG
import RieszN7.Cap.Dir6.ChkPos

/-!
# Cap piece `[17/12, 3/2]`: `capSharp_of_family` instantiated on the 9 real objects

The two node objects (`s = 17/12`, `s = 3/2`) and the 7 pin-response directions, with every object-side hypothesis
of `capSharp_of_family` discharged from the objects' kernel facts (`checkPos`, `chkA/B/G`) and the shared shapes
(`rfl`). What remains open, for arbitrary real weights `w`, is the piece-side input:
- PSD of the reduced family blocks (Step P, §3.2.2);
- the e-row `E_φ(P) ≤ e(family)` (§3.2.3);
- the three minorants with exact contacts (Step M, §3.2.4).

For the piece, `w = (1 − λ, λ, ρ_0(s), …, ρ_6(s))` and `φ = phiS s`. Private, AI-written, not reviewed.
-/

open Real

namespace RieszN7.Cap.P17o12_3o2
open ThomsonN7 ThomsonN7.Cert ThomsonN7.Cert.CapR ThomsonGen ThomsonN7.Base RieszN7.Cap

/-- The 9 objects: node `a = 17/12`, node `b = 3/2`, directions `0 … 6`. -/
def objs : Fin 9 → TCertR :=
  ![cap_n17o12, cap_n3o2, cap_dir0, cap_dir1, cap_dir2, cap_dir3, cap_dir4, cap_dir5, cap_dir6]

/-- Shared shapes (taken from node `b`). -/
def LA := cap_n3o2.SA.map shp
def LB := cap_n3o2.SB.map shp
def LG := cap_n3o2.SG.map shp
def LP := cap_n3o2.FP.map shpF
def LR := cap_n3o2.FR.map shpF

theorem shared : ∀ j, Shared 6 (-1) 1 (-99) 100 LA LB LG LP LR (objs j) := by
  intro j
  fin_cases j <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem pos : ∀ j, (objs j).checkPos = true := by
  intro j
  fin_cases j
  exacts [cap_n17o12_pos, cap_n3o2_pos, cap_dir0_pos, cap_dir1_pos, cap_dir2_pos, cap_dir3_pos, cap_dir4_pos,
    cap_dir5_pos, cap_dir6_pos]

theorem chkA : ∀ j, (objs j).chkA = true := by
  intro j
  fin_cases j
  exacts [cap_n17o12_A, cap_n3o2_A, cap_dir0_A, cap_dir1_A, cap_dir2_A, cap_dir3_A, cap_dir4_A, cap_dir5_A,
    cap_dir6_A]

theorem chkB : ∀ j, (objs j).chkB = true := by
  intro j
  fin_cases j
  exacts [cap_n17o12_B, cap_n3o2_B, cap_dir0_B, cap_dir1_B, cap_dir2_B, cap_dir3_B, cap_dir4_B, cap_dir5_B,
    cap_dir6_B]

theorem chkG : ∀ j, (objs j).chkG = true := by
  intro j
  fin_cases j
  exacts [cap_n17o12_G, cap_n3o2_G, cap_dir0_G, cap_dir1_G, cap_dir2_G, cap_dir3_G, cap_dir4_G, cap_dir5_G,
    cap_dir6_G]

theorem goodP : ∀ k < 6 + 1, ((LP.getD k (shpF TCertN.nbEmpty)).1.all fun row =>
      decide (row.length ≤ (LP.getD k (shpF TCertN.nbEmpty)).2)) = true ∧
      6 + 1 - k ≤ (LP.getD k (shpF TCertN.nbEmpty)).1.length := by
  decide +kernel

theorem goodR : ∀ k < 6 + 1, ((LR.getD k (shpF TCertN.nbEmpty)).1.all fun row =>
      decide (row.length ≤ (LR.getD k (shpF TCertN.nbEmpty)).2)) = true ∧
      6 + 1 - k ≤ (LR.getD k (shpF TCertN.nbEmpty)).1.length := by
  decide +kernel

/-- **The bridge on the real objects.** For any kernel `φ` and real weights `w` on the 9 objects: PSD of the reduced
family blocks, the e-row bound and the three minorants (with exact contacts) give `CapSpecSharp φ (−99/100)`. -/
theorem capSharp (φ : ℝ → ℝ) (w : Fin 9 → ℝ)
    (hPF : ∀ k < 6 + 1,
      (redF objs w (fun j => (objs j).FP) (LP.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hRF : ∀ k < 6 + 1,
      (redF objs w (fun j => (objs j).FR) (LR.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hPA : ∀ r < LA.length, QFnonneg (LA.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SA) (wA objs w) r))
    (hPB : ∀ r < LB.length, QFnonneg (LB.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SB) (wB objs w) r))
    (hPG : ∀ r < LG.length, QFnonneg (LG.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SG) (wG objs w) r))
    (hE : pairEnergy φ pentBipyramid ≤ efam objs w)
    (hHA : ∀ t, -1 ≤ t → t ≤ -99 / 100 →
      HAfam objs w t ≤ φ t ∧ (HAfam objs w t = φ t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 → HBfam objs w t ≤ φ t ∧ (HBfam objs w t = φ t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      HCfam objs w t ≤ φ t ∧ (HCfam objs w t = φ t → t = c1 ∨ t = c2)) :
    CapSpecSharp φ (-99 / 100) := by
  have hq : ((-99 : ℤ) : ℝ) / ((100 : ℕ) : ℝ) = -99 / 100 := by norm_num
  have h := capSharp_of_family φ objs w shared pos chkA chkB chkG (by norm_num) (by norm_num)
    (by norm_num) goodP goodR hPF hRF hPA hPB hPG hE (by rw [hq]; exact hHA) hHB hHC
  rwa [hq] at h

/-- The e-row of the 9 objects (one `ℤ[√5]` `decide` each). -/
theorem erow : ∀ j, ERowR (objs j) := by
  intro j
  fin_cases j
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)
  · exact erowR_of_chk _ (by decide +kernel)

/-- Negative control: a node with `e` raised by one unit fails the e-row check. -/
theorem erow_neg : erowChk { cap_n17o12 with e := cap_n17o12.e + 1 } = false := by decide +kernel

/-- **The bridge on the real objects, `φ = phiS s`, with the e-row discharged:** what remains is Step P (PSD of the
reduced family blocks), the three family pins of the e-row and Step M (minorants with exact contacts). -/
theorem capSharp_phiS (s : ℝ) (w : Fin 9 → ℝ)
    (hPF : ∀ k < 6 + 1,
      (redF objs w (fun j => (objs j).FP) (LP.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hRF : ∀ k < 6 + 1,
      (redF objs w (fun j => (objs j).FR) (LR.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hPA : ∀ r < LA.length, QFnonneg (LA.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SA) (wA objs w) r))
    (hPB : ∀ r < LB.length, QFnonneg (LB.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SB) (wB objs w) r))
    (hPG : ∀ r < LG.length, QFnonneg (LG.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SG) (wG objs w) r))
    (pA : HAfam objs w (-1) = RieszN7.phiS s (-1)) (pB : HBfam objs w 0 = RieszN7.phiS s 0)
    (pC : HCfam objs w c1 + HCfam objs w c2 = RieszN7.phiS s c1 + RieszN7.phiS s c2)
    (hHA : ∀ t, -1 ≤ t → t ≤ -99 / 100 →
      HAfam objs w t ≤ RieszN7.phiS s t ∧ (HAfam objs w t = RieszN7.phiS s t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 →
      HBfam objs w t ≤ RieszN7.phiS s t ∧ (HBfam objs w t = RieszN7.phiS s t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      HCfam objs w t ≤ RieszN7.phiS s t ∧ (HCfam objs w t = RieszN7.phiS s t → t = c1 ∨ t = c2)) :
    CapSpecSharp (RieszN7.phiS s) (-99 / 100) :=
  capSharp (RieszN7.phiS s) w hPF hRF hPA hPB hPG (hE_of_pins objs w s erow pA pB pC) hHA hHB hHC

/-! ### The piece weights and the e-row pins -/

/-- The three pin functionals entering the e-row: `β₀ = H_B(0)`, `α₀ = H_A(−1)`, `a₀ = (H_C(c₁) + H_C(c₂))/2`
(index 0, 2, 3 of check_capR's `Pin`). -/
noncomputable def pinB0 (c : TCertR) : ℝ := c.hdr.HBf 0
noncomputable def pinA0 (c : TCertR) : ℝ := c.hdr.HAf (-1)
noncomputable def pina0 (c : TCertR) : ℝ := (c.hdr.HCf c1 + c.hdr.HCf c2) / 2

/-- **The piece weights** `(1 − λ, λ, ρ₀, …, ρ₆)`, `ρ_k = v_k − (1 − λ) ṽ_{a,k} − λ ṽ_{b,k}`, for target pins `v` and node
pins `va, vb` (any reals; the e-row uses the components 0, 2, 3, which must be the nodes' actual pins). -/
noncomputable def wts (lam : ℝ) (v va vb : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![1 - lam, lam, v 0 - (1 - lam) * va 0 - lam * vb 0, v 1 - (1 - lam) * va 1 - lam * vb 1,
    v 2 - (1 - lam) * va 2 - lam * vb 2, v 3 - (1 - lam) * va 3 - lam * vb 3, v 4 - (1 - lam) * va 4 - lam * vb 4,
    v 5 - (1 - lam) * va 5 - lam * vb 5, v 6 - (1 - lam) * va 6 - lam * vb 6]

/-- Unit pins of the directions (index `i` of direction `i`): one `ℤ[√5]` `decide` each. -/
theorem dir_pins :
    (pinA0 cap_dir0 = 0 ∧ pinB0 cap_dir0 = 1 ∧ pina0 cap_dir0 = 0) ∧
    (pinA0 cap_dir1 = 0 ∧ pinB0 cap_dir1 = 0 ∧ pina0 cap_dir1 = 0) ∧
    (pinA0 cap_dir2 = 1 ∧ pinB0 cap_dir2 = 0 ∧ pina0 cap_dir2 = 0) ∧
    (pinA0 cap_dir3 = 0 ∧ pinB0 cap_dir3 = 0 ∧ pina0 cap_dir3 = 1) ∧
    (pinA0 cap_dir4 = 0 ∧ pinB0 cap_dir4 = 0 ∧ pina0 cap_dir4 = 0) ∧
    (pinA0 cap_dir5 = 0 ∧ pinB0 cap_dir5 = 0 ∧ pina0 cap_dir5 = 0) ∧
    (pinA0 cap_dir6 = 0 ∧ pinB0 cap_dir6 = 0 ∧ pina0 cap_dir6 = 0) := by
  have L := fun j => (checkPos_parts (objs j) (pos j)).1
  have h0 := pin_of_chk cap_dir0 0 1 0 (L 2) (by decide +kernel)
  have h1 := pin_of_chk cap_dir1 0 0 0 (L 3) (by decide +kernel)
  have h2 := pin_of_chk cap_dir2 1 0 0 (L 4) (by decide +kernel)
  have h3 := pin_of_chk cap_dir3 0 0 1 (L 5) (by decide +kernel)
  have h4 := pin_of_chk cap_dir4 0 0 0 (L 6) (by decide +kernel)
  have h5 := pin_of_chk cap_dir5 0 0 0 (L 7) (by decide +kernel)
  have h6 := pin_of_chk cap_dir6 0 0 0 (L 8) (by decide +kernel)
  simp only [pinA0, pinB0, pina0]
  push_cast at h0 h1 h2 h3 h4 h5 h6
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- Negative control: direction 2 (`α₀`) does not have the unit pin of direction 0. -/
theorem dir_pin_neg : pinChk cap_dir2 0 1 0 = false := by decide +kernel

/-- **The e-row pins of the family** are the target pins, for any `λ` and `v`, once `va, vb` are the nodes' pins. -/
theorem fam_pins (lam : ℝ) (v va vb : Fin 7 → ℝ)
    (ha : va 0 = pinB0 cap_n17o12 ∧ va 2 = pinA0 cap_n17o12 ∧ va 3 = pina0 cap_n17o12)
    (hb : vb 0 = pinB0 cap_n3o2 ∧ vb 2 = pinA0 cap_n3o2 ∧ vb 3 = pina0 cap_n3o2) :
    HAfam objs (wts lam v va vb) (-1) = v 2 ∧ HBfam objs (wts lam v va vb) 0 = v 0 ∧
      (HCfam objs (wts lam v va vb) c1 + HCfam objs (wts lam v va vb) c2) / 2 = v 3 := by
  obtain ⟨⟨a0, b0, c0⟩, ⟨a1, b1, c1'⟩, ⟨a2, b2, c2'⟩, ⟨a3, b3, c3⟩, ⟨a4, b4, c4⟩, ⟨a5, b5, c5⟩, ⟨a6, b6, c6⟩⟩ :=
    dir_pins
  simp only [pinA0, pinB0, pina0] at a0 b0 c0 a1 b1 c1' a2 b2 c2' a3 b3 c3 a4 b4 c4 a5 b5 c5 a6 b6 c6 ha hb
  obtain ⟨ha0, ha2, ha3⟩ := ha
  obtain ⟨hb0, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · simp only [HAfam, Fin.sum_univ_succ, Fin.sum_univ_zero, objs, wts, Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [a0, a1, a2, a3, a4, a5, a6, ha2, hb2]
    ring
  · simp only [HBfam, Fin.sum_univ_succ, Fin.sum_univ_zero, objs, wts, Matrix.cons_val_zero, Matrix.cons_val_succ]
    rw [b0, b1, b2, b3, b4, b5, b6, ha0, hb0]
    ring
  · simp only [HCfam, Fin.sum_univ_succ, Fin.sum_univ_zero, objs, wts, Matrix.cons_val_zero, Matrix.cons_val_succ]
    linear_combination (v 0 - (1 - lam) * va 0 - lam * vb 0) * c0 + (v 1 - (1 - lam) * va 1 - lam * vb 1) * c1'
      + (v 2 - (1 - lam) * va 2 - lam * vb 2) * c2' + (v 3 - (1 - lam) * va 3 - lam * vb 3) * c3
      + (v 4 - (1 - lam) * va 4 - lam * vb 4) * c4 + (v 5 - (1 - lam) * va 5 - lam * vb 5) * c5
      + (v 6 - (1 - lam) * va 6 - lam * vb 6) * c6 - (1 - lam) * ha3 - lam * hb3

/-- **Cap piece `[17/12, 3/2]` modulo Step P and Step M.** For `s` and `λ` (any reals), target pins `v` with the three
e-row components equal to their `phiS s` values, node pins `va, vb`, and `w = wts λ v va vb`: PSD of the reduced family
blocks (Step P) and the three minorants with exact contacts (Step M) give `CapSpecSharp (phiS s) (−99/100)`. -/
theorem capSharp_piece (s lam : ℝ) (v va vb : Fin 7 → ℝ)
    (hv : v 0 = RieszN7.phiS s 0 ∧ v 2 = RieszN7.phiS s (-1) ∧
      v 3 = (RieszN7.phiS s c1 + RieszN7.phiS s c2) / 2)
    (ha : va 0 = pinB0 cap_n17o12 ∧ va 2 = pinA0 cap_n17o12 ∧ va 3 = pina0 cap_n17o12)
    (hb : vb 0 = pinB0 cap_n3o2 ∧ vb 2 = pinA0 cap_n3o2 ∧ vb 3 = pina0 cap_n3o2)
    (hPF : ∀ k < 6 + 1,
      (redF objs (wts lam v va vb) (fun j => (objs j).FP) (LP.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hRF : ∀ k < 6 + 1,
      (redF objs (wts lam v va vb) (fun j => (objs j).FR) (LR.getD k (shpF TCertN.nbEmpty)).2 k).PosSemidef)
    (hPA : ∀ r < LA.length, QFnonneg (LA.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SA) (wA objs (wts lam v va vb)) r))
    (hPB : ∀ r < LB.length, QFnonneg (LB.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SB) (wB objs (wts lam v va vb)) r))
    (hPG : ∀ r < LG.length, QFnonneg (LG.getD r (shp tbDefault)).2.2.2
      (redS (fun j => (objs j).SG) (wG objs (wts lam v va vb)) r))
    (hHA : ∀ t, -1 ≤ t → t ≤ -99 / 100 → HAfam objs (wts lam v va vb) t ≤ RieszN7.phiS s t ∧
      (HAfam objs (wts lam v va vb) t = RieszN7.phiS s t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 → HBfam objs (wts lam v va vb) t ≤ RieszN7.phiS s t ∧
      (HBfam objs (wts lam v va vb) t = RieszN7.phiS s t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 → HCfam objs (wts lam v va vb) t ≤ RieszN7.phiS s t ∧
      (HCfam objs (wts lam v va vb) t = RieszN7.phiS s t → t = c1 ∨ t = c2)) :
    CapSpecSharp (RieszN7.phiS s) (-99 / 100) := by
  obtain ⟨pA, pB, pC⟩ := fam_pins lam v va vb ha hb
  obtain ⟨hv0, hv2, hv3⟩ := hv
  refine capSharp_phiS s (wts lam v va vb) hPF hRF hPA hPB hPG (pA.trans hv2) (pB.trans hv0) ?_ hHA hHB hHC
  linarith [pC, hv3]

end RieszN7.Cap.P17o12_3o2
