import RieszN7.Bridge
import RieszN7.Cells.S915_90.N1o2.ChkMeta
import RieszN7.Cells.S915_90.N1o2.ChkA
import RieszN7.Cells.S915_90.N1o2.ChkB
import RieszN7.Cells.S915_90.N1o2.ChkG
import RieszN7.Cells.S915_90.N9o16.ChkMeta
import RieszN7.Cells.S915_90.N9o16.ChkA
import RieszN7.Cells.S915_90.N9o16.ChkB
import RieszN7.Cells.S915_90.N9o16.ChkG
import RieszN7.Cells.S915_90.P1o2_9o16.Mid
import RieszN7.Cells.S915_90.P1o2_9o16.E

/-!
# `RieszN7.Cells.S915_90.P1o2_9o16.Spec` — slab cell `[-183/200, -9/10]`, piece `s ∈ [1/2, 9/16]` (Route 2)

`∀ s ∈ [1/2, 9/16], SlabSpec (phiS s) (-183/200) (-9/10)` by `Bridge.slabSpec_interp` from
* the two node certificates (`tc_cells_s915_90_n1o2`, `tc_cells_s915_90_n9o16`; checkMeta/chkA/chkB/chkG by kernel
  `decide`, `ThomsonGen.tcert_bound`),
* condition (E): `P1o2_9o16.E.energy` (upper models + Bernstein, two s-parts) and `pairEnergy_pent`,
* condition (H): for `t ≤ 1/2` concavity in s (`MinorR.Hint_le_of_nodes`) with the node chains `N*.Minor.min{A,B,C}`;
  for `t ∈ [1/2, 1)` (classes B, C) the 2-D boxes `P1o2_9o16.Mid.mid{B,C}` (`MinorR.peval2_hinterp`).
Route 2 (exact, no local lemma), as LEAN_PLAN_range.md prescribes for s ∈ [1/2, 3/2].
Hand-written template (Phase 2a, 2026-11-07); private, AI-written, not reviewed.
-/

open Real

namespace RieszN7.Cells.S915_90.P1o2_9o16.Spec

open ThomsonN7 ThomsonGen RieszN7 RieszN7.MinorR
open LogLean.Minor (peval)
open scoped InnerProductSpace

theorem spec : ∀ s ∈ Set.Icc ((1 : ℝ) / 2) (9 / 16), SlabSpec (phiS s) (-183 / 200) (-9 / 10) := by
  rintro s ⟨hs0, hs1⟩
  have ha : (0 : ℝ) < ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by norm_num
  have hab : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) < ((9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ) := by norm_num
  have hs0' : ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) ≤ s := by norm_num; linarith
  have hs1' : s ≤ ((9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ) := by norm_num; linarith
  -- node bounds
  have TBa := Bridge.tb_of_tcert tc_cells_s915_90_n1o2 tc_cells_s915_90_n1o2_meta tc_cells_s915_90_n1o2_A
    tc_cells_s915_90_n1o2_B tc_cells_s915_90_n1o2_G (lo := -183 / 200) (hi := -9 / 10)
    (HA := RieszN7.Cells.S915_90.N1o2.Minor.HA) (HB := RieszN7.Cells.S915_90.N1o2.Minor.HB)
    (HC := RieszN7.Cells.S915_90.N1o2.Minor.HC) (Lam := RieszN7.Cells.S915_90.N1o2.Minor.Lam)
    (by
      show ((tc_cells_s915_90_n1o2.an : ℤ) : ℝ) / ((tc_cells_s915_90_n1o2.ad : ℕ) : ℝ) = -183 / 200
      rw [show tc_cells_s915_90_n1o2.an = -183 from rfl, show tc_cells_s915_90_n1o2.ad = 200 from rfl]
      norm_num)
    (by
      show ((tc_cells_s915_90_n1o2.bn : ℤ) : ℝ) / ((tc_cells_s915_90_n1o2.bd : ℕ) : ℝ) = -9 / 10
      rw [show tc_cells_s915_90_n1o2.bn = -9 from rfl, show tc_cells_s915_90_n1o2.bd = 10 from rfl]
      norm_num)
    rfl rfl rfl rfl
  have TBb := Bridge.tb_of_tcert tc_cells_s915_90_n9o16 tc_cells_s915_90_n9o16_meta tc_cells_s915_90_n9o16_A
    tc_cells_s915_90_n9o16_B tc_cells_s915_90_n9o16_G (lo := -183 / 200) (hi := -9 / 10)
    (HA := RieszN7.Cells.S915_90.N9o16.Minor.HA) (HB := RieszN7.Cells.S915_90.N9o16.Minor.HB)
    (HC := RieszN7.Cells.S915_90.N9o16.Minor.HC) (Lam := RieszN7.Cells.S915_90.N9o16.Minor.Lam)
    (by
      show ((tc_cells_s915_90_n9o16.an : ℤ) : ℝ) / ((tc_cells_s915_90_n9o16.ad : ℕ) : ℝ) = -183 / 200
      rw [show tc_cells_s915_90_n9o16.an = -183 from rfl, show tc_cells_s915_90_n9o16.ad = 200 from rfl]
      norm_num)
    (by
      show ((tc_cells_s915_90_n9o16.bn : ℤ) : ℝ) / ((tc_cells_s915_90_n9o16.bd : ℕ) : ℝ) = -9 / 10
      rw [show tc_cells_s915_90_n9o16.bn = -9 from rfl, show tc_cells_s915_90_n9o16.bd = 10 from rfl]
      norm_num)
    rfl rfl rfl rfl
  have hLa : 0 < RieszN7.Cells.S915_90.N1o2.Minor.Lam := by
    norm_num [RieszN7.Cells.S915_90.N1o2.Minor.Lam]
  have hLb : 0 < RieszN7.Cells.S915_90.N9o16.Minor.Lam := by
    norm_num [RieszN7.Cells.S915_90.N9o16.Minor.Lam]
  refine Bridge.slabSpec_interp ha hab hs0' hs1' TBa TBb ?_ ?_ ?_ ?_
  · -- (E)
    have hE := RieszN7.Cells.S915_90.P1o2_9o16.E.energy s hs0 hs1
    rw [pairEnergy_pent]
    unfold ThomsonN7.Base.c1 ThomsonN7.Base.c2
    rw [show RieszN7.Cells.S915_90.P1o2_9o16.E.HE = hinterp 1 2 9 16 [320108834442164305920] (21 * 18446744073709551616)
          [312742378504987213824] (21 * 18446744073709551616) from rfl,
      show RieszN7.Cells.S915_90.P1o2_9o16.E.DHe = hden 1 2 9 16 (21 * 18446744073709551616)
          (21 * 18446744073709551616) from rfl,
      peval2_hinterp 1 2 9 16 [320108834442164305920] (21 * 18446744073709551616) [312742378504987213824]
        (21 * 18446744073709551616) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)] at hE
    have ea : tc_cells_s915_90_n1o2.ef = ((320108834442164305920 : ℤ) : ℝ) / ((18446744073709551616 : ℕ) : ℝ) := by
      show ((tc_cells_s915_90_n1o2.e : ℤ) : ℝ) / ((tc_cells_s915_90_n1o2.Lam : ℕ) : ℝ) = _
      rw [show tc_cells_s915_90_n1o2.e = 320108834442164305920 from rfl,
        show tc_cells_s915_90_n1o2.Lam = 18446744073709551616 from rfl]
    have eb : tc_cells_s915_90_n9o16.ef = ((312742378504987213824 : ℤ) : ℝ) / ((18446744073709551616 : ℕ) : ℝ) := by
      show ((tc_cells_s915_90_n9o16.e : ℤ) : ℝ) / ((tc_cells_s915_90_n9o16.Lam : ℕ) : ℝ) = _
      rw [show tc_cells_s915_90_n9o16.e = 312742378504987213824 from rfl,
        show tc_cells_s915_90_n9o16.Lam = 18446744073709551616 from rfl]
    have fa : (fun t => peval [320108834442164305920] t / (((21 * 18446744073709551616 : ℕ)) : ℝ))
        = fun _ => tc_cells_s915_90_n1o2.ef / 21 := by
      funext t; rw [ea]; simp only [peval]; push_cast; ring
    have fb : (fun t => peval [312742378504987213824] t / (((21 * 18446744073709551616 : ℕ)) : ℝ))
        = fun _ => tc_cells_s915_90_n9o16.ef / 21 := by
      funext t; rw [eb]; simp only [peval]; push_cast; ring
    rw [fa, fb] at hE
    exact hE
  · -- class A: t ≤ hi < 1/2, concavity
    intro t h0 h1
    exact Hint_le_of_nodes ha hab hs0' hs1' (by linarith)
      (RieszN7.Cells.S915_90.N1o2.Minor.minA t (by linarith) (by linarith))
      (RieszN7.Cells.S915_90.N9o16.Minor.minA t (by linarith) (by linarith))
  · -- class B
    intro t h0 h1
    rcases lt_or_ge t (1 / 2) with h | h
    · exact Hint_le_of_nodes ha hab hs0' hs1' h.le
        (RieszN7.Cells.S915_90.N1o2.Minor.minB t (by linarith) (by linarith))
        (RieszN7.Cells.S915_90.N9o16.Minor.minB t (by linarith) (by linarith))
    · have hm := RieszN7.Cells.S915_90.P1o2_9o16.Mid.midB s hs0 hs1 t h h1
      rw [show RieszN7.Cells.S915_90.P1o2_9o16.Models.HqB = hinterp 1 2 9 16 RieszN7.Cells.S915_90.N1o2.Minor.HB
            RieszN7.Cells.S915_90.N1o2.Minor.Lam RieszN7.Cells.S915_90.N9o16.Minor.HB
            RieszN7.Cells.S915_90.N9o16.Minor.Lam from rfl,
        show RieszN7.Cells.S915_90.P1o2_9o16.Models.DH = hden 1 2 9 16 RieszN7.Cells.S915_90.N1o2.Minor.Lam
            RieszN7.Cells.S915_90.N9o16.Minor.Lam from rfl,
        peval2_hinterp 1 2 9 16 RieszN7.Cells.S915_90.N1o2.Minor.HB RieszN7.Cells.S915_90.N1o2.Minor.Lam RieszN7.Cells.S915_90.N9o16.Minor.HB RieszN7.Cells.S915_90.N9o16.Minor.Lam
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hLa hLb] at hm
      exact hm
  · -- class C
    intro t h0 h1
    rcases lt_or_ge t (1 / 2) with h | h
    · exact Hint_le_of_nodes ha hab hs0' hs1' h.le
        (RieszN7.Cells.S915_90.N1o2.Minor.minC t (by linarith) (by linarith))
        (RieszN7.Cells.S915_90.N9o16.Minor.minC t (by linarith) (by linarith))
    · have hm := RieszN7.Cells.S915_90.P1o2_9o16.Mid.midC s hs0 hs1 t h h1
      rw [show RieszN7.Cells.S915_90.P1o2_9o16.Models.HqC = hinterp 1 2 9 16 RieszN7.Cells.S915_90.N1o2.Minor.HC
            RieszN7.Cells.S915_90.N1o2.Minor.Lam RieszN7.Cells.S915_90.N9o16.Minor.HC
            RieszN7.Cells.S915_90.N9o16.Minor.Lam from rfl,
        show RieszN7.Cells.S915_90.P1o2_9o16.Models.DH = hden 1 2 9 16 RieszN7.Cells.S915_90.N1o2.Minor.Lam
            RieszN7.Cells.S915_90.N9o16.Minor.Lam from rfl,
        peval2_hinterp 1 2 9 16 RieszN7.Cells.S915_90.N1o2.Minor.HC RieszN7.Cells.S915_90.N1o2.Minor.Lam RieszN7.Cells.S915_90.N9o16.Minor.HC RieszN7.Cells.S915_90.N9o16.Minor.Lam
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hLa hLb] at hm
      exact hm

end RieszN7.Cells.S915_90.P1o2_9o16.Spec

#print axioms RieszN7.Cells.S915_90.P1o2_9o16.Spec.spec
