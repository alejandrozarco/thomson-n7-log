import ThomsonGen.Generic.Glue
import ThomsonGen.Cert3
import RieszN7.Bridge

/-!
# `RieszN7.BridgeC1` — Case 1 node certificates + interpolation ⇒ `Case1Claim (phiS s)` on a piece

Hand-written (Phase 2a, 2026-11-08; private, AI-written, not reviewed).

* `nb_of_cert3`: for a packed cut certificate `cf : Cert.Cert3` (cut `an/ad = -9/10`, `cf.check = true`), the
  three-point bound on the cut (`ThomsonN7.ThreePoint.three_point_bound_cut` with `Cert3.hpt_cut`, as in
  `ThomsonGen.Case1.margin_of_threePoint_cut`), with the minorant in `peval` form:
  `eps/Λ ≤ Σ_{i<j} peval h ⟪y_i, y_j⟫ / Λ` for every configuration with all pair inner products `≥ -9/10`.
  No energy comparison is made at the node.
* `case1_interp`: Route 2 for one Case 1 piece `s ∈ [a, b]`.  From the two node bounds and
  `H(s, ·) = MinorR.Hint a b H_a H_b s = 1 + α (H_a − 1) + β (H_b − 1)` (`α, β ≥ 0`), the family satisfies
  `e(s) ≤ Σ_{i<j} H(s, ⟪y_i, y_j⟫)` with `e(s) = 21 · Hint a b (e_a/21) (e_b/21) s 0` (linearity, `Σ_{i<j} 1 = 21`).
  With condition (E) `E_s(P) < e(s)` and condition (H) `H(s, ·) ≤ phiS s` on `[-9/10, 1)` this is
  `ThomsonGen.Case1Claim (phiS s)`.  The F matrices of the two nodes are never combined.
-/

open Real

namespace RieszN7.BridgeC1

open ThomsonN7 ThomsonN7.Base ThomsonGen RieszN7.MinorR
open LogLean.Minor (peval)
open scoped InnerProductSpace

/-- The cut three-point bound of a packed Case 1 node certificate, minorant in `peval` form. -/
theorem nb_of_cert3 (cf : Cert.Cert3) (hc : cf.check = true) (hn : cf.n = 7)
    (han : (cf.an : ℝ) / cf.ad = -9 / 10) {H : List ℤ} {Lam : ℕ} (eH : cf.h = H) (eL : cf.Lam = Lam) :
    ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ ⟪y i, y j⟫_ℝ) →
      (cf.eps : ℝ) / Lam ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, peval H ⟪y i, y j⟫_ℝ / Lam := by
  intro y hy hya
  subst eH eL
  have hHf : ∀ t, cf.Hf t = peval cf.h t / cf.Lam := by
    intro t
    unfold Cert.Cert3.Hf
    rw [← Bridge.peval_eq_sum]
  have h := ThreePoint.three_point_bound_cut (n := 7) (by norm_num) (-9 / 10) cf.K cf.m cf.Fm
    (fun k hk => Cert.fmat_psd cf.Lam ((Cert.Cert3.check_parts hc).2.2.2.1 k hk)) cf.Hf
    ((cf.eps : ℝ) / cf.Lam) ?_ y hy.1 hya
  · simpa only [hHf] using h
  · intro u v t hg hu hv ht
    have h := Cert.Cert3.hpt_cut cf hc hg (by rw [han]; exact hu) (by rw [han]; exact hv)
      (by rw [han]; exact ht)
    rw [hn] at h
    exact h

/-- **Route 2 for one Case 1 piece.** -/
theorem case1_interp {a b s ea eb : ℝ} (ha : 0 < a) (hab : a < b) (hs0 : a ≤ s) (hs1 : s ≤ b)
    {Ha Hb : ℝ → ℝ}
    (TBa : ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ ⟪y i, y j⟫_ℝ) →
      ea ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, Ha ⟪y i, y j⟫_ℝ)
    (TBb : ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ ⟪y i, y j⟫_ℝ) →
      eb ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, Hb ⟪y i, y j⟫_ℝ)
    (hE : pairEnergy (phiS s) pentBipyramid < 21 * Hint a b (fun _ => ea / 21) (fun _ => eb / 21) s 0)
    (hH : ∀ t, -9 / 10 ≤ t → t < 1 → Hint a b Ha Hb s t ≤ phiS s t) :
    Case1Claim (phiS s) := by
  have hb : 0 < b := ha.trans hab
  have hs : 0 < s := lt_of_lt_of_le ha hs0
  have hα0 : 0 ≤ s * (b - s) / (a * (b - a)) :=
    div_nonneg (mul_nonneg hs.le (by linarith)) (mul_nonneg ha.le (by linarith))
  have hβ0 : 0 ≤ s * (s - a) / (b * (b - a)) :=
    div_nonneg (mul_nonneg hs.le (by linarith)) (mul_nonneg hb.le (by linarith))
  intro y hy hya
  have h1 := TBa y hy hya
  have h2 := TBb y hy hya
  have hsum : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, Hint a b Ha Hb s ⟪y i, y j⟫_ℝ ≤ pairEnergy (phiS s) y := by
    unfold pairEnergy
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.1 hj).ne
    exact hH _ (hya i j hij) (inner_lt_one_of_ne (hy.1 i) (hy.1 j) (fun h => hij (hy.2 h)))
  have key : 21 * Hint a b (fun _ => ea / 21) (fun _ => eb / 21) s 0
      ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, Hint a b Ha Hb s ⟪y i, y j⟫_ℝ := by
    rw [sum_Ioi_seven] at h1 h2 ⊢
    have k1 := mul_le_mul_of_nonneg_left h1 hα0
    have k2 := mul_le_mul_of_nonneg_left h2 hβ0
    unfold Hint
    linear_combination k1 + k2
  linarith

end RieszN7.BridgeC1
