import ThomsonGen.Generic.Glue
import RieszN7.Energy
import RieszN7.Cells.MinorR

/-!
# `RieszN7.Bridge` — node certificates + interpolation ⇒ `SlabSpec (phiS s)` on a cell piece (LEAN_PLAN_range.md §3.1.2)

Hand-written (Phase 2a, 2026-11-07; private, AI-written, not reviewed).

* `tb_of_tcert`: `ThomsonGen.tcert_bound` of a packed node certificate (the four kernel checks), restated with the
  minorants in `peval` form (`polyR_eq`, as `CoulN7.Bridge.polyR_eq`) and the cut as given reals.
* `slabSpec_interp`: Route 2 for one slab piece `s ∈ [a, b]`.  From the two node bounds
  `e_j ≤ Σ_{i<j} cls3 H_{A,j} H_{B,j} H_{C,j} ⟪y_i, y_j⟫` (j = a, b), the interpolated family
  `H_X(s, ·) = MinorR.Hint a b H_{X,a} H_{X,b} s = 1 + α (H_{X,a} − 1) + β (H_{X,b} − 1)` with
  `α = s(b−s)/(a(b−a)) ≥ 0`, `β = s(s−a)/(b(b−a)) ≥ 0` satisfies the typed bound with
  `e(s) = 21 · Hint a b (e_a/21) (e_b/21) s 0 = 21 + α (e_a − 21) + β (e_b − 21)` (linearity of `cls3` and
  `Σ_{i<j} 1 = 21`).  The remaining inputs are condition (E) `E_s(P) < e(s)` and condition (H) `H_X(s, ·) ≤ phiS s`
  on the class ranges.  No `TCert` for the family is built.
-/

open Real

namespace RieszN7.Bridge

open ThomsonN7 ThomsonGen RieszN7.MinorR
open LogLean.Minor (peval)
open scoped InnerProductSpace

/-- `peval` is the `polyR` sum (as `CoulN7.Bridge.peval_eq_sum`). -/
theorem peval_eq_sum (h : List ℤ) (x : ℝ) :
    peval h x = ∑ j ∈ Finset.range h.length, (h.getD j 0 : ℝ) * x ^ j := by
  induction h with
  | nil => simp [peval]
  | cons a as ih =>
    rw [peval, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)

theorem polyR_eq (Lam : ℕ) (h : List ℤ) (x : ℝ) : Cert.polyR Lam h x = peval h x / Lam := by
  unfold Cert.polyR
  rw [peval_eq_sum]

/-- The node bound of a packed certificate with its minorants in `peval` form. -/
theorem tb_of_tcert (cf : Cert.TCert) (hm : cf.checkMeta = true) (hA : cf.chkA = true) (hB : cf.chkB = true)
    (hG : cf.chkG = true) {lo hi : ℝ} {HA HB HC : List ℤ} {Lam : ℕ} (hlo : cf.alo = lo) (hhi : cf.ahi = hi)
    (eA : cf.HA = HA) (eB : cf.HB = HB) (eC : cf.HC = HC) (eL : cf.Lam = Lam) :
    ∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      cf.ef ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
        cls3 (fun t => peval HA t / Lam) (fun t => peval HB t / Lam) (fun t => peval HC t / Lam) i j
          ⟪y i, y j⟫_ℝ := by
  subst hlo hhi eA eB eC eL
  have e : ∀ X : List ℤ, Cert.polyR cf.Lam X = fun t => peval X t / cf.Lam := fun X => funext (polyR_eq cf.Lam X)
  have h := tcert_bound cf hm hA hB hG
  simp only [Cert.TCert.HAf, Cert.TCert.HBf, Cert.TCert.HCf, e] at h
  exact h

/-- `cls3` commutes with the interpolation (pointwise in the class). -/
theorem cls3_Hint (a b s x : ℝ) (HAa HBa HCa HAb HBb HCb : ℝ → ℝ) (i j : Fin 7) :
    cls3 (Hint a b HAa HAb s) (Hint a b HBa HBb s) (Hint a b HCa HCb s) i j x
      = 1 + s * (b - s) / (a * (b - a)) * (cls3 HAa HBa HCa i j x - 1)
          + s * (s - a) / (b * (b - a)) * (cls3 HAb HBb HCb i j x - 1) := by
  unfold cls3
  split_ifs <;> rfl

/-- **Route 2 for one slab piece.** -/
theorem slabSpec_interp {a b s lo hi ea eb : ℝ} (ha : 0 < a) (hab : a < b) (hs0 : a ≤ s) (hs1 : s ≤ b)
    {HAa HBa HCa HAb HBb HCb : ℝ → ℝ}
    (TBa : ∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      ea ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HAa HBa HCa i j ⟪y i, y j⟫_ℝ)
    (TBb : ∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      eb ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HAb HBb HCb i j ⟪y i, y j⟫_ℝ)
    (hE : pairEnergy (phiS s) pentBipyramid < 21 * Hint a b (fun _ => ea / 21) (fun _ => eb / 21) s 0)
    (hA : ∀ t, lo ≤ t → t ≤ hi → Hint a b HAa HAb s t ≤ phiS s t)
    (hB : ∀ t, lo ≤ t → t < 1 → Hint a b HBa HBb s t ≤ phiS s t)
    (hC : ∀ t, lo ≤ t → t < 1 → Hint a b HCa HCb s t ≤ phiS s t) :
    SlabSpec (phiS s) lo hi := by
  have hb : 0 < b := ha.trans hab
  have hs : 0 < s := lt_of_lt_of_le ha hs0
  have hα0 : 0 ≤ s * (b - s) / (a * (b - a)) :=
    div_nonneg (mul_nonneg hs.le (by linarith)) (mul_nonneg ha.le (by linarith))
  have hβ0 : 0 ≤ s * (s - a) / (b * (b - a)) :=
    div_nonneg (mul_nonneg hs.le (by linarith)) (mul_nonneg hb.le (by linarith))
  refine ⟨21 * Hint a b (fun _ => ea / 21) (fun _ => eb / 21) s 0, Hint a b HAa HAb s, Hint a b HBa HBb s,
    Hint a b HCa HCb s, hE, ?_, hA, hB, hC⟩
  intro y hy hlo hhi hmin
  have h1 := TBa y hy hlo hhi hmin
  have h2 := TBb y hy hlo hhi hmin
  simp only [cls3_Hint]
  rw [sum_Ioi_seven] at h1 h2 ⊢
  have k1 := mul_le_mul_of_nonneg_left h1 hα0
  have k2 := mul_le_mul_of_nonneg_left h2 hβ0
  unfold Hint
  beta_reduce
  linear_combination k1 + k2

end RieszN7.Bridge
