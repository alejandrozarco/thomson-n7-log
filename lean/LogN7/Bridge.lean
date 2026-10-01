/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`peval_eq_sum` ← `CutOneD.peval_eq_sum`. -/

/-
LogN7/Bridge.lean — from the 1-D minorant theorems (peval form, `LogLean.MinorCore`) and a packed typed
certificate (`Cert.TCert` / `Cert.TCertN` / `Cert.Cert3`) to the kernel-generic specifications for the log
kernel `φ₀ = LogLean.Minor.phi`.  Pattern of `Riesz2/Bridge.lean`; the cap is non-sharp
(`capSpec_of_tcertN`, δ = 10⁻¹⁶, τ = 1/1650).  The certificate's `HXf = polyR Lam HX` and the minorant
module's `peval HX t / HXd` are identified by the list identity `HXd·cf.HX = Lam·HX` (`scaledEq`).
-/
import ThomsonGen.Cert.NBlkCap
import LogN7.Basic

open Real

namespace LogN7

open ThomsonN7 ThomsonGen
open LogLean.Minor (peval padd pscale pneg peval_padd peval_pscale peval_pneg peval_eq_zero_of_all)
open scoped InnerProductSpace

/-- `peval` is the `polyR` sum. -/
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

/-- `a·p = b·q` as integer lists (trailing zeros allowed). -/
def scaledEq (a : ℕ) (p : List ℤ) (b : ℕ) (q : List ℤ) : Bool :=
  (padd (pscale (a:ℤ) p) (pneg (pscale (b:ℤ) q))).all (· == 0)

theorem div_eq_of_scaledEq {a b : ℕ} {p q : List ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : scaledEq a p b q = true) (x : ℝ) : peval p x / b = peval q x / a := by
  have e := peval_eq_zero_of_all _ h x
  simp only [peval_padd, peval_pscale, peval_pneg] at e
  push_cast at e
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_eq_div_iff hbR.ne' haR.ne']
  linarith

theorem HAf_eq (cf : Cert.TCert) {HA : List ℤ} {HAd : ℕ} (hd : 0 < HAd) (hL : 0 < cf.Lam)
    (e : scaledEq HAd cf.HA cf.Lam HA = true) (t : ℝ) : cf.HAf t = peval HA t / HAd := by
  unfold Cert.TCert.HAf
  rw [polyR_eq, div_eq_of_scaledEq hd hL e]

theorem HBf_eq (cf : Cert.TCert) {HB : List ℤ} {HBd : ℕ} (hd : 0 < HBd) (hL : 0 < cf.Lam)
    (e : scaledEq HBd cf.HB cf.Lam HB = true) (t : ℝ) : cf.HBf t = peval HB t / HBd := by
  unfold Cert.TCert.HBf
  rw [polyR_eq, div_eq_of_scaledEq hd hL e]

theorem HCf_eq (cf : Cert.TCert) {HC : List ℤ} {HCd : ℕ} (hd : 0 < HCd) (hL : 0 < cf.Lam)
    (e : scaledEq HCd cf.HC cf.Lam HC = true) (t : ℝ) : cf.HCf t = peval HC t / HCd := by
  unfold Cert.TCert.HCf
  rw [polyR_eq, div_eq_of_scaledEq hd hL e]

theorem c1_eq : Base.c1 = (-1 + √5) / 4 := by unfold Base.c1; ring
theorem c2_eq : Base.c2 = (-1 - √5) / 4 := by unfold Base.c2; ring

/-- **Log cap specification** from a facially reduced packed certificate and the
peval-form coercive minorant theorems (`δ = 10⁻¹⁶`, window `τ = τ₀ = 1/1650`). -/
theorem capSpec_of_minorN (cf : Cert.TCertN) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.toTCert.alo = -1) {a0 : ℝ} (hahi : cf.toTCert.ahi = a0)
    (hE : pairEnergy LogLean.Minor.phi pentBipyramid ≤ cf.toTCert.ef + 1 / 10 ^ 16)
    (hL : 0 < cf.toTCert.Lam)
    {HA HB HC : List ℤ} {HAd HBd HCd : ℕ} (hAd : 0 < HAd) (hBd : 0 < HBd) (hCd : 0 < HCd)
    (eA : scaledEq HAd cf.toTCert.HA cf.toTCert.Lam HA = true)
    (eB : scaledEq HBd cf.toTCert.HB cf.toTCert.Lam HB = true)
    (eC : scaledEq HCd cf.toTCert.HC cf.toTCert.Lam HC = true)
    (capA : ∀ t : ℝ, -1 ≤ t → t ≤ a0 → peval HA t / HAd ≤ LogLean.Minor.phi t ∧
      (LogLean.Minor.phi t - peval HA t / HAd ≤ 1 / 10 ^ 16 → |t + 1| ≤ 1 / 1650))
    (capB : ∀ t : ℝ, -1 ≤ t → t < 1 → peval HB t / HBd ≤ LogLean.Minor.phi t ∧
      (LogLean.Minor.phi t - peval HB t / HBd ≤ 1 / 10 ^ 16 → |t| ≤ 1 / 1650))
    (capC : ∀ t : ℝ, -1 ≤ t → t < 1 → peval HC t / HCd ≤ LogLean.Minor.phi t ∧
      (LogLean.Minor.phi t - peval HC t / HCd ≤ 1 / 10 ^ 16 →
        |t - (-1 + √5) / 4| ≤ 1 / 1650 ∨ |t - (-1 - √5) / 4| ≤ 1 / 1650)) :
    CapSpec LogLean.Minor.phi (1 / 1650) a0 := by
  rw [← hahi]
  refine capSpec_of_tcertN LogLean.Minor.phi cf hm hA hB hG halo (τ := 1 / 1650) le_rfl hE
    ?_ ?_ ?_
  · intro t h1 h2
    rw [HAf_eq cf.toTCert hAd hL eA]
    exact capA t h1 (hahi ▸ h2)
  · intro t h1 h2
    rw [HBf_eq cf.toTCert hBd hL eB]
    exact capB t h1 h2
  · intro t h1 h2
    rw [HCf_eq cf.toTCert hCd hL eC, c1_eq, c2_eq]
    exact capC t h1 h2

/-- **Slab specification** from a packed certificate and the peval-form minorant theorems. -/
theorem slabSpec_of_minor (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    {lo hi : ℝ} (halo : cf.alo = lo) (hahi : cf.ahi = hi)
    (hE : pairEnergy LogLean.Minor.phi pentBipyramid < cf.ef) (hL : 0 < cf.Lam)
    {HA HB HC : List ℤ} {HAd HBd HCd : ℕ} (hAd : 0 < HAd) (hBd : 0 < HBd) (hCd : 0 < HCd)
    (eA : scaledEq HAd cf.HA cf.Lam HA = true) (eB : scaledEq HBd cf.HB cf.Lam HB = true)
    (eC : scaledEq HCd cf.HC cf.Lam HC = true)
    (HA_le : ∀ t : ℝ, lo ≤ t → t ≤ hi → peval HA t / HAd ≤ LogLean.Minor.phi t)
    (HB_le : ∀ t : ℝ, lo ≤ t → t < 1 → peval HB t / HBd ≤ LogLean.Minor.phi t)
    (HC_le : ∀ t : ℝ, lo ≤ t → t < 1 → peval HC t / HCd ≤ LogLean.Minor.phi t) :
    SlabSpec LogLean.Minor.phi lo hi := by
  rw [← halo, ← hahi]
  refine slabSpec_of_tcert LogLean.Minor.phi cf hm hA hB hG hE ?_ ?_ ?_
  · intro t h1 h2
    rw [HAf_eq cf hAd hL eA]
    exact HA_le t (halo ▸ h1) (hahi ▸ h2)
  · intro t h1 h2
    rw [HBf_eq cf hBd hL eB]
    exact HB_le t (halo ▸ h1) h2
  · intro t h1 h2
    rw [HCf_eq cf hCd hL eC]
    exact HC_le t (halo ▸ h1) h2

/-- **Case 1 from a packed cut certificate** (`Cert.Cert3`) and the peval-form minorant
`H ≤ φ₀` on `[-9/10, 1)`. -/
theorem case1Claim_of_cert3 (cf : Cert.Cert3) (hc : cf.check = true) (hn : cf.n = 7)
    (han : (cf.an : ℝ) / cf.ad = -9 / 10) {η : ℝ} (hη : 0 < η)
    (hε : pairEnergy LogLean.Minor.phi pentBipyramid + η ≤ (cf.eps : ℝ) / cf.Lam) (hL : 0 < cf.Lam)
    {H : List ℤ} {Hd : ℕ} (hd : 0 < Hd) (e : scaledEq Hd cf.h cf.Lam H = true)
    (H_le : ∀ t : ℝ, -9 / 10 ≤ t → t < 1 → peval H t / Hd ≤ LogLean.Minor.phi t) :
    Case1Claim LogLean.Minor.phi := by
  have hC : (0 : ℝ) < ((Nat.choose 7 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by norm_num)
  have hHf : ∀ t, cf.Hf t = peval H t / Hd := by
    intro t
    unfold Cert.Cert3.Hf
    rw [← peval_eq_sum, div_eq_of_scaledEq hd hL e]
  refine case1Claim_of_threePoint_cut LogLean.Minor.phi (H := cf.Hf) hη cf.K cf.m cf.Fm
    (fun k hk => Cert.fmat_psd cf.Lam ((Cert.Cert3.check_parts hc).2.2.2.1 k hk)) ?_ ?_
  · intro u v t hg hu hv ht
    have h := Cert.Cert3.hpt_cut cf hc hg (by rw [han]; exact hu) (by rw [han]; exact hv)
      (by rw [han]; exact ht)
    rw [hn] at h
    have hdiv : (pairEnergy LogLean.Minor.phi pentBipyramid + η) / ((Nat.choose 7 2 : ℕ) : ℝ)
        ≤ ((cf.eps : ℝ) / cf.Lam) / ((Nat.choose 7 2 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hε hC.le
    linarith
  · intro t h1 h2
    rw [hHf]
    exact H_le t h1 h2

end LogN7
