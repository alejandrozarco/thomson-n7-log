/-
Riesz2/Bridge.lean — from the 1-D minorant theorems (peval form, `Riesz2.MinorCore`) and a packed
typed certificate (`ThomsonN7.Cert.TCert`, upstream) to M0's generic specifications
`ThomsonGen.CapSpecSharp phi2` and `ThomsonGen.SlabSpec phi2`.

The only kernel-specific inputs of `ThomsonGen.capSpecSharp_of_tcert` / `slabSpec_of_tcert` are
`E_φ(P) ≤ ef` (resp. `<`) and the 1-D facts about `cf.HAf = polyR cf.Lam cf.HA`.  Our minorant modules
state them for `peval HA t / HAd`; the two are identified by the list identity `HAd·cf.HA = Lam·HA`
(`scaledEq`, one `decide`).

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `peval_eq_sum` ← `CutOneD.peval_eq_sum`.
-/
import ThomsonGen.Generic.Glue
import Riesz2.Sharp
import Riesz2.Basic

open Real

namespace Riesz2

open ThomsonN7 ThomsonN7.Base ThomsonGen
open Minor
open scoped InnerProductSpace

/-- `pairEnergy phi2 P = 41/4`. -/
theorem pairEnergy_phi2_pent : pairEnergy phi2 pentBipyramid = 41 / 4 := by
  rw [← riesz2Energy_pent, riesz2Energy_eq_sum_phi2 pent_norm]
  rfl

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

/-- `cf.HAf t = peval HA t / HAd` from the scaled list identity. -/
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

/-- **Sharp cap specification from a packed certificate and the peval-form minorant theorems.** -/
theorem capSpecSharp_of_minor (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) {a0 : ℝ} (hahi : cf.ahi = a0) (hE : (41 / 4 : ℝ) ≤ cf.ef) (hL : 0 < cf.Lam)
    {HA HB HC : List ℤ} {HAd HBd HCd : ℕ} (hAd : 0 < HAd) (hBd : 0 < HBd) (hCd : 0 < HCd)
    (eA : scaledEq HAd cf.HA cf.Lam HA = true) (eB : scaledEq HBd cf.HB cf.Lam HB = true)
    (eC : scaledEq HCd cf.HC cf.Lam HC = true)
    (capA : ∀ t : ℝ, -1 ≤ t → t ≤ a0 →
      peval HA t / HAd ≤ phi2 t ∧ (peval HA t / HAd = phi2 t → t = -1))
    (capB : ∀ t : ℝ, -1 ≤ t → t < 1 →
      peval HB t / HBd ≤ phi2 t ∧ (peval HB t / HBd = phi2 t → t = 0))
    (capC : ∀ t : ℝ, -1 ≤ t → t < 1 →
      peval HC t / HCd ≤ phi2 t ∧ (peval HC t / HCd = phi2 t → 4 * t ^ 2 + 2 * t - 1 = 0)) :
    CapSpecSharp phi2 a0 := by
  rw [← hahi]
  refine capSpecSharp_of_tcert phi2 cf hm hA hB hG halo (by rw [pairEnergy_phi2_pent]; exact hE)
    ?_ ?_ ?_
  · intro t h1 h2
    rw [HAf_eq cf hAd hL eA]
    exact capA t h1 (hahi ▸ h2)
  · intro t h1 h2
    rw [HBf_eq cf hBd hL eB]
    exact capB t h1 h2
  · intro t h1 h2
    rw [HCf_eq cf hCd hL eC]
    exact ⟨(capC t h1 h2).1, fun he => eq_c1_or_c2_of_quad ((capC t h1 h2).2 he)⟩

/-- **Sharp cap specification from a facially reduced packed certificate** (`Cert.TCertN`) and the
peval-form minorant theorems. -/
theorem capSpecSharp_of_minorN (cf : Cert.TCertN) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.toTCert.alo = -1) {a0 : ℝ} (hahi : cf.toTCert.ahi = a0)
    (hE : (41 / 4 : ℝ) ≤ cf.toTCert.ef) (hL : 0 < cf.toTCert.Lam)
    {HA HB HC : List ℤ} {HAd HBd HCd : ℕ} (hAd : 0 < HAd) (hBd : 0 < HBd) (hCd : 0 < HCd)
    (eA : scaledEq HAd cf.toTCert.HA cf.toTCert.Lam HA = true)
    (eB : scaledEq HBd cf.toTCert.HB cf.toTCert.Lam HB = true)
    (eC : scaledEq HCd cf.toTCert.HC cf.toTCert.Lam HC = true)
    (capA : ∀ t : ℝ, -1 ≤ t → t ≤ a0 →
      peval HA t / HAd ≤ phi2 t ∧ (peval HA t / HAd = phi2 t → t = -1))
    (capB : ∀ t : ℝ, -1 ≤ t → t < 1 →
      peval HB t / HBd ≤ phi2 t ∧ (peval HB t / HBd = phi2 t → t = 0))
    (capC : ∀ t : ℝ, -1 ≤ t → t < 1 →
      peval HC t / HCd ≤ phi2 t ∧ (peval HC t / HCd = phi2 t → 4 * t ^ 2 + 2 * t - 1 = 0)) :
    CapSpecSharp phi2 a0 := by
  rw [← hahi]
  refine capSpecSharp_of_tcertN phi2 cf hm hA hB hG halo (by rw [pairEnergy_phi2_pent]; exact hE)
    ?_ ?_ ?_
  · intro t h1 h2
    rw [HAf_eq cf.toTCert hAd hL eA]
    exact capA t h1 (hahi ▸ h2)
  · intro t h1 h2
    rw [HBf_eq cf.toTCert hBd hL eB]
    exact capB t h1 h2
  · intro t h1 h2
    rw [HCf_eq cf.toTCert hCd hL eC]
    exact ⟨(capC t h1 h2).1, fun he => eq_c1_or_c2_of_quad ((capC t h1 h2).2 he)⟩

/-- **Slab specification from a packed certificate and the peval-form minorant theorems.** -/
theorem slabSpec_of_minor (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    {lo hi : ℝ} (halo : cf.alo = lo) (hahi : cf.ahi = hi) (hE : (41 / 4 : ℝ) < cf.ef)
    (hL : 0 < cf.Lam)
    {HA HB HC : List ℤ} {HAd HBd HCd : ℕ} (hAd : 0 < HAd) (hBd : 0 < HBd) (hCd : 0 < HCd)
    (eA : scaledEq HAd cf.HA cf.Lam HA = true) (eB : scaledEq HBd cf.HB cf.Lam HB = true)
    (eC : scaledEq HCd cf.HC cf.Lam HC = true)
    (HA_le : ∀ t : ℝ, lo ≤ t → t ≤ hi → peval HA t / HAd ≤ phi2 t)
    (HB_le : ∀ t : ℝ, lo ≤ t → t < 1 → peval HB t / HBd ≤ phi2 t)
    (HC_le : ∀ t : ℝ, lo ≤ t → t < 1 → peval HC t / HCd ≤ phi2 t) :
    SlabSpec phi2 lo hi := by
  rw [← halo, ← hahi]
  refine slabSpec_of_tcert phi2 cf hm hA hB hG (by rw [pairEnergy_phi2_pent]; exact hE) ?_ ?_ ?_
  · intro t h1 h2
    rw [HAf_eq cf hAd hL eA]
    exact HA_le t (halo ▸ h1) (hahi ▸ h2)
  · intro t h1 h2
    rw [HBf_eq cf hBd hL eB]
    exact HB_le t (halo ▸ h1) h2
  · intro t h1 h2
    rw [HCf_eq cf hCd hL eC]
    exact HC_le t (halo ▸ h1) h2

/-- **Case 1 from a packed cut certificate** (`ThomsonN7.Cert.Cert3`) and the peval-form minorant
`H ≤ phi2` on `[-9/10, 1)` (upstream `Case1.case1_margin`, generic in the data). -/
theorem case1Claim_of_cert3 (cf : Cert.Cert3) (hc : cf.check = true) (hn : cf.n = 7)
    (han : (cf.an : ℝ) / cf.ad = -9 / 10) {η : ℝ} (hη : 0 < η)
    (hε : (41 / 4 : ℝ) + η ≤ (cf.eps : ℝ) / cf.Lam) (hL : 0 < cf.Lam)
    {H : List ℤ} {Hd : ℕ} (hd : 0 < Hd) (e : scaledEq Hd cf.h cf.Lam H = true)
    (H_le : ∀ t : ℝ, -9 / 10 ≤ t → t < 1 → peval H t / Hd ≤ phi2 t) : Case1Claim phi2 := by
  have hC : (0 : ℝ) < ((Nat.choose 7 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by norm_num)
  have hHf : ∀ t, cf.Hf t = peval H t / Hd := by
    intro t
    unfold Cert.Cert3.Hf
    rw [← peval_eq_sum, div_eq_of_scaledEq hd hL e]
  refine case1Claim_of_threePoint_cut phi2 (H := cf.Hf) hη cf.K cf.m cf.Fm
    (fun k hk => Cert.fmat_psd cf.Lam ((Cert.Cert3.check_parts hc).2.2.2.1 k hk)) ?_ ?_
  · intro u v t hg hu hv ht
    have h := Cert.Cert3.hpt_cut cf hc hg (by rw [han]; exact hu) (by rw [han]; exact hv)
      (by rw [han]; exact ht)
    rw [hn] at h
    have hdiv : (pairEnergy phi2 pentBipyramid + η) / ((Nat.choose 7 2 : ℕ) : ℝ)
        ≤ ((cf.eps : ℝ) / cf.Lam) / ((Nat.choose 7 2 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hC.le
      rw [pairEnergy_phi2_pent]
      exact hε
    linarith
  · intro t h1 h2
    rw [hHf]
    exact H_le t h1 h2

end Riesz2
