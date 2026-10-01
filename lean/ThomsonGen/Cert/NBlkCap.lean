import ThomsonGen.Generic.Glue
import ThomsonGen.Cert.NBlk

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`capSpec_of_tcertN` ← `Glue.capSpec_of_tcert`. -/

/-!
# Non-sharp cap specification from a facially reduced certificate (`TCertN`)

`capSpec_of_tcertN` is `ThomsonGen.capSpec_of_tcert` with the PSD inputs of `checkMeta` replaced by
`Cert.TCertN.sound_lo` (positivity by congruence, `NBlk.lean`): the kernel inputs are
`E_φ(P) ≤ ef + δ` and the coercive one-dimensional facts with window `τ ≤ τ₀`.  Used by the log
cap (re-rounded, not exactly sharp, δ = 10⁻¹⁶).  `tcertN_bound_cap` is the bound of `sound_lo` in the
`cls3` shape (same statement as `Riesz2.tcertN_bound_cap`).  New file next to `NBlk.lean`; no existing
declaration is changed.  (Log port, 2026-09-30.)
-/

open Real

namespace ThomsonGen

open ThomsonN7 ThomsonN7.Base
open scoped InnerProductSpace

variable (φ : ℝ → ℝ)

/-- The bound of `TCertN.sound_lo` in the `cls3` shape. -/
theorem tcertN_bound_cap (cf : Cert.TCertN) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.toTCert.alo = -1) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ cf.toTCert.ahi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      cf.toTCert.ef ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
        cls3 cf.toTCert.HAf cf.toTCert.HBf cf.toTCert.HCf i j ⟪y i, y j⟫_ℝ := by
  intro y hy hhi hmin
  have hlo : cf.toTCert.alo ≤ ⟪y 0, y 1⟫_ℝ := by
    rw [halo]; exact neg_one_le_inner_of_unit (hy.1 0) (hy.1 1)
  rw [← sum_H7_eq_sum_cls3 cf.toTCert.HAf cf.toTCert.HBf cf.toTCert.HCf
    (fun i j => ⟪y i, y j⟫_ℝ)]
  exact Cert.TCertN.sound_lo cf hm hA hB hG y hy.1 (fun i j hij => hlo.trans (hmin i j hij))
    ⟨hlo, hhi⟩

/-- **Cap specification from a facially reduced packed certificate** (non-sharp: `δ`, `τ`). -/
theorem capSpec_of_tcertN (cf : Cert.TCertN) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.toTCert.alo = -1) {τ₀ δ τ : ℝ} (hτ : τ ≤ τ₀)
    (hE : pairEnergy φ pentBipyramid ≤ cf.toTCert.ef + δ)
    (hHA : ∀ t, -1 ≤ t → t ≤ cf.toTCert.ahi →
      cf.toTCert.HAf t ≤ φ t ∧ (φ t - cf.toTCert.HAf t ≤ δ → |t + 1| ≤ τ))
    (hHB : ∀ t, -1 ≤ t → t < 1 →
      cf.toTCert.HBf t ≤ φ t ∧ (φ t - cf.toTCert.HBf t ≤ δ → |t| ≤ τ))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      cf.toTCert.HCf t ≤ φ t ∧ (φ t - cf.toTCert.HCf t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ)) :
    CapSpec φ τ₀ cf.toTCert.ahi :=
  ⟨cf.toTCert.ef, δ, τ, cf.toTCert.HAf, cf.toTCert.HBf, cf.toTCert.HCf, hτ, hE,
    tcertN_bound_cap cf hm hA hB hG halo, hHA, hHB, hHC⟩

end ThomsonGen
