/-
Riesz2/Sharp.lean — the sharp-cap route (exact contact, no coercivity window, no local lemma).

Copy of the "Sharp caps" section of `ThomsonGen/Generic/{Energy,Glue}.lean`, placed in namespace
`Riesz2` (the two copies are independent; either can be used).

A sharp cap specification is a `CapSpec` with `τ₀ = τ = δ = 0` and `e = E(P)`: equality forces every
`⟪y i, y j⟫` to be a node, ring rigidity (`T4.ring_rigid`) applies at `τ = 0`, and `LocalMinAt φ 0` is
free (`‖z i - P i‖ ≤ 0` forces `z = P`).
-/
import ThomsonGen.Generic.Glue
import ThomsonGen.Cert.NBlk

open Real

namespace Riesz2

open ThomsonN7 ThomsonN7.Base ThomsonGen
open scoped InnerProductSpace

variable (φ : ℝ → ℝ)

/-- **Radius `0` is free for every kernel**: `‖z i - P i‖ ≤ 0` forces `z = P`. -/
theorem localMinAt_zero : LocalMinAt φ 0 := by
  intro z hz hzd
  have hzP : z = pentBipyramid := funext fun i => sub_eq_zero.1 (norm_le_zero_iff.1 (hzd i))
  subst hzP
  exact ⟨le_rfl, fun _ => ⟨LinearIsometryEquiv.refl ℝ R3, fun i => by simp⟩⟩

/-- **Sharp cap specification**: typed bound `E(P) ≤ ∑ H_cls` on the cap, minorants below `φ` with
exact contact sets `{-1}`, `{0}`, `{c1, c2}`. -/
def CapSpecSharp (a0 : ℝ) : Prop :=
  ∃ (HA HB HC : ℝ → ℝ),
    (∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      pairEnergy φ pentBipyramid ≤
        ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ∧
    (∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ φ t ∧ (HA t = φ t → t = -1)) ∧
    (∀ t, -1 ≤ t → t < 1 → HB t ≤ φ t ∧ (HB t = φ t → t = 0)) ∧
    (∀ t, -1 ≤ t → t < 1 → HC t ≤ φ t ∧ (HC t = φ t → t = c1 ∨ t = c2))

/-- A sharp cap specification is a cap specification with `τ₀ = τ = δ = 0`, `e = E(P)`. -/
theorem capSpec_of_sharp {a0 : ℝ} (h : CapSpecSharp φ a0) : CapSpec φ 0 a0 := by
  obtain ⟨HA, HB, HC, hTB, hA, hB, hC⟩ := h
  refine ⟨pairEnergy φ pentBipyramid, 0, 0, HA, HB, HC, le_rfl, by simp, hTB, ?_, ?_, ?_⟩
  · intro t h1 h2
    refine ⟨(hA t h1 h2).1, fun hs => ?_⟩
    have ht := (hA t h1 h2).2 (le_antisymm (hA t h1 h2).1 (by linarith))
    rw [ht]; norm_num
  · intro t h1 h2
    refine ⟨(hB t h1 h2).1, fun hs => ?_⟩
    have ht := (hB t h1 h2).2 (le_antisymm (hB t h1 h2).1 (by linarith))
    rw [ht]; norm_num
  · intro t h1 h2
    refine ⟨(hC t h1 h2).1, fun hs => ?_⟩
    rcases (hC t h1 h2).2 (le_antisymm (hC t h1 h2).1 (by linarith)) with ht | ht
    · left; rw [ht]; simp
    · right; rw [ht]; simp

/-- **Generic assembly, sharp-cap variant**: no tube width and no local lemma. -/
theorem seven_of_specs_sharp (hcase1 : Case1Claim φ) (a : ℕ → ℝ) (K : ℕ) (hK : -9 / 10 ≤ a K)
    (hcap : CapSpecSharp φ (a 0)) (hslab : ∀ k, k < K → SlabSpec φ (a k) (a (k + 1))) :
    ThomsonGen.Main φ :=
  seven_of_specs φ (τ₀ := 0) (by norm_num) (by rw [mul_zero]; exact localMinAt_zero φ) hcase1
    a K hK (capSpec_of_sharp φ hcap) hslab

/-- **Sharp cap specification from a packed certificate** (`E_φ(P) ≤ ef`, exact contact sets). -/
theorem capSpecSharp_of_tcert (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) (hE : pairEnergy φ pentBipyramid ≤ cf.ef)
    (hHA : ∀ t, -1 ≤ t → t ≤ cf.ahi → cf.HAf t ≤ φ t ∧ (cf.HAf t = φ t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 → cf.HBf t ≤ φ t ∧ (cf.HBf t = φ t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 → cf.HCf t ≤ φ t ∧ (cf.HCf t = φ t → t = c1 ∨ t = c2)) :
    CapSpecSharp φ cf.ahi :=
  ⟨cf.HAf, cf.HBf, cf.HCf,
    fun y hy hle hmin => hE.trans (tcert_bound_cap cf hm hA hB hG halo y hy hle hmin),
    hHA, hHB, hHC⟩

/-! ### Facially reduced certificates (`Cert.TCertN`, `ThomsonGen/Cert/NBlk.lean`) -/

/-- The bound of `TCertN.sound_lo` in the `cls3` shape (as `tcert_bound_cap`). -/
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

/-- **Sharp cap specification from a facially reduced packed certificate.** -/
theorem capSpecSharp_of_tcertN (cf : Cert.TCertN) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.toTCert.alo = -1) (hE : pairEnergy φ pentBipyramid ≤ cf.toTCert.ef)
    (hHA : ∀ t, -1 ≤ t → t ≤ cf.toTCert.ahi →
      cf.toTCert.HAf t ≤ φ t ∧ (cf.toTCert.HAf t = φ t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 → cf.toTCert.HBf t ≤ φ t ∧ (cf.toTCert.HBf t = φ t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      cf.toTCert.HCf t ≤ φ t ∧ (cf.toTCert.HCf t = φ t → t = c1 ∨ t = c2)) :
    CapSpecSharp φ cf.toTCert.ahi :=
  ⟨cf.toTCert.HAf, cf.toTCert.HBf, cf.toTCert.HCf,
    fun y hy hle hmin => hE.trans (tcertN_bound_cap cf hm hA hB hG halo y hy hle hmin),
    hHA, hHB, hHC⟩

end Riesz2
