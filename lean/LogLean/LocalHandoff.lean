import LogLean.LocalBridge
import ThomsonGen.Gauge

/-!
# LocalHandoff: Lemma L′ at upstream's `pentBipyramid`, hypothesis-free

`LocalMain.pent_local_min_sup_log` takes the gauge (Procrustes) step as a hypothesis; here it is discharged by
upstream's kernel-free `ThomsonN7.Reg.exists_gauge` (module `ThomsonGen.Gauge`), and the K-coordinate bipyramid
`Pbip` is replaced by upstream's `ThomsonN7.pentBipyramid` through `LocalBridge.Pbip_eq_pent`
(`LocalBridge.pentBipyramid` is upstream's definition verbatim, hence `rfl`).  `logEnergy` is `LocalMain.logEnergy`,
the definition of `LogN7/Challenge.lean` verbatim.  This is the analogue of upstream `pent_local_min_sup` (radius 1/300).
-/

namespace LocalHandoff

theorem pent_eq : LocalMain.Pbip = ThomsonN7.pentBipyramid :=
  LocalBridge.Pbip_eq_pent.trans rfl

theorem gauge_Pbip (y : Fin 7 → LocalMain.R3) : ∃ g : LocalMain.R3 ≃ₗᵢ[ℝ] LocalMain.R3,
    (∀ a b : Fin 3, ∑ i, LocalMain.Pbip i a * (g (y i)) b = ∑ i, LocalMain.Pbip i b * (g (y i)) a) ∧
    ∑ i, ‖g (y i) - LocalMain.Pbip i‖ ^ 2 ≤ ∑ i, ‖y i - LocalMain.Pbip i‖ ^ 2 :=
  ThomsonN7.Reg.exists_gauge LocalMain.Pbip y

/-- **Lemma L′, handoff form** (no hypotheses beyond the statement): every configuration in `SphereConfig 7`
within sup-distance `1/300` of the pentagonal bipyramid has log energy at least that of the bipyramid, with
equality only on its `O(3)`-orbit. -/
theorem pent_local_min_sup_log {z : Fin 7 → ThomsonN7.R3} (hz : z ∈ ThomsonN7.SphereConfig 7)
    (hclose : ∀ i, ‖z i - ThomsonN7.pentBipyramid i‖ ≤ 1 / 300) :
    LocalMain.logEnergy ThomsonN7.pentBipyramid ≤ LocalMain.logEnergy z ∧
      (LocalMain.logEnergy z = LocalMain.logEnergy ThomsonN7.pentBipyramid →
        ∃ g : ThomsonN7.R3 ≃ₗᵢ[ℝ] ThomsonN7.R3, ∀ i, z i = g (ThomsonN7.pentBipyramid i)) := by
  have hunit : ∀ i, ‖z i‖ = 1 := hz.1
  rw [← pent_eq] at hclose ⊢
  exact LocalMain.pent_local_min_sup_log gauge_Pbip hunit hclose

end LocalHandoff

#print axioms LocalBridge.Pbip_eq_pent
#print axioms LocalHandoff.pent_local_min_sup_log
