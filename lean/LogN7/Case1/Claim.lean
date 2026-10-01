import LogN7.Case1.Check
import LogN7.Bridge
import LogN7.Minor.MinorCase1
/-! Log kernel, Case 1 claim: `ThomsonGen.Case1Claim φ₀` from the checked cut certificate
(`LogN7.Case1Data.cf`, `r2c1_cf_ok`) and the 1-D minorant `H ≤ φ₀` on `[-9/10, 1)`
(`LogLean.Minor.CellCase1.HH_le_phi`, the same rational polynomial over another denominator: `scaledEq`).
Margin `η = eps/Λ − Ê ≈ 5·10⁻⁴`, where `Ê ≥ E(P)` is the enclosure `pairEnergy_pent_le`. -/

open Real
namespace LogN7
namespace Case1
open ThomsonN7 ThomsonN7.Cert ThomsonN7.Cert.Cert3 ThomsonGen

theorem lam_eq : LogN7.Case1Data.cf.Lam = 997120304160296103051264000 := rfl
theorem eps_eq : LogN7.Case1Data.cf.eps = -8158416256828131169075200000 := rfl
theorem an_eq : LogN7.Case1Data.cf.an = -9 := rfl
theorem ad_eq : LogN7.Case1Data.cf.ad = 10 := rfl
theorem lam_pos : 0 < LogN7.Case1Data.cf.Lam := by rw [lam_eq]; norm_num

theorem h_scaled : scaledEq LogLean.Minor.CellCase1.HdH LogN7.Case1Data.cf.h LogN7.Case1Data.cf.Lam
    LogLean.Minor.CellCase1.HH = true := by
  decide +kernel

theorem hD : (LogLean.Minor.CellCase1.D : ℝ) = 409600 := by norm_num [LogLean.Minor.CellCase1.D]

/-- **Case 1 (log kernel).** -/
theorem claim : Case1Claim LogLean.Minor.phi := by
  have hEP := pairEnergy_pent_le
  have hq : ((LogN7.Case1Data.cf.eps : ℤ) : ℝ) / ((LogN7.Case1Data.cf.Lam : ℕ) : ℝ) =
      (-8158416256828131169075200000 : ℝ) / 997120304160296103051264000 := by
    rw [eps_eq, lam_eq]; push_cast; ring
  have hm : -(6 * (69314718055994530941723212145717 : ℝ) + 5 / 2 * 160943791243410037460075933322218) /
      10 ^ 32 < (-8158416256828131169075200000 : ℝ) / 997120304160296103051264000 := by norm_num
  have han : ((LogN7.Case1Data.cf.an : ℤ) : ℝ) / (LogN7.Case1Data.cf.ad : ℝ) = -9 / 10 := by
    rw [an_eq, ad_eq]; norm_num
  refine case1Claim_of_cert3 LogN7.Case1Data.cf r2c1_cf_ok rfl han
    (η := (-8158416256828131169075200000 : ℝ) / 997120304160296103051264000 -
      -(6 * (69314718055994530941723212145717 : ℝ) + 5 / 2 * 160943791243410037460075933322218) / 10 ^ 32)
    (by linarith) (by rw [hq]; linarith) lam_pos (by decide) h_scaled ?_
  intro t h1 h2
  exact LogLean.Minor.CellCase1.HH_le_phi (by rw [hD]; push_cast; linarith) h2

end Case1
end LogN7
