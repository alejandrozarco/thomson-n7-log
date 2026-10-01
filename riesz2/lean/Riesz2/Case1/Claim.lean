import Riesz2.Case1.Check
import Riesz2.Bridge
import Riesz2.MinorCase1
/-! Riesz s = 2, Case 1 claim: `ThomsonGen.Case1Claim phi2` from the checked cut certificate
(`Riesz2.Case1Data.cf`, `r2c1_cf_ok`) and the 1-D minorant `H ≤ phi2` on `[-9/10, 1)`
(`Riesz2.Minor.Case1.H_le`, whose `H` is the same rational polynomial over a different denominator:
`scaledEq` identifies them).  Margin `η = eps/Λ - 41/4 = 140737488355/140737488355328 ≈ 10⁻³`. -/

open Real
namespace Riesz2
namespace Case1
open ThomsonN7.Cert ThomsonN7.Cert.Cert3 Minor

theorem lam_pos : 0 < Riesz2.Case1Data.cf.Lam := by decide +kernel

theorem eps_gt : (41 : ℤ) * (Riesz2.Case1Data.cf.Lam : ℤ) < 4 * Riesz2.Case1Data.cf.eps := by
  decide +kernel

theorem h_scaled : scaledEq Riesz2.Minor.Case1.Hd Riesz2.Case1Data.cf.h Riesz2.Case1Data.cf.Lam Riesz2.Minor.Case1.H = true := by
  decide +kernel

/-- **Case 1 (Riesz s = 2).** -/
theorem claim : ThomsonGen.Case1Claim phi2 := by
  have hL : (0 : ℝ) < (Riesz2.Case1Data.cf.Lam : ℝ) := by exact_mod_cast lam_pos
  have hR : (41 : ℝ) * (Riesz2.Case1Data.cf.Lam : ℝ) < 4 * (Riesz2.Case1Data.cf.eps : ℝ) := by
    exact_mod_cast eps_gt
  have h41 : (41 : ℝ) / 4 < (Riesz2.Case1Data.cf.eps : ℝ) / (Riesz2.Case1Data.cf.Lam : ℝ) := by
    rw [div_lt_div_iff₀ (by norm_num) hL]
    linarith
  have han : ((Riesz2.Case1Data.cf.an : ℤ) : ℝ) / (Riesz2.Case1Data.cf.ad : ℝ) = -9 / 10 := by
    show (((-9 : ℤ) : ℝ)) / (((10 : ℕ) : ℝ)) = -9 / 10
    norm_num
  exact case1Claim_of_cert3 Riesz2.Case1Data.cf r2c1_cf_ok rfl han
    (η := (Riesz2.Case1Data.cf.eps : ℝ) / (Riesz2.Case1Data.cf.Lam : ℝ) - 41 / 4) (by linarith)
    (by linarith) lam_pos (by decide) h_scaled (fun t h1 h2 => Riesz2.Minor.Case1.H_le h1 h2)

end Case1
end Riesz2
