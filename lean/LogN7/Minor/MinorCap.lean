import LogLean.MinorCore

open Finset

namespace LogLean.Minor

/-! ## 10. `log Φ` and the contact nodes (copy of `lean/gen/LogPhi.lean`, inserted by `lean/gen/emit_cap.py`) -/

/-- 33-digit bracket for `√5`. -/
theorem sqrt5_bounds :
    (223606797749978969640917366873127 : ℝ) / 10 ^ 32 ≤ √5 ∧
      √5 ≤ (223606797749978969640917366873128 : ℝ) / 10 ^ 32 := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- The base-5 partial sum `S = Σ_{i<38} 5⁻ⁱ/(2i+1)`, bracketed with the tail. -/
theorem S5_bounds :
    (107602235241001009722358308233216 : ℝ) / 10 ^ 32 ≤
        ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) ∧
      (∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1)) + ((1:ℝ)/5) ^ 38 * (5/4) ≤
        (107602235241001009722358308576815 : ℝ) / 10 ^ 32 := by
  constructor <;> norm_num [Finset.sum_range_succ]

/-- `(1 + x)/(1 - x) = Φ²` for `x = √5/5`. -/
theorem ratio_eq_phi_sq :
    (1 + √5 / 5) / (1 - √5 / 5) = ((1 + √5) / 2) ^ 2 := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs : √5 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hne : (1:ℝ) - √5 / 5 ≠ 0 := by linarith
  rw [div_eq_iff hne]
  linear_combination ((√5 - 3) / 20) * h5

/-- `log Φ = ½ log((1+x)/(1-x))`. -/
theorem logPhi_eq_atanh :
    Real.log ((1 + √5) / 2) = 1 / 2 * Real.log ((1 + √5 / 5) / (1 - √5 / 5)) := by
  rw [ratio_eq_phi_sq, Real.log_pow]; push_cast; ring

/-- `x^(2i+1)/(2i+1) = x · (5⁻ⁱ/(2i+1))` for `x = √5/5`. -/
theorem term_eq (i : ℕ) :
    (√5 / 5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) = √5 / 5 * (((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1)) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hx2 : (√5 / 5) ^ 2 = (1:ℝ) / 5 := by rw [div_pow, h5]; norm_num
  rw [pow_succ, pow_mul, hx2]; ring

/-- **`log Φ` to 1.54·10⁻²⁷.** -/
theorem logPhi_bounds :
    (481211825059603447497758913404 : ℝ) / 10 ^ 30 ≤ Real.log ((1 + √5) / 2) ∧
      Real.log ((1 + √5) / 2) ≤ (481211825059603447497758914942 : ℝ) / 10 ^ 30 := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) ≤ √5 := Real.sqrt_nonneg _
  have hs : √5 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hx0 : (0:ℝ) ≤ √5 / 5 := by positivity
  have hx1 : √5 / 5 < 1 := by linarith
  have hlo := Real.sum_range_le_log_div hx0 hx1 38
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 38
  rw [← logPhi_eq_atanh] at hlo hhi
  have hsum : ∑ i ∈ range 38, (√5 / 5) ^ (2 * i + 1) / (2 * (i:ℝ) + 1) =
      √5 / 5 * ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => term_eq i)
  have htail : (√5 / 5) ^ (2 * 38 + 1) / (1 - (√5 / 5) ^ 2) =
      √5 / 5 * (((1:ℝ)/5) ^ 38 * (5/4)) := by
    have hx2 : (√5 / 5) ^ 2 = (1:ℝ) / 5 := by rw [div_pow, h5]; norm_num
    rw [pow_succ, pow_mul, hx2]; ring
  rw [hsum] at hlo hhi
  rw [htail] at hhi
  obtain ⟨sl, sh⟩ := sqrt5_bounds
  obtain ⟨al, ah⟩ := S5_bounds
  set S := ∑ i ∈ range 38, ((1:ℝ)/5) ^ i / (2 * (i:ℝ) + 1) with hS
  set T := ((1:ℝ)/5) ^ 38 * (5/4) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  clear_value S T
  constructor
  · -- x·S ≥ (s_lo/5)·A_lo ≥ L_lo
    have h1 : (223606797749978969640917366873127 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308233216 : ℝ) / 10 ^ 32) ≤ √5 / 5 * S := by
      apply mul_le_mul (by linarith) al (by norm_num) hx0
    have h2 : (481211825059603447497758913404 : ℝ) / 10 ^ 30 ≤
        (223606797749978969640917366873127 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308233216 : ℝ) / 10 ^ 32) := by norm_num
    linarith
  · have h1 : √5 / 5 * S + √5 / 5 * T ≤ (223606797749978969640917366873128 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308576815 : ℝ) / 10 ^ 32) := by
      rw [← mul_add]
      apply mul_le_mul (by linarith) ah (by linarith [al]) (by norm_num)
    have h2 : (223606797749978969640917366873128 : ℝ) / 10 ^ 32 / 5 *
        ((107602235241001009722358308576815 : ℝ) / 10 ^ 32) ≤
        (481211825059603447497758914942 : ℝ) / 10 ^ 30 := by norm_num
    linarith

theorem logPhi_width :
    (481211825059603447497758914942 : ℝ) / 10 ^ 30 - 481211825059603447497758913404 / 10 ^ 30 ≤
      1 / 10 ^ 25 := by norm_num

/-! ### The contact nodes `c₁ = (-1+√5)/4`, `c₂ = (-1-√5)/4` (roots of `4t²+2t-1`). -/

/-- `2 - 2c₁ = (5 - √5)/2 = √5/Φ`, so `log(2 - 2c₁) = ½ log 5 - log Φ`. -/
theorem log_two_sub_two_c1 :
    Real.log (2 - 2 * ((-1 + √5) / 4)) = Real.log 5 / 2 - Real.log ((1 + √5) / 2) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hs : √5 < 5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hphi : (0:ℝ) < (1 + √5) / 2 := by positivity
  have hpos : (0:ℝ) < 2 - 2 * ((-1 + √5) / 4) := by linarith
  have hprod : (2 - 2 * ((-1 + √5) / 4)) * ((1 + √5) / 2) = √5 := by
    linear_combination (-1 / 4) * h5
  have hl : Real.log (2 - 2 * ((-1 + √5) / 4)) + Real.log ((1 + √5) / 2) = Real.log 5 / 2 := by
    rw [← Real.log_mul hpos.ne' hphi.ne', hprod, Real.log_sqrt (by norm_num)]
  linarith

/-- `2 - 2c₂ = (5 + √5)/2 = √5·Φ`, so `log(2 - 2c₂) = ½ log 5 + log Φ`. -/
theorem log_two_sub_two_c2 :
    Real.log (2 - 2 * ((-1 - √5) / 4)) = Real.log 5 / 2 + Real.log ((1 + √5) / 2) := by
  have h5 : √5 ^ 2 = (5:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (0:ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num)
  have hphi : (0:ℝ) < (1 + √5) / 2 := by positivity
  have hprod : 2 - 2 * ((-1 - √5) / 4) = √5 * ((1 + √5) / 2) := by
    linear_combination (-1 / 2) * h5
  rw [hprod, Real.log_mul hs0.ne' hphi.ne', Real.log_sqrt (by norm_num)]



/-! # Cap data: `cert_cap_log_D12_short.json` (generated by lean/gen/emit_cap.py) -/
namespace Cap
set_option profiler true
set_option profiler.threshold 200

def D : ℕ := 409600
def DW : ℕ := 30948500982134506872478105600
theorem D_eq : (D : ℝ) = 409600 := by norm_num [D]
theorem DW_eq : (DW : ℝ) = 30948500982134506872478105600 := by norm_num [DW]

def HA : List ℤ := [10865047368808009728, 10765869866588706816, -11227554594672052224, 6891346639278954496, 1056730577924118144, -16791209210950928384, 2823515197873660928, -12237139788567019520, -3644496825630303744, 35799617972298874880, 13033369599530637312, -16912157691000326144, -8586860697486471931]
def HdA : ℕ := 4611686018427387904
def HB : List ℤ := [-9589731483901991841, 13835058055282163712, 6917529027641081856, 4611686018427387904, 3359706518023620480, 2760014798199577344, 1837829761214876928, -5993720372811641856, -6033094037420731392, 25144197808029815808, 21079073720685170688, -11977509190245355008, -10291052537297954304]
def HdB : ℕ := 27670116110564327424
def HC : List ℤ := [-1023121723052469490449, 1477342765590617847752, 735672149305153675640, 464819520435275038080, 421528534405481758752, 556191658764983009280, 110381856594537267200, -969219557939187548160, -781481941681736417280, 883494289519701688320, 1589439771273645916160, 850215770478245150720, 164239031051290767360]
def HdC : ℕ := 2951479051793528258560
def KAd : List ℤ := [9223372036854775808]
theorem KAd_eval (t : ℝ) : peval KAd t / ((HdA * 10000000000000000 : ℕ) : ℝ) = 2 / 10 ^ 16 := by
  simp only [KAd, HdA, peval]; push_cast; ring
def HAd : List ℤ := addSlack HA 10000000000000000 KAd
def KBd : List ℤ := [55340232221128654848]
theorem KBd_eval (t : ℝ) : peval KBd t / ((HdB * 10000000000000000 : ℕ) : ℝ) = 2 / 10 ^ 16 := by
  simp only [KBd, HdB, peval]; push_cast; ring
def HBd : List ℤ := addSlack HB 10000000000000000 KBd
def KCd : List ℤ := [5902958103587056517120]
theorem KCd_eval (t : ℝ) : peval KCd t / ((HdC * 10000000000000000 : ℕ) : ℝ) = 2 / 10 ^ 16 := by
  simp only [KCd, HdC, peval]; push_cast; ring
def HCd : List ℤ := addSlack HC 10000000000000000 KCd
def KAw : List ℤ := [4611686018427387904, 4611686018427387904]
theorem KAw_eval (t : ℝ) : peval KAw t / ((HdA * 1000 : ℕ) : ℝ) = (t + 1) / 1000 := by
  simp only [KAw, HdA, peval]; push_cast; ring
def HAw : List ℤ := addSlack HA 1000 KAw
def KBw : List ℤ := [0, 0, 0, 0, 27670116110564327424]
theorem KBw_eval (t : ℝ) : peval KBw t / ((HdB * 1000 : ℕ) : ℝ) = t ^ 4 / 1000 := by
  simp only [KBw, HdB, peval]; push_cast; ring
def HBw : List ℤ := addSlack HB 1000 KBw
def KC1w : List ℤ := [431920336526307593428172446209531276125433490921187949453806040750531543040, -2795447139727433510020551804762342630509100321686254920292034138252624527360, 4523128485832663883733241601901871400518358776001584532791311875309106626560]
theorem KC1w_eval (t : ℝ) : peval KC1w t / ((HdC * 15324955408658888583583470271503091836187391221836021760000 : ℕ) : ℝ) = (t - (2988628985596660543901299 : ℝ) / 9671406556917033397649408) ^ 2 / 10 ^ 4 := by
  simp only [KC1w, HdC, peval]; push_cast; ring
def HC1w : List ℤ := addSlack HC 15324955408658888583583470271503091836187391221836021760000 KC1w
def KC2w : List ℤ := [2960426027848190319371758754978068751047131027912107864119859240979398656000, 7318575625560097393753793413971722217681973688706263616664761111841393868800, 4523128485832663883733241601901871400518358776001584532791311875309106626560]
theorem KC2w_eval (t : ℝ) : peval KC2w t / ((HdC * 15324955408658888583583470271503091836187391221836021760000 : ℕ) : ℝ) = (t - (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) ^ 2 / 10 ^ 4 := by
  simp only [KC2w, HdC, peval]; push_cast; ring
def HC2w : List ℤ := addSlack HC 15324955408658888583583470271503091836187391221836021760000 KC2w
def pAw : List Piece := [
  ⟨-409600, -408800, -1, 1, 5, 2, 0, 0, 0, 0, 0, -54916777467707473351141471129, 79228162514264337593543950336⟩]
theorem chainAw : chainOK HAw (HdA * 1000) D pAw (-409600) (-408800) = true := by decide +kernel
def pAd : List Piece := [
  ⟨-408800, -405503, -1, 1, 5, 2, 0, 0, 0, 0, 0, -54916777467707473351141471129, 79228162514264337593543950336⟩]
theorem chainAd : chainOK HAd (HdA * 10000000000000000) D pAd (-408800) (-405503) = true := by decide +kernel
def pBw : List Piece := [
  ⟨-20480, 0, 0, 1, 5, 1, 0, 0, 0, 0, 0, -27458388733853736675570735565, 79228162514264337593543950336⟩,
  ⟨0, 20480, 0, 1, 5, 1, 0, 0, 0, 0, 0, -27458388733853736675570735565, 79228162514264337593543950336⟩]
theorem chainBw : chainOK HBw (HdB * 1000) D pBw (-20480) (20480) = true := by decide +kernel
def pBd1 : List Piece := [
  ⟨-409600, -204800, -97, 128, 5, 0, 2, 2, 6, 0, 0, -49803509026589700453229270948, 79228162514264337593543950336⟩,
  ⟨-204800, -102400, -7, 18, 5, 0, 0, 2, 0, 2, 0, -40471775536182360971323250626, 79228162514264337593543950336⟩,
  ⟨-102400, -20480, -1, 8, 5, 0, 2, 0, 2, 0, 0, -32124255479057406416523745726, 79228162514264337593543950336⟩]
theorem chainBd1 : chainOK HBd (HdB * 10000000000000000) D pBd1 (-409600) (-20480) = true := by decide +kernel
def pBd2 : List Piece := [
  ⟨20480, 225280, 19, 64, 13, 0, 2, 1, 5, 0, 0, -13505493518969816759305772773, 79228162514264337593543950336⟩,
  ⟨225280, 327680, 2, 3, 5, 1, 0, 0, 0, 1, 0, 16062127739528703208261872862, 79228162514264337593543950336⟩,
  ⟨327680, 340480, 13, 16, 5, 0, 1, 0, 3, 0, 0, 38854649728178770142879598265, 79228162514264337593543950336⟩,
  ⟨340480, 366080, 31, 36, 5, 0, 0, 1, 1, 2, 0, 50743017439144996073741718677, 79228162514264337593543950336⟩,
  ⟨366080, 396800, 67, 72, 5, 0, 0, 1, 2, 2, 0, 78201406172998732749312454241, 79228162514264337593543950336⟩]
theorem chainBd2 : chainOK HBd (HdB * 10000000000000000) D pBd2 (20480) (396800) = true := by decide +kernel
def tailBd : Tail := ⟨396800, 0, 0, 0, 4, 0, 0, 109833554935414946702282942255, 79228162514264337593543950336⟩
theorem tailBd_ok : tailBd.check HBd (HdB * 10000000000000000) D = true := by decide +kernel
def pC2L : Piece := ⟨-25656881553953823146142334976, -25037863244976567176723209625, -1001514529799062687068928385, 1237940039285380274899124224, 5, 0, 0, 0, 0, 0, 0, -50940966460540811210031245852, 79228162514264337593543950336⟩
theorem okC2L : pC2L.checkCore HC2w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW = true := by decide +kernel
def pC2R : Piece := ⟨-25037863244976567176723209625, -24418865956804716956919791616, -1001514529799062687068928385, 1237940039285380274899124224, 5, 0, 0, 0, 0, 0, 0, -50940966460540811210031245852, 79228162514264337593543950336⟩
theorem okC2R : pC2R.checkCore HC2w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW = true := by decide +kernel
/-- node constant at `c̃2 = -1001514529799062687068928385/2^90` (|c̃ - c| < 2⁻⁸⁹): `L ≤ φ(c̃)`. -/
theorem nodeC2 : (((-50940966460540811210031245852 : ℤ) : ℝ) / ((79228162514264337593543950336 : ℕ) : ℝ)) ≤
    -(1 / 2) * Real.log (2 * ((((1237940039285380274899124224 : ℕ) : ℝ) - ((-1001514529799062687068928385 : ℤ) : ℝ)) / ((1237940039285380274899124224 : ℕ) : ℝ))) := by
  have e : 2 * ((((1237940039285380274899124224 : ℕ) : ℝ) - ((-1001514529799062687068928385 : ℤ) : ℝ)) / ((1237940039285380274899124224 : ℕ) : ℝ)) =
      2 - 2 * (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224 := by push_cast; ring
  rw [e]
  obtain ⟨sl, sh⟩ := sqrt5_bounds
  have hpc : (0:ℝ) < 2 - 2 * ((-1 - √5) / 4) := by linarith
  have hpt : (0:ℝ) < 2 - 2 * (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224 := by norm_num
  have hsplit : Real.log ((2 - 2 * (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) / (2 - 2 * ((-1 - √5) / 4))) =
      Real.log (2 - 2 * (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) - Real.log (2 - 2 * ((-1 - √5) / 4)) := Real.log_div hpt.ne' hpc.ne'
  have hq := Real.log_le_sub_one_of_pos (div_pos hpt hpc)
  have hY : (2 - 2 * (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) / (2 - 2 * ((-1 - √5) / 4)) - 1 ≤ (137961029759 : ℝ) / 1250000000000000000000000000000000000000 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hpc]; linarith
  have hc := log_two_sub_two_c2
  have hl5 := log5_enc.2
  have hp := logPhi_bounds.2
  have hnum : (((-50940966460540811210031245852 : ℤ) : ℝ) / ((79228162514264337593543950336 : ℕ) : ℝ)) ≤
      -(1 / 2) * ((h5 : ℝ) / DEN / 2 + (240605912529801723748879457471 : ℝ) / 500000000000000000000000000000 + (137961029759 : ℝ) / 1250000000000000000000000000000000000000) := by
    norm_num [h5, DEN]
  have hdiv : (h5 : ℝ) / DEN / 2 = ((h5 : ℝ) / DEN) / 2 := rfl
  linarith

def pC1L : Piece := ⟨8944615465737463520680738816, 9563612753909313740484156800, 382544510156372549619366272, 1237940039285380274899124224, 5, 0, 0, 0, 0, 0, 0, -12815437780932809159462987989, 79228162514264337593543950336⟩
theorem okC1L : pC1L.checkCore HC1w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW = true := by decide +kernel
def pC1R : Piece := ⟨9563612753909313740484156800, 10182631062886569709903282176, 382544510156372549619366272, 1237940039285380274899124224, 5, 0, 0, 0, 0, 0, 0, -12815437780932809159462987989, 79228162514264337593543950336⟩
theorem okC1R : pC1R.checkCore HC1w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW = true := by decide +kernel
/-- node constant at `c̃1 = 382544510156372549619366272/2^90` (|c̃ - c| < 2⁻⁸⁹): `L ≤ φ(c̃)`. -/
theorem nodeC1 : (((-12815437780932809159462987989 : ℤ) : ℝ) / ((79228162514264337593543950336 : ℕ) : ℝ)) ≤
    -(1 / 2) * Real.log (2 * ((((1237940039285380274899124224 : ℕ) : ℝ) - ((382544510156372549619366272 : ℤ) : ℝ)) / ((1237940039285380274899124224 : ℕ) : ℝ))) := by
  have e : 2 * ((((1237940039285380274899124224 : ℕ) : ℝ) - ((382544510156372549619366272 : ℤ) : ℝ)) / ((1237940039285380274899124224 : ℕ) : ℝ)) =
      2 - 2 * (2988628985596660543901299 : ℝ) / 9671406556917033397649408 := by push_cast; ring
  rw [e]
  obtain ⟨sl, sh⟩ := sqrt5_bounds
  have hpc : (0:ℝ) < 2 - 2 * ((-1 + √5) / 4) := by linarith
  have hpt : (0:ℝ) < 2 - 2 * (2988628985596660543901299 : ℝ) / 9671406556917033397649408 := by norm_num
  have hsplit : Real.log ((2 - 2 * (2988628985596660543901299 : ℝ) / 9671406556917033397649408) / (2 - 2 * ((-1 + √5) / 4))) =
      Real.log (2 - 2 * (2988628985596660543901299 : ℝ) / 9671406556917033397649408) - Real.log (2 - 2 * ((-1 + √5) / 4)) := Real.log_div hpt.ne' hpc.ne'
  have hq := Real.log_le_sub_one_of_pos (div_pos hpt hpc)
  have hY : (2 - 2 * (2988628985596660543901299 : ℝ) / 9671406556917033397649408) / (2 - 2 * ((-1 + √5) / 4)) - 1 ≤ (2200260296127 : ℝ) / 2500000000000000000000000000000000000000 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hpc]; linarith
  have hc := log_two_sub_two_c1
  have hl5 := log5_enc.2
  have hp := logPhi_bounds.1
  have hnum : (((-12815437780932809159462987989 : ℤ) : ℝ) / ((79228162514264337593543950336 : ℕ) : ℝ)) ≤
      -(1 / 2) * ((h5 : ℝ) / DEN / 2 - (120302956264900861874439728351 : ℝ) / 250000000000000000000000000000 + (2200260296127 : ℝ) / 2500000000000000000000000000000000000000) := by
    norm_num [h5, DEN]
  have hdiv : (h5 : ℝ) / DEN / 2 = ((h5 : ℝ) / DEN) / 2 := rfl
  linarith

def pCd1 : List Piece := [
  ⟨-409600, -339566, -7, 8, 5, 0, 1, 1, 2, 0, 0, -52360143247148586902185371038, 79228162514264337593543950336⟩]
theorem chainCd1 : chainOK HCd (HdC * 10000000000000000) D pCd1 (-409600) (-339566) = true := by decide +kernel
def pCd2 : List Piece := [
  ⟨-323181, -118381, -9, 16, 5, 0, 0, 2, 3, 0, 0, -45137642281386030712276260787, 79228162514264337593543950336⟩,
  ⟨-118381, 86419, 0, 1, 5, 1, 0, 0, 0, 0, 0, -27458388733853736675570735565, 79228162514264337593543950336⟩,
  ⟨86419, 118381, 1, 4, 5, 0, 1, 0, 1, 0, 0, -16062127739528703208261872863, 79228162514264337593543950336⟩]
theorem chainCd2 : chainOK HCd (HdC * 10000000000000000) D pCd2 (-323181) (118381) = true := by decide +kernel
def pCd3 : List Piece := [
  ⟨134766, 339566, 287, 512, 13, 0, 2, 2, 8, 0, 0, 5113268441117772897912200180, 79228162514264337593543950336⟩,
  ⟨339566, 403200, 29, 32, 5, 0, 1, 0, 4, 0, 0, 66313038462032506818450333829, 79228162514264337593543950336⟩]
theorem chainCd3 : chainOK HCd (HdC * 10000000000000000) D pCd3 (134766) (403200) = true := by decide +kernel
def tailCd : Tail := ⟨403200, 0, 0, 0, 5, 0, 0, 137291943669268683377853677819, 79228162514264337593543950336⟩
theorem tailCd_ok : tailCd.check HCd (HdC * 10000000000000000) D = true := by decide +kernel

/-- rest-chain helper: `H + 2·10⁻¹⁶ ≤ φ` from a chain on `addSlack H 10¹⁶ [2 Hd]`. -/
theorem slack_d {Hn Kn : List ℤ} {Hd : ℕ} (hHd : 0 < Hd) {t : ℝ}
    (hK : peval Kn t / ((Hd * 10000000000000000 : ℕ) : ℝ) = 2 / 10 ^ 16)
    (h : peval (addSlack Hn 10000000000000000 Kn) t / ((Hd * 10000000000000000 : ℕ) : ℝ) ≤ phi t) :
    peval Hn t / Hd + 2 / 10 ^ 16 ≤ phi t := by
  rw [peval_addSlack Hn Hd 10000000000000000 Kn hHd (by norm_num), hK] at h; exact h


/-- **Cap, class A** (contact at `t = -1`, linear). -/
theorem capA {t : ℝ} (h0 : -1 ≤ t) (h1 : t ≤ -99 / 100) :
    peval HA t / HdA ≤ phi t ∧ (phi t - peval HA t / HdA ≤ 1 / 10 ^ 16 → |t + 1| ≤ 1 / 1650) := by
  have hD := D_eq
  rcases lt_or_ge t (-511 / 512) with ha | ha
  · have h := chain_sound HAw (HdA * 1000) D (by decide) (by decide) pAw (-409600) (-408800) chainAw t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith)
    simp only [HAw] at h
    rw [peval_addSlack HA HdA 1000 KAw (by decide) (by norm_num), KAw_eval] at h
    refine ⟨by linarith, fun hδ => ?_⟩
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h := chain_sound HAd (HdA * 10000000000000000) D (by decide) (by decide) pAd (-408800) (-405503) chainAd t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith)
    have h' := slack_d (by decide) (KAd_eval t) h
    exact ⟨by linarith, fun hδ => by exfalso; linarith⟩

/-- **Cap, class B** (contact at `t = 0`, quartic). -/
theorem capB {t : ℝ} (h0 : -1 ≤ t) (h1 : t < 1) :
    peval HB t / HdB ≤ phi t ∧ (phi t - peval HB t / HdB ≤ 1 / 10 ^ 16 → |t| ≤ 1 / 1650) := by
  have hD := D_eq
  have rest : ∀ h : peval HBd t / ((HdB * 10000000000000000 : ℕ) : ℝ) ≤ phi t,
      peval HB t / HdB ≤ phi t ∧ (phi t - peval HB t / HdB ≤ 1 / 10 ^ 16 → |t| ≤ 1 / 1650) := by
    intro h
    have h' := slack_d (by decide) (KBd_eval t) h
    exact ⟨by linarith, fun hδ => by exfalso; linarith⟩
  rcases lt_or_ge t (-1 / 20) with ha | ha
  · exact rest (chain_sound HBd _ D (by decide) (by decide) pBd1 (-409600) (-20480) chainBd1 t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith))
  rcases lt_or_ge t (1 / 20) with hb | hb
  · have h := chain_sound HBw (HdB * 1000) D (by decide) (by decide) pBw (-20480) (20480) chainBw t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith)
    simp only [HBw] at h
    rw [peval_addSlack HB HdB 1000 KBw (by decide) (by norm_num), KBw_eval] at h
    have h4 : 0 ≤ t ^ 4 := by positivity
    refine ⟨by linarith, fun hδ => ?_⟩
    exact tube4 (κ := 1 / 1000) (by norm_num) (by norm_num) (by linarith) hδ (by norm_num)
  rcases lt_or_ge t ((31 : ℝ) / 32) with hc | hc
  · exact rest (chain_sound HBd _ D (by decide) (by decide) pBd2 (20480) (396800) chainBd2 t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith))
  · exact rest (Tail.sound HBd _ D (by decide) (by decide) tailBd tailBd_ok (by rw [show tailBd.T0 = 396800 from rfl, hD]; push_cast; linarith) h1)


/-- **Cap, class C** (contacts at `c₁,₂ = (-1 ± √5)/4`, quadratic). -/
theorem capC {t : ℝ} (h0 : -1 ≤ t) (h1 : t < 1) :
    peval HC t / HdC ≤ phi t ∧ (phi t - peval HC t / HdC ≤ 1 / 10 ^ 16 →
      |t - (-1 + √5) / 4| ≤ 1 / 1650 ∨ |t - (-1 - √5) / 4| ≤ 1 / 1650) := by
  have hD := D_eq
  have hDW := DW_eq
  have rest : ∀ h : peval HCd t / ((HdC * 10000000000000000 : ℕ) : ℝ) ≤ phi t,
      peval HC t / HdC ≤ phi t ∧ (phi t - peval HC t / HdC ≤ 1 / 10 ^ 16 →
        |t - (-1 + √5) / 4| ≤ 1 / 1650 ∨ |t - (-1 - √5) / 4| ≤ 1 / 1650) := by
    intro h
    have h' := slack_d (by decide) (KCd_eval t) h
    exact ⟨by linarith, fun hδ => by exfalso; linarith⟩
  rcases lt_or_ge t ((-169783 : ℝ) / 204800) with hr1 | hr1
  · exact rest (chain_sound HCd _ D (by decide) (by decide) pCd1 (-409600) (-339566) chainCd1 t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith))
  rcases lt_or_ge t ((-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) with h2L | h2L
  · have h := Piece.sound_of_node HC2w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW (by decide) (by decide) pC2L okC2L
      (by rw [show pC2L.Ln = -50940966460540811210031245852 from rfl, show pC2L.Ld = 79228162514264337593543950336 from rfl,
            show pC2L.gd = 1237940039285380274899124224 from rfl, show pC2L.gn = -1001514529799062687068928385 from rfl]; exact nodeC2)
      (t := t) (by rw [hDW, show pC2L.A = -25656881553953823146142334976 from rfl]; push_cast; linarith)
      (by rw [hDW, show pC2L.B = -25037863244976567176723209625 from rfl]; push_cast; linarith)
    simp only [HC2w] at h
    rw [peval_addSlack HC HdC 15324955408658888583583470271503091836187391221836021760000 KC2w (by decide) (by norm_num), KC2w_eval] at h
    have h2 : 0 ≤ (t - (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) ^ 2 := by positivity
    refine ⟨by linarith, fun hδ => Or.inr ?_⟩
    have ht := tube2 (κ := 1 / 10 ^ 4) (τ := (309485009821345068724780231 : ℝ) / 510650266205219363395888742400) (x := t - (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) (by norm_num) (by norm_num)
      (by linarith) hδ (by norm_num)
    obtain ⟨sl, sh⟩ := sqrt5_bounds
    rw [abs_le] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  rcases lt_or_ge t ((-323181 : ℝ) / 409600) with h2R | h2R
  · have h := Piece.sound_of_node HC2w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW (by decide) (by decide) pC2R okC2R
      (by rw [show pC2R.Ln = -50940966460540811210031245852 from rfl, show pC2R.Ld = 79228162514264337593543950336 from rfl,
            show pC2R.gd = 1237940039285380274899124224 from rfl, show pC2R.gn = -1001514529799062687068928385 from rfl]; exact nodeC2)
      (t := t) (by rw [hDW, show pC2R.A = -25037863244976567176723209625 from rfl]; push_cast; linarith)
      (by rw [hDW, show pC2R.B = -24418865956804716956919791616 from rfl]; push_cast; linarith)
    simp only [HC2w] at h
    rw [peval_addSlack HC HdC 15324955408658888583583470271503091836187391221836021760000 KC2w (by decide) (by norm_num), KC2w_eval] at h
    have h2 : 0 ≤ (t - (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) ^ 2 := by positivity
    refine ⟨by linarith, fun hδ => Or.inr ?_⟩
    have ht := tube2 (κ := 1 / 10 ^ 4) (τ := (309485009821345068724780231 : ℝ) / 510650266205219363395888742400) (x := t - (-1001514529799062687068928385 : ℝ) / 1237940039285380274899124224) (by norm_num) (by norm_num)
      (by linarith) hδ (by norm_num)
    obtain ⟨sl, sh⟩ := sqrt5_bounds
    rw [abs_le] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  rcases lt_or_ge t ((118381 : ℝ) / 409600) with hr2 | hr2
  · exact rest (chain_sound HCd _ D (by decide) (by decide) pCd2 (-323181) (118381) chainCd2 t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith))
  rcases lt_or_ge t ((2988628985596660543901299 : ℝ) / 9671406556917033397649408) with h1L | h1L
  · have h := Piece.sound_of_node HC1w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW (by decide) (by decide) pC1L okC1L
      (by rw [show pC1L.Ln = -12815437780932809159462987989 from rfl, show pC1L.Ld = 79228162514264337593543950336 from rfl,
            show pC1L.gd = 1237940039285380274899124224 from rfl, show pC1L.gn = 382544510156372549619366272 from rfl]; exact nodeC1)
      (t := t) (by rw [hDW, show pC1L.A = 8944615465737463520680738816 from rfl]; push_cast; linarith)
      (by rw [hDW, show pC1L.B = 9563612753909313740484156800 from rfl]; push_cast; linarith)
    simp only [HC1w] at h
    rw [peval_addSlack HC HdC 15324955408658888583583470271503091836187391221836021760000 KC1w (by decide) (by norm_num), KC1w_eval] at h
    have h2 : 0 ≤ (t - (2988628985596660543901299 : ℝ) / 9671406556917033397649408) ^ 2 := by positivity
    refine ⟨by linarith, fun hδ => Or.inl ?_⟩
    have ht := tube2 (κ := 1 / 10 ^ 4) (τ := (309485009821345068724780231 : ℝ) / 510650266205219363395888742400) (x := t - (2988628985596660543901299 : ℝ) / 9671406556917033397649408) (by norm_num) (by norm_num)
      (by linarith) hδ (by norm_num)
    obtain ⟨sl, sh⟩ := sqrt5_bounds
    rw [abs_le] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  rcases lt_or_ge t ((67383 : ℝ) / 204800) with h1R | h1R
  · have h := Piece.sound_of_node HC1w (HdC * 15324955408658888583583470271503091836187391221836021760000) DW (by decide) (by decide) pC1R okC1R
      (by rw [show pC1R.Ln = -12815437780932809159462987989 from rfl, show pC1R.Ld = 79228162514264337593543950336 from rfl,
            show pC1R.gd = 1237940039285380274899124224 from rfl, show pC1R.gn = 382544510156372549619366272 from rfl]; exact nodeC1)
      (t := t) (by rw [hDW, show pC1R.A = 9563612753909313740484156800 from rfl]; push_cast; linarith)
      (by rw [hDW, show pC1R.B = 10182631062886569709903282176 from rfl]; push_cast; linarith)
    simp only [HC1w] at h
    rw [peval_addSlack HC HdC 15324955408658888583583470271503091836187391221836021760000 KC1w (by decide) (by norm_num), KC1w_eval] at h
    have h2 : 0 ≤ (t - (2988628985596660543901299 : ℝ) / 9671406556917033397649408) ^ 2 := by positivity
    refine ⟨by linarith, fun hδ => Or.inl ?_⟩
    have ht := tube2 (κ := 1 / 10 ^ 4) (τ := (309485009821345068724780231 : ℝ) / 510650266205219363395888742400) (x := t - (2988628985596660543901299 : ℝ) / 9671406556917033397649408) (by norm_num) (by norm_num)
      (by linarith) hδ (by norm_num)
    obtain ⟨sl, sh⟩ := sqrt5_bounds
    rw [abs_le] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  rcases lt_or_ge t ((63 : ℝ) / 64) with hr3 | hr3
  · exact rest (chain_sound HCd _ D (by decide) (by decide) pCd3 (134766) (403200) chainCd3 t
      (by rw [hD]; push_cast; linarith) (by rw [hD]; push_cast; linarith))
  · exact rest (Tail.sound HCd _ D (by decide) (by decide) tailCd tailCd_ok (by rw [show tailCd.T0 = 403200 from rfl, hD]; push_cast; linarith) h1)

end Cap

end LogLean.Minor
