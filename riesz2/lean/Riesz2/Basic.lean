/-
Riesz2/Basic.lean — the Riesz s = 2 energy, its kernel form, and E(P) = 41/4 (RIESZ2_LEAN_PLAN.md §1).

* `riesz2Energy x = ∑_{i<j} (‖x i - x j‖²)⁻¹` (the trusted definition; the theorems quantify over
  `SphereConfig 7`, i.e. unit vectors AND pairwise distinct points, exactly as upstream: with Lean's
  `1/0 = 0` the statement would be false for coincident points — audit F1).
* On unit vectors `‖x - y‖² = 2 - 2⟪x, y⟫`, so `riesz2Energy x = ∑_{i<j} phi2 ⟪x i, x j⟫`
  (`= ThomsonGen.pairEnergy phi2 x` definitionally).
* `riesz2Energy pentBipyramid = 41/4`: one pair at `-1`, ten at `0`, five each at `c1, c2`
  (`cos 72°`, `cos 144°`), and `phi2 c1 + phi2 c2 = 1`.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `riesz2Energy` ← `coulombEnergy`; `riesz2Energy_eq_sum_phi2` ← `Base.coulombEnergy_eq_sum_phi`;
  `norm_sub_sq_inv_eq_phi2` ← `Base.norm_sub_inv_eq_phi`;
  `sum_Ioi_seven` ← `Reg.sum_Ioi_seven` (also `RegB.sum_pairs_seven`).
-/
import ThomsonGen.Base
import Riesz2.MinorCore

open Real

namespace Riesz2

open ThomsonN7 ThomsonN7.Base
open Minor (phi2)

/-- Riesz `s = 2` energy `∑_{i<j} ‖x i - x j‖⁻²`. -/
noncomputable def riesz2Energy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, (‖x i - x j‖ ^ 2)⁻¹

lemma norm_sub_sq_inv_eq_phi2 {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (‖x - y‖ ^ 2)⁻¹ = phi2 (inner ℝ x y) := by
  rw [norm_sub_sq_of_unit hx hy]
  unfold Minor.phi2
  rw [one_div]

/-- For unit vectors the energy is a sum of `phi2` of the pairwise inner products
(this is `ThomsonGen.pairEnergy phi2 x`). -/
lemma riesz2Energy_eq_sum_phi2 {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    riesz2Energy x = ∑ i, ∑ j ∈ Finset.Ioi i, phi2 (inner ℝ (x i) (x j)) := by
  unfold riesz2Energy
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    norm_sub_sq_inv_eq_phi2 (hx i) (hx j)

/-- The 21 pairs of `Fin 7` (pattern of upstream `coulombEnergy_seven`). -/
lemma sum_Ioi_seven (f : Fin 7 → Fin 7 → ℝ) : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, f i j =
    f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 + f 0 6
    + f 1 2 + f 1 3 + f 1 4 + f 1 5 + f 1 6
    + f 2 3 + f 2 4 + f 2 5 + f 2 6
    + f 3 4 + f 3 5 + f 3 6
    + f 4 5 + f 4 6 + f 5 6 := by
  have hI : ∀ i : Fin 7, ∑ j ∈ Finset.Ioi i, f i j = ∑ j, if i < j then f i j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp only [hI, Fin.sum_univ_seven]
  simp
  ring

/-- Inner product of two ring points as a cosine of the angle difference. -/
lemma inner_pent_ring {i j : Fin 7} (hi : (i : ℕ) < 5) (hj : (j : ℕ) < 5) :
    inner ℝ (pentBipyramid i) (pentBipyramid j) =
      cos (2 * π * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / 5) := by
  rw [pent_of_lt hi, pent_of_lt hj, inner_cyl]
  first
  | (simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
     rw [← cos_neg]; congr 1; ring)
  | (rw [← cos_neg]; simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
     congr 1; ring)
  | (simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, cos_sub]
     rw [← cos_neg, cos_neg]; simp only [cos_sub]; ring)

lemma phi2_zero : phi2 0 = 1 / 2 := by unfold Minor.phi2; norm_num

lemma phi2_neg_one : phi2 (-1) = 1 / 4 := by unfold Minor.phi2; norm_num

lemma sqrt5_lt_three : √5 < 3 := by
  first
  | (rw [Real.sqrt_lt' (by norm_num)]; norm_num)
  | (have h := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
     nlinarith [Real.sqrt_nonneg 5])

/-- `φ₂(c₁) + φ₂(c₂) = 1` (`= (5+√5)/10 + (5-√5)/10`). -/
lemma phi2_c1_add_c2 : phi2 c1 + phi2 c2 = 1 := by
  unfold Minor.phi2 c1 c2
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs := sqrt5_lt_three
  have hs0 := Real.sqrt_nonneg 5
  have h1 : (2 - 2 * ((√5 - 1) / 4)) ≠ 0 := by
    apply ne_of_gt; linarith
  have h2 : (2 - 2 * (-(1 + √5) / 4)) ≠ 0 := by
    apply ne_of_gt; linarith
  rw [div_add_div _ _ h1 h2, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
  first
  | linear_combination (1 / 4 : ℝ) * h5
  | linear_combination (-1 / 4 : ℝ) * h5
  | nlinarith [h5]

/-- `4t² + 2t - 1 = 4 (t - c1) (t - c2)`. -/
lemma quad_eq_c1_c2 (t : ℝ) : 4 * t ^ 2 + 2 * t - 1 = 4 * (t - c1) * (t - c2) := by
  unfold c1 c2
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  first
  | linear_combination (-1 / 4 : ℝ) * h5
  | linear_combination (1 / 4 : ℝ) * h5
  | nlinarith [h5]

/-- The exact contact set of the cap class `C`: the roots of `4t² + 2t - 1` are `c1, c2`. -/
lemma eq_c1_or_c2_of_quad {t : ℝ} (h : 4 * t ^ 2 + 2 * t - 1 = 0) : t = c1 ∨ t = c2 := by
  rw [quad_eq_c1_c2] at h
  rcases mul_eq_zero.mp h with h4 | h2
  · rcases mul_eq_zero.mp h4 with h0 | h1
    · norm_num at h0
    · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h2)

/-- **E(P) = 41/4.** -/
theorem riesz2Energy_pent : riesz2Energy pentBipyramid = 41 / 4 := by
  rw [riesz2Energy_eq_sum_phi2 pent_norm, sum_Ioi_seven]
  -- ring–ring pairs: angle differences 1, 4 ↦ c1; 2, 3 ↦ c2
  have i01 : inner ℝ (pentBipyramid 0) (pentBipyramid 1) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num
  have i04 : inner ℝ (pentBipyramid 0) (pentBipyramid 4) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_8pi5]; congr 1; norm_num <;> ring
  have i12 : inner ℝ (pentBipyramid 1) (pentBipyramid 2) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num <;> ring
  have i23 : inner ℝ (pentBipyramid 2) (pentBipyramid 3) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num <;> ring
  have i34 : inner ℝ (pentBipyramid 3) (pentBipyramid 4) = c1 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_2pi5]; congr 1; norm_num <;> ring
  have i02 : inner ℝ (pentBipyramid 0) (pentBipyramid 2) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_4pi5]; congr 1; norm_num <;> ring
  have i03 : inner ℝ (pentBipyramid 0) (pentBipyramid 3) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_6pi5]; congr 1; norm_num <;> ring
  have i13 : inner ℝ (pentBipyramid 1) (pentBipyramid 3) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_4pi5]; congr 1; norm_num <;> ring
  have i14 : inner ℝ (pentBipyramid 1) (pentBipyramid 4) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_6pi5]; congr 1; norm_num <;> ring
  have i24 : inner ℝ (pentBipyramid 2) (pentBipyramid 4) = c2 := by
    rw [inner_pent_ring (by decide) (by decide), ← cos_4pi5]; congr 1; norm_num <;> ring
  rw [i01, i02, i03, i04, i12, i13, i14, i23, i24, i34,
    pent_inner_north (i := 0) (by decide), pent_inner_north (i := 1) (by decide),
    pent_inner_north (i := 2) (by decide), pent_inner_north (i := 3) (by decide),
    pent_inner_north (i := 4) (by decide), pent_inner_south (i := 0) (by decide),
    pent_inner_south (i := 1) (by decide), pent_inner_south (i := 2) (by decide),
    pent_inner_south (i := 3) (by decide), pent_inner_south (i := 4) (by decide),
    pent_inner_poles, phi2_zero, phi2_neg_one]
  linarith [phi2_c1_add_c2]

end Riesz2
