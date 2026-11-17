import ThomsonGen.Base
import RieszN7.Core.Rpow

/-!
# `RieszN7.Basic` — the Riesz s-energy, its kernel form, and the closed form of `E_s(P)` (LEAN_PLAN_range.md §2)

* `rieszEnergy s x = Σ_{i<j} ‖x i − x j‖^(−s)` (trusted definition; theorems quantify over `SphereConfig 7`).
* On unit vectors `‖x − y‖^(−s) = phiS s ⟪x, y⟫` (`norm_sub_rpow_eq_phiS`), so `rieszEnergy s x` is the pair sum of
  `phiS s` (`rieszEnergy_eq_sum_phiS`; this is `ThomsonGen.pairEnergy (phiS s) x` definitionally — the
  `Generic.Energy` link is Phase 2, that module is not built in the Mac workspace).
* `rieszEnergy_pent`: `E_s(P) = phiS s (−1) + 10 phiS s 0 + 5 phiS s c₁ + 5 phiS s c₂`.

`sum_Ioi_seven`, `inner_pent_ring` and the proof of `rieszEnergy_pent` are copied from `lean/Riesz2/Basic.lean`
(s = 2 port; there with `phi2`).  Imports `ThomsonGen.Base` (→ `ThomsonGen.Preamble` → all of Mathlib).
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Real

namespace RieszN7

open ThomsonN7 ThomsonN7.Base

/-- Riesz `s`-energy `Σ_{i<j} ‖x i − x j‖^(−s)`. -/
noncomputable def rieszEnergy (s : ℝ) {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖ ^ (-s)

lemma norm_sub_rpow_eq_phiS (s : ℝ) {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ (-s) = phiS s (inner ℝ x y) := by
  unfold phiS
  rw [← norm_sub_sq_of_unit hx hy, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

lemma rieszEnergy_eq_sum_phiS (s : ℝ) {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    rieszEnergy s x = ∑ i, ∑ j ∈ Finset.Ioi i, phiS s (inner ℝ (x i) (x j)) := by
  unfold rieszEnergy
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    norm_sub_rpow_eq_phiS s (hx i) (hx j)

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

theorem rieszEnergy_pent (s : ℝ) :
    rieszEnergy s pentBipyramid = phiS s (-1) + 10 * phiS s 0 + 5 * phiS s c1 + 5 * phiS s c2 := by
  rw [rieszEnergy_eq_sum_phiS s pent_norm, sum_Ioi_seven]
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
    pent_inner_poles]
  ring

end RieszN7
