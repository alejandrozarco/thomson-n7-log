import ThomsonGen.Generic.Energy

/-!
# N = 7 Coulomb (s = 1): the kernel form of the energy and a rational enclosure of E(P)

* The Coulomb kernel is upstream's `ThomsonN7.Base.phi t = (√(2 - 2t))⁻¹` (regenerated `ThomsonGen.Base`);
  on unit vectors `coulombEnergy x = pairEnergy Base.phi x` (`coulombEnergy_eq_pairEnergy`).
* `pairEnergy_pent_le`, `pairEnergy_pent_ge`: `L ≤ E(P) ≤ U` with `U - L = 5·10⁻²⁴`, from upstream's closed
  form `pentBipyramid_energy` and 25-digit rational bounds of `√2`, `√5`, `sin (π/5)`.
-/

/-! Attribution: adapted from huwngtran/thomson-n7-lean @ 25f2fa5, `ThomsonN7/Solution.lean` (ours ← upstream):
`sin_pi_five_sq` ← `EPBounds.sin_pi_div_five_sq`; `sin_two_pi_five` ← `EPBounds.sin_two_pi_div_five`;
`sqrt5_enc`, `sqrt2_enc`, `sin_pi_five_enc`, `pairEnergy_pent_le`, `pairEnergy_pent_ge` follow the pattern of
`EPBounds.sqrt5_bounds`, `EPBounds.sin_pi_div_five_bounds`, `EPBounds.pent_formula_bounds` (25 instead of 9 digits). -/

open Real

namespace CoulN7

open ThomsonN7 ThomsonN7.Base ThomsonGen

/-- On unit vectors the Coulomb energy is `pairEnergy` of upstream's kernel `Base.phi`. -/
theorem coulombEnergy_eq_pairEnergy {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    coulombEnergy x = pairEnergy phi x := by
  rw [coulombEnergy_eq_sum_phi hx]
  rfl

theorem pairEnergy_pent : pairEnergy phi pentBipyramid =
    1 / 2 + 5 * √2 + 5 / (2 * sin (π / 5)) + 5 / (2 * sin (2 * π / 5)) := by
  rw [← coulombEnergy_eq_pairEnergy pent_norm, pentBipyramid_energy]

lemma sin_pi_five_sq : sin (π / 5) ^ 2 = (5 - √5) / 8 := by
  have h := sin_sq_add_cos_sq (π / 5)
  rw [cos_pi_div_five] at h
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

lemma sin_two_pi_five : sin (2 * π / 5) = sin (π / 5) * ((1 + √5) / 2) := by
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, sin_two_mul, cos_pi_div_five]
  ring

lemma sin_pi_five_pos : 0 < sin (π / 5) :=
  sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])

lemma sqrt5_enc : (22360679774997896964091736 : ℝ) / 10 ^ 25 ≤ √5 ∧
    √5 ≤ (22360679774997896964091737 : ℝ) / 10 ^ 25 :=
  ⟨(Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num),
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩⟩

lemma sqrt2_enc : (14142135623730950488016887 : ℝ) / 10 ^ 25 ≤ √2 ∧
    √2 ≤ (14142135623730950488016888 : ℝ) / 10 ^ 25 :=
  ⟨(Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num),
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩⟩

lemma sin_pi_five_enc : (5877852522924731291687058 : ℝ) / 10 ^ 25 ≤ sin (π / 5) ∧
    sin (π / 5) ≤ (5877852522924731291687061 : ℝ) / 10 ^ 25 := by
  have hs := sin_pi_five_sq
  have hp := sin_pi_five_pos
  obtain ⟨h5l, h5u⟩ := sqrt5_enc
  constructor
  · by_contra h
    push Not at h
    have : sin (π / 5) ^ 2 < ((5877852522924731291687058 : ℝ) / 10 ^ 25) ^ 2 := by
      apply pow_lt_pow_left₀ h hp.le (by norm_num)
    rw [hs] at this
    norm_num at this h5u
    linarith
  · by_contra h
    push Not at h
    have : ((5877852522924731291687061 : ℝ) / 10 ^ 25) ^ 2 < sin (π / 5) ^ 2 := by
      apply pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    rw [hs] at this
    norm_num at this h5l
    linarith

/-- **Upper enclosure of E(P)** (`U - E(P) < 5·10⁻²⁴`). -/
theorem pairEnergy_pent_le :
    pairEnergy phi pentBipyramid ≤ (14452977414221342935044494 : ℝ) / 10 ^ 24 := by
  rw [pairEnergy_pent, sin_two_pi_five]
  obtain ⟨h2l, h2u⟩ := sqrt2_enc
  obtain ⟨h5l, h5u⟩ := sqrt5_enc
  obtain ⟨hsl, hsu⟩ := sin_pi_five_enc
  have hp := sin_pi_five_pos
  have h1 : 5 / (2 * sin (π / 5)) ≤ 5 / (2 * ((5877852522924731291687058 : ℝ) / 10 ^ 25)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hb : ((5877852522924731291687058 : ℝ) / 10 ^ 25) *
      ((1 + (22360679774997896964091736 : ℝ) / 10 ^ 25) / 2) ≤ sin (π / 5) * ((1 + √5) / 2) :=
    mul_le_mul hsl (by linarith) (by norm_num) hp.le
  have h2 : 5 / (2 * (sin (π / 5) * ((1 + √5) / 2))) ≤
      5 / (2 * (((5877852522924731291687058 : ℝ) / 10 ^ 25) *
        ((1 + (22360679774997896964091736 : ℝ) / 10 ^ 25) / 2))) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at h1 h2 ⊢
  linarith

/-- **Lower enclosure of E(P)**. -/
theorem pairEnergy_pent_ge :
    (14452977414221342935044489 : ℝ) / 10 ^ 24 ≤ pairEnergy phi pentBipyramid := by
  rw [pairEnergy_pent, sin_two_pi_five]
  obtain ⟨h2l, h2u⟩ := sqrt2_enc
  obtain ⟨h5l, h5u⟩ := sqrt5_enc
  obtain ⟨hsl, hsu⟩ := sin_pi_five_enc
  have hp := sin_pi_five_pos
  have h1 : 5 / (2 * ((5877852522924731291687061 : ℝ) / 10 ^ 25)) ≤ 5 / (2 * sin (π / 5)) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h5p : 0 < √5 := Real.sqrt_pos.2 (by norm_num)
  have hb : sin (π / 5) * ((1 + √5) / 2) ≤ ((5877852522924731291687061 : ℝ) / 10 ^ 25) *
      ((1 + (22360679774997896964091737 : ℝ) / 10 ^ 25) / 2) :=
    mul_le_mul hsu (by linarith) (by positivity) (by norm_num)
  have hb0 : 0 < sin (π / 5) * ((1 + √5) / 2) := by positivity
  have h2 : 5 / (2 * (((5877852522924731291687061 : ℝ) / 10 ^ 25) *
        ((1 + (22360679774997896964091737 : ℝ) / 10 ^ 25) / 2))) ≤
      5 / (2 * (sin (π / 5) * ((1 + √5) / 2))) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  norm_num at h1 h2 ⊢
  linarith

end CoulN7
