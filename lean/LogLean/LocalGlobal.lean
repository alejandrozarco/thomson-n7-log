import LogLean.LocalGlobB
import LogLean.LocalGlobB2
import LogLean.LocalGlobC
import LogLean.LocalGlobD4
import LogLean.LocalGlobE

/-!
# LocalGlobal: real-side consequences of the global kernel checks

`F2_exp F3_exp F4_exp` (the (σ, w) expansions with their structured pieces), `bomb_*` (Bombieri bounds),
`pair_bomb` (per-pair degree 5/6 bounds); `F_sum` and the definitions are in LocalGlobA, the kernel checks in
LocalGlobB–E (split so that each module stays within the memory budget of one `decide +kernel` family).
-/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames Finset

variable {x : ℕ → ℝ} {a : ℝ}

/-! ## Real-side consequences -/

section real
variable (z : ℕ → ℝ)

/-- `|w|²` -/
noncomputable def wsq : ℝ := ∑ p ∈ range 14, z (2 + p) ^ 2

lemma ev_S16 (d : ℕ) : ev (S16 d) z alpha = wsq z ^ d := by
  rw [S16, ev_pow alpha_minpoly, ev_sumsq 16 2 14 (by norm_num)]; rfl

lemma ev_n2 (k : ℕ) : ev (pow n2 k) z alpha = (z 0 ^ 2 + z 1 ^ 2) ^ k := by
  rw [ev_pow alpha_minpoly]; simp [n2, ev, Mono.ev, Kel.ev_ofQ]

/-- **The quadratic part**: `F2(σŝ + w) = ½ wᵀHw` -/
theorem F2_exp : ev F2 (xsub z) alpha
    = (1 / 2) * ∑ p ∈ range 14, ∑ q ∈ range 14, (LocalCert.Hd p q).ev alpha * (z (2 + p) * z (2 + q)) := by
  rw [← ev_compose_forms F2 len2, ev_eq_of_eqPoly alpha_minpoly _ _ exp2, ev_eq_of_eqPoly alpha_minpoly _ _ piece2,
    ev_smul alpha_minpoly, Kel.ev_ofQ, ev_qfPoly _ 16 2 14 14 (by norm_num) (by norm_num)]
  norm_num

/-- **The cubic part**: `F3(σŝ + w) = F3(w) + Σ_α σ_α wᵀA_αw + ⟪Γm, w⟫` -/
theorem F3_exp : ev F3 (xsub z) alpha
    = ev G3_0 z alpha
      + (z 0 * ∑ p ∈ range 14, ∑ q ∈ range 14, (LocalGamma1.Ad 0 p q).ev alpha * (z (2 + p) * z (2 + q))
        + z 1 * ∑ p ∈ range 14, ∑ q ∈ range 14, (LocalGamma1.Ad 1 p q).ev alpha * (z (2 + p) * z (2 + q)))
      + (z 0 ^ 2 * ∑ p ∈ range 14, (LocalCert.Gd p 0).ev alpha * z (2 + p)
        + z 0 * z 1 * ∑ p ∈ range 14, (LocalCert.Gd p 1).ev alpha * z (2 + p)
        + z 1 ^ 2 * ∑ p ∈ range 14, (LocalCert.Gd p 2).ev alpha * z (2 + p)) := by
  rw [← ev_compose_forms F3 len3, ev_eq_of_eqPoly alpha_minpoly _ _ exp3, ev_merge, ev_merge,
    ev_eq_of_eqPoly alpha_minpoly _ _ piece3_1, ev_eq_of_eqPoly alpha_minpoly _ _ piece3_2]
  simp only [gamPoly, ev_merge, ev_mul alpha_minpoly, ev_xk 16 0 (by norm_num), ev_xk 16 1 (by norm_num),
    ev_qfPoly _ 16 2 14 14 (by norm_num) (by norm_num), ev_linPoly _ 16 2 14 (by norm_num)]
  simp [ev, Mono.ev, Kel.ev_ofQ] <;> ring

/-- **The quartic part**: `F4(σŝ + w) = F4(w) + T_σ(w) + wᵀB(σ)w + ⟪g̃(σ), w⟫ + Σ_b q_b(σ)⟪k_b, w⟫ + (13/40)|s|⁴` -/
theorem F4_exp : ev F4 (xsub z) alpha
    = ev G4_0 z alpha + evDP D41 z alpha + evDP D42 z alpha + evDP D43t z alpha
      + ∑ b ∈ range 5, ev (qb b) z alpha * ∑ p ∈ range 14, (Kd p b).ev alpha * z (2 + p)
      + (13 / 40 * (25 / 4)) * (z 0 ^ 2 + z 1 ^ 2) ^ 2 := by
  have hl := len4c
  simp only [Bool.and_eq_true] at hl
  have e4 : ev F4 (xsub z) alpha = ev (compose F4c0 forms) z alpha + ev (compose F4c1 forms) z alpha
      + ev (compose F4c2 forms) z alpha + ev (compose F4c3 forms) z alpha := by
    simp only [F4, ev_merge, ev_compose_forms _ hl.1.1.1, ev_compose_forms _ hl.1.1.2,
      ev_compose_forms _ hl.1.2, ev_compose_forms _ hl.2]; ring
  rw [e4, ev_eq_of_eqPoly alpha_minpoly _ _ exp4c0, ev_eq_of_eqPoly alpha_minpoly _ _ exp4c1,
    ev_eq_of_eqPoly alpha_minpoly _ _ exp4c2, ev_eq_of_eqPoly alpha_minpoly _ _ exp4c3]
  have e5 := ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ exp4
  simp only [ev_merge] at e5
  rw [show ev G4c0 z alpha + ev G4c1 z alpha + ev G4c2 z alpha + ev G4c3 z alpha
      = ev G4c0 z alpha + (ev G4c1 z alpha + (ev G4c2 z alpha + ev G4c3 z alpha)) by ring, e5,
    ev_eq_of_eqPoly alpha_minpoly _ _ piece4_1, ev_eq_of_eqPoly alpha_minpoly _ _ piece4_2,
    ev_eq_of_eqPoly alpha_minpoly _ _ piece4_3, ev_eq_of_eqPoly alpha_minpoly _ _ piece4_4,
    ev_merge, ev_flatDP alpha_minpoly, ev_flatDP alpha_minpoly, ev_flatDP alpha_minpoly,
    ev_smul alpha_minpoly, Kel.ev_ofQ, ev_pow alpha_minpoly]
  have ep : ev projPoly z alpha = ∑ b ∈ range 5, ev (qb b) z alpha * ∑ p ∈ range 14, (Kd p b).ev alpha * z (2 + p) := by
    simp only [projPoly, show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.foldr_cons, List.foldr_nil,
      ev_merge, ev_mul alpha_minpoly, ev_linPoly _ 16 2 14 (by norm_num), Finset.sum_range_succ,
      Finset.sum_range_zero, ev_nil]
    ring
  rw [ep]
  simp [n2_16, ev, Mono.ev, Kel.ev_ofQ, ev_replicate] <;> push_cast <;> ring

/-! ### The Bombieri bounds -/

lemma sok : ∀ d : ℕ, 1 ≤ d → d ≤ 3 → Sok (S16 d) = true
  | 1, _, _ => Sok16_1
  | 2, _, _ => Sok16_2
  | 3, _, _ => Sok16_3
  | 0, h, _ => absurd h (by decide)
  | _ + 4, _, h => absurd h (by omega)

/-- the split multinomial list: `ev S4m = |w|⁸` -/
lemma ev_S4m : ev S4m z alpha = wsq z ^ 4 := by
  have h3 : ev S3lit z alpha = wsq z ^ 3 := by
    rw [← ev_eq_of_eqPoly alpha_minpoly _ _ S3_eq, ev_S16]
  have hsum : wsq z = ev (((sumsq 16 2 14).drop 0).take 2) z alpha + ev (((sumsq 16 2 14).drop 2).take 2) z alpha
      + ev (((sumsq 16 2 14).drop 4).take 2) z alpha + ev (((sumsq 16 2 14).drop 6).take 2) z alpha
      + ev (((sumsq 16 2 14).drop 8).take 2) z alpha + ev (((sumsq 16 2 14).drop 10).take 2) z alpha
      + ev (((sumsq 16 2 14).drop 12).take 2) z alpha := by
    rw [← ev_append, ← ev_append, ← ev_append, ← ev_append, ← ev_append, ← ev_append, ← chunks_eq,
      ev_sumsq 16 2 14 (by norm_num)] <;> rfl
  simp only [S4m, ev_merge]
  rw [← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P0_eq, ← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P1_eq,
    ← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P2_eq, ← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P3_eq,
    ← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P4_eq, ← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P5_eq,
    ← ev_eq_of_eqPoly (x := z) alpha_minpoly _ _ P6_eq]
  simp only [ev_mul alpha_minpoly, h3]
  rw [hsum]; ring

theorem bomb_F3w : (ev G3_0 z alpha) ^ 2 ≤ 5 * wsq z ^ 3 := by
  have h := bombieri (x := z) alpha_minpoly 3 (constDP G3_0) (S16 3) ws3 (sok 3 (by norm_num) (by norm_num))
  rw [evDP_constDP, ev_eq_of_eqPoly alpha_minpoly _ _ bs3, ev_S16] at h
  simpa [ev, Mono.ev, Kel.ev_ofQ] using h

theorem bomb_F4w : (ev G4_0 z alpha) ^ 2 ≤ (35261 / 3840) * wsq z ^ 4 := by
  have h := bombieri (x := z) alpha_minpoly 4 (constDP G4_0) S4m ws4 Sok4m
  rw [evDP_constDP, ev_eq_of_eqPoly alpha_minpoly _ _ bs4, ev_S4m] at h
  simpa [ev, Mono.ev, Kel.ev_ofQ] using h

theorem bomb_D41 : (evDP D41 z alpha) ^ 2 ≤ (c13 : ℝ) * (z 0 ^ 2 + z 1 ^ 2) * wsq z ^ 3 := by
  have h := bombieri (x := z) alpha_minpoly 3 D41 (S16 3) ws41 (sok 3 (by norm_num) (by norm_num))
  rw [ev_eq_of_eqPoly alpha_minpoly _ _ bs41, ev_smul alpha_minpoly, Kel.ev_ofQ, ev_n2, ev_S16] at h
  simpa using h

theorem bomb_D42 : (evDP D42 z alpha) ^ 2 ≤ (c22 : ℝ) * (z 0 ^ 2 + z 1 ^ 2) ^ 2 * wsq z ^ 2 := by
  have h := bombieri (x := z) alpha_minpoly 2 D42 (S16 2) ws42 (sok 2 (by norm_num) (by norm_num))
  rw [ev_eq_of_eqPoly alpha_minpoly _ _ bs42, ev_smul alpha_minpoly, Kel.ev_ofQ, ev_n2, ev_S16] at h
  simpa using h

theorem bomb_D43t : (evDP D43t z alpha) ^ 2 ≤ (c6 : ℝ) * (z 0 ^ 2 + z 1 ^ 2) ^ 3 * wsq z := by
  have h := bombieri (x := z) alpha_minpoly 1 D43t (S16 1) ws43 (sok 1 (by norm_num) (by norm_num))
  rw [ev_eq_of_eqPoly alpha_minpoly _ _ bs43, ev_smul alpha_minpoly, Kel.ev_ofQ, ev_n2, ev_S16] at h
  simpa using h

end real

/-- per pair: `p_ij,5(x)² ≤ B5² (Σ_{k<4} x_k²)^5` and the same for degree 6, for every `(i,j) ∈ pairsL` -/
theorem pair_bomb {i j : ℕ} (hij : (i, j) ∈ pairsL) (x : ℕ → ℝ) :
    (ev (pijd i j 5) x alpha) ^ 2 ≤ (B5b i j : ℝ) ^ 2 * (∑ k ∈ range 4, x k ^ 2) ^ 5 ∧
    (ev (pijd i j 6) x alpha) ^ 2 ≤ (B6b i j : ℝ) ^ 2 * (∑ k ∈ range 4, x k ^ 2) ^ 6 ∧
    (0 : ℝ) ≤ B5b i j ∧ (0 : ℝ) ≤ B6b i j := by
  have h := pairBombOK_true
  simp only [pairBombOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨e5, w5⟩, h5⟩, p5⟩, e6⟩, w6⟩, h6⟩, p6⟩ := h (i, j) hij
  have hs := Sok4; simp only [Bool.and_eq_true] at hs
  have eS : ∀ d, ev (S4 d) x alpha = (∑ k ∈ range 4, x k ^ 2) ^ d := fun d => by
    rw [S4, ev_pow alpha_minpoly, ev_sumsq 4 0 4 (by norm_num)]; simp
  have hb5 := bombieri (x := x) alpha_minpoly 5 (constDP (pijd i j 5)) (S4 5) w5 hs.1
  have hb6 := bombieri (x := x) alpha_minpoly 6 (constDP (pijd i j 6)) (S4 6) w6 hs.2
  rw [evDP_constDP, ev_eq_of_eqPoly alpha_minpoly _ _ e5, eS] at hb5
  rw [evDP_constDP, ev_eq_of_eqPoly alpha_minpoly _ _ e6, eS] at hb6
  simp only [ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mono.ev, mul_one, add_zero] at hb5 hb6
  have k5 : (B5sq i j).ev alpha ≤ (B5b i j : ℝ) ^ 2 :=
    (Kel.ev_le_hi _ aLo_nonneg alpha_box.1 alpha_box.2).trans (by exact_mod_cast h5)
  have k6 : (B6sq i j).ev alpha ≤ (B6b i j : ℝ) ^ 2 :=
    (Kel.ev_le_hi _ aLo_nonneg alpha_box.1 alpha_box.2).trans (by exact_mod_cast h6)
  have hS : 0 ≤ ∑ k ∈ range 4, x k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  refine ⟨hb5.trans (mul_le_mul_of_nonneg_right k5 (by positivity)),
    hb6.trans (mul_le_mul_of_nonneg_right k6 (by positivity)), by exact_mod_cast p5, by exact_mod_cast p6⟩

end LocalGlobal
