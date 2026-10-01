import LogLean.LocalGlobData
import LogLean.LocalPairData
import LogLean.LocalFrames

/-!
# LocalGlobA: definitions of the global level and its light kernel checks (pair sums, `F2 = ½xᵀHx`, lengths)

Kernel checks (`decide +kernel`), all mirrored and pre-verified by `lean/gen/local_global.py`:
* `sum2 sum3 sum4`: `Σ_{i<j} embed(p_ij,d) + poles_d = F_d` (d = 2, 3, 4);
* `F2_qf`: `F2 = ½ Σ H_pq x_p x_q` with the `LocalCert` Hessian;
* `exp2 exp3 exp4c* exp4`: `F_d(σ₁ŝ₁ + σ₂ŝ₂ + w) = Σ_k G_d,k` (σ-degree pieces), `F4` in four chunks;
* `piece*`: each piece equals its structured form (½wᵀHw; `σ_α wᵀA_αw`; `⟪Γm,w⟫`; the dense forms `D41 D42 D43t`
  plus the kernel components `Σ_b q_b(σ)⟪k_b,w⟫`; `(13/40)(25/4)|σ|⁴`);
* Bombieri squares `bs*` and the multinomial sub-sequence checks `ws*`, `Sok*`; per pair `pairBombOK`.
Real-side consequences: `F2_eq`, `F3_eq`, `F4_eq` (the expansions), `bomb_F3w …` (the bounds), `F_sum` (the pair sums).
-/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames Finset

/-! ## Generic: evaluation only depends on the variables that occur -/

lemma Mono.ev_congr (m : Mono) (i : ℕ) {f g : ℕ → ℝ} (h : ∀ j, j < i + m.length → f j = g j) :
    m.ev i f = m.ev i g := by
  induction m generalizing i with
  | nil => simp [Mono.ev]
  | cons e m ih =>
    simp only [Mono.ev]
    rw [h i (by rw [List.length_cons]; omega), ih (i + 1) (fun j hj => h j (by rw [List.length_cons]; omega))]

/-- all monomials have length `≤ n` -/
def lenLe (n : ℕ) (p : Poly) : Bool := p.all fun t => decide (t.1.length ≤ n)

lemma ev_congr {a : ℝ} (p : Poly) (n : ℕ) (hp : lenLe n p = true) {f g : ℕ → ℝ} (h : ∀ j, j < n → f j = g j) :
    ev p f a = ev p g a := by
  induction p with
  | nil => simp [ev]
  | cons t p ih =>
    simp only [lenLe, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    rw [ev_cons, ev_cons, ih hp.2, Mono.ev_congr t.1 0 (fun j hj => h j (by omega))]

/-! ## The pair sums (T7) -/

def pairsL : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5),
   (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]

def sumPairs (d : ℕ) : Poly := pairsL.foldr (fun ij acc => merge (embed ij.1 ij.2 (pijd ij.1 ij.2 d)) acc) []

theorem sum2 : eqPoly (merge (sumPairs 2) poles2) F2 = true := by decide +kernel
theorem sum3 : eqPoly (sumPairs 3) F3 = true := by decide +kernel
theorem sum4 : eqPoly (merge (sumPairs 4) poles4) F4 = true := by decide +kernel
theorem len4_pairs : pairsL.all (fun ij => (List.range 5).all fun d => len4 (pijd ij.1 ij.2 (d + 2))) = true := by
  decide +kernel
theorem pairsL_ok : pairsL.all (fun ij => decide (ij.1 < ij.2 ∧ ij.2 < 7)) = true := by decide

variable {x : ℕ → ℝ} {a : ℝ}

lemma ev_sumPairs_aux (ha : a ^ 4 = 20 * a ^ 2 - 80) (d : ℕ) (L : List (ℕ × ℕ))
    (hl : ∀ ij ∈ L, len4 (pijd ij.1 ij.2 d) = true) (ho : ∀ ij ∈ L, ij.1 < ij.2 ∧ ij.2 < 7) :
    ev (L.foldr (fun ij acc => merge (embed ij.1 ij.2 (pijd ij.1 ij.2 d)) acc) []) x a
      = (L.map fun ij => ev (pijd ij.1 ij.2 d) (loc x ij.1 ij.2) a).sum := by
  induction L with
  | nil => simp [ev]
  | cons ij L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [ev_merge, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (fun q hq => ho q (List.mem_cons_of_mem _ hq))]
    congr 1
    exact ev_embed (ho ij List.mem_cons_self).1 (ho ij List.mem_cons_self).2 _ (hl ij List.mem_cons_self)

lemma ev_sumPairs (ha : a ^ 4 = 20 * a ^ 2 - 80) (d : ℕ) (hd : 2 ≤ d) (hd' : d ≤ 6) :
    ev (sumPairs d) x a = (pairsL.map fun ij => ev (pijd ij.1 ij.2 d) (loc x ij.1 ij.2) a).sum := by
  have hl := len4_pairs
  have ho := pairsL_ok
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hl ho
  refine ev_sumPairs_aux ha d pairsL (fun ij hij => ?_) ho
  have := hl ij hij (d - 2) (by omega)
  rwa [show d - 2 + 2 = d by omega] at this

lemma ev_poles2 : ev poles2 x a = (1 / 8) * (x 10 ^ 2 + x 11 ^ 2 + x 12 ^ 2 + x 13 ^ 2) := by
  simp [poles2, ev, Mono.ev, Kel.ev]; push_cast; ring
lemma ev_poles4 : ev poles4 x a = (1 / 32) * ((x 10 ^ 2 + x 11 ^ 2) ^ 2 + (x 12 ^ 2 + x 13 ^ 2) ^ 2) := by
  simp [poles4, ev, Mono.ev, Kel.ev]; push_cast; ring

/-- `F_d(x) = Σ_{i<j} p_ij,d(loc x) + poles_d(x)` -/
theorem F_sum (ha : a ^ 4 = 20 * a ^ 2 - 80) :
    ev F2 x a = (pairsL.map fun ij => ev (pijd ij.1 ij.2 2) (loc x ij.1 ij.2) a).sum
        + (1 / 8) * (x 10 ^ 2 + x 11 ^ 2 + x 12 ^ 2 + x 13 ^ 2) ∧
    ev F3 x a = (pairsL.map fun ij => ev (pijd ij.1 ij.2 3) (loc x ij.1 ij.2) a).sum ∧
    ev F4 x a = (pairsL.map fun ij => ev (pijd ij.1 ij.2 4) (loc x ij.1 ij.2) a).sum
        + (1 / 32) * ((x 10 ^ 2 + x 11 ^ 2) ^ 2 + (x 12 ^ 2 + x 13 ^ 2) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← ev_eq_of_eqPoly ha _ _ sum2, ev_merge, ev_sumPairs ha 2 le_rfl (by norm_num), ev_poles2]
  · rw [← ev_eq_of_eqPoly ha _ _ sum3, ev_sumPairs ha 3 (by norm_num) (by norm_num)]
  · rw [← ev_eq_of_eqPoly ha _ _ sum4, ev_merge, ev_sumPairs ha 4 (by norm_num) (by norm_num), ev_poles4]

/-! ## `F2 = ½ xᵀHx` -/

theorem F2_qf : eqPoly F2 (smul (Kel.ofQ (1 / 2)) (qfPoly LocalCert.Hd 14 0 14 14)) = true := by decide +kernel

theorem F2_eq (ha : a ^ 4 = 20 * a ^ 2 - 80) :
    ev F2 x a = (1 / 2) * ∑ p ∈ range 14, ∑ q ∈ range 14, (LocalCert.Hd p q).ev a * (x p * x q) := by
  rw [ev_eq_of_eqPoly ha _ _ F2_qf, ev_smul ha, Kel.ev_ofQ, ev_qfPoly _ 14 0 14 14 (by norm_num) (by norm_num)]
  push_cast; simp

/-! ## The `(σ, w)` expansion (variables `0, 1 = σ`, `2 + p = w_p`) -/

def formTerm (m : Mono) (c : Kel) : Poly := if c = Kel.zero then [] else [(m, c)]

lemma ev_formTerm (m : Mono) (c : Kel) : ev (formTerm m c) x a = c.ev a * m.ev 0 x := by
  unfold formTerm; split_ifs with h
  · simp [ev, h, Kel.ev, Kel.zero]
  · simp [ev]

def forms (p : ℕ) : Poly :=
  merge (merge (formTerm (unit 16 0) (Kd p 3)) (formTerm (unit 16 1) (Kd p 4))) [(unit 16 (2 + p), Kel.ofQ 1)]

lemma ev_forms (p : ℕ) (hp : p < 14) :
    ev (forms p) x a = (Kd p 3).ev a * x 0 + (Kd p 4).ev a * x 1 + x (2 + p) := by
  simp only [forms, ev_merge, ev_formTerm, ev_unit0 16 0 (by norm_num), ev_unit0 16 1 (by norm_num),
    ev_unit0 16 (2 + p) (by omega)]
  simp [ev, Kel.ev_ofQ, ev_unit0 16 (2 + p) (by omega)]

/-- the substitution `x_p = σ₁ ŝ₁[p] + σ₂ ŝ₂[p] + w_p` -/
noncomputable def xsub (z : ℕ → ℝ) (p : ℕ) : ℝ := (Kd p 3).ev alpha * z 0 + (Kd p 4).ev alpha * z 1 + z (2 + p)

lemma ev_compose_forms (p : Poly) (hp : lenLe 14 p = true) (z : ℕ → ℝ) :
    ev (compose p forms) z alpha = ev p (xsub z) alpha := by
  rw [ev_compose alpha_minpoly]
  exact ev_congr p 14 hp fun j hj => by rw [ev_forms j hj]; rfl

theorem len2 : lenLe 14 F2 = true := by decide +kernel
theorem len3 : lenLe 14 F3 = true := by decide +kernel
theorem len4c : (lenLe 14 F4c0 && lenLe 14 F4c1 && lenLe 14 F4c2 && lenLe 14 F4c3) = true := by decide +kernel

end LocalGlobal
