import RieszN7.Cap.StepP.Core
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# `RieszN7.Cap.StepP.Block` — from the scalar Step P argument to a reduced family block

The reduced family block of a piece is `R_{ii'} = Σ_j w_j / Λ̃_j · ent_j(i, i')` over the 9 objects (nodes `a, b`,
directions `0…6`) with `w = wt λ v va vb` (the bridge's `wts`).  Its quadratic form at `y` is
`Σ_j w_j / Λ̃_j · qf r (mat_j) y`; in the coordinates `x_i = y_i / cs_i` of the shared column scales it is
`Σ_j w_j / Λ̃_j · G_j` with `G_j = qf r (scl cs mat_j) x`, which is `famV` with `Q_a = G_0/Λ̃_0` etc.  Here:
`wt`, the rewriting lemmas, a segment lemma (`Phi_interval` + `famV_ge`), the literal symmetry check `symOK` and the
passage to `Matrix.PosSemidef` for kernel blocks.  Private, AI-written (Phase 2, CAP fork, 2026-11-08), not reviewed.
-/

namespace RieszN7.CapLit.StepP

open Finset RieszN7.LDL Matrix

/-- The piece weights `(1 − λ, λ, ρ₀, …, ρ₆)` (the bridge's `wts`, restated). -/
noncomputable def wt (lam : ℝ) (v va vb : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![1 - lam, lam, v 0 - (1 - lam) * va 0 - lam * vb 0, v 1 - (1 - lam) * va 1 - lam * vb 1,
    v 2 - (1 - lam) * va 2 - lam * vb 2, v 3 - (1 - lam) * va 3 - lam * vb 3, v 4 - (1 - lam) * va 4 - lam * vb 4,
    v 5 - (1 - lam) * va 5 - lam * vb 5, v 6 - (1 - lam) * va 6 - lam * vb 6]

/-- The weighted sum over the 9 objects is the family form. -/
theorem sum9_famV (a b s : ℝ) (v va vb : Fin 7 → ℝ) (G Lt : Fin 9 → ℝ) :
    ∑ j, wt (lam a b s) v va vb j / Lt j * G j
      = famV a b va vb (G 0 / Lt 0) (G 1 / Lt 1) (fun k => G k.succ.succ / Lt k.succ.succ) s v := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hk : ∀ k : Fin 7, wt (lam a b s) v va vb k.succ.succ = v k - (1 - lam a b s) * va k - lam a b s * vb k := by
    intro k; fin_cases k <;> rfl
  have h0 : wt (lam a b s) v va vb 0 = 1 - lam a b s := rfl
  have h1 : wt (lam a b s) v va vb (Fin.succ 0) = lam a b s := rfl
  have hs : ∑ k : Fin 7, wt (lam a b s) v va vb k.succ.succ / Lt k.succ.succ * G k.succ.succ
      = ∑ k : Fin 7, (v k - (1 - lam a b s) * va k - lam a b s * vb k) * (G k.succ.succ / Lt k.succ.succ) :=
    Finset.sum_congr rfl fun k _ => by rw [hk]; ring
  simp only [famV]
  rw [hs, h0, h1]
  have e : G (Fin.succ 0) / Lt (Fin.succ 0) = G 1 / Lt 1 := rfl
  rw [← e]
  ring

/-- `qf` in the original coordinates is `qf` of the scaled matrix at `x_i = y_i / cs_i`. -/
theorem qf_unscale (n : ℕ) (cs : List ℤ) (M : List (List ℤ)) (y : ℕ → ℝ)
    (hcs : ∀ i < n, cs.getD i 0 ≠ 0) :
    qf n M y = qf n (scl cs M) (fun i => y i / cs.getD i 0) := by
  rw [qf_scl]
  unfold qf
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : ((cs.getD i 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hcs i (Finset.mem_range.1 hi)
  have hj' : ((cs.getD j 0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hcs j (Finset.mem_range.1 hj)
  simp only [mul_div_cancel₀ _ hi', mul_div_cancel₀ _ hj']

/-- The column scales are nonzero (kernel check). -/
def csOK (n : ℕ) (cs : List ℤ) : Bool := (List.range n).all fun i => cs.getD i 0 != 0

theorem cs_ne (n : ℕ) (cs : List ℤ) (h : csOK n cs = true) : ∀ i < n, cs.getD i 0 ≠ 0 := by
  intro i hi
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simpa using this

/-- Swapping the object sum out of a quadratic form. -/
theorem qf_sum9 (r : ℕ) (c : Fin 9 → ℝ) (E : Fin 9 → ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    ∑ i ∈ range r, ∑ i' ∈ range r, y i * (∑ j, c j * (E j i i' : ℝ)) * y i'
      = ∑ j, c j * ∑ i ∈ range r, ∑ i' ∈ range r, y i * (E j i i' : ℝ) * y i' := by
  have h : ∀ i i', y i * (∑ j, c j * (E j i i' : ℝ)) * y i' = ∑ j, c j * (y i * (E j i i' : ℝ) * y i') := by
    intro i i'
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc _ = ∑ i ∈ range r, ∑ i' ∈ range r, ∑ j, c j * (y i * (E j i i' : ℝ) * y i') := by simp only [h]
    _ = ∑ i ∈ range r, ∑ j, ∑ i' ∈ range r, c j * (y i * (E j i i' : ℝ) * y i') :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j, ∑ i ∈ range r, ∑ i' ∈ range r, c j * (y i * (E j i i' : ℝ) * y i') := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

/-- **Segment lemma.** On `[t₀, t₂]` (inside `[s_m − δ, s_m + δ]`), with the sample margins, the `W` bound and the
Frobenius bounds at a fixed vector, the slack condition gives `0 ≤ famV s V` for all `V` within `ε` of the models. -/
theorem seg (a b sm : ℝ) (va vb : Fin 7 → ℝ) (Qa Qb : ℝ) (Q : Fin 7 → ℝ) (p : Fin 7 → Fin 6 → ℝ) (hab : a ≠ b)
    {t0 t2 δ τ N m0 m2 : ℝ} (F C ε : Fin 7 → ℝ)
    (ht : t0 < t2) (h0 : |t0 - sm| ≤ δ) (h2 : |t2 - sm| ≤ δ) (hN : 0 ≤ N) (hτ : 0 ≤ τ)
    (hF0 : ∀ k, 0 ≤ F k) (hF : ∀ k, |Q k| ≤ F k * N) (hW : ∑ k, p k 2 * Q k ≤ τ * N)
    (hm0 : m0 * N ≤ Phi a b sm va vb Qa Qb Q p t0) (hm2 : m2 * N ≤ Phi a b sm va vb Qa Qb Q p t2)
    (hC : ∀ k, 3 * δ * |p k 3| + 6 * δ ^ 2 * |p k 4| + 10 * δ ^ 3 * |p k 5| ≤ C k)
    (hsl : 0 ≤ min m0 m2 - (t2 - t0) ^ 2 / 4 * (τ + ∑ k, C k * F k) - ∑ k, ε k * F k)
    (s : ℝ) (hs : s ∈ Set.Icc t0 t2) (V : Fin 7 → ℝ) (hV : ∀ k, |V k - pv (p k) sm s| ≤ ε k) :
    0 ≤ famV a b va vb Qa Qb Q s V := by
  have h1 := Phi_interval a b sm va vb Qa Qb Q p hab (m := min m0 m2 - (t2 - t0) ^ 2 / 4 * (τ + ∑ k, C k * F k))
    F C ht h0 h2 hN hτ hF0 hF hW hm0 hm2 hC le_rfl s hs
  have h2' := famV_ge a b sm va vb Qa Qb Q p s V ε F hV hF
  have h3 : 0 ≤ (min m0 m2 - (t2 - t0) ^ 2 / 4 * (τ + ∑ k, C k * F k) - ∑ k, ε k * F k) * N :=
    mul_nonneg hsl hN
  have e : (min m0 m2 - (t2 - t0) ^ 2 / 4 * (τ + ∑ k, C k * F k) - ∑ k, ε k * F k) * N
      = (min m0 m2 - (t2 - t0) ^ 2 / 4 * (τ + ∑ k, C k * F k)) * N - (∑ k, ε k * F k) * N := by ring
  linarith

/-! ### Kernel blocks: symmetry and PSD -/

/-- The literal block is symmetric (kernel check, `O(r²)` entry reads). -/
def symOK (b : LB) : Bool :=
  (List.range b.r).all fun i => (List.range b.r).all fun j => b.ent i j == b.ent j i

theorem ent_symm (b : LB) (h : symOK b = true) {i j : ℕ} (hi : i < b.r) (hj : j < b.r) : b.ent i j = b.ent j i := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h i (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  simpa using this

/-- **PSD from a nonnegative quadratic form** (symmetric on `range r`). -/
theorem psd_of_qf (r : ℕ) (R : ℕ → ℕ → ℝ) (hsym : ∀ i < r, ∀ j < r, R i j = R j i)
    (h : ∀ y : ℕ → ℝ, 0 ≤ ∑ i ∈ range r, ∑ j ∈ range r, y i * R i j * y j) :
    (Matrix.of fun i i' : Fin r => R i i').PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial]
    exact hsym j j.2 i i.2
  · intro x
    set y : ℕ → ℝ := fun a => if ha : a < r then x ⟨a, ha⟩ else 0 with hy
    have hxy : ∀ a : Fin r, y a = x a := fun a => by simp [hy, a.2]
    have e : star x ⬝ᵥ (Matrix.of fun i i' : Fin r => R i i') *ᵥ x
        = ∑ i ∈ range r, ∑ j ∈ range r, y i * R i j * y j := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range r, y i * R i j * y j) r]
      simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun j => y i * R i j * y j) r]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hxy, hxy]; ring
    rw [e]; exact h y

end RieszN7.CapLit.StepP
