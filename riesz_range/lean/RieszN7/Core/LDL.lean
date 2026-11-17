import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `RieszN7.Core.LDL` — PSD with margin for integer symmetric matrices, checked in the kernel (LEAN_PLAN_range.md §3.0.7)

Data: `M` (rows, `n × n`), `L` (rows, row `i` of length `≤ n`, lower triangular in practice), pivots `d`, scales
`sM`, `sL ≥ 0` and a margin `μ`.  `ldlOK` checks in the kernel, with row-wise dot products (no `getD` in the
`O(n³)` part):

* `M` is symmetric (`tr n M = M`, structural transpose), the shapes, `d ≥ 0`, `sL ≥ 0`;
* for every row `i`, with `Δ := sM·M − sL·L diag(d) Lᵀ − μ I`: `Σ_{j≠i} |Δ_ij| ≤ Δ_ii` (diagonal dominance).

Soundness (`ldl_sound`): `μ Σ x_i² ≤ sM · xᵀ M x` for every real `x`.  `qform_dd_nonneg` is copied from the upstream
Coulomb proof (`ThomsonGen/Cert1.lean`, upstream `Cert.qform_dd_nonneg`) so that this module does not import that
closure.  Also `frob_bound` (Cauchy–Schwarz for `xᵀ R y`) and `psd_perturb` (absorbing `Σ (c_k − c_k⁰) R_k`).
Private prototype (Phase 1), AI-written, not reviewed.
-/

open Finset

namespace RieszN7.LDL

/-- Entry `(i, j)` of a matrix given by rows. -/
def ent (M : List (List ℤ)) (i j : ℕ) : ℤ := (M.getD i []).getD j 0

/-- `Σ_k a_k b_k c_k` (stops at the shortest list). -/
def dot3 : List ℤ → List ℤ → List ℤ → ℤ
  | [], _, _ => 0
  | _ :: _, [], _ => 0
  | _ :: _, _ :: _, [] => 0
  | a :: as, b :: bs, c :: cs => a * b * c + dot3 as bs cs

/-- Row `i` of `sM·M − sL·L diag(d) Lᵀ` from row `Mi` of `M` and row `Li` of `L` (`L` = all rows). -/
def drow (sM sL : ℤ) (Li d : List ℤ) : List ℤ → List (List ℤ) → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | m :: ms, Lj :: Ls => (sM * m - sL * dot3 Li d Lj) :: drow sM sL Li d ms Ls

/-- Diagonal dominance of row `i` of `r − μ e_i`. -/
def ddRow (i : ℕ) (μ : ℤ) (r : List ℤ) : Bool :=
  decide ((r.map (fun v => |v|)).sum - |r.getD i 0| + μ ≤ r.getD i 0)

def rowsOK (sM sL μ : ℤ) (L : List (List ℤ)) (d : List ℤ) : ℕ → List (List ℤ) → List (List ℤ) → Bool
  | _, [], _ => true
  | _, _ :: _, [] => true
  | i, Mi :: Ms, Li :: Ls => ddRow i μ (drow sM sL Li d Mi L) && rowsOK sM sL μ L d (i + 1) Ms Ls

/-- Structural transpose: the first `n` columns. -/
def tr : ℕ → List (List ℤ) → List (List ℤ)
  | 0, _ => []
  | k + 1, M => M.map (fun r => r.headD 0) :: tr k (M.map List.tail)

def ldlOK (n : ℕ) (sM sL μ : ℤ) (M L : List (List ℤ)) (d : List ℤ) : Bool :=
  M.length == n && L.length == n && d.length == n && M.all (fun r => r.length == n) &&
    L.all (fun r => decide (r.length ≤ n)) && d.all (fun v => decide (0 ≤ v)) && decide (0 ≤ sL) &&
    decide (tr n M = M) && rowsOK sM sL μ L d 0 M L

/-! ### List ↔ finite sums -/

theorem dot3_eq (a : List ℤ) : ∀ (b c : List ℤ) (N : ℕ), a.length ≤ N →
    dot3 a b c = ∑ k ∈ range N, a.getD k 0 * b.getD k 0 * c.getD k 0 := by
  induction a with
  | nil => intro b c N _; simp [dot3]
  | cons x as ih =>
    intro b c N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    have hN' : as.length ≤ N' := by simp at hN; omega
    rw [Finset.sum_range_succ']
    rcases b with _ | ⟨y, bs⟩
    · simp [dot3]
    rcases c with _ | ⟨z, cs⟩
    · simp [dot3]
    simp only [dot3, List.getD_cons_succ, List.getD_cons_zero, ih bs cs N' hN']
    ring

theorem list_sum_eq (r : List ℤ) : ∀ N : ℕ, r.length ≤ N → r.sum = ∑ k ∈ range N, r.getD k 0 := by
  induction r with
  | nil => intro N _; simp
  | cons x xs ih =>
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ', List.sum_cons, ih N' (by simp at hN; omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem drow_length (sM sL : ℤ) (Li d : List ℤ) :
    ∀ (Mi : List ℤ) (L : List (List ℤ)), (drow sM sL Li d Mi L).length = min Mi.length L.length := by
  intro Mi
  induction Mi with
  | nil => intro L; simp [drow]
  | cons m ms ih =>
    intro L
    rcases L with _ | ⟨Lj, Ls⟩
    · simp [drow]
    · simp only [drow, List.length_cons, ih Ls]; omega

theorem drow_getD (sM sL : ℤ) (Li d : List ℤ) :
    ∀ (Mi : List ℤ) (L : List (List ℤ)) (j : ℕ), j < Mi.length → j < L.length →
      (drow sM sL Li d Mi L).getD j 0 = sM * Mi.getD j 0 - sL * dot3 Li d (L.getD j []) := by
  intro Mi
  induction Mi with
  | nil => intro L j h; simp at h
  | cons m ms ih =>
    intro L j hj hL
    rcases L with _ | ⟨Lj, Ls⟩
    · simp at hL
    rcases j with _ | j
    · simp [drow]
    · simp only [drow, List.getD_cons_succ]
      exact ih Ls j (by simp at hj; omega) (by simp at hL; omega)

theorem rowsOK_spec (sM sL μ : ℤ) (L : List (List ℤ)) (d : List ℤ) :
    ∀ (Ms Ls : List (List ℤ)) (i0 : ℕ), rowsOK sM sL μ L d i0 Ms Ls = true →
      ∀ k, k < Ms.length → k < Ls.length →
        ddRow (i0 + k) μ (drow sM sL (Ls.getD k []) d (Ms.getD k []) L) = true := by
  intro Ms
  induction Ms with
  | nil => intro Ls i0 _ k hk; simp at hk
  | cons Mi Ms ih =>
    intro Ls i0 h k hk hkL
    rcases Ls with _ | ⟨Li, Ls⟩
    · simp at hkL
    simp only [rowsOK, Bool.and_eq_true] at h
    rcases k with _ | k
    · simpa using h.1
    · have := ih Ls (i0 + 1) h.2 k (by simp at hk; omega) (by simp at hkL; omega)
      have e : i0 + (k + 1) = i0 + 1 + k := by omega
      rw [e]
      simpa using this

theorem tr_getD : ∀ (n : ℕ) (M : List (List ℤ)) (j : ℕ), j < n →
    (tr n M).getD j [] = M.map (fun r => r.getD j 0) := by
  intro n
  induction n with
  | zero => intro M j h; omega
  | succ k ih =>
    intro M j hj
    rcases j with _ | j
    · simp only [tr, List.getD_cons_zero]
      congr 1; funext r; cases r <;> rfl
    · simp only [tr, List.getD_cons_succ]
      rw [ih _ j (by omega), List.map_map]
      congr 1; funext r; cases r <;> simp

/-! ### Diagonal dominance (copied from upstream `Cert.qform_dd_nonneg`, `ThomsonGen/Cert1.lean`) -/

lemma qform_dd_nonneg (r : ℕ) (Δ : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hs : ∀ i ∈ Finset.range r, ∀ j ∈ Finset.range r, Δ i j = Δ j i)
    (hdd : ∀ i ∈ Finset.range r,
      ∑ j ∈ Finset.range r, (if i = j then 0 else |Δ i j|) ≤ Δ i i) :
    0 ≤ ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, x i * Δ i j * x j := by
  set s := Finset.range r with hs_def
  have key : ∀ i j, (if i = j then Δ i i * x i ^ 2 else 0)
      - (if i = j then 0 else |Δ i j|) * (x i ^ 2 + x j ^ 2) / 2 ≤ x i * Δ i j * x j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos rfl]; nlinarith
    · rw [if_neg h, if_neg h]
      have h1 : 2 * (|x i| * |x j|) ≤ |x i| ^ 2 + |x j| ^ 2 := by
        nlinarith [sq_nonneg (|x i| - |x j|)]
      rw [sq_abs, sq_abs] at h1
      have h2 : |x i * Δ i j * x j| = |Δ i j| * (|x i| * |x j|) := by
        rw [abs_mul, abs_mul]; ring
      have h3 : -(x i * Δ i j * x j) ≤ |x i * Δ i j * x j| := neg_le_abs _
      rw [h2] at h3
      have h4 : 0 ≤ |Δ i j| := abs_nonneg _
      nlinarith
  have hsum := Finset.sum_le_sum (s := s) fun i _ =>
    Finset.sum_le_sum (s := s) fun j _ => key i j
  refine le_trans ?_ hsum
  simp only [Finset.sum_sub_distrib]
  have e1 : ∑ i ∈ s, ∑ j ∈ s, (if i = j then Δ i i * x i ^ 2 else 0)
      = ∑ i ∈ s, Δ i i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq]; simp [hi]
  set o : ℕ → ℕ → ℝ := fun i j => if i = j then 0 else |Δ i j| with ho
  have osymm : ∀ i ∈ s, ∀ j ∈ s, o j i = o i j := by
    intro i hi j hj
    simp only [ho]
    by_cases h : i = j
    · subst h; simp
    · have h' : ¬ j = i := fun e => h e.symm
      rw [if_neg h, if_neg h', hs i hi j hj]
  have e2 : ∑ i ∈ s, ∑ j ∈ s, o i j * (x i ^ 2 + x j ^ 2) / 2
      = ∑ i ∈ s, (∑ j ∈ s, o i j) * x i ^ 2 := by
    have ha : ∑ i ∈ s, ∑ j ∈ s, o i j * (x i ^ 2 + x j ^ 2) / 2
        = ∑ i ∈ s, ∑ j ∈ s, o i j * x i ^ 2 / 2 + ∑ i ∈ s, ∑ j ∈ s, o i j * x j ^ 2 / 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ i ∈ s, ∑ j ∈ s, o i j * x j ^ 2 / 2 = ∑ i ∈ s, ∑ j ∈ s, o i j * x i ^ 2 / 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      rw [osymm j hj i hi]
    have hc : ∑ i ∈ s, ∑ j ∈ s, o i j * x i ^ 2 / 2
        = (∑ i ∈ s, (∑ j ∈ s, o i j) * x i ^ 2) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, Finset.sum_div]
    rw [ha, hb, hc]; ring
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i hi => ?_
  have := hdd i hi
  nlinarith [sq_nonneg (x i)]

/-! ### Soundness -/

/-- `Σ_ij x_i (Σ_k l_ik d_k l_jk) x_j = Σ_k d_k (Σ_i l_ik x_i)² ≥ 0` for `d ≥ 0`. -/
theorem gram_nonneg (n : ℕ) (l : ℕ → ℕ → ℝ) (dd : ℕ → ℝ) (hd : ∀ k, 0 ≤ dd k) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, x i * (∑ k ∈ range n, l i k * dd k * l j k) * x j := by
  have h1 : ∀ i j, x i * (∑ k ∈ range n, l i k * dd k * l j k) * x j
      = ∑ k ∈ range n, dd k * (l i k * x i) * (l j k * x j) := by
    intro i j
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e : ∑ i ∈ range n, ∑ j ∈ range n, x i * (∑ k ∈ range n, l i k * dd k * l j k) * x j
      = ∑ k ∈ range n, dd k * (∑ i ∈ range n, l i k * x i) ^ 2 := by
    calc ∑ i ∈ range n, ∑ j ∈ range n, x i * (∑ k ∈ range n, l i k * dd k * l j k) * x j
        = ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, dd k * (l i k * x i) * (l j k * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
      _ = ∑ i ∈ range n, ∑ k ∈ range n, ∑ j ∈ range n, dd k * (l i k * x i) * (l j k * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k ∈ range n, ∑ i ∈ range n, ∑ j ∈ range n, dd k * (l i k * x i) * (l j k * x j) :=
          Finset.sum_comm
      _ = ∑ k ∈ range n, dd k * (∑ i ∈ range n, l i k * x i) ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hd k) (sq_nonneg _)

/-- **Soundness of `ldlOK`:** `μ |x|² ≤ sM · xᵀ M x`. -/
theorem ldl_sound (n : ℕ) (sM sL μ : ℤ) (M L : List (List ℤ)) (d : List ℤ)
    (h : ldlOK n sM sL μ M L d = true) (x : ℕ → ℝ) :
    (μ : ℝ) * ∑ i ∈ range n, x i ^ 2
      ≤ (sM : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, x i * (ent M i j : ℝ) * x j := by
  simp only [ldlOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hMn, hLn⟩, hdn⟩, hMr⟩, hLr⟩, hd⟩, hsL⟩, hsym⟩, hrows⟩ := h
  -- shapes
  have rowM : ∀ i < n, (M.getD i []).length = n := fun i hi => by
    rw [List.getD_eq_getElem M [] (by omega : i < M.length)]; exact hMr _ (List.getElem_mem _)
  have rowL : ∀ i < n, (L.getD i []).length ≤ n := fun i hi => by
    rw [List.getD_eq_getElem L [] (by omega : i < L.length)]; exact hLr _ (List.getElem_mem _)
  have dnn : ∀ k, 0 ≤ d.getD k 0 := fun k => by
    by_cases hk : k < d.length
    · rw [List.getD_eq_getElem d 0 hk]; exact hd _ (List.getElem_mem _)
    · exact le_of_eq (List.getD_eq_default d 0 (by omega : d.length ≤ k)).symm
  -- symmetry of M
  have symM : ∀ i < n, ∀ j < n, ent M i j = ent M j i := by
    intro i hi j _
    unfold ent
    conv_lhs => rw [← hsym]
    rw [tr_getD n M i hi]
    have := List.getD_map (l := M) (d := []) (n := j) (fun r => r.getD i 0)
    simpa using this
  -- the Gram part and Δ (integers)
  set G : ℕ → ℕ → ℤ := fun i j => ∑ k ∈ range n, ent L i k * d.getD k 0 * ent L j k with hG
  set Δ : ℕ → ℕ → ℤ := fun i j => sM * ent M i j - sL * G i j - (if i = j then μ else 0) with hΔ
  have symG : ∀ i j, G i j = G j i := fun i j => by
    simp only [hG]; exact Finset.sum_congr rfl fun k _ => by ring
  have symΔ : ∀ i ∈ range n, ∀ j ∈ range n, Δ i j = Δ j i := by
    intro i hi j hj
    simp only [hΔ, symM i (mem_range.1 hi) j (mem_range.1 hj), symG i j]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  -- the checked row
  have rowEnt : ∀ i < n, ∀ j < n,
      (drow sM sL (L.getD i []) d (M.getD i []) L).getD j 0 = sM * ent M i j - sL * G i j := by
    intro i hi j hj
    rw [drow_getD sM sL (L.getD i []) d (M.getD i []) L j (by rw [rowM i hi]; exact hj) (by omega),
      dot3_eq (L.getD i []) d (L.getD j []) n (rowL i hi)]
    rfl
  have ddΔ : ∀ i ∈ range n, ∑ j ∈ range n, (if i = j then (0 : ℤ) else |Δ i j|) ≤ Δ i i := by
    intro i hi
    have hi' := mem_range.1 hi
    have hrow := rowsOK_spec sM sL μ L d M L 0 hrows i (by omega) (by omega)
    simp only [Nat.zero_add] at hrow
    set r := drow sM sL (L.getD i []) d (M.getD i []) L with hr
    have hlen : r.length = n := by rw [hr, drow_length, rowM i hi', hLn, min_self]
    have hrj : ∀ j < n, r.getD j 0 = sM * ent M i j - sL * G i j := fun j hj => by
      rw [hr]; exact rowEnt i hi' j hj
    simp only [ddRow, decide_eq_true_eq] at hrow
    have hsum : (r.map (fun v => |v|)).sum = ∑ j ∈ range n, |r.getD j 0| := by
      rw [list_sum_eq _ n (by simp [hlen])]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := List.getD_map (l := r) (d := 0) (n := j) (fun v : ℤ => |v|)
      simpa using this
    have hoff : ∀ j ∈ range n, (if i = j then (0 : ℤ) else |Δ i j|) = (if i = j then 0 else |r.getD j 0|) := by
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · rw [if_neg hij, if_neg hij, hrj j (mem_range.1 hj)]
        simp [hΔ, hij]
    have hsplit : ∑ j ∈ range n, |r.getD j 0|
        = ∑ j ∈ range n, (if i = j then (0 : ℤ) else |r.getD j 0|) + |r.getD i 0| := by
      have : ∀ j, |r.getD j 0| = (if i = j then (0 : ℤ) else |r.getD j 0|) + (if i = j then |r.getD j 0| else 0) := by
        intro j; split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hi]
    have hdiag : Δ i i = r.getD i 0 - μ := by
      rw [hrj i hi']; simp [hΔ]
    rw [Finset.sum_congr rfl hoff, hdiag]
    linarith
  -- assemble
  have hΔR : 0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, x i * (Δ i j : ℝ) * x j := qform_dd_nonneg n (fun i j => (Δ i j : ℝ)) x
    (fun i hi j hj => by simp only [symΔ i hi j hj])
    (fun i hi => by
      have h2 : ((∑ j ∈ range n, (if i = j then (0 : ℤ) else |Δ i j|) : ℤ) : ℝ) ≤ ((Δ i i : ℤ) : ℝ) := by
        exact_mod_cast ddΔ i hi
      push_cast at h2
      refine le_trans (le_of_eq ?_) h2
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp)
  have hGR : 0 ≤ ∑ i ∈ range n, ∑ j ∈ range n,
      x i * (∑ k ∈ range n, (ent L i k : ℝ) * (d.getD k 0 : ℝ) * (ent L j k : ℝ)) * x j :=
    gram_nonneg n (fun i k => (ent L i k : ℝ)) (fun k => (d.getD k 0 : ℝ)) (fun k => by exact_mod_cast dnn k) x
  have hsLR : (0 : ℝ) ≤ sL := by exact_mod_cast hsL
  have hterm : ∀ i j, (sM : ℝ) * (x i * (ent M i j : ℝ) * x j)
      = x i * (Δ i j : ℝ) * x j
        + (sL : ℝ) * (x i * (∑ k ∈ range n, (ent L i k : ℝ) * (d.getD k 0 : ℝ) * (ent L j k : ℝ)) * x j)
        + (if i = j then (μ : ℝ) * x i ^ 2 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp only [hΔ, hG, eq_self_iff_true, if_true]; push_cast; ring
    · simp only [hΔ, hG, if_neg hij]; push_cast; ring
  have hdiagsum : ∑ i ∈ range n, ∑ j ∈ range n, (if i = j then (μ : ℝ) * x i ^ 2 else 0)
      = (μ : ℝ) * ∑ i ∈ range n, x i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq, if_pos hi]
  have e : (sM : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, x i * (ent M i j : ℝ) * x j
      = ∑ i ∈ range n, ∑ j ∈ range n, x i * (Δ i j : ℝ) * x j
        + (sL : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n,
            x i * (∑ k ∈ range n, (ent L i k : ℝ) * (d.getD k 0 : ℝ) * (ent L j k : ℝ)) * x j
        + (μ : ℝ) * ∑ i ∈ range n, x i ^ 2 := by
    rw [← hdiagsum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  rw [e]
  have := mul_nonneg hsLR hGR
  linarith

/-! ### Frobenius bound and perturbation -/

/-- Cauchy–Schwarz: `(xᵀ R y)² ≤ ‖R‖_F² |x|² |y|²`. -/
theorem frob_bound (n : ℕ) (R : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) :
    (∑ i ∈ range n, ∑ j ∈ range n, x i * R i j * y j) ^ 2
      ≤ (∑ i ∈ range n, ∑ j ∈ range n, R i j ^ 2) * ((∑ i ∈ range n, x i ^ 2) * ∑ j ∈ range n, y j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range n ×ˢ range n) (fun p => R p.1 p.2) (fun p => x p.1 * y p.2)
  simp only [Finset.sum_product] at h
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, x i * R i j * y j = ∑ i ∈ range n, ∑ j ∈ range n, R i j * (x i * y j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : (∑ i ∈ range n, x i ^ 2) * ∑ j ∈ range n, y j ^ 2 = ∑ i ∈ range n, ∑ j ∈ range n, (x i * y j) ^ 2 := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  exact h

/-- `|xᵀ R x| ≤ F |x|²` from `‖R‖_F² ≤ F²`, `F ≥ 0`. -/
theorem frob_qform (n : ℕ) (R : ℕ → ℕ → ℝ) (x : ℕ → ℝ) {F : ℝ} (hF : 0 ≤ F)
    (hR : ∑ i ∈ range n, ∑ j ∈ range n, R i j ^ 2 ≤ F ^ 2) :
    |∑ i ∈ range n, ∑ j ∈ range n, x i * R i j * x j| ≤ F * ∑ i ∈ range n, x i ^ 2 := by
  have h := frob_bound n R x x
  have hN : 0 ≤ ∑ i ∈ range n, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : (∑ i ∈ range n, ∑ j ∈ range n, x i * R i j * x j) ^ 2 ≤ (F * ∑ i ∈ range n, x i ^ 2) ^ 2 := by
    refine h.trans ?_
    rw [mul_pow, sq (∑ i ∈ range n, x i ^ 2)]
    exact mul_le_mul_of_nonneg_right hR (mul_nonneg hN hN)
  have := sq_le_sq.mp h2
  rwa [abs_of_nonneg (mul_nonneg hF hN)] at this

/-- **Perturbation:** `Q ≥ μ N`, `|q_k| ≤ F_k N`, `|δ_k| ≤ ε_k` ⇒ `Q + Σ δ_k q_k ≥ (μ − Σ ε_k F_k) N`. -/
theorem psd_perturb {ι : Type*} (K : Finset ι) {Q N μ : ℝ} (q δ ε F : ι → ℝ) (hQ : μ * N ≤ Q) (hN : 0 ≤ N)
    (hq : ∀ k ∈ K, |q k| ≤ F k * N) (hδ : ∀ k ∈ K, |δ k| ≤ ε k) :
    (μ - ∑ k ∈ K, ε k * F k) * N ≤ Q + ∑ k ∈ K, δ k * q k := by
  have h1 : ∀ k ∈ K, -(ε k * F k * N) ≤ δ k * q k := by
    intro k hk
    have hε : 0 ≤ ε k := (abs_nonneg _).trans (hδ k hk)
    have h2 : |δ k * q k| ≤ ε k * (F k * N) := by
      rw [abs_mul]; exact mul_le_mul (hδ k hk) (hq k hk) (abs_nonneg _) hε
    have h3 := neg_abs_le (δ k * q k)
    linarith
  have hs := Finset.sum_le_sum h1
  rw [Finset.sum_neg_distrib] at hs
  have e : ∑ k ∈ K, ε k * F k * N = (∑ k ∈ K, ε k * F k) * N := by rw [Finset.sum_mul]
  rw [e] at hs
  nlinarith

/-! ### Unit test: `[[2, -1], [-1, 2]] ⪰ 1·I` with `L = [[1], [-1, 2]]`... (trivial `L = 0`, `sL = 0`) -/

theorem test_small : ldlOK 2 1 0 1 [[2, -1], [-1, 2]] [[0], [0, 0]] [0, 0] = true := by decide +kernel

end RieszN7.LDL
