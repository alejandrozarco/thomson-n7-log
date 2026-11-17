import RieszN7.Core.LDL

/-!
# `RieszN7.Core.LDLK` — the LDL margin check with Kronecker-packed row identities (O(n²) kernel steps)

`ldlOK` (`RieszN7.Core.LDL`) recomputes `Σ_k L_ik d_k L_jk` for every `(i, j)` with small-integer list products:
`O(n³)` kernel steps, measured 17.5 s at n = 40 and > 3 GB / > 280 s at n = 83 (Phase 1).  `kldlOK` takes in addition
the witness rows `Δ = sM·M − sL·L diag(d) Lᵀ` and checks, per row `i`, the single integer identity at the Kronecker
point `B` (`pk B v = Σ_j v_j B^j`)

    pk B (sM·M_i − Δ_i) = sL · Σ_k (L_ik d_k) · pk B (column k of L),

which costs `O(n)` big-integer products per row.  With `|sM M_ij − Δ_ij| ≤ E`, `|L| ≤ mL`, `0 ≤ d ≤ md` and
`E + sL·n·mL²·md < B`, every coefficient of the difference is `< B` in absolute value, so the identity forces
`Δ_ij = sM M_ij − sL (L D Lᵀ)_ij` for all `j` (`kron_unique`), and the row test is `ddRow` on `Δ_i` exactly as in
`ldlOK`.  Soundness is by reduction: `kldlOK … = true → ldlOK … = true` (`kldl_imp`), a propositional implication (the
kernel never evaluates `ldlOK`), hence `kldl_sound` from `ldl_sound`.

Kernel cost model (v2): the kernel does not memoise, so every derived list that is used more than once is recomputed
at each use (v1 passed `(tr n L).map (pk B)` to every row: n^3.8 measured).  v2 consumes every derived object once:
the packed columns `Cs` are a literal argument, checked once against `colsPk B n L` (Horner over the rows, `O(n²)`);
symmetry of `M` is the Kronecker identity `colsPk B n M = M.map (pk B)` with `|M_ij| ≤ EM`, `2·EM < B` (`O(n²)`),
instead of the structural transpose.
Private prototype (Phase 1 / §5-rev), AI-written, not reviewed.
-/

open Finset RieszN7.LDL

namespace RieszN7.LDLK

/-- `Σ_j v_j B^j` (Horner). -/
def pk (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: as => a + B * pk B as

/-- `Σ_k a_k c_k` (stops at the shortest list). -/
def dot2 : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, c :: cs => a * c + dot2 as cs

/-- Pointwise product (stops at the shortest list). -/
def mul2 : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => a * b :: mul2 as bs

/-- `sM·m − x` pointwise (stops at the shortest list). -/
def sub2 (sM : ℤ) : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | m :: ms, x :: xs => (sM * m - x) :: sub2 sM ms xs

/-- Pad with zeros (or truncate) to length `k`. -/
def padTo : ℕ → List ℤ → List ℤ
  | 0, _ => []
  | k + 1, [] => 0 :: padTo k []
  | k + 1, a :: as => a :: padTo k as

/-- Pointwise sum (stops at the shortest list). -/
def vadd : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => (a + b) :: vadd as bs

def vscale (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: as => c * a :: vscale c as

/-- Packed columns `(Σ_j rows_j[k] B^j)_{k < n}`, by Horner over the rows (each row consumed once). -/
def colsPk (B : ℤ) (n : ℕ) : List (List ℤ) → List ℤ
  | [] => padTo n []
  | r :: rs => vadd (padTo n r) (vscale B (colsPk B n rs))

/-- The rows: coefficient bound, Kronecker identity, diagonal dominance of `Δ_i − μ e_i`. -/
def krows (sM sL μ E B : ℤ) (Cs d : List ℤ) : ℕ → List (List ℤ) → List (List ℤ) → List (List ℤ) → Bool
  | _, [], _, _ => true
  | _, _ :: _, [], _ => true
  | _, _ :: _, _ :: _, [] => true
  | i, Mi :: Ms, Li :: Ls, Di :: Ds =>
      let R := sub2 sM Mi Di
      R.all (fun v => decide (|v| ≤ E)) && decide (pk B R = sL * dot2 (mul2 Li d) Cs) && ddRow i μ Di &&
        krows sM sL μ E B Cs d (i + 1) Ms Ls Ds

def kldlOK (n : ℕ) (sM sL μ E EM mL md B : ℤ) (M L : List (List ℤ)) (d : List ℤ) (D : List (List ℤ))
    (Cs : List ℤ) : Bool :=
  M.length == n && L.length == n && d.length == n && D.length == n && M.all (fun r => r.length == n) &&
    L.all (fun r => decide (r.length ≤ n)) && D.all (fun r => r.length == n) &&
    d.all (fun v => decide (0 ≤ v ∧ v ≤ md)) && decide (0 ≤ sL) && decide (0 ≤ mL) && decide (0 ≤ md) &&
    decide (0 ≤ E) && L.all (fun r => r.all (fun v => decide (|v| ≤ mL))) &&
    decide (E + sL * n * mL * mL * md < B) &&
    M.all (fun r => r.all (fun v => decide (|v| ≤ EM))) && decide (2 * EM < B) &&
    decide (colsPk B n M = M.map (pk B)) && decide (colsPk B n L = Cs) &&
    krows sM sL μ E B Cs d 0 M L D

/-- The Gram entry `(L diag(d) Lᵀ)_ij`. -/
def gram (L : List (List ℤ)) (d : List ℤ) (n i j : ℕ) : ℤ := ∑ k ∈ range n, ent L i k * d.getD k 0 * ent L j k

/-! ### List lemmas -/

theorem pk_eq (B : ℤ) (l : List ℤ) : ∀ N : ℕ, l.length ≤ N → pk B l = ∑ j ∈ range N, l.getD j 0 * B ^ j := by
  induction l with
  | nil => intro N _; simp [pk]
  | cons a as ih =>
    intro N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ']
    simp only [pk, ih N' (by simp at hN; omega), Finset.mul_sum, List.getD_cons_succ, List.getD_cons_zero,
      pow_zero, mul_one]
    have hs : ∑ j ∈ range N', B * (as.getD j 0 * B ^ j) = ∑ j ∈ range N', as.getD j 0 * B ^ (j + 1) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [hs]; ring

theorem dot2_eq (a : List ℤ) : ∀ (c : List ℤ) (N : ℕ), a.length ≤ N →
    dot2 a c = ∑ k ∈ range N, a.getD k 0 * c.getD k 0 := by
  induction a with
  | nil => intro c N _; simp [dot2]
  | cons x as ih =>
    intro c N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ']
    rcases c with _ | ⟨y, cs⟩
    · simp [dot2]
    simp only [dot2, List.getD_cons_succ, List.getD_cons_zero, ih cs N' (by simp at hN; omega)]
    ring

theorem mul2_getD : ∀ (a b : List ℤ) (k : ℕ), (mul2 a b).getD k 0 = a.getD k 0 * b.getD k 0
  | [], _, _ => by simp [mul2]
  | _ :: _, [], _ => by simp [mul2]
  | _ :: _, _ :: _, 0 => by simp [mul2]
  | _ :: as, _ :: bs, k + 1 => by simp only [mul2, List.getD_cons_succ]; exact mul2_getD as bs k

theorem mul2_length_le : ∀ (a b : List ℤ), (mul2 a b).length ≤ a.length
  | [], _ => by simp [mul2]
  | _ :: _, [] => by simp [mul2]
  | _ :: as, _ :: bs => by simpa [mul2] using mul2_length_le as bs

theorem sub2_length (sM : ℤ) : ∀ (a b : List ℤ), (sub2 sM a b).length = min a.length b.length
  | [], _ => by simp [sub2]
  | _ :: _, [] => by simp [sub2]
  | _ :: as, _ :: bs => by simp only [sub2, List.length_cons, sub2_length sM as bs]; omega

theorem sub2_getD (sM : ℤ) : ∀ (a b : List ℤ) (j : ℕ), j < a.length → j < b.length →
    (sub2 sM a b).getD j 0 = sM * a.getD j 0 - b.getD j 0
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: _, _ :: _, 0, _, _ => by simp [sub2]
  | _ :: as, _ :: bs, j + 1, h1, h2 => by
      simp only [sub2, List.getD_cons_succ]
      exact sub2_getD sM as bs j (by simp at h1; omega) (by simp at h2; omega)

theorem padTo_length : ∀ (k : ℕ) (l : List ℤ), (padTo k l).length = k
  | 0, _ => rfl
  | k + 1, [] => by simp [padTo, padTo_length k []]
  | k + 1, _ :: as => by simp [padTo, padTo_length k as]

theorem padTo_getD : ∀ (k : ℕ) (l : List ℤ) (j : ℕ), j < k → (padTo k l).getD j 0 = l.getD j 0
  | 0, _, _, h => by omega
  | _ + 1, [], 0, _ => by simp [padTo]
  | k + 1, [], j + 1, h => by
      have := padTo_getD k [] j (by omega)
      simp only [padTo, List.getD_cons_succ, this, List.getD_nil]
  | _ + 1, _ :: _, 0, _ => by simp [padTo]
  | k + 1, _ :: as, j + 1, h => by
      simp only [padTo, List.getD_cons_succ]; exact padTo_getD k as j (by omega)

theorem vadd_length : ∀ (a b : List ℤ), (vadd a b).length = min a.length b.length
  | [], _ => by simp [vadd]
  | _ :: _, [] => by simp [vadd]
  | _ :: as, _ :: bs => by simp only [vadd, List.length_cons, vadd_length as bs]; omega

theorem vadd_getD : ∀ (a b : List ℤ) (j : ℕ), j < a.length → j < b.length →
    (vadd a b).getD j 0 = a.getD j 0 + b.getD j 0
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: _, _ :: _, 0, _, _ => by simp [vadd]
  | _ :: as, _ :: bs, j + 1, h1, h2 => by
      simp only [vadd, List.getD_cons_succ]
      exact vadd_getD as bs j (by simp at h1; omega) (by simp at h2; omega)

theorem vscale_length (c : ℤ) : ∀ (a : List ℤ), (vscale c a).length = a.length
  | [] => rfl
  | _ :: as => by simp [vscale, vscale_length c as]

theorem vscale_getD (c : ℤ) : ∀ (a : List ℤ) (j : ℕ), (vscale c a).getD j 0 = c * a.getD j 0
  | [], _ => by simp [vscale]
  | _ :: _, 0 => by simp [vscale]
  | _ :: as, j + 1 => by simp only [vscale, List.getD_cons_succ]; exact vscale_getD c as j

theorem colsPk_length (B : ℤ) (n : ℕ) : ∀ (rows : List (List ℤ)), (colsPk B n rows).length = n
  | [] => padTo_length n []
  | r :: rs => by simp only [colsPk, vadd_length, padTo_length, vscale_length, colsPk_length B n rs, min_self]

theorem colsPk_getD (B : ℤ) (n : ℕ) : ∀ (rows : List (List ℤ)) (k : ℕ), k < n →
    (colsPk B n rows).getD k 0 = ∑ j ∈ range rows.length, (rows.getD j []).getD k 0 * B ^ j
  | [], k, hk => by
      show (padTo n []).getD k 0 = _
      rw [padTo_getD n [] k hk]; simp
  | r :: rs, k, hk => by
      show (vadd (padTo n r) (vscale B (colsPk B n rs))).getD k 0 = _
      rw [vadd_getD _ _ k (by rw [padTo_length]; exact hk) (by rw [vscale_length, colsPk_length]; exact hk),
        padTo_getD n r k hk, vscale_getD, colsPk_getD B n rs k hk, List.length_cons, Finset.sum_range_succ',
        Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
      have hs : ∑ j ∈ range rs.length, B * ((rs.getD j []).getD k 0 * B ^ j)
          = ∑ j ∈ range rs.length, (rs.getD j []).getD k 0 * B ^ (j + 1) :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [hs]; ring

theorem tr_length : ∀ (n : ℕ) (M : List (List ℤ)), (tr n M).length = n
  | 0, _ => rfl
  | k + 1, M => by simp [tr, tr_length k]

theorem krows_spec (sM sL μ E B : ℤ) (Cs d : List ℤ) :
    ∀ (Ms Ls Ds : List (List ℤ)) (i0 : ℕ), krows sM sL μ E B Cs d i0 Ms Ls Ds = true →
      ∀ k, k < Ms.length → k < Ls.length → k < Ds.length →
        ((sub2 sM (Ms.getD k []) (Ds.getD k [])).all (fun v => decide (|v| ≤ E)) = true ∧
          pk B (sub2 sM (Ms.getD k []) (Ds.getD k [])) = sL * dot2 (mul2 (Ls.getD k []) d) Cs) ∧
        ddRow (i0 + k) μ (Ds.getD k []) = true := by
  intro Ms
  induction Ms with
  | nil => intro Ls Ds i0 _ k hk; simp at hk
  | cons Mi Ms ih =>
    intro Ls Ds i0 h k hk hkL hkD
    rcases Ls with _ | ⟨Li, Ls⟩
    · simp at hkL
    rcases Ds with _ | ⟨Di, Ds⟩
    · simp at hkD
    simp only [krows, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases k with _ | k
    · simpa using h.1
    · have := ih Ls Ds (i0 + 1) h.2 k (by simp at hk; omega) (by simp at hkL; omega) (by simp at hkD; omega)
      rw [show i0 + (k + 1) = i0 + 1 + k by omega]
      simpa using this

theorem rowsOK_of (sM sL μ : ℤ) (L : List (List ℤ)) (d : List ℤ) :
    ∀ (Ms Ls : List (List ℤ)) (i0 : ℕ), Ms.length = Ls.length →
      (∀ k, k < Ms.length → ddRow (i0 + k) μ (drow sM sL (Ls.getD k []) d (Ms.getD k []) L) = true) →
      rowsOK sM sL μ L d i0 Ms Ls = true := by
  intro Ms
  induction Ms with
  | nil => intro Ls i0 _ _; simp [rowsOK]
  | cons Mi Ms ih =>
    intro Ls i0 hlen h
    rcases Ls with _ | ⟨Li, Ls⟩
    · simp at hlen
    simp only [rowsOK, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by simp), ih Ls (i0 + 1) (by simpa using hlen) (fun k hk => ?_)⟩
    have := h (k + 1) (by simp; omega)
    rw [show i0 + (k + 1) = i0 + 1 + k by omega] at this
    simpa using this

/-! ### Balanced base-`B` uniqueness -/

theorem kron_unique (B : ℤ) (hB : 0 < B) : ∀ (N : ℕ) (e : ℕ → ℤ), (∀ j < N, |e j| < B) →
    ∑ j ∈ range N, e j * B ^ j = 0 → ∀ j < N, e j = 0 := by
  intro N
  induction N with
  | zero => intro e _ _ j hj; omega
  | succ N ih =>
    intro e hb hs
    rw [Finset.sum_range_succ'] at hs
    have hsplit : ∑ j ∈ range N, e (j + 1) * B ^ (j + 1) = B * ∑ j ∈ range N, e (j + 1) * B ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, pow_zero, mul_one] at hs
    have hS0 : ∑ j ∈ range N, e (j + 1) * B ^ j = 0 := by
      by_contra hne
      have h1 : B ≤ |B * ∑ j ∈ range N, e (j + 1) * B ^ j| := by
        rw [abs_mul, abs_of_pos hB]
        have : 1 ≤ |∑ j ∈ range N, e (j + 1) * B ^ j| := Int.one_le_abs hne
        nlinarith
      have h2 : |B * ∑ j ∈ range N, e (j + 1) * B ^ j| = |e 0| := by
        rw [show B * ∑ j ∈ range N, e (j + 1) * B ^ j = -(e 0) by linarith, abs_neg]
      have := hb 0 (by omega)
      linarith
    have he0 : e 0 = 0 := by rw [hS0, mul_zero] at hs; linarith
    have hrest := ih (fun j => e (j + 1)) (fun j hj => hb (j + 1) (by omega)) hS0
    intro j hj
    rcases j with _ | j
    · exact he0
    · exact hrest j (by omega)

/-! ### Soundness -/

theorem kldl_imp (n : ℕ) (sM sL μ E EM mL md B : ℤ) (M L : List (List ℤ)) (d : List ℤ) (D : List (List ℤ))
    (Cs : List ℤ) (h : kldlOK n sM sL μ E EM mL md B M L d D Cs = true) : ldlOK n sM sL μ M L d = true := by
  simp only [kldlOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hMn, hLn⟩, hdn⟩, hDn⟩, hMr⟩, hLr⟩, hDr⟩, hd⟩, hsL⟩, hmL⟩, hmd⟩, hE⟩, hLb⟩, hB⟩,
    hMb⟩, hEM⟩, hsymK⟩, hCs⟩, hrows⟩ := h
  -- shapes and bounds
  have rowM : ∀ i < n, (M.getD i []).length = n := fun i hi => by
    rw [List.getD_eq_getElem M [] (by omega : i < M.length)]; exact hMr _ (List.getElem_mem _)
  have rowD : ∀ i < n, (D.getD i []).length = n := fun i hi => by
    rw [List.getD_eq_getElem D [] (by omega : i < D.length)]; exact hDr _ (List.getElem_mem _)
  have rowL : ∀ i < n, (L.getD i []).length ≤ n := fun i hi => by
    rw [List.getD_eq_getElem L [] (by omega : i < L.length)]; exact hLr _ (List.getElem_mem _)
  have entB : ∀ i k, |ent L i k| ≤ mL := by
    intro i k
    unfold ent
    by_cases hi : i < L.length
    · rw [List.getD_eq_getElem L [] hi]
      by_cases hk : k < L[i].length
      · rw [List.getD_eq_getElem _ 0 hk]; exact hLb _ (List.getElem_mem _) _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ 0 (by omega)]; simpa using hmL
    · rw [List.getD_eq_default L [] (by omega)]; simpa using hmL
  have dB : ∀ k, |d.getD k 0| ≤ md := by
    intro k
    by_cases hk : k < d.length
    · rw [List.getD_eq_getElem d 0 hk]
      have := hd _ (List.getElem_mem hk)
      rw [abs_of_nonneg this.1]; exact this.2
    · rw [List.getD_eq_default d 0 (by omega)]; simpa using hmd
  have hG : ∀ i j, |gram L d n i j| ≤ (n : ℤ) * (mL * md * mL) := by
    intro i j
    unfold gram
    calc |∑ k ∈ range n, ent L i k * d.getD k 0 * ent L j k|
        ≤ ∑ k ∈ range n, |ent L i k * d.getD k 0 * ent L j k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range n, mL * md * mL := Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (entB i k) (dB k) (abs_nonneg _) hmL) (entB j k) (abs_nonneg _)
            (mul_nonneg hmL hmd)
      _ = (n : ℤ) * (mL * md * mL) := by simp
  have hBpos : 0 < B := by
    have : 0 ≤ sL * (n : ℤ) * mL * mL * md :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsL (Nat.cast_nonneg n)) hmL) hmL) hmd
    linarith
  -- the columns of L at the Kronecker point
  have hcol : ∀ k < n, Cs.getD k 0 = ∑ j ∈ range n, (L.getD j []).getD k 0 * B ^ j := by
    intro k hk
    rw [← hCs, colsPk_getD B n L k hk, hLn]
  -- symmetry of M from the Kronecker identity colsPk B n M = M.map (pk B)
  have entMB : ∀ i < n, ∀ j < n, |(M.getD i []).getD j 0| ≤ EM := by
    intro i hi j hj
    rw [List.getD_eq_getElem M [] (by omega : i < M.length)]
    have hl := hMr _ (List.getElem_mem (by omega : i < M.length))
    rw [List.getD_eq_getElem _ 0 (by omega : j < M[i].length)]
    exact hMb _ (List.getElem_mem _) _ (List.getElem_mem _)
  have symE : ∀ i < n, ∀ j < n, ent M i j = ent M j i := by
    intro i hi
    have h1 : (colsPk B n M).getD i 0 = ∑ j ∈ range n, (M.getD j []).getD i 0 * B ^ j := by
      rw [colsPk_getD B n M i hi, hMn]
    have h2 : (M.map (pk B)).getD i 0 = ∑ j ∈ range n, (M.getD i []).getD j 0 * B ^ j := by
      have : (M.map (pk B)).getD i 0 = pk B (M.getD i []) := by
        simpa [pk] using List.getD_map (l := M) (d := []) (n := i) (pk B)
      rw [this, pk_eq B _ n (le_of_eq (rowM i hi))]
    have hsum : ∑ j ∈ range n, ((M.getD j []).getD i 0 - (M.getD i []).getD j 0) * B ^ j = 0 := by
      have e : ∑ j ∈ range n, ((M.getD j []).getD i 0 - (M.getD i []).getD j 0) * B ^ j
          = ∑ j ∈ range n, (M.getD j []).getD i 0 * B ^ j - ∑ j ∈ range n, (M.getD i []).getD j 0 * B ^ j := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e, ← h1, ← h2, hsymK, sub_self]
    have hb : ∀ j < n, |(M.getD j []).getD i 0 - (M.getD i []).getD j 0| < B := by
      intro j hj
      have a1 := abs_le.mp (entMB j hj i hi)
      have a2 := abs_le.mp (entMB i hi j hj)
      rw [abs_lt]; constructor <;> linarith
    intro j hj
    have h0 : (M.getD j []).getD i 0 - (M.getD i []).getD j 0 = 0 :=
      kron_unique B hBpos n (fun j => (M.getD j []).getD i 0 - (M.getD i []).getD j 0) hb hsum j hj
    show (M.getD i []).getD j 0 = (M.getD j []).getD i 0
    linarith
  have hsym : tr n M = M := by
    apply List.ext_getElem
    · rw [tr_length, hMn]
    · intro j h1 h2
      have hj : j < n := by rw [tr_length] at h1; exact h1
      rw [← List.getD_eq_getElem _ [] h1, ← List.getD_eq_getElem _ [] h2, tr_getD n M j hj]
      apply List.ext_getElem
      · rw [List.length_map, hMn, rowM j hj]
      · intro i h3 h4
        have hi : i < n := by rw [List.length_map, hMn] at h3; exact h3
        rw [← List.getD_eq_getElem _ 0 h3, ← List.getD_eq_getElem _ 0 h4]
        have h5 : (M.map (fun r => r.getD j 0)).getD i 0 = (M.getD i []).getD j 0 := by
          simpa using List.getD_map (l := M) (d := []) (n := i) (fun r => r.getD j 0)
        rw [h5]
        exact symE i hi j hj
  -- each checked identity pins the witness row
  have rowEq : ∀ i < n, ∀ j < n, ent D i j = sM * ent M i j - sL * gram L d n i j := by
    intro i hi
    obtain ⟨⟨hall, hid⟩, -⟩ := krows_spec sM sL μ E B Cs d M L D 0 hrows i (by omega)
      (by omega) (by omega)
    obtain ⟨R, hR⟩ : ∃ R, R = sub2 sM (M.getD i []) (D.getD i []) := ⟨_, rfl⟩
    rw [← hR] at hall hid
    have hRl : R.length = n := by rw [hR, sub2_length, rowM i hi, rowD i hi, min_self]
    have hRj : ∀ j < n, R.getD j 0 = sM * (M.getD i []).getD j 0 - (D.getD i []).getD j 0 := fun j hj => by
      rw [hR]; exact sub2_getD sM _ _ j (by rw [rowM i hi]; exact hj) (by rw [rowD i hi]; exact hj)
    have hRb : ∀ j < n, |R.getD j 0| ≤ E := fun j hj => by
      rw [List.all_eq_true] at hall
      have := hall _ (List.getElem_mem (by omega : j < R.length))
      rw [List.getD_eq_getElem R 0 (by omega)]; simpa using this
    have hlhs : pk B R = ∑ j ∈ range n, R.getD j 0 * B ^ j := pk_eq B R n (by omega)
    have hrhs : dot2 (mul2 (L.getD i []) d) Cs = ∑ j ∈ range n, gram L d n i j * B ^ j := by
      rw [dot2_eq _ _ n ((mul2_length_le _ _).trans (rowL i hi))]
      calc ∑ k ∈ range n, (mul2 (L.getD i []) d).getD k 0 * Cs.getD k 0
          = ∑ k ∈ range n, ∑ j ∈ range n, ent L i k * d.getD k 0 * ent L j k * B ^ j := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [mul2_getD, hcol k (mem_range.1 hk), Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [ent]; ring
        _ = ∑ j ∈ range n, gram L d n i j * B ^ j := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [gram, Finset.sum_mul]
    have hbd : ∀ j < n, |R.getD j 0 - sL * gram L d n i j| < B := by
      intro j hj
      rw [abs_lt]
      have h2 := abs_le.mp (hRb j hj)
      have h3 := abs_le.mp (hG i j)
      have h5 := mul_le_mul_of_nonneg_left h3.1 hsL
      have h6 := mul_le_mul_of_nonneg_left h3.2 hsL
      have h7 := mul_neg sL ((n : ℤ) * (mL * md * mL))
      have h4 : sL * ((n : ℤ) * (mL * md * mL)) = sL * n * mL * mL * md := by ring
      constructor <;> linarith
    have hsum0 : ∑ j ∈ range n, (R.getD j 0 - sL * gram L d n i j) * B ^ j = 0 := by
      have e1 : ∑ j ∈ range n, (R.getD j 0 - sL * gram L d n i j) * B ^ j
          = ∑ j ∈ range n, R.getD j 0 * B ^ j - sL * ∑ j ∈ range n, gram L d n i j * B ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1, ← hlhs, hid, hrhs]; ring
    have hz := kron_unique B hBpos n (fun j => R.getD j 0 - sL * gram L d n i j) hbd hsum0
    intro j hj
    have h0 : R.getD j 0 - sL * gram L d n i j = 0 := hz j hj
    have h1 := hRj j hj
    unfold ent
    linarith
  -- hence the rows of `ldlOK`
  simp only [ldlOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hMn, hLn⟩, hdn⟩, hMr⟩, hLr⟩, fun v hv => (hd v hv).1⟩, hsL⟩, hsym⟩, ?_⟩
  refine rowsOK_of sM sL μ L d M L 0 (by rw [hMn, hLn]) (fun i hi => ?_)
  rw [hMn] at hi
  obtain ⟨-, hdd⟩ := krows_spec sM sL μ E B Cs d M L D 0 hrows i (by omega) (by omega)
    (by omega)
  have heq : drow sM sL (L.getD i []) d (M.getD i []) L = D.getD i [] := by
    apply List.ext_getElem
    · rw [drow_length, rowM i hi, hLn, min_self, rowD i hi]
    · intro j h1 h2
      have hj : j < n := by rw [rowD i hi] at h2; exact h2
      rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2,
        drow_getD sM sL _ d _ L j (by rw [rowM i hi]; exact hj) (by omega), dot3_eq _ d _ n (rowL i hi)]
      have := rowEq i hi j hj
      simp only [ent, gram] at this
      linarith
  rw [heq]; exact hdd

/-- **Soundness of `kldlOK`:** `μ |x|² ≤ sM · xᵀ M x`. -/
theorem kldl_sound (n : ℕ) (sM sL μ E EM mL md B : ℤ) (M L : List (List ℤ)) (d : List ℤ) (D : List (List ℤ))
    (Cs : List ℤ) (h : kldlOK n sM sL μ E EM mL md B M L d D Cs = true) (x : ℕ → ℝ) :
    (μ : ℝ) * ∑ i ∈ range n, x i ^ 2
      ≤ (sM : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, x i * (ent M i j : ℝ) * x j :=
  ldl_sound n sM sL μ M L d (kldl_imp n sM sL μ E EM mL md B M L d D Cs h) x

/-! ### Row-chunked `ldlOK` (§5-rev: the variant used for blocks larger than ~40)

`ldlOK = ldlPre && rowsOK …` definitionally; `rowsOK` over `M = take k M ++ drop k M` is the conjunction of the two row
ranges (`rowsOK_append`), so the rows of one large block can be checked by `decide +kernel` in separate modules
(measured: 83 × 83 block in chunks of 21 rows, ≤ 73 s and ≤ 2.2 GB each) and combined without kernel evaluation. -/

/-- The non-row part of `ldlOK` (shapes, `d ≥ 0`, `sL ≥ 0`, symmetry). -/
def ldlPre (n : ℕ) (sL : ℤ) (M L : List (List ℤ)) (d : List ℤ) : Bool :=
  M.length == n && L.length == n && d.length == n && M.all (fun r => r.length == n) &&
    L.all (fun r => decide (r.length ≤ n)) && d.all (fun v => decide (0 ≤ v)) && decide (0 ≤ sL) &&
    decide (tr n M = M)

theorem ldlOK_eq (n : ℕ) (sM sL μ : ℤ) (M L : List (List ℤ)) (d : List ℤ) :
    ldlOK n sM sL μ M L d = (ldlPre n sL M L d && rowsOK sM sL μ L d 0 M L) := rfl

theorem rowsOK_append (sM sL μ : ℤ) (L : List (List ℤ)) (d : List ℤ) :
    ∀ (M1 L1 M2 L2 : List (List ℤ)) (i0 : ℕ), M1.length = L1.length →
      rowsOK sM sL μ L d i0 (M1 ++ M2) (L1 ++ L2)
        = (rowsOK sM sL μ L d i0 M1 L1 && rowsOK sM sL μ L d (i0 + M1.length) M2 L2) := by
  intro M1
  induction M1 with
  | nil =>
    intro L1 M2 L2 i0 hlen
    rcases L1 with _ | ⟨l, L1⟩
    · simp [rowsOK]
    · simp at hlen
  | cons m M1 ih =>
    intro L1 M2 L2 i0 hlen
    rcases L1 with _ | ⟨l, L1⟩
    · simp at hlen
    simp only [List.cons_append, rowsOK, List.length_cons]
    rw [ih L1 M2 L2 (i0 + 1) (by simpa using hlen), Bool.and_assoc,
      show i0 + 1 + M1.length = i0 + (M1.length + 1) by omega]

/-- Two row chunks `[0, k)` and `[k, n)` give `ldlOK`; apply repeatedly (to `drop k`) for more chunks. -/
theorem ldlOK_of_split (n : ℕ) (sM sL μ : ℤ) (M L : List (List ℤ)) (d : List ℤ) (k : ℕ) (hk : k ≤ n)
    (hpre : ldlPre n sL M L d = true)
    (hA : rowsOK sM sL μ L d 0 (M.take k) (L.take k) = true)
    (hB : rowsOK sM sL μ L d k (M.drop k) (L.drop k) = true) : ldlOK n sM sL μ M L d = true := by
  have h0 := hpre
  simp only [ldlPre, Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨hMn, hLn⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h0
  have hsplit := rowsOK_append sM sL μ L d (M.take k) (L.take k) (M.drop k) (L.drop k) 0
    (by simp [List.length_take, hMn, hLn])
  rw [List.take_append_drop, List.take_append_drop] at hsplit
  have hlk : 0 + (M.take k).length = k := by rw [List.length_take, hMn, Nat.zero_add]; omega
  rw [hlk, hA, hB, Bool.and_self] at hsplit
  rw [ldlOK_eq, hpre, hsplit, Bool.and_self]

/-! ### Unit test (`L = 0`, `sL = 0`, `Δ = M`) -/

theorem test_small :
    kldlOK 2 1 0 1 0 2 0 0 5 [[2, -1], [-1, 2]] [[0], [0, 0]] [0, 0] [[2, -1], [-1, 2]] [0, 0] = true := by
  decide +kernel

end RieszN7.LDLK
