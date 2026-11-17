import RieszN7.Core.LDL

/-!
# `RieszN7.Cap.Lit.Base` — the light literal layer of the cap objects (B1, option (b) of `plan_range/PHASE2_cap.md`)

Every reduced block of a cap object is stored with the **trivial decomposition** `ent = 0 · LDLᵀ + Δ` (the family route
needs only the identities of an object, never its PSD), so the block matrix *is* its remainder `Δ`, packed as one
natural-number literal `x` with `r × r` offset-binary fields of `B` bits (upstream `Cert.unpackM`).  The literal lives
in a light module `RieszN7/Cap/<Obj>/Lit.lean` that imports only this file; the object's `TCertR` data (enzo-class,
ThomsonGen closure) and the Step P / margin modules (Mac-class) both refer to it.  `RieszN7.Cap.LitLink` (enzo) proves
once that the object's `Blk.ent` is `LB.ent` of its literal record.

Here: the unpacking functions (copies of upstream `Cert.unpackI`/`Cert.unpackM`, and strict variants for the kernel,
proved equal), the literal records `LB`/`Obj`, the integer matrix combinations used by the LDL and Frobenius checks
(`scl`: congruence by the column scales `cs`; `lin`: integer linear combinations; `dg`: multiples of the identity) with
their entry formulas, and the quadratic forms `qf` with the margin (`ldl_sound`) and Frobenius (`frob_qform`) bounds
restated for them.  Private, AI-written (Phase 2, CAP fork, 2026-11-08), not reviewed.
-/

open Finset

namespace RieszN7.CapLit

open RieszN7.LDL

/-! ### Unpacking -/

/-- `n` offset-binary fields of `B` bits (least significant first); a copy of upstream `Cert.unpackI`. -/
def uI (B : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | n + 1, x => (((x % (1 <<< B) : ℕ) : ℤ) - ((1 <<< (B - 1) : ℕ) : ℤ)) :: uI B n (x >>> B)

/-- `rows` rows of `cols` fields; a copy of upstream `Cert.unpackM`. -/
def uM (B cols : ℕ) : ℕ → ℕ → List (List ℤ)
  | 0, _ => []
  | rows + 1, x => uI B cols (x % (1 <<< (B * cols))) :: uM B cols rows (x >>> (B * cols))

/-- Strict `uI`: the shifted literal is forced (matched) before the recursive call (cf. `Pack.unpackS`). -/
def uIS (B : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | n + 1, x => (((x % (1 <<< B) : ℕ) : ℤ) - ((1 <<< (B - 1) : ℕ) : ℤ)) ::
      (match x >>> B with
       | 0 => uIS B n 0
       | q + 1 => uIS B n (q + 1))

/-- Strict `uM`. -/
def uMS (B cols : ℕ) : ℕ → ℕ → List (List ℤ)
  | 0, _ => []
  | rows + 1, x => uIS B cols (x % (1 <<< (B * cols))) ::
      (match x >>> (B * cols) with
       | 0 => uMS B cols rows 0
       | q + 1 => uMS B cols rows (q + 1))

theorem uIS_eq (B : ℕ) : ∀ n x, uIS B n x = uI B n x
  | 0, _ => rfl
  | n + 1, x => by
    simp only [uIS, uI, List.cons.injEq, true_and]
    split <;> simp_all [uIS_eq B n]

theorem uMS_eq (B cols : ℕ) : ∀ rows x, uMS B cols rows x = uM B cols rows x
  | 0, _ => rfl
  | rows + 1, x => by
    simp only [uMS, uM, List.cons.injEq, uIS_eq]
    refine ⟨trivial, ?_⟩
    split <;> simp_all [uMS_eq B cols rows]

/-! ### Literal records -/

/-- A block literal: size `r`, field width `B`, packed rows `x`. -/
structure LB where
  r : ℕ
  B : ℕ
  x : ℕ

instance : Inhabited LB := ⟨⟨0, 1, 0⟩⟩

namespace LB

/-- The block matrix (rows), decoded strictly. -/
def mat (b : LB) : List (List ℤ) := uMS b.B b.r b.r b.x

/-- Entry `(i, j)`. -/
def ent (b : LB) (i j : ℕ) : ℤ := LDL.ent b.mat i j

theorem mat_eq (b : LB) : b.mat = uM b.B b.r b.r b.x := uMS_eq _ _ _ _

end LB

/-- The literal record of a cap object: scalings and the block literals (SOS `A/B/G`, kernel `P/R`). -/
structure Obj where
  Lam : ℕ
  mA : ℕ
  mB : ℕ
  mG : ℕ
  SA : List LB
  SB : List LB
  SG : List LB
  FP : List LB
  FR : List LB

/-! ### Integer matrix combinations -/

/-- Padded sum of rows. -/
def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

/-- Padded sum of matrices. -/
def mpadd : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], Q => Q
  | p :: P, [] => p :: P
  | p :: P, q :: Q => padd p q :: mpadd P Q

/-- `c · M`. -/
def msc (c : ℤ) (M : List (List ℤ)) : List (List ℤ) := M.map fun row => row.map (c * ·)

/-- The congruence `(cs_i cs_j M_ij)` by the column scales `cs`. -/
def scl (cs : List ℤ) (M : List (List ℤ)) : List (List ℤ) :=
  List.zipWith (fun ci row => List.zipWith (fun cj v => ci * cj * v) cs row) cs M

/-- `Σ_t c_t · scl cs M_t`. -/
def lin (cs : List ℤ) : List (ℤ × List (List ℤ)) → List (List ℤ)
  | [] => []
  | t :: ts => mpadd (msc t.1 (scl cs t.2)) (lin cs ts)

/-- `c · I_n`. -/
def dg (c : ℤ) (n : ℕ) : List (List ℤ) :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then c else 0

/-- The matrix of the LDL / Frobenius checks: `c · I_n + Σ_t c_t · scl cs M_t`. -/
def comb (cs : List ℤ) (ts : List (ℤ × List (List ℤ))) (c : ℤ) (n : ℕ) : List (List ℤ) :=
  mpadd (dg c n) (lin cs ts)

/-- Sum of the squares of all entries. -/
def sumsq (M : List (List ℤ)) : ℤ := (M.map fun row => (row.map fun v => v * v).sum).sum

theorem getD_padd : ∀ (p q : List ℤ) (j : ℕ), (padd p q).getD j 0 = p.getD j 0 + q.getD j 0
  | [], q, j => by simp [padd]
  | a :: as, [], j => by simp [padd]
  | a :: as, b :: bs, 0 => by simp only [padd, List.getD_cons_zero]
  | a :: as, b :: bs, j + 1 => by simp only [padd, List.getD_cons_succ]; exact getD_padd as bs j

theorem ent_mpadd : ∀ (P Q : List (List ℤ)) (i j : ℕ), ent (mpadd P Q) i j = ent P i j + ent Q i j
  | [], Q, i, j => by simp [mpadd, ent]
  | p :: P, [], i, j => by simp [mpadd, ent]
  | p :: P, q :: Q, 0, j => by simp only [mpadd, ent, List.getD_cons_zero]; exact getD_padd p q j
  | p :: P, q :: Q, i + 1, j => by simp only [mpadd, ent, List.getD_cons_succ]; exact ent_mpadd P Q i j

theorem getD_map_mul (c : ℤ) : ∀ (row : List ℤ) (j : ℕ), (row.map (c * ·)).getD j 0 = c * row.getD j 0
  | [], j => by simp
  | a :: as, 0 => by simp
  | a :: as, j + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_mul c as j

theorem ent_msc (c : ℤ) : ∀ (M : List (List ℤ)) (i j : ℕ), ent (msc c M) i j = c * ent M i j
  | [], i, j => by simp [msc, ent]
  | row :: M, 0, j => by simp only [msc, ent, List.map_cons, List.getD_cons_zero]; exact getD_map_mul c row j
  | row :: M, i + 1, j => by
    simp only [msc, ent, List.map_cons, List.getD_cons_succ]; exact ent_msc c M i j

theorem getD_zipWith_mul (c : ℤ) : ∀ (cs row : List ℤ) (j : ℕ),
    (List.zipWith (fun cj v => c * cj * v) cs row).getD j 0 = c * cs.getD j 0 * row.getD j 0
  | [], row, j => by simp
  | a :: as, [], j => by simp
  | a :: as, b :: bs, 0 => by simp only [List.zipWith_cons_cons, List.getD_cons_zero]
  | a :: as, b :: bs, j + 1 => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]; exact getD_zipWith_mul c as bs j

theorem getD_zipRows (cs0 : List ℤ) : ∀ (l : List ℤ) (M : List (List ℤ)) (i j : ℕ),
    ((List.zipWith (fun ci row => List.zipWith (fun cj v => ci * cj * v) cs0 row) l M).getD i []).getD j 0
      = l.getD i 0 * cs0.getD j 0 * (M.getD i []).getD j 0
  | [], M, i, j => by simp
  | a :: l, [], i, j => by simp
  | a :: l, row :: M, 0, j => by
    simp only [List.zipWith_cons_cons, List.getD_cons_zero]; exact getD_zipWith_mul a cs0 row j
  | a :: l, row :: M, i + 1, j => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]; exact getD_zipRows cs0 l M i j

theorem ent_scl (cs : List ℤ) (M : List (List ℤ)) (i j : ℕ) :
    ent (scl cs M) i j = cs.getD i 0 * cs.getD j 0 * ent M i j :=
  getD_zipRows cs cs M i j

theorem getD_range_map {α : Type*} (f : ℕ → α) (d : α) (n i : ℕ) :
    ((List.range n).map f).getD i d = if i < n then f i else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem ent_dg (c : ℤ) (n i j : ℕ) : ent (dg c n) i j = if i < n ∧ j < n ∧ i = j then c else 0 := by
  unfold ent dg
  rw [getD_range_map]
  by_cases hi : i < n
  · rw [if_pos hi, getD_range_map]
    by_cases hj : j < n
    · by_cases h : i = j <;> simp [h, hi, hj]
    · simp [hj]
  · simp [hi]

/-! ### Quadratic forms -/

/-- `xᵀ M x` over `range n`. -/
noncomputable def qf (n : ℕ) (M : List (List ℤ)) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, ∑ j ∈ range n, x i * (ent M i j : ℝ) * x j

/-- `|x|²` over `range n`. -/
noncomputable def nrm (n : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ range n, x i ^ 2

theorem nrm_nonneg (n : ℕ) (x : ℕ → ℝ) : 0 ≤ nrm n x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem qf_mpadd (n : ℕ) (P Q : List (List ℤ)) (x : ℕ → ℝ) : qf n (mpadd P Q) x = qf n P x + qf n Q x := by
  unfold qf
  simp only [ent_mpadd, Int.cast_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem qf_msc (n : ℕ) (c : ℤ) (M : List (List ℤ)) (x : ℕ → ℝ) : qf n (msc c M) x = c * qf n M x := by
  unfold qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ent_msc]; push_cast; ring

theorem qf_scl (n : ℕ) (cs : List ℤ) (M : List (List ℤ)) (x : ℕ → ℝ) :
    qf n (scl cs M) x = qf n M (fun i => (cs.getD i 0 : ℝ) * x i) := by
  unfold qf
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ent_scl]; push_cast; ring

theorem qf_lin (n : ℕ) (cs : List ℤ) (x : ℕ → ℝ) : ∀ ts : List (ℤ × List (List ℤ)),
    qf n (lin cs ts) x = (ts.map fun t => (t.1 : ℝ) * qf n (scl cs t.2) x).sum
  | [] => by simp [lin, qf, ent]
  | t :: ts => by rw [lin, qf_mpadd, qf_msc, qf_lin n cs x ts, List.map_cons, List.sum_cons]

theorem qf_dg (n : ℕ) (c : ℤ) (x : ℕ → ℝ) : qf n (dg c n) x = c * nrm n x := by
  unfold qf nrm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · rw [ent_dg, if_pos ⟨Finset.mem_range.1 hi, Finset.mem_range.1 hi, rfl⟩]; ring
  · intro j hj hji
    rw [ent_dg, if_neg (fun h => hji h.2.2.symm)]; simp
  · intro h; exact absurd hi h

theorem qf_comb (cs : List ℤ) (ts : List (ℤ × List (List ℤ))) (c : ℤ) (n : ℕ) (x : ℕ → ℝ) :
    qf n (comb cs ts c n) x = (c : ℝ) * nrm n x + (ts.map fun t => (t.1 : ℝ) * qf n (scl cs t.2) x).sum := by
  rw [comb, qf_mpadd, qf_dg, qf_lin]

/-- **Margin from an LDL check:** `ldlOK … = true` gives `(μ / sM) |x|² ≤ xᵀ M x`. -/
theorem margin_of_ldl (n : ℕ) (sM sL μ : ℤ) (M L : List (List ℤ)) (d : List ℤ)
    (h : ldlOK n sM sL μ M L d = true) (hsM : 0 < sM) (x : ℕ → ℝ) :
    (μ : ℝ) / sM * nrm n x ≤ qf n M x := by
  have h1 := ldl_sound n sM sL μ M L d h x
  have hs : (0 : ℝ) < sM := by exact_mod_cast hsM
  unfold nrm qf
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  linarith

/-- `Σ_{i<n} f(L_i) ≤ Σ_L f` for `f ≥ 0` with `f default = 0` (missing entries count as `default`). -/
theorem sum_getD_le {α : Type*} (f : α → ℝ) (d : α) (hd : f d = 0) (hf : ∀ a, 0 ≤ f a) :
    ∀ (L : List α) (n : ℕ), ∑ i ∈ range n, f (L.getD i d) ≤ (L.map f).sum
  | [], n => by simp [hd]
  | a :: L, 0 => by
    simp only [Finset.range_zero, Finset.sum_empty, List.map_cons, List.sum_cons]
    exact add_nonneg (hf a) (List.sum_nonneg fun y hy => by obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy; exact hf v)
  | a :: L, n + 1 => by
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    have := sum_getD_le f d hd hf L n
    linarith

/-- Sum of squares of a row, in `ℝ`. -/
noncomputable def rsq (row : List ℤ) : ℝ := (row.map fun v => ((v : ℤ) : ℝ) ^ 2).sum

theorem rsq_nonneg (row : List ℤ) : 0 ≤ rsq row :=
  List.sum_nonneg fun y hy => by obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy; exact sq_nonneg _

theorem sumsq_cast (M : List (List ℤ)) : ((sumsq M : ℤ) : ℝ) = (M.map rsq).sum := by
  unfold sumsq rsq
  rw [Int.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun row _ => ?_
  simp only [Function.comp_apply, Int.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp [sq]

theorem frob_le (M : List (List ℤ)) (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, ((ent M i j : ℤ) : ℝ) ^ 2 ≤ ((sumsq M : ℤ) : ℝ) := by
  rw [sumsq_cast]
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_getD_le rsq [] (by simp [rsq]) rsq_nonneg M n)
  exact sum_getD_le (fun v : ℤ => ((v : ℤ) : ℝ) ^ 2) 0 (by simp) (fun _ => sq_nonneg _) (M.getD i []) n

/-- **Frobenius bound for `qf`:** `sumsq M ≤ F²`, `F ≥ 0` give `|xᵀ M x| ≤ F |x|²`. -/
theorem qf_frob (n : ℕ) (M : List (List ℤ)) (x : ℕ → ℝ) {F : ℝ} (hF : 0 ≤ F)
    (h : ((sumsq M : ℤ) : ℝ) ≤ F ^ 2) : |qf n M x| ≤ F * nrm n x :=
  frob_qform n (fun i j => ((ent M i j : ℤ) : ℝ)) x hF ((frob_le M n).trans h)

end RieszN7.CapLit
