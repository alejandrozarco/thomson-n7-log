import ThomsonGen.CertT

/-!
# Facially reduced blocks (`NBlk`): PSD by congruence

Sharp cap certificates (Riesz `s = 2`, log) live on a face of the PSD cone: every kernel block `F`
and every typed SOS block `B` is `N · B′ · Nᵀ` with an `m × r` basis `N` (`r ≤ m`, possibly `r = 0`)
and an `r × r` block `B′` that is positive definite and certified as usual (`LDLᵀ` + diagonally
dominant remainder, `Blk.ok`).  The expanded `m × m` block is singular, so it cannot be certified by
upstream's `Blk.ok`; instead:

* `NBlk` stores the integer basis `N` (rows) and the packed reduced block `B′`;
* `NBlk.expand` is the ordinary `Blk` `⟨[], [], N·ent(B′)·Nᵀ⟩` (pure remainder), computed by the
  kernel, so that all of upstream's identity machinery (`fmat`, `fkE`, `sqfF`, `hybChk`, …) applies
  unchanged to the expanded data;
* the only new fact is positivity by congruence: `xᵀ (N B′ Nᵀ) x = (Nᵀx)ᵀ B′ (Nᵀx) ≥ 0`
  (`qf_expand_nonneg`, `fmat_psd_expand`, `sqfE_nonneg_expand`).

Kernel-agnostic; generic in the degree, block sizes and multiplier lists.  Upstream modules are
untouched.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `padd` ← `SlabOneD.padd`; `fmat_psd_expand` ← `Cert.fmat_psd`;
  `tsum_nonneg_N` ← `Cert.tsum_nonneg`; `alpha_nonneg'` ← `Cert.TCert.alpha_nonneg`;
  `beta_nonneg'` ← `Cert.TCert.beta_nonneg`; `gamma_nonneg'` ← `Cert.TCert.gamma_nonneg`;
  `pscale` ← `SlabOneD.pscale`; `length_unpackM` ← `Cert.rowsN_length`.
-/

open Real

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert
open ThreePoint

/-- A facially reduced block: integer basis `N` (`m` rows of `r` entries) and the packed reduced
block `B′` of size `r` (`mkBlk r Bd Bl BD xd xl xD`). -/
structure NBlk where
  N : List (List ℤ)
  r : ℕ
  Bd : ℕ
  Bl : ℕ
  BD : ℕ
  xd : ℕ
  xl : ℕ
  xD : ℕ

namespace NBlk

/-- The reduced block `B′`. -/
def inner (nb : NBlk) : Blk := mkBlk nb.r nb.Bd nb.Bl nb.BD nb.xd nb.xl nb.xD

/-- Entry `N_{a i}` (missing entries count as `0`). -/
def n (nb : NBlk) (a i : ℕ) : ℤ := (nb.N.getD a []).getD i 0

/-! ### List matrix arithmetic (structural recursion, kernel-friendly)

`expandΔ` must be cheap in the kernel: the cap's SOS blocks have `m = 84`, `r = 82`.  The product
`N · ent(B′) · Nᵀ` is computed as `matMulT (matMul N (entMat B′)) N` with structural recursion only
(no random access); its entries are related to the random-access sums (`Blk.ent`, `getD`) by the
lemmas below, which need only length bounds `≤ r` (missing entries count as `0` on both sides). -/

def padd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

def pscale (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

def dot : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dot as bs

/-- `∑_i x_i · M_i` (row vector times matrix). -/
def vecMat : List ℤ → List (List ℤ) → List ℤ
  | a :: as, row :: rows => padd (pscale a row) (vecMat as rows)
  | _, _ => []

/-- `A · B`. -/
def matMul (A B : List (List ℤ)) : List (List ℤ) := A.map fun row => vecMat row B

/-- `A · Bᵀ` (`B` given by rows). -/
def matMulT (A B : List (List ℤ)) : List (List ℤ) := A.map fun ra => B.map fun rb => dot ra rb

def matAdd : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], B => B
  | ra :: A, [] => ra :: A
  | ra :: A, rb :: B => padd ra rb :: matAdd A B

/-- `x yᵀ`. -/
def outer (x y : List ℤ) : List (List ℤ) := x.map fun a => pscale a y

/-- `∑_q d_q l_q l_qᵀ`. -/
def ldl : List ℤ → List (List ℤ) → List (List ℤ)
  | dq :: ds, lq :: ls => matAdd (outer (pscale dq lq) lq) (ldl ds ls)
  | _, _ => []

/-- `ent(B′)` as a list matrix: `∑_q d_q l_q l_qᵀ + Δ`. -/
def entMat (b : Blk) : List (List ℤ) := matAdd (ldl b.d b.l) b.Δ

/-- The expanded remainder `N · ent(B′) · Nᵀ`. -/
def expandΔ (nb : NBlk) : List (List ℤ) := matMulT (matMul nb.N (entMat nb.inner)) nb.N

/-- The expanded block: no pivots, remainder `N · ent(B′) · Nᵀ` (`N.length` rows). -/
def expand (nb : NBlk) : Blk := ⟨[], [], nb.expandΔ⟩

/-- Specification entry `(N · ent(B′) · Nᵀ)_{a c}` (random-access sums). -/
def eent (nb : NBlk) (a c : ℕ) : ℤ :=
  ((List.range nb.r).map fun i =>
    ((List.range nb.r).map fun j => nb.n a i * nb.inner.ent nb.r i j * nb.n c j).sum).sum

/-- The computable check: the reduced block passes upstream's fast PSD check and the rows of `N`
have at most `r` entries. -/
def okN (nb : NBlk) : Bool := okF nb.r nb.inner && nb.N.all fun row => decide (row.length ≤ nb.r)

/-! #### `getD` lemmas -/

lemma getD_padd (p q : List ℤ) (j : ℕ) : (padd p q).getD j 0 = p.getD j 0 + q.getD j 0 := by
  induction p generalizing q j with
  | nil => simp [padd]
  | cons a as ih =>
    cases q with
    | nil => simp [padd]
    | cons b bs =>
      cases j with
      | zero => simp [padd]
      | succ j => simp only [padd, List.getD_cons_succ]; exact ih bs j

lemma getD_pscale (c : ℤ) (p : List ℤ) (j : ℕ) : (pscale c p).getD j 0 = c * p.getD j 0 := by
  induction p generalizing j with
  | nil => simp [pscale]
  | cons a as ih =>
    cases j with
    | zero => simp [pscale]
    | succ j => simp only [pscale, List.map_cons, List.getD_cons_succ]; exact ih j

lemma length_padd (p q : List ℤ) : (padd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a as ih =>
    cases q with
    | nil => simp [padd]
    | cons b bs => simp [padd, ih] <;> omega

lemma length_pscale (c : ℤ) (p : List ℤ) : (pscale c p).length = p.length := by
  simp [pscale]

lemma dot_eq_sum (r : ℕ) : ∀ (x y : List ℤ), x.length ≤ r → y.length ≤ r →
    dot x y = ∑ i ∈ Finset.range r, x.getD i 0 * y.getD i 0 := by
  induction r with
  | zero =>
    intro x y hx hy
    have : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [dot]
  | succ r ih =>
    intro x y hx hy
    rw [Finset.sum_range_succ']
    cases x with
    | nil => simp [dot]
    | cons a as =>
      cases y with
      | nil => simp [dot]
      | cons b bs =>
        simp only [dot, List.getD_cons_succ, List.getD_cons_zero]
        rw [ih as bs (by simp at hx; omega) (by simp at hy; omega)]
        ring

lemma getD_vecMat (r : ℕ) : ∀ (x : List ℤ) (M : List (List ℤ)), x.length ≤ r → M.length ≤ r →
    ∀ j, (vecMat x M).getD j 0 = ∑ i ∈ Finset.range r, x.getD i 0 * (M.getD i []).getD j 0 := by
  induction r with
  | zero =>
    intro x M hx hM j
    have : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [vecMat]
  | succ r ih =>
    intro x M hx hM j
    rw [Finset.sum_range_succ']
    cases x with
    | nil => simp [vecMat]
    | cons a as =>
      cases M with
      | nil => simp [vecMat]
      | cons row rows =>
        simp only [vecMat, getD_padd, getD_pscale, List.getD_cons_succ, List.getD_cons_zero]
        rw [ih as rows (by simp at hx; omega) (by simp at hM; omega) j]
        ring

lemma length_vecMat_le (r : ℕ) : ∀ (x : List ℤ) (M : List (List ℤ)),
    (∀ row ∈ M, row.length ≤ r) → (vecMat x M).length ≤ r := by
  intro x M hM
  induction x generalizing M with
  | nil => simp [vecMat]
  | cons a as ih =>
    cases M with
    | nil => simp [vecMat]
    | cons row rows =>
      simp only [vecMat, length_padd, length_pscale]
      have h1 := hM row (by simp)
      have h2 := ih rows (fun ρ hρ => hM ρ (by simp [hρ]))
      omega

lemma getD_map_nil {α : Type*} (f : α → List ℤ) (L : List α) (i : ℕ) (hi : L.length ≤ i) :
    (L.map f).getD i [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hi)]
  rfl

lemma getD_map_lt {α : Type*} (f : α → List ℤ) (L : List α) (i : ℕ) (hi : i < L.length) :
    (L.map f).getD i [] = f (L[i]'hi) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

lemma getD_map_lt' {α : Type*} (g : α → ℤ) (L : List α) (i : ℕ) (hi : i < L.length) :
    (L.map g).getD i 0 = g (L[i]'hi) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

lemma getD_nil_of_le {α : Type*} (L : List α) (d : α) (i : ℕ) (hi : L.length ≤ i) :
    L.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma getD_outer (x y : List ℤ) (i j : ℕ) :
    ((outer x y).getD i []).getD j 0 = x.getD i 0 * y.getD j 0 := by
  induction x generalizing i with
  | nil => simp [outer]
  | cons a as ih =>
    cases i with
    | zero => simp only [outer, List.map_cons, List.getD_cons_zero]; exact getD_pscale a y j
    | succ i => simp only [outer, List.map_cons, List.getD_cons_succ]; exact ih i

lemma getD_matAdd (A B : List (List ℤ)) (i j : ℕ) :
    ((matAdd A B).getD i []).getD j 0 = (A.getD i []).getD j 0 + (B.getD i []).getD j 0 := by
  induction A generalizing B i with
  | nil => simp [matAdd]
  | cons ra A ih =>
    cases B with
    | nil => simp [matAdd]
    | cons rb B =>
      cases i with
      | zero => simp only [matAdd, List.getD_cons_zero]; exact getD_padd ra rb j
      | succ i => simp only [matAdd, List.getD_cons_succ]; exact ih B i

lemma getD_ldl (r : ℕ) : ∀ (d : List ℤ) (l : List (List ℤ)), d.length ≤ r → l.length ≤ r →
    ∀ i j, ((ldl d l).getD i []).getD j 0
      = ∑ q ∈ Finset.range r, d.getD q 0 * (l.getD q []).getD i 0 * (l.getD q []).getD j 0 := by
  induction r with
  | zero =>
    intro d l hd hl i j
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ldl]
  | succ r ih =>
    intro d l hd hl i j
    rw [Finset.sum_range_succ']
    cases d with
    | nil => simp [ldl]
    | cons dq ds =>
      cases l with
      | nil => simp [ldl]
      | cons lq ls =>
        simp only [ldl, getD_matAdd, getD_outer, getD_pscale, List.getD_cons_succ,
          List.getD_cons_zero]
        rw [ih ds ls (by simp at hd; omega) (by simp at hl; omega) i j]
        ring

/-- `entMat` computes `Blk.ent`. -/
lemma getD_entMat (r : ℕ) (b : Blk) (hd : b.d.length ≤ r) (hl : b.l.length ≤ r) (i j : ℕ) :
    ((entMat b).getD i []).getD j 0 = b.ent r i j := by
  simp only [entMat, getD_matAdd, Blk.ent, Blk.list_sum_range_map, Blk.dq, Blk.lq, Blk.del]
  rw [getD_ldl r b.d b.l hd hl i j]

lemma getD_matMul (r : ℕ) (A B : List (List ℤ)) (hA : ∀ row ∈ A, row.length ≤ r)
    (hB : B.length ≤ r) (a j : ℕ) :
    ((matMul A B).getD a []).getD j 0
      = ∑ i ∈ Finset.range r, (A.getD a []).getD i 0 * (B.getD i []).getD j 0 := by
  by_cases ha : a < A.length
  · have h1 : (matMul A B).getD a [] = vecMat (A[a]'ha) B := getD_map_lt _ A a ha
    rw [h1, getD_vecMat r (A[a]'ha) B (hA _ (List.getElem_mem ha)) hB j,
      List.getD_eq_getElem A [] ha]
  · push_neg at ha
    have h1 : (matMul A B).getD a [] = [] := getD_map_nil _ A a ha
    rw [h1, getD_nil_of_le A [] a ha]
    simp

lemma getD_matMulT (A B : List (List ℤ)) (a c : ℕ) (ha : a < A.length) (hc : c < B.length) :
    ((matMulT A B).getD a []).getD c 0 = dot (A.getD a []) (B.getD c []) := by
  have h1 : (matMulT A B).getD a [] = B.map fun rb => dot (A[a]'ha) rb := getD_map_lt _ A a ha
  rw [h1, getD_map_lt' _ B c hc, List.getD_eq_getElem A [] ha, List.getD_eq_getElem B [] hc]

lemma length_unpackI (B : ℕ) : ∀ (n x : ℕ), (unpackI B n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp [unpackI, length_unpackI B n]

lemma length_unpackM (B cols : ℕ) : ∀ (rows x : ℕ), (unpackM B cols rows x).length = rows
  | 0, _ => rfl
  | rows + 1, x => by simp [unpackM, length_unpackM B cols rows]

lemma inner_d_length (nb : NBlk) : nb.inner.d.length = nb.r := length_unpackI _ _ _
lemma inner_l_length (nb : NBlk) : nb.inner.l.length = nb.r := length_unpackM _ _ _ _

lemma okN_parts {nb : NBlk} (h : nb.okN = true) :
    nb.inner.ok nb.r = true ∧ ∀ row ∈ nb.N, row.length ≤ nb.r := by
  simp only [okN, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨okF_sound h.1, h.2⟩

/-! #### Length bounds -/

lemma mem_unpackM_length (B cols : ℕ) : ∀ (rows x : ℕ) (row : List ℤ),
    row ∈ unpackM B cols rows x → row.length = cols
  | 0, _, _, h => by simp [unpackM] at h
  | rows + 1, x, row, h => by
    simp only [unpackM, List.mem_cons] at h
    rcases h with rfl | h
    · exact length_unpackI _ _ _
    · exact mem_unpackM_length B cols rows _ row h

lemma length_matAdd (A B : List (List ℤ)) : (matAdd A B).length = max A.length B.length := by
  induction A generalizing B with
  | nil => simp [matAdd]
  | cons ra A ih =>
    cases B with
    | nil => simp [matAdd]
    | cons rb B => simp [matAdd, ih] <;> omega

lemma mem_matAdd_length {r : ℕ} : ∀ (A B : List (List ℤ)), (∀ ρ ∈ A, ρ.length ≤ r) →
    (∀ ρ ∈ B, ρ.length ≤ r) → ∀ ρ ∈ matAdd A B, ρ.length ≤ r
  | [], B, _, hB, ρ, h => hB ρ (by simpa [matAdd] using h)
  | ra :: A, [], hA, _, ρ, h => hA ρ (by simpa [matAdd] using h)
  | ra :: A, rb :: B, hA, hB, ρ, h => by
    simp only [matAdd, List.mem_cons] at h
    rcases h with rfl | h
    · rw [length_padd]
      have := hA ra (by simp); have := hB rb (by simp); omega
    · exact mem_matAdd_length A B (fun σ hσ => hA σ (by simp [hσ]))
        (fun σ hσ => hB σ (by simp [hσ])) ρ h

lemma mem_outer_length {r : ℕ} (x y : List ℤ) (hy : y.length ≤ r) :
    ∀ ρ ∈ outer x y, ρ.length ≤ r := by
  intro ρ h
  simp only [outer, List.mem_map] at h
  obtain ⟨a, -, rfl⟩ := h
  simpa [length_pscale] using hy

lemma length_outer (x y : List ℤ) : (outer x y).length = x.length := by simp [outer]

lemma ldl_bounds {r : ℕ} : ∀ (d : List ℤ) (l : List (List ℤ)), (∀ ρ ∈ l, ρ.length ≤ r) →
    (ldl d l).length ≤ r ∧ ∀ ρ ∈ ldl d l, ρ.length ≤ r
  | [], _, _ => by simp [ldl]
  | _ :: _, [], _ => by simp [ldl]
  | dq :: ds, lq :: ls, hl => by
    have hlq := hl lq (by simp)
    have ih := ldl_bounds ds ls (fun ρ hρ => hl ρ (by simp [hρ]))
    simp only [ldl]
    constructor
    · rw [length_matAdd, length_outer, length_pscale]; omega
    · exact mem_matAdd_length _ _ (mem_outer_length _ _ hlq) ih.2

lemma entMat_bounds (nb : NBlk) :
    (entMat nb.inner).length ≤ nb.r ∧ ∀ ρ ∈ entMat nb.inner, ρ.length ≤ nb.r := by
  have hl : ∀ ρ ∈ nb.inner.l, ρ.length ≤ nb.r := fun ρ h =>
    (mem_unpackM_length _ _ _ _ ρ h).le
  have hΔ : ∀ ρ ∈ nb.inner.Δ, ρ.length ≤ nb.r := fun ρ h =>
    (mem_unpackM_length _ _ _ _ ρ h).le
  have hldl := ldl_bounds nb.inner.d nb.inner.l hl
  constructor
  · simp only [entMat]
    rw [length_matAdd]
    have : nb.inner.Δ.length = nb.r := length_unpackM _ _ _ _
    omega
  · exact mem_matAdd_length _ _ hldl.2 hΔ

/-- **The kernel-computed expansion has the specified entries.** -/
lemma getD_expandΔ (nb : NBlk) (hN : ∀ row ∈ nb.N, row.length ≤ nb.r) {a c : ℕ}
    (ha : a < nb.N.length) (hc : c < nb.N.length) :
    (nb.expandΔ.getD a []).getD c 0 = nb.eent a c := by
  have hE := entMat_bounds nb
  have hrow : (matMul nb.N (entMat nb.inner)).getD a [] = vecMat (nb.N[a]'ha) (entMat nb.inner) :=
    getD_map_lt _ nb.N a ha
  have hNc : nb.N.getD c [] ∈ nb.N := by
    rw [List.getD_eq_getElem nb.N [] hc]; exact List.getElem_mem hc
  unfold expandΔ
  rw [getD_matMulT _ _ a c (by simpa [matMul] using ha) hc, hrow]
  rw [dot_eq_sum nb.r _ _ (length_vecMat_le nb.r _ _ hE.2) (hN _ hNc)]
  simp only [eent, Blk.list_sum_range_map, n]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [getD_vecMat nb.r _ _ (hN _ (List.getElem_mem ha)) hE.1 j, Finset.sum_mul,
    List.getD_eq_getElem nb.N [] ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_entMat nb.r nb.inner nb.inner_d_length.le nb.inner_l_length.le i j]

/-- Well-formedness of a reduced block of expanded size `m`: rows of `N` of length `≤ r`, and at
least `m` rows. -/
def Good (m : ℕ) (nb : NBlk) : Prop := (∀ row ∈ nb.N, row.length ≤ nb.r) ∧ m ≤ nb.N.length

lemma del_expand {m : ℕ} {nb : NBlk} (hg : nb.Good m) {a c : ℕ} (ha : a < m) (hc : c < m) :
    nb.expand.del a c = nb.eent a c := by
  simp only [Blk.del, expand]
  have := hg.2
  exact getD_expandΔ nb hg.1 (by omega) (by omega)

lemma dq_expand (nb : NBlk) (q : ℕ) : nb.expand.dq q = 0 := by
  simp [Blk.dq, expand]

lemma ent_expand {m : ℕ} {nb : NBlk} (hg : nb.Good m) {a c : ℕ} (ha : a < m) (hc : c < m) :
    nb.expand.ent m a c = nb.eent a c := by
  simp only [Blk.ent, dq_expand, zero_mul, del_expand hg ha hc]
  simp

lemma cast_eent (nb : NBlk) (a c : ℕ) :
    (nb.eent a c : ℝ) = ∑ i ∈ Finset.range nb.r, ∑ j ∈ Finset.range nb.r,
      (nb.n a i : ℝ) * (nb.inner.ent nb.r i j : ℝ) * (nb.n c j : ℝ) := by
  simp only [eent, Blk.list_sum_range_map]
  push_cast
  rfl

lemma sum4_comm {m r : ℕ} (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m, ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
        f a c i j
      = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, ∑ a ∈ Finset.range m,
          ∑ c ∈ Finset.range m, f a c i j := by
  calc ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m, ∑ i ∈ Finset.range r,
          ∑ j ∈ Finset.range r, f a c i j
      = ∑ a ∈ Finset.range m, ∑ i ∈ Finset.range r, ∑ c ∈ Finset.range m,
          ∑ j ∈ Finset.range r, f a c i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range r, ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m,
          ∑ j ∈ Finset.range r, f a c i j := Finset.sum_comm
    _ = ∑ i ∈ Finset.range r, ∑ a ∈ Finset.range m, ∑ j ∈ Finset.range r,
          ∑ c ∈ Finset.range m, f a c i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, ∑ a ∈ Finset.range m,
          ∑ c ∈ Finset.range m, f a c i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- **Congruence**: `xᵀ (N B′ Nᵀ) x = yᵀ B′ y` with `y = Nᵀ x`. -/
lemma qf_eent (m : ℕ) (nb : NBlk) (x : ℕ → ℝ) :
    ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m, x a * (nb.eent a c : ℝ) * x c
      = ∑ i ∈ Finset.range nb.r, ∑ j ∈ Finset.range nb.r,
          (∑ a ∈ Finset.range m, (nb.n a i : ℝ) * x a) * (nb.inner.ent nb.r i j : ℝ)
            * (∑ c ∈ Finset.range m, (nb.n c j : ℝ) * x c) := by
  have lhs : ∀ a c, x a * (nb.eent a c : ℝ) * x c
      = ∑ i ∈ Finset.range nb.r, ∑ j ∈ Finset.range nb.r,
          x a * ((nb.n a i : ℝ) * (nb.inner.ent nb.r i j : ℝ) * nb.n c j) * x c := by
    intro a c
    rw [cast_eent, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  have rhs : ∀ i j, (∑ a ∈ Finset.range m, (nb.n a i : ℝ) * x a) * (nb.inner.ent nb.r i j : ℝ)
        * (∑ c ∈ Finset.range m, (nb.n c j : ℝ) * x c)
      = ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m,
          x a * ((nb.n a i : ℝ) * (nb.inner.ent nb.r i j : ℝ) * nb.n c j) * x c := by
    intro i j
    rw [Finset.sum_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  simp only [lhs, rhs]
  exact sum4_comm fun a c i j =>
    x a * ((nb.n a i : ℝ) * (nb.inner.ent nb.r i j : ℝ) * nb.n c j) * x c

/-- Nonnegativity of the quadratic form of the expanded block. -/
lemma qf_expand_nonneg {m : ℕ} {nb : NBlk} (hg : nb.Good m) (h : nb.inner.ok nb.r = true)
    (x : ℕ → ℝ) :
    0 ≤ ∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m,
      x a * (nb.expand.ent m a c : ℝ) * x c := by
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => by
    rw [ent_expand hg (Finset.mem_range.1 ha) (Finset.mem_range.1 hc)]]
  rw [qf_eent]
  exact Blk.qf_ent_nonneg h (fun i => ∑ a ∈ Finset.range m, (nb.n a i : ℝ) * x a)

lemma eent_comm (nb : NBlk) (h : nb.inner.ok nb.r = true) (a c : ℕ) :
    nb.eent a c = nb.eent c a := by
  have hc : ∀ a c, nb.eent a c = ∑ i ∈ Finset.range nb.r, ∑ j ∈ Finset.range nb.r,
      nb.n a i * nb.inner.ent nb.r i j * nb.n c j := by
    intro a c
    simp only [eent, Blk.list_sum_range_map]
  rw [hc, hc, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun i hi => ?_
  rw [Blk.ent_comm h (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)]
  ring

lemma ent_expand_comm {m : ℕ} {nb : NBlk} (hg : nb.Good m) (h : nb.inner.ok nb.r = true)
    {a c : ℕ} (ha : a < m) (hc : c < m) : nb.expand.ent m a c = nb.expand.ent m c a := by
  rw [ent_expand hg ha hc, ent_expand hg hc ha, eent_comm nb h]

/-- **PSD by congruence** for the kernel blocks (mirrors upstream `fmat_psd`). -/
lemma fmat_psd_expand {m : ℕ} (Lam : ℕ) {nb : NBlk} (hg : nb.Good m)
    (h : nb.inner.ok nb.r = true) : (fmat m Lam nb.expand).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [fmat, Matrix.of_apply, star_trivial]
    rw [ent_expand_comm hg h j.2 i.2]
  · intro x
    set x' : ℕ → ℝ := fun a => if ha : a < m then x ⟨a, ha⟩ else 0 with hx'
    have h0 := div_nonneg (qf_expand_nonneg hg h x') (Nat.cast_nonneg (α := ℝ) Lam)
    have hx'' : ∀ i : Fin m, x' i = x i := fun i => by simp [hx', i.2]
    have h1 : (∑ a ∈ Finset.range m, ∑ c ∈ Finset.range m,
          x' a * (nb.expand.ent m a c : ℝ) * x' c) / Lam
        = ∑ a : Fin m, ∑ c : Fin m, x a * ((nb.expand.ent m a c : ℝ) / Lam * x c) := by
      rw [← sum_fin_eq_range m (fun a c => x' a * (nb.expand.ent m a c : ℝ) * x' c),
        Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hx'', hx'']
      ring
    rw [h1] at h0
    simpa [dotProduct, Matrix.mulVec, fmat, Matrix.of_apply, star_trivial, Finset.mul_sum]
      using h0

/-- `getD` of a list of zeros. -/
lemma getD_zero_of_all : ∀ (l : List ℤ), l.all (fun x => decide (x = 0)) = true → ∀ q,
    l.getD q 0 = 0
  | [], _, q => by simp
  | x :: xs, h, q => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    cases q with
    | zero => simp [h.1]
    | succ q => simp only [List.getD_cons_succ]; exact getD_zero_of_all xs h.2 q

/-- **PSD by congruence** for a typed SOS block whose Gram data has zero pivots and the expanded
remainder (the shape produced by `TBlkN.toTBlk`). -/
lemma sqfE_nonneg_expand {b : Blk} {zs : List (ℕ × ℕ × ℕ)} {nb : NBlk} (hg : nb.Good zs.length)
    (hd : b.d.all (fun x => decide (x = 0)) = true) (hΔ : b.Δ = nb.expandΔ)
    (h : nb.inner.ok nb.r = true) (u v t : ℝ) : 0 ≤ (sqfE b zs).ev u v t := by
  rw [ev_sqfE]
  have h1 : ∑ q ∈ Finset.range zs.length, (b.dq q : ℝ)
      * (∑ a ∈ Finset.range zs.length, (b.lq q a : ℝ) * zval zs u v t a) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun q _ => ?_
    have h0 : b.dq q = 0 := getD_zero_of_all b.d hd q
    rw [h0]
    simp
  have h2 : ∑ a ∈ Finset.range zs.length, ∑ c ∈ Finset.range zs.length,
      zval zs u v t a * (b.del a c : ℝ) * zval zs u v t c
      = ∑ a ∈ Finset.range zs.length, ∑ c ∈ Finset.range zs.length,
        zval zs u v t a * (nb.eent a c : ℝ) * zval zs u v t c := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
    simp only [Blk.del, hΔ]
    rw [getD_expandΔ nb hg.1 (by have := Finset.mem_range.1 ha; have := hg.2; omega)
      (by have := Finset.mem_range.1 hc; have := hg.2; omega)]
  rw [h1, h2, qf_eent, zero_add]
  exact Blk.qf_ent_nonneg h _

/-! ### Row-wise evaluation (keeps each kernel check small)

A single `decide` of `expandΔ` for an `84 × 82` block exceeds ~10 GB in the kernel. The certificate modules
instead store `entMat nb.inner` (packed), check it and the expanded remainder one row per declaration, and
assemble with the two lemmas below. -/

lemma eq_of_getD_rows {L M : List (List ℤ)} (hl : L.length = M.length)
    (h : ∀ a < L.length, L.getD a [] = M.getD a []) : L = M := by
  apply List.ext_getElem hl
  intro a h1 h2
  have := h a h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

lemma expandΔ_eq (nb : NBlk) {E : List (List ℤ)} (hE : entMat nb.inner = E) :
    nb.expandΔ = nb.N.map (fun row => nb.N.map fun rb => dot (vecMat row E) rb) := by
  simp only [expandΔ, matMulT, matMul, hE, List.map_map, Function.comp_def] <;> rfl

end NBlk

/-! ## Packing the expanded remainder into a `TBlk`

`unpackI B n x` reads `n` offset-binary fields of `B` bits; `packI` is its (computable) inverse.
Soundness never relies on the inverse property: the certificate check compares the unpacked data of
the produced `TBlk` with the kernel-computed `expandΔ` by `decide`. -/

/-- Pack signed fields (least significant first) with offset `2^(B-1)`. -/
def packI (B : ℕ) : List ℤ → ℕ
  | [] => 0
  | v :: vs => (v + offB B).toNat + (packI B vs <<< B)

/-- Pack rows of `cols` fields each. -/
def packM (B cols : ℕ) : List (List ℤ) → ℕ
  | [] => 0
  | row :: rows => packI B row + (packM B cols rows <<< (B * cols))

/-- A typed SOS block given by multiplier codes, monomial basis and a facially reduced Gram block. -/
structure TBlkN where
  g : List ℕ
  z : List (ℕ × ℕ × ℕ)
  nb : NBlk
  BDe : ℕ
  /-- The expanded remainder `nb.expandΔ`, stored packed (`packM BDe m`) so that the identity checks do
  not recompute the expansion; `okN` checks the stored data against `expandΔ`. -/
  BD : ℕ

namespace TBlkN

/-- The size of the expanded block. -/
def m (s : TBlkN) : ℕ := s.z.length

/-- The ordinary typed block with zero pivots and the stored packed expanded remainder. -/
def toTBlk (s : TBlkN) : TBlk :=
  ⟨s.g, s.z, s.m, 1, 1, s.BDe, 2 ^ s.m - 1, 2 ^ (s.m * s.m) - 1, s.BD⟩

/-- The computable check: reduced block PSD, zero pivots, remainder equal to the expansion. -/
def okN (s : TBlkN) : Bool :=
  s.nb.okN && decide (s.nb.N.length = s.m) && s.toTBlk.B.d.all (fun x => decide (x = 0)) &&
    decide (s.toTBlk.B.Δ = s.nb.expandΔ)

lemma tblkE_nonneg_N (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) {s : TBlkN} (h : s.okN = true)
    {u v t : ℝ} (hg : GramCut an ad u v t) (hb : (bd : ℝ) * u ≤ bn) :
    0 ≤ (tblkE an ad bn bd s.toTBlk).ev u v t := by
  simp only [okN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hlen⟩, hd⟩, hΔ⟩ := h
  have hp := NBlk.okN_parts hok
  rw [tblkE, ev_mul, ev_sqfF]
  refine mul_nonneg (gT_nonneg an ad bn bd s.g hg hb) ?_
  exact NBlk.sqfE_nonneg_expand (nb := s.nb)
    ⟨hp.2, by show s.z.length ≤ s.nb.N.length; simp only [m] at hlen; omega⟩ hd
    (by simpa [toTBlk, m] using hΔ) hp.1 u v t

lemma okN_of_parts {s : TBlkN} (h1 : s.nb.okN = true) (h2 : s.nb.N.length = s.m)
    (h3 : s.toTBlk.B.d.all (fun x => decide (x = 0)) = true) (h4 : s.toTBlk.B.Δ = s.nb.expandΔ) :
    s.okN = true := by
  simp [okN, h1, h2, h3, h4]

end TBlkN

lemma tsum_nonneg_N (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ) (S : List TBlkN)
    (hS : S.all (fun s => s.okN) = true) {u v t : ℝ} (hg : GramCut an ad u v t)
    (hb : (bd : ℝ) * u ≤ bn) :
    0 ≤ (((S.map TBlkN.toTBlk).map (tblkE an ad bn bd)).map fun e => e.ev u v t).sum := by
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨e, ⟨s', ⟨s, hs, rfl⟩, rfl⟩, rfl⟩ := hx
  exact TBlkN.tblkE_nonneg_N an ad bn bd (List.all_eq_true.mp hS s hs) hg hb

/-! ## Typed certificates with facially reduced blocks (`TCertN`)

`TCertN` has the fields of upstream `TCert` with `NBlk`/`TBlkN` block lists.  `toTCert` expands every
block; the identity checks are upstream's `TCert.chkA/chkB/chkG` on the expanded certificate, and
`sound_lo` is upstream's `TCert.sound_lo` with the PSD inputs replaced by congruence. -/

/-! Upstream `TCert.sound_lo` with the block checks of `checkMeta` replaced by explicit
positivity facts (kernel blocks PSD, typed sums nonnegative on the cut). -/
namespace TCert

variable (cf : TCert)

lemma alpha_nonneg' (hL : 0 < cf.Lam) (hAd : 0 < cf.ad) (hBd : 0 < cf.bd) (hmA : 0 < cf.mA)
    (hSA : ∀ {u v t : ℝ}, GramCut cf.an cf.ad u v t → (cf.bd : ℝ) * u ≤ cf.bn →
      0 ≤ ((cf.SA.map (tblkE cf.an cf.ad cf.bn cf.bd)).map fun e => e.ev u v t).sum)
    (hA : cf.chkA = true) {u v t : ℝ}
    (hg : GramOK u v t) (hu : cf.alo ≤ u) (hu' : u ≤ cf.ahi) (hv : cf.alo ≤ v)
    (ht : cf.alo ≤ t) :
    0 ≤ lamA (Sk cf.K cf.m cf.FPm) (Sk cf.K cf.m cf.FRm) cf.HAf cf.ψBaf cf.calf u v t := by
  have hgc := gramCut_of_le' cf.an cf.ad hAd hg hu hv ht
  have hbd : (0 : ℝ) < cf.bd := by exact_mod_cast hBd
  have hb : (cf.bd : ℝ) * u ≤ cf.bn := by
    have := (le_div_iff₀ hbd).1 hu'
    linarith
  have h0 := cf.idA_ev hA u v t
  simp only [idA, idT, FA, ev_sub, ev_smul, ev_sumE, SPE, SRE,
    ev_lamAE cf.K cf.m cf.Lam cf.blkP cf.blkR hL] at h0
  push_cast at h0
  have hS := hSA hgc hb
  have hLr : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hmr : (0 : ℝ) < cf.mA := by exact_mod_cast hmA
  change 0 ≤ lamA (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkP k)))
    (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k))) (polyR cf.Lam cf.HA)
    (polyR cf.Lam cf.ψBa) ((cf.cal : ℝ) / cf.Lam) u v t
  refine nonneg_of_scaled (L := cf.mA * 5 * cf.Lam) (mul_pos (mul_pos hmr (by norm_num)) hLr)
    hS ?_
  linear_combination h0

lemma beta_nonneg' (hL : 0 < cf.Lam) (hAd : 0 < cf.ad) (hmB : 0 < cf.mB)
    (hSB : ∀ {u v t : ℝ}, GramCut cf.an cf.ad u v t → ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) →
      0 ≤ ((cf.SB.map (tblkE cf.an cf.ad 1 1)).map fun e => e.ev u v t).sum)
    (hB : cf.chkB = true) {u v t : ℝ}
    (hg : GramOK u v t) (hu : cf.alo ≤ u) (hv : cf.alo ≤ v) (ht : cf.alo ≤ t) :
    0 ≤ lamB (Sk cf.K cf.m cf.FPm) (Sk cf.K cf.m cf.FRm) cf.HBf cf.ψBaf cf.ψCbf cf.cbef
      u v t := by
  have hgc := gramCut_of_le' cf.an cf.ad hAd hg hu hv ht
  have hb : ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) := by
    have := le_one_of_gramOK hg
    simpa using this
  have h0 := cf.idB_ev hB u v t
  simp only [idB, idT, FB, ev_sub, ev_smul, ev_sumE, SPE, SRE,
    ev_lamBE cf.K cf.m cf.Lam cf.blkP cf.blkR hL] at h0
  push_cast at h0
  have hS := hSB hgc hb
  have hLr : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hmr : (0 : ℝ) < cf.mB := by exact_mod_cast hmB
  change 0 ≤ lamB (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkP k)))
    (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k))) (polyR cf.Lam cf.HB)
    (polyR cf.Lam cf.ψBa) (polyR cf.Lam cf.ψCb) ((cf.cbe : ℝ) / cf.Lam) u v t
  refine nonneg_of_scaled (L := cf.mB * 4 * cf.Lam) (mul_pos (mul_pos hmr (by norm_num)) hLr)
    hS ?_
  linear_combination h0

lemma gamma_nonneg' (hL : 0 < cf.Lam) (hAd : 0 < cf.ad) (hmG : 0 < cf.mG)
    (hSG : ∀ {u v t : ℝ}, GramCut cf.an cf.ad u v t → ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) →
      0 ≤ ((cf.SG.map (tblkE cf.an cf.ad 1 1)).map fun e => e.ev u v t).sum)
    (hG : cf.chkG = true) {u v t : ℝ}
    (hg : GramOK u v t) (hu : cf.alo ≤ u) (hv : cf.alo ≤ v) (ht : cf.alo ≤ t) :
    0 ≤ lamG (Sk cf.K cf.m cf.FRm) cf.HCf cf.ψCbf
      ((cf.ef + 2 * Sk cf.K cf.m cf.FPm 1 1 1 + 5 * Sk cf.K cf.m cf.FRm 1 1 1 - 5 * cf.calf
        - 20 * cf.cbef) / 10) u v t := by
  have hgc := gramCut_of_le' cf.an cf.ad hAd hg hu hv ht
  have hb : ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) := by
    have := le_one_of_gramOK hg
    simpa using this
  have h0 := cf.idG_ev hG u v t
  simp only [idG, idT, FG, ev_sub, ev_smul, ev_sumE, SPE, SRE,
    ev_lamGE cf.K cf.m cf.Lam cf.blkP cf.blkR hL] at h0
  push_cast at h0
  have hS := hSG hgc hb
  have hLr : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hmr : (0 : ℝ) < cf.mG := by exact_mod_cast hmG
  change 0 ≤ lamG (Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k)))
    (polyR cf.Lam cf.HC) (polyR cf.Lam cf.ψCb)
    (((cf.e : ℝ) / cf.Lam + 2 * Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkP k)) 1 1 1
      + 5 * Sk cf.K cf.m (fun k => fmat (cf.m k) cf.Lam (cf.blkR k)) 1 1 1
      - 5 * ((cf.cal : ℝ) / cf.Lam) - 20 * ((cf.cbe : ℝ) / cf.Lam)) / 10) u v t
  refine nonneg_of_scaled (L := cf.mG * 30 * cf.Lam) (mul_pos (mul_pos hmr (by norm_num)) hLr)
    hS ?_
  linear_combination h0

/-- **Soundness with explicit positivity inputs** (upstream `sound_lo` without `checkMeta`). -/
theorem sound_lo' (hL : 0 < cf.Lam) (hAd : 0 < cf.ad) (hBd : 0 < cf.bd) (hmA : 0 < cf.mA)
    (hmB : 0 < cf.mB) (hmG : 0 < cf.mG)
    (hFP : ∀ k, k < cf.K → (cf.FPm k).PosSemidef) (hFR : ∀ k, k < cf.K → (cf.FRm k).PosSemidef)
    (hSA : ∀ {u v t : ℝ}, GramCut cf.an cf.ad u v t → (cf.bd : ℝ) * u ≤ cf.bn →
      0 ≤ ((cf.SA.map (tblkE cf.an cf.ad cf.bn cf.bd)).map fun e => e.ev u v t).sum)
    (hSB : ∀ {u v t : ℝ}, GramCut cf.an cf.ad u v t → ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) →
      0 ≤ ((cf.SB.map (tblkE cf.an cf.ad 1 1)).map fun e => e.ev u v t).sum)
    (hSG : ∀ {u v t : ℝ}, GramCut cf.an cf.ad u v t → ((1 : ℕ) : ℝ) * u ≤ ((1 : ℤ) : ℝ) →
      0 ≤ ((cf.SG.map (tblkE cf.an cf.ad 1 1)).map fun e => e.ev u v t).sum)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (x : Fin 7 → R3) (hx : ∀ i, ‖x i‖ = 1)
    (hmin : ∀ i j, i ≠ j → cf.alo ≤ inner ℝ (x i) (x j))
    (hcut : cf.alo ≤ inner ℝ (x 0) (x 1) ∧ inner ℝ (x 0) (x 1) ≤ cf.ahi) :
    cf.ef ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H7 cf.HAf cf.HBf cf.HCf i j (inner ℝ (x i) (x j)) :=
  typed7_bound_lo cf.K cf.m cf.FPm cf.FRm hFP hFR cf.HAf cf.HBf cf.HCf
    cf.ψBaf cf.ψCbf cf.ef cf.calf cf.cbef cf.alo cf.ahi cf.alo x hx hmin hcut
    (fun _ _ _ hg h1 h2 h3 h4 => cf.alpha_nonneg' hL hAd hBd hmA hSA hA hg h1 h2 h3 h4)
    (fun _ _ _ hg h1 h2 h3 => cf.beta_nonneg' hL hAd hmB hSB hB hg h1 h2 h3)
    (fun _ _ _ hg h1 h2 h3 => cf.gamma_nonneg' hL hAd hmG hSG hG hg h1 h2 h3)

end TCert

/-- A typed certificate whose blocks are facially reduced (fields as `TCert`). -/
structure TCertN where
  dd : ℕ
  Lam : ℕ
  an : ℤ
  ad : ℕ
  bn : ℤ
  bd : ℕ
  e : ℤ
  cal : ℤ
  cbe : ℤ
  HA : List ℤ
  HB : List ℤ
  HC : List ℤ
  ψBa : List ℤ
  ψCb : List ℤ
  FP : List NBlk
  FR : List NBlk
  mA : ℕ
  mB : ℕ
  mG : ℕ
  SA : List TBlkN
  SB : List TBlkN
  SG : List TBlkN

namespace TCertN

variable (cf : TCertN)

def K : ℕ := cf.dd + 1
def m (k : ℕ) : ℕ := cf.dd + 1 - k

/-- The default (empty) reduced block. -/
def nbEmpty : NBlk := ⟨[], 0, 1, 1, 1, 0, 0, 0⟩

/-- The expanded kernel blocks. -/
def FPx : List Blk := (List.range cf.K).map fun k => (cf.FP.getD k nbEmpty).expand
def FRx : List Blk := (List.range cf.K).map fun k => (cf.FR.getD k nbEmpty).expand

/-- The expanded certificate: an ordinary upstream `TCert`. -/
def toTCert : TCert :=
  ⟨cf.dd, cf.Lam, cf.an, cf.ad, cf.bn, cf.bd, cf.e, cf.cal, cf.cbe, cf.HA, cf.HB, cf.HC, cf.ψBa,
    cf.ψCb, cf.FPx, cf.FRx, cf.mA, cf.mB, cf.mG, cf.SA.map TBlkN.toTBlk, cf.SB.map TBlkN.toTBlk,
    cf.SG.map TBlkN.toTBlk⟩

/-- The cheap checks: positivity, block counts, and the reduced PSD certificates. -/
def checkMeta : Bool :=
  decide (0 < cf.Lam) && decide (0 < cf.ad) && decide (0 < cf.bd) &&
  decide (0 < cf.mA) && decide (0 < cf.mB) && decide (0 < cf.mG) &&
  decide (cf.FP.length = cf.K) && decide (cf.FR.length = cf.K) &&
  (List.range cf.K).all (fun k => decide ((cf.FP.getD k nbEmpty).N.length = cf.m k)) &&
  (List.range cf.K).all (fun k => decide ((cf.FR.getD k nbEmpty).N.length = cf.m k)) &&
  cf.FP.all NBlk.okN && cf.FR.all NBlk.okN &&
  cf.SA.all TBlkN.okN && cf.SB.all TBlkN.okN && cf.SG.all TBlkN.okN

/-- The part of `checkMeta` before the SOS blocks. With `checkMeta_of_parts` it lets a certificate check
`checkMeta` in pieces (one kernel `decide` per SOS block), since a single `decide` over all of it can be too
large for the kernel. -/
def checkMetaF : Bool :=
  decide (0 < cf.Lam) && decide (0 < cf.ad) && decide (0 < cf.bd) &&
  decide (0 < cf.mA) && decide (0 < cf.mB) && decide (0 < cf.mG) &&
  decide (cf.FP.length = cf.K) && decide (cf.FR.length = cf.K) &&
  (List.range cf.K).all (fun k => decide ((cf.FP.getD k nbEmpty).N.length = cf.m k)) &&
  (List.range cf.K).all (fun k => decide ((cf.FR.getD k nbEmpty).N.length = cf.m k)) &&
  cf.FP.all NBlk.okN && cf.FR.all NBlk.okN

lemma checkMeta_of_parts (h0 : cf.checkMetaF = true) (hA : cf.SA.all TBlkN.okN = true)
    (hB : cf.SB.all TBlkN.okN = true) (hG : cf.SG.all TBlkN.okN = true) : cf.checkMeta = true := by
  show (cf.checkMetaF && cf.SA.all TBlkN.okN && cf.SB.all TBlkN.okN && cf.SG.all TBlkN.okN) = true
  rw [h0, hA, hB, hG]; rfl

/-- The identity checks: upstream's hybrid Kronecker checks on the expanded certificate. -/
def chkA : Bool := cf.toTCert.chkA
def chkB : Bool := cf.toTCert.chkB
def chkG : Bool := cf.toTCert.chkG

lemma toTCert_K : cf.toTCert.K = cf.K := rfl
lemma toTCert_m (k : ℕ) : cf.toTCert.m k = cf.m k := rfl

lemma blkP_eq {k : ℕ} (hk : k < cf.K) :
    cf.toTCert.blkP k = (cf.FP.getD k nbEmpty).expand := by
  simp [TCert.blkP, toTCert, FPx, List.getD_eq_getElem?_getD, List.getElem?_range hk]

lemma blkR_eq {k : ℕ} (hk : k < cf.K) :
    cf.toTCert.blkR k = (cf.FR.getD k nbEmpty).expand := by
  simp [TCert.blkR, toTCert, FRx, List.getD_eq_getElem?_getD, List.getElem?_range hk]

lemma okN_getD {L : List NBlk} (hall : L.all NBlk.okN = true) {k : ℕ} (hk : k < L.length) :
    (L.getD k nbEmpty).okN = true := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.all_eq_true.mp hall _ (List.getElem_mem hk)

lemma checkMeta_parts (hm : cf.checkMeta = true) :
    0 < cf.Lam ∧ 0 < cf.ad ∧ 0 < cf.bd ∧ 0 < cf.mA ∧ 0 < cf.mB ∧ 0 < cf.mG ∧
    cf.FP.length = cf.K ∧ cf.FR.length = cf.K ∧
    (∀ k < cf.K, (cf.FP.getD k nbEmpty).N.length = cf.m k) ∧
    (∀ k < cf.K, (cf.FR.getD k nbEmpty).N.length = cf.m k) ∧
    cf.FP.all NBlk.okN = true ∧ cf.FR.all NBlk.okN = true ∧
    cf.SA.all TBlkN.okN = true ∧ cf.SB.all TBlkN.okN = true ∧ cf.SG.all TBlkN.okN = true := by
  simp only [checkMeta, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩ := hm
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, List.all_eq_true.mpr h11,
    List.all_eq_true.mpr h12, List.all_eq_true.mpr h13, List.all_eq_true.mpr h14,
    List.all_eq_true.mpr h15⟩

lemma hFP (hm : cf.checkMeta = true) : ∀ k, k < cf.toTCert.K → (cf.toTCert.FPm k).PosSemidef := by
  intro k hk
  obtain ⟨-, -, -, -, -, -, hlP, -, hmP, -, hP, -, -, -, -⟩ := cf.checkMeta_parts hm
  rw [toTCert_K] at hk
  unfold TCert.FPm
  rw [toTCert_m, blkP_eq cf hk]
  have hp := NBlk.okN_parts (okN_getD hP (hlP ▸ hk))
  exact NBlk.fmat_psd_expand _ ⟨hp.2, (hmP k hk).ge⟩ hp.1

lemma hFR (hm : cf.checkMeta = true) : ∀ k, k < cf.toTCert.K → (cf.toTCert.FRm k).PosSemidef := by
  intro k hk
  obtain ⟨-, -, -, -, -, -, -, hlR, -, hmR, -, hR, -, -, -⟩ := cf.checkMeta_parts hm
  rw [toTCert_K] at hk
  unfold TCert.FRm
  rw [toTCert_m, blkR_eq cf hk]
  have hp := NBlk.okN_parts (okN_getD hR (hlR ▸ hk))
  exact NBlk.fmat_psd_expand _ ⟨hp.2, (hmR k hk).ge⟩ hp.1

/-- **Soundness of a facially reduced typed certificate with lower cut**, stated for the expanded
certificate `cf.toTCert` (so that the generic bridges apply verbatim). -/
theorem sound_lo (hm : cf.checkMeta = true) (hA : cf.chkA = true) (hB : cf.chkB = true)
    (hG : cf.chkG = true) (x : Fin 7 → R3) (hx : ∀ i, ‖x i‖ = 1)
    (hmin : ∀ i j, i ≠ j → cf.toTCert.alo ≤ inner ℝ (x i) (x j))
    (hcut : cf.toTCert.alo ≤ inner ℝ (x 0) (x 1) ∧ inner ℝ (x 0) (x 1) ≤ cf.toTCert.ahi) :
    cf.toTCert.ef ≤ ∑ i, ∑ j ∈ Finset.Ioi i,
      H7 cf.toTCert.HAf cf.toTCert.HBf cf.toTCert.HCf i j (inner ℝ (x i) (x j)) := by
  obtain ⟨hL, hAd, hBd, hmA, hmB, hmG, -, -, -, -, -, -, hSA, hSB, hSG⟩ := cf.checkMeta_parts hm
  refine cf.toTCert.sound_lo' hL hAd hBd hmA hmB hmG (cf.hFP hm) (cf.hFR hm) ?_ ?_ ?_ hA hB hG
    x hx hmin hcut
  · intro u v t hgc hb
    exact tsum_nonneg_N cf.an cf.ad cf.bn cf.bd cf.SA hSA hgc hb
  · intro u v t hgc hb
    exact tsum_nonneg_N cf.an cf.ad 1 1 cf.SB hSB hgc hb
  · intro u v t hgc hb
    exact tsum_nonneg_N cf.an cf.ad 1 1 cf.SG hSG hgc hb

end TCertN

end Cert
end ThomsonN7
