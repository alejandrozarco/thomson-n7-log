import LogLean.LocalSP

/-!
# LocalBomb: polynomial builders and the Bombieri inequality

Kernel-computable constructions on `LocalSP.Poly` with their evaluation lemmas:
* `unit n k` (the monomial `x_k` in `n` variables), `linPoly`, `qfPoly` (linear / quadratic forms from `Kel` data),
  `shift2` (a 14-variable polynomial read in the `w`-block `2..15`), `embed i j` (a 4-variable pair polynomial
  read in the 14 coordinates), `sumsq`;
* dense polynomials with polynomial coefficients `DP = List (Mono × Poly)` (monomial in `w`, coefficient in `σ`),
  `flatDP`, `evDP`, `constDP`;
* **Bombieri** (squared form, no square roots): `(evDP D)² ≤ ev (bombSq d D) · ev S` where `S = (Σ w_k²)^d` is
  computed in the kernel by `pow` (its terms `(d!/m!) w^{2m}` are the multinomial expansion), the weights `d!/m!`
  are computed by `wtOf` and matched against `S` by `wsub` (a sorted sub-sequence check).  Proof: Cauchy–Schwarz
  over the list (`cs_step`) and a sub-sequence sum inequality (`wsub_le`).
-/

namespace LocalBomb
open LocalKel LocalSP

/-! ## Unit monomials -/

/-- the exponent list of `x_k` among `n` variables -/
def unit : ℕ → ℕ → Mono
  | 0, _ => []
  | n + 1, 0 => 1 :: List.replicate n 0
  | n + 1, k + 1 => 0 :: unit n k

lemma ev_replicate (n i : ℕ) (x : ℕ → ℝ) : Mono.ev (List.replicate n 0) i x = 1 := by
  induction n generalizing i with
  | zero => simp [Mono.ev]
  | succ n ih => simp [List.replicate, Mono.ev, ih]

lemma ev_unit (n k i : ℕ) (hk : k < n) (x : ℕ → ℝ) : Mono.ev (unit n k) i x = x (i + k) := by
  induction n generalizing k i with
  | zero => omega
  | succ n ih =>
    rcases k with _ | k
    · simp [unit, Mono.ev, ev_replicate]
    · have e := ih k (i + 1) (by omega)
      have e2 : i + 1 + k = i + (k + 1) := by omega
      simp only [unit, Mono.ev, pow_zero, one_mul]
      rw [e] <;> simp only [e2]

lemma ev_unit0 (n k : ℕ) (hk : k < n) (x : ℕ → ℝ) : Mono.ev (unit n k) 0 x = x k := by
  rw [ev_unit n k 0 hk]; simp

variable {x : ℕ → ℝ} {a : ℝ}

/-- `x_k` as a polynomial -/
def xk (n k : ℕ) : Poly := [(unit n k, Kel.ofQ 1)]

lemma ev_xk (n k : ℕ) (hk : k < n) : ev (xk n k) x a = x k := by
  simp [xk, ev, ev_unit0 n k hk, Kel.ev_ofQ]

/-! ## Linear and quadratic forms -/

/-- `Σ_{p<m} v p · x_{off+p}` -/
def linPoly (v : ℕ → Kel) (n off : ℕ) : ℕ → Poly
  | 0 => []
  | m + 1 => merge (linPoly v n off m) [(unit n (off + m), v m)]

lemma ev_linPoly (v : ℕ → Kel) (n off m : ℕ) (h : off + m ≤ n) :
    ev (linPoly v n off m) x a = ∑ p ∈ Finset.range m, (v p).ev a * x (off + p) := by
  induction m with
  | zero => simp [linPoly, ev]
  | succ m ih =>
    rw [linPoly, ev_merge, ih (by omega), Finset.sum_range_succ]
    simp [ev, ev_unit0 n (off + m) (by omega)]

/-- `Σ_{q<m} H p q · x_{off+p} x_{off+q}` -/
def qfRow (H : ℕ → ℕ → Kel) (n off p : ℕ) : ℕ → Poly
  | 0 => []
  | q + 1 => merge (qfRow H n off p q) [((unit n (off + p)).add (unit n (off + q)), H p q)]

/-- `Σ_{p<m} Σ_{q<m'} H p q · x_{off+p} x_{off+q}` -/
def qfPoly (H : ℕ → ℕ → Kel) (n off m' : ℕ) : ℕ → Poly
  | 0 => []
  | p + 1 => merge (qfPoly H n off m' p) (qfRow H n off p m')

lemma ev_qfRow (H : ℕ → ℕ → Kel) (n off p m : ℕ) (hp : off + p < n) (h : off + m ≤ n) :
    ev (qfRow H n off p m) x a = ∑ q ∈ Finset.range m, (H p q).ev a * (x (off + p) * x (off + q)) := by
  induction m with
  | zero => simp [qfRow, ev]
  | succ m ih =>
    rw [qfRow, ev_merge, ih (by omega), Finset.sum_range_succ]
    simp [ev, Mono.ev_add, ev_unit0 n (off + p) hp, ev_unit0 n (off + m) (by omega)]

lemma ev_qfPoly (H : ℕ → ℕ → Kel) (n off m' m : ℕ) (h : off + m ≤ n) (h' : off + m' ≤ n) :
    ev (qfPoly H n off m' m) x a
      = ∑ p ∈ Finset.range m, ∑ q ∈ Finset.range m', (H p q).ev a * (x (off + p) * x (off + q)) := by
  induction m with
  | zero => simp [qfPoly, ev]
  | succ m ih =>
    rw [qfPoly, ev_merge, ih (by omega), Finset.sum_range_succ, ev_qfRow H n off m m' (by omega) h']

/-! ## Reading polynomials in other coordinates -/

lemma Mono.ev_shift (m : Mono) (i j : ℕ) (x : ℕ → ℝ) : m.ev (i + j) x = m.ev i (fun k => x (k + j)) := by
  induction m generalizing i with
  | nil => simp [Mono.ev]
  | cons e m ih =>
    simp only [Mono.ev]
    rw [show i + j + 1 = (i + 1) + j by omega, ih (i + 1)]

/-- a polynomial in `w` read in the variables `2..` (`σ` occupies `0, 1`) -/
def shift2 (p : Poly) : Poly := p.map fun t => (0 :: 0 :: t.1, t.2)

lemma Mono.ev_cons_zero (m : Mono) (i : ℕ) (x : ℕ → ℝ) : Mono.ev (0 :: m) i x = m.ev (i + 1) x := by
  simp [Mono.ev]

lemma ev_shift2 (p : Poly) : ev (shift2 p) x a = ev p (fun k => x (k + 2)) a := by
  induction p with
  | nil => simp [shift2, ev]
  | cons t p ih =>
    simp only [shift2, List.map_cons, ev_cons] at ih ⊢
    rw [ih]; congr 1
    rw [Mono.ev_cons_zero, Mono.ev_cons_zero]
    show t.2.ev a * t.1.ev (0 + 2) x = _
    rw [Mono.ev_shift]

/-- the 4 local coordinates of the pair `(i, j)` -/
def loc (x : ℕ → ℝ) (i j : ℕ) : ℕ → ℝ
  | 0 => x (2 * i)
  | 1 => x (2 * i + 1)
  | 2 => x (2 * j)
  | 3 => x (2 * j + 1)
  | _ => 0

/-- a 4-variable exponent list `[a, b, c, d]` placed at the coordinates `2i, 2i+1, 2j, 2j+1` (14 variables) -/
def embedM (i j : ℕ) (m : Mono) : Mono :=
  (List.range 14).map fun p =>
    if p = 2 * i then m.getD 0 0 else if p = 2 * i + 1 then m.getD 1 0
    else if p = 2 * j then m.getD 2 0 else if p = 2 * j + 1 then m.getD 3 0 else 0

def embed (i j : ℕ) (p : Poly) : Poly := p.map fun t => (embedM i j t.1, t.2)

/-- `Mono.ev` of a mapped range: `∏_{p<n} x_{i+p}^{f p}` -/
lemma ev_map_range (f : ℕ → ℕ) (n i : ℕ) :
    Mono.ev ((List.range n).map f) i x = ∏ p ∈ Finset.range n, x (i + p) ^ f p := by
  induction n generalizing i f with
  | zero => simp [Mono.ev]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Mono.ev]
    rw [ih (f ∘ Nat.succ) (i + 1), Finset.prod_range_succ']
    simp only [Function.comp, add_zero]
    rw [mul_comm]; congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    congr 2; omega

lemma ev_embedM {i j : ℕ} (hij : i < j) (hj : j < 7) (m : Mono) (hm : m.length = 4) :
    Mono.ev (embedM i j m) 0 x = Mono.ev m 0 (loc x i j) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, m = [a, b, c, d] := by
    match m, hm with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  simp only [embedM, ev_map_range, zero_add]
  simp only [Mono.ev, loc, List.getD_cons_zero, List.getD_cons_succ, mul_one]
  have key : ∀ p ∈ Finset.range 14, x p ^ (if p = 2 * i then a else if p = 2 * i + 1 then b
      else if p = 2 * j then c else if p = 2 * j + 1 then d else 0)
      = (if p = 2 * i then x (2 * i) ^ a else 1) * (if p = 2 * i + 1 then x (2 * i + 1) ^ b else 1)
        * (if p = 2 * j then x (2 * j) ^ c else 1) * (if p = 2 * j + 1 then x (2 * j + 1) ^ d else 1) := by
    intro p _
    by_cases h1 : p = 2 * i
    · subst h1
      simp only [if_true, if_neg (show 2 * i ≠ 2 * i + 1 by omega), if_neg (show 2 * i ≠ 2 * j by omega),
        if_neg (show 2 * i ≠ 2 * j + 1 by omega), mul_one]
    by_cases h2 : p = 2 * i + 1
    · subst h2
      simp only [if_true, if_neg h1, if_neg (show 2 * i + 1 ≠ 2 * j by omega),
        if_neg (show 2 * i + 1 ≠ 2 * j + 1 by omega), mul_one, one_mul]
    by_cases h3 : p = 2 * j
    · subst h3
      simp only [if_true, if_neg h1, if_neg h2, if_neg (show 2 * j ≠ 2 * j + 1 by omega), mul_one, one_mul]
    by_cases h4 : p = 2 * j + 1
    · subst h4
      simp only [if_true, if_neg h1, if_neg h2, if_neg h3, mul_one, one_mul]
    simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, pow_zero, mul_one]
  rw [Finset.prod_congr rfl key]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' (Finset.range 14) (2 * i), Finset.prod_ite_eq' (Finset.range 14) (2 * i + 1),
    Finset.prod_ite_eq' (Finset.range 14) (2 * j), Finset.prod_ite_eq' (Finset.range 14) (2 * j + 1)]
  simp only [Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  ring

/-- monomials of length 4 -/
def len4 (p : Poly) : Bool := p.all fun t => decide (t.1.length = 4)

lemma ev_embed {i j : ℕ} (hij : i < j) (hj : j < 7) (p : Poly) (hp : len4 p = true) :
    ev (embed i j p) x a = ev p (loc x i j) a := by
  induction p with
  | nil => simp [embed, ev]
  | cons t p ih =>
    simp only [len4, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp only [embed, List.map_cons, ev_cons] at ih ⊢
    rw [ih hp.2, ev_embedM hij hj t.1 hp.1]

/-! ## `Σ_{p<m} x_{off+p}²` -/

def sumsq (n off : ℕ) : ℕ → Poly
  | 0 => []
  | m + 1 => merge (sumsq n off m) [((unit n (off + m)).add (unit n (off + m)), Kel.ofQ 1)]

lemma ev_sumsq (n off m : ℕ) (h : off + m ≤ n) :
    ev (sumsq n off m) x a = ∑ p ∈ Finset.range m, x (off + p) ^ 2 := by
  induction m with
  | zero => simp [sumsq, ev]
  | succ m ih =>
    rw [sumsq, ev_merge, ih (by omega), Finset.sum_range_succ]
    simp [ev, Mono.ev_add, ev_unit0 n (off + m) (by omega), Kel.ev_ofQ, sq]

/-! ## Dense polynomials with polynomial coefficients -/

/-- entries `(w-monomial, coefficient polynomial in σ)` -/
abbrev DP := List (Mono × Poly)

noncomputable def evDP (D : DP) (x : ℕ → ℝ) (a : ℝ) : ℝ := (D.map fun t => ev t.2 x a * t.1.ev 0 x).sum

def flatDP : DP → Poly
  | [] => []
  | t :: D => merge (mul t.2 [(t.1, Kel.ofQ 1)]) (flatDP D)

lemma ev_flatDP (ha : a ^ 4 = 20 * a ^ 2 - 80) (D : DP) : ev (flatDP D) x a = evDP D x a := by
  induction D with
  | nil => simp [flatDP, ev, evDP]
  | cons t D ih =>
    simp only [flatDP, evDP, List.map_cons, List.sum_cons] at ih ⊢
    rw [ev_merge, ev_mul ha, ih]; simp [ev, Kel.ev_ofQ]

/-- a polynomial with constant coefficients as a `DP` -/
def constDP (p : Poly) : DP := p.map fun t => (t.1, [([], t.2)])

lemma evDP_constDP (p : Poly) : evDP (constDP p) x a = ev p x a := by
  induction p with
  | nil => simp [constDP, evDP, ev]
  | cons t p ih =>
    simp only [constDP, List.map_cons, evDP, List.sum_cons, ev_cons] at ih ⊢
    rw [ih]; simp [ev, Mono.ev]

/-- `d!/m!`, the Bombieri weight of the monomial `m` of degree `d` -/
def wtOf (d : ℕ) (m : Mono) : ℚ := (Nat.factorial d : ℚ) / ((m.map Nat.factorial).foldr (· * ·) 1 : ℕ)

lemma wtOf_pos (d : ℕ) (m : Mono) : 0 < wtOf d m := by
  unfold wtOf
  have h1 : (0 : ℚ) < Nat.factorial d := by exact_mod_cast Nat.factorial_pos d
  have h2 : 0 < ((m.map Nat.factorial).foldr (· * ·) 1 : ℕ) := by
    induction m with
    | nil => simp
    | cons e m ih => simp only [List.map_cons, List.foldr_cons]; exact Nat.mul_pos (Nat.factorial_pos e) ih
  exact div_pos h1 (by exact_mod_cast h2)

/-- `Σ_t coef_t² / wt_t` -/
def bombSq (d : ℕ) : DP → Poly
  | [] => []
  | t :: D => merge (smul (Kel.ofQ (1 / wtOf d t.1)) (mul t.2 t.2)) (bombSq d D)

lemma ev_bombSq (ha : a ^ 4 = 20 * a ^ 2 - 80) (d : ℕ) (D : DP) :
    ev (bombSq d D) x a = (D.map fun t => (1 / (wtOf d t.1 : ℝ)) * (ev t.2 x a) ^ 2).sum := by
  induction D with
  | nil => simp [bombSq, ev]
  | cons t D ih =>
    simp only [bombSq, List.map_cons, List.sum_cons]
    rw [ev_merge, ev_smul ha, ev_mul ha, ih, Kel.ev_ofQ]; push_cast; ring

/-- `2m` -/
def dbl (m : Mono) : Mono := m.map (2 * ·)

lemma ev_dbl (m : Mono) (i : ℕ) : Mono.ev (dbl m) i x = (Mono.ev m i x) ^ 2 := by
  induction m generalizing i with
  | nil => simp [dbl, Mono.ev]
  | cons e m ih => simp only [dbl, List.map_cons, Mono.ev, pow_mul] at ih ⊢; rw [ih]; ring

/-- the doubled monomials of `D` with their weights form a sub-sequence of `S` (both sorted) -/
def wsub (d : ℕ) : DP → Poly → Bool
  | [], _ => true
  | _ :: _, [] => false
  | t :: D, s :: S => if dbl t.1 = s.1 ∧ Kel.ofQ (wtOf d t.1) = s.2 then wsub d D S else wsub d (t :: D) S

/-- every term of `S` is `≥ 0`: even exponents and a nonnegative rational coefficient -/
def Sok (S : Poly) : Bool := S.all fun s =>
  (s.1.all fun e => decide (e % 2 = 0)) && decide (s.2.c1 = 0 ∧ s.2.c2 = 0 ∧ s.2.c3 = 0 ∧ 0 ≤ s.2.c0)

lemma ev_nonneg_of_even (m : Mono) (h : m.all (fun e => decide (e % 2 = 0)) = true) (i : ℕ) :
    0 ≤ Mono.ev m i x := by
  induction m generalizing i with
  | nil => simp [Mono.ev]
  | cons e m ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Mono.ev]
    obtain ⟨k, hk⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
    rw [hk, pow_mul]
    exact mul_nonneg (pow_nonneg (sq_nonneg _) _) (ih h.2 _)

lemma term_nonneg_of_Sok (s : Mono × Kel)
    (h : ((s.1.all fun e => decide (e % 2 = 0)) && decide (s.2.c1 = 0 ∧ s.2.c2 = 0 ∧ s.2.c3 = 0 ∧ 0 ≤ s.2.c0)) = true) :
    0 ≤ s.2.ev a * s.1.ev 0 x := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨he, h1, h2, h3, h0⟩ := h
  have : s.2.ev a = s.2.c0 := by simp [Kel.ev, h1, h2, h3]
  rw [this]
  exact mul_nonneg (by exact_mod_cast h0) (ev_nonneg_of_even s.1 he 0)

/-- weighted squares of `D`'s monomials are bounded by `ev S` -/
lemma wsub_le (d : ℕ) (D : DP) (S : Poly) (hs : wsub d D S = true) (he : Sok S = true) :
    (D.map fun t => (wtOf d t.1 : ℝ) * (t.1.ev 0 x) ^ 2).sum ≤ ev S x a := by
  induction S generalizing D with
  | nil =>
    cases D with
    | nil => simp [ev]
    | cons t D => simp [wsub] at hs
  | cons s S ih =>
    simp only [Sok, List.all_cons, Bool.and_eq_true] at he
    have hs0 : 0 ≤ s.2.ev a * s.1.ev 0 x := term_nonneg_of_Sok s (by simp only [Bool.and_eq_true]; exact he.1)
    have he2 : Sok S = true := by simp only [Sok]; exact he.2
    cases D with
    | nil =>
      simp only [List.map_nil, List.sum_nil]; rw [ev_cons]
      exact add_nonneg hs0 (ih [] (by simp [wsub]) he2)
    | cons t D =>
      simp only [wsub] at hs
      split_ifs at hs with hm
      · obtain ⟨hm1, hm2⟩ := hm
        simp only [List.map_cons, List.sum_cons]
        rw [ev_cons, ← hm2, Kel.ev_ofQ, ← hm1, ev_dbl]
        exact add_le_add (le_refl _) (ih D hs he2)
      · rw [ev_cons]
        exact (ih (t :: D) hs he2).trans (by linarith)

/-- one Cauchy–Schwarz step: `(c m + s)² ≤ (c²/w + A)(w m² + B)` from `s² ≤ A B`. -/
lemma cs_step {c m s A B w : ℝ} (hw : 0 < w) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : s ^ 2 ≤ A * B) :
    (c * m + s) ^ 2 ≤ (c ^ 2 / w + A) * (w * m ^ 2 + B) := by
  set u := c ^ 2 / w * B with hu
  set v := A * (w * m ^ 2) with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have huv : (c * m * s) ^ 2 ≤ u * v := by
    have e : u * v = c ^ 2 * m ^ 2 * (A * B) := by rw [hu, hv]; field_simp <;> ring
    rw [e]
    have : (c * m * s) ^ 2 = c ^ 2 * m ^ 2 * s ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have h4 : (2 * (c * m * s)) ^ 2 ≤ (u + v) ^ 2 := by nlinarith [sq_nonneg (u - v)]
  have h5 : |2 * (c * m * s)| ≤ |u + v| := sq_le_sq.mp h4
  rw [abs_of_nonneg (show 0 ≤ u + v by linarith)] at h5
  have h6 : 2 * (c * m * s) ≤ u + v := (le_abs_self _).trans h5
  have e2 : (c ^ 2 / w + A) * (w * m ^ 2 + B) = c ^ 2 * m ^ 2 + u + v + A * B := by
    rw [hu, hv]; field_simp <;> ring
  rw [e2]; nlinarith

lemma bombSq_nonneg (ha : a ^ 4 = 20 * a ^ 2 - 80) (d : ℕ) (D : DP) : 0 ≤ ev (bombSq d D) x a := by
  rw [ev_bombSq ha]
  induction D with
  | nil => simp
  | cons t D ih =>
    simp only [List.map_cons, List.sum_cons]
    have := wtOf_pos d t.1
    have : (0 : ℝ) < wtOf d t.1 := by exact_mod_cast this
    positivity

lemma wsum_nonneg (d : ℕ) (D : DP) : 0 ≤ (D.map fun t => (wtOf d t.1 : ℝ) * (t.1.ev 0 x) ^ 2).sum := by
  induction D with
  | nil => simp
  | cons t D ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (0 : ℝ) < wtOf d t.1 := by exact_mod_cast wtOf_pos d t.1
    positivity

/-- Cauchy–Schwarz over the list: `(evDP D)² ≤ bombSq · Σ_t wt_t m_t²`. -/
lemma cs_list (ha : a ^ 4 = 20 * a ^ 2 - 80) (d : ℕ) (D : DP) :
    (evDP D x a) ^ 2 ≤ ev (bombSq d D) x a * (D.map fun t => (wtOf d t.1 : ℝ) * (t.1.ev 0 x) ^ 2).sum := by
  rw [ev_bombSq ha]
  induction D with
  | nil => simp [evDP]
  | cons t D ih =>
    simp only [evDP, List.map_cons, List.sum_cons] at ih ⊢
    have hw : (0 : ℝ) < wtOf d t.1 := by exact_mod_cast wtOf_pos d t.1
    have hA : 0 ≤ (D.map fun t => (1 / (wtOf d t.1 : ℝ)) * (ev t.2 x a) ^ 2).sum := by
      have := bombSq_nonneg (x := x) ha d D; rwa [ev_bombSq ha] at this
    have hB := wsum_nonneg (x := x) d D
    have := cs_step (c := ev t.2 x a) (m := t.1.ev 0 x) hw hA hB ih
    calc _ ≤ ((ev t.2 x a) ^ 2 / (wtOf d t.1 : ℝ) + _) * ((wtOf d t.1 : ℝ) * (t.1.ev 0 x) ^ 2 + _) := this
      _ = _ := by ring

/-- **Bombieri inequality** (squared form): with `S` the multinomial list `(Σ w_k²)^d` (checked by `wsub`/`Sok`),
`(evDP D)² ≤ ev (bombSq d D) · ev S`. -/
theorem bombieri (ha : a ^ 4 = 20 * a ^ 2 - 80) (d : ℕ) (D : DP) (S : Poly) (hs : wsub d D S = true)
    (he : Sok S = true) : (evDP D x a) ^ 2 ≤ ev (bombSq d D) x a * ev S x a :=
  (cs_list ha d D).trans (mul_le_mul_of_nonneg_left (wsub_le d D S hs he) (bombSq_nonneg ha d D))

end LocalBomb
