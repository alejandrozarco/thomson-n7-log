import LogLean.LocalKel

/-!
# LocalSP: verified sparse polynomials over K = ℚ(α) (kernel-computable, `decide +kernel`)

Two monomial types:
* `Mono = List ℕ` (exponent vector, any number of variables; evaluation at `x : ℕ → ℝ`), used for the pair
  polynomials (4 variables), the global Taylor data (14 variables) and the `(σ, w)` expansion (16 variables);
* `M6` (exponents of the six pair atoms `A B C C′ rᵢ² rⱼ²`) with `T6 = List (M6 × Kel)`, the class polynomials of
  the atom level (`LocalAtom`), composed with atom polynomials by `compose6`.

All operations (`merge`, `smul`, `mul`, `pow`, `compose`) are structurally recursive with an evaluation lemma; an
identity `p = q` is certified by `eqPoly p q = true` (the difference has only zero coefficients) and turned into a
real identity by `ev_eq_of_eqPoly`.  Soundness never uses the sort order; the order only decides whether equal
monomials get merged (which the final zero check verifies).  Generalises `LocalPairKron.SP` (Part II §11).
-/

namespace LocalSP
open LocalKel

/-! ## Monomials as exponent lists -/

abbrev Mono := List ℕ

namespace Mono

def add : Mono → Mono → Mono
  | [], n => n
  | a :: m, [] => a :: m
  | a :: m, b :: n => (a + b) :: add m n

/-- lexicographic order (only used to choose the merge order). -/
def lt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: m, b :: n => if a < b then true else if b < a then false else lt m n

/-- `x_i^{e_0} x_{i+1}^{e_1} ⋯` (the exponent list starts at variable `i`). -/
noncomputable def ev : Mono → ℕ → (ℕ → ℝ) → ℝ
  | [], _, _ => 1
  | e :: m, i, x => x i ^ e * ev m (i + 1) x

lemma ev_add (m n : Mono) (i : ℕ) (x : ℕ → ℝ) : (add m n).ev i x = m.ev i x * n.ev i x := by
  induction m generalizing n i with
  | nil => simp [add, ev]
  | cons a m ih =>
    cases n with
    | nil => simp [add, ev]
    | cons b n => simp only [add, ev, ih, pow_add]; ring

end Mono

/-! ## Sparse polynomials -/

abbrev Poly := List (Mono × Kel)

noncomputable def ev (p : Poly) (x : ℕ → ℝ) (a : ℝ) : ℝ := (p.map fun t => t.2.ev a * t.1.ev 0 x).sum

variable {x : ℕ → ℝ} {a : ℝ}

lemma ev_nil : ev [] x a = 0 := by simp [ev]
lemma ev_cons (t : Mono × Kel) (p : Poly) : ev (t :: p) x a = t.2.ev a * t.1.ev 0 x + ev p x a := by simp [ev]
lemma ev_append (p q : Poly) : ev (p ++ q) x a = ev p x a + ev q x a := by
  simp [ev, List.map_append, List.sum_append]

/-- merge of two (sorted) polynomials, adding coefficients of equal monomials; fuel = total length. -/
def mergeF : ℕ → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, t :: p, [] => t :: p
  | n + 1, t :: p, s :: q =>
    if t.1 = s.1 then (t.1, t.2.add s.2) :: mergeF n p q
    else if t.1.lt s.1 then t :: mergeF n p (s :: q) else s :: mergeF n (t :: p) q

def merge (p q : Poly) : Poly := mergeF (p.length + q.length) p q

lemma ev_mergeF (n : ℕ) : ∀ p q : Poly, ev (mergeF n p q) x a = ev p x a + ev q x a := by
  induction n with
  | zero => intro p q; simp [mergeF, ev_append]
  | succ n ih =>
    intro p q
    match p, q with
    | [], q => simp [mergeF, ev_nil]
    | t :: p, [] => simp [mergeF, ev_nil]
    | t :: p, s :: q =>
      simp only [mergeF]
      split_ifs with h1 h2
      · simp only [ev_cons, ih, Kel.ev_add, h1]; ring
      · simp only [ev_cons, ih]; ring
      · simp only [ev_cons, ih]; ring

lemma ev_merge (p q : Poly) : ev (merge p q) x a = ev p x a + ev q x a := ev_mergeF _ p q

def smul (c : Kel) (p : Poly) : Poly := p.map fun t => (t.1, c.mul t.2)

lemma ev_smul (ha : a ^ 4 = 20 * a ^ 2 - 80) (c : Kel) (p : Poly) :
    ev (smul c p) x a = c.ev a * ev p x a := by
  induction p with
  | nil => simp [smul, ev]
  | cons t p ih =>
    simp only [smul] at ih
    simp only [smul, List.map_cons, ev_cons]
    rw [ih, Kel.ev_mul _ _ ha]; ring

def mulRow (t : Mono × Kel) (q : Poly) : Poly := q.map fun s => (t.1.add s.1, t.2.mul s.2)

lemma ev_mulRow (ha : a ^ 4 = 20 * a ^ 2 - 80) (t : Mono × Kel) (q : Poly) :
    ev (mulRow t q) x a = (t.2.ev a * t.1.ev 0 x) * ev q x a := by
  induction q with
  | nil => simp [mulRow, ev]
  | cons s q ih =>
    simp only [mulRow] at ih
    simp only [mulRow, List.map_cons, ev_cons]
    rw [ih, Kel.ev_mul _ _ ha, Mono.ev_add]; ring

def mul : Poly → Poly → Poly
  | [], _ => []
  | t :: p, q => merge (mulRow t q) (mul p q)

lemma ev_mul (ha : a ^ 4 = 20 * a ^ 2 - 80) (p q : Poly) :
    ev (mul p q) x a = ev p x a * ev q x a := by
  induction p with
  | nil => simp [mul, ev]
  | cons t p ih => rw [mul, ev_merge, ev_mulRow ha, ih, ev_cons]; ring

def one : Poly := [([], Kel.ofQ 1)]

lemma ev_one : ev one x a = 1 := by simp [one, ev, Mono.ev, Kel.ev_ofQ]

def pow (p : Poly) : ℕ → Poly
  | 0 => one
  | n + 1 => mul p (pow p n)

lemma ev_pow (ha : a ^ 4 = 20 * a ^ 2 - 80) (p : Poly) (n : ℕ) :
    ev (pow p n) x a = (ev p x a) ^ n := by
  induction n with
  | zero => simp [pow, ev_one]
  | succ n ih => rw [pow, ev_mul ha, ih, pow_succ]; ring

def allZero (p : Poly) : Bool := p.all fun t => decide (t.2 = Kel.zero)

lemma ev_eq_zero_of_allZero (p : Poly) (h : allZero p = true) : ev p x a = 0 := by
  induction p with
  | nil => simp [ev]
  | cons t p ih =>
    simp only [allZero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ev_cons, h.1, ih h.2]
    simp [Kel.ev, Kel.zero]

/-- `p = q` as polynomials (both sides sorted): the difference has only zero coefficients. -/
def eqPoly (p q : Poly) : Bool := allZero (merge p (smul (Kel.ofQ (-1)) q))

theorem ev_eq_of_eqPoly (ha : a ^ 4 = 20 * a ^ 2 - 80) (p q : Poly) (h : eqPoly p q = true) :
    ev p x a = ev q x a := by
  have h0 := ev_eq_zero_of_allZero (x := x) (a := a) _ h
  rw [ev_merge, ev_smul ha, Kel.ev_ofQ] at h0
  push_cast at h0; linarith

/-! ### Substitution of polynomials for the variables -/

/-- `∏_k f (i+k) ^ m_k` as a polynomial. -/
def monoPoly : Mono → ℕ → (ℕ → Poly) → Poly
  | [], _, _ => one
  | e :: m, i, f => mul (pow (f i) e) (monoPoly m (i + 1) f)

lemma ev_monoPoly (ha : a ^ 4 = 20 * a ^ 2 - 80) (m : Mono) (i : ℕ) (f : ℕ → Poly) :
    ev (monoPoly m i f) x a = m.ev i (fun j => ev (f j) x a) := by
  induction m generalizing i with
  | nil => simp [monoPoly, ev_one, Mono.ev]
  | cons e m ih => simp only [monoPoly, ev_mul ha, ev_pow ha, ih, Mono.ev]

/-- `p` with the variable `j` replaced by the polynomial `f j`. -/
def compose : Poly → (ℕ → Poly) → Poly
  | [], _ => []
  | t :: p, f => merge (smul t.2 (monoPoly t.1 0 f)) (compose p f)

lemma ev_compose (ha : a ^ 4 = 20 * a ^ 2 - 80) (p : Poly) (f : ℕ → Poly) :
    ev (compose p f) x a = ev p (fun j => ev (f j) x a) a := by
  induction p with
  | nil => simp [compose, ev_nil]
  | cons t p ih => rw [compose, ev_merge, ev_smul ha, ev_monoPoly ha, ih, ev_cons]

/-! ## Polynomials in the six pair atoms `A B C C′ rᵢ² rⱼ²` -/

/-- exponents of `A B C C′ rᵢ² rⱼ²`. -/
structure M6 where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  f : ℕ
  deriving DecidableEq

noncomputable def M6.ev (m : M6) (A B C Cp ri rj : ℝ) : ℝ :=
  A ^ m.a * B ^ m.b * C ^ m.c * Cp ^ m.d * ri ^ m.e * rj ^ m.f

abbrev T6 := List (M6 × Kel)

/-- `T6` as a real function of the six atom values. -/
noncomputable def evT6 (T : T6) (A B C Cp ri rj a : ℝ) : ℝ :=
  (T.map fun t => t.2.ev a * t.1.ev A B C Cp ri rj).sum

lemma evT6_nil (A B C Cp ri rj : ℝ) : evT6 [] A B C Cp ri rj a = 0 := by simp [evT6]
lemma evT6_cons (t : M6 × Kel) (T : T6) (A B C Cp ri rj : ℝ) :
    evT6 (t :: T) A B C Cp ri rj a = t.2.ev a * t.1.ev A B C Cp ri rj + evT6 T A B C Cp ri rj a := by
  simp [evT6]

def monoPoly6 (m : M6) (A B C Cp ri rj : Poly) : Poly :=
  mul (pow A m.a) (mul (pow B m.b) (mul (pow C m.c) (mul (pow Cp m.d) (mul (pow ri m.e) (pow rj m.f)))))

lemma ev_monoPoly6 (ha : a ^ 4 = 20 * a ^ 2 - 80) (m : M6) (A B C Cp ri rj : Poly) :
    ev (monoPoly6 m A B C Cp ri rj) x a
      = m.ev (ev A x a) (ev B x a) (ev C x a) (ev Cp x a) (ev ri x a) (ev rj x a) := by
  simp only [monoPoly6, ev_mul ha, ev_pow ha, M6.ev]; ring

def compose6 : T6 → Poly → Poly → Poly → Poly → Poly → Poly → Poly
  | [], _, _, _, _, _, _ => []
  | t :: T, A, B, C, Cp, ri, rj => merge (smul t.2 (monoPoly6 t.1 A B C Cp ri rj)) (compose6 T A B C Cp ri rj)

lemma ev_compose6 (ha : a ^ 4 = 20 * a ^ 2 - 80) (T : T6) (A B C Cp ri rj : Poly) :
    ev (compose6 T A B C Cp ri rj) x a
      = evT6 T (ev A x a) (ev B x a) (ev C x a) (ev Cp x a) (ev ri x a) (ev rj x a) a := by
  induction T with
  | nil => simp [compose6, ev_nil, evT6_nil]
  | cons t T ih => rw [compose6, ev_merge, ev_smul ha, ev_monoPoly6 ha, ih, evT6_cons]

/-- The pair-level check `compose6 T atoms = p`. -/
def checkEq6 (T : T6) (A B C Cp ri rj p : Poly) : Bool := eqPoly (compose6 T A B C Cp ri rj) p

theorem eq_of_checkEq6 (ha : a ^ 4 = 20 * a ^ 2 - 80) (T : T6) (A B C Cp ri rj p : Poly)
    (h : checkEq6 T A B C Cp ri rj p = true) :
    evT6 T (ev A x a) (ev B x a) (ev C x a) (ev Cp x a) (ev ri x a) (ev rj x a) a = ev p x a := by
  rw [← ev_compose6 ha]; exact ev_eq_of_eqPoly ha _ _ h

end LocalSP
