import LogLean.LocalSP

/-!
# LocalAtom: the atom level of the Taylor link

For a pair of class `g = ⟪Pᵢ,Pⱼ⟫`, the pair term `f_ij = W⟪hᵢ,hⱼ⟫ + ½ψ₅(u_ij)` is the explicit polynomial
`PhiR g W (1/(1−g))` in the atoms `A B C C′ νᵢ νⱼ`, with `ν = n̂(r²) + e`, `n̂(x) = −x/2 − x²/8 − x³/16`.
This file proves `|PhiR(atoms) − T6_g(A,B,C,C′,rᵢ²,rⱼ²)| ≤ K_g R⁷` for `R² = rᵢ² + rⱼ² ≤ ρ²`, where `T6_g`
(weight-≤6 part) and `K_g` are certified by one `decide +kernel` per class (`check_adj` …).

Method: a `Rep = (T, err)` represents a real `q` if `|q − T(atoms)| ≤ err·R⁷` (`Ok`).  Products are truncated at
weight 6 (weights: A, C, C′ = 1; B, rᵢ², rⱼ² = 2); each dropped monomial of weight `w ≥ 7` contributes
`|c|·β^m·ρ^(w−7)` to `err`, and the cross terms of a product are bounded through `bnd`, the monomial-wise bound of
`T` at `R ≤ ρ`.  Everything is computed in K = ℚ(α) (coefficients) and ℚ (bounds).  Python mirror:
`lean/gen/local_atom.py` (294 Kel products and 803 monomial comparisons per class).
-/

/-! ## Weighted monomial arithmetic on `M6` -/

namespace LocalSP.M6
open LocalKel

def add (m n : M6) : M6 := ⟨m.a + n.a, m.b + n.b, m.c + n.c, m.d + n.d, m.e + n.e, m.f + n.f⟩
/-- weight: A, C, C′ weight 1; B, rᵢ², rⱼ² weight 2. -/
def wt (m : M6) : ℕ := m.a + 2 * m.b + m.c + m.d + 2 * m.e + 2 * m.f
/-- packed key (exponents < 8); only used for the merge order. -/
def key (m : M6) : ℕ := ((((m.a * 8 + m.b) * 8 + m.c) * 8 + m.d) * 8 + m.e) * 8 + m.f

lemma ev_add (m n : M6) (A B C Cp ri rj : ℝ) :
    (m.add n).ev A B C Cp ri rj = m.ev A B C Cp ri rj * n.ev A B C Cp ri rj := by
  simp only [ev, add, pow_add]; ring

end LocalSP.M6

namespace LocalAtom
open LocalKel LocalSP

def rho : ℚ := 1 / 100

/-- Class constants: atom bounds `|A| ≤ bA R`, `|B| ≤ bB R²`, `|C|, |C′| ≤ bC R`, `|e| ≤ ce R⁸`. -/
structure Cls where
  bA : ℚ
  bB : ℚ
  bC : ℚ
  ce : ℚ

def Cls.betapow (cl : Cls) (m : M6) : ℚ := cl.bA ^ m.a * cl.bB ^ m.b * cl.bC ^ (m.c + m.d)

/-- monomial-wise bound of `|T(atoms)|` for `R ≤ ρ`. -/
def bnd (cl : Cls) (T : T6) : ℚ :=
  (T.map fun t => t.2.aub aLo aHi * cl.betapow t.1 * rho ^ t.1.wt).sum

def mergeF : ℕ → T6 → T6 → T6
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, t :: p, [] => t :: p
  | n + 1, t :: p, s :: q =>
    if t.1 = s.1 then (t.1, t.2.add s.2) :: mergeF n p q
    else if t.1.key < s.1.key then t :: mergeF n p (s :: q) else s :: mergeF n (t :: p) q

def merge (p q : T6) : T6 := mergeF (p.length + q.length) p q

def smul (c : Kel) (p : T6) : T6 := p.map fun t => (t.1, c.mul t.2)

/-- kept (weight ≤ 6) products of one row. -/
def rowKept (t : M6 × Kel) : T6 → T6
  | [] => []
  | s :: q => if (t.1.add s.1).wt ≤ 6 then (t.1.add s.1, t.2.mul s.2) :: rowKept t q else rowKept t q

/-- bound (÷ R⁷) of the dropped products of one row. -/
def rowDrop (cl : Cls) (t : M6 × Kel) : T6 → ℚ
  | [] => 0
  | s :: q => if (t.1.add s.1).wt ≤ 6 then rowDrop cl t q
      else t.2.aub aLo aHi * s.2.aub aLo aHi * cl.betapow (t.1.add s.1) * rho ^ ((t.1.add s.1).wt - 7)
        + rowDrop cl t q

def mulKept : T6 → T6 → T6
  | [], _ => []
  | t :: p, q => merge (rowKept t q) (mulKept p q)

def mulDrop (cl : Cls) : T6 → T6 → ℚ
  | [], _ => 0
  | t :: p, q => rowDrop cl t q + mulDrop cl p q

def allZero6 (p : T6) : Bool := p.all fun t => decide (t.2 = Kel.zero)

/-- `p = q` as polynomials in the atoms (both sorted). -/
def eq6 (p q : T6) : Bool := allZero6 (merge p (smul (Kel.ofQ (-1)) q))

/-- A represented real: `|q − T(atoms)| ≤ err·R⁷`. -/
structure Rep where
  T : T6
  err : ℚ

namespace Rep

def add (r s : Rep) : Rep := ⟨merge r.T s.T, r.err + s.err⟩
def smul (c : Kel) (r : Rep) : Rep := ⟨LocalAtom.smul c r.T, c.aub aLo aHi * r.err⟩
def mul (cl : Cls) (r s : Rep) : Rep :=
  ⟨mulKept r.T s.T, mulDrop cl r.T s.T + r.err * (bnd cl s.T + s.err * rho ^ 7) + bnd cl r.T * s.err⟩
def atom (m : M6) : Rep := ⟨[(m, Kel.ofQ 1)], 0⟩
/-- the chart remainder `e` (weight 8): `T = 0`, `|e| ≤ ce R⁸ ≤ ce ρ R⁷`. -/
def e (cl : Cls) : Rep := ⟨[], cl.ce * rho⟩

end Rep

/-- `ν = n̂(r²) + e` as a `Rep`. -/
def nuRep (cl : Cls) (r e : Rep) : Rep :=
  (((r.smul (Kel.ofQ (-1/2))).add ((Rep.mul cl r r).smul (Kel.ofQ (-1/8)))).add
    ((Rep.mul cl (Rep.mul cl r r) r).smul (Kel.ofQ (-1/16)))).add e

/-- The class polynomial `f_ij` in the atoms, as a `Rep` (same expression tree as `PhiR`). -/
def PhiRep (cl : Cls) (g W inv : Kel) : Rep :=
  let A := Rep.atom ⟨1, 0, 0, 0, 0, 0⟩
  let B := Rep.atom ⟨0, 1, 0, 0, 0, 0⟩
  let C := Rep.atom ⟨0, 0, 1, 0, 0, 0⟩
  let Cp := Rep.atom ⟨0, 0, 0, 1, 0, 0⟩
  let ri := Rep.atom ⟨0, 0, 0, 0, 1, 0⟩
  let rj := Rep.atom ⟨0, 0, 0, 0, 0, 1⟩
  let νi := nuRep cl ri (Rep.e cl)
  let νj := nuRep cl rj (Rep.e cl)
  let hh := ((B.add (Rep.mul cl νj Cp)).add (Rep.mul cl νi C)).add ((Rep.mul cl νi νj).smul g)
  let ℓ := A.add ((νi.add νj).smul g)
  let u := (ℓ.add hh).smul inv
  let u2 := Rep.mul cl u u
  let u3 := Rep.mul cl u2 u
  let u4 := Rep.mul cl u3 u
  let u5 := Rep.mul cl u4 u
  (hh.smul W).add ((((u2.smul (Kel.ofQ (1/4))).add (u3.smul (Kel.ofQ (1/6)))).add
    (u4.smul (Kel.ofQ (1/8)))).add (u5.smul (Kel.ofQ (1/10))))

/-- The class check: `T = T6_g` and `err ≤ K_g`. -/
def checkClass (cl : Cls) (g W inv : Kel) (T : T6) (K : ℚ) : Bool :=
  eq6 (PhiRep cl g W inv).T T && decide ((PhiRep cl g W inv).err ≤ K)

/-! ## Real side -/

noncomputable def nhat (x : ℝ) : ℝ := (-1/2 : ℝ) * x + (-1/8 : ℝ) * (x * x) + (-1/16 : ℝ) * (x * x * x)

/-- `f_ij = W⟪hᵢ,hⱼ⟫ + ½ψ₅(u)` in the atoms (`gR = g`, `WR = 1/(2(1−g))`, `invR = 1/(1−g)`). -/
noncomputable def PhiR (gR WR invR A B C Cp νi νj : ℝ) : ℝ :=
  let hh := B + νj * Cp + νi * C + gR * (νi * νj)
  let ℓ := A + gR * (νi + νj)
  let u := invR * (ℓ + hh)
  let u2 := u * u
  let u3 := u2 * u
  let u4 := u3 * u
  let u5 := u4 * u
  WR * hh + ((1/4 : ℝ) * u2 + (1/6 : ℝ) * u3 + (1/8 : ℝ) * u4 + (1/10 : ℝ) * u5)

lemma PhiR_eq (gR WR invR A B C Cp νi νj : ℝ) :
    PhiR gR WR invR A B C Cp νi νj
      = WR * (B + νj * Cp + νi * C + gR * νi * νj)
        + (1/2) * ((invR * (A + gR * (νi + νj) + (B + νj * Cp + νi * C + gR * νi * νj))) ^ 2 / 2
          + (invR * (A + gR * (νi + νj) + (B + νj * Cp + νi * C + gR * νi * νj))) ^ 3 / 3
          + (invR * (A + gR * (νi + νj) + (B + νj * Cp + νi * C + gR * νi * νj))) ^ 4 / 4
          + (invR * (A + gR * (νi + νj) + (B + νj * Cp + νi * C + gR * νi * νj))) ^ 5 / 5) := by
  simp only [PhiR]; ring

lemma nhat_eq (x : ℝ) : nhat x = -x / 2 - x ^ 2 / 8 - x ^ 3 / 16 := by simp only [nhat]; ring

/-! ### Evaluation lemmas (no bounds) -/

section eval
variable {A B C Cp ri rj a : ℝ}

lemma evT6_mergeF (n : ℕ) : ∀ p q : T6,
    evT6 (mergeF n p q) A B C Cp ri rj a = evT6 p A B C Cp ri rj a + evT6 q A B C Cp ri rj a := by
  induction n with
  | zero => intro p q; simp [mergeF, evT6, List.map_append, List.sum_append]
  | succ n ih =>
    intro p q
    match p, q with
    | [], q => simp [mergeF, evT6_nil]
    | t :: p, [] => simp [mergeF, evT6_nil]
    | t :: p, s :: q =>
      simp only [mergeF]
      split_ifs with h1 h2
      · simp only [evT6_cons, ih, Kel.ev_add, h1]; ring
      · simp only [evT6_cons, ih]; ring
      · simp only [evT6_cons, ih]; ring

lemma evT6_merge (p q : T6) :
    evT6 (merge p q) A B C Cp ri rj a = evT6 p A B C Cp ri rj a + evT6 q A B C Cp ri rj a :=
  evT6_mergeF _ p q

lemma evT6_smul (ha : a ^ 4 = 20 * a ^ 2 - 80) (c : Kel) (p : T6) :
    evT6 (smul c p) A B C Cp ri rj a = c.ev a * evT6 p A B C Cp ri rj a := by
  induction p with
  | nil => simp [smul, evT6]
  | cons t p ih =>
    simp only [smul] at ih
    simp only [smul, List.map_cons, evT6_cons]
    rw [ih, Kel.ev_mul _ _ ha]; ring

lemma evT6_eq_zero_of_allZero6 (p : T6) (h : allZero6 p = true) : evT6 p A B C Cp ri rj a = 0 := by
  induction p with
  | nil => simp [evT6]
  | cons t p ih =>
    simp only [allZero6, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [evT6_cons, h.1, ih h.2]
    simp [Kel.ev, Kel.zero]

lemma evT6_eq_of_eq6 (ha : a ^ 4 = 20 * a ^ 2 - 80) (p q : T6) (h : eq6 p q = true) :
    evT6 p A B C Cp ri rj a = evT6 q A B C Cp ri rj a := by
  have h0 := evT6_eq_zero_of_allZero6 (A := A) (B := B) (C := C) (Cp := Cp) (ri := ri) (rj := rj) (a := a) _ h
  rw [evT6_merge, evT6_smul ha, Kel.ev_ofQ] at h0
  push_cast at h0; linarith

end eval

/-! ## Semantics and soundness -/

section semantics

variable {cl : Cls} {A B C Cp ri rj R a : ℝ}

/-- The ambient hypotheses of the atom level. -/
structure Hyp (cl : Cls) (A B C Cp ri rj R a : ℝ) : Prop where
  hA : |A| ≤ (cl.bA : ℝ) * R
  hB : |B| ≤ (cl.bB : ℝ) * R ^ 2
  hC : |C| ≤ (cl.bC : ℝ) * R
  hCp : |Cp| ≤ (cl.bC : ℝ) * R
  hri0 : 0 ≤ ri
  hri : ri ≤ R ^ 2
  hrj0 : 0 ≤ rj
  hrj : rj ≤ R ^ 2
  hR0 : 0 ≤ R
  hR : R ≤ (rho : ℝ)
  hbA : (0 : ℝ) ≤ cl.bA
  hbB : (0 : ℝ) ≤ cl.bB
  hbC : (0 : ℝ) ≤ cl.bC
  hce : (0 : ℝ) ≤ cl.ce
  hlo : (aLo : ℝ) ≤ a
  hhi : a ≤ aHi
  hmin : a ^ 4 = 20 * a ^ 2 - 80

/-- `r` represents `q`. -/
def Ok (cl : Cls) (A B C Cp ri rj R a : ℝ) (r : Rep) (q : ℝ) : Prop :=
  (0 : ℝ) ≤ r.err ∧ |q - evT6 r.T A B C Cp ri rj a| ≤ (r.err : ℝ) * R ^ 7

lemma rho_nonneg : (0 : ℝ) ≤ (rho : ℝ) := by norm_num [rho]

lemma mul_le_mul6 {a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4) (h5 : a5 ≤ b5) (h6 : a6 ≤ b6)
    (n1 : 0 ≤ a1) (n2 : 0 ≤ a2) (n3 : 0 ≤ a3) (n4 : 0 ≤ a4) (n5 : 0 ≤ a5) (n6 : 0 ≤ a6) :
    a1 * a2 * a3 * a4 * a5 * a6 ≤ b1 * b2 * b3 * b4 * b5 * b6 := by
  have m2 : a1 * a2 ≤ b1 * b2 := mul_le_mul h1 h2 n2 (n1.trans h1)
  have m3 : a1 * a2 * a3 ≤ b1 * b2 * b3 := mul_le_mul m2 h3 n3 ((mul_nonneg n1 n2).trans m2)
  have m4 : a1 * a2 * a3 * a4 ≤ b1 * b2 * b3 * b4 :=
    mul_le_mul m3 h4 n4 ((mul_nonneg (mul_nonneg n1 n2) n3).trans m3)
  have m5 : a1 * a2 * a3 * a4 * a5 ≤ b1 * b2 * b3 * b4 * b5 :=
    mul_le_mul m4 h5 n5 ((mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4).trans m4)
  exact mul_le_mul m5 h6 n6 ((mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) n5).trans m5)

variable (h : Hyp cl A B C Cp ri rj R a)
include h

lemma aub_nonneg (c : Kel) : (0 : ℝ) ≤ (c.aub aLo aHi : ℝ) :=
  (abs_nonneg _).trans (Kel.abs_ev_le c aLo_nonneg h.hlo h.hhi)

lemma abs_ev_le' (c : Kel) : |c.ev a| ≤ (c.aub aLo aHi : ℝ) := Kel.abs_ev_le c aLo_nonneg h.hlo h.hhi

lemma betapow_nonneg (m : M6) : (0 : ℝ) ≤ (cl.betapow m : ℝ) := by
  have := h.hbA; have := h.hbB; have := h.hbC
  simp only [Cls.betapow]; push_cast; positivity

/-- monomial bound: `|m(atoms)| ≤ β^m R^{wt m}`. -/
lemma mono_bound (m : M6) : |m.ev A B C Cp ri rj| ≤ (cl.betapow m : ℝ) * R ^ m.wt := by
  have hA' : |A| ^ m.a ≤ ((cl.bA : ℝ) * R) ^ m.a := pow_le_pow_left₀ (abs_nonneg _) h.hA _
  have hB' : |B| ^ m.b ≤ ((cl.bB : ℝ) * R ^ 2) ^ m.b := pow_le_pow_left₀ (abs_nonneg _) h.hB _
  have hC' : |C| ^ m.c ≤ ((cl.bC : ℝ) * R) ^ m.c := pow_le_pow_left₀ (abs_nonneg _) h.hC _
  have hCp' : |Cp| ^ m.d ≤ ((cl.bC : ℝ) * R) ^ m.d := pow_le_pow_left₀ (abs_nonneg _) h.hCp _
  have hri' : |ri| ^ m.e ≤ (R ^ 2) ^ m.e :=
    pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg h.hri0]; exact h.hri) _
  have hrj' : |rj| ^ m.f ≤ (R ^ 2) ^ m.f :=
    pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg h.hrj0]; exact h.hrj) _
  have e1 : |m.ev A B C Cp ri rj| = |A| ^ m.a * |B| ^ m.b * |C| ^ m.c * |Cp| ^ m.d * |ri| ^ m.e * |rj| ^ m.f := by
    simp only [M6.ev, abs_mul, abs_pow]
  have e2 : (cl.betapow m : ℝ) * R ^ m.wt = ((cl.bA : ℝ) * R) ^ m.a * ((cl.bB : ℝ) * R ^ 2) ^ m.b
      * ((cl.bC : ℝ) * R) ^ m.c * ((cl.bC : ℝ) * R) ^ m.d * (R ^ 2) ^ m.e * (R ^ 2) ^ m.f := by
    simp only [Cls.betapow, M6.wt]; push_cast; ring
  rw [e1, e2]
  exact mul_le_mul6 hA' hB' hC' hCp' hri' hrj' (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity)

lemma term_bound (t : M6 × Kel) :
    |t.2.ev a * t.1.ev A B C Cp ri rj| ≤ (t.2.aub aLo aHi : ℝ) * ((cl.betapow t.1 : ℝ) * R ^ t.1.wt) := by
  rw [abs_mul]
  exact mul_le_mul (abs_ev_le' h _) (mono_bound h _) (abs_nonneg _) (aub_nonneg h _)

lemma pow_le_rho (n : ℕ) : R ^ n ≤ (rho : ℝ) ^ n := pow_le_pow_left₀ h.hR0 h.hR n

/-- `|T(atoms)| ≤ bnd T`. -/
lemma bnd_sound (T : T6) : |evT6 T A B C Cp ri rj a| ≤ (bnd cl T : ℝ) := by
  induction T with
  | nil => simp [evT6, bnd]
  | cons t T ih =>
    have hb : (bnd cl (t :: T) : ℝ) = (t.2.aub aLo aHi : ℝ) * (cl.betapow t.1 : ℝ) * (rho : ℝ) ^ t.1.wt
        + (bnd cl T : ℝ) := by
      simp only [bnd, List.map_cons, List.sum_cons]; push_cast; ring
    rw [evT6_cons, hb]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    refine (term_bound h t).trans ?_
    have hr := pow_le_rho h t.1.wt
    have hb0 := betapow_nonneg h t.1
    have ha0 := aub_nonneg h t.2
    calc (t.2.aub aLo aHi : ℝ) * ((cl.betapow t.1 : ℝ) * R ^ t.1.wt)
        ≤ (t.2.aub aLo aHi : ℝ) * ((cl.betapow t.1 : ℝ) * (rho : ℝ) ^ t.1.wt) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hb0) ha0
      _ = _ := by ring

lemma bnd_nonneg (T : T6) : (0 : ℝ) ≤ (bnd cl T : ℝ) := (abs_nonneg _).trans (bnd_sound h T)

lemma rowDrop_nonneg (t : M6 × Kel) (q : T6) : (0 : ℝ) ≤ (rowDrop cl t q : ℝ) := by
  induction q with
  | nil => simp [rowDrop]
  | cons s q ih =>
    simp only [rowDrop]
    split_ifs
    · exact ih
    · push_cast
      have := aub_nonneg h t.2; have := aub_nonneg h s.2; have := betapow_nonneg h (t.1.add s.1)
      have := rho_nonneg
      positivity

lemma mulDrop_nonneg (p q : T6) : (0 : ℝ) ≤ (mulDrop cl p q : ℝ) := by
  induction p with
  | nil => simp [mulDrop]
  | cons t p ih => simp only [mulDrop]; push_cast; exact add_nonneg (rowDrop_nonneg h t q) ih

/-- one row of the truncated product. -/
lemma row_sound (t : M6 × Kel) (q : T6) :
    |t.2.ev a * t.1.ev A B C Cp ri rj * evT6 q A B C Cp ri rj a - evT6 (rowKept t q) A B C Cp ri rj a|
      ≤ (rowDrop cl t q : ℝ) * R ^ 7 := by
  induction q with
  | nil => simp [rowKept, rowDrop, evT6]
  | cons s q ih =>
    simp only [rowKept, rowDrop]
    split_ifs with hw
    · rw [evT6_cons, evT6_cons, Kel.ev_mul _ _ h.hmin, M6.ev_add]
      refine le_of_eq_of_le ?_ ih
      congr 1; ring
    · rw [evT6_cons]
      push_cast
      have hw7 : 7 ≤ (t.1.add s.1).wt := by omega
      have hterm : |t.2.ev a * t.1.ev A B C Cp ri rj * (s.2.ev a * s.1.ev A B C Cp ri rj)|
          ≤ (t.2.aub aLo aHi : ℝ) * (s.2.aub aLo aHi : ℝ) * (cl.betapow (t.1.add s.1) : ℝ)
            * (rho : ℝ) ^ ((t.1.add s.1).wt - 7) * R ^ 7 := by
        have e : t.2.ev a * t.1.ev A B C Cp ri rj * (s.2.ev a * s.1.ev A B C Cp ri rj)
            = (t.2.ev a * s.2.ev a) * (t.1.add s.1).ev A B C Cp ri rj := by rw [M6.ev_add]; ring
        rw [e, abs_mul, abs_mul]
        have hm := mono_bound h (t.1.add s.1)
        have hR7 : R ^ (t.1.add s.1).wt ≤ (rho : ℝ) ^ ((t.1.add s.1).wt - 7) * R ^ 7 := by
          have e2 : R ^ (t.1.add s.1).wt = R ^ ((t.1.add s.1).wt - 7) * R ^ 7 := by
            rw [← pow_add]; congr 1; omega
          rw [e2]
          exact mul_le_mul_of_nonneg_right (pow_le_rho h _) (pow_nonneg h.hR0 7)
        have hb0 := betapow_nonneg h (t.1.add s.1)
        calc |t.2.ev a| * |s.2.ev a| * |(t.1.add s.1).ev A B C Cp ri rj|
            ≤ (t.2.aub aLo aHi : ℝ) * (s.2.aub aLo aHi : ℝ)
              * ((cl.betapow (t.1.add s.1) : ℝ) * ((rho : ℝ) ^ ((t.1.add s.1).wt - 7) * R ^ 7)) := by
              refine mul_le_mul (mul_le_mul (abs_ev_le' h _) (abs_ev_le' h _) (abs_nonneg _) (aub_nonneg h _))
                (hm.trans (mul_le_mul_of_nonneg_left hR7 hb0)) (abs_nonneg _) ?_
              exact mul_nonneg (aub_nonneg h _) (aub_nonneg h _)
          _ = _ := by ring
      calc |t.2.ev a * t.1.ev A B C Cp ri rj * (s.2.ev a * s.1.ev A B C Cp ri rj + evT6 q A B C Cp ri rj a)
              - evT6 (rowKept t q) A B C Cp ri rj a|
          = |t.2.ev a * t.1.ev A B C Cp ri rj * (s.2.ev a * s.1.ev A B C Cp ri rj)
              + (t.2.ev a * t.1.ev A B C Cp ri rj * evT6 q A B C Cp ri rj a
                - evT6 (rowKept t q) A B C Cp ri rj a)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hterm ih
        _ = _ := by ring

lemma mul_sound (p q : T6) :
    |evT6 p A B C Cp ri rj a * evT6 q A B C Cp ri rj a - evT6 (mulKept p q) A B C Cp ri rj a|
      ≤ (mulDrop cl p q : ℝ) * R ^ 7 := by
  induction p with
  | nil => simp [mulKept, mulDrop, evT6]
  | cons t p ih =>
    simp only [mulKept, mulDrop]
    rw [evT6_merge, evT6_cons]
    push_cast
    calc |(t.2.ev a * t.1.ev A B C Cp ri rj + evT6 p A B C Cp ri rj a) * evT6 q A B C Cp ri rj a
            - (evT6 (rowKept t q) A B C Cp ri rj a + evT6 (mulKept p q) A B C Cp ri rj a)|
        = |(t.2.ev a * t.1.ev A B C Cp ri rj * evT6 q A B C Cp ri rj a - evT6 (rowKept t q) A B C Cp ri rj a)
            + (evT6 p A B C Cp ri rj a * evT6 q A B C Cp ri rj a
              - evT6 (mulKept p q) A B C Cp ri rj a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (row_sound h t q) ih
      _ = _ := by ring

/-! ### The `Ok` calculus -/

lemma Ok_atomA : Ok cl A B C Cp ri rj R a (Rep.atom ⟨1, 0, 0, 0, 0, 0⟩) A := by
  simp [Ok, Rep.atom, evT6, M6.ev, Kel.ev_ofQ]
lemma Ok_atomB : Ok cl A B C Cp ri rj R a (Rep.atom ⟨0, 1, 0, 0, 0, 0⟩) B := by
  simp [Ok, Rep.atom, evT6, M6.ev, Kel.ev_ofQ]
lemma Ok_atomC : Ok cl A B C Cp ri rj R a (Rep.atom ⟨0, 0, 1, 0, 0, 0⟩) C := by
  simp [Ok, Rep.atom, evT6, M6.ev, Kel.ev_ofQ]
lemma Ok_atomCp : Ok cl A B C Cp ri rj R a (Rep.atom ⟨0, 0, 0, 1, 0, 0⟩) Cp := by
  simp [Ok, Rep.atom, evT6, M6.ev, Kel.ev_ofQ]
lemma Ok_atomRi : Ok cl A B C Cp ri rj R a (Rep.atom ⟨0, 0, 0, 0, 1, 0⟩) ri := by
  simp [Ok, Rep.atom, evT6, M6.ev, Kel.ev_ofQ]
lemma Ok_atomRj : Ok cl A B C Cp ri rj R a (Rep.atom ⟨0, 0, 0, 0, 0, 1⟩) rj := by
  simp [Ok, Rep.atom, evT6, M6.ev, Kel.ev_ofQ]

lemma Ok_e {e : ℝ} (he : |e| ≤ (cl.ce : ℝ) * R ^ 8) : Ok cl A B C Cp ri rj R a (Rep.e cl) e := by
  simp only [Ok, Rep.e, evT6_nil, sub_zero]
  push_cast
  refine ⟨mul_nonneg h.hce (rho_nonneg), ?_⟩
  calc |e| ≤ (cl.ce : ℝ) * R ^ 8 := he
    _ = (cl.ce : ℝ) * R * R ^ 7 := by ring
    _ ≤ (cl.ce : ℝ) * (rho : ℝ) * R ^ 7 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h.hR h.hce) (pow_nonneg h.hR0 7)

lemma Ok_add {r s : Rep} {q1 q2 : ℝ} (h1 : Ok cl A B C Cp ri rj R a r q1) (h2 : Ok cl A B C Cp ri rj R a s q2) :
    Ok cl A B C Cp ri rj R a (r.add s) (q1 + q2) := by
  simp only [Ok, Rep.add] at *
  rw [evT6_merge]; push_cast
  refine ⟨add_nonneg h1.1 h2.1, ?_⟩
  calc |q1 + q2 - (evT6 r.T A B C Cp ri rj a + evT6 s.T A B C Cp ri rj a)|
      = |(q1 - evT6 r.T A B C Cp ri rj a) + (q2 - evT6 s.T A B C Cp ri rj a)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1.2 h2.2
    _ = _ := by ring

lemma Ok_smul (c : Kel) {r : Rep} {q : ℝ} (h1 : Ok cl A B C Cp ri rj R a r q) :
    Ok cl A B C Cp ri rj R a (r.smul c) (c.ev a * q) := by
  simp only [Ok, Rep.smul] at *
  rw [evT6_smul h.hmin]; push_cast
  refine ⟨mul_nonneg (aub_nonneg h c) h1.1, ?_⟩
  calc |c.ev a * q - c.ev a * evT6 r.T A B C Cp ri rj a| = |c.ev a| * |q - evT6 r.T A B C Cp ri rj a| := by
        rw [← abs_mul]; congr 1; ring
    _ ≤ (c.aub aLo aHi : ℝ) * ((r.err : ℝ) * R ^ 7) :=
        mul_le_mul (abs_ev_le' h c) h1.2 (abs_nonneg _) (aub_nonneg h c)
    _ = _ := by ring

lemma Ok_smulQ (q0 : ℚ) (c : ℝ) (hc : (q0 : ℝ) = c) {r : Rep} {q : ℝ} (h1 : Ok cl A B C Cp ri rj R a r q) :
    Ok cl A B C Cp ri rj R a (r.smul (Kel.ofQ q0)) (c * q) := by
  have := Ok_smul h (Kel.ofQ q0) h1
  rwa [Kel.ev_ofQ, hc] at this

lemma Ok_mul {r s : Rep} {q1 q2 : ℝ} (h1 : Ok cl A B C Cp ri rj R a r q1) (h2 : Ok cl A B C Cp ri rj R a s q2) :
    Ok cl A B C Cp ri rj R a (Rep.mul cl r s) (q1 * q2) := by
  obtain ⟨e1, h1⟩ := h1
  obtain ⟨e2, h2⟩ := h2
  simp only [Ok, Rep.mul]
  push_cast
  have hb1 := bnd_sound h r.T
  have hb2 := bnd_sound h s.T
  have hm := mul_sound h r.T s.T
  have hR7 : R ^ 7 ≤ (rho : ℝ) ^ 7 := pow_le_rho h 7
  have hR0 := h.hR0
  have hR70 : 0 ≤ R ^ 7 := pow_nonneg hR0 7
  have hd := mulDrop_nonneg h r.T s.T
  have hbn1 := bnd_nonneg h r.T
  have hbn2 := bnd_nonneg h s.T
  refine ⟨by have := rho_nonneg; positivity, ?_⟩
  have hq2 : |q2| ≤ (bnd cl s.T : ℝ) + (s.err : ℝ) * (rho : ℝ) ^ 7 := by
    calc |q2| = |evT6 s.T A B C Cp ri rj a + (q2 - evT6 s.T A B C Cp ri rj a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ (bnd cl s.T : ℝ) + (s.err : ℝ) * R ^ 7 := add_le_add hb2 h2
      _ ≤ _ := by gcongr
  have t1 : |(q1 - evT6 r.T A B C Cp ri rj a) * q2|
      ≤ (r.err : ℝ) * R ^ 7 * ((bnd cl s.T : ℝ) + (s.err : ℝ) * (rho : ℝ) ^ 7) := by
    rw [abs_mul]; exact mul_le_mul h1 hq2 (abs_nonneg _) (mul_nonneg e1 hR70)
  have t2 : |evT6 r.T A B C Cp ri rj a * (q2 - evT6 s.T A B C Cp ri rj a)|
      ≤ (bnd cl r.T : ℝ) * ((s.err : ℝ) * R ^ 7) := by
    rw [abs_mul]; exact mul_le_mul hb1 h2 (abs_nonneg _) hbn1
  calc |q1 * q2 - evT6 (mulKept r.T s.T) A B C Cp ri rj a|
      = |(q1 - evT6 r.T A B C Cp ri rj a) * q2
          + evT6 r.T A B C Cp ri rj a * (q2 - evT6 s.T A B C Cp ri rj a)
          + (evT6 r.T A B C Cp ri rj a * evT6 s.T A B C Cp ri rj a
            - evT6 (mulKept r.T s.T) A B C Cp ri rj a)| := by congr 1; ring
    _ ≤ |(q1 - evT6 r.T A B C Cp ri rj a) * q2
          + evT6 r.T A B C Cp ri rj a * (q2 - evT6 s.T A B C Cp ri rj a)|
        + |evT6 r.T A B C Cp ri rj a * evT6 s.T A B C Cp ri rj a
            - evT6 (mulKept r.T s.T) A B C Cp ri rj a| := abs_add_le _ _
    _ ≤ (|(q1 - evT6 r.T A B C Cp ri rj a) * q2|
          + |evT6 r.T A B C Cp ri rj a * (q2 - evT6 s.T A B C Cp ri rj a)|)
        + (mulDrop cl r.T s.T : ℝ) * R ^ 7 := add_le_add (abs_add_le _ _) hm
    _ ≤ (r.err : ℝ) * R ^ 7 * ((bnd cl s.T : ℝ) + (s.err : ℝ) * (rho : ℝ) ^ 7)
          + (bnd cl r.T : ℝ) * ((s.err : ℝ) * R ^ 7) + (mulDrop cl r.T s.T : ℝ) * R ^ 7 := by
        gcongr
    _ = _ := by ring

lemma nuRep_ok {r e : Rep} {x ex : ℝ} (hr : Ok cl A B C Cp ri rj R a r x) (he : Ok cl A B C Cp ri rj R a e ex) :
    Ok cl A B C Cp ri rj R a (nuRep cl r e) (nhat x + ex) := by
  unfold nuRep nhat
  exact Ok_add h (Ok_add h (Ok_add h (Ok_smulQ h (-1/2) (-1/2) (by norm_num) hr)
    (Ok_smulQ h (-1/8) (-1/8) (by norm_num) (Ok_mul h hr hr)))
    (Ok_smulQ h (-1/16) (-1/16) (by norm_num) (Ok_mul h (Ok_mul h hr hr) hr))) he

/-- **Soundness of the class evaluator.** -/
theorem PhiRep_ok (g W inv : Kel) {ei ej : ℝ}
    (hei : |ei| ≤ (cl.ce : ℝ) * R ^ 8) (hej : |ej| ≤ (cl.ce : ℝ) * R ^ 8) :
    Ok cl A B C Cp ri rj R a (PhiRep cl g W inv)
      (PhiR (g.ev a) (W.ev a) (inv.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej)) := by
  have hA := Ok_atomA h
  have hB := Ok_atomB h
  have hC := Ok_atomC h
  have hCp := Ok_atomCp h
  have hνi := nuRep_ok h (Ok_atomRi h) (Ok_e h hei)
  have hνj := nuRep_ok h (Ok_atomRj h) (Ok_e h hej)
  have hhh := Ok_add h (Ok_add h (Ok_add h hB (Ok_mul h hνj hCp)) (Ok_mul h hνi hC))
    (Ok_smul h g (Ok_mul h hνi hνj))
  have hℓ := Ok_add h hA (Ok_smul h g (Ok_add h hνi hνj))
  have hu := Ok_smul h inv (Ok_add h hℓ hhh)
  have hu2 := Ok_mul h hu hu
  have hu3 := Ok_mul h hu2 hu
  have hu4 := Ok_mul h hu3 hu
  have hu5 := Ok_mul h hu4 hu
  have key := Ok_add h (Ok_smul h W hhh) (Ok_add h (Ok_add h (Ok_add h
    (Ok_smulQ h (1/4) (1/4) (by norm_num) hu2) (Ok_smulQ h (1/6) (1/6) (by norm_num) hu3))
    (Ok_smulQ h (1/8) (1/8) (by norm_num) hu4)) (Ok_smulQ h (1/10) (1/10) (by norm_num) hu5))
  unfold PhiRep PhiR
  exact key

/-- From a representation and a passed check to the real bound (stated for an abstract `r`). -/
lemma bound_of_Ok {r : Rep} {q : ℝ} (hok : Ok cl A B C Cp ri rj R a r q) (T : T6) (K : ℚ)
    (hT : eq6 r.T T = true) (hK : r.err ≤ K) :
    |q - evT6 T A B C Cp ri rj a| ≤ (K : ℝ) * R ^ 7 := by
  have hT' := evT6_eq_of_eq6 (A := A) (B := B) (C := C) (Cp := Cp) (ri := ri) (rj := rj) h.hmin _ _ hT
  have hK' : (r.err : ℝ) ≤ K := Rat.cast_le.mpr hK
  rw [← hT']
  exact hok.2.trans (mul_le_mul_of_nonneg_right hK' (pow_nonneg h.hR0 7))

/-- **Atom-level bound of a class**: from the kernel check `checkClass … = true`. -/
theorem class_bound (g W inv : Kel) (T : T6) (K : ℚ) (hc : checkClass cl g W inv T K = true)
    {ei ej : ℝ} (hei : |ei| ≤ (cl.ce : ℝ) * R ^ 8) (hej : |ej| ≤ (cl.ce : ℝ) * R ^ 8) :
    |PhiR (g.ev a) (W.ev a) (inv.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej) - evT6 T A B C Cp ri rj a|
      ≤ (K : ℝ) * R ^ 7 := by
  have hc' : eq6 (PhiRep cl g W inv).T T = true ∧ (PhiRep cl g W inv).err ≤ K := by
    have h2 := hc
    simp only [checkClass, Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2
  exact bound_of_Ok h (PhiRep_ok h g W inv hei hej) T K hc'.1 hc'.2

end semantics

/-! ## Class data (generated by `lean/gen/export_local_lean.py` from `local_atom.py`) -/

/-- `|e| ≤ CE r⁸` for the chart remainder (LocalGeom). -/
def CE : ℚ := 391 / 10000
/-- rational upper bound of √2 -/
def SQ2 : ℚ := 1414213563 / 1000000000

-- DATA

/-- `T6` of class `ring_adj` (g = ⟨-3/2, 0, 1/8, 0⟩): 68 monomials in `A B C C′ rᵢ² rⱼ²` -/
def T6adj : LocalSP.T6 :=
  [(⟨0, 0, 0, 0, 0, 2⟩, ⟨1/80, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 0, 3⟩, ⟨1/96, 0, -1/2400, 0⟩),
    (⟨0, 0, 0, 0, 1, 1⟩, ⟨-1/10, 0, 1/80, 0⟩),
    (⟨0, 0, 0, 0, 1, 2⟩, ⟨-1/40, 0, 3/1600, 0⟩),
    (⟨0, 0, 0, 0, 2, 0⟩, ⟨1/80, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 2, 1⟩, ⟨-1/40, 0, 3/1600, 0⟩),
    (⟨0, 0, 0, 0, 3, 0⟩, ⟨1/96, 0, -1/2400, 0⟩),
    (⟨0, 0, 0, 1, 0, 1⟩, ⟨0, 0, -1/40, 0⟩),
    (⟨0, 0, 0, 1, 0, 2⟩, ⟨-1/10, 0, 1/160, 0⟩),
    (⟨0, 0, 0, 1, 1, 1⟩, ⟨-1/10, 0, 1/80, 0⟩),
    (⟨0, 0, 0, 2, 0, 2⟩, ⟨-1/20, 0, 1/80, 0⟩),
    (⟨0, 0, 1, 0, 1, 0⟩, ⟨0, 0, -1/40, 0⟩),
    (⟨0, 0, 1, 0, 1, 1⟩, ⟨-1/10, 0, 1/80, 0⟩),
    (⟨0, 0, 1, 0, 2, 0⟩, ⟨-1/10, 0, 1/160, 0⟩),
    (⟨0, 0, 1, 1, 1, 1⟩, ⟨-1/10, 0, 1/40, 0⟩),
    (⟨0, 0, 2, 0, 2, 0⟩, ⟨-1/20, 0, 1/80, 0⟩),
    (⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1/20, 0⟩),
    (⟨0, 1, 0, 0, 0, 1⟩, ⟨1/5, 0, -1/40, 0⟩),
    (⟨0, 1, 0, 0, 0, 2⟩, ⟨1/20, 0, -3/800, 0⟩),
    (⟨0, 1, 0, 0, 1, 0⟩, ⟨1/5, 0, -1/40, 0⟩),
    (⟨0, 1, 0, 0, 1, 1⟩, ⟨-1/10, 0, 7/400, 0⟩),
    (⟨0, 1, 0, 0, 2, 0⟩, ⟨1/20, 0, -3/800, 0⟩),
    (⟨0, 1, 0, 1, 0, 1⟩, ⟨1/5, 0, -1/20, 0⟩),
    (⟨0, 1, 1, 0, 1, 0⟩, ⟨1/5, 0, -1/20, 0⟩),
    (⟨0, 2, 0, 0, 0, 0⟩, ⟨-1/5, 0, 1/20, 0⟩),
    (⟨0, 2, 0, 0, 0, 1⟩, ⟨1/5, 0, -3/100, 0⟩),
    (⟨0, 2, 0, 0, 1, 0⟩, ⟨1/5, 0, -3/100, 0⟩),
    (⟨0, 3, 0, 0, 0, 0⟩, ⟨-4/15, 0, 4/75, 0⟩),
    (⟨1, 0, 0, 0, 0, 1⟩, ⟨1/5, 0, -1/40, 0⟩),
    (⟨1, 0, 0, 0, 0, 2⟩, ⟨1/20, 0, -3/800, 0⟩),
    (⟨1, 0, 0, 0, 1, 0⟩, ⟨1/5, 0, -1/40, 0⟩),
    (⟨1, 0, 0, 0, 1, 1⟩, ⟨-1/10, 0, 7/400, 0⟩),
    (⟨1, 0, 0, 0, 2, 0⟩, ⟨1/20, 0, -3/800, 0⟩),
    (⟨1, 0, 0, 1, 0, 1⟩, ⟨1/5, 0, -1/20, 0⟩),
    (⟨1, 0, 0, 1, 0, 2⟩, ⟨-3/20, 0, 7/400, 0⟩),
    (⟨1, 0, 0, 1, 1, 1⟩, ⟨-1/5, 0, 3/100, 0⟩),
    (⟨1, 0, 1, 0, 1, 0⟩, ⟨1/5, 0, -1/20, 0⟩),
    (⟨1, 0, 1, 0, 1, 1⟩, ⟨-1/5, 0, 3/100, 0⟩),
    (⟨1, 0, 1, 0, 2, 0⟩, ⟨-3/20, 0, 7/400, 0⟩),
    (⟨1, 1, 0, 0, 0, 0⟩, ⟨-2/5, 0, 1/10, 0⟩),
    (⟨1, 1, 0, 0, 0, 1⟩, ⟨2/5, 0, -3/50, 0⟩),
    (⟨1, 1, 0, 0, 1, 0⟩, ⟨2/5, 0, -3/50, 0⟩),
    (⟨1, 1, 0, 1, 0, 1⟩, ⟨4/5, 0, -4/25, 0⟩),
    (⟨1, 1, 1, 0, 1, 0⟩, ⟨4/5, 0, -4/25, 0⟩),
    (⟨1, 2, 0, 0, 0, 0⟩, ⟨-4/5, 0, 4/25, 0⟩),
    (⟨2, 0, 0, 0, 0, 0⟩, ⟨-1/5, 0, 1/20, 0⟩),
    (⟨2, 0, 0, 0, 0, 1⟩, ⟨1/5, 0, -3/100, 0⟩),
    (⟨2, 0, 0, 0, 0, 2⟩, ⟨1/50, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 1, 0⟩, ⟨1/5, 0, -3/100, 0⟩),
    (⟨2, 0, 0, 0, 1, 1⟩, ⟨-4/25, 0, 3/100, 0⟩),
    (⟨2, 0, 0, 0, 2, 0⟩, ⟨1/50, 0, 0, 0⟩),
    (⟨2, 0, 0, 1, 0, 1⟩, ⟨2/5, 0, -2/25, 0⟩),
    (⟨2, 0, 1, 0, 1, 0⟩, ⟨2/5, 0, -2/25, 0⟩),
    (⟨2, 1, 0, 0, 0, 0⟩, ⟨-4/5, 0, 4/25, 0⟩),
    (⟨2, 1, 0, 0, 0, 1⟩, ⟨18/25, 0, -3/25, 0⟩),
    (⟨2, 1, 0, 0, 1, 0⟩, ⟨18/25, 0, -3/25, 0⟩),
    (⟨2, 2, 0, 0, 0, 0⟩, ⟨-48/25, 0, 9/25, 0⟩),
    (⟨3, 0, 0, 0, 0, 0⟩, ⟨-4/15, 0, 4/75, 0⟩),
    (⟨3, 0, 0, 0, 0, 1⟩, ⟨6/25, 0, -1/25, 0⟩),
    (⟨3, 0, 0, 0, 1, 0⟩, ⟨6/25, 0, -1/25, 0⟩),
    (⟨3, 0, 0, 1, 0, 1⟩, ⟨16/25, 0, -3/25, 0⟩),
    (⟨3, 0, 1, 0, 1, 0⟩, ⟨16/25, 0, -3/25, 0⟩),
    (⟨3, 1, 0, 0, 0, 0⟩, ⟨-32/25, 0, 6/25, 0⟩),
    (⟨4, 0, 0, 0, 0, 0⟩, ⟨-8/25, 0, 3/50, 0⟩),
    (⟨4, 0, 0, 0, 0, 1⟩, ⟨8/25, 0, -7/125, 0⟩),
    (⟨4, 0, 0, 0, 1, 0⟩, ⟨8/25, 0, -7/125, 0⟩),
    (⟨4, 1, 0, 0, 0, 0⟩, ⟨-48/25, 0, 44/125, 0⟩),
    (⟨5, 0, 0, 0, 0, 0⟩, ⟨-48/125, 0, 44/625, 0⟩)]

def g_adj : Kel := ⟨-3/2, 0, 1/8, 0⟩
def W_adj : Kel := ⟨0, 0, 1/20, 0⟩
def inv_adj : Kel := ⟨0, 0, 1/10, 0⟩
/-- rational upper bound of √(1 − g²) -/
def sg_adj : ℚ := 951056517/1000000000
def cl_adj : Cls := ⟨SQ2 * sg_adj, 1/2, sg_adj, CE⟩
/-- `K_g` of class `ring_adj` (exact err 36.492852) -/
def K_adj : ℚ := 364929/10000

set_option profiler true in
theorem check_adj : checkClass cl_adj g_adj W_adj inv_adj T6adj K_adj = true := by
  decide +kernel

/-- **Atom-level bound, class `ring_adj`.** -/
theorem bound_adj {A B C Cp ri rj R a ei ej : ℝ} (h : Hyp cl_adj A B C Cp ri rj R a)
    (hei : |ei| ≤ (CE : ℝ) * R ^ 8) (hej : |ej| ≤ (CE : ℝ) * R ^ 8) :
    |PhiR (g_adj.ev a) (W_adj.ev a) (inv_adj.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej)
        - evT6 T6adj A B C Cp ri rj a| ≤ (K_adj : ℝ) * R ^ 7 :=
  class_bound h g_adj W_adj inv_adj T6adj K_adj check_adj hei hej

/-- `T6` of class `ring_diag` (g = ⟨1, 0, -1/8, 0⟩): 68 monomials in `A B C C′ rᵢ² rⱼ²` -/
def T6diag : LocalSP.T6 :=
  [(⟨0, 0, 0, 0, 0, 2⟩, ⟨1/80, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 0, 3⟩, ⟨1/480, 0, 1/2400, 0⟩),
    (⟨0, 0, 0, 0, 1, 1⟩, ⟨3/20, 0, -1/80, 0⟩),
    (⟨0, 0, 0, 0, 1, 2⟩, ⟨1/80, 0, -3/1600, 0⟩),
    (⟨0, 0, 0, 0, 2, 0⟩, ⟨1/80, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 2, 1⟩, ⟨1/80, 0, -3/1600, 0⟩),
    (⟨0, 0, 0, 0, 3, 0⟩, ⟨1/480, 0, 1/2400, 0⟩),
    (⟨0, 0, 0, 1, 0, 1⟩, ⟨-1/2, 0, 1/40, 0⟩),
    (⟨0, 0, 0, 1, 0, 2⟩, ⟨1/40, 0, -1/160, 0⟩),
    (⟨0, 0, 0, 1, 1, 1⟩, ⟨3/20, 0, -1/80, 0⟩),
    (⟨0, 0, 0, 2, 0, 2⟩, ⟨1/5, 0, -1/80, 0⟩),
    (⟨0, 0, 1, 0, 1, 0⟩, ⟨-1/2, 0, 1/40, 0⟩),
    (⟨0, 0, 1, 0, 1, 1⟩, ⟨3/20, 0, -1/80, 0⟩),
    (⟨0, 0, 1, 0, 2, 0⟩, ⟨1/40, 0, -1/160, 0⟩),
    (⟨0, 0, 1, 1, 1, 1⟩, ⟨2/5, 0, -1/40, 0⟩),
    (⟨0, 0, 2, 0, 2, 0⟩, ⟨1/5, 0, -1/80, 0⟩),
    (⟨0, 1, 0, 0, 0, 0⟩, ⟨1, 0, -1/20, 0⟩),
    (⟨0, 1, 0, 0, 0, 1⟩, ⟨-3/10, 0, 1/40, 0⟩),
    (⟨0, 1, 0, 0, 0, 2⟩, ⟨-1/40, 0, 3/800, 0⟩),
    (⟨0, 1, 0, 0, 1, 0⟩, ⟨-3/10, 0, 1/40, 0⟩),
    (⟨0, 1, 0, 0, 1, 1⟩, ⟨1/4, 0, -7/400, 0⟩),
    (⟨0, 1, 0, 0, 2, 0⟩, ⟨-1/40, 0, 3/800, 0⟩),
    (⟨0, 1, 0, 1, 0, 1⟩, ⟨-4/5, 0, 1/20, 0⟩),
    (⟨0, 1, 1, 0, 1, 0⟩, ⟨-4/5, 0, 1/20, 0⟩),
    (⟨0, 2, 0, 0, 0, 0⟩, ⟨4/5, 0, -1/20, 0⟩),
    (⟨0, 2, 0, 0, 0, 1⟩, ⟨-2/5, 0, 3/100, 0⟩),
    (⟨0, 2, 0, 0, 1, 0⟩, ⟨-2/5, 0, 3/100, 0⟩),
    (⟨0, 3, 0, 0, 0, 0⟩, ⟨4/5, 0, -4/75, 0⟩),
    (⟨1, 0, 0, 0, 0, 1⟩, ⟨-3/10, 0, 1/40, 0⟩),
    (⟨1, 0, 0, 0, 0, 2⟩, ⟨-1/40, 0, 3/800, 0⟩),
    (⟨1, 0, 0, 0, 1, 0⟩, ⟨-3/10, 0, 1/40, 0⟩),
    (⟨1, 0, 0, 0, 1, 1⟩, ⟨1/4, 0, -7/400, 0⟩),
    (⟨1, 0, 0, 0, 2, 0⟩, ⟨-1/40, 0, 3/800, 0⟩),
    (⟨1, 0, 0, 1, 0, 1⟩, ⟨-4/5, 0, 1/20, 0⟩),
    (⟨1, 0, 0, 1, 0, 2⟩, ⟨1/5, 0, -7/400, 0⟩),
    (⟨1, 0, 0, 1, 1, 1⟩, ⟨2/5, 0, -3/100, 0⟩),
    (⟨1, 0, 1, 0, 1, 0⟩, ⟨-4/5, 0, 1/20, 0⟩),
    (⟨1, 0, 1, 0, 1, 1⟩, ⟨2/5, 0, -3/100, 0⟩),
    (⟨1, 0, 1, 0, 2, 0⟩, ⟨1/5, 0, -7/400, 0⟩),
    (⟨1, 1, 0, 0, 0, 0⟩, ⟨8/5, 0, -1/10, 0⟩),
    (⟨1, 1, 0, 0, 0, 1⟩, ⟨-4/5, 0, 3/50, 0⟩),
    (⟨1, 1, 0, 0, 1, 0⟩, ⟨-4/5, 0, 3/50, 0⟩),
    (⟨1, 1, 0, 1, 0, 1⟩, ⟨-12/5, 0, 4/25, 0⟩),
    (⟨1, 1, 1, 0, 1, 0⟩, ⟨-12/5, 0, 4/25, 0⟩),
    (⟨1, 2, 0, 0, 0, 0⟩, ⟨12/5, 0, -4/25, 0⟩),
    (⟨2, 0, 0, 0, 0, 0⟩, ⟨4/5, 0, -1/20, 0⟩),
    (⟨2, 0, 0, 0, 0, 1⟩, ⟨-2/5, 0, 3/100, 0⟩),
    (⟨2, 0, 0, 0, 0, 2⟩, ⟨1/50, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 1, 0⟩, ⟨-2/5, 0, 3/100, 0⟩),
    (⟨2, 0, 0, 0, 1, 1⟩, ⟨11/25, 0, -3/100, 0⟩),
    (⟨2, 0, 0, 0, 2, 0⟩, ⟨1/50, 0, 0, 0⟩),
    (⟨2, 0, 0, 1, 0, 1⟩, ⟨-6/5, 0, 2/25, 0⟩),
    (⟨2, 0, 1, 0, 1, 0⟩, ⟨-6/5, 0, 2/25, 0⟩),
    (⟨2, 1, 0, 0, 0, 0⟩, ⟨12/5, 0, -4/25, 0⟩),
    (⟨2, 1, 0, 0, 0, 1⟩, ⟨-42/25, 0, 3/25, 0⟩),
    (⟨2, 1, 0, 0, 1, 0⟩, ⟨-42/25, 0, 3/25, 0⟩),
    (⟨2, 2, 0, 0, 0, 0⟩, ⟨132/25, 0, -9/25, 0⟩),
    (⟨3, 0, 0, 0, 0, 0⟩, ⟨4/5, 0, -4/75, 0⟩),
    (⟨3, 0, 0, 0, 0, 1⟩, ⟨-14/25, 0, 1/25, 0⟩),
    (⟨3, 0, 0, 0, 1, 0⟩, ⟨-14/25, 0, 1/25, 0⟩),
    (⟨3, 0, 0, 1, 0, 1⟩, ⟨-44/25, 0, 3/25, 0⟩),
    (⟨3, 0, 1, 0, 1, 0⟩, ⟨-44/25, 0, 3/25, 0⟩),
    (⟨3, 1, 0, 0, 0, 0⟩, ⟨88/25, 0, -6/25, 0⟩),
    (⟨4, 0, 0, 0, 0, 0⟩, ⟨22/25, 0, -3/50, 0⟩),
    (⟨4, 0, 0, 0, 0, 1⟩, ⟨-4/5, 0, 7/125, 0⟩),
    (⟨4, 0, 0, 0, 1, 0⟩, ⟨-4/5, 0, 7/125, 0⟩),
    (⟨4, 1, 0, 0, 0, 0⟩, ⟨128/25, 0, -44/125, 0⟩),
    (⟨5, 0, 0, 0, 0, 0⟩, ⟨128/125, 0, -44/625, 0⟩)]

def g_diag : Kel := ⟨1, 0, -1/8, 0⟩
def W_diag : Kel := ⟨1, 0, -1/20, 0⟩
def inv_diag : Kel := ⟨2, 0, -1/10, 0⟩
/-- rational upper bound of √(1 − g²) -/
def sg_diag : ℚ := 587785253/1000000000
def cl_diag : Cls := ⟨SQ2 * sg_diag, 1/2, sg_diag, CE⟩
/-- `K_g` of class `ring_diag` (exact err 0.532784) -/
def K_diag : ℚ := 333/625

set_option profiler true in
theorem check_diag : checkClass cl_diag g_diag W_diag inv_diag T6diag K_diag = true := by
  decide +kernel

/-- **Atom-level bound, class `ring_diag`.** -/
theorem bound_diag {A B C Cp ri rj R a ei ej : ℝ} (h : Hyp cl_diag A B C Cp ri rj R a)
    (hei : |ei| ≤ (CE : ℝ) * R ^ 8) (hej : |ej| ≤ (CE : ℝ) * R ^ 8) :
    |PhiR (g_diag.ev a) (W_diag.ev a) (inv_diag.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej)
        - evT6 T6diag A B C Cp ri rj a| ≤ (K_diag : ℝ) * R ^ 7 :=
  class_bound h g_diag W_diag inv_diag T6diag K_diag check_diag hei hej

/-- `T6` of class `pole_ring` (g = ⟨0, 0, 0, 0⟩): 32 monomials in `A B C C′ rᵢ² rⱼ²` -/
def T6pole : LocalSP.T6 :=
  [(⟨0, 0, 0, 1, 0, 1⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨0, 0, 0, 1, 0, 2⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨0, 0, 0, 2, 0, 2⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨0, 0, 1, 0, 1, 0⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨0, 0, 1, 0, 2, 0⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨0, 0, 1, 1, 1, 1⟩, ⟨1/8, 0, 0, 0⟩),
    (⟨0, 0, 2, 0, 2, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨0, 1, 0, 0, 0, 0⟩, ⟨1/2, 0, 0, 0⟩),
    (⟨0, 1, 0, 1, 0, 1⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨0, 1, 1, 0, 1, 0⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨0, 2, 0, 0, 0, 0⟩, ⟨1/4, 0, 0, 0⟩),
    (⟨0, 3, 0, 0, 0, 0⟩, ⟨1/6, 0, 0, 0⟩),
    (⟨1, 0, 0, 1, 0, 1⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨1, 0, 0, 1, 0, 2⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨1, 0, 1, 0, 1, 0⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨1, 0, 1, 0, 2, 0⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨1, 1, 0, 0, 0, 0⟩, ⟨1/2, 0, 0, 0⟩),
    (⟨1, 1, 0, 1, 0, 1⟩, ⟨-1/2, 0, 0, 0⟩),
    (⟨1, 1, 1, 0, 1, 0⟩, ⟨-1/2, 0, 0, 0⟩),
    (⟨1, 2, 0, 0, 0, 0⟩, ⟨1/2, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 0, 0⟩, ⟨1/4, 0, 0, 0⟩),
    (⟨2, 0, 0, 1, 0, 1⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨2, 0, 1, 0, 1, 0⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨2, 1, 0, 0, 0, 0⟩, ⟨1/2, 0, 0, 0⟩),
    (⟨2, 2, 0, 0, 0, 0⟩, ⟨3/4, 0, 0, 0⟩),
    (⟨3, 0, 0, 0, 0, 0⟩, ⟨1/6, 0, 0, 0⟩),
    (⟨3, 0, 0, 1, 0, 1⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨3, 0, 1, 0, 1, 0⟩, ⟨-1/4, 0, 0, 0⟩),
    (⟨3, 1, 0, 0, 0, 0⟩, ⟨1/2, 0, 0, 0⟩),
    (⟨4, 0, 0, 0, 0, 0⟩, ⟨1/8, 0, 0, 0⟩),
    (⟨4, 1, 0, 0, 0, 0⟩, ⟨1/2, 0, 0, 0⟩),
    (⟨5, 0, 0, 0, 0, 0⟩, ⟨1/10, 0, 0, 0⟩)]

def g_pole : Kel := ⟨0, 0, 0, 0⟩
def W_pole : Kel := ⟨1/2, 0, 0, 0⟩
def inv_pole : Kel := ⟨1, 0, 0, 0⟩
/-- rational upper bound of √(1 − g²) -/
def sg_pole : ℚ := 1000000001/1000000000
def cl_pole : Cls := ⟨SQ2 * sg_pole, 1/2, sg_pole, CE⟩
/-- `K_g` of class `pole_ring` (exact err 5.564423) -/
def K_pole : ℚ := 11129/2000

set_option profiler true in
theorem check_pole : checkClass cl_pole g_pole W_pole inv_pole T6pole K_pole = true := by
  decide +kernel

/-- **Atom-level bound, class `pole_ring`.** -/
theorem bound_pole {A B C Cp ri rj R a ei ej : ℝ} (h : Hyp cl_pole A B C Cp ri rj R a)
    (hei : |ei| ≤ (CE : ℝ) * R ^ 8) (hej : |ej| ≤ (CE : ℝ) * R ^ 8) :
    |PhiR (g_pole.ev a) (W_pole.ev a) (inv_pole.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej)
        - evT6 T6pole A B C Cp ri rj a| ≤ (K_pole : ℝ) * R ^ 7 :=
  class_bound h g_pole W_pole inv_pole T6pole K_pole check_pole hei hej

/-- `T6` of class `pole_pole` (g = ⟨-1, 0, 0, 0⟩): 66 monomials in `A B C C′ rᵢ² rⱼ²` -/
def T6pp : LocalSP.T6 :=
  [(⟨0, 0, 0, 0, 0, 2⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 0, 3⟩, ⟨1/96, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 1, 1⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 1, 2⟩, ⟨-1/64, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 2, 0⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 2, 1⟩, ⟨-1/64, 0, 0, 0⟩),
    (⟨0, 0, 0, 0, 3, 0⟩, ⟨1/96, 0, 0, 0⟩),
    (⟨0, 0, 0, 1, 0, 1⟩, ⟨-1/8, 0, 0, 0⟩),
    (⟨0, 0, 0, 1, 0, 2⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨0, 0, 0, 1, 1, 1⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨0, 0, 0, 2, 0, 2⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨0, 0, 1, 0, 1, 0⟩, ⟨-1/8, 0, 0, 0⟩),
    (⟨0, 0, 1, 0, 1, 1⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨0, 0, 1, 0, 2, 0⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨0, 0, 1, 1, 1, 1⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨0, 0, 2, 0, 2, 0⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨0, 1, 0, 0, 0, 0⟩, ⟨1/4, 0, 0, 0⟩),
    (⟨0, 1, 0, 0, 0, 1⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨0, 1, 0, 0, 0, 2⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨0, 1, 0, 0, 1, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨0, 1, 0, 0, 2, 0⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨0, 1, 0, 1, 0, 1⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨0, 1, 1, 0, 1, 0⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨0, 2, 0, 0, 0, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨0, 2, 0, 0, 0, 1⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨0, 2, 0, 0, 1, 0⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨0, 3, 0, 0, 0, 0⟩, ⟨1/48, 0, 0, 0⟩),
    (⟨1, 0, 0, 0, 0, 1⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨1, 0, 0, 0, 0, 2⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨1, 0, 0, 0, 1, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨1, 0, 0, 0, 2, 0⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨1, 0, 0, 1, 0, 1⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨1, 0, 0, 1, 0, 2⟩, ⟨-3/64, 0, 0, 0⟩),
    (⟨1, 0, 0, 1, 1, 1⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨1, 0, 1, 0, 1, 0⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨1, 0, 1, 0, 1, 1⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨1, 0, 1, 0, 2, 0⟩, ⟨-3/64, 0, 0, 0⟩),
    (⟨1, 1, 0, 0, 0, 0⟩, ⟨1/8, 0, 0, 0⟩),
    (⟨1, 1, 0, 0, 0, 1⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨1, 1, 0, 0, 1, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨1, 1, 0, 1, 0, 1⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨1, 1, 1, 0, 1, 0⟩, ⟨-1/16, 0, 0, 0⟩),
    (⟨1, 2, 0, 0, 0, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 0, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 0, 1⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 0, 2⟩, ⟨5/256, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 1, 0⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 1, 1⟩, ⟨1/128, 0, 0, 0⟩),
    (⟨2, 0, 0, 0, 2, 0⟩, ⟨5/256, 0, 0, 0⟩),
    (⟨2, 0, 0, 1, 0, 1⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨2, 0, 1, 0, 1, 0⟩, ⟨-1/32, 0, 0, 0⟩),
    (⟨2, 1, 0, 0, 0, 0⟩, ⟨1/16, 0, 0, 0⟩),
    (⟨2, 1, 0, 0, 0, 1⟩, ⟨3/64, 0, 0, 0⟩),
    (⟨2, 1, 0, 0, 1, 0⟩, ⟨3/64, 0, 0, 0⟩),
    (⟨2, 2, 0, 0, 0, 0⟩, ⟨3/64, 0, 0, 0⟩),
    (⟨3, 0, 0, 0, 0, 0⟩, ⟨1/48, 0, 0, 0⟩),
    (⟨3, 0, 0, 0, 0, 1⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨3, 0, 0, 0, 1, 0⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨3, 0, 0, 1, 0, 1⟩, ⟨-1/64, 0, 0, 0⟩),
    (⟨3, 0, 1, 0, 1, 0⟩, ⟨-1/64, 0, 0, 0⟩),
    (⟨3, 1, 0, 0, 0, 0⟩, ⟨1/32, 0, 0, 0⟩),
    (⟨4, 0, 0, 0, 0, 0⟩, ⟨1/128, 0, 0, 0⟩),
    (⟨4, 0, 0, 0, 0, 1⟩, ⟨1/128, 0, 0, 0⟩),
    (⟨4, 0, 0, 0, 1, 0⟩, ⟨1/128, 0, 0, 0⟩),
    (⟨4, 1, 0, 0, 0, 0⟩, ⟨1/64, 0, 0, 0⟩),
    (⟨5, 0, 0, 0, 0, 0⟩, ⟨1/320, 0, 0, 0⟩)]

def g_pp : Kel := ⟨-1, 0, 0, 0⟩
def W_pp : Kel := ⟨1/4, 0, 0, 0⟩
def inv_pp : Kel := ⟨1/2, 0, 0, 0⟩
/-- rational upper bound of √(1 − g²) -/
def sg_pp : ℚ := 0
def cl_pp : Cls := ⟨SQ2 * sg_pp, 1/2, sg_pp, CE⟩
/-- `K_g` of class `pole_pole` (exact err 0.001763) -/
def K_pp : ℚ := 9/5000

set_option profiler true in
theorem check_pp : checkClass cl_pp g_pp W_pp inv_pp T6pp K_pp = true := by
  decide +kernel

/-- **Atom-level bound, class `pole_pole`.** -/
theorem bound_pp {A B C Cp ri rj R a ei ej : ℝ} (h : Hyp cl_pp A B C Cp ri rj R a)
    (hei : |ei| ≤ (CE : ℝ) * R ^ 8) (hej : |ej| ≤ (CE : ℝ) * R ^ 8) :
    |PhiR (g_pp.ev a) (W_pp.ev a) (inv_pp.ev a) A B C Cp (nhat ri + ei) (nhat rj + ej)
        - evT6 T6pp A B C Cp ri rj a| ≤ (K_pp : ℝ) * R ^ 7 :=
  class_bound h g_pp W_pp inv_pp T6pp K_pp check_pp hei hej

end LocalAtom

#print axioms LocalAtom.bound_adj
#print axioms LocalAtom.bound_diag
#print axioms LocalAtom.bound_pole
#print axioms LocalAtom.bound_pp
