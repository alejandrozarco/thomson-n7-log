import ThomsonGen.Case1Stat

/-!
# `RieszN7.Cells.C1Split` — splitting the Kronecker statistics of one Case 1 SOS block

Hand-written (Phase 2a, 2026-11-08; private, AI-written, not reviewed).

Upstream's `ThomsonN7.Case1.c1Stat` evaluates the statistics of a whole SOS block `sblkE an ad s` in one kernel
`decide`.  For the degree-5 block `S0` (`|z| = 56`) of the Riesz Case 1 nodes this one evaluation peaks at about
9.3 GB on enzo.  `c1Stat_sblkE` rewrites the statistics of a block with identity permutation (`s.σ = 0`) as
`c1Mul (stat of the multiplier) (c1Add (Σ over pivots q) (Σ over remainder rows a))`, and `c1Sum_append` splits a
list sum, so that each part can be evaluated in its own declaration.  Only definitional unfolding and the
associativity of `c1Add` are used; nothing about the certificate is assumed.
-/

namespace RieszN7.C1Split

open ThomsonN7 ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert ThomsonN7.Case1

theorem c1Add_c0 (x : C1Stat) : c1Add (c1C 0) x = x := by
  obtain ⟨a, b, c, d, e⟩ := x
  simp [c1Add, c1C]

theorem c1Add_assoc (x y z : C1Stat) : c1Add (c1Add x y) z = c1Add x (c1Add y z) := by
  obtain ⟨a1, b1, c1, d1, e1⟩ := x
  obtain ⟨a2, b2, c2, d2, e2⟩ := y
  obtain ⟨a3, b3, c3, d3, e3⟩ := z
  simp only [c1Add, Prod.mk.injEq]
  refine ⟨by ring, max_assoc _ _ _, max_assoc _ _ _, max_assoc _ _ _, by ring⟩

theorem c1Sum_append (l1 l2 : List C1Stat) : c1Sum (l1 ++ l2) = c1Add (c1Sum l1) (c1Sum l2) := by
  induction l1 with
  | nil => exact (c1Add_c0 _).symm
  | cons x l ih =>
    show c1Add x (c1Sum (l ++ l2)) = c1Add (c1Add x (c1Sum l)) (c1Sum l2)
    rw [ih, c1Add_assoc]

theorem c1Stat_sbst012 (w D : ℕ) (e : Ex) : c1Stat w D (sbst 0 1 2 e) = c1Stat w D e := by
  induction e with
  | c n => rfl
  | mon a b d => simp [sbst, c1Stat]
  | add p q ihp ihq =>
    show c1Add (c1Stat w D (sbst 0 1 2 p)) (c1Stat w D (sbst 0 1 2 q)) = c1Add (c1Stat w D p) (c1Stat w D q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show c1Mul (c1Stat w D (sbst 0 1 2 p)) (c1Stat w D (sbst 0 1 2 q)) = c1Mul (c1Stat w D p) (c1Stat w D q)
    rw [ihp, ihq]

/-- The pivot part `q` of the quadratic form of a block (one summand of `sqfE`). -/
def pivE (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (q : ℕ) : Ex :=
  smulNZ (b.dq q) (Ex.sq (sumRange zs.length fun a => smulNZ (b.lq q a) (zmon zs a)))

/-- The remainder row `a` of the quadratic form of a block (one summand of `sqfE`). -/
def remE (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (a : ℕ) : Ex :=
  sumRange zs.length fun c => smulNZ (b.del a c) (zzmon zs a c)

/-- Statistics of an SOS block with identity permutation, split into pivots and remainder rows. -/
theorem c1Stat_sblkE (w D : ℕ) (an : ℤ) (ad : ℕ) (s : SBlk) (hσ : s.σ = 0) :
    c1Stat w D (sblkE an ad s) = c1Mul (c1Stat w D (gE an ad s.g))
      (c1Add (c1Sum ((List.range s.z.length).map fun q => c1Stat w D (pivE s.B s.z q)))
        (c1Sum ((List.range s.z.length).map fun a => c1Stat w D (remE s.B s.z a)))) := by
  unfold sblkE
  rw [hσ]
  show c1Stat w D (sbst 0 1 2 (mul (gE an ad s.g) (sqfE s.B s.z))) = _
  rw [c1Stat_sbst012]
  show c1Mul (c1Stat w D (gE an ad s.g))
      (c1Add (c1Stat w D (sumRange s.z.length fun q => pivE s.B s.z q))
        (c1Stat w D (sumRange s.z.length fun a => remE s.B s.z a))) = _
  rw [c1Stat_sumRange, c1Stat_sumRange]

end RieszN7.C1Split
