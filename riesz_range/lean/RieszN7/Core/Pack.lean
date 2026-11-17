import Mathlib.Data.Int.Init

/-!
# `RieszN7.Core.Pack` — packed integer data (one big `Nat` literal per row), unpacked by the kernel

Large `List (List ℤ)` literals are slow to *elaborate* (the 83 × 83 LDL test did not finish in 24 min); the s = 1
data modules avoid them the same way (`mkBlk` with hex literals).  A row of `k` integers is one natural number holding
`k` fields of `w` bits, field `j` = zigzag code of entry `j` (`v ↦ 2v` for `v ≥ 0`, `v ↦ −2v − 1` for `v < 0`).
Only definitions: what the data *is* is whatever these functions compute; no soundness lemma is needed.
Private prototype (Phase 1), AI-written, not reviewed.
-/

namespace RieszN7.Pack

def unzig (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) - 1

/-- `k` fields of `w` bits, low field first. -/
def unpack (w : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | k + 1, N => unzig (N % 2 ^ w) :: unpack w k (N / 2 ^ w)

/-- Rows of length `n`. -/
def unpackRows (w n : ℕ) (rows : List ℕ) : List (List ℤ) := rows.map (unpack w n)

/-- Lower-triangular rows: row `i` (from `k = i + 1`) has `i + 1` fields. -/
def unpackTri (w : ℕ) : ℕ → List ℕ → List (List ℤ)
  | _, [] => []
  | k, r :: rs => unpack w k r :: unpackTri w (k + 1) rs

example : unpack 8 3 (4 + 3 * 2 ^ 8 + 0 * 2 ^ 16) = [2, -2, 0] := by decide +kernel

/-! ### Strict variants (Phase 1 / §5-rev)

The kernel does not memoise: in `unpack w k (N / 2 ^ w)` the quotient stays an unevaluated term, so field `j` of a row
re-evaluates the whole chain `((N / 2^w) / 2^w) / …` (`O(k²)` big divisions per row; measured as an `n^3.8` total in the
LDL tests).  `unpackS` matches on the quotient, which forces the kernel to reduce it to a literal before recursing. -/

def unpackS (w : ℕ) : ℕ → ℕ → List ℤ
  | 0, _ => []
  | k + 1, N =>
    unzig (N % 2 ^ w) ::
      (match N / 2 ^ w with
       | 0 => unpackS w k 0
       | q + 1 => unpackS w k (q + 1))

def unpackRowsS (w n : ℕ) (rows : List ℕ) : List (List ℤ) := rows.map (unpackS w n)

def unpackTriS (w : ℕ) : ℕ → List ℕ → List (List ℤ)
  | _, [] => []
  | k, r :: rs => unpackS w k r :: unpackTriS w (k + 1) rs

example : unpackS 8 3 (4 + 3 * 2 ^ 8 + 0 * 2 ^ 16) = [2, -2, 0] := by decide +kernel

end RieszN7.Pack
