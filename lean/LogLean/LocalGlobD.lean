import LogLean.LocalGlobA

/-! # LocalGlobD: kernel checks of the global level (Bombieri squares and sub-sequence checks); the consequences are in LocalGlobal -/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames


def n2 : Poly := [([2, 0], Kel.ofQ 1), ([0, 2], Kel.ofQ 1)]
def S16 (d : ℕ) : Poly := pow (sumsq 16 2 14) d

set_option profiler true in
theorem bs3 : eqPoly (bombSq 3 (constDP G3_0)) [([], Kel.ofQ 5)] = true := by decide +kernel
set_option profiler true in
theorem bs4 : eqPoly (bombSq 4 (constDP G4_0)) [([], Kel.ofQ (35261 / 3840))] = true := by decide +kernel
set_option profiler true in
theorem bs41 : eqPoly (bombSq 3 D41) (smul (Kel.ofQ c13) (pow n2 1)) = true := by decide +kernel
set_option profiler true in
theorem bs42 : eqPoly (bombSq 2 D42) (smul (Kel.ofQ c22) (pow n2 2)) = true := by decide +kernel
set_option profiler true in
theorem bs43 : eqPoly (bombSq 1 D43t) (smul (Kel.ofQ c6) (pow n2 3)) = true := by decide +kernel
set_option profiler true in
theorem ws3 : wsub 3 (constDP G3_0) (S16 3) = true := by decide +kernel
set_option profiler true in
theorem ws41 : wsub 3 D41 (S16 3) = true := by decide +kernel
set_option profiler true in
theorem ws42 : wsub 2 D42 (S16 2) = true := by decide +kernel
set_option profiler true in
theorem ws43 : wsub 1 D43t (S16 1) = true := by decide +kernel

end LocalGlobal
