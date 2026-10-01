import LogLean.LocalGlobA

/-! # LocalGlobE: kernel checks of the global level (per-pair Bombieri data); the consequences are in LocalGlobal -/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames

/-- per pair: Bombieri squares and weights of the degree 5 and 6 parts, and the rational bounds -/
def S4 (d : ℕ) : Poly := pow (sumsq 4 0 4) d
def pairBombOK : Bool := pairsL.all fun ij =>
  eqPoly (bombSq 5 (constDP (pijd ij.1 ij.2 5))) [([], B5sq ij.1 ij.2)]
  && wsub 5 (constDP (pijd ij.1 ij.2 5)) (S4 5)
  && decide ((B5sq ij.1 ij.2).hi aLo aHi ≤ B5b ij.1 ij.2 ^ 2) && decide (0 ≤ B5b ij.1 ij.2)
  && eqPoly (bombSq 6 (constDP (pijd ij.1 ij.2 6))) [([], B6sq ij.1 ij.2)]
  && wsub 6 (constDP (pijd ij.1 ij.2 6)) (S4 6)
  && decide ((B6sq ij.1 ij.2).hi aLo aHi ≤ B6b ij.1 ij.2 ^ 2) && decide (0 ≤ B6b ij.1 ij.2)
set_option profiler true in
theorem pairBombOK_true : pairBombOK = true := by decide +kernel
set_option profiler true in
theorem Sok4 : (Sok (S4 5) && Sok (S4 6)) = true := by decide +kernel

end LocalGlobal
