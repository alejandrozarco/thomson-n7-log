import LogLean.LocalGlobA

/-! # LocalGlobC: kernel checks of the global level (structured forms of the σ-graded pieces); the consequences are in LocalGlobal -/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames


set_option profiler true in
theorem piece2 : eqPoly G2_0 (smul (Kel.ofQ (1 / 2)) (qfPoly LocalCert.Hd 16 2 14 14)) = true := by decide +kernel
set_option profiler true in
theorem piece3_1 : eqPoly G3_1 (merge (mul (xk 16 0) (qfPoly (LocalGamma1.Ad 0) 16 2 14 14))
    (mul (xk 16 1) (qfPoly (LocalGamma1.Ad 1) 16 2 14 14))) = true := by decide +kernel
def gamPoly : Poly :=
  merge (mul [([2, 0], Kel.ofQ 1)] (linPoly (fun p => LocalCert.Gd p 0) 16 2 14))
    (merge (mul [([1, 1], Kel.ofQ 1)] (linPoly (fun p => LocalCert.Gd p 1) 16 2 14))
      (mul [([0, 2], Kel.ofQ 1)] (linPoly (fun p => LocalCert.Gd p 2) 16 2 14)))
set_option profiler true in
theorem piece3_2 : eqPoly G3_2 gamPoly = true := by decide +kernel
set_option profiler true in
theorem piece4_1 : eqPoly G4_1 (flatDP D41) = true := by decide +kernel
set_option profiler true in
theorem piece4_2 : eqPoly G4_2 (flatDP D42) = true := by decide +kernel
def projPoly : Poly :=
  (List.range 5).foldr (fun b acc => merge (mul (qb b) (linPoly (fun p => Kd p b) 16 2 14)) acc) []
set_option profiler true in
theorem piece4_3 : eqPoly G4_3 (merge (flatDP D43t) projPoly) = true := by decide +kernel
def n2_16 : Poly := [([2, 0] ++ List.replicate 14 0, Kel.ofQ 1), ([0, 2] ++ List.replicate 14 0, Kel.ofQ 1)]
set_option profiler true in
theorem piece4_4 : eqPoly G4_4 (smul (Kel.ofQ (13 / 40 * (25 / 4))) (pow n2_16 2)) = true := by decide +kernel


end LocalGlobal
