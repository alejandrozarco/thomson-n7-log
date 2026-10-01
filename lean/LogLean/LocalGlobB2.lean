import LogLean.LocalGlobA

/-! # LocalGlobB2: kernel checks of the global level (the last two F₄ chunks and the piece decomposition); the consequences are in LocalGlobal -/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames

set_option profiler true in
theorem exp4c2 : eqPoly (compose F4c2 forms) G4c2 = true := by decide +kernel
set_option profiler true in
theorem exp4c3 : eqPoly (compose F4c3 forms) G4c3 = true := by decide +kernel
set_option profiler true in
theorem exp4 : eqPoly (merge G4c0 (merge G4c1 (merge G4c2 G4c3)))
    (merge G4_0 (merge G4_1 (merge G4_2 (merge G4_3 G4_4)))) = true := by decide +kernel

end LocalGlobal
