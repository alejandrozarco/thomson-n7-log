import LogLean.LocalGlobA

/-! # LocalGlobB: kernel checks of the global level (expansions of F₂, F₃ and the first two F₄ chunks); the consequences are in LocalGlobal -/

namespace LocalGlobal
open LocalKel LocalSP LocalBomb LocalGlobData LocalPairData LocalFrames

set_option profiler true in
theorem exp2 : eqPoly (compose F2 forms) G2_0 = true := by decide +kernel
set_option profiler true in
theorem exp3 : eqPoly (compose F3 forms) (merge G3_0 (merge G3_1 G3_2)) = true := by decide +kernel
set_option profiler true in
theorem exp4c0 : eqPoly (compose F4c0 forms) G4c0 = true := by decide +kernel
set_option profiler true in
theorem exp4c1 : eqPoly (compose F4c1 forms) G4c1 = true := by decide +kernel

end LocalGlobal
