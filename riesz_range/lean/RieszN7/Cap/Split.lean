import RieszN7.Cap.TCertR

/-! `fqRed` of one reduced SOS block split into its two summands (`sqSum` part and `Δ` part), so that a
certificate module can check the largest blocks with two kernel `decide`s instead of one.  The kernel's caches
are per declaration, so this halves the peak working set of the largest decide (Phase 2 step 4: the 84-block of
the s = 11/12 cap object alone takes the module to ~8.0 GB, against a 9 GiB cap).  Definitional only.
Private working module (2026-11-07), AI-written, not reviewed. -/

namespace ThomsonN7.Cert.CapR

/-- The two summands of `fqRed` (both sides unfold to the same term). -/
theorem fqRed_split (w D : ℕ) (s : TBlkR) (a b : ℤ)
    (ha : sqSum (NBlk.vecMat ((weights w D s.z).map fun p : ℕ => (p : ℤ)) s.nb.N) s.nb.inner.d s.nb.inner.l = a)
    (hb : NBlk.dot (NBlk.vecMat (NBlk.vecMat ((weights w D s.z).map fun p : ℕ => (p : ℤ)) s.nb.N) s.nb.inner.Δ)
      (NBlk.vecMat ((weights w D s.z).map fun p : ℕ => (p : ℤ)) s.nb.N) = b) :
    fqRed w D s = a + b := by
  rw [← ha, ← hb]
  rfl

end ThomsonN7.Cert.CapR
