import ThomsonGen.CertT

/-!
# Splitting the kernel checks of a packed certificate into separate declarations

A single `decide +kernel` of `TCert.checkMeta` or of `TCert.chkA/B/G` can exceed the memory budget
(Riesz s = 2 slabs: 9.2–12.8 GB).  These two lemmas let a certificate module check the same Booleans
piecewise, one kernel `decide` per block, with no change to what is checked:

* `TCert.checkMeta_of_parts`: positivity facts plus the five block-list checks;
* `hybChk_of_parts`: the Kronecker width/degree, `Fx.kev`, and one value per SOS block, then the
  (literal) sum.

New file next to `NBlk.lean`; no existing declaration is changed.  (Log port, 2026-09-30.)
-/

namespace ThomsonN7
namespace Cert

open Kron Kron.Ex

theorem TCert.checkMeta_of_parts (cf : TCert) (h1 : 0 < cf.Lam) (h2 : 0 < cf.ad) (h3 : 0 < cf.bd)
    (h4 : 0 < cf.mA) (h5 : 0 < cf.mB) (h6 : 0 < cf.mG)
    (hP : (List.range cf.K).all (fun k => (cf.blkP k).ok (cf.m k)) = true)
    (hR : (List.range cf.K).all (fun k => (cf.blkR k).ok (cf.m k)) = true)
    (hA : cf.SA.all (fun s => okF s.z.length s.B) = true)
    (hB : cf.SB.all (fun s => okF s.z.length s.B) = true)
    (hG : cf.SG.all (fun s => okF s.z.length s.B) = true) : cf.checkMeta = true := by
  unfold TCert.checkMeta
  rw [hP, hR, hA, hB, hG]
  simp [h1, h2, h3, h4, h5, h6]

theorem hybChk_of_parts (fq : ℕ → ℕ → TBlk → ℤ) (Fx : Ex) (an : ℤ) (ad : ℕ) (bn : ℤ) (bd : ℕ)
    (S : List TBlk) (W D : ℕ) (vF : ℤ) (vs : List ℤ)
    (hwf : S.all TBlk.wf = true)
    (hW : hybW Fx an ad bn bd S = W) (hD : hybD Fx an ad bn bd S = D)
    (hF : Fx.kev W D = vF)
    (hS : S.map (fun s => (gT an ad bn bd s.g).kev W D * fq W D s) = vs)
    (hsum : vF - vs.sum = 0) : hybChk fq Fx an ad bn bd S = true := by
  unfold hybChk hybVal
  rw [hW, hD, hF, hS, hwf, hsum]
  simp

end Cert
end ThomsonN7
