import RieszN7.Core.LDLK
import RieszN7.Cap.Lit.Base

/-!
# `RieszN7.Cap.Lit.LDLC` — chaining row chunks of `ldlOK` (§5-rev: blocks of size ≥ 50 are checked in row chunks)

A chunk fact is `rowsOK sM sL μ L d i₀ ((M.drop i₀).take c) ((L.drop i₀).take c) = true` (one `decide +kernel` each), the
last chunk `rowsOK … i₀ (M.drop i₀) (L.drop i₀) = true`; `rowsOK_step` glues a chunk to the rest, `ldlOK_of_rows` adds
the shape/symmetry part `ldlPre`.  No kernel evaluation in the gluing.  Private, AI-written (Phase 2, CAP fork,
2026-11-08), not reviewed.
-/

namespace RieszN7.CapLit

open RieszN7.LDL RieszN7.LDLK

theorem rowsOK_step (sM sL μ : ℤ) (L : List (List ℤ)) (d : List ℤ) (M L' : List (List ℤ)) (n i0 c : ℕ)
    (hM : M.length = n) (hL : L'.length = n) (hc : i0 + c ≤ n)
    (hA : rowsOK sM sL μ L d i0 ((M.drop i0).take c) ((L'.drop i0).take c) = true)
    (hB : rowsOK sM sL μ L d (i0 + c) (M.drop (i0 + c)) (L'.drop (i0 + c)) = true) :
    rowsOK sM sL μ L d i0 (M.drop i0) (L'.drop i0) = true := by
  have hlen : ((M.drop i0).take c).length = ((L'.drop i0).take c).length := by
    simp [List.length_take, List.length_drop, hM, hL]
  have h := rowsOK_append sM sL μ L d ((M.drop i0).take c) ((L'.drop i0).take c)
    ((M.drop i0).drop c) ((L'.drop i0).drop c) i0 hlen
  rw [List.take_append_drop, List.take_append_drop] at h
  have hl : ((M.drop i0).take c).length = c := by simp [List.length_take, List.length_drop, hM]; omega
  rw [hl, List.drop_drop, List.drop_drop, hA, Bool.true_and] at h
  rw [h]
  simpa [Nat.add_comm] using hB

theorem ldlOK_of_rows (n : ℕ) (sM sL μ : ℤ) (M L : List (List ℤ)) (d : List ℤ)
    (hpre : ldlPre n sL M L d = true) (h0 : rowsOK sM sL μ L d 0 (M.drop 0) (L.drop 0) = true) :
    ldlOK n sM sL μ M L d = true := by
  rw [ldlOK_eq, hpre, Bool.true_and]
  simpa using h0

theorem lengths_of_pre {n : ℕ} {sL : ℤ} {M L : List (List ℤ)} {d : List ℤ} (h : ldlPre n sL M L d = true) :
    M.length = n ∧ L.length = n := by
  simp only [ldlPre, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hMn, hLn⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hMn, hLn⟩

end RieszN7.CapLit
