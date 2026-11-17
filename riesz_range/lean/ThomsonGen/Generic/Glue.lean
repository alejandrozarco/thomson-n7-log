import ThomsonGen.Generic.Energy
import ThomsonGen.Verbatim.Generic
import ThomsonGen.T4
import ThomsonGen.CertT

/-!
# Kernel-generic glue (M0)

Generic (in the kernel `φ`, the tube width `τ₀` and the local statement `LocalMinAt φ ((11/2) τ₀)`)
versions of upstream `Glue1`–`Glue4`, `Glue3`/`Bridge` (typed bound → cap/slab specifications) and
`TR_E.margin_of_threePoint_cut` (Case 1).  The proofs use only

* `pairEnergy φ = ∑_{i<j} φ ⟪x i, x j⟫` and its `O(3)`/`S₇` invariance (`Generic.Energy`);
* `⟪x i, x j⟫ < 1` for distinct unit vectors (`Base.inner_lt_one_of_ne`), `-1 ≤ ⟪x i, x j⟫`;
* the hypotheses `H ≤ φ` and the coercivity implications `φ t - H t ≤ δ → window`;
* kernel-free upstream lemmas: `T4.ring_rigid` (ring rigidity), `GV.exists_iso_close` (chart),
  `ThreePoint.typed7_bound(_lo)`, `ThreePoint.three_point_bound_cut`, `Cert.TCert.sound_lo`.

The small kernel-free glue lemmas of upstream `Glue` (`exists_minpair_perm`, `exists_cell`, `cls3`,
`TubeRigid`, `typed7_cls3`, `tcert_bound`, …) are restated here so that this module does not import
the Coulomb-specific upstream modules (`Loc2`, `Case1`, …).  Upstream `1/165000` is the parameter `τ₀`.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `concl_of_comp_perm` ← `Glue.concl_of_comp_perm`; `exists_minpair_perm` ← `Glue.exists_minpair_perm`;
  `RootedClaim` ← `Glue.RootedClaim`; `case2_of_rooted` ← `Glue.case2_of_rooted`; `exists_cell` ← `Glue.exists_cell`;
  `rooted_of_cap_slabs` ← `Glue.rooted_of_cap_slabs`; `cls3` ← `Glue.cls3`;
  `pair_facts_tube` ← `Glue.pair_facts_tube`; `slab_of_typed` ← `Glue.slab_of_typed`;
  `inWindow_of_close` ← `Glue.inWindow_of_close`; `cap_of_typed_tube` ← `Glue.cap_of_typed_tube`;
  `capSpec_sound` ← `Glue.capSpec_sound`; `SlabSpec` ← `Glue.SlabSpec`;
  `slabSpec_sound` ← `Glue.slabSpec_sound`; `H7_eq_cls3` ← `Glue.H7_eq_cls3`;
  `sum_H7_eq_sum_cls3` ← `Glue.sum_H7_eq_sum_cls3`; `typed7_cls3` ← `Glue.typed7_cls3`;
  `typed7_cls3_lo` ← `Glue.typed7_cls3_lo`; `capSpec_of_typed7` ← `Glue.capSpec_of_typed7`;
  `slabSpec_of_typed7` ← `Glue.slabSpec_of_typed7`; `tcert_bound` ← `Glue.tcert_bound`;
  `tcert_bound_cap` ← `Glue.tcert_bound_cap`; `slabSpec_of_tcert` ← `Glue.slabSpec_of_tcert`;
  `capSpec_of_tcert` ← `Glue.capSpec_of_tcert`;
  `margin_of_threePoint_cut` ← `TwoRegime.margin_of_threePoint_cut`;
  `seven_of_case2` ← `Case1.seven_of_case2`; `TubeRigid` ← `Glue.TubeRigid`;
  `Case1Claim` ← `Case1.case1_margin`; `seven_of_specs` ← `Glue.seven_of_specs`.

`exists_perm_of_ne` is upstream `Glue.exists_perm_of_ne` unchanged; it is not stored here but
regenerated into `ThomsonGen/Verbatim/Generic.lean` by `regen.sh`.
-/

open Real

namespace ThomsonGen

open ThomsonN7 ThomsonN7.Base
open scoped InnerProductSpace

/-! ### Minimal pair, rooted claim, Case 1 / Case 2 -/

section Rooted

variable (φ : ℝ → ℝ)

/-- The conclusion is invariant under relabelling. -/
lemma concl_of_comp_perm (σ : Equiv.Perm (Fin 7)) {y : Fin 7 → R3}
    (h : Concl φ (fun i => y (σ i))) : Concl φ y := by
  obtain ⟨h1, h2⟩ := h
  rw [pairEnergy_comp_perm φ σ y] at h1
  refine ⟨h1, fun hE => ?_⟩
  obtain ⟨g, τ, hg⟩ := h2 (by rw [pairEnergy_comp_perm φ σ y]; exact hE)
  refine ⟨g, σ.symm.trans τ, fun j => ?_⟩
  have := hg (σ.symm j)
  simpa using this

/-- **Normal form: the pair `(0,1)` carries the smallest inner product** (kernel-free). -/
lemma exists_minpair_perm (y : Fin 7 → R3) :
    ∃ σ : Equiv.Perm (Fin 7), ∀ i j : Fin 7, i ≠ j →
      ⟪y (σ 0), y (σ 1)⟫_ℝ ≤ ⟪y (σ i), y (σ j)⟫_ℝ := by
  classical
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun p : Fin 7 × Fin 7 => p.1 ≠ p.2)) (fun p => ⟪y p.1, y p.2⟫_ℝ)
    ⟨(0, 1), by simp⟩
  obtain ⟨σ, h5, h6⟩ := exists_perm_of_ne (Finset.mem_filter.1 hp).2
  refine ⟨σ, fun i j hij => ?_⟩
  rw [h5, h6]
  exact hmin (σ i, σ j) (by simpa using σ.injective.ne hij)

/-- **Rooted Case-2 claim**: `(0,1)` is a minimal pair with inner product `< -9/10`. -/
def RootedClaim : Prop :=
  ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ < -9 / 10 →
    (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) → Concl φ y

theorem case2_of_rooted (h : RootedClaim φ) :
    ∀ y ∈ SphereConfig 7, (∃ i j, i ≠ j ∧ ⟪y i, y j⟫_ℝ < -9 / 10) → Concl φ y := by
  rintro y hy ⟨i0, j0, hne, hlt⟩
  obtain ⟨σ, hσ⟩ := exists_minpair_perm y
  have hy' : (fun i => y (σ i)) ∈ SphereConfig 7 := by
    simpa using sphereConfig_comp (LinearIsometryEquiv.refl ℝ R3) σ hy
  refine concl_of_comp_perm φ σ (h (fun i => y (σ i)) hy' ?_ fun i j hij => hσ i j hij)
  have := hσ (σ.symm i0) (σ.symm j0) (by simpa using hne)
  simp only [Equiv.apply_symm_apply] at this
  exact lt_of_le_of_lt this hlt

/-- **Case 1**: every configuration all of whose pair inner products are `≥ -9/10` has energy
strictly above `E(P)` (upstream `Case1.case1_margin`, margin `3/10000`, for Coulomb). -/
def Case1Claim : Prop :=
  ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → (-9 / 10 : ℝ) ≤ ⟪y i, y j⟫_ℝ) →
    pairEnergy φ pentBipyramid < pairEnergy φ y

/-- Case 1 plus Case 2 give the theorem (upstream `Case1.seven_of_case2`). -/
theorem seven_of_case2 (h1 : Case1Claim φ)
    (h2 : ∀ y ∈ SphereConfig 7, (∃ i j, i ≠ j ∧ ⟪y i, y j⟫_ℝ < -9 / 10) → Concl φ y) :
    Main φ := by
  refine main_of_concl φ fun y hy => ?_
  by_cases hc : ∃ i j, i ≠ j ∧ ⟪y i, y j⟫_ℝ < -9 / 10
  · exact h2 y hy hc
  · push Not at hc
    have hm := h1 y hy fun i j hij => hc i j hij
    exact ⟨hm.le, fun hEq => absurd hEq hm.ne'⟩

theorem seven_of_rooted (h1 : Case1Claim φ) (h : RootedClaim φ) : Main φ :=
  seven_of_case2 φ h1 (case2_of_rooted φ h)

/-- Covering lemma (kernel-free): the cap `(-∞, a 0]` and the slabs `[a k, a (k+1)]`, `k < K`,
cover `(-∞, -9/10)` when `a K ≥ -9/10`. -/
lemma exists_cell (a : ℕ → ℝ) (K : ℕ) (hK : -9 / 10 ≤ a K) (t : ℝ) (ht : t < -9 / 10) :
    t ≤ a 0 ∨ ∃ k, k < K ∧ a k < t ∧ t ≤ a (k + 1) := by
  classical
  have hex : ∃ k, t ≤ a k := ⟨K, by linarith⟩
  have hk := Nat.find_spec hex
  have hkK : Nat.find hex ≤ K := Nat.find_min' hex (by linarith)
  rcases h0 : Nat.find hex with _ | k
  · left
    rw [h0] at hk
    exact hk
  · right
    refine ⟨k, by omega, ?_, by rw [h0] at hk; exact hk⟩
    have := Nat.find_min hex (m := k) (by omega)
    exact not_le.1 this

/-- **Cap + slabs give the rooted claim.** -/
theorem rooted_of_cap_slabs (a : ℕ → ℝ) (K : ℕ) (hK : -9 / 10 ≤ a K)
    (cap : ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a 0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) → Concl φ y)
    (slab : ∀ k, k < K → ∀ y ∈ SphereConfig 7, a k < ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ a (k + 1) →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      pairEnergy φ pentBipyramid < pairEnergy φ y) :
    RootedClaim φ := by
  intro y hy ht hmin
  rcases exists_cell a K hK _ ht with h0 | ⟨k, hk, h1, h2⟩
  · exact cap y hy h0 hmin
  · have := slab k hk y hy h1 h2 hmin
    exact ⟨this.le, fun hE => absurd hE this.ne'⟩

end Rooted

/-! ### Class selector and termwise facts -/

section Typed

/-- Class selector for a pair `{i, j}`: `A` for the pole pair `{0, 1}`, `B` for pole--ring pairs
and `C` for ring--ring pairs (same definition as upstream `Glue.cls3`). -/
def cls3 {α : Sort*} (A B C : α) (i j : Fin 7) : α :=
  if i.val ≤ 1 ∧ j.val ≤ 1 then A else if i.val ≤ 1 ∨ j.val ≤ 1 then B else C

variable (φ : ℝ → ℝ)

/-- Termwise facts for the pairs of a minimal-pair configuration: the class minorant lies below
`φ`, and a slack at most `δ` puts the inner product in the class predicate. -/
lemma pair_facts_tube {y : Fin 7 → R3} (hy : y ∈ SphereConfig 7) {lo hi δ : ℝ}
    (HA HB HC : ℝ → ℝ) (ZA ZB ZC : ℝ → Prop)
    (hmin : ∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ)
    (hlo : lo ≤ ⟪y 0, y 1⟫_ℝ) (hhi : ⟪y 0, y 1⟫_ℝ ≤ hi)
    (hA : ∀ t, lo ≤ t → t ≤ hi → HA t ≤ φ t ∧ (φ t - HA t ≤ δ → ZA t))
    (hB : ∀ t, lo ≤ t → t < 1 → HB t ≤ φ t ∧ (φ t - HB t ≤ δ → ZB t))
    (hC : ∀ t, lo ≤ t → t < 1 → HC t ≤ φ t ∧ (φ t - HC t ≤ δ → ZC t))
    (i j : Fin 7) (hij : i < j) :
    cls3 HA HB HC i j ⟪y i, y j⟫_ℝ ≤ φ ⟪y i, y j⟫_ℝ ∧
    (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ ≤ δ →
      cls3 ZA ZB ZC i j ⟪y i, y j⟫_ℝ) := by
  have hne : i ≠ j := hij.ne
  have hlt : ⟪y i, y j⟫_ℝ < 1 := inner_lt_one_of_ne (hy.1 i) (hy.1 j) (fun h => hne (hy.2 h))
  have hge : lo ≤ ⟪y i, y j⟫_ℝ := hlo.trans (hmin i j hne)
  have hij' : i.val < j.val := hij
  have hj7 := j.isLt
  unfold cls3
  by_cases h1 : i.val ≤ 1 ∧ j.val ≤ 1
  · have hi5 : i = 0 := Fin.ext (by simp; omega)
    have hj6 : j = 1 := Fin.ext (by simp; omega)
    subst hi5 hj6
    simpa only [h1, ite_true, and_self] using hA _ hlo hhi
  · by_cases h2 : i.val ≤ 1 ∨ j.val ≤ 1
    · simpa only [h1, h2, ite_false, ite_true] using hB _ hge hlt
    · simpa only [h1, h2, ite_false] using hC _ hge hlt

/-- **Slab claim from a typed minorant bound** (upstream `Glue.slab_of_typed`). -/
theorem slab_of_typed {lo hi e : ℝ} (HA HB HC : ℝ → ℝ) (he : pairEnergy φ pentBipyramid < e)
    (hTB : ∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
    (hA : ∀ t, lo ≤ t → t ≤ hi → HA t ≤ φ t)
    (hB : ∀ t, lo ≤ t → t < 1 → HB t ≤ φ t)
    (hC : ∀ t, lo ≤ t → t < 1 → HC t ≤ φ t) :
    ∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      pairEnergy φ pentBipyramid < pairEnergy φ y := by
  intro y hy hlo hhi hmin
  have h1 := hTB y hy hlo hhi hmin
  have h2 : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ
      ≤ pairEnergy φ y := by
    unfold pairEnergy
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    exact (pair_facts_tube φ hy (δ := 0) HA HB HC (fun _ => True) (fun _ => True)
      (fun _ => True) hmin hlo hhi
      (fun t h1 h2 => ⟨hA t h1 h2, fun _ => trivial⟩)
      (fun t h1 h2 => ⟨hB t h1 h2, fun _ => trivial⟩)
      (fun t h1 h2 => ⟨hC t h1 h2, fun _ => trivial⟩) i j (Finset.mem_Ioi.1 hj)).1
  linarith

/-! ### Tube rigidity and the near-sharp cap -/

/-- **Tube rigidity** (same statement as upstream `Glue.TubeRigid`, kernel-free). -/
def TubeRigid (τ : ℝ) : Prop :=
  ∀ y : Fin 7 → R3, (∀ i, ‖y i‖ = 1) →
    |⟪y 0, y 1⟫_ℝ + 1| ≤ τ →
    (∀ r : Fin 7, 2 ≤ r.val → |⟪y 0, y r⟫_ℝ| ≤ τ) →
    (∀ r : Fin 7, 2 ≤ r.val → |⟪y 1, y r⟫_ℝ| ≤ τ) →
    (∀ r r' : Fin 7, 2 ≤ r.val → r < r' →
      |⟪y r, y r'⟫_ℝ - c1| ≤ τ ∨ |⟪y r, y r'⟫_ℝ - c2| ≤ τ) →
    ∃ σ : Equiv.Perm (Fin 7), ∀ i j, i ≠ j →
      |⟪y i, y j⟫_ℝ - ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ| ≤ τ

/-- Ring rigidity (upstream `T4.ring_rigid`, interval arithmetic plus the 2-colouring of `K₅`)
gives `TubeRigid τ` for every `τ ≤ 1/10`. -/
theorem tubeRigid_of_le {τ : ℝ} (h : τ ≤ 1 / 10) : TubeRigid τ :=
  fun y hy h01 h0r h1r hrr => T4.ring_rigid h y hy h01 h0r h1r hrr

lemma inWindow_of_close {τ : ℝ} {y : Fin 7 → R3} {σ : Equiv.Perm (Fin 7)}
    (h : ∀ i j, i ≠ j →
      |⟪y i, y j⟫_ℝ - ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ| ≤ τ) :
    TwoRegime.InWindow (fun _ => τ) (fun _ => τ) y σ := by
  intro i j hij
  have := abs_le.1 (h i j hij)
  constructor <;> linarith [this.1, this.2]

/-- **Cap claim from a near-sharp typed minorant bound (tube route)**, generic in `φ`
(upstream `Glue.cap_of_typed_tube`): `E(P) ≤ e + δ`, slack `≤ δ` forces the `τ`-tube around the
class nodes, tube rigidity and the local window close the argument. -/
theorem cap_of_typed_tube {a0 e δ τ : ℝ} (HA HB HC : ℝ → ℝ)
    (hL : LocalGramA φ (fun _ => τ) (fun _ => τ)) (hrig : TubeRigid τ)
    (hTB : ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
    (hEδ : pairEnergy φ pentBipyramid ≤ e + δ)
    (hA : ∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ φ t ∧ (φ t - HA t ≤ δ → |t + 1| ≤ τ))
    (hB : ∀ t, -1 ≤ t → t < 1 → HB t ≤ φ t ∧ (φ t - HB t ≤ δ → |t| ≤ τ))
    (hC : ∀ t, -1 ≤ t → t < 1 → HC t ≤ φ t ∧
      (φ t - HC t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ)) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) → Concl φ y := by
  intro y hy hle hmin
  by_cases hbig : pairEnergy φ pentBipyramid < pairEnergy φ y
  · exact ⟨hbig.le, fun hE => absurd hE hbig.ne'⟩
  push Not at hbig
  have hlo : -1 ≤ ⟪y 0, y 1⟫_ℝ := neg_one_le_inner_of_unit (hy.1 0) (hy.1 1)
  have hP := hTB y hy hle hmin
  have hpf := fun i j hij => pair_facts_tube φ hy HA HB HC (fun t => |t + 1| ≤ τ)
    (fun t => |t| ≤ τ) (fun t => |t - c1| ≤ τ ∨ |t - c2| ≤ τ) hmin hlo hle hA hB hC i j hij
  have hnn : ∀ i j, j ∈ Finset.Ioi i →
      0 ≤ φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ := fun i j hj =>
    sub_nonneg.2 (hpf i j (Finset.mem_Ioi.1 hj)).1
  have hsplit : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
      (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
      = pairEnergy φ y
        - ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ := by
    unfold pairEnergy
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib ..
  have htot : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
      (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ≤ δ := by
    rw [hsplit]; linarith
  have hsl : ∀ i j, i < j →
      φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ ≤ δ := by
    intro i j hij
    have h1 : φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ
        ≤ ∑ j ∈ Finset.Ioi i, (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) :=
      Finset.single_le_sum (f := fun j => φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
        (fun j hj => hnn i j hj) (Finset.mem_Ioi.2 hij)
    have h2 : ∑ j ∈ Finset.Ioi i, (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
        ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
          (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) :=
      Finset.single_le_sum
        (f := fun i => ∑ j ∈ Finset.Ioi i,
          (φ ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ))
        (fun i _ => Finset.sum_nonneg fun j hj => hnn i j hj) (Finset.mem_univ i)
    linarith
  have hcl : ∀ i j, i < j →
      cls3 (fun t => |t + 1| ≤ τ) (fun t => |t| ≤ τ)
        (fun t => |t - c1| ≤ τ ∨ |t - c2| ≤ τ) i j ⟪y i, y j⟫_ℝ :=
    fun i j hij => (hpf i j hij).2 (hsl i j hij)
  have hAp : |⟪y 0, y 1⟫_ℝ + 1| ≤ τ := by
    have h := hcl 0 1 (by decide)
    simpa [cls3] using h
  have hBp : ∀ k : Fin 7, k.val ≤ 1 → ∀ r : Fin 7, 2 ≤ r.val → k < r → |⟪y k, y r⟫_ℝ| ≤ τ := by
    intro k hk r hr hkr
    have h := hcl k r hkr
    have h1 : ¬ (k.val ≤ 1 ∧ r.val ≤ 1) := by omega
    have h2 : k.val ≤ 1 ∨ r.val ≤ 1 := Or.inl hk
    simpa only [cls3, h1, h2, ite_false, ite_true] using h
  have hCp : ∀ r r' : Fin 7, 2 ≤ r.val → r < r' →
      |⟪y r, y r'⟫_ℝ - c1| ≤ τ ∨ |⟪y r, y r'⟫_ℝ - c2| ≤ τ := by
    intro r r' hr hrr'
    have h := hcl r r' hrr'
    have hr' : 2 ≤ r'.val := by
      have : r.val < r'.val := hrr'
      omega
    have h1 : ¬ (r.val ≤ 1 ∧ r'.val ≤ 1) := by omega
    have h2 : ¬ (r.val ≤ 1 ∨ r'.val ≤ 1) := by omega
    simpa only [cls3, h1, h2, ite_false] using h
  obtain ⟨σ, hσ⟩ := hrig y hy.1 hAp
    (fun r hr => hBp 0 (by simp) r hr (by rw [Fin.lt_def]; simp; omega))
    (fun r hr => hBp 1 (by simp) r hr (by rw [Fin.lt_def]; simp; omega)) hCp
  exact local_of_windowA φ hL hy σ (inWindow_of_close hσ)

/-! ### Specifications and assembly -/

/-- **Cap specification** for the kernel `φ` and the tube width `τ₀` (upstream `Glue.CapSpec` with
`τ₀ = 1/165000` hard-coded). -/
def CapSpec (τ₀ a0 : ℝ) : Prop :=
  ∃ (e δ τ : ℝ) (HA HB HC : ℝ → ℝ),
    τ ≤ τ₀ ∧ pairEnergy φ pentBipyramid ≤ e + δ ∧
    (∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ∧
    (∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ φ t ∧ (φ t - HA t ≤ δ → |t + 1| ≤ τ)) ∧
    (∀ t, -1 ≤ t → t < 1 → HB t ≤ φ t ∧ (φ t - HB t ≤ δ → |t| ≤ τ)) ∧
    (∀ t, -1 ≤ t → t < 1 →
      HC t ≤ φ t ∧ (φ t - HC t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ))

theorem capSpec_sound {τ₀ a0 : ℝ} (hτ₀ : τ₀ ≤ 1 / 10) (hL : LocalMinAt φ (11 / 2 * τ₀))
    (h : CapSpec φ τ₀ a0) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) → Concl φ y := by
  obtain ⟨e, δ, τ, HA, HB, HC, hτ, hEδ, hTB, hA, hB, hC⟩ := h
  exact cap_of_typed_tube φ HA HB HC (localGramA_of_le φ hτ₀ hL hτ)
    (tubeRigid_of_le (hτ.trans hτ₀)) (fun y hy hle hmin => hTB y hy hle hmin) hEδ hA hB hC

/-- **Slab specification** for the kernel `φ` (upstream `Glue.SlabSpec`). -/
def SlabSpec (lo hi : ℝ) : Prop :=
  ∃ (e : ℝ) (HA HB HC : ℝ → ℝ),
    pairEnergy φ pentBipyramid < e ∧
    (∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ∧
    (∀ t, lo ≤ t → t ≤ hi → HA t ≤ φ t) ∧
    (∀ t, lo ≤ t → t < 1 → HB t ≤ φ t) ∧
    (∀ t, lo ≤ t → t < 1 → HC t ≤ φ t)

theorem slabSpec_sound {lo hi : ℝ} (h : SlabSpec φ lo hi) :
    ∀ y ∈ SphereConfig 7, lo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ hi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      pairEnergy φ pentBipyramid < pairEnergy φ y := by
  obtain ⟨e, HA, HB, HC, he, hTB, hA, hB, hC⟩ := h
  exact slab_of_typed φ HA HB HC he (fun y hy hlo hhi hmin => hTB y hy hlo hhi hmin) hA hB hC

/-- **Generic assembly** (upstream `Glue.seven_of_specs`).  Inputs for a kernel `φ`:
a tube width `τ₀ ≤ 1/10` with the local statement `LocalMinAt φ ((11/2) τ₀)`, Case 1, a cap
specification at `a 0` and slab specifications on `[a k, a (k+1)]`, `k < K`, `a K ≥ -9/10`. -/
theorem seven_of_specs {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 1 / 10) (hL : LocalMinAt φ (11 / 2 * τ₀))
    (hcase1 : Case1Claim φ) (a : ℕ → ℝ) (K : ℕ) (hK : -9 / 10 ≤ a K)
    (hcap : CapSpec φ τ₀ (a 0)) (hslab : ∀ k, k < K → SlabSpec φ (a k) (a (k + 1))) :
    Main φ :=
  seven_of_rooted φ hcase1 (rooted_of_cap_slabs φ a K hK (capSpec_sound φ hτ₀ hL hcap)
    (fun k hk y hy hlo hhi hmin => slabSpec_sound φ (hslab k hk) y hy hlo.le hhi hmin))

/-! ### Sharp caps (exact contact, no coercivity window, no local lemma)

For a kernel whose cap certificate is exactly sharp (`e = E(P)`) and whose minorants touch `φ`
only at the nodes of `P` (`H t = φ t → t ∈ nodes`), e.g. Riesz `s = 2` with
`φ₂ - H = F·q/(2-2t)`: equality forces every `⟪y i, y j⟫` to be a node, ring rigidity applies at
`τ = 0`, and `LocalMinAt φ 0` is free (`localMinAt_zero`).  This is the case `τ₀ = δ = 0` of
`CapSpec`. -/

/-- **Sharp cap specification**: typed bound `E(P) ≤ ∑ H_cls` on the cap, minorants below `φ` with
exact contact sets `{-1}`, `{0}`, `{c1, c2}`. -/
def CapSpecSharp (a0 : ℝ) : Prop :=
  ∃ (HA HB HC : ℝ → ℝ),
    (∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      pairEnergy φ pentBipyramid ≤
        ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ∧
    (∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ φ t ∧ (HA t = φ t → t = -1)) ∧
    (∀ t, -1 ≤ t → t < 1 → HB t ≤ φ t ∧ (HB t = φ t → t = 0)) ∧
    (∀ t, -1 ≤ t → t < 1 → HC t ≤ φ t ∧ (HC t = φ t → t = c1 ∨ t = c2))

/-- A sharp cap specification is a cap specification with `τ₀ = τ = δ = 0`, `e = E(P)`. -/
theorem capSpec_of_sharp {a0 : ℝ} (h : CapSpecSharp φ a0) : CapSpec φ 0 a0 := by
  obtain ⟨HA, HB, HC, hTB, hA, hB, hC⟩ := h
  refine ⟨pairEnergy φ pentBipyramid, 0, 0, HA, HB, HC, le_rfl, by simp, hTB, ?_, ?_, ?_⟩
  · intro t h1 h2
    refine ⟨(hA t h1 h2).1, fun hs => ?_⟩
    have ht := (hA t h1 h2).2 (le_antisymm (hA t h1 h2).1 (by linarith))
    rw [ht]; norm_num
  · intro t h1 h2
    refine ⟨(hB t h1 h2).1, fun hs => ?_⟩
    have ht := (hB t h1 h2).2 (le_antisymm (hB t h1 h2).1 (by linarith))
    rw [ht]; norm_num
  · intro t h1 h2
    refine ⟨(hC t h1 h2).1, fun hs => ?_⟩
    rcases (hC t h1 h2).2 (le_antisymm (hC t h1 h2).1 (by linarith)) with ht | ht
    · left; rw [ht]; simp
    · right; rw [ht]; simp

/-- **Generic assembly, sharp-cap variant**: no tube width and no local lemma. -/
theorem seven_of_specs_sharp (hcase1 : Case1Claim φ) (a : ℕ → ℝ) (K : ℕ) (hK : -9 / 10 ≤ a K)
    (hcap : CapSpecSharp φ (a 0)) (hslab : ∀ k, k < K → SlabSpec φ (a k) (a (k + 1))) :
    Main φ :=
  seven_of_specs φ (τ₀ := 0) (by norm_num) (by rw [mul_zero]; exact localMinAt_zero φ) hcase1
    a K hK (capSpec_of_sharp φ hcap) hslab

/-! ### Typed three-point bound → specifications (kernel-free bridges, generic in `φ`) -/

lemma H7_eq_cls3 (HA HB HC : ℝ → ℝ) (i j : Fin 7) (t : ℝ) :
    ThreePoint.H7 HA HB HC i j t = cls3 HA HB HC i j t := by
  have h1 : ThreePoint.isP i ↔ i.val ≤ 1 := by unfold ThreePoint.isP; omega
  have h2 : ThreePoint.isP j ↔ j.val ≤ 1 := by unfold ThreePoint.isP; omega
  unfold ThreePoint.H7 cls3
  by_cases hi : i.val ≤ 1 <;> by_cases hj : j.val ≤ 1 <;> simp [h1, h2, hi, hj]

lemma sum_H7_eq_sum_cls3 (HA HB HC : ℝ → ℝ) (g : Fin 7 → Fin 7 → ℝ) :
    ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, ThreePoint.H7 HA HB HC i j (g i j) =
      ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j (g i j) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact H7_eq_cls3 HA HB HC i j _

/-- The typed three-point bound (`ThreePoint.typed7_bound`, kernel-free) in the `cls3` shape. -/
theorem typed7_cls3 (K : ℕ) (m : ℕ → ℕ)
    (FP FR : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hFP : ∀ k, k < K → (FP k).PosSemidef) (hFR : ∀ k, k < K → (FR k).PosSemidef)
    (HA HB HC ψBa ψCb : ℝ → ℝ) (e cal cbe alo ahi : ℝ)
    (hα : ∀ u v t, ThreePoint.GramOK u v t → alo ≤ u → u ≤ ahi →
      0 ≤ ThreePoint.lamA (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HA ψBa cal u v t)
    (hβ : ∀ u v t, ThreePoint.GramOK u v t →
      0 ≤ ThreePoint.lamB (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HB ψBa ψCb cbe u v t)
    (hγ : ∀ u v t, ThreePoint.GramOK u v t →
      0 ≤ ThreePoint.lamG (ThreePoint.Sk K m FR) HC ψCb
        ((e + 2 * ThreePoint.Sk K m FP 1 1 1 + 5 * ThreePoint.Sk K m FR 1 1 1
          - 5 * cal - 20 * cbe) / 10) u v t) :
    ∀ y ∈ SphereConfig 7, alo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ ahi →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ := by
  intro y hy hlo hhi
  rw [← sum_H7_eq_sum_cls3 HA HB HC (fun i j => ⟪y i, y j⟫_ℝ)]
  exact ThreePoint.typed7_bound K m FP FR hFP hFR HA HB HC ψBa ψCb e cal cbe alo ahi y hy.1
    ⟨hlo, hhi⟩ hα hβ hγ

/-- As `typed7_cls3`, with the lower cut `amin` on all pair inner products. -/
theorem typed7_cls3_lo (K : ℕ) (m : ℕ → ℕ)
    (FP FR : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hFP : ∀ k, k < K → (FP k).PosSemidef) (hFR : ∀ k, k < K → (FR k).PosSemidef)
    (HA HB HC ψBa ψCb : ℝ → ℝ) (e cal cbe alo ahi amin : ℝ)
    (hα : ∀ u v t, ThreePoint.GramOK u v t → alo ≤ u → u ≤ ahi → amin ≤ v → amin ≤ t →
      0 ≤ ThreePoint.lamA (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HA ψBa cal u v t)
    (hβ : ∀ u v t, ThreePoint.GramOK u v t → amin ≤ u → amin ≤ v → amin ≤ t →
      0 ≤ ThreePoint.lamB (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HB ψBa ψCb cbe u v t)
    (hγ : ∀ u v t, ThreePoint.GramOK u v t → amin ≤ u → amin ≤ v → amin ≤ t →
      0 ≤ ThreePoint.lamG (ThreePoint.Sk K m FR) HC ψCb
        ((e + 2 * ThreePoint.Sk K m FP 1 1 1 + 5 * ThreePoint.Sk K m FR 1 1 1
          - 5 * cal - 20 * cbe) / 10) u v t) :
    ∀ y ∈ SphereConfig 7, alo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ ahi →
      (∀ i j, i ≠ j → amin ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ := by
  intro y hy hlo hhi hmin
  rw [← sum_H7_eq_sum_cls3 HA HB HC (fun i j => ⟪y i, y j⟫_ℝ)]
  exact ThreePoint.typed7_bound_lo K m FP FR hFP hFR HA HB HC ψBa ψCb e cal cbe alo ahi amin y
    hy.1 hmin ⟨hlo, hhi⟩ hα hβ hγ

/-- **Cap specification from typed three-point data** (generic `Glue.capSpec_of_typed7`). -/
theorem capSpec_of_typed7 {τ₀ a0 e δ τ : ℝ} (hτ : τ ≤ τ₀) (K : ℕ) (m : ℕ → ℕ)
    (FP FR : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hFP : ∀ k, k < K → (FP k).PosSemidef) (hFR : ∀ k, k < K → (FR k).PosSemidef)
    (HA HB HC ψBa ψCb : ℝ → ℝ) (cal cbe : ℝ)
    (hα : ∀ u v t, ThreePoint.GramOK u v t → -1 ≤ u → u ≤ a0 →
      0 ≤ ThreePoint.lamA (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HA ψBa cal u v t)
    (hβ : ∀ u v t, ThreePoint.GramOK u v t →
      0 ≤ ThreePoint.lamB (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HB ψBa ψCb cbe u v t)
    (hγ : ∀ u v t, ThreePoint.GramOK u v t →
      0 ≤ ThreePoint.lamG (ThreePoint.Sk K m FR) HC ψCb
        ((e + 2 * ThreePoint.Sk K m FP 1 1 1 + 5 * ThreePoint.Sk K m FR 1 1 1
          - 5 * cal - 20 * cbe) / 10) u v t)
    (hEδ : pairEnergy φ pentBipyramid ≤ e + δ)
    (hA : ∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ φ t ∧ (φ t - HA t ≤ δ → |t + 1| ≤ τ))
    (hB : ∀ t, -1 ≤ t → t < 1 → HB t ≤ φ t ∧ (φ t - HB t ≤ δ → |t| ≤ τ))
    (hC : ∀ t, -1 ≤ t → t < 1 →
      HC t ≤ φ t ∧ (φ t - HC t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ)) :
    CapSpec φ τ₀ a0 :=
  ⟨e, δ, τ, HA, HB, HC, hτ, hEδ, fun y hy hle _ =>
    typed7_cls3 K m FP FR hFP hFR HA HB HC ψBa ψCb e cal cbe (-1) a0 hα hβ hγ y hy
      (neg_one_le_inner_of_unit (hy.1 0) (hy.1 1)) hle, hA, hB, hC⟩

/-- **Slab specification from typed three-point data** (generic `Glue.slabSpec_of_typed7`). -/
theorem slabSpec_of_typed7 {lo hi e : ℝ} (K : ℕ) (m : ℕ → ℕ)
    (FP FR : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (hFP : ∀ k, k < K → (FP k).PosSemidef) (hFR : ∀ k, k < K → (FR k).PosSemidef)
    (HA HB HC ψBa ψCb : ℝ → ℝ) (cal cbe : ℝ) (he : pairEnergy φ pentBipyramid < e)
    (hα : ∀ u v t, ThreePoint.GramOK u v t → lo ≤ u → u ≤ hi → lo ≤ v → lo ≤ t →
      0 ≤ ThreePoint.lamA (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HA ψBa cal u v t)
    (hβ : ∀ u v t, ThreePoint.GramOK u v t → lo ≤ u → lo ≤ v → lo ≤ t →
      0 ≤ ThreePoint.lamB (ThreePoint.Sk K m FP) (ThreePoint.Sk K m FR) HB ψBa ψCb cbe u v t)
    (hγ : ∀ u v t, ThreePoint.GramOK u v t → lo ≤ u → lo ≤ v → lo ≤ t →
      0 ≤ ThreePoint.lamG (ThreePoint.Sk K m FR) HC ψCb
        ((e + 2 * ThreePoint.Sk K m FP 1 1 1 + 5 * ThreePoint.Sk K m FR 1 1 1
          - 5 * cal - 20 * cbe) / 10) u v t)
    (hA : ∀ t, lo ≤ t → t ≤ hi → HA t ≤ φ t)
    (hB : ∀ t, lo ≤ t → t < 1 → HB t ≤ φ t)
    (hC : ∀ t, lo ≤ t → t < 1 → HC t ≤ φ t) :
    SlabSpec φ lo hi :=
  ⟨e, HA, HB, HC, he, fun y hy hlo hhi hmin =>
    typed7_cls3_lo K m FP FR hFP hFR HA HB HC ψBa ψCb e cal cbe lo hi lo hα hβ hγ y hy hlo hhi
      (fun i j hij => hlo.trans (hmin i j hij)), hA, hB, hC⟩

/-- The bound of `TCert.sound_lo` (a packed certificate whose four boolean checks pass) in the
shape of the `cls3` sums (upstream `Glue.tcert_bound`). -/
theorem tcert_bound (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true) :
    ∀ y ∈ SphereConfig 7, cf.alo ≤ ⟪y 0, y 1⟫_ℝ → ⟪y 0, y 1⟫_ℝ ≤ cf.ahi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      cf.ef ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 cf.HAf cf.HBf cf.HCf i j ⟪y i, y j⟫_ℝ := by
  intro y hy hlo hhi hmin
  rw [← sum_H7_eq_sum_cls3 cf.HAf cf.HBf cf.HCf (fun i j => ⟪y i, y j⟫_ℝ)]
  exact Cert.TCert.sound_lo cf hm hA hB hG y hy.1 (fun i j hij => hlo.trans (hmin i j hij))
    ⟨hlo, hhi⟩

theorem tcert_bound_cap (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ cf.ahi →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      cf.ef ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 cf.HAf cf.HBf cf.HCf i j ⟪y i, y j⟫_ℝ := by
  intro y hy hhi hmin
  refine tcert_bound cf hm hA hB hG y hy ?_ hhi hmin
  rw [halo]
  exact neg_one_le_inner_of_unit (hy.1 0) (hy.1 1)

/-- **Slab specification from a packed certificate** (generic `Glue.slabSpec_of_tcert`): the
energy comparison `E_φ(P) < ef` and the one-dimensional facts `H ≤ φ` are the kernel inputs. -/
theorem slabSpec_of_tcert (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (hE : pairEnergy φ pentBipyramid < cf.ef)
    (hHA : ∀ t, cf.alo ≤ t → t ≤ cf.ahi → cf.HAf t ≤ φ t)
    (hHB : ∀ t, cf.alo ≤ t → t < 1 → cf.HBf t ≤ φ t)
    (hHC : ∀ t, cf.alo ≤ t → t < 1 → cf.HCf t ≤ φ t) :
    SlabSpec φ cf.alo cf.ahi :=
  ⟨cf.ef, cf.HAf, cf.HBf, cf.HCf, hE, tcert_bound cf hm hA hB hG, hHA, hHB, hHC⟩

/-- **Cap specification from a packed certificate** (generic `Glue.capSpec_of_tcert`): the
kernel inputs are `E_φ(P) ≤ ef + δ` and the coercive one-dimensional facts with window `τ ≤ τ₀`. -/
theorem capSpec_of_tcert (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) {τ₀ δ τ : ℝ} (hτ : τ ≤ τ₀)
    (hE : pairEnergy φ pentBipyramid ≤ cf.ef + δ)
    (hHA : ∀ t, -1 ≤ t → t ≤ cf.ahi → cf.HAf t ≤ φ t ∧ (φ t - cf.HAf t ≤ δ → |t + 1| ≤ τ))
    (hHB : ∀ t, -1 ≤ t → t < 1 → cf.HBf t ≤ φ t ∧ (φ t - cf.HBf t ≤ δ → |t| ≤ τ))
    (hHC : ∀ t, -1 ≤ t → t < 1 →
      cf.HCf t ≤ φ t ∧ (φ t - cf.HCf t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ)) :
    CapSpec φ τ₀ cf.ahi :=
  ⟨cf.ef, δ, τ, cf.HAf, cf.HBf, cf.HCf, hτ, hE, tcert_bound_cap cf hm hA hB hG halo,
    hHA, hHB, hHC⟩

/-- **Sharp cap specification from a packed certificate** (`E_φ(P) ≤ ef`, exact contact sets). -/
theorem capSpecSharp_of_tcert (cf : Cert.TCert) (hm : cf.checkMeta = true)
    (hA : cf.chkA = true) (hB : cf.chkB = true) (hG : cf.chkG = true)
    (halo : cf.alo = -1) (hE : pairEnergy φ pentBipyramid ≤ cf.ef)
    (hHA : ∀ t, -1 ≤ t → t ≤ cf.ahi → cf.HAf t ≤ φ t ∧ (cf.HAf t = φ t → t = -1))
    (hHB : ∀ t, -1 ≤ t → t < 1 → cf.HBf t ≤ φ t ∧ (cf.HBf t = φ t → t = 0))
    (hHC : ∀ t, -1 ≤ t → t < 1 → cf.HCf t ≤ φ t ∧ (cf.HCf t = φ t → t = c1 ∨ t = c2)) :
    CapSpecSharp φ cf.ahi :=
  ⟨cf.HAf, cf.HBf, cf.HCf,
    fun y hy hle hmin => hE.trans (tcert_bound_cap cf hm hA hB hG halo y hy hle hmin),
    hHA, hHB, hHC⟩

end Typed

/-! ### Case 1 from a cut three-point certificate -/

section Case1

variable (φ : ℝ → ℝ)

/-- **Margin on the cut** (generic `TwoRegime.margin_of_threePoint_cut`): a cut three-point
certificate and a one-dimensional minorant `H ≤ φ` on `[a, 1)` give `E(y) ≥ E(P) + η` for every
configuration all of whose pair inner products are `≥ a`. -/
theorem margin_of_threePoint_cut {H : ℝ → ℝ} {a η : ℝ} (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (hF : ∀ k, k < K → (F k).PosSemidef)
    (hpt : ∀ u v t : ℝ, ThreePoint.GramOK u v t → a ≤ u → a ≤ v → a ≤ t →
      ∑ k ∈ Finset.range K, ThreePoint.matDot (F k) (ThreePoint.Rk 7 (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - (pairEnergy φ pentBipyramid + η) / ((Nat.choose 7 2 : ℕ) : ℝ))
    (hH : ∀ t : ℝ, a ≤ t → t < 1 → H t ≤ φ t) :
    ∀ y ∈ SphereConfig 7, (∀ i j, i ≠ j → a ≤ ⟪y i, y j⟫_ℝ) →
      pairEnergy φ pentBipyramid + η ≤ pairEnergy φ y := by
  intro y hy hya
  have h2 : ∑ i, ∑ j ∈ Finset.Ioi i, H ⟪y i, y j⟫_ℝ ≤ pairEnergy φ y := by
    unfold pairEnergy
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.1 hj).ne
    exact hH _ (hya i j hij) (inner_lt_one_of_ne (hy.1 i) (hy.1 j) (fun h => hij (hy.2 h)))
  have h4 := ThreePoint.three_point_bound_cut (by norm_num) a K m F hF H
    (pairEnergy φ pentBipyramid + η) hpt y hy.1 hya
  linarith

/-- Case 1 (cut `-9/10`) from a cut three-point certificate with a positive margin. -/
theorem case1Claim_of_threePoint_cut {H : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (hF : ∀ k, k < K → (F k).PosSemidef)
    (hpt : ∀ u v t : ℝ, ThreePoint.GramOK u v t → -9 / 10 ≤ u → -9 / 10 ≤ v → -9 / 10 ≤ t →
      ∑ k ∈ Finset.range K, ThreePoint.matDot (F k) (ThreePoint.Rk 7 (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - (pairEnergy φ pentBipyramid + η) / ((Nat.choose 7 2 : ℕ) : ℝ))
    (hH : ∀ t : ℝ, -9 / 10 ≤ t → t < 1 → H t ≤ φ t) :
    Case1Claim φ := by
  intro y hy hya
  have := margin_of_threePoint_cut φ (a := -9 / 10) K m F hF hpt hH y hy hya
  linarith

end Case1

end ThomsonGen
