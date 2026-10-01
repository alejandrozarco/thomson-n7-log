import ThomsonGen.TwoRegime

/-!
# Kernel-generic pair energy and local statements (M0)

`pairEnergy φ x = ∑_{i<j} φ ⟪x i, x j⟫` for an arbitrary kernel `φ : ℝ → ℝ` of the inner product.
Everything here uses only this sum form, `O(3)`/`S₇` invariance (which hold for every `φ`), and the
kernel-free chart lemma `GV.exists_iso_close`.  The Coulomb energy is the instance `φ = Base.phi`
on unit configurations (`ThomsonGen.Coulomb`); the log energy will be `φ₀ t = -½ log (2 - 2t)`.

Generic versions of upstream `TwoRegime.LocalMinAt`, `localMinAt_of_sq`, `LocalGram`,
`localGram_of_localMinAt`, `LocalGramA`, `localGramA_of_localGram`, `local_of_windowA`, and of
`Glue.localGramA_of_le` with the window `τ₀` and the radius `(11/2) τ₀` as parameters.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `pairEnergy_comp_perm` ← `Base.coulombEnergy_comp_perm`; `Concl` ← `Glue.Concl`;
  `localMinAt_of_sq` ← `TwoRegime.localMinAt_of_sq`;
  `localGram_of_localMinAt` ← `TwoRegime.localGram_of_localMinAt`;
  `localGramA_of_localGram` ← `TwoRegime.localGramA_of_localGram`;
  `local_of_windowA` ← `TwoRegime.local_of_windowA`; `LocalGram` ← `TwoRegime.LocalGram`
  (docstring wording also from `TwoRegime.InWindow`); `LocalGramA` ← `TwoRegime.LocalGramA`;
  `pairEnergy` ← `coulombEnergy`; `pairEnergy_comp_isometry` ← `Base.coulombEnergy_comp_isometry`.
-/

open Real

namespace ThomsonGen

open ThomsonN7 ThomsonN7.Base
open scoped InnerProductSpace

/-- The pair energy `∑_{i<j} φ ⟪x i, x j⟫` for a kernel `φ` of the inner product. -/
noncomputable def pairEnergy (φ : ℝ → ℝ) {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, φ ⟪x i, x j⟫_ℝ

section Invariance

variable (φ : ℝ → ℝ)

lemma pairEnergy_comp_isometry {n : ℕ} (g : R3 ≃ₗᵢ[ℝ] R3) (x : Fin n → R3) :
    pairEnergy φ (fun i => g (x i)) = pairEnergy φ x := by
  unfold pairEnergy
  simp only [LinearIsometryEquiv.inner_map_map]

lemma pairEnergy_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → R3) :
    pairEnergy φ (fun i => x (σ i)) = pairEnergy φ x := by
  have key : ∀ y : Fin n → R3, 2 * pairEnergy φ y =
      ∑ i, ∑ j, if i = j then 0 else φ ⟪y i, y j⟫_ℝ := by
    intro y
    exact two_mul_sum_Ioi (fun i j => φ ⟪y i, y j⟫_ℝ) (fun i j => by rw [real_inner_comm])
  have h := key (fun i => x (σ i))
  have h' := key x
  have : 2 * pairEnergy φ (fun i => x (σ i)) = 2 * pairEnergy φ x := by
    rw [h, h']
    calc ∑ i, ∑ j, (if i = j then (0 : ℝ) else φ ⟪x (σ i), x (σ j)⟫_ℝ)
        = ∑ i, ∑ j, (if σ i = σ j then (0 : ℝ) else φ ⟪x (σ i), x (σ j)⟫_ℝ) := by
          simp only [σ.apply_eq_iff_eq]
      _ = ∑ i, ∑ j, (if σ i = j then (0 : ℝ) else φ ⟪x (σ i), x j⟫_ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Equiv.sum_comp σ (fun j => if σ i = j then (0 : ℝ) else φ ⟪x (σ i), x j⟫_ℝ)
      _ = ∑ i, ∑ j, (if i = j then (0 : ℝ) else φ ⟪x i, x j⟫_ℝ) :=
          Equiv.sum_comp σ (fun i => ∑ j, if i = j then (0 : ℝ) else φ ⟪x i, x j⟫_ℝ)
  linarith

/-- Orthogonal maps and relabellings together. -/
lemma pairEnergy_comp {n : ℕ} (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin n)) (x : Fin n → R3) :
    pairEnergy φ (fun a => g (x (σ a))) = pairEnergy φ x := by
  rw [pairEnergy_comp_isometry φ g (fun a => x (σ a)), pairEnergy_comp_perm φ σ x]

end Invariance

section Local

variable (φ : ℝ → ℝ)

/-- The conclusion of the `N = 7` theorem for one configuration, for the kernel `φ`. -/
def Concl (y : Fin 7 → R3) : Prop :=
  pairEnergy φ pentBipyramid ≤ pairEnergy φ y ∧
  (pairEnergy φ y = pairEnergy φ pentBipyramid →
    ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, y i = g (pentBipyramid (σ i)))

/-- The two statements of the `N = 7` theorem for the kernel `φ` (minimality and uniqueness). -/
def Main : Prop :=
  (∀ x ∈ SphereConfig 7, pairEnergy φ pentBipyramid ≤ pairEnergy φ x) ∧
  (∀ x ∈ SphereConfig 7, pairEnergy φ x = pairEnergy φ pentBipyramid →
    ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)))

theorem main_of_concl (h : ∀ y ∈ SphereConfig 7, Concl φ y) : Main φ :=
  ⟨fun x hx => (h x hx).1, fun x hx hE => (h x hx).2 hE⟩

/-- **Local statement** (sup-norm radius `d` around the labelled `P`). -/
def LocalMinAt (d : ℝ) : Prop :=
  ∀ z ∈ SphereConfig 7, (∀ i, ‖z i - pentBipyramid i‖ ≤ d) →
    pairEnergy φ pentBipyramid ≤ pairEnergy φ z ∧
    (pairEnergy φ z = pairEnergy φ pentBipyramid →
      ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, z i = g (pentBipyramid i))

/-- A local statement on the ball `∑ ‖z i - P i‖² ≤ r²` gives `LocalMinAt d` when `7 d² ≤ r²`. -/
theorem localMinAt_of_sq {r d : ℝ} (hd : 7 * d ^ 2 ≤ r ^ 2)
    (hL : ∀ z ∈ SphereConfig 7, ∑ i, ‖z i - pentBipyramid i‖ ^ 2 ≤ r ^ 2 →
      pairEnergy φ pentBipyramid ≤ pairEnergy φ z ∧
      (pairEnergy φ z = pairEnergy φ pentBipyramid →
        ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, z i = g (pentBipyramid i))) :
    LocalMinAt φ d := by
  intro z hz hzd
  apply hL z hz
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 7)), ‖z i - pentBipyramid i‖ ^ 2 ≤ d ^ 2 := by
    intro i _
    have h0 : 0 ≤ ‖z i - pentBipyramid i‖ := norm_nonneg _
    nlinarith [hzd i]
  calc ∑ i, ‖z i - pentBipyramid i‖ ^ 2 ≤ ∑ _i : Fin 7, d ^ 2 := Finset.sum_le_sum h
    _ = 7 * d ^ 2 := by simp
    _ ≤ r ^ 2 := hd

/-- **Radius `0` is free for every kernel**: `‖z i - P i‖ ≤ 0` forces `z = P`.  With the tube width
`τ₀ = 0` this is the local statement of a *sharp* certificate (exact contact sets, e.g. Riesz
`s = 2`), so such a kernel needs no local lemma. -/
theorem localMinAt_zero : LocalMinAt φ 0 := by
  intro z hz hzd
  have hzP : z = pentBipyramid := funext fun i => sub_eq_zero.1 (norm_le_zero_iff.1 (hzd i))
  subst hzP
  exact ⟨le_rfl, fun _ => ⟨LinearIsometryEquiv.refl ℝ R3, fun i => by simp⟩⟩

/-- A local statement at a radius `d` gives it at every smaller radius. -/
theorem localMinAt_mono {d d' : ℝ} (h : d' ≤ d) (hL : LocalMinAt φ d) : LocalMinAt φ d' :=
  fun z hz hzd => hL z hz fun i => (hzd i).trans h

/-- **Local statement, Gram-window form** (window `ω` of the nominal value). -/
def LocalGram (ω : ℝ → ℝ) : Prop :=
  ∀ y ∈ SphereConfig 7,
    (∀ i j, i ≠ j → |⟪y i, y j⟫_ℝ - ⟪pentBipyramid i, pentBipyramid j⟫_ℝ|
      ≤ ω ⟪pentBipyramid i, pentBipyramid j⟫_ℝ) →
    pairEnergy φ pentBipyramid ≤ pairEnergy φ y ∧
    (pairEnergy φ y = pairEnergy φ pentBipyramid →
      ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, y i = g (pentBipyramid i))

/-- A uniform Gram window `w ≤ 1/10` is controlled by the sup-norm statement at radius `(11/2) w`
(chart step `GV.exists_iso_close`, kernel-free). -/
theorem localGram_of_localMinAt {w : ℝ} (hw : w ≤ 1 / 10) (hL : LocalMinAt φ (11 / 2 * w)) :
    LocalGram φ (fun _ => w) := by
  intro y hy hG
  have hw0 : 0 ≤ w := (abs_nonneg _).trans (hG 0 1 (by decide))
  have hG' : ∀ i j, |⟪y i, y j⟫_ℝ - ⟪pentBipyramid i, pentBipyramid j⟫_ℝ| ≤ w := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hy.1 i, pent_norm i]
      simpa using hw0
    · exact hG i j h
  obtain ⟨g, hg⟩ := GV.exists_iso_close hy.1 hw hG'
  have hz : (fun a => g (y (Equiv.refl (Fin 7) a))) ∈ SphereConfig 7 :=
    sphereConfig_comp g (Equiv.refl (Fin 7)) hy
  have hE : pairEnergy φ (fun a => g (y (Equiv.refl (Fin 7) a))) = pairEnergy φ y :=
    pairEnergy_comp φ g (Equiv.refl (Fin 7)) y
  obtain ⟨h1, h2⟩ := hL _ hz (fun i => by simpa using hg i)
  refine ⟨hE ▸ h1, fun hEq => ?_⟩
  obtain ⟨g', hg'⟩ := h2 (hE.trans hEq)
  refine ⟨g'.trans g.symm, fun j => ?_⟩
  have := hg' j
  simp only [Equiv.refl_apply] at this
  simp only [LinearIsometryEquiv.trans_apply]
  rw [← this]
  simp

/-- **Local statement, asymmetric Gram-window form** (window `[t - lo t, t + hi t]`). -/
def LocalGramA (lo hi : ℝ → ℝ) : Prop :=
  ∀ y ∈ SphereConfig 7, TwoRegime.InWindow lo hi y (Equiv.refl (Fin 7)) →
    pairEnergy φ pentBipyramid ≤ pairEnergy φ y ∧
    (pairEnergy φ y = pairEnergy φ pentBipyramid →
      ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, y i = g (pentBipyramid i))

theorem localGramA_of_localGram {ω lo hi : ℝ → ℝ} (hL : LocalGram φ ω) (hlo : ∀ t, lo t ≤ ω t)
    (hhi : ∀ t, hi t ≤ ω t) : LocalGramA φ lo hi := by
  intro y hy hw
  refine hL y hy fun i j hij => ?_
  obtain ⟨h1, h2⟩ := hw i j hij
  rw [abs_le]
  have := hlo ⟪pentBipyramid i, pentBipyramid j⟫_ℝ
  have := hhi ⟪pentBipyramid i, pentBipyramid j⟫_ℝ
  simp only [Equiv.refl_apply] at h1 h2
  constructor <;> linarith

/-- The local statement transported along a relabelling. -/
theorem local_of_windowA {lo hi : ℝ → ℝ} (hL : LocalGramA φ lo hi) {y : Fin 7 → R3}
    (hy : y ∈ SphereConfig 7) (σ : Equiv.Perm (Fin 7)) (hσ : TwoRegime.InWindow lo hi y σ) :
    Concl φ y := by
  have hz : (fun a => (LinearIsometryEquiv.refl ℝ R3) (y (σ.symm a))) ∈ SphereConfig 7 :=
    sphereConfig_comp (LinearIsometryEquiv.refl ℝ R3) σ.symm hy
  have hE : pairEnergy φ (fun a => (LinearIsometryEquiv.refl ℝ R3) (y (σ.symm a)))
      = pairEnergy φ y :=
    pairEnergy_comp φ (LinearIsometryEquiv.refl ℝ R3) σ.symm y
  obtain ⟨h1, h2⟩ := hL _ hz (fun i j hij => by
    have := hσ (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h))
    simpa using this)
  refine ⟨hE ▸ h1, fun hEq => ?_⟩
  obtain ⟨g', hg'⟩ := h2 (hE.trans hEq)
  refine ⟨g', σ, fun j => ?_⟩
  have := hg' (σ j)
  simpa using this

/-- **The certified local window.**  `LocalMinAt φ ((11/2) τ₀)` with `τ₀ ≤ 1/10` gives the uniform
Gram-window statement for every `τ ≤ τ₀` (upstream `Glue.localGramA_of_le`, where `τ₀ = 1/165000`
and the local statement is the Coulomb `localMinAt_tiny`). -/
theorem localGramA_of_le {τ₀ τ : ℝ} (hτ₀ : τ₀ ≤ 1 / 10) (hL : LocalMinAt φ (11 / 2 * τ₀))
    (hτ : τ ≤ τ₀) : LocalGramA φ (fun _ => τ) (fun _ => τ) :=
  localGramA_of_localGram φ (localGram_of_localMinAt φ hτ₀ hL) (fun _ => hτ) (fun _ => hτ)

end Local

end ThomsonGen
