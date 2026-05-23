import Mathlib
import SimplicialLatentGeometry.Geometry.Common

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Geometry / Sphere — $S^{d-1}$ Čech instance (Paper 2)

The second concrete instance of `HomogeneousGeometricModel`. Implements detection on the
unit sphere $S^{d-1} \subset \mathbb{R}^d$ with uniform measure, using Čech fill (existential
common-ball) rather than Rips clique.

Strategic context (see `wiki/decisions.md` session-63 entries + local
`my_theorems/paper2_sphere_scoping.md`):

* On $\ell_\infty$ torus, Helly-2 collapses Čech to Rips and gives no dimensional barrier
  in the matched fixed-$p$ regime (Paper 1: $\text{geomCov} \to p^3(1-p)^3 > 0$).
* On $S^{d-1}$, Helly-$d$ preserves the Čech-Rips gap; concentration of measure forces
  caps to nearly hemispheres at matched $p$, but the existential Čech fill saturates
  ($q_{\text{Čech}} \to 1$) while Rips fill collapses ($q_{\text{Rips}} \to p^3$).
* The signal $\text{geomCov}_{\text{Čech}} \sim p^3 (1 - q_{\text{Čech}})$ vanishes
  super-exponentially: $1 - q_{\text{Čech}} \sim (3 z_p^2 / d)^{(d-2)/2}$ via the joint
  Gram-entry density $\propto (\det G)^{(d-4)/2}$ singularity at $\det G = 0$.
* Detection threshold: $d^*(n, p) = 3 \log n / \log\log n$, sub-logarithmic.

## Layout (this file)

* `SphereSetting` — dimension index `d : ℕ`, $d \ge 2$.
* `uniformOnSphere d` — uniform probability measure on $S^{d-1}$ (via Haar / $SO(d)$).
* `sphereEdge` — pairwise inner-product threshold.
* `matchedCap p d` — the cap half-angle realizing edge probability $p$.
* `sphereCech` — Čech fill (existential common cap).
* Aristotle targets: cap volume closed form, Gram-density tail asymptotic, $\text{geomCov}$
  closed form, and the `HomogeneousGeometricModel` instance hookup.

## Status

S1 skeleton (Phase A6 in the OQ-18 plan). All proof bodies are `sorry` pending
Aristotle dispatch. The asymptotic claims are stated against the math-precheck verdict
(session 63) and not the original audit's $\log n$ headline.
-/

namespace SphereGeometry

open MeasureTheory
open scoped Pointwise

/-! ## Point space: unit sphere in $\mathbb{R}^d$ -/

/-- The unit sphere $S^{d-1} \subset \mathbb{R}^d$, as the subtype carried by mathlib's
    `Metric.sphere`. Concretised 2026-05-19 to use the standard mathlib sphere instead of
    `{x // ‖x‖ = 1}` so that the radial-pushforward `Measure.toSphere` (HaarToSphere.lean)
    applies directly. -/
abbrev SpherePoint (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- Measurable-space structure inherited from `EuclideanSpace`. -/
instance (d : ℕ) : MeasurableSpace (SpherePoint d) := Subtype.instMeasurableSpace

/-- Uniform probability measure on $S^{d-1}$. Built from the standard Lebesgue measure on
    `EuclideanSpace ℝ (Fin d)` via mathlib's `Measure.toSphere` (radial pushforward; see
    `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`), then normalized to total
    mass 1. For `d ≤ 1` this is the zero measure (the underlying `toSphere` vanishes,
    so the normalization factor `μ univ⁻¹` is `⊤⁻¹ = 0`); consumers only quantify over
    `ValidRegime p d` which forces `5 ≤ d`. -/
noncomputable def uniformOnSphere (d : ℕ) : Measure (SpherePoint d) :=
  let μ : Measure (SpherePoint d) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  (μ Set.univ)⁻¹ • μ

/-- The uniform measure is a probability measure whenever the sphere is non-trivial,
    i.e. `2 ≤ d`. Derives from the finite-measure instance on `Measure.toSphere` plus
    `toSphere_apply_univ`'s non-zero ball volume formula (`dim * vol(ball 0 1)`). -/
instance uniformOnSphere_isProb (d : ℕ) [hd : Fact (2 ≤ d)] :
    IsProbabilityMeasure (uniformOnSphere d) := by
  constructor
  unfold uniformOnSphere
  have h_dim_pos : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    exact lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hd.out
  haveI h_nontriv : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.finrank_pos_iff.mp h_dim_pos
  have h_ne : (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have h_finite :
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ ≠ ⊤ :=
    (measure_lt_top _ _).ne
  have h_pos :
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ ≠ 0 := by
    rwa [Measure.measure_univ_ne_zero]
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h_pos h_finite

/-- Uniform-sphere as `Fact (2 ≤ d)` is the natural form for typeclass synthesis; expose a
    direct version with explicit hypothesis for backward compatibility with the rest of
    this file (which threads `hd : 2 ≤ d` as an ordinary argument). -/
lemma uniformOnSphere_isProb' (d : ℕ) (hd : 2 ≤ d) :
    IsProbabilityMeasure (uniformOnSphere d) :=
  @uniformOnSphere_isProb d ⟨hd⟩

/-- The uniform sphere measure is always zero-or-probability (it equals the
    normalized `Measure.toSphere`; if the underlying total mass is 0, the
    normalization `0⁻¹ • 0 = ⊤ • 0 = 0`, otherwise mass is `c⁻¹ * c = 1`).
    Concretised 2026-05-19 to replace the axiomatic ENNReal arithmetic chain. -/
instance uniformOnSphere_isZeroOrProb (d : ℕ) :
    IsZeroOrProbabilityMeasure (uniformOnSphere d) := by
  unfold uniformOnSphere
  set μ : Measure (SpherePoint d) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hμ_def
  refine ⟨?_⟩
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases h : μ Set.univ = 0
  · left; simp [h]
  · right
    have h_finite : μ Set.univ ≠ ⊤ := (measure_lt_top μ Set.univ).ne
    exact ENNReal.inv_mul_cancel h h_finite

/-- **No atoms on `Measure.toSphere`** (for `d ≥ 2`).
    A singleton `{x}` on the sphere pulls back via `toSphere_apply'` to
    `dim · vol(Ioo 0 1 • {x.val})`. The latter set is contained in the 1-dimensional
    submodule `ℝ ∙ x.val`, which is a strict subspace whenever the ambient dimension
    `d ≥ 2`. By `addHaar_submodule`, strict subspaces have Lebesgue measure zero.
    Concretised 2026-05-19 to discharge `capProb_one`, `capProb_continuous`,
    `matchedCos_exists` (see wiki/INDEX.md session 78). -/
instance toSphere_noAtoms (d : ℕ) [hd : Fact (2 ≤ d)] :
    MeasureTheory.NoAtoms
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) := by
  refine ⟨fun x => ?_⟩
  have hd2 : (2 : ℕ) ≤ d := hd.out
  -- Step 1: rewrite singleton-measure via `toSphere_apply'`.
  have h_meas : MeasurableSet ({x} : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    measurableSet_singleton x
  rw [Measure.toSphere_apply' _ h_meas]
  -- Goal: `dim * volume (Ioo 0 1 • ((↑) '' {x})) = 0`.
  -- It suffices to show the inner volume is 0.
  have h_image : ((↑) : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d)) '' {x} = {(x : EuclideanSpace ℝ (Fin d))} := by
    simp
  rw [h_image]
  -- Now: `dim * volume (Ioo 0 1 • {x.val}) = 0`.
  -- Show: `Ioo 0 1 • {x.val} ⊆ Submodule.span ℝ {x.val}`.
  have h_sub :
      (Set.Ioo (0 : ℝ) 1 • {(x : EuclideanSpace ℝ (Fin d))} : Set _) ⊆
        (Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))} : Set _) := by
    intro y hy
    rcases hy with ⟨r, _hr, v, hv, rfl⟩
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  -- The submodule `ℝ ∙ x.val` is strict (has finrank 1 < d).
  have hx_ne : (x : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    intro hzero
    have hx_norm : ‖(x : EuclideanSpace ℝ (Fin d))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp x.2
    rw [hzero, norm_zero] at hx_norm
    exact zero_ne_one hx_norm
  have h_finrank_span : Module.finrank ℝ
      (Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))}) = 1 :=
    finrank_span_singleton hx_ne
  have h_finrank_amb :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have h_strict :
      Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))} ≠ ⊤ := by
    intro htop
    -- If span = ⊤, then finrank = d, contradicting finrank_span_singleton = 1 and d ≥ 2.
    have hcong : Module.finrank ℝ
        (Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))}) =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      rw [htop]; exact finrank_top _ _
    rw [h_finrank_span, h_finrank_amb] at hcong
    omega
  -- `volume` is an additive Haar measure on `EuclideanSpace`; strict submodules have measure 0.
  have h_submodule_zero :
      (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))}) = 0 :=
    Measure.addHaar_submodule (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (Submodule.span ℝ {(x : EuclideanSpace ℝ (Fin d))}) h_strict
  have h_inner_zero :
      (volume : Measure (EuclideanSpace ℝ (Fin d)))
        (Set.Ioo (0 : ℝ) 1 • {(x : EuclideanSpace ℝ (Fin d))}) = 0 :=
    measure_mono_null h_sub h_submodule_zero
  rw [h_inner_zero, mul_zero]

/-- The uniform measure on the sphere has no atoms (for `d ≥ 2`).
    Follows from `toSphere_noAtoms` and the fact that scalar-multiplying a measure
    preserves the no-atoms property. -/
instance uniformOnSphere_noAtoms (d : ℕ) [hd : Fact (2 ≤ d)] :
    MeasureTheory.NoAtoms (uniformOnSphere d) := by
  refine ⟨fun x => ?_⟩
  unfold uniformOnSphere
  rw [Measure.smul_apply, smul_eq_mul]
  haveI : MeasureTheory.NoAtoms
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) :=
    toSphere_noAtoms d
  rw [MeasureTheory.measure_singleton, mul_zero]

/-! ## Edge and fill predicates -/

/-- Two points on the sphere are within angular distance $\theta$ iff their Euclidean
    inner product is at least $\cos\theta$. We parameterize by `r := cos θ` directly. -/
def sphereEdge {d : ℕ} (r : ℝ) (x y : SpherePoint d) : Prop :=
  inner ℝ x.val y.val ≥ r

/-- Čech fill at scale `r`: three points lie in a common spherical cap of half-angle
    `arccos r`, i.e., there exists a center `z ∈ S^{d-1}` with all three inner products
    `⟨z, x_i⟩ ≥ r`. -/
def sphereCechFill {d : ℕ} (r : ℝ) (x₁ x₂ x₃ : SpherePoint d) : Prop :=
  ∃ z : SpherePoint d,
    inner ℝ z.val x₁.val ≥ r ∧ inner ℝ z.val x₂.val ≥ r ∧ inner ℝ z.val x₃.val ≥ r

/-! ## Cap probability — concrete quantity

The uniform probability that a single point lies in a spherical cap of cosine threshold
`r ∈ [-1, 1]` centred at a fixed pole. In dimension `d ≥ 2` this is
`(1/2) · I_{1-r²}((d-1)/2, 1/2)` when `r ≥ 0` by the standard incomplete-beta formula
(Li 2011, Eq. (3)).

Concretised 2026-05-19 as the `uniformOnSphere`-measure of the half-space cap at the
canonical pole `e₀ = EuclideanSpace.single 0 1` (well-defined whenever `d ≥ 1`; in
the trivial case `d = 0` the function returns `0`). -/

/-- The canonical pole `e₀ ∈ S^{d-1}` (the first basis vector), packaged as the
    underlying ambient vector in `EuclideanSpace ℝ (Fin d)`. For `d = 0` this is
    the zero vector (does not lie on the sphere, but `capProb` carries a guard
    on `0 < d` that ensures only the `d ≥ 1` branch is ever invoked). -/
noncomputable def spherePoleVec (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : 0 < d then EuclideanSpace.single (⟨0, h⟩ : Fin d) (1 : ℝ) else 0

/-- Cap probability: uniform measure of `{x : S^{d-1} | inner pole x ≥ r}`,
    converted to `ℝ`. Returns `0` in the degenerate case `d = 0`. -/
noncomputable def capProb (d : ℕ) (r : ℝ) : ℝ :=
  (uniformOnSphere d
    {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ r}).toReal

/-- Cap probability is in `[0, 1]` for any threshold and dimension.
    The lower bound is immediate (`.toReal` of an ENNReal is nonneg); the upper
    bound uses the unconditional `IsZeroOrProbabilityMeasure` instance on
    `uniformOnSphere d` (`uniformOnSphere_isZeroOrProb`). -/
theorem capProb_mem_unitInterval (d : ℕ) (r : ℝ) :
    0 ≤ capProb d r ∧ capProb d r ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  unfold capProb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (ENNReal.ofReal_one.symm ▸ prob_le_one)

/-- Monotone in the threshold: a higher cosine threshold gives a smaller cap.
    Follows from set inclusion `{inner ≥ r'} ⊆ {inner ≥ r}` when `r ≤ r'` and
    `Measure.toReal` monotone on a finite measure (the uniform sphere measure
    is always sub-probability). -/
theorem capProb_antitone (d : ℕ) : Antitone (capProb d) := by
  intro r r' hrr'
  unfold capProb
  have h_sub :
      {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ r'} ⊆
      {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ r} := by
    intro x hx
    exact le_trans hrr' hx
  have h_top :
      uniformOnSphere d
        {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ r} ≠ ⊤ := by
    exact (measure_lt_top _ _).ne
  exact ENNReal.toReal_mono h_top (measure_mono h_sub)

/-- Pole vector has norm 1 (for `d ≥ 1`). -/
private lemma norm_spherePoleVec (d : ℕ) (hd : 1 ≤ d) :
    ‖spherePoleVec d‖ = 1 := by
  have hd' : 0 < d := hd
  unfold spherePoleVec
  rw [dif_pos hd']
  simp

/-- For `d ≥ 1`, any sphere point's inner product with the pole is at most 1 in absolute value. -/
private lemma abs_inner_spherePoleVec_le_one (d : ℕ) (hd : 1 ≤ d)
    (x : SpherePoint d) : |inner ℝ (spherePoleVec d) x.val| ≤ 1 := by
  have hx : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have h_pole : ‖spherePoleVec d‖ = 1 := norm_spherePoleVec d hd
  have := abs_real_inner_le_norm (spherePoleVec d) x.val
  rw [h_pole, hx, one_mul] at this
  exact this

/-- For `d ≥ 1`, the inner product `inner pole x.val` lies in `[-1, 1]`. -/
private lemma neg_one_le_inner_spherePoleVec (d : ℕ) (hd : 1 ≤ d)
    (x : SpherePoint d) : -1 ≤ inner ℝ (spherePoleVec d) x.val := by
  have h := abs_inner_spherePoleVec_le_one d hd x
  exact (abs_le.mp h).1

/-- **Endpoint `r = -1`: cap is the whole sphere.**
    For `d ≥ 2` the underlying measure is a probability measure, and Cauchy-Schwarz
    gives `inner pole x.val ≥ -1` for every `x : S^{d-1}`, so the cap set is `Set.univ`.
    Concretised 2026-05-19 (was axiomatic). -/
theorem capProb_neg_one (d : ℕ) (hd : 2 ≤ d) : capProb d (-1) = 1 := by
  unfold capProb
  have h_set :
      {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ -1} = Set.univ := by
    ext x
    refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
    exact neg_one_le_inner_spherePoleVec d (by linarith) x
  rw [h_set]
  haveI := uniformOnSphere_isProb' d hd
  simp

/-- **Endpoint `r = 1`: cap is the single pole point, measure-zero.**
    By Cauchy-Schwarz equality on unit vectors, `{x : S^{d-1} | ⟨pole, x⟩ ≥ 1}` is the
    singleton `{pole}`. Combined with `uniformOnSphere_noAtoms` (concretised 2026-05-19
    via radial pushforward + `addHaar_submodule`), the uniform measure of any singleton
    is zero. Concretised 2026-05-19 (was axiomatic). -/
theorem capProb_one (d : ℕ) (hd : 2 ≤ d) : capProb d 1 = 0 := by
  unfold capProb
  haveI : Fact (2 ≤ d) := ⟨hd⟩
  -- Step 1: pole vector has norm 1.
  have h_pole_norm : ‖spherePoleVec d‖ = 1 := norm_spherePoleVec d (by linarith)
  -- Step 2: the cap set is contained in the singleton `{pole}` (as a sphere point).
  have h_pole_mem : spherePoleVec d ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_sphere_zero_iff_norm]; exact h_pole_norm
  let polePt : SpherePoint d := ⟨spherePoleVec d, h_pole_mem⟩
  have h_set_sub :
      {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ 1} ⊆ {polePt} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hx_norm : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
    -- Cauchy-Schwarz: |⟨pole, x.val⟩| ≤ 1, with hx: ⟨pole, x.val⟩ ≥ 1.
    have h_le : inner ℝ (spherePoleVec d) x.val ≤ 1 := by
      have := abs_inner_spherePoleVec_le_one d (by linarith) x
      exact (abs_le.mp this).2
    have h_eq : inner ℝ (spherePoleVec d) x.val = 1 := le_antisymm h_le hx
    -- inner_eq_norm_mul_iff_real with both norms 1 gives x.val = pole.
    have h_eq' : inner ℝ (spherePoleVec d) x.val =
        ‖spherePoleVec d‖ * ‖x.val‖ := by
      rw [h_pole_norm, hx_norm, h_eq, mul_one]
    have h_smul : ‖x.val‖ • spherePoleVec d = ‖spherePoleVec d‖ • x.val :=
      (inner_eq_norm_mul_iff_real (x := spherePoleVec d) (y := x.val)).mp h_eq'
    rw [h_pole_norm, hx_norm, one_smul, one_smul] at h_smul
    -- So `spherePoleVec d = x.val`, i.e. x = polePt.
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact h_smul.symm
  -- Step 3: measure of singleton is zero (NoAtoms).
  have h_singleton :
      uniformOnSphere d ({polePt} : Set (SpherePoint d)) = 0 :=
    MeasureTheory.measure_singleton (μ := uniformOnSphere d) polePt
  have h_le := measure_mono (μ := uniformOnSphere d) h_set_sub
  have h_zero :
      uniformOnSphere d
        {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ 1} = 0 := by
    apply le_antisymm
    · rw [h_singleton] at h_le; exact h_le
    · exact zero_le _
  rw [h_zero]; simp

/-
The radial cone `Ioo 0 1 • (coe '' {x | ⟨pole, x⟩ = r})` is contained in
    `{w | ⟨pole, w⟩ = r · ‖w‖}`.
-/
private lemma cone_subset_inner_eq_mul_norm (d : ℕ) (r : ℝ) :
    Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val = r}) ⊆
    {w : EuclideanSpace ℝ (Fin d) | inner ℝ (spherePoleVec d) w = r * ‖w‖} := by
  intro w hw; obtain ⟨ t, ht, x, hx, rfl ⟩ := hw; simp_all +decide [ inner_smul_right ] ;
  rw [ norm_smul, Real.norm_of_nonneg ht.1.le, hx.2, mul_one, mul_comm ]

/-
Lebesgue measure of `{w | ⟨pole, w⟩ = c · ‖w‖}` is zero for any `c : ℝ`
    in dimension `d ≥ 2`.  This is a codimension-1 cone (the zero set of a
    smooth function with non-vanishing gradient away from the origin).
-/
set_option maxHeartbeats 800000 in
private lemma volume_inner_eq_mul_norm_zero (d : ℕ) (hd : 2 ≤ d) (c : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
      {w : EuclideanSpace ℝ (Fin d) | inner ℝ (spherePoleVec d) w = c * ‖w‖} = 0 := by
  by_cases hc : c = 0 ∨ |c| > 1 ∨ |c| = 1;
  · rcases hc with ( rfl | hc | hc );
    · have h_submodule_zero : (volume : Measure (EuclideanSpace ℝ (Fin d))) (Submodule.span ℝ {(spherePoleVec d : EuclideanSpace ℝ (Fin d))} : Submodule ℝ (EuclideanSpace ℝ (Fin d))).orthogonal = 0 := by
        have h_orthogonal_submodule : (Submodule.span ℝ {(spherePoleVec d : EuclideanSpace ℝ (Fin d))} : Submodule ℝ (EuclideanSpace ℝ (Fin d))).orthogonal ≠ ⊤ := by
          simp +decide [ Submodule.eq_top_iff', Submodule.mem_orthogonal ];
          refine' ⟨ spherePoleVec d, spherePoleVec d, _, _ ⟩ <;> norm_num [ spherePoleVec ];
          linarith;
        convert Measure.addHaar_submodule _ _ h_orthogonal_submodule using 1;
        infer_instance;
      convert h_submodule_zero using 2 ; ext ; simp +decide [ Submodule.mem_orthogonal_singleton_iff_inner_right ];
    · have h_zero : ∀ w : EuclideanSpace ℝ (Fin d), inner ℝ (spherePoleVec d) w = c * ‖w‖ → w = 0 := by
        intro w hw
        have h_norm : |inner ℝ (spherePoleVec d) w| ≤ ‖w‖ := by
          have h_norm : ‖spherePoleVec d‖ = 1 := by
            convert norm_spherePoleVec d ( by linarith ) using 1;
          simpa [ h_norm ] using abs_real_inner_le_norm ( spherePoleVec d ) w;
        contrapose! h_norm;
        rw [ hw, abs_mul, abs_of_nonneg ( norm_nonneg _ ) ] ; nlinarith [ norm_pos_iff.mpr h_norm ];
      rw [ show { w : EuclideanSpace ℝ ( Fin d ) | inner ℝ ( spherePoleVec d ) w = c * ‖w‖ } = { 0 } from Set.eq_singleton_iff_unique_mem.mpr ⟨ by norm_num, h_zero ⟩ ] ; norm_num;
      cases d <;> norm_num at *;
    · -- If $|c| = 1$, then the set $\{w \mid \langle \text{pole}, w \rangle = c \|w\|\}$ is contained in the span of $\text{pole}$.
      have h_subset_span : {w : EuclideanSpace ℝ (Fin d) | inner ℝ (spherePoleVec d) w = c * ‖w‖} ⊆ Submodule.span ℝ {spherePoleVec d} := by
        intro w hw
        have h_eq : ‖w - (inner ℝ (spherePoleVec d) w) • spherePoleVec d‖ = 0 := by
          have h_eq : ‖w - (inner ℝ (spherePoleVec d) w) • spherePoleVec d‖ ^ 2 = ‖w‖ ^ 2 - (inner ℝ (spherePoleVec d) w) ^ 2 := by
            rw [ @norm_sub_sq ℝ ];
            norm_num [ norm_smul, inner_smul_right ];
            rw [ real_inner_comm ] ; ring;
            rw [ show ‖spherePoleVec d‖ = 1 from norm_spherePoleVec d ( by linarith ) ] ; norm_num ; ring;
          grind;
        exact eq_of_sub_eq_zero ( norm_eq_zero.mp h_eq ) ▸ Submodule.mem_span_singleton.mpr ⟨ _, rfl ⟩;
      refine' MeasureTheory.measure_mono_null h_subset_span _;
      convert Measure.addHaar_submodule _ _ _;
      · infer_instance;
      · infer_instance;
      · infer_instance;
      · have h_finrank : Module.finrank ℝ (Submodule.span ℝ {spherePoleVec d}) = 1 := by
          rw [ finrank_span_singleton ] ; norm_num [ spherePoleVec ];
          linarith;
        exact fun h => by rw [ h ] at h_finrank; norm_num at h_finrank; linarith [ show Module.finrank ℝ ( EuclideanSpace ℝ ( Fin d ) ) = d by simp +decide [ Module.finrank_pi ] ] ;
  · -- For the remaining case, define f(w) = (w - ⟨pole,w⟩•pole) + (c/√(1-c²)) * ‖w - ⟨pole,w⟩•pole‖ • pole.
    set f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun w => (w - inner ℝ (spherePoleVec d) w • spherePoleVec d) + (c / Real.sqrt (1 - c^2)) • ‖w - inner ℝ (spherePoleVec d) w • spherePoleVec d‖ • spherePoleVec d;
    -- Show that $f$ is smooth on the set where $\pi(w) \neq 0$.
    have h_smooth : ∀ w : EuclideanSpace ℝ (Fin d), w - inner ℝ (spherePoleVec d) w • spherePoleVec d ≠ 0 → DifferentiableAt ℝ f w := by
      intro w hw_ne_zero
      have h_inner_diff : DifferentiableAt ℝ (fun w => inner ℝ (spherePoleVec d) w) w := by
        exact DifferentiableAt.inner ℝ ( differentiableAt_const _ ) ( differentiableAt_id )
      have h_norm_diff : DifferentiableAt ℝ (fun w => ‖w - inner ℝ (spherePoleVec d) w • spherePoleVec d‖) w := by
        exact DifferentiableAt.norm ℝ ( differentiableAt_id.sub ( h_inner_diff.smul_const _ ) ) hw_ne_zero
      have h_f_diff : DifferentiableAt ℝ (fun w => (w - inner ℝ (spherePoleVec d) w • spherePoleVec d) + (c / Real.sqrt (1 - c^2)) • ‖w - inner ℝ (spherePoleVec d) w • spherePoleVec d‖ • spherePoleVec d) w := by
        fun_prop (disch := norm_num)
      exact h_f_diff;
    -- Show that $f$ maps the set $\{w \mid \langle \text{pole}, w \rangle = c \|w\|\}$ to itself.
    have h_map : ∀ w : EuclideanSpace ℝ (Fin d), inner ℝ (spherePoleVec d) w = c * ‖w‖ → w - inner ℝ (spherePoleVec d) w • spherePoleVec d ≠ 0 → f w = w := by
      intros w hw hw_ne_zero
      have h_norm : ‖w - inner ℝ (spherePoleVec d) w • spherePoleVec d‖ = Real.sqrt (1 - c^2) * ‖w‖ := by
        have h_norm : ‖w - inner ℝ (spherePoleVec d) w • spherePoleVec d‖^2 = (1 - c^2) * ‖w‖^2 := by
          rw [ @norm_sub_sq ℝ ];
          simp_all +decide [ norm_smul, inner_smul_right ];
          rw [ real_inner_comm ] ; rw [ hw ] ; ring;
          rw [ show ‖spherePoleVec d‖ = 1 from norm_spherePoleVec d ( by linarith ) ] ; norm_num ; ring;
        rw [ ← Real.sqrt_sq ( norm_nonneg _ ), h_norm, Real.sqrt_mul ( by nlinarith [ abs_lt.mp ( show |c| < 1 from lt_of_le_of_ne ( le_of_not_gt fun h => hc <| Or.inr <| Or.inl h ) fun h => hc <| Or.inr <| Or.inr h ) ] ), Real.sqrt_sq ( norm_nonneg _ ) ];
      simp +zetaDelta at *;
      rw [ h_norm ] ; ext ; norm_num ; ring;
      rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( by cases abs_cases c <;> cases lt_or_gt_of_ne hc.1 <;> cases lt_or_gt_of_ne hc.2.2 <;> nlinarith ) ) ) ] ; rw [ hw ] ; ring;
    -- Show that the determinant of the derivative of $f$ is zero on the set where $\pi(w) \neq 0$.
    have h_det_zero : ∀ w : EuclideanSpace ℝ (Fin d), w - inner ℝ (spherePoleVec d) w • spherePoleVec d ≠ 0 → LinearMap.det (fderiv ℝ f w).toLinearMap = 0 := by
      intro w hw_nonzero
      have h_deriv_zero : (fderiv ℝ f w) (spherePoleVec d) = 0 := by
        have h_deriv_zero : ∀ t : ℝ, f (w + t • spherePoleVec d) = f w := by
          simp +zetaDelta at *;
          simp +decide [ inner_add_right, inner_smul_right, norm_smul, hw_nonzero ];
          rw [ show ‖spherePoleVec d‖ = 1 from norm_spherePoleVec d ( by linarith ) ] ; norm_num ; ring;
          intro t; rw [ show w + t • spherePoleVec d - ( inner ℝ ( spherePoleVec d ) w + t ) • spherePoleVec d = w - inner ℝ ( spherePoleVec d ) w • spherePoleVec d by ext i; simpa using by ring ] ;
        have h_deriv_zero : HasDerivAt (fun t : ℝ => f (w + t • spherePoleVec d)) ((fderiv ℝ f w) (spherePoleVec d)) 0 := by
          convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp 0 ( h_smooth _ _ |> DifferentiableAt.hasFDerivAt ) ( HasFDerivAt.add ( hasFDerivAt_const _ _ ) ( HasFDerivAt.smul ( hasFDerivAt_id 0 ) ( hasFDerivAt_const _ _ ) ) ) ) using 1 ; norm_num;
          simpa using hw_nonzero;
        exact h_deriv_zero.deriv.symm.trans ( by rw [ show ( fun t : ℝ => f ( w + t • spherePoleVec d ) ) = fun _ => f w from funext ‹_› ] ; norm_num );
      have h_deriv_zero : ¬ Function.Injective (fderiv ℝ f w).toLinearMap := by
        intro h_inj;
        have := @h_inj ( spherePoleVec d ) 0 ; simp_all +decide [ Function.Injective ];
        unfold spherePoleVec at this; rcases d with ( _ | _ | d ) <;> norm_num at *;
      contrapose! h_deriv_zero;
      exact LinearEquiv.injective ( LinearMap.equivOfDetNeZero _ h_deriv_zero );
    -- Apply the theorem that states if the determinant of the derivative of a function is zero almost everywhere, then the image of the function has measure zero.
    have h_image_zero : MeasureTheory.volume (f '' {w : EuclideanSpace ℝ (Fin d) | inner ℝ (spherePoleVec d) w = c * ‖w‖ ∧ w - inner ℝ (spherePoleVec d) w • spherePoleVec d ≠ 0}) = 0 := by
      have h_image_zero : ∀ {S : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet S → (∀ w ∈ S, DifferentiableAt ℝ f w) → (∀ w ∈ S, LinearMap.det (fderiv ℝ f w).toLinearMap = 0) → MeasureTheory.volume (f '' S) = 0 := by
        intros S hS h_diff h_det_zero
        have h_image_zero : MeasureTheory.volume (f '' S) = 0 := by
          have h_diff : DifferentiableOn ℝ f S := by
            exact fun w hw => DifferentiableAt.differentiableWithinAt ( h_diff w hw )
          have h_det_zero : ∀ w ∈ S, LinearMap.det (fderiv ℝ f w).toLinearMap = 0 := by
            assumption
          have := @MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero;
          convert this volume ( fun w hw => DifferentiableAt.hasFDerivAt ( by solve_by_elim ) |> HasFDerivAt.hasFDerivWithinAt ) h_det_zero using 1;
        exact h_image_zero;
      apply h_image_zero;
      · refine' MeasurableSet.inter _ _;
        · exact measurableSet_eq_fun ( by exact Continuous.measurable ( by exact Continuous.inner continuous_const continuous_id' ) ) ( by exact Continuous.measurable ( by exact Continuous.mul continuous_const continuous_norm ) );
        · refine' MeasurableSet.compl _;
          refine' measurableSet_eq_fun _ _;
          · fun_prop (disch := norm_num);
          · exact measurable_const;
      · exact fun w hw => h_smooth w hw.2;
      · exact fun w hw => h_det_zero w hw.2;
    refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_union_null h_image_zero _ );
    rotate_left;
    exact { w : EuclideanSpace ℝ ( Fin d ) | w - inner ℝ ( spherePoleVec d ) w • spherePoleVec d = 0 };
    · -- The set $\{w \mid w - \langle \text{pole}, w \rangle \cdot \text{pole} = 0\}$ is a subspace of dimension $d-1$.
      have h_subspace : {w : EuclideanSpace ℝ (Fin d) | w - inner ℝ (spherePoleVec d) w • spherePoleVec d = 0} = Submodule.span ℝ {spherePoleVec d} := by
        ext w; simp [Submodule.mem_span_singleton];
        constructor <;> intro h;
        · exact ⟨ inner ℝ ( spherePoleVec d ) w, sub_eq_zero.mp h ▸ rfl ⟩;
        · rcases h with ⟨ a, rfl ⟩ ; norm_num [ inner_smul_right, norm_smul, norm_spherePoleVec ] ; ring;
          rw [ norm_spherePoleVec ] <;> norm_num;
          linarith;
      rw [ h_subspace ];
      have h_subspace_dim : Module.finrank ℝ (Submodule.span ℝ {spherePoleVec d} : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = 1 := by
        rw [ finrank_span_singleton ] ; norm_num [ spherePoleVec ];
        linarith;
      have h_subspace_dim : Module.finrank ℝ (Submodule.span ℝ {spherePoleVec d} : Submodule ℝ (EuclideanSpace ℝ (Fin d))) < d := by
        linarith;
      convert MeasureTheory.Measure.addHaar_submodule _ _ _;
      · infer_instance;
      · infer_instance;
      · infer_instance;
      · exact fun h => h_subspace_dim.ne <| by rw [ h ] ; simp +decide [ finrank_top ] ;
    · grind

/-
**Level sets of the inner-product with the pole have `toSphere`-measure zero**
    (for `d ≥ 2`).  Derived from `cone_subset_inner_eq_mul_norm` and
    `volume_inner_eq_mul_norm_zero` via `toSphere_apply'`.
-/
private lemma toSphere_levelSet_zero (d : ℕ) [hd : Fact (2 ≤ d)] (r : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
      {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val = r} = 0 := by
  have h_measure_zero : (volume : Measure (EuclideanSpace ℝ (Fin d))) (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val = r})) = 0 := by
    exact MeasureTheory.measure_mono_null ( cone_subset_inner_eq_mul_norm d r ) ( volume_inner_eq_mul_norm_zero d hd.out r );
  convert congr_arg ( fun x : ENNReal => x * ( Module.finrank ℝ ( EuclideanSpace ℝ ( Fin d ) ) : ENNReal ) ) h_measure_zero using 1;
  · convert Measure.toSphere_apply' _ _ using 1;
    · exact mul_comm _ _;
    · infer_instance;
    · exact measurableSet_eq_fun ( by exact Continuous.measurable ( by exact Continuous.inner continuous_const continuous_subtype_val ) ) measurable_const;
  · norm_num

/-- The uniform sphere measure of any level set `{x | ⟨pole, x⟩ = r}` is zero. -/
private lemma uniformOnSphere_levelSet_zero (d : ℕ) [hd : Fact (2 ≤ d)] (r : ℝ) :
    uniformOnSphere d {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val = r} = 0 := by
  unfold uniformOnSphere
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [toSphere_levelSet_zero]
  simp

/-
**`capProb d` equals the measure of the strict-inequality cap.**
    Follows from `uniformOnSphere_levelSet_zero`: the boundary set
    `{x | ⟨pole, x⟩ = r}` has measure zero, so `μ{≥ r} = μ{> r}`.
-/
private lemma capProb_eq_strict (d : ℕ) (hd : 2 ≤ d) (r : ℝ) :
    capProb d r =
      (uniformOnSphere d
        {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val > r}).toReal := by
  unfold capProb at *;
  rw [ show { x : SpherePoint d | r ≤ inner ℝ ( spherePoleVec d ) ( x : EuclideanSpace ℝ ( Fin d ) ) } = { x : SpherePoint d | r < inner ℝ ( spherePoleVec d ) ( x : EuclideanSpace ℝ ( Fin d ) ) } ∪ { x : SpherePoint d | inner ℝ ( spherePoleVec d ) ( x : EuclideanSpace ℝ ( Fin d ) ) = r } from ?_, MeasureTheory.measure_union ];
  · rw [ show ( uniformOnSphere d ) { x : SpherePoint d | inner ℝ ( spherePoleVec d ) x.val = r } = 0 from ?_ ] ; norm_num;
    convert uniformOnSphere_levelSet_zero d r using 1;
    exact ⟨ hd ⟩;
  · grind;
  · exact measurableSet_eq_fun ( by exact Continuous.measurable <| by exact Continuous.inner continuous_const <| by exact continuous_subtype_val ) measurable_const;
  · ext; simp [le_iff_lt_or_eq];
    rw [ eq_comm ]

/-
Continuity in the threshold (for `d ≥ 2`).  Proved from
    `uniformOnSphere_levelSet_zero`: the level-set `{x | ⟨pole, x⟩ = r}` has
    measure zero for every `r`, so the map `r ↦ μ{⟨pole, ·⟩ ≥ r}` is both
    left-continuous (continuity of measure from above on the decreasing family
    `{⟨pole, ·⟩ ≥ s}` as `s ↑ r`) and right-continuous (continuity from below
    on `{⟨pole, ·⟩ ≥ s}` as `s ↓ r`, combined with `μ{= r} = 0`).
-/
theorem capProb_continuous (d : ℕ) (hd : 2 ≤ d) : Continuous (capProb d) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro r
  unfold capProb;
  -- We'll use the fact that if the measure of the set {x | inner ℝ (spherePoleVec d) x.val ≥ r} is continuous, then the function itself is continuous.
  have h_cont : ContinuousAt (fun r => (uniformOnSphere d {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val ≥ r})) r := by
    have h_cont : ∀ᵐ x ∂(uniformOnSphere d), ContinuousAt (fun r => if inner ℝ (spherePoleVec d) x.val ≥ r then (1 : ℝ) else 0) r := by
      have h_cont : ∀ᵐ x ∂(uniformOnSphere d), inner ℝ (spherePoleVec d) x.val ≠ r := by
        have h_cont_at : uniformOnSphere d {x : SpherePoint d | inner ℝ (spherePoleVec d) x.val = r} = 0 := by
          convert uniformOnSphere_levelSet_zero d r using 1;
          exact ⟨ hd ⟩;
        exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_cont_at;
      filter_upwards [ h_cont ] with x hx;
      cases lt_or_gt_of_ne hx <;> [ exact ContinuousAt.congr ( continuousAt_const ) ( Filter.EventuallyEq.symm <| Filter.eventuallyEq_of_mem ( Ioi_mem_nhds ‹_› ) fun y hy => if_neg hy.out.not_ge ) ; exact ContinuousAt.congr ( continuousAt_const ) ( Filter.EventuallyEq.symm <| Filter.eventuallyEq_of_mem ( Iio_mem_nhds ‹_› ) fun y hy => if_pos hy.out.le ) ];
    have h_cont : Filter.Tendsto (fun r => ∫ x : SpherePoint d, (if inner ℝ (spherePoleVec d) x.val ≥ r then (1 : ℝ) else 0) ∂(uniformOnSphere d)) (nhds r) (nhds (∫ x : SpherePoint d, (if inner ℝ (spherePoleVec d) x.val ≥ r then (1 : ℝ) else 0) ∂(uniformOnSphere d))) := by
      refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
      refine' fun x => 1;
      · refine' Filter.Eventually.of_forall fun n => Measurable.aestronglyMeasurable _;
        refine' Measurable.ite _ measurable_const measurable_const;
        exact measurableSet_le measurable_const ( Continuous.measurable ( by exact Continuous.inner ( continuous_const ) ( continuous_subtype_val ) ) );
      · exact Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · apply_rules [ MeasureTheory.integrable_const ];
      · exact h_cont.mono fun x hx => hx.tendsto;
    convert h_cont using 1;
    constructor <;> intro h <;> simp_all +decide [ ContinuousAt ];
    convert ENNReal.tendsto_ofReal h using 1;
    · ext r; rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
      change ( uniformOnSphere d ) { x : SpherePoint d | r ≤ inner ℝ ( spherePoleVec d ) x.val } = ENNReal.ofReal ( ∫ x in { x : SpherePoint d | r ≤ inner ℝ ( spherePoleVec d ) x.val }, 1 ∂uniformOnSphere d );
      · simp +decide [ MeasureTheory.measureReal_def ];
      · exact measurableSet_le measurable_const ( Continuous.measurable ( by exact Continuous.inner continuous_const <| by exact continuous_subtype_val ) );
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
    · rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
      change nhds ( uniformOnSphere d { x : SpherePoint d | r ≤ inner ℝ ( spherePoleVec d ) x.val } ) = nhds ( ENNReal.ofReal ( ∫ x in { x : SpherePoint d | r ≤ inner ℝ ( spherePoleVec d ) x.val }, 1 ∂uniformOnSphere d ) );
      · simp +decide [ MeasureTheory.measureReal_def ];
      · exact measurableSet_le measurable_const ( Continuous.measurable ( by exact Continuous.inner ( continuous_const ) ( continuous_subtype_val ) ) );
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
  exact ENNReal.continuousAt_toReal ( by aesop ) |> ContinuousAt.comp <| h_cont

/-! ## Matched threshold

For two iid uniform points on $S^{d-1}$, the marginal edge probability at threshold
`r` is `2 · capProb d r · (1/2) = capProb d r` (rotate the first point to the pole).
The matched threshold `matchedCos p d` is the unique `r ∈ [-1, 1]` with
`capProb d r = p`. Existence + uniqueness from continuity + strict monotonicity. -/

/-- The matched cosine threshold realizing edge probability `p` in dimension `d`.
    Defined via classical choice on the existence axiom `matchedCos_exists`. -/
noncomputable def matchedCos (p : ℝ) (d : ℕ) : ℝ :=
  Classical.epsilon (fun r : ℝ => -1 ≤ r ∧ r ≤ 1 ∧ capProb d r = p)

/-- Existence of a matched threshold. IVT (`intermediate_value_Icc'`, antitone-endpoint
    variant) applied to the continuous `capProb d` on `[-1, 1]`, using
    `capProb_neg_one d hd = 1` and `capProb_one d hd = 0`. Concretised 2026-05-19
    (was axiomatic; downgraded to theorem dependent on `capProb_continuous` only). -/
theorem matchedCos_exists (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 2 ≤ d) :
    ∃ r : ℝ, -1 ≤ r ∧ r ≤ 1 ∧ capProb d r = p := by
  have h_cont : ContinuousOn (capProb d) (Set.Icc (-1 : ℝ) 1) :=
    (capProb_continuous d hd).continuousOn
  have h_neg_one : capProb d (-1) = 1 := capProb_neg_one d hd
  have h_one : capProb d 1 = 0 := capProb_one d hd
  have h_le : (-1 : ℝ) ≤ 1 := by norm_num
  have h_image : Set.Icc (capProb d 1) (capProb d (-1)) ⊆ capProb d '' Set.Icc (-1 : ℝ) 1 :=
    intermediate_value_Icc' h_le h_cont
  rw [h_neg_one, h_one] at h_image
  have hp_mem : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hp0, le_of_lt hp1⟩
  obtain ⟨r, hr_mem, hr_eq⟩ := h_image hp_mem
  exact ⟨r, hr_mem.1, hr_mem.2, hr_eq⟩

/-- The specification realized by `matchedCos`. -/
lemma matchedCos_spec (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 2 ≤ d) :
    -1 ≤ matchedCos p d ∧ matchedCos p d ≤ 1 ∧ capProb d (matchedCos p d) = p := by
  unfold matchedCos
  exact Classical.epsilon_spec (matchedCos_exists p d hp0 hp1 hd)

/-- Asymptotic: $\text{matchedCos}(p, d) \sim z_p / \sqrt{d}$ as $d \to \infty$,
    where $z_p = \Phi^{-1}(1-p)$ is the standard normal quantile. Stated against
    an axiomatized normal-quantile constant `normalQuantile p`. -/
axiom normalQuantile : ℝ → ℝ

/-- **Cap-CLT + normal-quantile inversion (auxiliary axiom).**
    The Poincaré / CLT limit for spherical caps says that as $d \to \infty$,
    the spherical cap probability at cosine threshold $t / \sqrt{d}$ converges
    to $\Phi(-t)$. Inverting this uniformly: if a sequence of thresholds
    $r_d \in [-1, 1]$ satisfies `capProb d (r d) = p` for all sufficiently large
    $d$, then $\sqrt{d} \cdot r_d \to \Phi^{-1}(1 - p) = $ `normalQuantile (1 - p)`.
    Axiomatized pending Mathlib formalization of the CLT for spherical caps
    (Li 2011 / Poincaré limit) + continuous inversion of the normal CDF. -/
axiom capCLT_matched_inversion (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (r : ℕ → ℝ) (hr : ∀ᶠ d in Filter.atTop, capProb d (r d) = p) :
    Filter.Tendsto (fun d : ℕ => Real.sqrt d * r d) Filter.atTop
      (nhds (normalQuantile (1 - p)))

lemma matchedCos_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => Real.sqrt d * matchedCos p d) Filter.atTop
      (nhds (normalQuantile (1 - p))) := by
  apply capCLT_matched_inversion p hp0 hp1
  rw [Filter.eventually_atTop]
  exact ⟨2, fun d hd => (matchedCos_spec p d hp0 hp1 hd).2.2⟩

/-! ## Triangle (Čech-fill) probability and the asymptotic headline

The triangle (Rips/Čech) probabilities are axiomatized as functions of `(p, d)`; their
defining integral expressions live in the moonshot proof and are not yet ported. -/

/-- $q_{\text{Čech}}(p, d) = \Pr[\text{sphereCechFill at threshold matchedCos } p d]$.
    Defined as the measure (under the iid product of `uniformOnSphere d` on three points)
    of the Čech-fill event at the matched cosine threshold. Concretised 2026-05-19. -/
noncomputable def cechFillProb (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchedCos p d
  let ν := (uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))
  (ν {triple : SpherePoint d × SpherePoint d × SpherePoint d |
    sphereCechFill r triple.1 triple.2.1 triple.2.2}).toReal

/-- Rips clique probability under matched edge $p$: probability that all three pairwise
    edges are present at the matched cosine threshold. -/
noncomputable def ripsFillProb (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchedCos p d
  let ν := (uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))
  (ν {triple : SpherePoint d × SpherePoint d × SpherePoint d |
    sphereEdge r triple.1 triple.2.1 ∧
    sphereEdge r triple.1 triple.2.2 ∧
    sphereEdge r triple.2.1 triple.2.2}).toReal

open Classical in
/-- Geometric covariance under Čech fill on the sphere:
    `E[(A₁₂−p)(A₁₃−p)(A₂₃−p)(F^{Čech}−q_{Čech})]`. Closed form follows the four-moment
    decomposition `q_Rips(1−q_Čech) + 3p²(β−p)` with `β = E[A₁₂ · F^{Čech}]`. -/
noncomputable def geomCovCech (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchedCos p d
  let q := cechFillProb p d
  let ν := (uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))
  ∫ triple, ((if sphereEdge r triple.1 triple.2.1 then (1:ℝ) - p else -p) *
             (if sphereEdge r triple.1 triple.2.2 then (1:ℝ) - p else -p) *
             (if sphereEdge r triple.2.1 triple.2.2 then (1:ℝ) - p else -p) *
             (if sphereCechFill r triple.1 triple.2.1 triple.2.2
                then (1:ℝ) - q else -q)) ∂ν

/-! ### Structural axioms for Paper 2 sphere asymptotics

The Paper 2 headlines (`cechFillProb_tail_asymptotic` and `geomCovCech_asymptotic`)
are derived from a small set of **named load-bearing structural axioms** capturing
the deep moonshot content: Wishart pushforward, joint Gram density, surface
concentration, algebraic decomposition. Each axiom is documented with its
mathematical content + reference to `paper2_sphere_scoping.md`. Future work
removes these by porting Wishart/incomplete-Beta machinery to Mathlib.

This architecture is preferred over bare-fact axioms (`cechFillProb_tail_asymptotic`
as axiom) because:
1. The audit trail names WHICH math content is unproven (Gram density, etc.)
   rather than just "the headline."
2. Multiple headlines derive from a common axiom layer (DRY).
3. Future ports replace axioms in dependency order, with each removal directly
   measurable. -/

/-- **Axiom (Wishart-derived Gram density tail).** For three iid uniform points
    on $S^{d-1}$ with $d \ge 5$, the joint density of the three pairwise inner
    products $(y_{12}, y_{13}, y_{23})$ is proportional to $(\det G)^{(d-4)/2}$
    where $G$ is the $3 \times 3$ Gram matrix. The vanishing at the boundary
    $\det G = 0$ forces a super-exponential tail: for the matched cosine
    threshold $r_d = $ `matchedCos p d`, the complement triple-cover probability
    is bounded above by `(3 (normalQuantile (1 - p))^2 / d)^((d-2)/2)` eventually.

    See `paper2_sphere_scoping.md` § "Tail computation" + § "Tightened rate analysis". -/
axiom cechFillProb_compl_le_gram_tail (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d : ℕ in Filter.atTop,
      1 - cechFillProb p d ≤
        ((3 * (normalQuantile (1 - p))^2) / (d : ℝ))^(((d : ℝ) - 2) / 2)

/-- **`cechFillProb p d ≤ 1`** — direct consequence of the iid-product measure being
    zero-or-probability (`uniformOnSphere_isZeroOrProb`) applied to the underlying
    integrand set. Concretised 2026-05-19 (was axiomatic). -/
theorem cechFillProb_le_one (p : ℝ) (d : ℕ) : cechFillProb p d ≤ 1 := by
  unfold cechFillProb
  -- The product measure of zero-or-probability measures is again zero-or-probability:
  -- product instance only fires for IsProbabilityMeasure, so we case-split.
  -- More directly: `measureReal_le_one` from probability typeclass requires
  -- `IsZeroOrProbabilityMeasure` on the product. We prove that.
  have h_inst : IsZeroOrProbabilityMeasure
      ((uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))) := by
    rcases (uniformOnSphere_isZeroOrProb d).measure_univ with h | h
    · -- uniformOnSphere d = 0 since μ univ = 0 and the measure is finite
      have h_zero : uniformOnSphere d = 0 := by
        rw [← Measure.measure_univ_eq_zero]; exact h
      refine ⟨Or.inl ?_⟩
      rw [h_zero]; simp
    · -- uniformOnSphere d is a probability measure
      haveI : IsProbabilityMeasure (uniformOnSphere d) := ⟨h⟩
      exact inferInstance
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (ENNReal.ofReal_one.symm ▸ prob_le_one)

/-- **Axiom (Rips-Čech algebraic decomposition, sphere).** The geometric covariance
    on the sphere admits the algebraic decomposition
    $\text{geomCov}_{\text{Čech}} = q_{\text{Rips}} \cdot (1 - q_{\text{Čech}})
       + 3 p^2 \cdot (\beta - p)$
    where $\beta := \mathbb E[A_{12} \cdot F^{\text{Čech}}]$ is the
    wedge-Čech joint moment. Combined with surface-concentration ($\beta - p
    \to -p \cdot c_d \cdot (1 - q_{\text{Čech}})$ with $c_d \to 0$ super-exp,
    SLOWER than $1 - q_{\text{Čech}}$) and Rips clique convergence
    ($q_{\text{Rips}} \to p^3$ on sphere), this gives
    $\text{geomCov}_{\text{Čech}} / (p^3 (1 - q_{\text{Čech}})) \to 1$.

    Stated here as a black-box ratio convergence; future work derives this from
    the Wishart density axiom + sphere clique probability axioms.

    See `paper2_sphere_scoping.md` § "Surface-concentration argument" +
    § "Sub-leading rate of $c_d$". -/
axiom geomCovCech_decomp_ratio_tendsto (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geomCovCech p d / (p ^ 3 * (1 - cechFillProb p d)))
      Filter.atTop (nhds 1)

/-- **Auxiliary fact.** For any $p \in (0, 1)$, the asymptotic upper bound
    `(3 (normalQuantile (1 - p))^2 / d)^((d-2)/2) → 0` as $d \to \infty$.
    Pure analytic statement — base tends to 0, exponent tends to $\infty$. -/
private lemma gram_tail_bound_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto
      (fun d : ℕ => ((3 * (normalQuantile (1 - p))^2) / (d : ℝ))^(((d : ℝ) - 2) / 2))
      Filter.atTop (nhds 0) := by
  -- Strategy: let `a = 3 * (normalQuantile (1-p))^2 ≥ 0`. Squeeze the function `f d :=
  -- (a/d)^((d-2)/2)` between `0` and `a/d`. For `d ≥ a + 1` and `d ≥ 4` we have
  -- `0 ≤ a/d ≤ 1` and `1 ≤ (d-2)/2`, so by `Real.rpow_le_rpow_of_exponent_ge` (which
  -- requires `0 < base`, handled via case split on `a/d = 0`) the rpow at the larger
  -- exponent is dominated by the rpow at exponent 1, i.e. by `a/d` itself. Then
  -- `a/d → 0`, and the lower bound `0` is immediate from `Real.rpow_nonneg`.
  set a : ℝ := 3 * (normalQuantile (1 - p))^2 with ha_def
  have ha_nn : 0 ≤ a := by
    have : (0 : ℝ) ≤ 3 * (normalQuantile (1 - p))^2 := by positivity
    exact this
  -- Bound `a/d → 0`.
  have h_bd_to_zero : Filter.Tendsto (fun d : ℕ => a / (d : ℝ)) Filter.atTop (nhds 0) := by
    have h_inv : Filter.Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h_eq : (fun d : ℕ => a / (d : ℝ)) = (fun d : ℕ => a * (1 / (d : ℝ))) := by
      funext d; ring
    rw [h_eq, show (0 : ℝ) = a * 0 by ring]
    exact h_inv.const_mul a
  -- Squeeze.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_bd_to_zero
  · -- Lower bound: `0 ≤ (a/d)^((d-2)/2)`.
    refine Filter.Eventually.of_forall fun d => ?_
    exact Real.rpow_nonneg (by positivity) _
  · -- Upper bound: `(a/d)^((d-2)/2) ≤ a/d` eventually.
    have h_large_a : ∀ᶠ d : ℕ in Filter.atTop, a + 1 ≤ (d : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (a + 1)
    have h_large_4 : ∀ᶠ d : ℕ in Filter.atTop, 4 ≤ d := Filter.eventually_ge_atTop 4
    filter_upwards [h_large_a, h_large_4] with d hd_a hd_4
    have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast hd_4
    have hd_pos : (0 : ℝ) < d := by linarith
    have h_ad_nn : 0 ≤ a / (d : ℝ) := div_nonneg ha_nn hd_pos.le
    have h_ad_le_one : a / (d : ℝ) ≤ 1 := by
      rw [div_le_one hd_pos]; linarith
    have h_exp_ge_one : (1 : ℝ) ≤ ((d : ℝ) - 2) / 2 := by linarith
    by_cases h_ad_zero : a / (d : ℝ) = 0
    · rw [h_ad_zero]
      rw [Real.zero_rpow (by linarith : ((d : ℝ) - 2) / 2 ≠ 0)]
    · have h_ad_pos : 0 < a / (d : ℝ) := h_ad_nn.lt_of_ne (Ne.symm h_ad_zero)
      have := Real.rpow_le_rpow_of_exponent_ge h_ad_pos h_ad_le_one h_exp_ge_one
      simpa using this

/-- **Tail asymptotic (Paper 2 headline part 1).** Derived from the Wishart
    Gram-density tail axiom + squeeze: $0 \le 1 - q_{\text{Čech}} \le $ Gram tail bound,
    and Gram tail bound $\to 0$. -/
theorem cechFillProb_tail_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => cechFillProb p d) Filter.atTop (nhds 1) := by
  -- Strategy: show `1 - cechFillProb p d → 0`, then transport via `1 - (1 - x) = x`.
  have h_compl_to_zero :
      Filter.Tendsto (fun d : ℕ => 1 - cechFillProb p d) Filter.atTop (nhds 0) := by
    -- Squeeze: 0 ≤ 1 - q ≤ Gram-tail bound, where bound → 0.
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (gram_tail_bound_tendsto_zero p hp0 hp1)
    · -- 0 ≤ 1 - cechFillProb p d eventually (always, by cechFillProb_le_one)
      exact Filter.Eventually.of_forall (fun d => by
        have := cechFillProb_le_one p d
        linarith)
    · exact cechFillProb_compl_le_gram_tail p hp0 hp1
  -- Now `1 - q → 0` ⇒ `q → 1`.
  have := (tendsto_const_nhds (x := (1:ℝ))).sub h_compl_to_zero
  simpa using this

/-- **GeomCov asymptotic (Paper 2 headline part 2).** Direct from the
    `geomCovCech_decomp_ratio_tendsto` structural axiom (which encodes the
    surface-concentration + algebraic decomposition). -/
theorem geomCovCech_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geomCovCech p d / (p ^ 3 * (1 - cechFillProb p d)))
      Filter.atTop (nhds 1) :=
  geomCovCech_decomp_ratio_tendsto p hp0 hp1

/-! ## CechSphereModel instance -/

/-- Validity regime for the sphere instance: $d \ge 5$ (so the Gram density vanishes at the
    boundary $\det G = 0$, enabling the super-exponential tail), $p \in (0, 1)$. -/
def SphereValidRegime (p : ℝ) (d : ℕ) : Prop :=
  0 < p ∧ p < 1 ∧ 5 ≤ d

/-- The sphere Čech instance of `CechSphereModel ℕ`. Wires the asymptotic theorem
    `geomCovCech_asymptotic` as the typeclass axiom.

    Note: this is **not** an instance of `HomogeneousGeometricModel` — the Rips closed form
    fails under Čech (see session-65 decision in `wiki/decisions.md`). The split typeclass
    architecture in `Geometry/Common.lean` keeps Rips and Čech models distinct. -/
noncomputable instance : CechSphereModel ℕ where
  Point d := SpherePoint d
  pointSpace _ := inferInstance
  μ d := uniformOnSphere d
  WellFormed d := 2 ≤ d
  isProb d hd := uniformOnSphere_isProb' d hd
  edge _ r x y := sphereEdge r x y
  matchR p d := matchedCos p d
  cechFillProb p d := cechFillProb p d
  geomCovCech p d := geomCovCech p d
  ValidRegime p d := SphereValidRegime p d
  geomCov_asymptotic := by
    intro p hp0 hp1
    exact geomCovCech_asymptotic p hp0 hp1

/-! ## Aristotle dispatch plan (S2–S6)

Phase | Target | Statement |
|---|---|---|
| S2 | Cap volume closed form | `volume(spherical_cap θ) = (1/2) · I_{sin² θ}((d-1)/2, 1/2)` |
| S3 | `matchedCos` exists and unique | inverse function of cap-volume formula |
| S4 | Joint Gram density | `f(y_{12}, y_{13}, y_{23}) ∝ (det G)^{(d-4)/2}` |
| S5 | Tail asymptotic | `Pr[det G ≤ t] ~ t^{(d-2)/2}` |
| S6 | GeomCov closed form | the four-moment decomposition + leading-order $p^3(1-q_{\text{Čech}})$ |

Each is an Aristotle job; expected difficulty moderate to high. References:
Wendel 1962, Anderson-Cook 1986, Li 2011 (cap formula), Reitzner 2010 (random polytopes).
-/

end SphereGeometry
