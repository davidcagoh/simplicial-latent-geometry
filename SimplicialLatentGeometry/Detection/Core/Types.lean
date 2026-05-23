import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.Core.Types`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


/-!
# Testing for Geometry in Random Simplicial Complexes

Formalisation of the phase transition for the filled triangle statistic (Goh, in preparation).
The core question: can we distinguish a 2-parameter complex 2PC(n, p, q) from a Čech complex
on the flat torus 𝕋^d using the signed filled-triangle statistic?
-/

/-! ## Definitions -/

-- `TwoParamSample` moved to `Core.Statistic` (Phase A1 core-extraction, OQ-18).

/-- The flat d-dimensional torus T^d = (ℝ/ℤ)^d with unit side length,
    equipped with the product metric inherited from AddCircle (1 : ℝ). -/
abbrev Torus (d : ℕ) := Fin d → AddCircle (1 : ℝ)



/-- **Definition 2 (Vietoris–Rips Complex on the Flat Torus).** A sample from Rips(n, r, d)
    is n points on the sup-norm flat torus T^d. The simplicial complex structure is
    determined by the radius r:
    - edge {i,j} is present iff dist(points i, points j) ≤ r
    - triangle {i,j,k} is filled iff all three pairwise distances are ≤ r
      (clique complex / flag complex of the geometric graph).

    On the sup-norm torus, ℓ∞-balls are axis-aligned boxes and Helly's theorem gives
    Helly number 2, so the Kahle Čech complex (K10 Def 1.4, nerve of {B(x_i, r/2)})
    coincides with this Rips complex. We adopt the Rips presentation because it is
    manifestly a clique complex (downward closed by construction) and the moment
    computations factor coordinate-by-coordinate under sup-norm. -/
structure CechSample (n d : ℕ) where
  points : Fin n → Torus d



/-- In Rips(s, r), vertices i and j are connected iff their torus distance is ≤ r. -/
def CechSample.hasEdge {n d : ℕ} (s : CechSample n d) (r : ℝ) (i j : Fin n) : Prop :=
  dist (s.points i) (s.points j) ≤ r



/-- In Rips(s, r), triangle t is filled iff all three pairwise distances are ≤ r
    (clique complex). Equivalently F_ijk = A_ij · A_ik · A_jk. -/
def CechSample.hasFill {n d : ℕ} (s : CechSample n d) (r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) : Prop :=
  ∀ i ∈ t.val, ∀ j ∈ t.val, dist (s.points i) (s.points j) ≤ r



/-- Volume of the Euclidean d-ball of radius r: V_d(r) = π^(d/2) / Γ(d/2 + 1) · r^d. -/
noncomputable def euclidBallVol (d : ℕ) (r : ℝ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) * r ^ d



/-- **Definition 3 (Parameter Matching).** Given edge probability p and dimension d,
    the matching radius r(p, d) is the unique r ≥ 0 satisfying (2r)^d = p.
    On the unit sup-norm torus Fin d → AddCircle (1:ℝ), the ball of radius r has volume
    (2r)^d (Lebesgue measure). Solving (2r)^d = p gives r = p^(1/d) / 2.
    As d → ∞, r → 1/2 from below (since p^(1/d) → 1 for p ∈ (0,1)).
    For d = 0, set r = 0 (degenerate case). -/
noncomputable def matchRadius (p : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0
  else p ^ ((1 : ℝ) / (d : ℝ)) / 2



open MeasureTheory in
/-- **Definition 4 (Empty Volume).** V_e(s, d) is the volume of the region a third point
    must occupy to form an *empty* 3-cycle in Cech(n, r, d), given two connected vertices
    at separation s. Equals V_d(2r) * I_{x}((d+1)/2, 1/2) where x = 1 - (s/2r)^2.

    V_e(s,d) is the intersection volume of two d-balls of radius 2r with centres separated
    by s. Using the regularised incomplete Beta function:
      V_e(s,d) = V_d(2r) * (integral_0^x t^(a-1)*(1-t)^(b-1) dt) / B(a,b),
    where a = (d+1)/2, b = 1/2, x = 1-(s/(4r))^2 = 1-(s/(2*(2r)))^2, and B(a,b) = Gamma(a)*Gamma(b)/Gamma(a+b).
    Note: the parameter x uses radius 2r (not r): for two balls of radius R at distance s,
    x = 1-(s/(2R))^2. Here R = 2r, giving x = 1-(s/(4r))^2. -/
noncomputable def volumeEmpty (d : ℕ) (r s : ℝ) : ℝ :=
  -- x = 1 - (s/(4r))²: correct beta parameter for intersection of two (2r)-balls.
  -- For two balls of radius R at distance s, the regularised incBeta parameter is
  -- x = 1 - (s/(2R))². Here R = 2r, so x = 1 - (s/(4r))² = 1 - (s/(2*(2*r)))².
  let x := 1 - (s / (2 * (2 * r))) ^ 2
  let a := ((d : ℝ) + 1) / 2
  let b := (1 : ℝ) / 2
  -- Incomplete Beta integral: ∫₀ˣ t^(a-1) · (1-t)^(b-1) dt
  let incBeta := ∫ t in Set.Ioo 0 x, t ^ (a - 1) * (1 - t) ^ (b - 1)
  -- Beta function: B(a,b) = Γ(a)·Γ(b)/Γ(a+b)
  let betaFn := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)
  euclidBallVol d (2 * r) * incBeta / betaFn



open MeasureTheory in
/-- **Definition 4 (Fill Volume).** V_f(s, d) is the volume of the intersection of two
    r-balls at distance s — the region a third point can occupy to form a filled triangle
    in Cech(n, r, d) given two connected vertices at separation s. Using the regularised
    incomplete Beta function (same structure as volumeEmpty but for r-balls, not 2r-balls):
      V_f(s,d) = V_d(r) · I_{x}((d+1)/2, 1/2) / B((d+1)/2, 1/2)
    where x = 1-(s/(2r))^2.  (Compare volumeEmpty: radius 2r, x = 1-(s/(4r))^2.)
    Since x_fill = 1-(s/2r)^2 ≤ 1-(s/4r)^2 = x_empty and euclidBallVol d r ≤ euclidBallVol d (2r),
    we have V_f ≤ V_e, so the fill/empty ratio is ≤ 1. -/
noncomputable def volumeFill (d : ℕ) (r s : ℝ) : ℝ :=
  -- x = 1 - (s/(2r))²: correct beta parameter for intersection of two r-balls.
  -- For two balls of radius R at distance s, x = 1-(s/(2R))². Here R=r.
  let x := 1 - (s / (2 * r)) ^ 2
  let a := ((d : ℝ) + 1) / 2
  let b := (1 : ℝ) / 2
  -- Incomplete Beta integral: ∫₀ˣ t^(a-1) · (1-t)^(b-1) dt
  let incBeta := ∫ t in Set.Ioo 0 x, t ^ (a - 1) * (1 - t) ^ (b - 1)
  -- Beta function: B(a,b) = Γ(a)·Γ(b)/Γ(a+b)
  let betaFn := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)
  euclidBallVol d r * incBeta / betaFn



open Classical in
open MeasureTheory in
/-- **Definition 5 (Filling Probability, Rips convention).** Under Rips,
    F_ijk = A_ij · A_ik · A_jk, so the matched fill probability is just the
    triangle (3-clique) probability:
      q(p,d) = P(all 3 pairwise distances ≤ r) for r = matchRadius p d.
    On the sup-norm torus this equals (3 r²)^d for r ≤ 1/4 (see `gamma_pow_eq`). -/
noncomputable def fillingProb (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchRadius p d
  ∫ pts : Fin 3 → Torus d,
    ((if dist (pts 0) (pts 1) ≤ r then (1:ℝ) else 0) *
     (if dist (pts 0) (pts 2) ≤ r then (1:ℝ) else 0) *
     (if dist (pts 1) (pts 2) ≤ r then (1:ℝ) else 0))
  ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))

/-! ## Moment Setup -/

-- `MeasurableSpace (TwoParamSample n)`, `triangleEdges`, `filledTriangleCount`, and
-- `twoParamMeasure` moved to `Core.Statistic` (Phase A1 core-extraction, OQ-18).

/-- Sigma-algebra on CechSample induced by the points projection.
    This is the coarsest sigma-algebra making `CechSample.points` measurable,
    which ensures `Measure.comap` of the product measure is well-defined. -/
instance (n d : ℕ) : MeasurableSpace (CechSample n d) :=
  MeasurableSpace.comap CechSample.points inferInstance



open MeasureTheory in
/-- Expected fill volume 𝔼[V_f]: V_f(s,d) averaged over the separation PDF d·s^(d-1). -/
noncomputable def expectedFillVol (d : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Set.Ioo 0 1, volumeFill d r s * (d : ℝ) * s ^ (d - 1)



/-! ## Asymptotics -/

open MeasureTheory in
/-- Expected empty volume: V_e(s,d) averaged over the separation PDF d·s^(d-1). -/
noncomputable def expectedEmptyVol (d : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Set.Ioo 0 1, volumeEmpty d r s * (d : ℝ) * s ^ (d - 1)



-- SUPERSEDED (Strategy 1): `asymptotics_expectedEmptyVol`, `asymptotics_expectedFillVol`,
-- `decay_fillingProb` assumed E[V_f] → 0 polynomially, but Aristotle showed
-- E[V_f] → L > 0 as d → ∞. Removed 2026-05-19. The Strategy 2 replacements are in the
-- closed-form chain `geometricCov_eq` / `geometricCov_tendsto_pcubed_compcubed`.

/-! ## Main Theorems -/

-- `tvDist` (total variation distance) and its supporting lemmas moved to
-- `Core.Detection` (Phase A3).

/-! ### Infrastructure lemmas -/

/-- The matching radius satisfies the torus ball volume equation (2r)^d = p.
    With the corrected sup-norm torus formula: matchRadius p d = p^(1/d)/2 for d ≥ 1.
    So (2 * matchRadius p d)^d = (p^(1/d))^d = p.

    PROVIDED SOLUTION
    Step 1: Unfold matchRadius: for d ≥ 1, matchRadius p d = p^(1/d)/2.
    Step 2: 2 * matchRadius p d = p^(1/d).
    Step 3: (p^(1/d))^d = p^(1/d * d) = p^1 = p.
    Use Real.rpow_natCast and Real.rpow_mul (hp0.le). -/
lemma matchRadius_spec (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (2 * matchRadius p d) ^ d = p := by
  unfold matchRadius
  rw [if_neg (by omega)]
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Real.rpow_natCast (p ^ ((1:ℝ) / (d:ℝ))) d]
  rw [← Real.rpow_mul hp0.le]
  rw [one_div, inv_mul_cancel₀ hd', Real.rpow_one]



/-! ### Helper lemmas for geometric covariance decay

**Lemma C (Geometric covariance decays to zero).**
For fixed p ∈ (0,1), geometricCov p d → 0 as d → ∞.

Intuition: As d → ∞, the torus geometry becomes "asymptotically independent" — the
edge and fill events decouple, and since q = fillingProb p d = E_Čech[fill], the
centered fill factor satisfies E[(F-q)] = 0. The full covariance decays because the
joint distribution of (edge₁₂, edge₁₃, edge₂₃, fill) converges to a product measure.

Note: The precise decay rate geometricCov p d ~ C(p)/d^α determines the phase
transition threshold d*(n,p). This is an open research question. -/

/-
PROBLEM
The torus diameter in the sup metric is 1/2.

PROVIDED SOLUTION
The sup metric on Fin d → AddCircle 1 gives dist x y = sup_i dist (x i) (y i). Each coordinate uses the AddCircle metric where dist ≤ |period|/2 = 1/2 by AddCircle.norm_le_half_period. Use dist_pi_le_iff to reduce to coordinate-wise, then dist_eq_norm and AddCircle.norm_le_half_period.
-/
lemma torus_dist_le_half (d : ℕ) (x y : Torus d) : dist x y ≤ 1/2 := by
  -- Since the distance on each coordinate is ≤ 1/2, the supremum of these distances is also ≤ 1/2.
  have h_sup_le_half : ∀ i : Fin d, dist (x i) (y i) ≤ 1 / 2 := by
    intro i
    have h_dist_le : dist (x i) (y i) ≤ 1 / 2 := by
      have h_abs : ∀ x y : AddCircle (1 : ℝ), dist x y ≤ 1 / 2 := by
        intro x y; exact (by
        convert AddCircle.norm_le_half_period ( 1 : ℝ ) _ using 1;
        · norm_num [ abs_of_nonneg ];
        · norm_num)
      exact h_abs (x i) (y i);
    exact h_dist_le;
  rw [ dist_pi_le_iff ] ; aesop;
  norm_num +zetaDelta at *



/-! ### Regime-free closed form (Aristotle dispatch target)

`geometricCov_eq_deep` carries the hypothesis `matchRadius ≤ 1/4`. That was an
artefact of the specific proof template (using `(3r²)^d` volume identity), NOT
the underlying math: the closed form `geomCov = q[(1-p)^3 + p^3] − q^2` holds for
*any* `r ≤ 1/2` via a regime-independent argument:

(a) `centered_edge_moment_fill = (1-p)^3 · q` is purely algebraic — for 0/1
    indicators E, `E · (E - p) = (1 - p) · E`, so the product collapses to
    `(1-p)^3 · F` and integrates to `(1-p)^3 · q`. NO regime dependence.

(b) `centered_edge_moment = q − p^3` reduces by Fubini to the identity
    `μ_W = p^2` where `μ_W := ∫ E_12 E_13` is the wedge probability. This holds
    whenever `r ≤ 1/2` (each 1D torus ball has Lebesgue 2r, and matched
    `(2r)^d = p`).

Since `matchRadius p d = p^{1/d}/2 ≤ 1/2` ALWAYS, no auxiliary hypothesis is
needed. This single regime-free identity replaces `geometricCov_eq_deep` (deep
hypothesis) and the would-be `geometricCov_eq_mid` (mid hypothesis). -/

/-! #### Regime-free helpers -/

open Classical MeasureTheory in
lemma matchRadius_lt_half (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    matchRadius p d < 1 / 2 := by
  unfold matchRadius
  rw [if_neg (by omega)]
  apply div_lt_div_of_pos_right _ (by norm_num : (0:ℝ) < 2)
  exact Real.rpow_lt_one hp0.le hp1 (by positivity)



open Classical MeasureTheory in
lemma matchRadius_pos' (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hd : 1 ≤ d) :
    0 < matchRadius p d := by
  unfold matchRadius; rw [if_neg (by omega)]; positivity



/-
OLD PROOF BODY:
  have h_comap_prob : MeasureTheory.IsProbabilityMeasure (cechMeasure n d r) := by
    exact?
  generalize_proofs at *; (
  constructor
  generalize_proofs at *; (
  rw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ h_comap_prob ];
  apply measurable_to_countable';
  intro x
  have h_preimage : MeasurableSet {s : CechSample n d | cechObservation r s = x} := by
    have h_preimage : MeasurableSet {s : Fin n → Torus d | cechObservation r ⟨s⟩ = x} := by
      -- The set {s | cechObservation r ⟨s⟩ = x} is a finite intersection of measurable sets, hence measurable.
      have h_measurable : ∀ i j, MeasurableSet {s : Fin n → Torus d | (cechObservation r ⟨s⟩).edge i j = x.edge i j} := by
        intro i j
        have h_measurable : MeasurableSet {s : Fin n → Torus d | dist (s i) (s j) ≤ r} := by
          exact measurableSet_le ( measurable_pi_apply i |> Measurable.dist <| measurable_pi_apply j ) measurable_const
        generalize_proofs at *; (
        cases x.edge i j <;> simp_all +decide [ cechObservation ];
        · exact Measurable.not h_measurable;
        · convert h_measurable using 1)
      generalize_proofs at *; (
      have h_measurable : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, MeasurableSet {s : Fin n → Torus d | (cechObservation r ⟨s⟩).fill t = x.fill t} := by
        intro t
        have h_measurable : MeasurableSet {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ r} := by
          -- The set {s | ∃ z, ∀ i ∈ t.val, dist (s i) z ≤ r} is the union over all z of the sets {s | ∀ i ∈ t.val, dist (s i) z ≤ r}, which are closed and hence measurable.
          have h_union_measurable : MeasurableSet (⋃ z : Torus d, {s : Fin n → Torus d | ∀ i ∈ t.val, dist (s i) z ≤ r}) := by
            -- The union of closed sets is closed, and closed sets are measurable.
            have h_closed : IsClosed (⋃ z : Torus d, {s : Fin n → Torus d | ∀ i ∈ t.val, dist (s i) z ≤ r}) := by
              refine' isClosed_of_closure_subset fun s hs => _;
              rw [ mem_closure_iff_seq_limit ] at hs
              generalize_proofs at *; (
              obtain ⟨ x, hx₁, hx₂ ⟩ := hs
              generalize_proofs at *; (
              choose z hz using fun n => Set.mem_iUnion.mp ( hx₁ n );
              -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
              obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
                have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
                  exact isCompact_univ_iff.mpr ( by infer_instance )
                generalize_proofs at *; (
                have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;)
              generalize_proofs at *; (
              obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
              refine' Set.mem_iUnion.mpr ⟨ z', fun i hi => _ ⟩
              generalize_proofs at *; (
              exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _ hi |> le_trans <| by norm_num;))))
            generalize_proofs at *; (
            exact h_closed.measurableSet)
          generalize_proofs at *; (
          convert h_union_measurable using 1 ; ext ; aesop)
        generalize_proofs at *; (
        by_cases h : x.fill t <;> simp_all +decide [ cechObservation ];
        · convert h_measurable using 1;
        · exact Measurable.not h_measurable)
      generalize_proofs at *; (
      have h_measurable : MeasurableSet {s : Fin n → Torus d | ∀ i j, (cechObservation r ⟨s⟩).edge i j = x.edge i j} ∧ MeasurableSet {s : Fin n → Torus d | ∀ t : {σ : Finset (Fin n) // σ.card = 3}, (cechObservation r ⟨s⟩).fill t = x.fill t} := by
        exact ⟨ by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by solve_by_elim, by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun t => by solve_by_elim ⟩
      generalize_proofs at *; (
      convert h_measurable.1.inter h_measurable.2 using 1
      generalize_proofs at *; (
      ext; simp [cechObservation];
      exact ⟨ fun h => ⟨ fun i j => by simpa using congr_arg ( fun f => f.edge i j ) h, fun a b => by simpa using congr_arg ( fun f => f.fill ⟨ a, b ⟩ ) h ⟩, fun h => by cases x; aesop ⟩ ;))))
    generalize_proofs at *; (
    convert h_preimage.preimage _ using 1
    generalize_proofs at *; (
    exact measurable_iff_comap_le.mpr le_rfl))
  exact h_preimage))
-/

-- `twoParamMeasure_isProbabilityMeasure` moved to `Core/Detection.lean` (phase A3.1).

-- The following three lemmas are moved up from below so that the Chebyshev /
-- Paley–Zygmund proofs that follow can cite them without forward reference.

lemma torus_pi_measure_real_univ' (d : ℕ) :
    (MeasureTheory.Measure.pi fun _ : Fin 3 =>
      (MeasureTheory.volume : MeasureTheory.Measure (Torus d))).real Set.univ = 1 := by
  rw [MeasureTheory.Measure.real]
  have h1 : (MeasureTheory.Measure.pi fun _ : Fin 3 =>
    (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) Set.univ = 1 := by
    erw [MeasureTheory.Measure.pi_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    erw [MeasureTheory.Measure.pi_univ]
    simp [AddCircle.measure_univ]
  rw [h1]; simp



open Classical in
/-- **fillingProb_nonneg.** The filling probability is nonneg. -/
lemma fillingProb_nonneg (p : ℝ) (d : ℕ) : 0 ≤ fillingProb p d := by
  unfold fillingProb
  apply MeasureTheory.integral_nonneg
  intro pts; simp only
  split_ifs <;> norm_num



open MeasureTheory in
open Classical in
/-- **fillingProb_le_one.** The filling probability is ≤ 1. -/
lemma fillingProb_le_one (p : ℝ) (d : ℕ) : fillingProb p d ≤ 1 := by
  unfold fillingProb
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const 1) ?_) ?_
  · exact Filter.Eventually.of_forall fun pts => by simp only; split_ifs <;> norm_num
  · exact Filter.Eventually.of_forall fun pts => by simp only; split_ifs <;> norm_num
  · simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact le_of_eq (torus_pi_measure_real_univ' d)



-- OQ-6 (session 97): `fillingProb_nonneg'` and `fillingProb_le_one'` deleted as dead
-- forward-reference workarounds; all callers now use `fillingProb_nonneg` / `fillingProb_le_one`.
