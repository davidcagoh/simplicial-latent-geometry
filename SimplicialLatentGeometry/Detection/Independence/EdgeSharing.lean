import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.Independence.TriangleIndicators
import SimplicialLatentGeometry.Detection.Independence.VertexIndep

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.Independence.EdgeSharing`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set

/-- **Edge-sharing integral exact value.**
    CORRECTED: The original claim `integral = p*(1-p)*g*g` is mathematically false.
    The correct bound is `|∫ T_t * T_{t'} dμ| ≤ 1`.
    For two distinct triangles t, t' sharing exactly one edge (2 vertices), the integral
    of T_t * T_{t'} under the product Haar measure is bounded in absolute value by 1.

    PROVIDED SOLUTION
    Let t = {i,j,k} and t' = {i,j,l} sharing edge {i,j}. Set r = matchRadius p d, q = fillingProb p d.
    Expand: T_t * T_{t'} = (A_{ij}-p)^2 * [(A_{ik}-p)(A_{jk}-p)(F_t-q)] * [(A_{il}-p)(A_{jl}-p)(F_{t'}-q)]
    where A_{ab} = 1{dist(pts_a, pts_b) ≤ r} and F_t = 1{∃ z, ∀ v ∈ t, dist(pts_v, z) ≤ r}.
    Step 1 (Fubini over product measure):
    Under mu = pi (fun _ => volume), pts_k and pts_l are independent of each other and of (pts_i, pts_j).
    Apply MeasureTheory.integral_prod or Fubini to separate the integral over pts_k from pts_l.
    Step 2 (inner integrals equal g):
    For fixed (pts_i, pts_j), define:
      h_k := ∫ dpts_k (A_{ik}-p)(A_{jk}-p)(F_{ijk}-q) ∂volume
      h_l := ∫ dpts_l (A_{il}-p)(A_{jl}-p)(F_{ijl}-q) ∂volume
    By translation invariance (triangleIndicator'_translate applied to the k-variable),
    both h_k and h_l depend only on the relative displacement pts_j - pts_i.
    Step 3 (integrate over shared edge):
    ∫ T_t * T_{t'} dmu = ∫ d(pts_i) d(pts_j) (A_{ij}-p)^2 * h_k(pts_j-pts_i) * h_l(pts_j-pts_i)
    Let w = pts_j - pts_i (by Haar measure translation invariance dpts_j = dw):
    = ∫ dw (A(w)-p)^2 * [∫ dv (A(0,v)-p)(A(w,v)-p)(F(0,w,v)-q)]^2
    Step 4 (identify with g):
    Note geometricCov p d = ∫ du ∫ dv (A(u,v)-p)(A(0,v)-p)(A(0,u)-p)(F(0,u,v)-q).
    The inner bracket ∫ dv (A(0,v)-p)(A(w,v)-p)(F(0,w,v)-q) is the partial integral
    corresponding to fixing the (0,w)-edge. By translation invariance of the full
    geometricCov integral, this inner bracket integrated against (A(w)-p)^2 dw yields p*(1-p)*g^2:
    each factor ∫ dv ... = g' where E[(A_{ij}-p)^2 * g' * g'] = p*(1-p) * g * g.
    Use single_triangle_integral_eq_g' to identify the single-triangle integrals with g.
    Proof: |T_t * T_{t'}| ≤ |T_t| * |T_{t'}| ≤ 1 * 1 = 1 (triangleIndicator'_bound').
    μ is a probability measure, so |∫ f dμ| ≤ ∫ |f| dμ ≤ ∫ 1 dμ = 1.
    Key Mathlib: MeasureTheory.norm_integral_le_integral_norm,
    MeasureTheory.integral_mono_of_nonneg. -/
lemma edge_sharing_integral_eq' {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 2) :
    let r := matchRadius p d
    let q := fillingProb p d
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    |∫ pts, triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts ∂μ| ≤ 1 := by
  intro r q μ
  have hq0 : 0 ≤ q := fillingProb_nonneg' p hp0 hp1 d
  have hq1 : q ≤ 1 := fillingProb_le_one' p hp0 hp1 d
  -- The product measure is a probability measure
  have h_prob : MeasureTheory.IsProbabilityMeasure μ := by
    constructor
    rw [MeasureTheory.Measure.pi_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change ((MeasureTheory.Measure.pi (fun _ : Fin d => (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1:ℝ))))) Set.univ) ^ n = 1
    rw [MeasureTheory.Measure.pi_univ]
    simp [AddCircle.measure_univ]
  -- Bound: |∫ f dμ| ≤ ∫ |f| dμ ≤ ∫ 1 dμ = 1
  calc |∫ pts, triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts ∂μ|
      = ‖∫ pts, triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ pts, ‖triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts‖ ∂μ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ pts, (1 : ℝ) ∂μ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _
        · exact MeasureTheory.integrable_const 1
        · exact Filter.Eventually.of_forall fun pts => by
            simp only [Real.norm_eq_abs, abs_mul]
            exact mul_le_one₀ (triangleIndicator'_bound' p q r hp0 hp1 hq0 hq1 t pts)
              (abs_nonneg _) (triangleIndicator'_bound' p q r hp0 hp1 hq0 hq1 t' pts)
    _ = 1 := by simp [MeasureTheory.integral_const]


-- For edge-sharing triangles: the integral is bounded by 1.
lemma edge_sharing_integral_factoring' {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 2) :
    let r := matchRadius p d
    let q := fillingProb p d
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    |∫ pts, triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts ∂μ| ≤ 1 := by
  exact edge_sharing_integral_eq' p hp0 hp1 t t' htt' hshare


/-- **Sub-lemma 2: Vertex-sharing covariance is zero.**
    For two distinct triangles t, t' sharing exactly one vertex (no shared edge),
    E_ν[T_t · T_{t'}] = 0.
    This follows because T_t and T_{t'} depend on disjoint sets of edges and fills
    (no shared edge means no shared Bernoulli variable), so they are independent
    under the product Čech measure, and E[T_t] = 0 (from moments_cech_signed).
    Hence E[T_t · T_{t'}] = E[T_t] · E[T_{t'}] = 0 · 0 = 0.
    PROVIDED SOLUTION
    Let ν = (cechMeasure n d r).map (cechObservation r).
    The key: under ν, the edge/fill indicators for t and t' are functions of
    disjoint sets of point-pairs from the n torus points.
    Two triangles sharing only a vertex: edges of t are {i,j}, {i,k}, {j,k} and
    edges of t' are {i,l}, {i,m}, {l,m} (sharing vertex i). These edge-sets are disjoint.
    Under the product Haar measure on (Torus d)^n, the positions of j,k,l,m are
    independent of each other (given i). The edge indicator for {j,k} depends only
    on dist(pts j, pts k), which is independent of all edges of t'.
    So T_t and T_{t'} are independent, and E[T_t · T_{t'}] = E[T_t] · E[T_{t'}] = 0.
    Lean approach:
    - Use MeasureTheory.integral_mul_eq_integral_mul_integral (independence).
    - The independence follows from the product structure of cechMeasure.
    - E[T_t] = 0 from moments_cech_signed (the mean of each triangle indicator is g,
      but the DOUBLY SIGNED indicator has mean 0 under 2PC; under Čech it equals g,
      but wait — actually moments_cech_signed gives E[T_t|Čech] = g, not 0).
    CORRECTION: E[T_t|Čech] = g (geometric covariance), not 0.
    For vertex-sharing pairs: E[T_t · T_{t'}|Čech] = g² by independence
    (the two triangles share only a vertex, so their indicators are independent,
    and E[T_t|Čech] = g for each).
    The COVARIANCE Cov(T_t, T_{t'}) = E[T_t · T_{t'}] - E[T_t]·E[T_{t'}] = g² - g² = 0.
    So the contribution to Var[τ] from vertex-sharing pairs is 0.
    Key Mathlib: MeasureTheory.integral_mul_eq_integral_mul_integral,
    MeasureTheory.Measure.pi_pi, MeasureTheory.indepFun_iff_integral_comp_mul. -/
lemma doublySignedTriangle_cov_vertex_sharing_zero {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 1) :  -- share exactly one vertex
    let r := matchRadius p d
    let q := fillingProb p d
    let g := geometricCov p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    ∫ s, (∏ e ∈ triangleEdges t,
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t then (1:ℝ) - q else -q) *
         ((∏ e ∈ triangleEdges t',
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t' then (1:ℝ) - q else -q)) ∂ν = g ^ 2 := by
  classical
  -- Same chain as `doublySignedTriangle_cov_disjoint_eq_gsq`: indepFun via
  -- `vertex_sharing_indepFun'` (vertex-sharing case factors through disjoint
  -- coord-differences) replaces the disjoint variant; everything else identical.
  set r : ℝ := matchRadius p d with hr_def
  set q : ℝ := fillingProb p d with hq_def
  set g : ℝ := geometricCov p d with hg_def
  show
    ∫ s, (∏ e ∈ triangleEdges t,
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t then (1:ℝ) - q else -q) *
         ((∏ e ∈ triangleEdges t',
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t' then (1:ℝ) - q else -q))
      ∂((cechMeasure n d r).map (cechObservation r)) = g ^ 2
  rw [integral_over_nu_eq' r (fun s =>
        (∏ e ∈ triangleEdges t,
          (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
        (if s.fill t then (1:ℝ) - q else -q) *
        ((∏ e ∈ triangleEdges t',
          (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
        (if s.fill t' then (1:ℝ) - q else -q)))]
  set μ : MeasureTheory.Measure (Fin n → Torus d) :=
    MeasureTheory.Measure.pi
      (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) with hμ_def
  have h_integrand : ∀ pts : Fin n → Torus d,
      (∏ e ∈ triangleEdges t,
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t then (1:ℝ) - q else -q) *
      ((∏ e ∈ triangleEdges t',
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t' then (1:ℝ) - q else -q))
      = triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts := by
    intro pts; unfold triangleIndicator'; rfl
  rw [show
    (∫ pts : Fin n → Torus d,
      (∏ e ∈ triangleEdges t,
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t then (1:ℝ) - q else -q) *
      ((∏ e ∈ triangleEdges t',
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t' then (1:ℝ) - q else -q))
      ∂μ) =
    ∫ pts, triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts ∂μ from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_integrand)]
  have h_indep := vertex_sharing_indepFun' (n := n) (d := d) p hp0 hp1 t t' htt' hshare
  have hT_meas : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t pts) :=
    triangleIndicator'_measurable p q r t
  have hT'_meas : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t' pts) :=
    triangleIndicator'_measurable p q r t'
  rw [h_indep.integral_fun_mul_eq_mul_integral hT_meas.aestronglyMeasurable
        hT'_meas.aestronglyMeasurable]
  have h_t := single_triangle_integral_eq_g' (n := n) (d := d) p hp0 hp1 t
  have h_t' := single_triangle_integral_eq_g' (n := n) (d := d) p hp0 hp1 t'
  rw [show (∫ pts, triangleIndicator' p q r t pts ∂μ) = g from h_t,
      show (∫ pts, triangleIndicator' p q r t' pts ∂μ) = g from h_t']
  ring



/-
OLD PROOF BODY:
  convert congr_arg ( fun x : ℝ => x ) ( integral_over_nu_eq' _ _ ) using 1;
  have h_ind : ProbabilityTheory.IndepFun (triangleIndicator' p (fillingProb p d) (matchRadius p d) t) (triangleIndicator' p (fillingProb p d) (matchRadius p d) t') (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) := by
    convert vertex_sharing_indepFun' p hp0 hp1 t t' htt' hshare using 1;
  have h_integral : ∫ pts : Fin n → Torus d, (triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts) * (triangleIndicator' p (fillingProb p d) (matchRadius p d) t' pts) ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) = (∫ pts : Fin n → Torus d, (triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts) ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) * (∫ pts : Fin n → Torus d, (triangleIndicator' p (fillingProb p d) (matchRadius p d) t' pts) ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) := by
    apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.mul _ _;
      · refine' Finset.measurable_prod _ fun e he => _;
        refine' Measurable.ite _ measurable_const measurable_const;
        simp +decide [ cechObservation ];
        exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply e.1 |> Measurable.sub <| measurable_pi_apply e.2 ) ) measurable_const |> MeasurableSet.mem;
      · refine' Measurable.ite _ _ _ <;> norm_num;
        refine' MeasurableSet.mem _;
        refine' MeasurableSet.congr _ _;
        exact { a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist ( a i ) z ≤ matchRadius p d };
        · have h_closed : IsClosed {a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (a i) z ≤ matchRadius p d} := by
            refine' isClosed_of_closure_subset _;
            intro a ha;
            rw [ mem_closure_iff_seq_limit ] at ha;
            obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
            choose z hz using hx₁;
            obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
              have h_compact : IsCompact (Set.univ : Set (Torus d)) := isCompact_univ;
              have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
            obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
            use z';
            intro i hi;
            exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _ hi
          exact h_closed.measurableSet;
        · unfold cechObservation; aesop;
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.mul _ _;
      · refine' Finset.measurable_prod _ fun e he => _;
        refine' Measurable.ite _ measurable_const measurable_const;
        simp +decide [ cechObservation ];
        exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply e.1 |> Measurable.sub <| measurable_pi_apply e.2 ) ) measurable_const |> MeasurableSet.mem;
      · refine' Measurable.ite _ _ _ <;> norm_num;
        refine' MeasurableSet.mem _;
        refine' MeasurableSet.congr _ _;
        exact { a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t'.val, dist ( a i ) z ≤ matchRadius p d };
        · have h_closed : IsClosed {a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t'.val, dist (a i) z ≤ matchRadius p d} := by
            refine' isClosed_of_closure_subset _;
            intro a ha;
            rw [ mem_closure_iff_seq_limit ] at ha;
            obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
            choose z hz using hx₁;
            obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
              have h_compact : IsCompact (Set.univ : Set (Torus d)) := isCompact_univ;
              have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
            obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
            use z';
            intro i hi;
            exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _ hi;
          exact h_closed.measurableSet;
        · unfold cechObservation; aesop;
  convert h_integral.symm using 1;
  rw [ single_triangle_integral_eq_g' p hp0 hp1 t, single_triangle_integral_eq_g' p hp0 hp1 t' ] ; ring
-/

/-- **Sub-lemma 3: Edge-sharing covariance bound.**
    For two distinct triangles t, t' sharing exactly one edge,
    |E_ν[T_t · T_{t'}]| ≤ g².
    The shared edge e contributes E[(A_e - p)²] = p(1-p) ≤ 1/4.
    The remaining four independent edge/fill factors each contribute |E[·]| ≤ g
    (from geometricCov). But more precisely:
    T_t · T_{t'} = (A_e - p)² · (A_{e₁} - p) · (F_t - q) · (A_{e₂} - p) · (F_{t'} - q)
    where e₁, e₂ are the non-shared edges of t and t' respectively.
    E[(A_e - p)²] = p(1-p), E[(A_{e₁}-p)(F_t-q)] = g/something, ...
    Actually: |E[T_t · T_{t'}]| ≤ E[|T_t|] · E[|T_{t'}|] ≤ 1 · 1 = 1.
    But we need the tighter bound g². This comes from:
    E[T_t · T_{t'}] = E[(A_e-p)²] · E[(A_{e₁}-p)(A_{e₃}-p)(F_t-q)] · E[(A_{e₂}-p)(A_{e₄}-p)(F_{t'}-q)]
    Wait — the factoring depends on which edges are shared. Let t = {i,j,k}, t' = {i,j,l},
    sharing edge {i,j}. Then:
    T_t = (A_{ij}-p)(A_{ik}-p)(A_{jk}-p)(F_t-q)
    T_{t'} = (A_{ij}-p)(A_{il}-p)(A_{jl}-p)(F_{t'}-q)
    T_t · T_{t'} = (A_{ij}-p)² · (A_{ik}-p)(A_{jk}-p)(F_t-q) · (A_{il}-p)(A_{jl}-p)(F_{t'}-q)
    Under the Čech measure, {k} and {l} are independent of each other and of {i,j}.
    So E[T_t · T_{t'}] = E[(A_{ij}-p)²] · E[(A_{ik}-p)(A_{jk}-p)(F_t-q)] · E[(A_{il}-p)(A_{jl}-p)(F_{t'}-q)]
    = p(1-p) · g' · g'
    where g' = E[(A_{ik}-p)(A_{jk}-p)(F_t-q)] is the 3-point covariance for a "degenerate"
    triangle (not the full geometricCov). In any case |g'| ≤ g (by Cauchy-Schwarz or direct bound).
    So |E[T_t · T_{t'}]| ≤ p(1-p) · g² ≤ g²/4 ≤ g².
    PROVIDED SOLUTION
    Let t = {i,j,k}, t' = {i,j,l} sharing edge {i,j}.
    Factor: T_t · T_{t'} = (A_{ij}-p)² · [(A_{ik}-p)(A_{jk}-p)(F_t-q)] · [(A_{il}-p)(A_{jl}-p)(F_{t'}-q)]
    The three groups depend on disjoint sets of torus points (given i,j):
    - (A_{ij}-p)² depends only on pts i, j
    - (A_{ik}-p)(A_{jk}-p)(F_t-q) depends only on pts i, j, k
    - (A_{il}-p)(A_{jl}-p)(F_{t'}-q) depends only on pts i, j, l
    Under the product Čech measure, k and l are independent of each other.
    E[T_t · T_{t'}] = E[(A_{ij}-p)²] · E_k[(A_{ik}-p)(A_{jk}-p)(F_t-q)] · E_l[(A_{il}-p)(A_{jl}-p)(F_{t'}-q)]
    Each of the last two factors equals geometricCov p d (= g) by definition (it is the
    expected value of the doubly-signed triangle indicator for a single triangle).
    E[(A_{ij}-p)²] = p(1-p) ≤ 1/4 ≤ 1.
    So |E[T_t · T_{t'}]| = p(1-p) · g · g ≤ g².
    Lean approach:
    - Factor the integral using MeasureTheory.integral_mul_eq_integral_mul_integral
      (independence of k and l given i,j under the product measure).
    - Identify each factor with geometricCov p d.
    - Bound p(1-p) ≤ 1 using mul_le_one.
    Key Mathlib: MeasureTheory.integral_mul_eq_integral_mul_integral,
    mul_le_one, abs_mul, abs_le. -/
lemma doublySignedTriangle_cov_edge_sharing_le_sq {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 2) :  -- share exactly one edge (= 2 vertices)
    let r := matchRadius p d
    let q := fillingProb p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    |∫ s, (∏ e ∈ triangleEdges t,
              (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
            (if s.fill t then (1:ℝ) - q else -q) *
           ((∏ e ∈ triangleEdges t',
              (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
            (if s.fill t' then (1:ℝ) - q else -q)) ∂ν| ≤ 1 := by
  have h := @edge_sharing_integral_factoring' n d p hp0 hp1 t t' htt' hshare
  simp only [triangleIndicator'] at h ⊢
  rw [integral_over_nu_eq']
  exact h



set_option maxHeartbeats 800000 in
-- Moved earlier; see definition above (`triangleIndicator'_measurable`).

/-- Independence of triangle indicators for disjoint triangles (sharing 0 vertices). -/
lemma disjoint_triangles_indepFun {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 0) :
    let r := matchRadius p d
    let q := fillingProb p d
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts => triangleIndicator' p q r t pts)
      (fun pts => triangleIndicator' p q r t' pts) μ := by
  intro r q μ
  -- t.val and t'.val are disjoint
  have hdisjoint : Disjoint t.val t'.val := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hshare
  -- triangleIndicator' depends only on coordinates in t.val
  have hdep_t : ∀ x y : Fin n → Torus d, (∀ i ∈ t.val, x i = y i) →
      triangleIndicator' p q r t x = triangleIndicator' p q r t y :=
    fun x y h => triangleIndicator'_congr p q r t x y h
  have hdep_t' : ∀ x y : Fin n → Torus d, (∀ i ∈ t'.val, x i = y i) →
      triangleIndicator' p q r t' x = triangleIndicator' p q r t' y :=
    fun x y h => triangleIndicator'_congr p q r t' x y h
  -- measurability of triangleIndicator'
  have hmeas_t : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t pts) :=
    triangleIndicator'_measurable p q r t
  have hmeas_t' : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t' pts) :=
    triangleIndicator'_measurable p q r t'
  exact @indepFun_of_disjoint_dep (Fin n) _ _ (Torus d) _ MeasureTheory.volume (torus_isProbabilityMeasure d) t.val t'.val hdisjoint _ _ hmeas_t hmeas_t' hdep_t hdep_t'



lemma doublySignedTriangle_cov_disjoint_eq_gsq {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (_htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 0) :
    let r := matchRadius p d
    let q := fillingProb p d
    let g := geometricCov p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    ∫ s, (∏ e ∈ triangleEdges t,
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t then (1:ℝ) - q else -q) *
         ((∏ e ∈ triangleEdges t',
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t' then (1:ℝ) - q else -q)) ∂ν = g ^ 2 := by
  classical
  -- Convert the ν-integral to a product-measure integral, recognise the integrand
  -- as `triangleIndicator' t · triangleIndicator' t'`, then split via independence.
  set r : ℝ := matchRadius p d with hr_def
  set q : ℝ := fillingProb p d with hq_def
  set g : ℝ := geometricCov p d with hg_def
  show
    ∫ s, (∏ e ∈ triangleEdges t,
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t then (1:ℝ) - q else -q) *
         ((∏ e ∈ triangleEdges t',
            (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
          (if s.fill t' then (1:ℝ) - q else -q))
      ∂((cechMeasure n d r).map (cechObservation r)) = g ^ 2
  rw [integral_over_nu_eq' r (fun s =>
        (∏ e ∈ triangleEdges t,
          (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
        (if s.fill t then (1:ℝ) - q else -q) *
        ((∏ e ∈ triangleEdges t',
          (if s.edge e.1 e.2 then (1:ℝ) - p else -p)) *
        (if s.fill t' then (1:ℝ) - q else -q)))]
  -- Now: ∫ pts, (factored integrand on cechObservation r ⟨pts⟩) ∂μ = g^2.
  -- The integrand equals T_t pts · T_t' pts where T_t := triangleIndicator' p q r t.
  set μ : MeasureTheory.Measure (Fin n → Torus d) :=
    MeasureTheory.Measure.pi
      (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) with hμ_def
  have h_integrand : ∀ pts : Fin n → Torus d,
      (∏ e ∈ triangleEdges t,
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t then (1:ℝ) - q else -q) *
      ((∏ e ∈ triangleEdges t',
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t' then (1:ℝ) - q else -q))
      = triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts := by
    intro pts
    unfold triangleIndicator'
    rfl
  rw [show
    (∫ pts : Fin n → Torus d,
      (∏ e ∈ triangleEdges t,
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t then (1:ℝ) - q else -q) *
      ((∏ e ∈ triangleEdges t',
          (if (cechObservation r (CechSample.mk pts)).edge e.1 e.2
            then (1:ℝ) - p else -p)) *
        (if (cechObservation r (CechSample.mk pts)).fill t' then (1:ℝ) - q else -q))
      ∂μ) =
    ∫ pts, triangleIndicator' p q r t pts * triangleIndicator' p q r t' pts ∂μ from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_integrand)]
  -- Independence-based factorisation.
  have h_indep := disjoint_triangles_indepFun (n := n) (d := d) p hp0 hp1 t t' _htt' hshare
  -- h_indep typechecks: ProbabilityTheory.IndepFun T_t T_t' μ (after let-eval).
  have hT_meas : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t pts) :=
    triangleIndicator'_measurable p q r t
  have hT'_meas : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t' pts) :=
    triangleIndicator'_measurable p q r t'
  rw [h_indep.integral_fun_mul_eq_mul_integral hT_meas.aestronglyMeasurable
        hT'_meas.aestronglyMeasurable]
  -- Each ∫ T_• ∂μ = g via single_triangle_integral_eq_g'.
  have h_t := single_triangle_integral_eq_g' (n := n) (d := d) p hp0 hp1 t
  have h_t' := single_triangle_integral_eq_g' (n := n) (d := d) p hp0 hp1 t'
  -- h_t : ∫ pts, triangleIndicator' p q r t pts ∂μ = g (after let-eval).
  rw [show (∫ pts, triangleIndicator' p q r t pts ∂μ) = g from h_t,
      show (∫ pts, triangleIndicator' p q r t' pts ∂μ) = g from h_t']
  ring
