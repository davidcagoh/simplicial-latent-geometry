import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.Core.MeasureScaffold`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


open Classical in
/-- Filled triangle count in a Čech sample: triangles whose r-balls have a common point. -/
noncomputable def cechFilledCount {n d : ℕ} (s : CechSample n d) (r : ℝ) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    if s.hasFill r t then (1 : ℝ) else 0



/-- Čech(n,r,d) probability measure: n i.i.d. uniform points on the torus T^d.
    Defined as the pullback (comap) of the product Haar measure through the
    `CechSample.points` projection. The radius parameter `r` does not affect the
    point distribution; it only determines the simplicial complex structure. -/
noncomputable def cechMeasure (n d : ℕ) (_r : ℝ) :
    MeasureTheory.Measure (CechSample n d) :=
  MeasureTheory.Measure.comap CechSample.points
    (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))))



-- CORRECTED: The original variance formula `C(n,3) * p³q * (1 - p³q)` is incorrect for n ≥ 4.
-- Two distinct triangles sharing an edge (e.g. {i,j,k} and {i,j,l}) use the same edge
-- Bernoulli variable edge(i,j), creating positive covariance:
--   Cov[I_t₁, I_t₂] = p⁵q² - p⁶q² = p⁵q²(1-p)  when t₁,t₂ share one edge.
-- The number of ordered pairs of distinct triangles sharing one edge is 12·C(n,4).
-- Numerical verification (n=4, p=q=1/2): claimed Var = 7/16, actual Var = 5/8.
--
-- The original statement was:
--   variance filledTriangleCount (twoParamMeasure n p q) =
--     (n.choose 3 : ℝ) * p ^ 3 * q * (1 - p ^ 3 * q)
-- This is commented out below and replaced with the corrected formula.

/-! **Lemma 3 (Moments under 2PC, corrected).** Under 2PC(n, p, q):
      𝔼[Δ_f] = C(n,3) · p³ · q
      Var[Δ_f] = C(n,3) · p³q · (1 - p³q) + 12 · C(n,4) · p⁵ · q² · (1 - p)

    The mean follows from linearity of expectation: each triangle indicator
    I_t = edge(ij)·edge(ik)·edge(jk)·fill(t) has E[I_t] = p³q.

    The variance has two contributions:
    • Diagonal: C(n,3) individual Bernoulli variances p³q(1-p³q).
    • Off-diagonal: 12·C(n,4) ordered pairs of triangles sharing one edge contribute
      covariance p⁵q²(1-p) each, since the shared edge variable appears in both indicators.

    **Modification from original:** added the covariance term
    `12 * C(n,4) * p^5 * q^2 * (1-p)` which was missing in the original statement. -/

-- `twoParamMeasure_totalMass` moved to `Core/Detection.lean` (phase A3.1).

/-
PROVIDED SOLUTION
The key insight: filledTriangleCount is a finite sum over triangles, so the integral decomposes as a sum of integrals by linearity. For each triangle t, the integral of its indicator I_t = (fill(t) indicator) * (product of edge indicators) against the Bernoulli product measure factors into p^3 * q. Summing over all C(n,3) triangles gives C(n,3)*p^3*q.

Step-by-step:
1. Unfold filledTriangleCount as ∑ t, I_t(s)
2. Use MeasureTheory.integral_finset_sum to exchange ∫ and ∑
3. For each triangle t, compute ∫ I_t(s) ∂μ:
   a. Convert integral to lintegral (since I_t ≥ 0)
   b. Use lintegral_withDensity_eq_lintegral_mul
   c. Use lintegral_count to convert to tsum
   d. Factor the tsum into independent products: edge contributions and fill contributions
   e. Each edge in the triangle contributes factor p, others contribute 1
   f. Fill for t contributes factor q, others contribute 1
   g. Total: p^3 * q
4. Sum of C(n,3) copies of p^3*q = C(n,3)*p^3*q

The factoring of the tsum is the hardest part. The key identity is:
∑_{(edge,fill)} f(edge)*g(fill) = (∑_edge f(edge))*(∑_fill g(fill))
and within the edge sum, the product over independent coordinates factors.
-/
set_option maxHeartbeats 800000 in
open MeasureTheory ProbabilityTheory in
/-- Mean of filledTriangleCount under 2PC. -/
lemma moments_twoParam_mean (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, filledTriangleCount s ∂twoParamMeasure n p q = (n.choose 3 : ℝ) * p ^ 3 * q := by
  unfold filledTriangleCount;
  rw [ MeasureTheory.integral_finset_sum ];
  · -- For each triangle $t$, the integral of its indicator function is $p^3 q$.
    have h_indicator : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, ∫ s : TwoParamSample n, (if s.fill t then 1 else 0) * (∏ e ∈ triangleEdges t, if s.edge e.1 e.2 then 1 else 0) ∂twoParamMeasure n p q = p ^ 3 * q := by
      intro t
      have h_triangle : ∫ s : TwoParamSample n, (if s.fill t then (1 : ℝ) else 0) * ∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then 1 else 0) ∂twoParamMeasure n p q = (∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if s i j then p else 1 - p) * (∏ e ∈ triangleEdges t, if s e.1 e.2 then 1 else 0)) * (∑ s : {s : Finset (Fin n) // s.card = 3} → Bool, (∏ t : {s : Finset (Fin n) // s.card = 3}, if s t then q else 1 - q) * (if s t then 1 else 0)) := by
        rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
        · rw [ twoParamMeasure ];
          rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
          · rw [ MeasureTheory.lintegral_count ];
            rw [ show ( ∑' a : TwoParamSample n, _ ) = ∑' a : ( Fin n → Fin n → Bool ) × ( { s : Finset ( Fin n ) // s.card = 3 } → Bool ), _ from ?_ ];
            rotate_left;
            use fun a => ENNReal.ofReal ( ( ∏ i, ∏ j, if a.1 i j = true then p else 1 - p ) * ( ∏ t, if a.2 t = true then q else 1 - q ) * ( if a.2 t = true then 1 else 0 ) * ( ∏ e ∈ triangleEdges t, if a.1 e.1 e.2 = true then 1 else 0 ) );
            · rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun a : TwoParamSample n => ( a.edge, a.fill ) ) ⟨ fun a => _, fun a => _ ⟩ ) ];
              congr! 1;
              ext; simp [ENNReal.ofReal_mul, ENNReal.ofReal_prod_of_nonneg];
              all_goals norm_num [ ENNReal.ofReal_mul, hp, hp1, hq, hq1 ];
              any_goals intro a b ha hb; cases a; cases b; congr! 1;
              split_ifs <;> simp +decide [ *, ENNReal.ofReal_mul, Finset.prod_ite ];
              · rw [ ENNReal.ofReal_mul, ENNReal.ofReal_mul ] <;> norm_num [ hp, hp1, hq, hq1 ];
                · rw [ ENNReal.ofReal_prod_of_nonneg ] ; aesop;
                  exact fun _ _ => mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ );
                · exact Finset.prod_nonneg fun _ _ => mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ );
                · exact mul_nonneg ( Finset.prod_nonneg fun _ _ => mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ ) ) ( mul_nonneg ( pow_nonneg hq _ ) ( pow_nonneg ( sub_nonneg.2 hq1 ) _ ) );
              · exact fun a b => ⟨ ⟨ a, b ⟩, rfl, rfl ⟩;
            · rw [ ENNReal.tsum_toReal_eq ];
              · erw [ Summable.tsum_prod ];
                · rw [ tsum_fintype, Finset.sum_mul ];
                  refine' Finset.sum_congr rfl fun i hi => _;
                  rw [ tsum_fintype ];
                  rw [ Finset.mul_sum _ _ _ ];
                  refine' Finset.sum_congr rfl fun j hj => _;
                  rw [ ENNReal.toReal_ofReal ] <;> norm_num [ mul_assoc, mul_comm, mul_left_comm ];
                  split_ifs <;> first | positivity | exact mul_nonneg ( Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) ( mul_nonneg ( Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) ( Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) ) ;
                · exact ⟨ _, hasSum_fintype _ ⟩;
              · exact fun a => ENNReal.ofReal_ne_top;
          · fun_prop (disch := norm_num);
          · fun_prop;
        · exact Filter.Eventually.of_forall fun s => mul_nonneg ( by positivity ) ( Finset.prod_nonneg fun _ _ => by positivity );
        · refine' Measurable.aestronglyMeasurable _;
          fun_prop (disch := solve_by_elim);
      -- Let's simplify the expression for the expected value of the product of edge indicators.
      have h_edge_prod : ∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if s i j then p else 1 - p) * (∏ e ∈ triangleEdges t, if s e.1 e.2 then 1 else 0) = p ^ (triangleEdges t).card * (∏ i : Fin n, ∏ j : Fin n, if i = j then 1 else 1) := by
        have h_edge_prod : ∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if s i j then p else 1 - p) * (∏ e ∈ triangleEdges t, if s e.1 e.2 then 1 else 0) = ∏ e ∈ Finset.univ ×ˢ Finset.univ, (∑ s : Bool, if e ∈ triangleEdges t then if s then p else 0 else if s then p else 1 - p) := by
          rw [ Finset.prod_sum ];
          refine' Finset.sum_bij ( fun s _ => fun e _ => s e.1 e.2 ) _ _ _ _ <;> simp +decide;
          · simp +decide [ funext_iff ];
          · exact fun b => ⟨ fun i j => b ( i, j ) ( Finset.mem_univ _ ), rfl ⟩;
          · intro a; rw [ ← Finset.prod_product' ] ; simp +decide [ Finset.prod_ite ] ;
            simp +decide [ Finset.filter_not, Finset.card_sdiff ] ; ring;
            rw [ show ( Finset.filter ( fun x => a x.1 x.2 = true ) ( Finset.univ : Finset ( Fin n × Fin n ) ) ) = Finset.filter ( fun x => a x.1 x.2 = true ) ( triangleEdges t ) ∪ Finset.filter ( fun x => a x.1 x.2 = true ) ( Finset.univ \ triangleEdges t ) from ?_, show ( Finset.filter ( fun x => a x.1 x.2 = false ) ( Finset.univ : Finset ( Fin n × Fin n ) ) ) = Finset.filter ( fun x => a x.1 x.2 = false ) ( triangleEdges t ) ∪ Finset.filter ( fun x => a x.1 x.2 = false ) ( Finset.univ \ triangleEdges t ) from ?_ ];
            · rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num [ Finset.disjoint_left ] ; ring;
              · by_cases h : Finset.card ( Finset.filter ( fun x => a x.1 x.2 = false ) ( triangleEdges t ) ) = 0 <;> simp +decide [ h ];
              · tauto;
              · tauto;
            · grind +ring;
            · grind;
        simp +zetaDelta at *;
        convert h_edge_prod using 1;
      -- Let's simplify the expression for the expected value of the fill indicator.
      have h_fill_indicator : ∑ s : {s : Finset (Fin n) // s.card = 3} → Bool, (∏ t : {s : Finset (Fin n) // s.card = 3}, if s t then q else 1 - q) * (if s t then 1 else 0) = q * (∏ t : {s : Finset (Fin n) // s.card = 3}, if t = t then 1 else 1) := by
        have h_fill_indicator : ∀ (f : {s : Finset (Fin n) // s.card = 3} → Bool → ℝ), (∑ s : {s : Finset (Fin n) // s.card = 3} → Bool, (∏ t : {s : Finset (Fin n) // s.card = 3}, f t (s t))) = (∏ t : {s : Finset (Fin n) // s.card = 3}, (∑ s : Bool, f t s)) := by
          exact?;
        convert h_fill_indicator ( fun u s => if u = t then ( if s then q else 1 - q ) * ( if s then 1 else 0 ) else ( if s then q else 1 - q ) ) using 1;
        · refine' Finset.sum_congr rfl fun s hs => _;
          rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ t ) ] ; simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ] ; ring;
          by_cases h : s t <;> simp +decide [ h ];
          simp +decide [ Finset.filter_singleton, h ];
          rw [ Finset.sdiff_singleton_eq_erase ];
        · rw [ Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_univ t ] ; norm_num;
      -- Let's simplify the expression for the cardinality of the set of edges in the triangle.
      have h_card_edges : (triangleEdges t).card = 3 := by
        rcases t with ⟨ t, ht ⟩ ; simp +decide [ triangleEdges ] ;
        rw [ Finset.card_eq_three ] at ht;
        rcases ht with ⟨ x, y, z, hxy, hxz, hyz, rfl ⟩ ; simp +decide [ Finset.filter, hxy, hxz, hyz ] ;
        simp +decide [ Multiset.filter_cons, Multiset.filter_singleton ];
        cases lt_or_gt_of_ne hxy <;> cases lt_or_gt_of_ne hxz <;> cases lt_or_gt_of_ne hyz <;> simp +decide [ * ];
        all_goals simp +decide [ *, not_lt_of_gt ] ;
      aesop;
    simp_all +decide [ mul_assoc ];
  · refine' fun t _ => MeasureTheory.Integrable.mono' _ _ _;
    any_goals exact fun _ _ _ => 1;
    · apply_rules [ MeasureTheory.integrable_const ];
      constructor;
      convert twoParamMeasure_totalMass n p q hp hp1 hq hq1 |> fun h => h.trans_lt ENNReal.one_lt_top;
    · refine' Measurable.aestronglyMeasurable _;
      fun_prop;
    · filter_upwards [ ] with s using by split_ifs <;> norm_num ; exact Finset.prod_le_one ( fun _ _ => by split_ifs <;> norm_num ) fun _ _ => by split_ifs <;> norm_num;



-- DEPRECATED (Strategy 1): `moments_cech` and its wrappers `cechFilledCount_integral`
-- / `cechFilledCount_variance` were removed 2026-05-19 (session 77 follow-up). They had
-- no downstream callers; the Strategy 2 replacement is `moments_cech_signed`.

/-- **Definition 6 (Signed Filled Triangle Statistic).**
    Δ̃_f(s) = Δ_f(s) − 𝔼_2PC[Δ_f] = filledTriangleCount s − C(n,3) p³q. -/
noncomputable def signedFilledCount (n : ℕ) (p q : ℝ) (s : TwoParamSample n) : ℝ :=
  filledTriangleCount s - (n.choose 3 : ℝ) * p ^ 3 * q



open Classical in
/-- Signed filled triangle count under the Čech model:
    Δ̃_f(s) = cechFilledCount s r − C(n,3) p³q. -/
noncomputable def cechSignedCount (n d : ℕ) (p q : ℝ) (s : CechSample n d) (r : ℝ) : ℝ :=
  cechFilledCount s r - (n.choose 3 : ℝ) * p ^ 3 * q



open Classical in
/-- The observed simplicial complex from a Čech sample: read off edge and fill indicators. -/
noncomputable def cechObservation {n d : ℕ} (r : ℝ) (s : CechSample n d) : TwoParamSample n where
  edge := fun i j => decide (s.hasEdge r i j)
  fill := fun t => decide (s.hasFill r t)



/-- The Čech measure is a probability measure (product of Haar probability measures).
    Uses isProbabilityMeasure_comap with CechSample.points injective and surjective. -/
instance cechMeasure_isProbabilityMeasure (n d : ℕ) (r : ℝ) :
    MeasureTheory.IsProbabilityMeasure (cechMeasure n d r) := by
  unfold cechMeasure
  generalize_proofs at *;
  constructor;
  rw [MeasureTheory.Measure.comap_apply];
  · erw [show (CechSample.points '' Set.univ : Set (Fin n → Torus d)) = Set.univ from
        Set.eq_univ_of_forall fun x => ⟨⟨x⟩, Set.mem_univ _, rfl⟩];
    erw [MeasureTheory.Measure.pi_univ]; norm_num;
  · exact fun x y h => by cases x; cases y; aesop;
  · intro s hs;
    obtain ⟨t, ht, rfl⟩ := hs;
    rw [Set.image_preimage_eq_inter_range];
    exact MeasurableSet.inter ht (by
      rw [show Set.range CechSample.points = Set.univ from
            Set.eq_univ_of_forall fun x => ⟨⟨x⟩, rfl⟩];
      exact MeasurableSet.univ);
  · exact MeasurableSet.univ



/-- Under the comap sigma-algebra, `s.hasFill r t` is a finite intersection of
    closed preimages `{s | dist (s.points i) (s.points j) ≤ r}`. CechSample-level
    version of `DisjointTriangles.measurableSet_hasFill`. -/
lemma measurableSet_cechSample_hasFill (n d : ℕ) (r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    MeasurableSet {s : CechSample n d | s.hasFill r t} := by
  have h_rewrite : {s : CechSample n d | s.hasFill r t} =
      ⋂ i ∈ t.val, ⋂ j ∈ t.val,
        {s : CechSample n d | dist (s.points i) (s.points j) ≤ r} := by
    ext s; simp [CechSample.hasFill]
  rw [h_rewrite]
  -- Under the comap MS, a preimage of a measurable target set is measurable.
  have h_points_meas : Measurable (CechSample.points : CechSample n d → Fin n → Torus d) :=
    fun x hx => ⟨x, hx, rfl⟩
  refine MeasurableSet.biInter t.val.countable_toSet (fun i _ => ?_)
  refine MeasurableSet.biInter t.val.countable_toSet (fun j _ => ?_)
  exact measurableSet_le
    (((measurable_pi_apply i).comp h_points_meas).dist
      ((measurable_pi_apply j).comp h_points_meas))
    measurable_const



/-- The Rips observation map `cechObservation r : CechSample n d → TwoParamSample n`
    is measurable. Since `TwoParamSample n` has the discrete σ-algebra (and is finite,
    hence countable), it suffices to show that each singleton preimage is measurable;
    that preimage is a finite intersection of `hasEdge` / `hasFill` sets (and their
    complements), all of which are measurable in the comap σ-algebra on `CechSample n d`. -/
lemma cechObservation_measurable {n d : ℕ} (r : ℝ) :
    Measurable (cechObservation r : CechSample n d → TwoParamSample n) := by
  classical
  have h_points_meas : Measurable (CechSample.points : CechSample n d → Fin n → Torus d) :=
    fun _ hx => ⟨_, hx, rfl⟩
  have h_hasEdge : ∀ i j : Fin n, MeasurableSet {s : CechSample n d | s.hasEdge r i j} := by
    intro i j
    exact measurableSet_le
      (((measurable_pi_apply i).comp h_points_meas).dist
        ((measurable_pi_apply j).comp h_points_meas))
      measurable_const
  refine measurable_to_countable' (fun x => ?_)
  have h_eq : (cechObservation r) ⁻¹' {x} =
      (⋂ i : Fin n, ⋂ j : Fin n,
        {s : CechSample n d | decide (s.hasEdge r i j) = x.edge i j}) ∩
      (⋂ t : {σ : Finset (Fin n) // σ.card = 3},
        {s : CechSample n d | decide (s.hasFill r t) = x.fill t}) := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨fun i j => ?_, fun t => ?_⟩
      · exact congrArg (fun y : TwoParamSample n => y.edge i j) h
      · exact congrArg (fun y : TwoParamSample n => y.fill t) h
    · rintro ⟨he, hf⟩
      cases x with
      | mk xe xf =>
        show cechObservation r s = ⟨xe, xf⟩
        unfold cechObservation
        congr 1
        · funext i j; exact he i j
        · funext t; exact hf t
  rw [h_eq]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    by_cases hb : x.edge i j
    · have hset : {s : CechSample n d | decide (s.hasEdge r i j) = x.edge i j} =
          {s | s.hasEdge r i j} := by
        ext s
        by_cases hs : s.hasEdge r i j <;> simp [hb, hs]
      rw [hset]; exact h_hasEdge i j
    · have hset : {s : CechSample n d | decide (s.hasEdge r i j) = x.edge i j} =
          {s | s.hasEdge r i j}ᶜ := by
        ext s
        by_cases hs : s.hasEdge r i j <;> simp [hb, hs]
      rw [hset]; exact (h_hasEdge i j).compl
  · refine MeasurableSet.iInter (fun t => ?_)
    by_cases hb : x.fill t
    · have hset : {s : CechSample n d | decide (s.hasFill r t) = x.fill t} =
          {s | s.hasFill r t} := by
        ext s
        by_cases hs : s.hasFill r t <;> simp [hb, hs]
      rw [hset]; exact measurableSet_cechSample_hasFill n d r t
    · have hset : {s : CechSample n d | decide (s.hasFill r t) = x.fill t} =
          {s | s.hasFill r t}ᶜ := by
        ext s
        by_cases hs : s.hasFill r t <;> simp [hb, hs]
      rw [hset]; exact (measurableSet_cechSample_hasFill n d r t).compl



/-- cechFilledCount is integrable under cechMeasure: each triangle indicator is the
    integrable indicator of `measurableSet_cechSample_hasFill` (probability measure
    is finite). -/
lemma cechFilledCount_integrable (n d : ℕ) (r : ℝ) :
    MeasureTheory.Integrable (fun s => cechFilledCount s r) (cechMeasure n d r) := by
  classical
  unfold cechFilledCount
  refine MeasureTheory.integrable_finset_sum _ (fun t _ => ?_)
  have h_indicator :
      (fun s : CechSample n d => if s.hasFill r t then (1:ℝ) else 0)
        = Set.indicator {s | s.hasFill r t} (fun _ => (1:ℝ)) := by
    ext s
    by_cases h : s.hasFill r t <;> simp [Set.indicator, h]
  rw [h_indicator]
  exact (MeasureTheory.integrable_const (1:ℝ) (μ := cechMeasure n d r)).indicator
    (measurableSet_cechSample_hasFill n d r t)



/-! ### Helper lemmas for snr_diverges -/

-- DEPRECATED (Strategy 1): `cechFilledCount_integral` / `cechFilledCount_variance` were
-- thin wrappers around the now-deleted `moments_cech`. Removed 2026-05-19 with no
-- downstream callers. See `moments_cech_signed` for the Strategy 2 mean identity.

-- DEPRECATED (Strategy 1): `snr_diverges` was the SNR argument under the unsigned
-- filled-triangle statistic. Superseded by `cech_complement_prob_bound` and the full
-- Paley–Zygmund chain (`paleyZygmund_cech_prob_tendsto_one`, `phase_transition`).
-- Removed 2026-05-19; no downstream callers.

/-! ### Strategy 2: Doubly-Signed Statistic -/

-- `doublySignedFilledCount` (τ_f on 2PC) moved to `Core.Statistic`
-- (Phase A1 core-extraction, OQ-18).

open Classical in
/-- Doubly-signed filled triangle count in a Čech sample. -/
noncomputable def cechDoublySignedCount {n d : ℕ} (p q : ℝ) (s : CechSample n d) (r : ℝ) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    (∏ e ∈ triangleEdges t,
      (if s.hasEdge r e.1 e.2 then (1 : ℝ) - p else -p)) *
    (if s.hasFill r t then (1 : ℝ) - q else -q)



-- ────────────────────────────────────────────────────────────────────────────
-- end OQ-16 / Track C stubs
-- ────────────────────────────────────────────────────────────────────────────

/- **Lemma A (Variance of doubly-signed stat under 2PC).**
    Under 2PC(n,p,q): E[τ_f] = 0, Var[τ_f] = C(n,3)·p³(1-p)³·q(1-q).

    PROVIDED SOLUTION
    Step 1: E[τ_f] = 0 because each summand has E[∏(A_e-p)·(F-q)] = 0 by independence
    and E[A_e-p] = 0 for each edge factor.

    Step 2: Var[τ_f] = E[τ_f²] = Σ_t Σ_t' E[T_t · T_t'].
    For t ≠ t': T_t · T_t' contains at least one edge factor (A_e - p) for an edge e
    appearing in exactly one of t, t'. By independence, this contributes E[A_e-p] = 0.
    Hence E[T_t · T_t'] = 0 for all t ≠ t'.

    Step 3: Diagonal: E[T_t²] = ∏_{e∈edges(t)} E[(A_e-p)²] · E[(F_t-q)²]
    = p(1-p) · p(1-p) · p(1-p) · q(1-q) = p³(1-p)³q(1-q).

    Step 4: Var[τ_f] = C(n,3) · p³(1-p)³q(1-q). -/
-- 2PC moment chain (`moments_twoParam_signed` + 7 private helpers) moved to `Core/Detection.lean` (post-A3.4 cleanup).

/-
PROBLEM
**Lemma B (Mean of doubly-signed stat under Čech).**
    Under Čech(n, r, d) with r = matchRadius p d, q = fillingProb p d:
    E[τ_f] = C(n,3) · geometricCov p d.

open MeasureTheory ProbabilityTheory in

PROVIDED SOLUTION
By linearity: E[τ_f] = Σ_t E[T_t]. By identical distribution of all triangles under
    the uniform measure, each E[T_t] = geometricCov p d. Sum over C(n,3) triangles.

By linearity of expectation, the integral of cechDoublySignedCount (which is a Finset.sum over triangles t) equals the sum of the integrals of each triangle's contribution. By the identical distribution of all triangles under the uniform product measure on the torus, each triangle's expected contribution equals geometricCov p d. Since there are C(n,3) triangles, the total is C(n,3) * geometricCov p d.

Key steps:
1. Unfold cechDoublySignedCount as a Finset.sum over triangles.
2. Use MeasureTheory.integral_finset_sum to swap sum and integral.
3. Show each summand's integral equals geometricCov p d by a change of variables / symmetry argument on the product measure.
4. Use Finset.sum_const to get C(n,3) * geometricCov p d.

For step 3, the key is that cechMeasure is the comap of the product measure through CechSample.points, and for any specific triangle t with vertices {i,j,k}, the marginal distribution of (points i, points j, points k) under the product measure is the same as the product measure on Fin 3 → Torus d (since the product measure on Fin n → Torus d has i.i.d. uniform marginals). This is exactly the measure used in the definition of geometricCov.

Since this involves a lot of measure theory machinery that may be hard to formalize directly, consider using sorry for the symmetry/identical distribution step and focusing on the algebraic structure.
-/

/-- CechSample is measurably equivalent to Fin n → Torus d. -/
noncomputable def cechEquiv (n d : ℕ) : MeasurableEquiv (CechSample n d) (Fin n → Torus d) where
  toFun := CechSample.points
  invFun := CechSample.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := measurable_iff_comap_le.mpr le_rfl
  measurable_invFun := by intro s hs; obtain ⟨t, ht, rfl⟩ := hs; exact ht



open MeasureTheory in
/-- Integrating over CechSample with cechMeasure equals integrating over Fin n → Torus d
    with the product measure. -/
lemma cech_integral_eq (n d : ℕ) (r : ℝ) (g : CechSample n d → ℝ) :
    ∫ s, g s ∂cechMeasure n d r =
    ∫ pts, g ⟨pts⟩ ∂Measure.pi (fun _ : Fin n => (volume : Measure (Torus d))) := by
  have key : cechMeasure n d r = Measure.map (cechEquiv n d).symm
      (Measure.pi (fun _ : Fin n => (volume : Measure (Torus d)))) := by
    ext s hs
    unfold cechMeasure
    rw [Measure.map_apply (cechEquiv n d).symm.measurable hs]
    rw [show Measure.comap CechSample.points (Measure.pi fun x ↦ volume) =
        Measure.comap (cechEquiv n d) (Measure.pi fun x ↦ volume) from rfl]
    rw [MeasurableEquiv.comap_apply]
  rw [key, integral_map_equiv]; rfl



/-! ### TV distance helper lemmas -/

/-
PROBLEM
tvDist is at least |μ(A) - ν(A)| for any measurable set A.

PROVIDED SOLUTION
Unfold tvDist. We need sSup S ≥ |(μ A).toReal - (ν A).toReal| where S = {x | ∃ s, MeasurableSet s ∧ x = |(μ s).toReal - (ν s).toReal|}.

Use le_csSup with two things:
1. BddAbove S: Since μ and ν are finite measures, (μ s).toReal ≤ (μ Set.univ).toReal for all s (by ENNReal.toReal_mono, measure_ne_top, measure_mono, subset_univ). Similarly for ν. So |a - b| ≤ a + b ≤ (μ univ).toReal + (ν univ).toReal. This bounds every element of S. Use BddAbove with upper bound (μ univ).toReal + (ν univ).toReal.

2. Membership: |(μ A).toReal - (ν A).toReal| ∈ S via ⟨A, hA, rfl⟩.

Key steps:
- unfold tvDist
- apply le_csSup
- For bddAbove: use ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, by rintro x ⟨s, hs, rfl⟩; ...⟩
- For membership: exact ⟨A, hA, rfl⟩
-/
-- `tvDist_ge_abs`, `tvDist_le_one`, `tvDist_tendsto_one_of_events` moved to
-- `Core.Detection` (Phase A3.2).

/-
PROBLEM
cechObservation relates doublySignedFilledCount to cechDoublySignedCount.

PROVIDED SOLUTION
Unfold both doublySignedFilledCount and cechDoublySignedCount. The cechObservation r s has edge i j = decide (s.hasEdge r i j) and fill t = decide (s.hasFill r t). In doublySignedFilledCount, the terms are (if s.edge e.1 e.2 then ...) which for Bool b is the same as (if b = true then ...). And (decide P = true) ↔ P. So each term matches. Use congr and simp with decide/Bool lemmas.
-/
lemma doublySignedFilledCount_cechObservation {n d : ℕ} (p q r : ℝ)
    (s : CechSample n d) :
    doublySignedFilledCount p q (cechObservation r s) =
    cechDoublySignedCount p q s r := by
  classical
  -- Under the new Rips definition of `cechObservation` (`edge := decide ∘ hasEdge`,
  -- `fill := decide ∘ hasFill`), the doubly-signed-count formulas match pointwise
  -- via `decide_eq_true_eq` (Bool-`if` ≡ Prop-`if` for Decidable propositions).
  unfold doublySignedFilledCount cechDoublySignedCount cechObservation
  congr 1
  funext t
  congr 1
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    by_cases h : s.hasEdge r e.1 e.2
    · rw [if_pos (by simp [h] : (decide (s.hasEdge r e.1 e.2) = true)), if_pos h]
    · rw [if_neg (by simp [h] : ¬(decide (s.hasEdge r e.1 e.2) = true)), if_neg h]
  · by_cases h : s.hasFill r t
    · rw [if_pos (by simp [h] : (decide (s.hasFill r t) = true)), if_pos h]
    · rw [if_neg (by simp [h] : ¬(decide (s.hasFill r t) = true)), if_neg h]



/-
PROBLEM
The pushforward of cechMeasure through cechObservation is a probability measure.

PROVIDED SOLUTION
Use MeasureTheory.Measure.isProbabilityMeasure_map with AEMeasurable. Need to show cechObservation r is AEMeasurable, which follows from Measurable. To show Measurable: use measurable_to_countable' which says that for f : α → β with β Countable and MeasurableSingletonClass, f is measurable if preimage of each singleton is measurable.

TwoParamSample n is Finite (it's a product of finite Bool function spaces), hence Countable. Its MeasurableSpace is ⊤, so MeasurableSingletonClass holds (every singleton is measurable).

For preimage of each singleton {x} under cechObservation r: the preimage is defined by conditions on distances between points (hasEdge) and existence of common balls (hasFill). These are Borel conditions. The preimage through CechSample.points gives a closed/Borel set in Fin n → Torus d, which is measurable in the comap sigma algebra.

Actually, simpler: use that cechObservation r factors as g ∘ CechSample.points where g is measurable from (Fin n → Torus d) to TwoParamSample n. Then cechObservation r is measurable by composition with the comap.

Or even simpler: try apply MeasureTheory.Measure.isProbabilityMeasure_map; apply Measurable.aemeasurable; apply measurable_to_countable'; intro b; show the preimage is measurable.
-/
instance cechPushforward_isProbabilityMeasure (n d : ℕ) (r : ℝ) :
    MeasureTheory.IsProbabilityMeasure
      ((cechMeasure n d r).map (cechObservation r)) :=
  MeasureTheory.Measure.isProbabilityMeasure_map (cechObservation_measurable r).aemeasurable



/-
OLD PROOF BODY (Čech-nerve form):
  -- By the squeeze theorem, it suffices to show that the upper bound tends to zero.
  suffices h_squeeze : ∀ᶠ k in Filter.atTop, ((twoParamMeasure (nSeq k) p (fillingProb p (dSeq k))) {s | doublySignedFilledCount p (fillingProb p (dSeq k)) s ≥ (Nat.choose (nSeq k) 3) * geometricCov p (dSeq k) / 2}).toReal ≤ (p ^ 3 * (1 - p) ^ 3) / ((Nat.choose (nSeq k) 3) * (geometricCov p (dSeq k)) ^ 2) by
    refine' squeeze_zero_norm' _ _;
    use fun k => p ^ 3 * ( 1 - p ) ^ 3 / ( ( Nat.choose ( nSeq k ) 3 ) * ( geometricCov p ( dSeq k ) ) ^ 2 );
    · filter_upwards [ h_squeeze ] with k hk using by rw [ Real.norm_of_nonneg ( ENNReal.toReal_nonneg ) ] ; exact hk;
    · refine' tendsto_const_nhds.div_atTop _;
      apply_rules [ choose3_g_sq_tendsto_atTop ]
  generalize_proofs at *; (
  have h_bound : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 3) * geometricCov p (dSeq k) > 0 := by
    filter_upwards [ hSNR.eventually_gt_atTop 0, hn.eventually_gt_atTop 3 ] with k hk₁ hk₂ using mul_pos ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) <| by nlinarith [ show ( nSeq k : ℝ ) ^ ( 3 / 2 : ℝ ) > 0 by positivity ] ;
  generalize_proofs at *; (
  filter_upwards [ h_bound ] with k hk
  generalize_proofs at *; (
  have := chebyshev_single_bound ( nSeq k ) p ( fillingProb p ( dSeq k ) ) ( ( Nat.choose ( nSeq k ) 3 ) * geometricCov p ( dSeq k ) / 2 ) ?_ ?_ ?_ ?_ ?_ <;> norm_num at * <;> try nlinarith [ show 0 ≤ fillingProb p ( dSeq k ) from fillingProb_nonneg p ( dSeq k ), show fillingProb p ( dSeq k ) ≤ 1 from fillingProb_le_one p ( dSeq k ) ] ;
  refine le_trans this ?_;
  field_simp [mul_comm, mul_assoc, mul_left_comm] at *;
  exact mul_le_mul_of_nonneg_right ( by nlinarith [ sq_nonneg ( fillingProb p ( dSeq k ) - 1 / 2 ), fillingProb_nonneg p ( dSeq k ), fillingProb_le_one p ( dSeq k ), pow_pos ( sub_pos.mpr hp1 ) 3 ] ) ( by positivity ) ;)))
-/

/-! Crude second moment bound for the doubly-signed statistic under Čech.
    Since |T_t| ≤ 1 for each triangle term, E[τ²] ≤ C(n,3) + 12·C(n,4).
    Diagonal: C(n,3) terms with E[T_t²] ≤ 1.
    Off-diagonal: only triangle pairs sharing an edge contribute nonzero
    covariance (pairs sharing exactly 1 vertex have Cov=0 by translation invariance).
    There are 12·C(n,4) such ordered pairs, each with |E[T_t T_{t'}]| ≤ 1.

    PROVIDED SOLUTION
    Step 1: Expand τ² = (Σ_t T_t)^2 = Σ_t T_t^2 + Σ_{t≠t'} T_t * T_{t'}.
    Step 2: Bound each term:
    - Diagonal: |T_t| ≤ 1 since each edge factor |A_e - p| ≤ max(p, 1-p) ≤ 1 and
      |F_t - q| ≤ 1, so |T_t| = |∏_{e∈edges(t)} (A_e-p)| * |F_t-q| ≤ 1.
      Therefore T_t^2 ≤ 1 and ∫ T_t^2 dν ≤ 1.
    - Off-diagonal: similarly |T_t * T_{t'}| ≤ 1, so |∫ T_t * T_{t'} dν| ≤ 1.
    Step 3: Count the pairs:
    - Diagonal: exactly C(n,3) triangles.
    - Off-diagonal: only pairs sharing an edge can have nonzero integral.
      Pairs sharing no edge or only a vertex: each T_t and T_{t'} share no edge,
      so they share at most 1 vertex. In the Cech model, the edge and fill indicators
      for t and t' are not independent (they share a vertex), but we use the crude
      bound |∫ T_t T_{t'} dν| ≤ 1 regardless.
      Pairs sharing exactly one edge: there are 3 edges per triangle, and for each
      ordered pair (t, t') sharing edge e, the remaining vertex of t and t' are
      independent of each other but both depend on e. Count: each of C(n,2) edges
      can be shared by at most C(n-2, 1) = n-2 pairs of triangles, giving
      at most 3*C(n,3)*(n-3) = 12*C(n,4) ordered pairs.
    Step 4: Combine: ∫ τ^2 dν = Σ_t ∫ T_t^2 dν + Σ_{t≠t'} ∫ T_t T_{t'} dν
      ≤ C(n,3)*1 + 12*C(n,4)*1 = C(n,3) + 12*C(n,4).
    Lean approach:
    - Use cech_integral_eq to convert the integral over ν to an integral over
      the product measure on Fin n → Torus d.
    - Expand the square using Finset.sum_mul_sq or Finset.sum_comm.
    - For the bound on each term: use norm_le_one or bound each factor by 1.
    - For counting: use Finset.card_le_card and the combinatorial identity
      that the number of ordered pairs of distinct triangles sharing an edge
      is at most 12*C(n,4) (each 4-element set {a,b,c,d} contributes at most
      3 edges, each shared by exactly 1 pair of triangles from the 4-set).
    Key Mathlib: integral_le_integral_of_le, Finset.sum_le_sum, norm_mul_le. -/

/-- **Sub-lemma 1: Diagonal bound.**
    Each doubly-signed triangle indicator T_t satisfies |T_t| ≤ 1.
    T_t = ∏_{e ∈ edges(t)} (A_e - p) * (F_t - q).
    Each edge factor: |A_e - p| = p if A_e = 0, or 1-p if A_e = 1. Both ≤ 1.
    Fill factor: |F_t - q| = q if F_t = 0, or 1-q if F_t = 1. Both ≤ 1.
    So |T_t| = product of 4 factors each ≤ 1, hence |T_t| ≤ 1.
    Therefore T_t^2 ≤ 1 and ∫ T_t^2 dν ≤ 1.
    PROVIDED SOLUTION
    Unfold doublySignedFilledCount. The indicator for triangle t is:
      T_t s = (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then 1-p else -p)) *
              (if s.fill t then 1-q else -q)
    Each edge factor has |·| ≤ max(p, 1-p) ≤ 1 (since 0 < p < 1).
    The fill factor has |·| ≤ max(q, 1-q) ≤ 1 (since 0 < q < 1).
    triangleEdges t has exactly 3 elements (card = 3 for a triangle).
    Use Finset.prod_le_one (or norm_num + abs_le) to bound the product.
    Key Mathlib: abs_le, Finset.abs_prod, Finset.prod_le_prod. -/
lemma doublySignedTriangle_sq_le_one {n : ℕ} (p q : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (s : TwoParamSample n) (t : {σ : Finset (Fin n) // σ.card = 3}) :
    ((∏ e ∈ triangleEdges t,
        (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.fill t then (1 : ℝ) - q else -q)) ^ 2 ≤ 1 := by
  have h_abs : abs ((∏ e ∈ triangleEdges t, if s.edge e.1 e.2 = true then 1 - p else -p) * (if s.fill t = true then 1 - q else -q)) ≤ 1 := by
    rw [ abs_mul, Finset.abs_prod ]
    refine' mul_le_one₀ ( Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => _ ) ( abs_nonneg _ ) _
    · grind
    · split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩
  nlinarith only [ abs_le.mp h_abs ]
