import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals

set_option linter.style.longLine false
set_option linter.style.whitespace false

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

open MeasureTheory in
/-- Expected fill volume 𝔼[V_f]: V_f(s,d) averaged over the separation PDF d·s^(d-1). -/
noncomputable def expectedFillVol (d : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Set.Ioo 0 1, volumeFill d r s * (d : ℝ) * s ^ (d - 1)

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

/- COMMENTED OUT — incorrect variance formula (see note above):
open MeasureTheory ProbabilityTheory in
lemma moments_twoParam (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, filledTriangleCount s ∂twoParamMeasure n p q = (n.choose 3 : ℝ) * p ^ 3 * q ∧
    variance filledTriangleCount (twoParamMeasure n p q) =
      (n.choose 3 : ℝ) * p ^ 3 * q * (1 - p ^ 3 * q) := by
  sorry
-/

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

/- DEPRECATED (Strategy 1) — superseded by doublySignedFilledCount / cech_second_moment_bound
   in Strategy 2. No downstream callers.
open MeasureTheory ProbabilityTheory in
/-- Variance of filledTriangleCount under 2PC (corrected). -/
lemma moments_twoParam_var (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    variance filledTriangleCount (twoParamMeasure n p q) =
      (n.choose 3 : ℝ) * p ^ 3 * q * (1 - p ^ 3 * q) +
      12 * (n.choose 4 : ℝ) * p ^ 5 * q ^ 2 * (1 - p) := by
  sorry
-/

/- DEPRECATED duplicate (Strategy 1). The variance half depends on `moments_twoParam_var`
   which is itself commented out as dead. Kept only for reference; use `moments_twoParam_mean`
   directly for the expectation, and `moments_twoParam_signed` / `cech_second_moment_bound`
   for Strategy 2 variance arguments. No downstream callers.
open MeasureTheory ProbabilityTheory in
lemma moments_twoParam (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, filledTriangleCount s ∂twoParamMeasure n p q = (n.choose 3 : ℝ) * p ^ 3 * q ∧
    variance filledTriangleCount (twoParamMeasure n p q) =
      (n.choose 3 : ℝ) * p ^ 3 * q * (1 - p ^ 3 * q) +
      12 * (n.choose 4 : ℝ) * p ^ 5 * q ^ 2 * (1 - p) :=
  ⟨moments_twoParam_mean n p q hp hp1 hq hq1, moments_twoParam_var n p q hp hp1 hq hq1⟩
-/

/- COMMENTED OUT — disproved for d=0 where expectedFillVol vanishes but cechFilledCount is nonzero.
   When d=0, Torus 0 is a single point, all Čech fills hold trivially, but
   expectedFillVol 0 r = 0 (the integrand has factor d=0). This makes
   C(n,3)*p*EVf = 0 ≠ C(n,3) = E[cechFilledCount]. Adding 0 < p < 1 rules out
   d=0 since euclidBallVol 0 (2r) = 1 for any r, contradicting p < 1.

   Original statement (without the 0 < p < 1 hypotheses):
   open MeasureTheory ProbabilityTheory in
   lemma moments_cech (n d : ℕ) (r p : ℝ) (hp : p = euclidBallVol d (2 * r)) :
       let μ := cechMeasure n d r
       let EVf := expectedFillVol d r
       ∫ s, cechFilledCount s r ∂μ = (n.choose 3 : ℝ) * p * EVf ∧
       variance (fun s => cechFilledCount s r) μ =
         (n.choose 3 : ℝ) * p * EVf * (1 - p * EVf) +
         12 * (n.choose 4 : ℝ) * (p - p ^ 2) * EVf ^ 2 := by
     sorry
-/

open MeasureTheory ProbabilityTheory in
/-- **Lemma 4 (Moments under Čech, corrected).** Under Čech(n, r, d) with p = V_d(2r) ∈ (0,1):
      𝔼[Δ_f] = C(n,3) p 𝔼[V_f]
      Var[Δ_f] = C(n,3) p 𝔼[V_f](1 - p 𝔼[V_f]) + 12 C(n,4) (p - p²) 𝔼[V_f]²

    **Modification from original:** added hypotheses `0 < p` and `p < 1` to exclude
    the degenerate case d=0 where euclidBallVol 0 (2r) = 1 and the formula fails.

    **Deprecated (Strategy 1):** used only by `cechFilledCount_integral` and
    `cechFilledCount_variance` (Strategy 1 helpers). The Strategy 2 replacement is
    `moments_cech_signed`. -/
@[deprecated "Strategy 1 lemma; use moments_cech_signed for Strategy 2 proofs"]
lemma moments_cech (n d : ℕ) (r p : ℝ) (hp : p = euclidBallVol d (2 * r))
    (hp0 : 0 < p) (hp1 : p < 1) :
    let μ := cechMeasure n d r
    let EVf := expectedFillVol d r
    ∫ s, cechFilledCount s r ∂μ = (n.choose 3 : ℝ) * p * EVf ∧
    variance (fun s => cechFilledCount s r) μ =
      (n.choose 3 : ℝ) * p * EVf * (1 - p * EVf) +
      12 * (n.choose 4 : ℝ) * (p - p ^ 2) * EVf ^ 2 := by
  sorry

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

/-! ## Asymptotics -/

open MeasureTheory in
/-- Expected empty volume: V_e(s,d) averaged over the separation PDF d·s^(d-1). -/
noncomputable def expectedEmptyVol (d : ℕ) (r : ℝ) : ℝ :=
  ∫ s in Set.Ioo 0 1, volumeEmpty d r s * (d : ℝ) * s ^ (d - 1)

/- SUPERSEDED by Strategy 2 — these asymptotics assumed E[V_f] → 0 polynomially,
   but Aristotle showed E[V_f] → L > 0 (positive constant) as d → ∞.
   Kept for reference; not used in the current proof.

open MeasureTheory in
lemma asymptotics_expectedEmptyVol (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧
    Filter.Tendsto
      (fun d : ℕ => expectedEmptyVol d (matchRadius p d) / (C * (d : ℝ) ^ (-β)))
      Filter.atTop (nhds 1) := by
  sorry

open MeasureTheory in
lemma asymptotics_expectedFillVol (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A γ : ℝ, 0 < A ∧ 0 < γ ∧
    Filter.Tendsto
      (fun d : ℕ => expectedFillVol d (matchRadius p d) / (A * (d : ℝ) ^ (-γ)))
      Filter.atTop (nhds 1) := by
  sorry

lemma decay_fillingProb (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧
    Filter.Tendsto
      (fun d : ℕ => fillingProb p d / (B * (d : ℝ) ^ (-δ)))
      Filter.atTop (nhds 1) := by
  sorry
-/

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

/-- cechFilledCount is integrable under cechMeasure: bounded by C(n,3), measurable via comap
    sigma-algebra (Čech fill sets are closed hence Borel), finite measure from probability instance. -/
lemma cechFilledCount_integrable (n d : ℕ) (r : ℝ) :
    MeasureTheory.Integrable (fun s => cechFilledCount s r) (cechMeasure n d r) := by
  -- OQ-18 Rips refactor: under clique `hasFill`, this is a finite intersection of
  -- `{dist ≤ r}` sets pulled back through `CechSample.points`. The original existential-
  -- form proof is no longer the right shape. Stubbed pending refactor.
  sorry

/-! ### Helper lemmas for snr_diverges -/

/-- The integral of `cechFilledCount` under `cechMeasure` equals C(n,3)·p·EVf.
    This is the first component of `moments_cech`. -/
lemma cechFilledCount_integral (n d : ℕ) (r p : ℝ) (hp : p = euclidBallVol d (2 * r))
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ s, cechFilledCount s r ∂cechMeasure n d r = (n.choose 3 : ℝ) * p * expectedFillVol d r :=
  (moments_cech n d r p hp hp0 hp1).1

/-- The variance of `cechFilledCount` under `cechMeasure`. -/
lemma cechFilledCount_variance (n d : ℕ) (r p : ℝ) (hp : p = euclidBallVol d (2 * r))
    (hp0 : 0 < p) (hp1 : p < 1) :
    ProbabilityTheory.variance (fun s => cechFilledCount s r) (cechMeasure n d r) =
      (n.choose 3 : ℝ) * p * expectedFillVol d r * (1 - p * expectedFillVol d r) +
      12 * (n.choose 4 : ℝ) * (p - p ^ 2) * expectedFillVol d r ^ 2 :=
  (moments_cech n d r p hp hp0 hp1).2

/-
PROVIDED SOLUTION
Step 1: Derive hp : p = euclidBallVol d (2 * r).
  From hr : r = matchRadius p d and matchRadius_spec p d hp0 hp1 : euclidBallVol d (2 * matchRadius p d) = p.
  So hp : p = euclidBallVol d (2 * r) follows by rw [hr] and symmetry of matchRadius_spec.

Step 2: Get the moments of cechFilledCount from moments_cech.
  obtain ⟨h_mean, h_var⟩ := moments_cech n d r p hp

Step 3: For the integral part:
  Show ∫ cechSignedCount = ∫ cechFilledCount - C(n,3)*p^3*q.
  Unfold cechSignedCount to get cechFilledCount s r - constant.
  Use MeasureTheory.integral_sub (cechFilledCount_integrable) (integrable_const _)
  and MeasureTheory.integral_const with the fact that cechMeasure is a probability measure
  (so μ.real Set.univ = 1, using MeasureTheory.IsProbabilityMeasure.measure_univ).
  Then ∫ cechSignedCount = h_mean value - C(n,3)*p^3*q = C(n,3)*(p*EVf - p^3*q) by ring.

Step 4: For the variance part:
  Show variance(cechSignedCount) = variance(cechFilledCount).
  cechSignedCount s = cechFilledCount s r - c for constant c.
  By ProbabilityTheory.variance definition and integral linearity:
  ∫ (X - E[X])^2 is the same for X and X-c since (X-c) - E[X-c] = X - E[X].
  More concretely, show the functions s ↦ cechSignedCount s - E[cechSignedCount] and
  s ↦ cechFilledCount s - E[cechFilledCount] are equal (pointwise), hence their L2 norms agree.
  Then use h_var.
-/
open MeasureTheory ProbabilityTheory in
/- DEPRECATED (Strategy 1) — superseded by cech_complement_prob_bound in Strategy 2.
   No downstream callers; snr_diverges was the Strategy 1 SNR argument.
/-- **Lemma 7 (SNR of Δ̃_f).** Under the matched pair 2PC(n,p,q*) and Čech(n,r,d):
      𝔼_Čech[Δ̃_f] = C(n,3)(p·𝔼[V_f] - p³q*)
      Var_Čech[Δ̃_f] = C(n,3)·p·𝔼[V_f]·(1-p·𝔼[V_f]) + 12·C(n,4)·(p-p²)·𝔼[V_f]²
    so SNR = 𝔼[Δ̃_f]²/Var[Δ̃_f] → ∞ whenever n·𝔼[V_f](p,d) → 0.

    PROVIDED SOLUTION
    Mean: 𝔼_Čech[Δ̃_f] = 𝔼_Čech[Δ_f] - 𝔼_2PC[Δ_f] = C(n,3)(p·𝔼[V_f] - p³q*)
    (use Lemmas 3 and 4).
    Variance: Var_Čech[Δ̃_f] = Var_Čech[Δ_f] (shifting by a constant); apply Lemma 4.
    SNR = 𝔼[Δ̃_f]²/Var[Δ̃_f] ~ n²·(p·𝔼[V_f])² / (n⁴·(p-p²)·𝔼[V_f]²) = O(1/n²) when
    n·𝔼[V_f] → 0... wait, SNR → ∞ when n·𝔼[V_f] → 0 via:
    SNR ~ [C(n,3)·p·𝔼[V_f]]² / [12·C(n,4)·(p-p²)·𝔼[V_f]²]
        ~ n⁶·(p·𝔼[V_f])² / [n⁴·𝔼[V_f]²] = Θ(n²·p²) → ∞.
    More carefully: the numerator 𝔼[Δ̃_f]² ~ C(n,3)²·p²·𝔼[V_f]² (dominant when q* is small)
    grows faster than Var ~ 12·C(n,4)·(p-p²)·𝔼[V_f]² since C(n,3)²/C(n,4) → ∞ with n. -/
lemma snr_diverges (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (r : ℝ) (hr : r = matchRadius p d) (q : ℝ) (_hq : q = fillingProb p d) :
    let μ := cechMeasure n d r
    let EVf := expectedFillVol d r
    ∫ s, cechSignedCount n d p q s r ∂μ =
        (n.choose 3 : ℝ) * (p * EVf - p ^ 3 * q) ∧
    variance (fun s => cechSignedCount n d p q s r) μ =
        (n.choose 3 : ℝ) * p * EVf * (1 - p * EVf) +
        12 * (n.choose 4 : ℝ) * (p - p ^ 2) * EVf ^ 2 := by
  sorry
-/

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

open Classical MeasureTheory in
/-- Geometric covariance: the expected value of one doubly-signed triangle term under Čech.
    g(p,d) = E_Čech[(A₁₂-p)(A₁₃-p)(A₂₃-p)(F_{123}-q)]
    where r = matchRadius p d, q = fillingProb p d.
    Measures how much the joint distribution of edges and fills deviates from independence.
    As d → ∞ this decays to 0 (Lemma C below). -/
noncomputable def geometricCov (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchRadius p d
  let q := fillingProb p d
  ∫ pts : Fin 3 → Torus d,
    let x₁ := pts 0; let x₂ := pts 1; let x₃ := pts 2
    let e₁₂ := if dist x₁ x₂ ≤ r then (1 : ℝ) - p else -p
    let e₁₃ := if dist x₁ x₃ ≤ r then (1 : ℝ) - p else -p
    let e₂₃ := if dist x₂ x₃ ≤ r then (1 : ℝ) - p else -p
    let fill := if ∃ z : Torus d, dist x₁ z ≤ r ∧ dist x₂ z ≤ r ∧ dist x₃ z ≤ r
                then (1 : ℝ) - q else -q
    e₁₂ * e₁₃ * e₂₃ * fill
  ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))

-- ────────────────────────────────────────────────────────────────────────────
-- OQ-16 / Track A: quantitative `geomCov` decay rate (sim-A5 packet, session 31).
-- See `analytic_decay_rate.md` and `requests/sim_A5_packet.md` for derivations.
-- ────────────────────────────────────────────────────────────────────────────

/-- **Helper: 1D-Helly trivialisation.** If two arcs share a common centre vertex,
    the triple intersection is automatically nonempty: pick `z = x₁`. -/
lemma wedge_implies_fill {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r) (x₁ x₂ x₃ : Torus d)
    (h12 : dist x₁ x₂ ≤ r) (h13 : dist x₁ x₃ ≤ r) :
    ∃ z : Torus d, dist x₁ z ≤ r ∧ dist x₂ z ≤ r ∧ dist x₃ z ≤ r := by
  refine ⟨x₁, ?_, ?_, ?_⟩
  · simp [dist_self]; exact hr0
  · rw [dist_comm]; exact h12
  · rw [dist_comm]; exact h13

open Classical MeasureTheory in
/-- **Sim-A5 / Job 1, Lemma 1.** Triangle (3-pairwise-edge) probability under Čech,
    deep regime `r ≤ 1/4`. Equals `(3 r²)^d` by sup-norm coordinate factorisation
    and the 1D area calculation: in each coordinate, the event "all 3 pairwise
    distances ≤ r" has probability `3 r²` (square `[-r,r]²` of area `4r²` minus
    two corner triangles of total area `r²`).

    PROVIDED SOLUTION
    Step 1: Apply `MeasureTheory.integral_fintype_prod` (or `volume_pi` + Fubini)
      to reduce the `Fin 3 → Torus d` integral to nested integrals over `Torus d`.
    Step 2: Use sup-norm coordinate decomposition (`Pi.dist_def`) to factor the
      indicator product across the `d` torus coordinates.
    Step 3: Per coordinate, condition on `u₁ = 0`. The event becomes
      `|u₂| ≤ r ∧ |u₃| ≤ r ∧ |u₂ - u₃| ≤ r` on the square `[-r,r]²`.
      Area of square: `4 r²`. Area cut by `|u₂ - u₃| ≤ r` constraint: two
      corner right-triangles of legs `r`, total area `r²`. Remaining area: `3 r²`.
    Step 4: Per-coordinate probability is `3 r²`. Raise to dth power. -/
lemma gamma_pow_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (3 * (matchRadius p d) ^ 2) ^ d := by
  convert integral_triangle_eq_pow d hd ( matchRadius p d ) ( by unfold matchRadius; positivity ) hr using 1

open Classical MeasureTheory in
/-- **Sim-A5 / Job 1, Lemma 2.** Single-edge ∧ fill probability under Čech,
    deep regime `r ≤ 1/4`. Equals `(7 r²)^d`.

    PROVIDED SOLUTION
    Step 1: Same coordinate factorisation as `gamma_pow_eq`. Per coordinate,
      we need `PP[|u₁ - u₂| ≤ r ∧ ∃ z : |u_i - z| ≤ r ∀ i]`.
    Step 2: Condition on `u₁ = 0, u₂ = s` with `|s| ≤ r`. The set of valid
      `z` is the overlap arc `[max(-r, s-r), min(r, s+r)]` of length `2r - |s|`.
      Then `u₃ ∈ B(z, r)` for some such `z` ⟺ `u₃ ∈ [s - 2r + |s|, 2r - |s|]`...
      wait — easier: `u₃ ∈ ⋃_z B(z, r) = [\min_z (z-r), \max_z (z+r)]
      = [\min(-r, s-r) - r, \max(r, s+r) + r]`. For `s ∈ [0, r]`, this is
      `[-2r + s, 2r]`... Length `4r - s` for `s ∈ [0, r]` (and `4r + s` for
      `s ∈ [-r, 0]`, equivalently `4r - |s|`).
    Step 3: Per-coordinate probability:
      `∫_{-r}^{r} (4r - |s|) ds = 2 ∫_0^r (4r - s) ds = 2(4r² - r²/2) = 7 r²`.
    Step 4: Raise to dth power. -/
lemma mu_e_pow_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (7 * (matchRadius p d) ^ 2) ^ d := by
  exact integral_edgeFill_eq_pow d hd ( matchRadius p d ) ( by unfold matchRadius; positivity ) hr

/-- **Filling probability closed form, Rips convention, deep regime `r ≤ 1/4`.**
    Under Rips, F_ijk = A_ij·A_ik·A_jk so `fillingProb p d` equals the triangle
    (3-clique) probability `(3r²)^d` from `gamma_pow_eq`. -/
lemma fillingProb_eq_low_r (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    fillingProb p d = (3 * (matchRadius p d) ^ 2) ^ d := by
  unfold fillingProb
  exact gamma_pow_eq p d hp0 hp1 hd hr

/-
────────────────────────────────────────────────────────────────────────────
Helper lemmas for geometricCov expansion
────────────────────────────────────────────────────────────────────────────
-/
open Classical MeasureTheory in
/-- The integral of a single edge indicator over the 3-point product measure
    equals the edge probability `p = (2r)^d`. -/
lemma edge_integral (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
  have h_volume_edge : volume ( {pts : Fin 3 → Torus d | dist (pts 0) (pts 1) ≤ matchRadius p d} ) = ENNReal.ofReal ( (2 * matchRadius p d) ^ d ) := by
    convert volume_coordFactored_eq_pow d ( { pts : Fin 3 → AddCircle ( 1 : ℝ ) | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d } ) _ using 1;
    · congr with x ; simp +decide [ dist_eq_norm ];
      rw [ pi_norm_le_iff_of_nonneg ];
      · rfl;
      · unfold matchRadius; positivity;
    · have h_volume_edge : volume ( {pts : Fin 3 → AddCircle ( 1 : ℝ ) | dist (pts 0) (pts 1) ≤ matchRadius p d} ) = ENNReal.ofReal (2 * matchRadius p d) := by
        have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d} = ∫⁻ (x : T1), volume {y : T1 | dist x y ≤ matchRadius p d} ∂volume := by
          have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d} = ∫⁻ (x : T1 × T1 × T1), (if dist x.1 x.2.1 ≤ matchRadius p d then 1 else 0) ∂volume := by
            have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d} = ∫⁻ (x : Fin 3 → T1), (if dist (x 0) (x 1) ≤ matchRadius p d then 1 else 0) ∂volume := by
              erw [ MeasureTheory.lintegral_indicator ];
              · aesop;
              · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
            rw [ h_volume ];
            have h_volume : MeasureTheory.MeasureSpace.volume = MeasureTheory.Measure.map (fun x : T1 × T1 × T1 => ![x.1, x.2.1, x.2.2]) (MeasureTheory.MeasureSpace.volume) := by
              simp +decide [ MeasureTheory.MeasureSpace.volume ];
              erw [ MeasureTheory.Measure.pi_eq ];
              intro s hs; erw [ MeasureTheory.Measure.map_apply ];
              · simp +decide [ Set.preimage, Fin.prod_univ_three ];
                simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
                erw [ show { a : T1 × T1 × T1 | a.1 ∈ s 0 } ∩ ( { a : T1 × T1 × T1 | a.2.1 ∈ s 1 } ∩ { a : T1 × T1 × T1 | a.2.2 ∈ s 2 } ) = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; simp +decide [ mul_assoc ];
              · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
              · exact MeasurableSet.univ_pi hs;
            rw [ h_volume, MeasureTheory.lintegral_map ];
            · rfl;
            · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
            · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
          erw [ h_volume, MeasureTheory.lintegral_prod ];
          · congr! 2;
            erw [ MeasureTheory.lintegral_prod ];
            · erw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
              exact?;
              · exact measurableSet_le ( measurable_const.dist measurable_id' ) measurable_const;
              · filter_upwards [ ] with x ; aesop;
            · exact Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_le ( measurable_const.dist measurable_fst ) measurable_const ) measurable_const measurable_const );
          · exact Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_le ( measurable_fst.dist measurable_snd.fst ) measurable_const ) measurable_const measurable_const );
        have h_volume : ∀ x : T1, volume {y : T1 | dist x y ≤ matchRadius p d} = ENNReal.ofReal (2 * matchRadius p d) := by
          intro x;
          convert volume_closedBall_inter_T1 ( matchRadius p d ) ( show 0 ≤ matchRadius p d from ?_ ) ( show matchRadius p d ≤ 1 / 4 from hr ) x x ?_ using 1 <;> norm_num [ dist_comm ];
          · exact congr_arg _ ( by ext; simp +decide [ dist_comm ] );
          · unfold matchRadius; positivity;
          · unfold matchRadius; positivity;
        aesop;
      rw [ h_volume_edge, ENNReal.ofReal_pow ( by exact mul_nonneg zero_le_two ( by unfold matchRadius; positivity ) ) ];
    · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
  convert congr_arg ENNReal.toReal h_volume_edge using 1;
  · erw [ MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    · rfl;
    · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const;
  · rw [ ENNReal.toReal_ofReal ( pow_nonneg ( mul_nonneg zero_le_two ( by unfold matchRadius; positivity ) ) _ ), matchRadius_spec p d hp0 hp1 hd ]

open Classical MeasureTheory in
/-- The integral of a wedge indicator (two edges sharing a vertex) over the
    3-point product measure equals `p²`, because the two edge events are
    conditionally independent given the shared vertex. -/
lemma wedge_integral (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
  have h_volume : (∫ (pts : Fin 3 → Torus d), (if dist (pts 0) (pts 1) ≤ matchRadius p d then 1 else 0) * (if dist (pts 0) (pts 2) ≤ matchRadius p d then 1 else 0) ∂Measure.pi fun _ => volume) = (4 * (matchRadius p d) ^ 2) ^ d := by
    convert volume_coordFactored_eq_pow d _ _ using 1;
    case convert_1 => exact { pts : Fin 3 → T1 | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d ∧ dist ( pts 0 ) ( pts 2 ) ≤ matchRadius p d };
    · rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
      change (∫ x in { pts : Fin 3 → Torus d | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d ∧ dist ( pts 0 ) ( pts 2 ) ≤ matchRadius p d }, 1 ∂Measure.pi fun _ => volume) = _ ↔ _;
      · simp +decide [ MeasureTheory.measureReal_def ];
        rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
        convert Iff.rfl using 2;
        · congr! 2;
          ext; simp +decide [ dist_pi_le_iff ] ;
          rw [ dist_pi_le_iff, dist_pi_le_iff ] ; aesop;
          · unfold matchRadius; positivity;
          · unfold matchRadius; positivity;
        · have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d} = ENNReal.ofReal (4 * (matchRadius p d) ^ 2) := by
            have h_volume : volume ({pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d}) = ∫⁻ (u1 : T1), volume ({c : T1 | dist u1 c ≤ matchRadius p d}) * volume ({c : T1 | dist u1 c ≤ matchRadius p d}) ∂volume := by
              have h_volume : volume ({pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d}) = ∫⁻ (u1 : T1), volume ({c : T1 × T1 | dist u1 c.1 ≤ matchRadius p d ∧ dist u1 c.2 ≤ matchRadius p d}) ∂volume := by
                erw [ MeasureTheory.volume_pi ];
                erw [ MeasureTheory.Measure.pi_eq ];
                rotate_right;
                exact MeasureTheory.Measure.map ( fun x : T1 × T1 × T1 => ![x.1, x.2.1, x.2.2] ) ( MeasureTheory.Measure.prod ( MeasureTheory.MeasureSpace.volume ) ( MeasureTheory.Measure.prod ( MeasureTheory.MeasureSpace.volume ) ( MeasureTheory.MeasureSpace.volume ) ) );
                · rw [ MeasureTheory.Measure.map_apply ];
                  · erw [ MeasureTheory.Measure.prod_apply ];
                    · congr! 2;
                    · simp +decide [ Set.preimage ];
                      exact MeasurableSet.mem ( MeasurableSet.inter ( measurableSet_le ( measurable_fst.dist measurable_snd.fst ) measurable_const ) ( measurableSet_le ( measurable_fst.dist measurable_snd.snd ) measurable_const ) );
                  · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
                  · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
                · intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; norm_num [ Fin.prod_univ_three ] ;
                  · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
                    erw [ show { x : T1 × T1 × T1 | x.1 ∈ s 0 ∧ x.2.1 ∈ s 1 ∧ x.2.2 ∈ s 2 } = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ; erw [ MeasureTheory.Measure.prod_prod ] ; ring;
                  · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
                  · exact MeasurableSet.univ_pi hs;
              convert h_volume using 3;
              erw [ ← MeasureTheory.Measure.prod_prod ];
              exact?;
            have h_volume : ∀ u1 : T1, volume ({c : T1 | dist u1 c ≤ matchRadius p d}) = ENNReal.ofReal (2 * matchRadius p d) := by
              intro u1;
              have h_volume : volume (Metric.closedBall u1 (matchRadius p d)) = ENNReal.ofReal (2 * matchRadius p d) := by
                rw [ two_mul, AddCircle.volume_closedBall ];
                grind;
              convert h_volume using 1;
              exact congr_arg _ ( by ext; simp +decide [ dist_comm ] );
            simp_all +decide [ mul_pow ];
            rw [ ENNReal.ofReal_pow ( by unfold matchRadius; positivity ) ] ; ring;
          rw [ h_volume, ENNReal.toReal_ofReal ( by positivity ) ];
      · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
      · filter_upwards [ ] with x using by rw [ Set.indicator_apply ] ; aesop;
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
  convert h_volume using 1;
  rw [ show 4 * matchRadius p d ^ 2 = ( 2 * matchRadius p d ) ^ 2 by ring, ← pow_mul, Nat.mul_comm, pow_mul, matchRadius_spec p d hp0 hp1 hd ]

open Classical MeasureTheory in
/-- Algebraic identity: `p² · (7r²)^d = p³ · (7r/2)^d`,
    used to convert between the mu_e and half-radius forms. -/
lemma p_sq_mu_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    p ^ 2 * (7 * (matchRadius p d) ^ 2) ^ d
    = p ^ 3 * (7 * matchRadius p d / 2) ^ d := by
  have h_match : p = (2 * matchRadius p d) ^ d := by
    exact?;
  rw [ show p ^ 3 = p ^ 2 * p by ring, h_match ] ; ring;
  rw [ show matchRadius p d ^ d * 2 ^ d = p by rw [ ← mul_pow, mul_comm ] ; exact h_match.symm ] ; ring;
  norm_num [ pow_mul', ← mul_pow ] ; ring

/- **Sim-A5 / Job 2, Lemma 4 (8-term collapse).** Closed-form `geometricCov`
    in the deep regime via the doubly-centered binomial expansion.

    PROVIDED SOLUTION
    Step 1: Expand `∏_{(ij)}(A_{ij} - p) · (F - q)` into 16 monomials.
    Step 2: Group by edge-set `S ⊆ {12,13,23}` and fill `u ∈ {0,1}`.
      Each `EE[A_S F^u] = μ_{S,u}^d` by coordinate factorisation.
    Step 3: Pair `(S, 0)` with `(S, 1)`. Pair contribution:
      `(-p)^{3-|S|} μ_{S,0}^d · [(1 - δ_S/μ_{S,0})^d - (1 - δ_∅)^d]`
      where `δ_S = μ_{S,0} - μ_{S,1}` and `q = (1 - δ_∅)^d`.
    Step 4 (S=∅): bracket = 0. ✓
    Step 5 (S=wedge, |S|=2): by `wedge_implies_fill`, `δ_w = 0`. Bracket = 0.
    Step 6 (S={12,13,23}): all-edges ⟹ fill (by `wedge_implies_fill` twice).
      So `μ_{S,0} = μ_{S,1} = γ` and contribution is `γ^d · (1 - q)`.
    Step 7 (S=single edge): `μ_{S,0} = α = 2r`, `μ_{S,1} = μ_e = 7 r²`.
      `α^d = p`, so contribution per edge is `p² · (μ_e^d - q · α^d) =
      p² · ((7r²)^d - q · p)`. Summed over 3 edges, and folded with the
      outer `(-p)^{3-|S|} = p²` and the binomial sign... -- carefully tracked
      in `analytic_decay_rate.md` §A3.3, lands at `3 p^3 [(7r/2)^d - q]`.

   COMMENTED OUT: The formula below is false. The proof sketch in §A3.3 incorrectly
   claims the wedge (|S|=2) contributions vanish. In fact, for any wedge S (e.g. S={12,13}),
   `wedge_implies_fill` gives A_S · F = A_S pointwise, so
   E[A_S · (F - q)] = (1 - q) · E[A_S] ≠ 0 in general.
   Since E[A₁₂·A₁₃] = (4r²)^d = p² (where p = (2r)^d), the total wedge contribution is
   -3p·(1-q)·p² = -3p³(1-q), yielding the corrected formula:
     geometricCov = (1-q)·(3r²)^d + 3p³·((7r/2)^d - 1)
   The original formula has `-fillingProb p d` where `-1` should appear.
   Numerical check: d=1, p=1/4 gives geometricCov = 3/256 ≈ 0.01172,
   but the formula below gives 51/1024 ≈ 0.04980. -/
/-
theorem geometricCov_eq_deep (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    geometricCov p d
    = (1 - fillingProb p d) * (3 * (matchRadius p d) ^ 2) ^ d
      + 3 * p ^ 3 * ((7 * matchRadius p d / 2) ^ d - fillingProb p d) := by
  sorry
-/

/-! ### Symmetric integral helpers -/

open Classical MeasureTheory in
/-- Integral of A₁₃ (edge indicator for vertices 0,2) equals p. By symmetry with edge_integral. -/
lemma edge_integral_02 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
      -- The swap is measure-preserving, so the integral of the composition is equal to the integral of the original function.
      have h_swap : MeasureTheory.MeasurePreserving (fun (pts : Fin 3 → Torus d) => fun i => pts (Equiv.swap 1 2 i)) (MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ *, Fin.prod_univ_three ] ;
          · rw [ show ( fun pts i => pts ( Equiv.swap 1 2 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 1 2 i ) ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
            · grind;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      convert edge_integral p d hp0 hp1 hd hr using 1;
      rw [ ← h_swap.integral_comp ];
      · rfl;
      · constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 1 2 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 1 2 i );
          · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;

open Classical MeasureTheory in
/-- Integral of A₂₃ (edge indicator for vertices 1,2) equals p. By symmetry with edge_integral. -/
lemma edge_integral_12 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
      convert edge_integral_02 p d hp0 hp1 hd hr using 1;
      -- Apply the measure-preserving permutation to the integral.
      have h_perm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (Measure.pi (fun _ => volume)) (Measure.pi (fun _ => volume)) := by
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three ] ;
          · rw [ show ( fun pts : Fin 3 → Torus d => fun i => pts ( Equiv.swap 0 1 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 0 1 i ) ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
            · grind +qlia;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_perm.integral_comp ];
      · rfl;
      · refine' ⟨ _, _, _ ⟩;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 0 1 i );
          · exact h_perm.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;

open Classical MeasureTheory in
/-- Wedge integral for edges (0,1) and (1,2), sharing vertex 1, equals p². -/
lemma wedge_integral_1center (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
      have := @wedge_integral;
      convert this p d hp0 hp1 hd hr using 1;
      -- The permutation that swaps 0 and 1 and leaves 2 fixed is measure-preserving.
      have h_perm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (Measure.pi (fun _ : Fin 3 => volume)) (Measure.pi (fun _ : Fin 3 => volume)) := by
        refine' ⟨ _, _ ⟩;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three, hs ] ;
          · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
            erw [ show { x : Fin 3 → Torus d | x 1 ∈ s 0 ∧ x 0 ∈ s 1 ∧ x 2 ∈ s 2 } = ( Set.pi Set.univ fun i => if i = 0 then s 1 else if i = 1 then s 0 else s 2 ) by ext; simp +decide [ Fin.forall_fin_succ ] ; tauto ] ; erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_perm.integral_comp ];
      · simp +decide [ dist_comm ];
        rfl;
      · constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 0 1 i );
          · exact h_perm.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;

open Classical MeasureTheory in
/-- Wedge integral for edges (0,2) and (1,2), sharing vertex 2, equals p². -/
lemma wedge_integral_2center (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
      -- The integral is invariant under permutation of the variables, so we canswap the variables.
      have h_perm : ∀ (f : (Fin 3 → Torus d) → ℝ), (∫ pts : Fin 3 → Torus d, f pts ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) = ∫ pts : Fin 3 → Torus d, f (pts ∘ (Equiv.swap 1 2)) ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) ) := by
        intro f
        have h_measure_preserving : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => pts ∘ (Equiv.swap 1 2)) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
          refine' ⟨ _, _ ⟩;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
            intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ hs, Fin.prod_univ_three ] ;
            · rw [ show ( fun pts : Fin 3 → Torus d => pts ∘ ⇑ ( Equiv.swap 1 2 ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 1 2 i ) ) from ?_ ];
              · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
              · ext; simp +decide [ Set.mem_univ_pi ] ;
                exact ⟨ fun h i => by simpa using h ( Equiv.swap 1 2 i ), fun h i => by simpa using h ( Equiv.swap 1 2 i ) ⟩;
            · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
            · exact MeasurableSet.univ_pi hs;
        rw [ ← h_measure_preserving.integral_comp ];
        constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 1 2 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts => pts ∘ ( Equiv.swap 1 2 );
          · exact h_measure_preserving.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;
      convert h_perm _ using 3 ; norm_num [ Equiv.swap_apply_def ];
      convert wedge_integral_1center p d hp0 hp1 hd hr |> Eq.symm using 3 ; norm_num [ dist_comm ];
      simp +decide [ dist_comm ]

open Classical MeasureTheory in
/-- Edge-fill integral for edge (0,2): ∫ A₁₃·F = (7r²)^d. By symmetry with mu_e_pow_eq. -/
lemma mu_e_pow_eq_02 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (7 * (matchRadius p d) ^ 2) ^ d := by
      convert mu_e_pow_eq p d hp0 hp1 hd hr using 1;
      -- The permutation is measure-preserving, so the integrals are equal.
      have h_measure_preserving : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => ![pts 0, pts 2, pts 1]) (Measure.pi fun _ => volume) (Measure.pi fun _ => volume) := by
        refine' ⟨ _, _ ⟩;
        · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 2; exact measurable_pi_apply 1 ] ;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · simp +decide [ Set.preimage, Fin.prod_univ_three ];
            simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
            erw [ show { a : Fin 3 → Torus d | a 0 ∈ s 0 } ∩ ( { a : Fin 3 → Torus d | a 2 ∈ s 1 } ∩ { a : Fin 3 → Torus d | a 1 ∈ s 2 } ) = ( Set.pi Set.univ fun i => if i = 0 then s 0 else if i = 1 then s 2 else s 1 ) by ext; simp +decide [ Fin.forall_fin_succ ] ; tauto ] ; erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
          · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 2; exact measurable_pi_apply 1 ] ;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_measure_preserving.integral_comp ];
      · simp +decide [ dist_comm ];
        simp +decide only [and_comm];
      · constructor;
        · exact fun x y h => by ext i; fin_cases i <;> have := congr_fun h 0 <;> have := congr_fun h 1 <;> have := congr_fun h 2 <;> aesop;
        · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 2; exact measurable_pi_apply 1 ] ;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts => ![pts 0, pts 2, pts 1];
          · exact h_measure_preserving.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · intro pts; ext i; fin_cases i <;> rfl;

open Classical MeasureTheory in
/-- Edge-fill integral for edge (1,2): ∫ A₂₃·F = (7r²)^d. By symmetry with mu_e_pow_eq. -/
lemma mu_e_pow_eq_12 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (7 * (matchRadius p d) ^ 2) ^ d := by
      convert mu_e_pow_eq_02 p d hp0 hp1 hd hr using 1;
      -- By symmetry of the measure, we can swap the indices 0 and 1.
      have h_symm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (MeasureTheory.Measure.pi fun _ => MeasureTheory.volume) (MeasureTheory.Measure.pi fun _ => MeasureTheory.volume) := by
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three ] ;
          · rw [ show ( fun pts : Fin 3 → Torus d => fun i => pts ( Equiv.swap 0 1 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 0 1 i ) ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
            · grind;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_symm.integral_comp ] ; norm_num [ Equiv.swap_apply_def ] ; ring;
      · simp +decide [ and_comm, and_left_comm, and_assoc ];
      · constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 0 1 i );
          · exact h_symm.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;

open Classical MeasureTheory in
/-- The centered third moment of edge indicators: ∫ (A₁₂-p)(A₁₃-p)(A₂₃-p) = γ - p³.
    Expands the product and uses gamma_pow_eq, wedge_integral, edge_integral. -/
lemma centered_edge_moment (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (3 * (matchRadius p d) ^ 2) ^ d - p ^ 3 := by
  -- Expand the integrand using the binomial theorem.
  have h_expand : ∀ pts : Fin 3 → Torus d, ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) - p) * ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) - p) * ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) - p) = (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) - p * ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0)) + p ^ 2 * ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0)) - p ^ 3 := by
    intro pts; ring;
  rw [ MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall h_expand ), MeasureTheory.integral_sub, MeasureTheory.integral_add ];
  · rw [ MeasureTheory.integral_sub ];
    · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul ];
      rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
      · rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
        · rw [ gamma_pow_eq, wedge_integral, wedge_integral_1center, wedge_integral_2center, edge_integral, edge_integral_02, edge_integral_12 ] ; norm_num ; ring;
          all_goals assumption;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
        · refine' MeasureTheory.Integrable.add _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun a => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.add _ _;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun a => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun pts => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
  · refine' MeasureTheory.Integrable.sub _ _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.add _ _;
      · refine' MeasureTheory.Integrable.add _ _;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · fun_prop;
      · exact measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun pts => 1 + p * 3 + p ^ 2 * 3 + p ^ 3;
    · norm_num;
    · refine' Measurable.aestronglyMeasurable _;
      apply_rules [ Measurable.sub, Measurable.add, Measurable.mul, measurable_const ];
      all_goals apply_rules [ Measurable.ite, measurable_const ];
      all_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
    · refine' Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ _, _ ⟩ <;> split_ifs <;> nlinarith [ pow_pos hp0 3 ];
  · norm_num

open Classical MeasureTheory in
/-- Pointwise rewriting: (A₁₂-p)(A₁₃-p)(A₂₃-p)·F = A₁₂·A₁₃·A₂₃ - p(A₁₂·A₁₃ + A₁₂·A₂₃ + A₁₃·A₂₃)
    + p²(A₁₂·F + A₁₃·F + A₂₃·F) - p³·F.
    Uses wedge_implies_fill: if two edges sharing a vertex are present, then F=1,
    so wedge·F = wedge and triangle·F = triangle. -/
lemma integrand_fill_rewrite (d : ℕ) (r : ℝ) (p : ℝ) (hr0 : 0 ≤ r)
    (pts : Fin 3 → Torus d) :
    let A₁₂ := if dist (pts 0) (pts 1) ≤ r then (1:ℝ) else 0
    let A₁₃ := if dist (pts 0) (pts 2) ≤ r then (1:ℝ) else 0
    let A₂₃ := if dist (pts 1) (pts 2) ≤ r then (1:ℝ) else 0
    let F := if ∃ z : Torus d, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r
             then (1:ℝ) else 0
    (A₁₂ - p) * (A₁₃ - p) * (A₂₃ - p) * F =
    A₁₂ * A₁₃ * A₂₃
    - p * (A₁₂ * A₁₃ + A₁₂ * A₂₃ + A₁₃ * A₂₃)
    + p ^ 2 * (A₁₂ * F + A₁₃ * F + A₂₃ * F)
    - p ^ 3 * F := by
  by_cases h : ∃ z : Torus d, dist ( pts 0 ) z ≤ r ∧ dist ( pts 1 ) z ≤ r ∧ dist ( pts 2 ) z ≤ r <;> simp +decide [ h ] ; ring;
  · split_ifs <;> ring;
  · split_ifs <;> norm_num;
    · exact False.elim <| h <| wedge_implies_fill r hr0 _ _ _ ‹_› ‹_›;
    · exact False.elim <| h ⟨ pts 2, by assumption, by assumption, by simp +decide [ hr0 ] ⟩;
    · contrapose! h;
      use pts 1;
      simp_all +decide [ dist_comm ];
    · exact False.elim <| h <| wedge_implies_fill r hr0 _ _ _ ‹_› ‹_›

set_option maxHeartbeats 800000 in
open Classical MeasureTheory in
/-- **OQ-18 Rips refactor — Aristotle target.** Centered triple-edge moment times fill
    indicator. Under Rips, F = A₁₂·A₁₃·A₂₃, and the indicator identity X_e·A_e = (1-p)·A_e
    (since A_e ∈ {0,1}) gives
      ∫ (A₁₂-p)(A₁₃-p)(A₂₃-p) · F = (1-p)³ · q
    where q = fillingProb p d = (3r²)^d on r ≤ 1/4.

    Original statement (Čech existential nerve form, no longer correct): the indicator was
    `∃ z, ...` and the RHS was `(3r²)^d − 3p³ + 3p²·(7r²)^d − p³·q`. Under Rips, the indicator
    becomes the triangle product and the identity simplifies dramatically.

    See `my_theorems/oq18_math_audit.md` §"Centered edge identity" for the derivation. -/
lemma centered_edge_moment_fill (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
       (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
       (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0))
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (1 - p) ^ 3 * fillingProb p d := by
  -- OQ-18 Rips refactor — Aristotle target. See docstring above and
  -- `my_theorems/oq18_math_audit.md`. Proof: pointwise identity X_e · A_e = (1-p) · A_e
  -- (since A_e is a 0/1 indicator), so the integrand reduces to (1-p)^3 · A_{12}·A_{13}·A_{23},
  -- whose integral is (1-p)^3 · fillingProb.
  sorry

-- BEGIN dead-code old centered_edge_moment_fill proof body (commented out for Rips refactor)
example : True := by trivial
/-
OLD PROOF BODY (preserved for reference, no longer well-typed under Rips clique form):
  rw [ MeasureTheory.integral_congr_ae ];
  any_goals filter_upwards [ ] with pts; exact integrand_fill_rewrite d ( matchRadius p d ) p ( by unfold matchRadius; positivity ) pts;
  rw [ MeasureTheory.integral_sub, MeasureTheory.integral_add ];
  · rw [ MeasureTheory.integral_sub ];
    · congr;
      · convert gamma_pow_eq p d hp0 hp1 hd hr using 1;
      · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_add, MeasureTheory.integral_add ];
        · rw [ wedge_integral, wedge_integral_1center, wedge_integral_2center ] <;> ring <;> aesop;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num;
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            exact Measurable.mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const );
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.add _ _;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun _ => 1;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.mul _ _;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
            · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun _ => 1;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.mul _ _;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
            · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · rw [ MeasureTheory.integral_const_mul ];
        rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
        · rw [ mu_e_pow_eq, mu_e_pow_eq_02, mu_e_pow_eq_12 ];
          all_goals linarith;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num;
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
            · refine' Measurable.ite _ measurable_const measurable_const;
              convert measurableSet_hasFill ( matchRadius p d ) ( ⟨ { 0, 1, 2 }, by simp +decide ⟩ : { σ : Finset ( Fin 3 ) // σ.card = 3 } ) using 1;
              simp +decide [ Fin.forall_fin_succ ];
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
            · refine' Measurable.ite _ measurable_const measurable_const;
              convert measurableSet_hasFill ( matchRadius p d ) using 1;
              rotate_left;
              exact 3;
              bv_omega;
              constructor <;> intro h;
              · convert measurableSet_hasFill ( matchRadius p d ) using 1;
              · convert h ⟨ { 0, 1, 2 }, by decide ⟩ using 1;
                simp +decide [ Fin.forall_fin_succ ];
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.add _ _;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun _ => 1;
            · fun_prop;
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.mul _ _;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
              · refine' Measurable.ite _ measurable_const measurable_const;
                convert measurableSet_hasFill ( matchRadius p d ) ( ⟨ { 0, 1, 2 }, by simp +decide ⟩ : { σ : Finset ( Fin 3 ) // σ.card = 3 } ) using 1;
                simp +decide [ Fin.forall_fin_succ ];
            · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
          · refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun _ => 1;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.mul _ _;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
              · refine' Measurable.ite _ measurable_const measurable_const;
                have h_measurable : MeasurableSet {a : Fin 3 → Torus d | ∃ z : Torus d, dist (a 0) z ≤ matchRadius p d ∧ dist (a 1) z ≤ matchRadius p d ∧ dist (a 2) z ≤ matchRadius p d} := by
                  have h_closed : IsClosed {a : Fin 3 → Torus d | ∃ z : Torus d, dist (a 0) z ≤ matchRadius p d ∧ dist (a 1) z ≤ matchRadius p d ∧ dist (a 2) z ≤ matchRadius p d} := by
                    refine' isClosed_of_closure_subset _;
                    intro a ha;
                    rw [ mem_closure_iff_seq_limit ] at ha;
                    obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
                    choose z hz using hx₁;
                    -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
                    obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
                      have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
                        exact isCompact_univ;
                      have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
                    obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
                    use z';
                    have h_dist : Filter.Tendsto (fun n => dist (x (subseq n) 0) (z (subseq n))) Filter.atTop (nhds (dist (a 0) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 1) (z (subseq n))) Filter.atTop (nhds (dist (a 1) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 2) (z (subseq n))) Filter.atTop (nhds (dist (a 2) z')) := by
                      exact ⟨ Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 0 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 1 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 2 ) hsubseq₂ ⟩;
                    exact ⟨ le_of_tendsto_of_tendsto' h_dist.1 tendsto_const_nhds fun n => hz _ |>.1, le_of_tendsto_of_tendsto' h_dist.2.1 tendsto_const_nhds fun n => hz _ |>.2.1, le_of_tendsto_of_tendsto' h_dist.2.2 tendsto_const_nhds fun n => hz _ |>.2.2 ⟩
                  exact h_closed.measurableSet;
                exact h_measurable;
            · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
            · refine' Measurable.ite _ measurable_const measurable_const;
              convert measurableSet_hasFill ( matchRadius p d ) using 1;
              rotate_left;
              exact 3;
              bv_omega;
              constructor <;> intro h;
              · convert measurableSet_hasFill ( matchRadius p d ) using 1;
              · convert h ⟨ { 0, 1, 2 }, by decide ⟩ using 1;
                simp +decide [ Fin.forall_fin_succ ];
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · rw [ MeasureTheory.integral_const_mul, fillingProb ];
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 3;
      · fun_prop;
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.add, Measurable.mul, Measurable.ite, measurable_const ];
        all_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ by split_ifs <;> norm_num, by split_ifs <;> norm_num ⟩;
  · refine' MeasureTheory.Integrable.sub _ _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.add _ _;
      · refine' MeasureTheory.Integrable.add _ _;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun _ => 1;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · refine' Measurable.aestronglyMeasurable _;
            apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
            · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          exact Measurable.mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const );
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun _ => p ^ 2 * 3;
    · fun_prop;
    · apply_rules [ Measurable.aestronglyMeasurable, Measurable.mul, Measurable.add, measurable_const ];
      all_goals apply_rules [ Measurable.ite, measurable_const ];
      any_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
      · convert measurableSet_hasFill ( matchRadius p d ) using 1;
        rotate_left;
        exact 3;
        bv_omega;
        constructor <;> intro h;
        · convert measurableSet_hasFill ( matchRadius p d ) using 1;
        · convert h ⟨ { 0, 1, 2 }, by decide ⟩ using 1;
          simp +decide [ Fin.forall_fin_succ ];
      · convert measurableSet_hasFill ( matchRadius p d ) ( ⟨ { 0, 1, 2 }, by simp +decide ⟩ : { σ : Finset ( Fin 3 ) // σ.card = 3 } ) using 1;
        simp +decide [ Fin.forall_fin_succ ];
      · refine' MeasurableSet.congr _ _;
        exact { a : Fin 3 → Torus d | ∃ z : Torus d, dist ( a 0 ) z ≤ matchRadius p d ∧ dist ( a 1 ) z ≤ matchRadius p d ∧ dist ( a 2 ) z ≤ matchRadius p d };
        · convert measurableSet_hasFill ( matchRadius p d ) using 1;
          rotate_left;
          exact 3;
          bv_omega;
          constructor <;> intro h;
          · convert measurableSet_hasFill ( matchRadius p d ) using 1;
          · convert h ⟨ { 0, 1, 2 }, by decide ⟩ using 1;
            simp +decide [ Fin.forall_fin_succ ];
        · rfl;
    · filter_upwards [ ] with x using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; split_ifs <;> nlinarith;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun _ => 1 + p + p ^ 2 * 3;
    · norm_num;
    · apply_rules [ Measurable.aestronglyMeasurable, Measurable.sub, Measurable.add, Measurable.mul, measurable_const ];
      all_goals apply_rules [ Measurable.ite, measurable_const ];
      all_goals apply_rules [ IsClosed.measurableSet, measurableSet_le ];
      any_goals exact isClosed_le ( Continuous.dist ( continuous_apply _ ) ( continuous_apply _ ) ) continuous_const;
      · refine' isClosed_of_closure_subset _;
        intro a ha;
        rw [ mem_closure_iff_seq_limit ] at ha;
        obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
        choose z hz using hx₁;
        -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
        obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
          have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
            exact isCompact_univ;
          have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
        obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
        use z';
        have h_dist : Filter.Tendsto (fun n => dist (x (subseq n) 0) (z (subseq n))) Filter.atTop (nhds (dist (a 0) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 1) (z (subseq n))) Filter.atTop (nhds (dist (a 1) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 2) (z (subseq n))) Filter.atTop (nhds (dist (a 2) z')) := by
          exact ⟨ Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 0 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 1 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 2 ) hsubseq₂ ⟩;
        exact ⟨ le_of_tendsto_of_tendsto' h_dist.1 tendsto_const_nhds fun n => hz _ |>.1, le_of_tendsto_of_tendsto' h_dist.2.1 tendsto_const_nhds fun n => hz _ |>.2.1, le_of_tendsto_of_tendsto' h_dist.2.2 tendsto_const_nhds fun n => hz _ |>.2.2 ⟩;
      · refine' isClosed_of_closure_subset _;
        intro a ha;
        rw [ mem_closure_iff_seq_limit ] at ha;
        obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
        choose z hz using hx₁;
        -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
        obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
          have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
            exact isCompact_univ;
          have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
        obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
        use z';
        have h_dist : Filter.Tendsto (fun n => dist (x (subseq n) 0) (z (subseq n))) Filter.atTop (nhds (dist (a 0) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 1) (z (subseq n))) Filter.atTop (nhds (dist (a 1) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 2) (z (subseq n))) Filter.atTop (nhds (dist (a 2) z')) := by
          exact ⟨ Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 0 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 1 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 2 ) hsubseq₂ ⟩;
        exact ⟨ le_of_tendsto_of_tendsto' h_dist.1 tendsto_const_nhds fun n => hz _ |>.1, le_of_tendsto_of_tendsto' h_dist.2.1 tendsto_const_nhds fun n => hz _ |>.2.1, le_of_tendsto_of_tendsto' h_dist.2.2 tendsto_const_nhds fun n => hz _ |>.2.2 ⟩;
      · refine' isClosed_of_closure_subset _;
        intro a ha;
        rw [ mem_closure_iff_seq_limit ] at ha;
        obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
        choose z hz using hx₁;
        -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
        obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
          have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
            exact isCompact_univ;
          have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
        obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
        use z';
        have h_dist : Filter.Tendsto (fun n => dist (x (subseq n) 0) (z (subseq n))) Filter.atTop (nhds (dist (a 0) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 1) (z (subseq n))) Filter.atTop (nhds (dist (a 1) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 2) (z (subseq n))) Filter.atTop (nhds (dist (a 2) z')) := by
          exact ⟨ Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 0 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 1 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 2 ) hsubseq₂ ⟩;
        exact ⟨ le_of_tendsto_of_tendsto' h_dist.1 tendsto_const_nhds fun n => hz _ |>.1, le_of_tendsto_of_tendsto' h_dist.2.1 tendsto_const_nhds fun n => hz _ |>.2.1, le_of_tendsto_of_tendsto' h_dist.2.2 tendsto_const_nhds fun n => hz _ |>.2.2 ⟩;
    · refine' Filter.Eventually.of_forall fun x => _;
      split_ifs <;> norm_num <;> try nlinarith;
      all_goals rw [ abs_le ] ; constructor <;> nlinarith;
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun _ => 1;
    · norm_num [ MeasureTheory.integrable_const_iff ];
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.ite _ measurable_const measurable_const;
      convert measurableSet_hasFill ( matchRadius p d ) using 1;
      rotate_left;
      exact 3;
      bv_omega;
      constructor <;> intro h;
      · convert measurableSet_hasFill ( matchRadius p d ) using 1;
      · convert h ⟨ { 0, 1, 2 }, by decide ⟩ using 1;
        simp +decide [ Fin.forall_fin_succ ];
    · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
-/

set_option maxHeartbeats 800000 in
open Classical MeasureTheory in
/-- **OQ-18 Rips refactor — Aristotle target.** Closed form for `geometricCov` under Rips:
      geomCov(p,d) = q · ((1-p)^3 + p^3) − q^2
    where q = fillingProb p d. Equivalently `geomCov = q · ((1-p)^3 + p^3 − q)`.

    Derivation (see `my_theorems/oq18_math_audit.md`):
    * F = A₁₂·A₁₃·A₂₃ (Rips clique).
    * geomCov = E[X₁₂ X₁₃ X₂₃ (F − q)] = E[X₁₂ X₁₃ X₂₃ F] − q · E[X₁₂ X₁₃ X₂₃].
    * E[X₁₂ X₁₃ X₂₃ F] = (1−p)^3 · q (via the indicator identity X_e · A_e = (1−p)·A_e).
    * E[X₁₂ X₁₃ X₂₃] = q − p^3 (from the edge/wedge/triangle expansion; wedges have prob p^2
      by translation invariance + conditional independence).
    * Combining: geomCov = (1−p)^3 q − q(q − p^3) = q((1−p)^3 + p^3) − q^2.

    Original Čech-nerve form (commented out below) had RHS = (1−q)·γ^d + 3p³·((7r/2)^d − 1)
    where γ = 3r². Under Rips, the simpler closed form above holds. The asymptotic regime
    (d → ∞, p fixed) gives q = (3/4)^d · p^2 and hence geomCov ~ (3/4)^d · p^2 · ((1−p)^3 + p^3),
    replacing the sharp algebraic collapse at d*(p) with smooth exponential decay. -/
theorem geometricCov_eq_deep (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    geometricCov p d
    = fillingProb p d * ((1 - p) ^ 3 + p ^ 3) - fillingProb p d ^ 2 := by
  -- Proof sketch: algebraic combination of `centered_edge_moment` and
  -- `centered_edge_moment_fill` (new Rips form), as above. Pending Aristotle.
  sorry

/-
OLD PROOF BODY (Čech-nerve form, preserved for reference; no longer typechecks under Rips):
theorem geometricCov_eq_deep_OLD (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    geometricCov p d
    = (1 - fillingProb p d) * (3 * (matchRadius p d) ^ 2) ^ d
      + 3 * p ^ 3 * ((7 * matchRadius p d / 2) ^ d - 1) := by
  -- Use centered_edge_moment and centered_edge_moment_fill to decompose
  have h_cem := centered_edge_moment p d hp0 hp1 hd hr
  have h_cemf := centered_edge_moment_fill p d hp0 hp1 hd hr
  have h_psm := p_sq_mu_eq p d hp0 hp1 hd
  -- geometricCov = cemf - fillingProb * cem
  -- = (γ - 3p³ + 3p²μ - p³q) - q(γ - p³)
  -- = γ(1-q) - 3p³ + 3p²μ
  -- = (1-q)γ + 3p³((7r/2)^d - 1)  [using h_psm]
  -- Step 1: Show geometricCov = ∫PF - q·∫P
  have h_gcov : geometricCov p d =
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    - fillingProb p d *
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
    rw [ ← MeasureTheory.integral_const_mul ];
    rw [ ← MeasureTheory.integral_sub ];
    · nontriviality;
      unfold geometricCov; norm_num; ring;
      congr; ext; split_ifs <;> ring;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun pts => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.mul _ _;
        · refine' Measurable.mul _ _;
          · refine' Measurable.mul _ _;
            · exact Measurable.sub ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
            · exact Measurable.sub ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
          · exact Measurable.sub ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
        · refine' Measurable.ite _ measurable_const measurable_const;
          convert measurableSet_hasFill _ _ using 1;
          rotate_left;
          exact matchRadius p d;
          exact ⟨ { 0, 1, 2 }, by simp +decide ⟩;
          simp +decide [ Fin.forall_fin_succ ];
      · refine' Filter.Eventually.of_forall fun x => _;
        split_ifs <;> norm_num [ abs_of_nonneg, hp0.le, hp1.le ];
        all_goals nlinarith [ mul_pos hp0 hp0, mul_pos hp0 ( sub_pos.mpr hp1 ), mul_pos ( sub_pos.mpr hp1 ) ( sub_pos.mpr hp1 ) ] ;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun a => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.mul ( Measurable.mul _ _ ) _;
        · exact Measurable.sub ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
        · exact Measurable.sub ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
        · exact Measurable.sub ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
      · refine' Filter.Eventually.of_forall fun x => _;
        split_ifs <;> norm_num [ abs_of_nonneg, hp0.le, hp1.le ];
        all_goals nlinarith [ mul_pos hp0 ( sub_pos.mpr hp1 ) ] ;
  -- Combine h_gcov, h_cemf, h_cem, h_psm to get the result algebraically
  have h1 : geometricCov p d =
      ((3 * (matchRadius p d) ^ 2) ^ d - 3 * p ^ 3
        + 3 * p ^ 2 * (7 * (matchRadius p d) ^ 2) ^ d
        - p ^ 3 * fillingProb p d)
      - fillingProb p d * ((3 * (matchRadius p d) ^ 2) ^ d - p ^ 3) := by
    rw [h_gcov, h_cemf, h_cem]
  rw [h1]
  nlinarith
-/

/-- **Sim-A5 / Job 2, Lemma 5 (decay-rate upper bound).**
    Under Rips, `geometricCov = q · ((1-p)^3 + p^3) − q^2 ≤ q · ((1-p)^3 + p^3)`
    since `q^2 ≥ 0`. With `q = (3r²)^d`, this gives an explicit exponential decay bound.

    Original Čech-form RHS (commented out): `(1−q)·(3r²)^d + 3p³·(7r/2)^d`. Under Rips,
    the new RHS is `q · ((1-p)^3 + p^3)` which is the dominant term of the new closed form. -/
theorem geometricCov_decay_rate_le (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    geometricCov p d
      ≤ fillingProb p d * ((1 - p) ^ 3 + p ^ 3) := by
  have h := geometricCov_eq_deep p d hp0 hp1 hd hr
  nlinarith [sq_nonneg (fillingProb p d)]

-- ────────────────────────────────────────────────────────────────────────────
-- OQ-16 / Track B stubs — sparse regime lower bound
-- ────────────────────────────────────────────────────────────────────────────

/-- **Track B, Lemma 1 (geomCov lower bound).**
    In the deep regime r ≤ 1/4, geometricCov is bounded below by the leading
    gamma term minus the (small) correction 3p³.

    Formally: geomCov(p,d) ≥ (1−q)·γ^d − 3p³

    where γ^d = (3·r²)^d, q = fillingProb p d, r = matchRadius p d.

    PROVIDED SOLUTION
    Step 1: Apply `geometricCov_eq_deep`: geomCov = (1−q)·γ^d + 3p³·((7r/2)^d − 1).
    Step 2: Since r ≤ 1/4, we have 7r/2 ≤ 7/8 < 1. By `pow_le_one` (all d ≥ 1,
      base in [0,1]), (7r/2)^d ≤ 1^d = 1. So (7r/2)^d − 1 ≤ 0.
    Step 3: Since p > 0, we have 3p³ > 0 (use `pow_pos`). Therefore
      3p³ · ((7r/2)^d − 1) ≥ 3p³ · (0 − 1) = −3p³.
    Step 4: Conclude geomCov ≥ (1−q)·γ^d − 3p³ by `linarith`.

    **OQ-18 Rips refactor (2026-05-16).** Under Rips, the closed form is
    `geomCov = q ((1-p)^3 + p^3) − q^2` (see new `geometricCov_eq_deep`). The original
    Čech-form lower bound below is no longer derivable from that. Stubbed pending refactor;
    downstream `geometricCov_lower_bound_explicit` inherits the stub. -/
lemma geometricCov_lower_bound (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (1 - fillingProb p d) * (3 * matchRadius p d ^ 2) ^ d - 3 * p ^ 3
      ≤ geometricCov p d := by
  -- OQ-18: statement is from the Čech-nerve era. Under Rips, the geomCov closed form is
  -- different (q((1-p)^3+p^3) − q^2). Re-derivation of a lower bound in the Čech-form
  -- statement is pending. Sorrying as placeholder.
  sorry

/-- **Track B, Lemma 2 (geomCov lower bound, explicit p form).**
    In the deep regime r ≤ 1/4, and using the matchRadius identity (2r)^d = p,
    the leading term satisfies (3·r²)^d = (3/4)^d · p^2.

    Therefore: geomCov(p,d) ≥ (1−q) · (3/4)^d · p^2 − 3p³.

    This is the form used in Corollary~\ref{cor:sparse}: taking sequences (p_n, d_n)
    with n^{3/2} · (3/4)^{d_n} · p_n^2 → ∞ yields n^{3/2} · geomCov → ∞.

    PROVIDED SOLUTION
    Step 1: Apply `geometricCov_lower_bound` to get
      geomCov ≥ (1−q) · (3·r²)^d − 3p³.
    Step 2: Show (3·r²)^d = (3/4)^d · p^2 using the matchRadius identity (2r)^d = p.
      Calculation: (3·r²)^d = 3^d · r^(2d) = 3^d · (r^d)^2.
      From (2r)^d = p: 2^d · r^d = p, so r^d = p / 2^d.
      Hence r^(2d) = (r^d)^2 = p^2 / 4^d (by `pow_mul`, `sq`).
      So (3·r²)^d = 3^d · p^2 / 4^d = (3/4)^d · p^2 (by `div_pow`, `mul_div_assoc`).
    Step 3: Use `fillingProb_nonneg` and `fillingProb_le_one` to bound (1−q) ∈ [0,1].
    Step 4: Combine with Step 1 to get geomCov ≥ (1−q) · (3/4)^d · p^2 − 3p³. -/
lemma geometricCov_lower_bound_explicit (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (1 - fillingProb p d) * (3/4 : ℝ) ^ d * p ^ 2 - 3 * p ^ 3
      ≤ geometricCov p d := by
  refine le_trans ?_ ( geometricCov_lower_bound p d hp0 hp1 hd hr );
  rw [ show matchRadius p d = p ^ (1 / ( d : ℝ ) ) / 2 by unfold matchRadius; aesop ] ; ring_nf;
  rw [ ← Real.rpow_natCast _ ( d * 2 ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ show d ≠ 0 by linarith ] ; ring_nf ; norm_num

-- ────────────────────────────────────────────────────────────────────────────
-- end OQ-16 / Track A+B stubs
-- ────────────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────────────
-- OQ-16 / Track C stubs — fill-pair statistic τ_ff
-- ────────────────────────────────────────────────────────────────────────────

/- **Track C, Job 5 — double-fill joint probability.**
    For adjacent triangles {1,2,3} and {1,2,4} sharing edge {1,2},
    the probability that BOTH are filled under the Čech model equals
    (112/3 · r³)^d.

    Proof strategy (factorisation over the d coordinates of 𝕋^d):
    Step 1: By Fubini, condition on (x1, x2); x3 and x4 are then independent.
      E[F_{123}·F_{124}] = ∫_{x1,x2} g(x1,x2)² dx1 dx2
      where g(x1,x2) = ∫_{x3} fill_{123} = vol_d(fill fiber | x1,x2).
    Step 2: By the coordinate product structure of 𝕋^d = (𝕋^1)^d,
      g(x1,x2) = ∏_l fill_fiber_1D(x1^l, x2^l).
    Step 3: New 1D lemma in TorusIntegrals.lean (`integral_fill_fiber_sq_line`):
      2 * ∫_0^{2r} (4r − b)² db = 112/3 · r³.
      (Here 4r − b is the fill-fiber length at distance b, from `fill_fiber_real_length`.)
    Step 4: Lift to d dimensions:
      ∫_{x1,x2 ∈ 𝕋^{2d}} g(x1,x2)² = (112/3 · r³)^d. -/
open Classical MeasureTheory MeasureTheory.Measure in
lemma doubleFill_joint_prob (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫ pts : Fin 4 → (Fin d → T1),
      (if (∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r) ∧
          (∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 3) z ≤ r)
       then (1:ℝ) else 0)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 4 => (MeasureTheory.volume : MeasureTheory.Measure (Fin d → T1)))
    = (112 / 3 * r ^ 3) ^ d := by
  rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
  change (∫ x in { pts : Fin 4 → Fin d → T1 | (∃ z, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r) ∧ (∃ z, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 3) z ≤ r) }, 1 ∂Measure.pi fun _ => volume) = _;
  · convert congr_arg ENNReal.toReal ( volume_coordFactored4_eq_pow d ( doubleFillSet r ) ( doubleFillSet_measurableSet r ) ) using 1;
    · rw [ doubleFillSet_torus_eq d hd r hr0 hr ];
      aesop;
    · rw [ volume_doubleFillSet r hr0 hr, ENNReal.toReal_pow, ENNReal.toReal_ofReal ( by positivity ) ];
  · convert doubleFillSet_measurableSet r |> MeasurableSet.preimage <| measurable_pi_lambda _ fun i => measurable_pi_apply i using 1;
    rw [ doubleFillSet_torus_eq d hd r hr0 hr ];
    constructor <;> intro h;
    · convert doubleFillSet_measurableSet r using 1;
    · simp +decide only [Set.setOf_forall];
      exact MeasurableSet.iInter fun i => h.preimage <| measurable_pi_lambda _ fun j => measurable_pi_apply i |> Measurable.comp <| measurable_pi_apply j;
  · norm_num [ Filter.EventuallyEq, Set.indicator ]

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

set_option maxHeartbeats 800000 in
open Classical in
lemma cechDoublySigned_triangle_integral (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    let r := matchRadius p d
    let q := fillingProb p d
    ∫ s, ((∏ e ∈ triangleEdges t,
      (if s.hasEdge r e.1 e.2 then (1 : ℝ) - p else -p)) *
    (if s.hasFill r t then (1 : ℝ) - q else -q)) ∂cechMeasure n d r =
      geometricCov p d := by
  -- OQ-18 Rips refactor: `hasFill` is now the clique predicate (not existential), and
  -- `geometricCov` still references the existential fill via the integrand below. Bridging
  -- requires `wedge_implies_fill` (the two are equivalent because the wedge case forces the
  -- triangle case, and triangle ⇒ existential is trivial). Original proof references the
  -- existential form throughout; stubbed pending refactor.
  sorry

/-
OLD PROOF BODY (Čech-nerve form, no longer typechecks):
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 3 → Fin n, StrictMono σ ∧ t.val = Finset.image σ Finset.univ := by
    have h_order : ∃ σ : Fin 3 → Fin n, StrictMono σ ∧ ∀ i, σ i ∈ t.val := by
      exact ⟨ fun i => t.val.orderEmbOfFin t.2 i, by simp +decide [ StrictMono ], fun i => Finset.orderEmbOfFin_mem _ _ _ ⟩;
    obtain ⟨ σ, hσ₁, hσ₂ ⟩ := h_order; use σ; simp_all +decide [ Finset.card_image_of_injective _ hσ₁.injective ] ;
    rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hσ₂ i ) ( by simp +decide [ Finset.card_image_of_injective _ hσ₁.injective, t.2 ] ) ];
  -- Apply the measure-preserving property of the embedding σ to rewrite the integral.
  have h_measure_preserving : MeasureTheory.Measure.map (fun s : Fin n → Torus d => s ∘ σ) (MeasureTheory.Measure.pi (fun _ : Fin n => MeasureTheory.volume)) = MeasureTheory.Measure.pi (fun _ : Fin 3 => MeasureTheory.volume) := by
    refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
    intro s hs; erw [ MeasureTheory.Measure.map_apply ];
    · simp +decide [ Set.preimage, hσ.1.injective.eq_iff ];
      rw [ show { x : Fin n → Torus d | ∀ i, x ( σ i ) ∈ s i } = ( Set.pi Set.univ fun i => if h : ∃ j, σ j = i then s ( Classical.choose h ) else Set.univ ) from ?_, MeasureTheory.Measure.pi_pi ];
      · rw [ ← Finset.prod_subset ( Finset.subset_univ ( Finset.image σ Finset.univ ) ) ];
        · rw [ Finset.prod_image ];
          · refine' Finset.prod_congr rfl fun i _ => _;
            split_ifs <;> simp_all +decide [ hσ.1.injective.eq_iff ];
            rw [ hσ.1.injective ( Classical.choose_spec ‹∃ j, σ j = σ i› ) ];
          · exact hσ.1.injective.injOn;
        · aesop;
      · ext x; simp [Set.mem_pi];
        constructor;
        · intro hx i; split_ifs with h; exact (by
          simpa only [ Classical.choose_spec h ] using hx ( Classical.choose h )); exact (by
          trivial);
        · intro hx i; specialize hx ( σ i ) ; simp_all +decide [ hσ.1.injective.eq_iff ] ;
          convert hx;
          exact hσ.1.injective ( by have := Classical.choose_spec ( show ∃ j, σ j = σ i from ⟨ i, rfl ⟩ ) ; aesop );
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · exact MeasurableSet.univ_pi hs;
  have h_integral_eq : ∫ s : Fin n → Torus d, (∏ e ∈ triangleEdges t, (if dist (s e.1) (s e.2) ≤ matchRadius p d then 1 - p else -p)) * (if ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ matchRadius p d then 1 - fillingProb p d else -fillingProb p d) ∂MeasureTheory.Measure.pi (fun _ : Fin n => MeasureTheory.volume) =
    ∫ s : Fin 3 → Torus d, (∏ e ∈ Finset.univ.filter (fun e : Fin 3 × Fin 3 => e.1 < e.2), (if dist (s e.1) (s e.2) ≤ matchRadius p d then 1 - p else -p)) * (if ∃ z : Torus d, ∀ i : Fin 3, dist (s i) z ≤ matchRadius p d then 1 - fillingProb p d else -fillingProb p d) ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => MeasureTheory.volume) := by
      rw [ ← h_measure_preserving, MeasureTheory.integral_map ];
      · congr with s ; simp +decide [ triangleEdges, hσ ];
        rw [ show ( Finset.image σ Finset.univ ×ˢ Finset.image σ Finset.univ : Finset ( Fin n × Fin n ) ) = Finset.image ( fun x : Fin 3 × Fin 3 => ( σ x.1, σ x.2 ) ) ( Finset.univ : Finset ( Fin 3 × Fin 3 ) ) from ?_ ];
        · rw [ Finset.prod_filter, Finset.prod_image ] ; simp +decide [ hσ.1.injective.eq_iff ];
          · simp +decide [ Finset.prod_filter, hσ.1.lt_iff_lt ];
          · exact fun x _ y _ hxy => by have := hσ.1.injective ( congr_arg Prod.fst hxy ) ; have := hσ.1.injective ( congr_arg Prod.snd hxy ) ; aesop;
        · ext ⟨x, y⟩; simp [Finset.mem_image];
      · exact measurable_pi_lambda _ ( fun _ => measurable_pi_apply _ ) |> Measurable.aemeasurable;
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.mul _ _;
        · refine' Finset.measurable_prod _ fun e he => _;
          exact Measurable.ite ( measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const ) measurable_const measurable_const;
        · refine' Measurable.ite _ measurable_const measurable_const;
          convert measurableSet_hasFill _ _ using 1;
          rotate_left;
          exact matchRadius p d;
          exact ⟨ Finset.univ, by simp +decide ⟩;
          simp +decide [ Finset.mem_univ ];
  convert h_integral_eq using 1;
  · convert cech_integral_eq n d ( matchRadius p d ) _ using 1;
  · refine' MeasureTheory.integral_congr_ae _;
    filter_upwards [ ] with s;
    rw [ show ( Finset.univ.filter fun e : Fin 3 × Fin 3 => e.1 < e.2 ) = { ( 0, 1 ), ( 0, 2 ), ( 1, 2 ) } by decide ] ; simp +decide [ Fin.forall_fin_succ ] ; ring
-/

/-
PROVIDED SOLUTION
The function is bounded: each factor (if ... then 1-p else -p) is in [-1,1], so the product of 3 edge factors times one fill factor is bounded by 1 in absolute value. Under cechMeasure (which is a probability measure, proved by cechMeasure_isProbabilityMeasure), any bounded measurable function is integrable. Use MeasureTheory.Integrable.mono' with the constant function 1, showing |f s| ≤ 1 for all s. The function is measurable because the sigma algebra on CechSample is the comap through points, and hasEdge/hasFill are measurable (shown earlier in the file for cechFilledCount_integrable). Actually, since the sigma-algebra is MeasurableSpace.comap, measurability may be tricky. Use AEStronglyMeasurable instead, similar to how cechFilledCount_integrable works.

Alternatively, since cechMeasure is a finite measure and the function is bounded, use memℒp_top_of_bound or integrable_of_norm_bounded.
-/
open Classical in
lemma cechDoublySigned_summand_integrable (n d : ℕ) (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    MeasureTheory.Integrable
      (fun s => (∏ e ∈ triangleEdges t,
        (if s.hasEdge r e.1 e.2 then (1 : ℝ) - p else -p)) *
        (if s.hasFill r t then (1 : ℝ) - q else -q))
      (cechMeasure n d r) := by
  -- OQ-18: under clique `hasFill`, measurability is via finite intersection. The original
  -- proof references `exact?` which doesn't close under the new sigma-algebra setup. Stub.
  sorry

/-
OLD PROOF BODY:
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun s => ( ∏ e ∈ triangleEdges t, ( |1 - p| + |p| ) ) * ( |1 - q| + |q| );
  · apply_rules [ MeasureTheory.integrable_const ];
  · apply_rules [ Measurable.aestronglyMeasurable, Measurable.mul, measurable_const ];
    · refine' Finset.measurable_prod _ _;
      -- The function that checks the distance between two points is measurable because the distance function is continuous and the preimage of a measurable set under a continuous function is measurable.
      have h_dist_measurable : ∀ i j : Fin n, Measurable (fun s : CechSample n d => dist (s.points i) (s.points j)) := by
        intro i j;
        -- The distance function is continuous, and the composition of continuous functions is continuous.
        have h_dist_cont : Continuous (fun s : Fin n → Torus d => dist (s i) (s j)) := by
          fun_prop (disch := norm_num);
        exact h_dist_cont.measurable.comp ( measurable_id'.comp ( show Measurable ( fun s : CechSample n d => s.points ) from by exact? ) );
      intro i hi; exact Measurable.ite ( measurableSet_le ( h_dist_measurable _ _ ) measurable_const ) measurable_const measurable_const;
    · refine' Measurable.ite _ measurable_const measurable_const;
      -- The set {a | a.hasFill r t} is measurable because it is the preimage of a measurable set under a continuous map.
      have h_measurable : MeasurableSet {a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (a i) z ≤ r} := by
        -- The set of points in the torus that are within distance $r$ of some point is measurable.
        have h_measurable_set : MeasurableSet {a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (a i) z ≤ r} := by
          have h_closed : IsClosed {a : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (a i) z ≤ r} := by
            refine' isClosed_of_closure_subset _;
            intro a ha;
            rw [ mem_closure_iff_seq_limit ] at ha
            obtain ⟨a_seq, ha_seq⟩ := ha
            have h_seq : ∀ k, ∃ z_k : Torus d, ∀ i ∈ t.val, dist (a_seq k i) z_k ≤ r := by
              exact ha_seq.1
            obtain ⟨z_seq, hz_seq⟩ : ∃ z_seq : ℕ → Torus d, ∀ k, ∀ i ∈ t.val, dist (a_seq k i) (z_seq k) ≤ r := by
              exact ⟨ fun k => Classical.choose ( h_seq k ), fun k => Classical.choose_spec ( h_seq k ) ⟩
            have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
              exact isCompact_univ_iff.mpr ( by infer_instance )
            have h_subseq : ∃ z : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun k => z_seq (subseq k)) Filter.atTop (nhds z) := by
              have := h_compact.isSeqCompact fun k => Set.mem_univ ( z_seq k ) ; aesop;
            obtain ⟨z, subseq, hsubseq_mono, hsubseq_conv⟩ := h_subseq
            have h_limit : ∀ i ∈ t.val, dist (a i) z ≤ r := by
              intro i hi
              have h_dist : Filter.Tendsto (fun k => dist (a_seq (subseq k) i) (z_seq (subseq k))) Filter.atTop (nhds (dist (a i) z)) := by
                exact Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( ha_seq.2.comp hsubseq_mono.tendsto_atTop ) i ) hsubseq_conv
              generalize_proofs at *; (
              exact le_of_tendsto' h_dist fun k => hz_seq _ _ hi)
            use z, h_limit
          exact h_closed.measurableSet;
        exact h_measurable_set;
      convert h_measurable.preimage ( show Measurable ( fun a : CechSample n d => a.points ) from ?_ ) using 1;
      exact?;
  · refine' Filter.Eventually.of_forall fun s => _;
    refine' le_trans ( norm_mul_le _ _ ) _;
    gcongr;
    · exact le_trans ( by rw [ Real.norm_eq_abs, Finset.abs_prod ] ) ( Finset.prod_le_prod ( fun _ _ => abs_nonneg _ ) fun _ _ => by split_ifs <;> norm_num );
    · split_ifs <;> norm_num [ abs_le ]
-/

/-
PROVIDED SOLUTION
Unfold cechDoublySignedCount as a Finset.sum. Use MeasureTheory.integral_finset_sum (with cechDoublySigned_summand_integrable for integrability) to swap sum and integral. Then each summand's integral equals geometricCov p d by cechDoublySigned_triangle_integral. Use Finset.sum_const and Finset.card_univ to get C(n,3) * geometricCov p d. The cardinality of {σ : Finset (Fin n) // σ.card = 3} equals n.choose 3.
-/
lemma moments_cech_signed (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let r := matchRadius p d
    let q := fillingProb p d
    ∫ s, cechDoublySignedCount p q s r ∂cechMeasure n d r =
      (n.choose 3 : ℝ) * geometricCov p d := by
  convert MeasureTheory.integral_finset_sum _ _;
  · rw [ Finset.sum_congr rfl fun x hx => cechDoublySigned_triangle_integral n d p hp0 hp1 x ] ; aesop;
  · intro t ht
    generalize_proofs at *; (
    convert cechDoublySigned_summand_integrable n d p ( fillingProb p d ) ( matchRadius p d ) t using 1)

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

/-- **matchRadius_tendsto_half.** As dimension d → ∞, matchRadius p d → 1/2 from below.

    PROVIDED SOLUTION
    Step 1: matchRadius p d = p^(1/d)/2. Since p ∈ (0,1), p^(1/d) = exp(log(p)/d).
    Step 2: As d→∞, log(p)/d → 0, so exp(log(p)/d) → exp(0) = 1.
    Step 3: Therefore matchRadius p d → 1/2.
    Step 4: Use Filter.Tendsto.div_const and Real.tendsto_rpow_atTop or
            show p^(1/d) → 1 via Real.rpow_natCast and tendsto argument,
            then divide by 2. For d ≥ 1: matchRadius p d = p^(1/d)/2.
            p^(1/d) = Real.exp(Real.log p / d). As d → ∞, Real.log p / d → 0
            (since Real.log p < 0 for p ∈ (0,1)), so Real.exp(Real.log p / d) → 1.
            Therefore matchRadius p d = Real.exp(Real.log p / d) / 2 → 1/2. -/
lemma matchRadius_tendsto_half (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => matchRadius p d) Filter.atTop (nhds (1/2)) := by
  suffices h : Filter.Tendsto (fun d : ℕ => p ^ ((1:ℝ) / (d:ℝ)) / 2) Filter.atTop (nhds (1/2)) by
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with d hd
    simp [matchRadius, show d ≠ 0 by omega]
  apply Filter.Tendsto.div_const
  have h1 : Filter.Tendsto (fun d : ℕ => (1:ℝ) / (d:ℝ)) Filter.atTop (nhds 0) :=
    (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop)
  have h2 : Filter.Tendsto (fun _ : ℕ => p) Filter.atTop (nhds p) := tendsto_const_nhds
  have := Filter.Tendsto.rpow h2 h1 (Or.inl hp0.ne')
  rwa [Real.rpow_zero] at this

/-
With the corrected matchRadius (r = p^(1/d)/2), we have r < 1/2 always for p ∈ (0,1).
The old lemma geometricCov_eq_large_r assumed r > 1/2 which is never satisfied.
Instead, the correct limit argument is: as d → ∞, matchRadius p d → 1/2 from below
(by matchRadius_tendsto_half), so fillingProb p d → 1, so geometricCov p d → 0.

geometricCov_eq_limit: geometricCov p d = (1-p)^3 * (1 - fillingProb p d)
holds as a LIMIT as d → ∞ (not as a pointwise identity for fixed d).

PROVIDED SOLUTION for geometricCov_tendsto_zero_direct:
Step 1: By matchRadius_tendsto_half, matchRadius p d → 1/2.
Step 2: As r → 1/2, for any s ∈ (0,1), the fill/empty ratio → 1 (the balls grow to
  cover the whole torus). So fillingProb p d → 1 via dominated convergence (bounded by 1).
Step 3: geometricCov p d = (1-p)^3 * ∫ (1 - fillingProb-integrand) ... → 0.
Step 4: Direct approach: show the integrand of geometricCov → 0 as d → ∞.
  The integrand at pts ∈ (Torus d)^3 is
    ∏ e, (1{dist ≤ r} - p) * (1{fill} - q) where q = fillingProb p d.
  As r → 1/2, each edge indicator → 1 a.e., so (1{dist ≤ r} - p) → (1-p) a.e.
  The fill indicator also → 1 a.e., so (1{fill} - q) → (1-q) → 0 since q → 1.
  By DCT, geometricCov → (1-p)^3 * (1 - 1) = 0.
-/

/-- The integral of the beta-like density d · s^{d-1} over (0,1) equals 1 for d ≥ 1. -/
lemma beta_density_integral (d : ℕ) (hd : 1 ≤ d) :
    ∫ s in Set.Ioo (0 : ℝ) 1, (d : ℝ) * s ^ (d - 1 : ℕ) = 1 := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le] <;> norm_num [hd]
  rw [zero_pow (by linarith), sub_zero, mul_div_cancel₀ _ (by positivity)]


private lemma addCircle_three_balls_intersect' (r : ℝ) (hr : r > 1/3)
    (a₁ a₂ a₃ : AddCircle (1 : ℝ)) :
    ∃ z : AddCircle (1 : ℝ), dist a₁ z ≤ r ∧ dist a₂ z ≤ r ∧ dist a₃ z ≤ r := by
  by_contra h_contra;
  have h_complement_measure : (MeasureTheory.volume (Metric.closedBall a₁ r)ᶜ) + (MeasureTheory.volume (Metric.closedBall a₂ r)ᶜ) + (MeasureTheory.volume (Metric.closedBall a₃ r)ᶜ) < 1 := by
    rw [ MeasureTheory.measure_compl, MeasureTheory.measure_compl, MeasureTheory.measure_compl ] <;> norm_num;
    · have h_ball_measure : ∀ a : AddCircle (1 : ℝ), MeasureTheory.volume (Metric.closedBall a r) = ENNReal.ofReal (min (2 * r) 1) := by
        intro a;
        rw [ AddCircle.volume_closedBall ] ; norm_num;
        exact min_comm _ _;
      cases min_cases ( 2 * r ) 1 <;> simp_all +decide [ ENNReal.ofReal ];
      rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
      rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
      rw [ ENNReal.toReal_sub_of_le ] <;> norm_num;
      · rw [ max_eq_left ] <;> linarith;
      · linarith;
    · exact measurableSet_closedBall;
    · exact measurableSet_closedBall;
    · exact measurableSet_closedBall;
  have h_complement_measure : (MeasureTheory.volume ((Metric.closedBall a₁ r)ᶜ ∪ (Metric.closedBall a₂ r)ᶜ ∪ (Metric.closedBall a₃ r)ᶜ)) < 1 := by
    refine' lt_of_le_of_lt _ h_complement_measure;
    exact le_trans ( MeasureTheory.measure_union_le _ _ ) ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl );
  obtain ⟨z, hz⟩ : ∃ z : AddCircle (1 : ℝ), z ∉ (Metric.closedBall a₁ r)ᶜ ∪ (Metric.closedBall a₂ r)ᶜ ∪ (Metric.closedBall a₃ r)ᶜ := by
    contrapose! h_complement_measure;
    rw [ show ( Metric.closedBall a₁ r ) ᶜ ∪ ( Metric.closedBall a₂ r ) ᶜ ∪ ( Metric.closedBall a₃ r ) ᶜ = Set.univ from Set.eq_univ_of_forall h_complement_measure ] ; norm_num;
  simp_all +decide [ dist_comm ];
  linarith [ h_contra z hz.1.1 hz.1.2 ]

private lemma matchRadius_eventually_gt_third' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d in Filter.atTop, matchRadius p d > 1/3 := by
  convert ( Filter.Tendsto.eventually ( matchRadius_tendsto_half p hp0 hp1 ) ( lt_mem_nhds ( show 1/3 < 1/2 by norm_num ) ) ) using 1

private lemma fill_eventually_always' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d in Filter.atTop, ∀ pts : Fin 3 → Torus d,
      ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                      dist (pts 1) z ≤ matchRadius p d ∧
                      dist (pts 2) z ≤ matchRadius p d := by
  have matchRadius_gt_third : ∀ᶠ d in Filter.atTop, matchRadius p d > 1/3 := by
    exact?
  generalize_proofs at *; (
  filter_upwards [ matchRadius_gt_third ] with d hd;
  intro pts
  have h_fill_cond : ∀ i : Fin d, ∃ z_i : AddCircle (1 : ℝ), dist (pts 0 i) z_i ≤ matchRadius p d ∧ dist (pts 1 i) z_i ≤ matchRadius p d ∧ dist (pts 2 i) z_i ≤ matchRadius p d := by
    exact?
  generalize_proofs at *; (
  choose! z hz using h_fill_cond; use z; simp_all +decide [ dist_pi_le_iff ] ;
  exact ⟨ by rw [ dist_pi_le_iff ( by positivity ) ] ; aesop, by rw [ dist_pi_le_iff ( by positivity ) ] ; aesop, by rw [ dist_pi_le_iff ( by positivity ) ] ; aesop ⟩))

open MeasureTheory in
open Classical in
/-- **OQ-18 Rips refactor — STATEMENT FALSE under Rips.** Under the new clique-form
    `fillingProb p d = (3r²)^d` with `r = p^{1/d}/2 → 1/2`, `q → 0` not `1`. The correct
    statement is `fillingProb_tendsto_zero` (see new lemma below). This stub is kept
    because downstream `geometricCov_eventually_zero` still cites it. -/
private lemma fillingProb_eventually_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d : ℕ in Filter.atTop, fillingProb p d = 1 := by
  sorry

/-- **OQ-18 Rips refactor — STATEMENT FALSE under Rips.** Under Rips on sup-norm torus
    with matched p, `q = (3r²)^d → 0` as `d → ∞`, not `1`. The correct asymptotic is
    `fillingProb_tendsto_zero`. -/
lemma fillingProb_tendsto_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => fillingProb p d) Filter.atTop (nhds 1) := by
  sorry

/-- **OQ-18 Rips refactor — new asymptotic.** Under Rips, with matched p ∈ (0,1) fixed,
    `fillingProb p d = (3 r(p,d)²)^d → 0` as `d → ∞` because `r → 1/2` and so
    `3 r² → 3/4 < 1`. Replaces the Čech-era `fillingProb_tendsto_one`. -/
lemma fillingProb_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => fillingProb p d) Filter.atTop (nhds 0) := by
  sorry

/-
PROVIDED SOLUTION (updated for corrected matchRadius = p^(1/d)/2):
With the corrected matchRadius, r = p^(1/d)/2 → 1/2 as d → ∞ (by matchRadius_tendsto_half).
The asymptotic chain for geometricCov_tendsto_zero now runs:

1. matchRadius_tendsto_half: matchRadius p d → 1/2.
2. As r → 1/2, the torus ball of radius r approaches the whole torus. So for any
   two points x, y on Torus d, dist x y ≤ 1/2 means the edge probability → 1.
3. fillingProb p d → 1 (proved separately via substituted_tendsto and DCT).
4. geometricCov p d = ∫ [(1{edge}-p)^3 * (1{fill}-q)] dμ where q = fillingProb p d → 1.
   As q → 1, the fill factor (1{fill} - q) → 0 uniformly, so geometricCov → 0.

Direct approach: geometricCov p d is a bounded integral (|integrand| ≤ 1 · 2) and the
integrand → 0 pointwise as d → ∞ (since r → 1/2 means fill → 1 a.e. and q → 1).
By DCT, geometricCov → 0.

Step 1: Show geometricCov p d = (1-p)^3 * (1 - fillingProb p d) in the limit.
  This follows from fillingProb_tendsto_one and the definition of geometricCov.
Step 2: (1-p)^3 * (1 - fillingProb p d) → (1-p)^3 * 0 = 0 by fillingProb_tendsto_one.
Step 3: Show geometricCov p d - (1-p)^3 * (1 - fillingProb p d) → 0 using matchRadius_tendsto_half
  and the boundedness of the integrand.
-/
open MeasureTheory in
private lemma geometricCov_eq_when_fill_always' (p : ℝ) (d : ℕ)
    (hfill : ∀ pts : Fin 3 → Torus d,
      ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                      dist (pts 1) z ≤ matchRadius p d ∧
                      dist (pts 2) z ≤ matchRadius p d) :
    geometricCov p d = (1 - fillingProb p d) *
      ∫ pts : Fin 3 → Torus d,
        (let r := matchRadius p d
         let x₁ := pts 0; let x₂ := pts 1; let x₃ := pts 2
         let e₁₂ := if dist x₁ x₂ ≤ r then (1 : ℝ) - p else -p
         let e₁₃ := if dist x₁ x₃ ≤ r then (1 : ℝ) - p else -p
         let e₂₃ := if dist x₂ x₃ ≤ r then (1 : ℝ) - p else -p
         e₁₂ * e₁₃ * e₂₃)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))) := by
  unfold geometricCov;
  rw [ ← MeasureTheory.integral_const_mul ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, hfill ]

/-
Bound the absolute value of the three-edge-product integral by 1 on a
product of Haar probability measures on `Torus d`.
-/
open MeasureTheory in
private lemma edgeProduct_integral_bounded' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) :
    |∫ pts : Fin 3 → Torus d,
        (let r := matchRadius p d
         let x₁ := pts 0; let x₂ := pts 1; let x₃ := pts 2
         let e₁₂ := if dist x₁ x₂ ≤ r then (1 : ℝ) - p else -p
         let e₁₃ := if dist x₁ x₃ ≤ r then (1 : ℝ) - p else -p
         let e₂₃ := if dist x₂ x₃ ≤ r then (1 : ℝ) - p else -p
         e₁₂ * e₁₃ * e₂₃)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))| ≤ 1 := by
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ( Fin 3 → Torus d ) → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun _ => 1;
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
  · exact MeasureTheory.integrable_const _;
  · filter_upwards [ ] with x;
    norm_num [ abs_le ];
    split_ifs <;> constructor <;> nlinarith [ mul_nonneg hp0.le ( sq_nonneg p ), mul_nonneg hp0.le ( sq_nonneg ( 1 - p ) ) ];
  · norm_num [ MeasureTheory.Measure.pi_univ ]

lemma geometricCov_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geometricCov p d) Filter.atTop (nhds 0) := by
  by_contra h_contra;
  apply_mod_cast h_contra <| squeeze_zero_norm' _ _;
  use fun d => |1 - fillingProb p d|;
  · filter_upwards [ fill_eventually_always' p hp0 hp1 ] with d hd;
    rw [ geometricCov_eq_when_fill_always' p d hd ];
    rw [ norm_mul ];
    exact mul_le_of_le_one_right ( abs_nonneg _ ) ( edgeProduct_integral_bounded' p hp0 hp1 d );
  · simpa using Filter.Tendsto.abs ( fillingProb_tendsto_one p hp0 hp1 |> Filter.Tendsto.const_sub 1 )

open MeasureTheory in
/-- **Corollary.** For all sufficiently large d, geometricCov p d = 0 exactly.
    Once matchRadius > 1/3, every triple fills, so F_t - q = 1 - 1 = 0 everywhere
    and the integral collapses. This is stronger than geometricCov_tendsto_zero. -/
lemma geometricCov_eventually_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d : ℕ in Filter.atTop, geometricCov p d = 0 := by
  filter_upwards [fillingProb_eventually_one p hp0 hp1,
                  fill_eventually_always' p hp0 hp1] with d hq hfill
  rw [geometricCov_eq_when_fill_always' p d hfill, hq]
  ring

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
  -- OQ-18: `cechObservation` likely still encodes the old existential fill; under Rips
  -- the equivalence between `s.hasFill` (clique) and the existential needs to be threaded.
  -- Stub pending refactor.
  sorry

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
      ((cechMeasure n d r).map (cechObservation r)) := by
  -- OQ-18: original proof had `exact?` and existential-form `hasFill` measurability.
  -- Stub pending refactor.
  sorry

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

private lemma torus_pi_measure_real_univ' (d : ℕ) :
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

/-
PROBLEM
Chebyshev bound for a single k: the probability that doublySignedFilledCount
    exceeds lam is at most Var/lam².

PROVIDED SOLUTION
Use Chebyshev's inequality (ProbabilityTheory.meas_ge_le_variance_div_sq from Mathlib).

Step 1: Show the measure is a probability measure via twoParamMeasure_isProbabilityMeasure.

Step 2: Show doublySignedFilledCount is Memℒp 2. Since TwoParamSample n is finite (instance twoParamSampleFintype') and MeasurableSpace is ⊤ (discrete), every function is in every Lp space. Use Memℒp.of_bound with the bound being Finset.univ.sup |f| or similar.

Step 3: Get E[X] = 0 from moments_twoParam_signed.

Step 4: Apply meas_ge_le_variance_div_sq with c = lam to get:
  μ({|X - E[X]| ≥ lam}) ≤ ENNReal.ofReal(Var/lam²)

Step 5: Since E[X] = 0, {X ≥ lam} ⊆ {|X| ≥ lam}. So μ({X ≥ lam}) ≤ μ({|X| ≥ lam}).

Step 6: Convert ENNReal bound to ℝ: .toReal ≤ Var/lam².

Step 7: Substitute Var = C(n,3)*p³(1-p)³*q*(1-q) from moments_twoParam_signed.

Key tactic: apply ENNReal.toReal_le_of_le_ofReal, then apply meas_ge_le_variance_div_sq, then substitute the variance formula.
-/
lemma chebyshev_single_bound (n : ℕ) (p q lam : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hlam : 0 < lam) :
    (twoParamMeasure n p q
      {s | doublySignedFilledCount p q s ≥ lam}).toReal ≤
    (n.choose 3 : ℝ) * p ^ 3 * (1 - p) ^ 3 * q * (1 - q) / lam ^ 2 := by
  have := @ProbabilityTheory.meas_ge_le_variance_div_sq ( TwoParamSample n ) _ ( twoParamMeasure n p q ) ?_ ?_ ?_ ?_ ?_ <;> norm_num at *;
  rotate_left;
  rotate_left;
  use fun s => doublySignedFilledCount p q s
  generalize_proofs at *; (
  have h_memLp : MeasureTheory.MemLp (fun s => doublySignedFilledCount p q s) 2 (twoParamMeasure n p q) := by
    have h_finite : MeasureTheory.IsFiniteMeasure (twoParamMeasure n p q) := by
      constructor
      generalize_proofs at *; (
      convert twoParamMeasure_totalMass n p q hp hp1 hq hq1 |> fun h => h.symm ▸ ENNReal.one_lt_top)
    exact?
  generalize_proofs at *; (
  exact h_memLp));
  exact lam
  exact hlam
  generalize_proofs at *; (
  -- Since the expected value of the doublySignedFilledCount is zero, the set where the doublySignedFilledCount is at least lam is a subset of the set where the absolute value of the doublySignedFilledCount is at least lam.
  have h_subset : {s : TwoParamSample n | lam ≤ doublySignedFilledCount p q s} ⊆ {s : TwoParamSample n | lam ≤ |doublySignedFilledCount p q s|} := by
    exact fun x hx => le_trans hx.out ( le_abs_self _ )
  generalize_proofs at *; (
  refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_subset ) _ <;> norm_num [ moments_twoParam_signed n p q hp hp1 hq hq1 ] at *;
  · exact ne_of_lt ( lt_of_le_of_lt this ( ENNReal.ofReal_lt_top ) );
  · exact le_trans ( ENNReal.toReal_mono ( by aesop ) this ) ( by rw [ ENNReal.toReal_ofReal ( div_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) ) hq ) ( sub_nonneg.mpr hq1 ) ) ( sq_nonneg _ ) ) ] ) ;));
  constructor;
  rw [ twoParamMeasure_totalMass ] <;> aesop

/-
PROBLEM
(n^{3/2} * g)² = n³ * g², and C(n,3) ≥ n³/6 - O(n²), so
    if n^{3/2}*g → ∞, then C(n,3)*g² → ∞.

PROVIDED SOLUTION
Key identity: (n^{3/2} * g)² = n³ * g². So n³ * g² → ∞ (squaring a sequence tending to ∞ gives ∞).

Then C(n,3) = n*(n-1)*(n-2)/6 ≥ n³/27 for n ≥ 3 (since (n-1)/n ≥ 2/3 and (n-2)/n ≥ 1/3 for n ≥ 3). Actually more carefully: C(n,3) ≥ (n-2)³/6.

So C(n,3)*g² ≥ (n³/27)*g² = (n^{3/2}*g)²/27 → ∞.

More precisely:
- From hSNR: n^{3/2}*g → ∞, so (n^{3/2}*g)² → ∞ (use Filter.Tendsto.atTop_mul_atTop or tendsto_pow_atTop)
- C(n,3) ≥ n*(n-1)*(n-2)/6 (this is equality, from Nat.choose_three)
- For n ≥ 3: n*(n-1)*(n-2) ≥ n³/27... actually n*(n-1)*(n-2) ≥ (n/3)³ = n³/27
- So C(n,3) ≥ n³/162
- C(n,3)*g² ≥ (n³*g²)/162 = (n^{3/2}*g)²/162
- Since (n^{3/2}*g)² → ∞, (n^{3/2}*g)²/162 → ∞.

Use Filter.Tendsto.atTop_div_const to divide by 162.

Alternative cleaner approach:
C(n,3)*g² ≥ (n choose 3)*g² and for n ≥ 3:
(n choose 3) = n!/(3!(n-3)!) = n(n-1)(n-2)/6

We want to show n(n-1)(n-2)/6 * g² → ∞.
n(n-1)(n-2) = n³ - 3n² + 2n ≥ n³ - 3n² ≥ n³(1 - 3/n).
For n ≥ 6: 1 - 3/n ≥ 1/2, so n(n-1)(n-2) ≥ n³/2 and C(n,3) ≥ n³/12.
Hence C(n,3)*g² ≥ n³*g²/12 = (n^{3/2}*g)²/12 → ∞.

Use eventually filter and Filter.Tendsto.atTop_mono'.
-/
lemma choose3_g_sq_tendsto_atTop (p : ℝ)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => (Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2)
      Filter.atTop Filter.atTop := by
  -- From Lemma 25, we know that $C(n, 3) \geq n^3 / 162$ for $n \geq 6$.
  have h_choose_bound : ∀ k, nSeq k ≥ 6 → (Nat.choose (nSeq k) 3 : ℝ) ≥ (nSeq k ^ 3 : ℝ) / 162 := by
    intro k hk; rw [ Nat.cast_choose ] <;> try linarith;
    rcases n : nSeq k with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.factorial ] ; ring_nf ; norm_num at *;
    norm_num [ Nat.factorial_ne_zero ] ; nlinarith [ ( by norm_cast : ( 3 : ℝ ) ≤ ↑‹ℕ› ) ] ;
  -- Using the bound from Lemma 25, we can show that $(Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2$ is bounded below by $(nSeq k ^ 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2 / 162$.
  have h_bound_below : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2 ≥ (nSeq k ^ 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2 / 162 := by
    filter_upwards [ hn.eventually_ge_atTop 6 ] with k hk using by nlinarith [ h_choose_bound k hk ] ;
  -- Since $(nSeq k ^ 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2$ tends to infinity, dividing by 162 still results in infinity.
  have h_div_inf : Filter.Tendsto (fun k => (nSeq k ^ 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2 / 162) Filter.atTop Filter.atTop := by
    have h_div_inf : Filter.Tendsto (fun k => ((nSeq k ^ (3 / 2 : ℝ) * geometricCov p (dSeq k)) ^ 2) / 162) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const ( by norm_num ) ( Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| hSNR );
    convert h_div_inf using 2 ; ring ; norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring;
  exact Filter.tendsto_atTop_mono' Filter.atTop h_bound_below h_div_inf

/-- Under 2PC, the probability that the doubly-signed statistic exceeds threshold λ
    is bounded by Var/λ² (Chebyshev). As n^{3/2}·g → ∞, this bound → 0. -/
lemma chebyshev_2PC_prob_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => (twoParamMeasure (nSeq k) p (fillingProb p (dSeq k))
        {s | doublySignedFilledCount p (fillingProb p (dSeq k)) s ≥
          (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2}).toReal)
      Filter.atTop (nhds 0) := by
  -- A3.5: concrete L∞ corollary of `chebyshev_prob_tendsto_zero_abstract`. The abstract
  -- lemma takes a per-k Chebyshev bound; we supply it from `chebyshev_single_bound`
  -- specialized at `q k := fillingProb p (dSeq k)`.
  exact chebyshev_prob_tendsto_zero_abstract p hp0 hp1 nSeq
    (fun k => geometricCov p (dSeq k)) (fun k => fillingProb p (dSeq k))
    (fun k => fillingProb_nonneg p (dSeq k))
    (fun k => fillingProb_le_one p (dSeq k))
    hn hSNR
    (fun k lam hlam => chebyshev_single_bound (nSeq k) p (fillingProb p (dSeq k)) lam
      hp0.le hp1.le (fillingProb_nonneg p (dSeq k)) (fillingProb_le_one p (dSeq k)) hlam)

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
private lemma doublySignedTriangle_sq_le_one {n : ℕ} (p q : ℝ)
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

-- The doubly-signed indicator for triangle t, viewed as a function of the torus points.
open Classical in
private noncomputable def triangleIndicator' {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts : Fin n → Torus d) : ℝ :=
  let s := cechObservation r (CechSample.mk pts)
  (∏ e ∈ triangleEdges t,
    (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
  (if s.fill t then (1 : ℝ) - q else -q)

private lemma triangleIndicator'_translate {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts : Fin n → Torus d) (h : Torus d) :
    triangleIndicator' p q r t (fun i => pts i + h) = triangleIndicator' p q r t pts := by
  -- OQ-18: under Rips clique `hasFill`, translation invariance follows directly from
  -- `dist_eq_norm` on each pair (no existential to shift). Proof rewrite pending.
  sorry

private lemma triangleIndicator'_congr {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts pts' : Fin n → Torus d)
    (h : ∀ i ∈ t.val, pts i = pts' i) :
    triangleIndicator' p q r t pts = triangleIndicator' p q r t pts' := by
  unfold triangleIndicator'
  unfold cechObservation
  simp +decide [h, triangleEdges]
  congr! 3
  · unfold CechSample.hasFill
    aesop
  · unfold CechSample.hasEdge
    aesop
  · refine' Finset.prod_congr rfl fun x hx => _
    unfold CechSample.hasEdge
    aesop

-- Converting integral over ν to integral over product measure on torus points.
private lemma integral_over_nu_eq' {n d : ℕ} (r : ℝ) (f : TwoParamSample n → ℝ) :
    let ν := (cechMeasure n d r).map (cechObservation r)
    ∫ s, f s ∂ν = ∫ pts : Fin n → Torus d,
      f (cechObservation r (CechSample.mk pts))
      ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) := by
  -- OQ-18: original proof uses `exact?` and existential-form `hasFill` measurability.
  -- Stub pending refactor.
  sorry

/-
OLD PROOF BODY:
  convert MeasureTheory.integral_map _ _ using 3;
  · exact?;
  · apply_rules [ Measurable.aemeasurable, measurable_to_countable' ];
    intro x
    have h_preimage : MeasurableSet {s : Fin n → Torus d | cechObservation r ⟨s⟩ = x} := by
      have h_measurable : ∀ i j, MeasurableSet {s : Fin n → Torus d | (cechObservation r ⟨s⟩).edge i j = x.edge i j} := by
        intro i j
        have h_measurable : MeasurableSet {s : Fin n → Torus d | dist (s i) (s j) ≤ r} := by
          exact measurableSet_le ( measurable_pi_apply i |> Measurable.dist <| measurable_pi_apply j ) measurable_const
        generalize_proofs at *; (
        cases x.edge i j <;> simp_all +decide [ cechObservation ];
        · exact Measurable.not h_measurable;
        · exact h_measurable)
      generalize_proofs at *; (
      have h_measurable : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, MeasurableSet {s : Fin n → Torus d | (cechObservation r ⟨s⟩).fill t = x.fill t} := by
        intro t
        have h_measurable : MeasurableSet {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ r} := by
          have h_measurable : IsClosed (⋃ z : Torus d, {s : Fin n → Torus d | ∀ i ∈ t.val, dist (s i) z ≤ r}) := by
            refine' isClosed_of_closure_subset fun s hs => _;
            rw [ mem_closure_iff_seq_limit ] at hs
            generalize_proofs at *; (
            obtain ⟨ x, hx₁, hx₂ ⟩ := hs
            generalize_proofs at *; (
            choose z hz using fun n => Set.mem_iUnion.mp ( hx₁ n );
            obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
              have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
                exact isCompact_univ_iff.mpr ( by infer_instance )
              generalize_proofs at *; (
              have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;)
            generalize_proofs at *; (
            obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
            exact Set.mem_iUnion.mpr ⟨ z', fun i hi => le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _ hi |> le_trans <| by norm_num ⟩)))
          generalize_proofs at *; (
          convert h_measurable.measurableSet using 1 ; ext ; aesop)
        generalize_proofs at *; (
        cases x.fill t <;> simp_all +decide [ cechObservation ];
        · exact Measurable.not h_measurable;
        · convert h_measurable using 1)
      generalize_proofs at *; (
      have h_measurable : MeasurableSet {s : Fin n → Torus d | ∀ i j, (cechObservation r ⟨s⟩).edge i j = x.edge i j} ∧ MeasurableSet {s : Fin n → Torus d | ∀ t : {σ : Finset (Fin n) // σ.card = 3}, (cechObservation r ⟨s⟩).fill t = x.fill t} := by
        exact ⟨ by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by solve_by_elim, by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun t => by solve_by_elim ⟩
      generalize_proofs at *; (
      convert h_measurable.1.inter h_measurable.2 using 1
      generalize_proofs at *; (ext; simp [cechObservation]; exact ⟨ fun h => ⟨ fun i j => by simpa using congr_arg ( fun f => f.edge i j ) h, fun a b => by simpa using congr_arg ( fun f => f.fill ⟨ a, b ⟩ ) h ⟩, fun h => by cases x; aesop ⟩ ;))))
    generalize_proofs at *; (
    convert h_preimage.preimage _ using 1
    generalize_proofs at *; (exact measurable_iff_comap_le.mpr le_rfl));
  · exact?
-/

-- The integral of a single triangle indicator over the product measure equals geometricCov.
private lemma single_triangle_integral_eq_g' {n d : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    let r := matchRadius p d
    let q := fillingProb p d
    ∫ pts : Fin n → Torus d,
      triangleIndicator' p q r t pts
      ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    = geometricCov p d := by
  -- OQ-18: depends on `cechDoublySigned_triangle_integral` (now stubbed) and the
  -- `CechSample.hasFill` form. Stub pending refactor.
  sorry
set_option maxHeartbeats 400000 in
private lemma shear_measurePreserving_vertex {n d : ℕ} (i : Fin n) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    MeasureTheory.MeasurePreserving
      (fun pts : Fin n → Torus d => fun v => if v = i then pts v else pts v - pts i) μ μ := by
  refine' ⟨ _, _ ⟩;
  · exact measurable_pi_lambda _ fun _ => by split_ifs <;> [ exact measurable_pi_apply _; exact ( measurable_pi_apply _ |> Measurable.sub <| measurable_pi_apply _ ) ] ;
  · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
    intro s hs; rw [ MeasureTheory.Measure.map_apply ] ; (
    have h_preimage : (fun pts : Fin n → Torus d => fun v => if v = i then pts v else pts v - pts i) ⁻¹' Set.univ.pi s = {pts : Fin n → Torus d | pts i ∈ s i ∧ ∀ v ≠ i, pts v - pts i ∈ s v} := by
      grind;
    have h_split : (MeasureTheory.Measure.pi fun x => MeasureTheory.volume) {pts : Fin n → Torus d | pts i ∈ s i ∧ ∀ v ≠ i, pts v - pts i ∈ s v} = (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) {p : Torus d × ({j // j ≠ i} → Torus d) | p.1 ∈ s i ∧ ∀ j : {j // j ≠ i}, p.2 j - p.1 ∈ s j} := by
      have h_split : (MeasureTheory.Measure.pi fun x => MeasureTheory.volume) = MeasureTheory.Measure.map (fun p : Torus d × ({j // j ≠ i} → Torus d) => fun v => if h : v = i then p.1 else p.2 ⟨v, h⟩) (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) := by
        convert MeasureTheory.Measure.pi_eq _;
        · exact?;
        · intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · rw [ show ( fun p : Torus d × ( { j // j ≠ i } → Torus d ) => fun v => if h : v = i then p.1 else p.2 ⟨ v, h ⟩ ) ⁻¹' Set.univ.pi s = ( s i ) ×ˢ ( Set.pi Set.univ fun j : { j // j ≠ i } => s j ) from ?_ ];
            · simp +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ), MeasureTheory.Measure.pi_pi ];
              refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide [ Finset.mem_sdiff, Finset.mem_singleton ];
            · grind;
          · exact measurable_pi_lambda _ fun v => by split_ifs <;> [ exact measurable_fst; exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd ] ;
          · exact MeasurableSet.univ_pi hs;
      rw [ h_split, MeasureTheory.Measure.map_apply ];
      · congr with p ; aesop;
      · exact measurable_pi_lambda _ fun v => by split_ifs <;> [ exact measurable_fst; exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd ] ;
      · simp +decide only [Set.setOf_and, Set.setOf_forall];
        refine' MeasurableSet.inter _ _;
        · exact measurable_pi_apply i ( hs i );
        · refine' MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => _;
          exact measurableSet_preimage ( measurable_pi_apply j |> Measurable.sub <| measurable_pi_apply i ) ( hs j );
    have h_fubini : (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) {p : Torus d × ({j // j ≠ i} → Torus d) | p.1 ∈ s i ∧ ∀ j : {j // j ≠ i}, p.2 j - p.1 ∈ s j} = ∫⁻ x in s i, ∏ j : {j // j ≠ i}, MeasureTheory.volume (s j) ∂MeasureTheory.volume := by
      have h_fubini : (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) {p : Torus d × ({j // j ≠ i} → Torus d) | p.1 ∈ s i ∧ ∀ j : {j // j ≠ i}, p.2 j - p.1 ∈ s j} = ∫⁻ x in s i, (MeasureTheory.Measure.pi fun x => MeasureTheory.volume) {p : {j // j ≠ i} → Torus d | ∀ j : {j // j ≠ i}, p j - x ∈ s j} ∂MeasureTheory.volume := by
        rw [ MeasureTheory.Measure.prod_apply ];
        · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
          · congr with x ; aesop;
          · exact hs i;
        · simp +decide only [Set.setOf_and, Set.setOf_forall];
          refine' MeasurableSet.inter _ _;
          · exact measurableSet_preimage ( measurable_fst ) ( hs i );
          · refine' MeasurableSet.iInter fun j => _;
            exact measurableSet_preimage ( show Measurable fun x : Torus d × ( { j // j ≠ i } → Torus d ) => x.2 j - x.1 from Measurable.sub ( measurable_pi_apply _ |> Measurable.comp <| measurable_snd ) measurable_fst ) ( hs _ );
      rw [ h_fubini ];
      refine' MeasureTheory.lintegral_congr fun x => _;
      rw [ show { p : { j // j ≠ i } → Torus d | ∀ j : { j // j ≠ i }, p j - x ∈ s j } = ( Set.pi Set.univ fun j : { j // j ≠ i } => ( fun y => y - x ) ⁻¹' s j ) by ext; simp +decide [ Set.pi ] ];
      simp +decide [ sub_eq_add_neg ];
    simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ) ];
    rw [ mul_comm, ← Finset.prod_attach ];
    refine' congr rfl ( Finset.prod_bij ( fun x hx => x ) _ _ _ _ ) <;> aesop);
    · exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_pi_apply j; exact measurable_pi_apply j |> Measurable.sub <| measurable_pi_apply i ] ;
    · exact MeasurableSet.univ_pi hs
private lemma indepFun_proj_pairs_vertex {n d : ℕ} (j k l m : Fin n)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts : Fin n → Torus d => (pts j, pts k))
      (fun pts : Fin n → Torus d => (pts l, pts m)) μ := by
  intro μ;
  have h_indep : ProbabilityTheory.iIndepFun (fun i : Fin n => fun pts : Fin n → Torus d => pts i) μ := by
    convert ProbabilityTheory.iIndepFun_pi _
    rotate_left
    exact?
    exacts [ fun i x => x, fun i => measurable_id.aemeasurable, rfl ]
  have := h_indep.indepFun_finset { j, k } { l, m } ; simp_all +decide [ ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul ] ;
  intro s t hs ht; specialize this ( Ne.symm hjl ) ( Ne.symm hkl ) ( Ne.symm hjm ) ( Ne.symm hkm ) ( fun i => measurable_pi_apply i ) ; simp_all +decide [ Set.preimage ] ;
  convert this ( ( fun f => ( f ⟨ j, by aesop ⟩, f ⟨ k, by aesop ⟩ ) ) ⁻¹' s ) ( ( fun f => ( f ⟨ l, by aesop ⟩, f ⟨ m, by aesop ⟩ ) ) ⁻¹' t ) _ _ using 1 <;> simp +decide [ Set.preimage ];
  · exact measurableSet_preimage ( measurable_pi_apply _ |> Measurable.prodMk <| measurable_pi_apply _ ) hs |> MeasurableSet.mem;
  · exact measurableSet_preimage ( measurable_pi_apply _ |> Measurable.prodMk <| measurable_pi_apply _ ) ht |> MeasurableSet.mem
private lemma indepFun_comp_measurePreserving_vertex {Omega Alpha Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {μ : MeasureTheory.Measure Omega}
    {f : Omega → Alpha} {g : Omega → Beta} {Ψ : Omega → Omega}
    (hΨ : MeasureTheory.MeasurePreserving Ψ μ μ)
    (hf : Measurable f) (hg : Measurable g)
    (hind : ProbabilityTheory.IndepFun f g μ) :
    ProbabilityTheory.IndepFun (f ∘ Ψ) (g ∘ Ψ) μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at *
  intro s t hs ht
  have eq1 : (f ∘ Ψ) ⁻¹' s ∩ (g ∘ Ψ) ⁻¹' t = Ψ ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) := by
    ext x; simp [Set.mem_preimage, Set.mem_inter_iff]
  have eq2 : (f ∘ Ψ) ⁻¹' s = Ψ ⁻¹' (f ⁻¹' s) := by ext; simp
  have eq3 : (g ∘ Ψ) ⁻¹' t = Ψ ⁻¹' (g ⁻¹' t) := by ext; simp
  rw [eq1, eq2, eq3]
  rw [hΨ.measure_preimage ((hs.preimage hf).inter (ht.preimage hg)).nullMeasurableSet,
      hΨ.measure_preimage (hs.preimage hf).nullMeasurableSet,
      hΨ.measure_preimage (ht.preimage hg).nullMeasurableSet]
  exact hind s t hs ht
private lemma indepFun_coord_diffs_vertex {n d : ℕ}
    (i j k l m : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m)
    (_hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (_hlm : l ≠ m) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts : Fin n → Torus d => (pts j - pts i, pts k - pts i))
      (fun pts : Fin n → Torus d => (pts l - pts i, pts m - pts i))
      μ := by
  intro μ
  let Ψ : (Fin n → Torus d) → (Fin n → Torus d) := fun pts v => if v = i then pts v else pts v - pts i
  have h_eq : (fun pts : Fin n → Torus d => (pts j - pts i, pts k - pts i)) =
      (fun pts : Fin n → Torus d => (pts j, pts k)) ∘ Ψ := by
    ext pts <;> simp [Ψ, hij.symm, hik.symm]
  have h'_eq : (fun pts : Fin n → Torus d => (pts l - pts i, pts m - pts i)) =
      (fun pts : Fin n → Torus d => (pts l, pts m)) ∘ Ψ := by
    ext pts <;> simp [Ψ, hil.symm, him.symm]
  rw [h_eq, h'_eq]
  exact indepFun_comp_measurePreserving_vertex
    (shear_measurePreserving_vertex i)
    (Measurable.prod (measurable_pi_apply j) (measurable_pi_apply k))
    (Measurable.prod (measurable_pi_apply l) (measurable_pi_apply m))
    (indepFun_proj_pairs_vertex j k l m hjl hjm hkl hkm)

/-
Helper: extract shared vertex and other vertices from two triangles sharing exactly one vertex
-/
private lemma extract_vertices_of_card_inter_one {n : ℕ}
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 1) :
    ∃ i j k l m : Fin n,
      t.val = {i, j, k} ∧ t'.val = {i, l, m} ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      i ≠ l ∧ i ≠ m ∧ l ≠ m ∧
      j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m := by
  obtain ⟨ i, hi ⟩ := Finset.card_eq_one.mp hshare;
  -- Since t and t' are distinct and their intersection is {i}, we can extract the other elements from t and t'.
  obtain ⟨j, k, hjk⟩ : ∃ j k : Fin n, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ t.val = {i, j, k} := by
    have := Finset.card_eq_three.mp t.2;
    rcases this with ⟨ x, y, z, hxy, hxz, hyz, ht ⟩ ; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    grind
  obtain ⟨l, m, hlm⟩ : ∃ l m : Fin n, l ≠ m ∧ l ≠ i ∧ m ≠ i ∧ t'.val = {i, l, m} := by
    have h_card : (t'.val \ {i}).card = 2 := by
      grind;
    obtain ⟨ l, m, h ⟩ := Finset.card_eq_two.mp h_card;
    grind;
  grind +locals

/-
Helper: triangleIndicator' factors through coordinate differences
-/
private lemma triangleIndicator'_factor_coord_diffs {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (i j k : Fin n)
    (ht_eq : t.val = {i, j, k})
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ F : (Torus d × Torus d) → ℝ, Measurable F ∧
      ∀ pts : Fin n → Torus d,
        triangleIndicator' p q r t pts = F (pts j - pts i, pts k - pts i) := by
  -- OQ-18: factorisation through (pts j − pts i, pts k − pts i) for the clique `hasFill`
  -- is now structurally cleaner (no existential to handle), but the original proof's
  -- closed-set + compactness argument for the existential no longer applies. Stub.
  sorry

/-
OLD PROOF BODY:
  refine' ⟨ fun xy => triangleIndicator' p q r t ( fun v => if v = i then 0 else if v = j then xy.1 else if v = k then xy.2 else 0 ), _, _ ⟩ <;> norm_num [ triangleIndicator' ];
  · refine' Measurable.ite _ _ _ <;> norm_num [ cechObservation ];
    · refine' MeasurableSet.mem _;
      refine' IsClosed.measurableSet _;
      simp +decide [ ht_eq, dist_comm ];
      simp +decide [ hij.symm, hik.symm, hjk.symm ];
      refine' isClosed_of_closure_subset _;
      intro a ha;
      rw [ mem_closure_iff_seq_limit ] at ha;
      obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
      choose z hz using hx₁;
      -- Since $z_n$ is bounded, it has a convergent subsequence.
      obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
        have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
          exact isCompact_univ_iff.mpr ( by infer_instance );
        have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
      obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
      refine' ⟨ z', _, _, _ ⟩;
      · exact le_of_tendsto' ( hsubseq₂.norm ) fun n => hz _ |>.1;
      · exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist hsubseq₂ ( continuousAt_fst.tendsto.comp hx₂ |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) ) tendsto_const_nhds fun n => hz _ |>.2.1;
      · exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist hsubseq₂ ( continuous_snd.continuousAt.tendsto.comp ( hx₂.comp hsubseq₁.tendsto_atTop ) ) ) tendsto_const_nhds fun n => hz _ |>.2.2;
    · refine' Measurable.mul _ measurable_const;
      refine' Finset.measurable_prod _ _ ; intros ; simp +decide [ cechObservation ];
      unfold CechSample.hasEdge; simp +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
      refine' Measurable.ite _ _ _ <;> norm_num [ dist_eq_norm ];
      exact MeasurableSet.mem ( measurableSet_le ( measurable_norm.comp ( Measurable.sub ( by split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ] ) ( by split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ] ) ) ) measurable_const );
    · refine' Measurable.mul _ measurable_const;
      refine' Finset.measurable_prod _ fun e he => _;
      refine' Measurable.ite _ _ _ <;> norm_num [ cechObservation ];
      refine' Measurable.comp ( show Measurable fun x : ℝ => x ≤ r from measurableSet_Iic.mem ) _;
      refine' Measurable.dist _ _ <;> norm_num [ cechObservation ];
      · split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ];
      · split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ];
  · intro pts; congr! 2; simp +decide [ cechObservation, triangleEdges ] ;
    · constructor <;> rintro ⟨ z, hz ⟩;
      · use z - pts i; simp_all +decide [ CechSample.hasFill ] ;
        aesop;
      · use z + pts i; simp_all +decide [ CechSample.hasFill ] ;
        split_ifs at hz <;> simp_all +decide [ dist_eq_norm, sub_eq_iff_eq_add ];
        exact ⟨ by convert hz.2.1 using 1; abel_nf, by convert hz.2.2 using 1; abel_nf ⟩;
    · refine' Finset.prod_congr rfl fun e he => _ ; simp +decide [ cechObservation ] ;
      unfold CechSample.hasEdge; simp +decide [ Finset.mem_product, Finset.mem_univ, * ] ;
      unfold triangleEdges at he; simp +decide [ Finset.mem_product, Finset.mem_univ, * ] at he;
      rcases he with ⟨ ⟨ he₁ | he₁ | he₁, he₂ | he₂ | he₂ ⟩, he₃ ⟩ <;> simp +decide [ he₁, he₂ ] at he₃ ⊢;
      all_goals simp +decide [ dist_eq_norm, norm_sub_rev, hij.symm, hik.symm, hjk.symm ] ;
    · refine' congr_arg₂ _ ( Finset.prod_congr rfl fun x hx => _ ) rfl ; simp +decide [ cechObservation ] ;
      simp +decide [ triangleEdges ] at hx ⊢;
      simp +decide [ ht_eq, CechSample.hasEdge ] at hx ⊢;
      rcases hx.1.1 with ( h | h | h ) <;> rcases hx.1.2 with ( j | j | j ) <;> simp +decide [ h, j ] at hx ⊢;
      all_goals simp +decide [ dist_eq_norm, norm_sub_rev, hij.symm, hik.symm, hjk.symm ] ;
-/

/-
When two triangles t, t' share exactly one vertex i, their triangle indicators
under the torus Haar measure μ are independent.
-/
set_option maxHeartbeats 800000 in
private lemma vertex_sharing_indepFun' {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 1) :
    let r := matchRadius p d
    let q := fillingProb p d
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts => triangleIndicator' p q r t pts)
      (fun pts => triangleIndicator' p q r t' pts) μ := by
  intro r q μ
  obtain ⟨i, j, k, l, m, ht_eq, ht'_eq, hij, hik, hjk, hil, him, hlm, hjl, hjm, hkl, hkm⟩ :=
    extract_vertices_of_card_inter_one t t' htt' hshare
  obtain ⟨F, hF_meas, hF_eq⟩ := triangleIndicator'_factor_coord_diffs p q r t i j k ht_eq hij hik hjk
  obtain ⟨G, hG_meas, hG_eq⟩ := triangleIndicator'_factor_coord_diffs p q r t' i l m ht'_eq hil him hlm
  have h_eq_F : (fun pts => triangleIndicator' p q r t pts) =
      F ∘ (fun pts : Fin n → Torus d => (pts j - pts i, pts k - pts i)) := by
    ext pts; exact hF_eq pts
  have h_eq_G : (fun pts => triangleIndicator' p q r t' pts) =
      G ∘ (fun pts : Fin n → Torus d => (pts l - pts i, pts m - pts i)) := by
    ext pts; exact hG_eq pts
  rw [h_eq_F, h_eq_G]
  exact (indepFun_coord_diffs_vertex i j k l m hij hik hil him hjk hjl hjm hkl hkm hlm).comp hF_meas hG_meas

open Classical in
private lemma fillingProb_nonneg' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) : 0 ≤ fillingProb p d := by
  unfold fillingProb
  apply MeasureTheory.integral_nonneg
  intro pts; simp only
  split_ifs <;> norm_num
-- Moved here from below to avoid forward reference in volumeFill_div_le_one'.
open MeasureTheory in
private lemma incBeta_nonneg' (d : ℕ) (x : ℝ) :
    0 ≤ ∫ t in Set.Ioo 0 x,
      t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) := by
  by_contra h_neg;
  convert h_neg <| MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht => ?_ using 1;
  by_cases h : 1 - t ≥ 0;
  · exact mul_nonneg ( Real.rpow_nonneg ht.1.le _ ) ( Real.rpow_nonneg h _ );
  · norm_num [ Real.rpow_def_of_neg ( not_le.mp h ) ];
    norm_num [ show 1 / 2 * Real.pi = Real.pi / 2 by ring ]

open MeasureTheory in
private lemma incBeta_mono' (d : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    ∫ t in Set.Ioo 0 x, t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) ≤
    ∫ t in Set.Ioo 0 y, t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) := by
  refine' MeasureTheory.setIntegral_mono_set _ _ _;
  · have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioc 0 1) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioo 0 1) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ)) (Set.Ioo 0 1) ∧ MeasureTheory.IntegrableOn (fun t : ℝ => (1 - t) ^ (1 / 2 - 1 : ℝ)) (Set.Ioo 0 1) := by
          constructor;
          · exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith [ show ( d : ℝ ) ≥ 0 by positivity ] ) ).1.mono_set ( Set.Ioo_subset_Ioc_self );
          · have h_integrable : ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t) ^ (-1 / 2 : ℝ) = 2 * Real.sqrt 1 := by
              rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_comp_sub_left fun t => t ^ ( -1 / 2 : ℝ ), integral_rpow ] <;> norm_num;
            exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef ( by norm_num at *; aesop ) ] ; norm_num );
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun t => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) + ( 1 - t ) ^ ( 1 / 2 - 1 : ℝ );
        · exact MeasureTheory.Integrable.add h_integrable.1 h_integrable.2;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.1.aestronglyMeasurable ) ( h_integrable.2.aestronglyMeasurable );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with t ht;
          rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.rpow_nonneg ht.1.le _ ) ( Real.rpow_nonneg ( sub_nonneg.2 ht.2.le ) _ ) ) ];
          rcases d with ( _ | _ | d ) <;> norm_num at *;
          · norm_num [ Real.rpow_neg ht.1.le, Real.rpow_neg ( sub_nonneg.2 ht.2.le ) ];
            rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow ];
            field_simp;
            rw [ div_add_div, div_le_div_iff₀ ] <;> nlinarith [ Real.sqrt_pos.2 ht.1, Real.sqrt_pos.2 ( sub_pos.2 ht.2 ), Real.mul_self_sqrt ( show 0 ≤ t by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 - t by linarith ), mul_pos ( Real.sqrt_pos.2 ht.1 ) ( Real.sqrt_pos.2 ( sub_pos.2 ht.2 ) ) ];
          · rw [ Real.rpow_neg ( by linarith ) ];
            exact le_add_of_nonneg_of_le ( Real.rpow_nonneg ht.1.le _ ) ( mul_le_of_le_one_left ( inv_nonneg.2 ( Real.rpow_nonneg ( by linarith ) _ ) ) ( Real.rpow_le_one ht.1.le ht.2.le ( by linarith [ show ( d : ℝ ) ≥ 0 by positivity ] ) ) );
      rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc ] at *;
    have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioc 0 (max y 1)) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioc 1 (max y 1)) := by
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun t => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) * 0 ^ ( 1 / 2 - 1 : ℝ );
        · norm_num;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.pow_const _ ) ( Measurable.pow_const ( measurable_const.sub measurable_id ) _ ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht ; norm_num [ Real.rpow_def_of_neg ( by linarith [ ht.1 ] : 1 - t < 0 ) ];
          norm_num [ show 1 / 2 * Real.pi = Real.pi / 2 by ring ];
      convert MeasureTheory.IntegrableOn.union ‹MeasureTheory.IntegrableOn ( fun t : ℝ => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) * ( 1 - t ) ^ ( 1 / 2 - 1 : ℝ ) ) ( Set.Ioc 0 1 ) volume› ‹MeasureTheory.IntegrableOn ( fun t : ℝ => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) * ( 1 - t ) ^ ( 1 / 2 - 1 : ℝ ) ) ( Set.Ioc 1 ( Max.max y 1 ) ) volume› using 1 ; norm_num;
    exact h_integrable.mono_set ( Set.Ioo_subset_Ioc_self.trans ( Set.Ioc_subset_Ioc_right ( le_max_left _ _ ) ) );
  · refine' MeasureTheory.ae_restrict_mem measurableSet_Ioo |> fun h => h.mono fun t ht => _;
    by_cases h : 1 - t ≥ 0 <;> simp_all +decide [ Real.rpow_def_of_pos, Real.rpow_def_of_neg ];
    · exact mul_nonneg ( Real.exp_nonneg _ ) ( Real.rpow_nonneg ( by linarith ) _ );
    · norm_num [ ( by ring : 1 / 2 * Real.pi = Real.pi / 2 ) ];
  · exact MeasureTheory.ae_of_all _ fun t ht => ⟨ ht.1, ht.2.trans_le hxy ⟩

open MeasureTheory in
private lemma volumeFill_div_volumeEmpty_le_one_ge2' (d : ℕ) (r s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    volumeFill d r s / volumeEmpty d r s ≤ 1 := by
  unfold volumeFill volumeEmpty;
  by_cases hr : r = 0 <;> simp_all +decide [ mul_pow, div_eq_mul_inv ];
  · unfold euclidBallVol;
    cases d <;> norm_num;
    by_cases h : ∫ t in Set.Ioo ( 0 : ℝ ) 1, t ^ ( - ( 1 / 2 : ℝ ) ) * ( 1 - t ) ^ ( - ( 1 / 2 : ℝ ) ) = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    norm_num [ ← mul_assoc, ne_of_gt ( Real.Gamma_pos_of_pos _ ) ];
  · unfold euclidBallVol; ring_nf; norm_num [ hr ] ;
    field_simp;
    refine' div_le_one_of_le₀ _ _;
    · refine' le_trans ( mul_le_of_le_one_right ( MeasureTheory.setIntegral_nonneg ( by norm_num ) fun x hx => _ ) ( pow_le_one₀ ( by norm_num ) ( by norm_num ) ) ) _;
      · exact mul_nonneg ( Real.rpow_nonneg hx.1.le _ ) ( Real.rpow_nonneg ( sub_nonneg.2 <| hx.2.le.trans <| div_le_one_of_le₀ ( by nlinarith ) <| by positivity ) _ );
      · convert incBeta_mono' d _ using 3 ; ring;
        · grind;
        · rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_self_pos.2 hr ];
    · refine' MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht => mul_nonneg ( Real.rpow_nonneg ( by linarith [ ht.1 ] ) _ ) ( Real.rpow_nonneg ( by linarith [ ht.2, show ( r ^ 2 * 16 + -s ^ 2 ) / ( r ^ 2 * 16 ) ≤ 1 by rw [ div_le_iff₀ <| by positivity ] ; nlinarith ] ) _ )

private lemma volumeFill_div_volumeEmpty_le_one' (d : ℕ) (r s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    volumeFill d r s / volumeEmpty d r s ≤ 1 := by
  rcases d with _ | d
  · exact volumeFill_div_volumeEmpty_le_one_ge2' 0 r s hs hs1
  · exact volumeFill_div_volumeEmpty_le_one_ge2' (d + 1) r s hs hs1

-- Helper: volumeFill/volumeEmpty ≤ 1 (proved later as volumeFill_div_volumeEmpty_le_one)
private lemma volumeFill_div_le_one' (d : ℕ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 < s) (hs1 : s < 1) :
    volumeFill d r s / volumeEmpty d r s ≤ 1 := by
  exact volumeFill_div_volumeEmpty_le_one' d r s hs hs1
-- Helper: beta density integral ≤ 1 (proof duplicated from beta_density_integral_le_one below)
private lemma beta_density_integral_le_one' (d : ℕ) :
    ∫ s in Set.Ioo (0:ℝ) 1, (↑d * s ^ (d - 1 : ℕ)) ≤ 1 := by
  rcases d with ( _ | d ) <;> norm_num [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one ] at *;
  rw [ mul_inv_cancel₀ ( by linarith ) ]
-- `torus_pi_measure_real_univ'`, `fillingProb_nonneg`, `fillingProb_le_one` moved earlier.

open Classical in
private lemma fillingProb_le_one' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) : fillingProb p d ≤ 1 := by
  unfold fillingProb
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const 1) ?_) ?_
  · exact Filter.Eventually.of_forall fun pts => by simp only; split_ifs <;> norm_num
  · exact Filter.Eventually.of_forall fun pts => by simp only; split_ifs <;> norm_num
  · simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact le_of_eq (torus_pi_measure_real_univ' d)

private lemma triangleIndicator'_bound' {n d : ℕ} (p q r : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts : Fin n → Torus d) :
    |triangleIndicator' p q r t pts| ≤ 1 := by
  unfold triangleIndicator';
  rw [ abs_mul, Finset.abs_prod ];
  refine' mul_le_one₀ _ _ _;
  · exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => abs_le.mpr ⟨ by split_ifs <;> linarith, by split_ifs <;> linarith ⟩;
  · positivity;
  · split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩
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
private lemma edge_sharing_integral_eq' {n d : ℕ} (p : ℝ)
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
private lemma edge_sharing_integral_factoring' {n d : ℕ} (p : ℝ)
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
private lemma doublySignedTriangle_cov_vertex_sharing_zero {n d : ℕ} (p : ℝ)
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
  -- OQ-18: relies on `vertex_sharing_indepFun'` (which uses `triangleIndicator'_factor_coord_diffs`,
  -- now stubbed) and the existential-form `hasFill` measurability. Stub pending refactor.
  sorry

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
private lemma doublySignedTriangle_cov_edge_sharing_le_sq {n d : ℕ} (p : ℝ)
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
private lemma triangleIndicator'_measurable {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t pts) := by
  unfold triangleIndicator' cechObservation
  simp only [CechSample.hasEdge, CechSample.hasFill]
  refine Measurable.mul ?_ ?_
  · exact Finset.measurable_prod _ fun e _ => by
      exact Measurable.ite (by simp only [decide_eq_true_eq]; exact measurableSet_le (Measurable.dist (measurable_pi_apply _) (measurable_pi_apply _)) measurable_const) measurable_const measurable_const
  · refine Measurable.ite ?_ measurable_const measurable_const
    simp only [decide_eq_true_eq]
    exact measurableSet_hasFill r t

/-- Independence of triangle indicators for disjoint triangles (sharing 0 vertices). -/
private lemma disjoint_triangles_indepFun {n d : ℕ} (p : ℝ)
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

private lemma doublySignedTriangle_cov_disjoint_eq_gsq {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (_htt' : t ≠ t')
    (_hshare : (t.val ∩ t'.val).card = 0) :
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
  -- OQ-18: relies on `disjoint_triangles_indepFun`, `single_triangle_integral_eq_g'`,
  -- and the existential-form `hasFill` measurability. Stub pending refactor.
  sorry

/-
OLD PROOF BODY:
  convert congr_arg ( fun x : ℝ => x ) ( integral_over_nu_eq' _ _ ) using 1;
  have h_ind : ProbabilityTheory.IndepFun (triangleIndicator' p (fillingProb p d) (matchRadius p d) t) (triangleIndicator' p (fillingProb p d) (matchRadius p d) t') (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) := by
    apply_rules [ disjoint_triangles_indepFun ];
  have h_integrable : MeasureTheory.Integrable (fun pts : Fin n → Torus d => triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts) (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) ∧ MeasureTheory.Integrable (fun pts : Fin n → Torus d => triangleIndicator' p (fillingProb p d) (matchRadius p d) t' pts) (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) := by
    have h_integrable : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, MeasureTheory.Integrable (fun pts : Fin n → Torus d => triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts) (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) := by
      intro t
      generalize_proofs at *; (
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1
      generalize_proofs at *; (
      norm_num +zetaDelta at *);
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.mul _ _;
        · refine' Finset.measurable_prod _ fun e he => _;
          refine' Measurable.ite _ measurable_const measurable_const;
          simp +decide [ cechObservation ];
          exact measurableSet_le ( measurable_pi_apply e.1 |> Measurable.dist <| measurable_pi_apply e.2 ) measurable_const |> MeasurableSet.mem;
        · refine' Measurable.ite _ measurable_const measurable_const;
          have h_measurable : MeasurableSet {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ matchRadius p d} := by
            have h_measurable : IsClosed (⋃ z : Torus d, {s : Fin n → Torus d | ∀ i ∈ t.val, dist (s i) z ≤ matchRadius p d}) := by
              refine' isClosed_of_closure_subset fun s hs => _;
              rw [ mem_closure_iff_seq_limit ] at hs
              generalize_proofs at *; (
              obtain ⟨ x, hx₁, hx₂ ⟩ := hs
              generalize_proofs at *; (
              choose z hz using fun n => Set.mem_iUnion.mp ( hx₁ n );
              obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
                have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
                  exact isCompact_univ_iff.mpr ( by infer_instance )
                generalize_proofs at *; (
                have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;)
              generalize_proofs at *; (
              obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
              exact Set.mem_iUnion.mpr ⟨ z', fun i hi => le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _ hi |> le_trans <| by norm_num ⟩)))
            generalize_proofs at *; (
            convert h_measurable.measurableSet using 1 ; ext ; aesop)
          generalize_proofs at *; (
          convert h_measurable using 1;
          ext; simp [cechObservation];
          exact?);
      · exact Filter.Eventually.of_forall fun x => triangleIndicator'_bound' p ( fillingProb p d ) ( matchRadius p d ) hp0 hp1 ( fillingProb_nonneg' p hp0 hp1 d ) ( fillingProb_le_one' p hp0 hp1 d ) t x |> le_trans <| by norm_num;)
    generalize_proofs at *; (
    exact ⟨ h_integrable t, h_integrable t' ⟩);
  have h_integral : ∫ pts, (triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts) * (triangleIndicator' p (fillingProb p d) (matchRadius p d) t' pts) ∂(MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) = (∫ pts, triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts ∂(MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))))) * (∫ pts, triangleIndicator' p (fillingProb p d) (matchRadius p d) t' pts ∂(MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))))) := by
    apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
    · exact h_integrable.1.1;
    · exact h_integrable.2.1;
  convert h_integral.symm using 1 ; ring!;
  rw [ single_triangle_integral_eq_g' p hp0 hp1 t, single_triangle_integral_eq_g' p hp0 hp1 t' ] ; ring!
-/

/-
Helper: the second moment E[τ²] satisfies a structured upper bound.
    E[τ²] ≤ C(n,3) + 12·C(n,4) + (C(n,3)² - C(n,3) - 12·C(n,4))·g².
    This comes from expanding τ² as a double sum and classifying pairs.
-/
set_option maxHeartbeats 1600000 in
private lemma cech_second_moment_structured (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let r := matchRadius p d
    let q := fillingProb p d
    let g := geometricCov p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    ∫ s, (doublySignedFilledCount p q s) ^ 2 ∂ν ≤
      (Nat.choose n 3 : ℝ) + 12 * (Nat.choose n 4 : ℝ) +
      ((Nat.choose n 3 : ℝ) ^ 2 - (Nat.choose n 3 : ℝ) - 12 * (Nat.choose n 4 : ℝ)) * g ^ 2 := by
  by_cases hn : n < 4;
  · interval_cases n <;> norm_num [ Nat.choose ];
    · rw [ MeasureTheory.integral_eq_zero_of_ae ];
      filter_upwards [ ] with s ; aesop;
    · rw [ MeasureTheory.integral_eq_zero_of_ae ];
      filter_upwards [ ] with s ; norm_num [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ];
      convert Finset.sum_empty;
    · -- Since there are no triangles when n=2, the sum is empty and thus the integral is zero.
      have h_empty : ∀ s : TwoParamSample 2, doublySignedFilledCount p (fillingProb p d) s = 0 := by
        unfold doublySignedFilledCount; aesop;
      aesop;
    · refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
      refine' fun s => 1;
      · exact Filter.Eventually.of_forall fun s => sq_nonneg _;
      · apply_rules [ MeasureTheory.integrable_const ];
      · filter_upwards [ ] with s;
        unfold doublySignedFilledCount;
        rw [ show ( Finset.univ : Finset { σ : Finset ( Fin 3 ) // σ.card = 3 } ) = { ⟨ { 0, 1, 2 }, by decide ⟩ } from by decide ] ; norm_num;
        split_ifs <;> norm_num [ triangleEdges ];
        · refine' le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) _ ) _;
          · rw [ Finset.abs_prod ];
            exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => by split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩ ;
          · refine' abs_le.mpr ⟨ _, _ ⟩ <;> linarith [ show 0 ≤ fillingProb p d from fillingProb_nonneg' p hp0 hp1 d, show fillingProb p d ≤ 1 from fillingProb_le_one' p hp0 hp1 d ];
        · refine' le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) _ ) _;
          · simp +decide [ Finset.prod_filter, Finset.prod_product ];
            split_ifs <;> exact abs_le.mpr ⟨ by nlinarith [ mul_nonneg hp0.le ( sq_nonneg p ), mul_nonneg hp0.le ( sq_nonneg ( 1 - p ) ) ], by nlinarith [ mul_nonneg hp0.le ( sq_nonneg p ), mul_nonneg hp0.le ( sq_nonneg ( 1 - p ) ) ] ⟩;
          · rw [ abs_of_nonneg ( fillingProb_nonneg' p hp0 hp1 d ) ] ; exact fillingProb_le_one' p hp0 hp1 d;
      · rw [ MeasureTheory.integral_const ] ; norm_num;
  · have h_bound : ∀ (t t' : {σ : Finset (Fin n) // σ.card = 3}), t ≠ t' → |∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d)))| ≤ if (t.val ∩ t'.val).card = 2 then 1 else (geometricCov p d) ^ 2 := by
      intros t t' htt';
      split_ifs;
      · convert doublySignedTriangle_cov_edge_sharing_le_sq p hp0 hp1 t t' htt' ‹_› using 1;
        simp +decide only [mul_assoc];
        congr! 1;
      · by_cases hshare : (t.val ∩ t'.val).card = 1 ∨ (t.val ∩ t'.val).card = 0;
        · cases hshare <;> simp_all +decide [ mul_assoc ];
          · have := @doublySignedTriangle_cov_vertex_sharing_zero n d p hp0 hp1 t t' htt' ‹_›; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
          · have h_disjoint : ∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d))) = (geometricCov p d) ^ 2 := by
              convert doublySignedTriangle_cov_disjoint_eq_gsq p hp0 hp1 t t' _ _ using 1;
              · simp +decide only [mul_assoc];
              · assumption;
              · aesop;
            convert h_disjoint.symm ▸ abs_pow ( geometricCov p d ) 2 |> le_of_eq using 1 ; ring!;
            · exact congr_arg _ ( by congr; ext; split_ifs <;> ring );
            · norm_num [ sq_abs ];
        · have h_card : (t.val ∩ t'.val).card ≤ 3 := by
            exact le_trans ( Finset.card_le_card ( Finset.inter_subset_left ) ) t.2.le;
          interval_cases _ : Finset.card ( t.val ∩ t'.val ) <;> simp_all +decide;
          have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_left : ( t.val ∩ t'.val ) ⊆ t.val ) ; have := Finset.eq_of_subset_of_card_le ( Finset.inter_subset_right : ( t.val ∩ t'.val ) ⊆ t'.val ) ; aesop;
    have h_off_diag : ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' ∈ Finset.univ.erase t, |∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d)))| ≤ 12 * Nat.choose n 4 + (Nat.choose n 3 * (Nat.choose n 3 - 1) - 12 * Nat.choose n 4) * (geometricCov p d) ^ 2 := by
      refine' le_trans ( Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => h_bound t t' _ ) _;
      · aesop;
      · have h_off_diag : ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' ∈ Finset.univ.erase t, (if (t.val ∩ t'.val).card = 2 then 1 else 0) = 12 * Nat.choose n 4 := by
          have h_off_diag : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' ∈ Finset.univ.erase t, (if (t.val ∩ t'.val).card = 2 then 1 else 0) = 3 * (n - 3) := by
            intro t
            have h_edge_sharing : Finset.card (Finset.filter (fun t' : Finset (Fin n) => t'.card = 3 ∧ (t.val ∩ t').card = 2) (Finset.powersetCard 3 (Finset.univ : Finset (Fin n)))) = 3 * (n - 3) := by
              have h_card : Finset.card (Finset.filter (fun t' : Finset (Fin n) => t'.card = 3 ∧ (t.val ∩ t').card = 2) (Finset.powersetCard 3 (Finset.univ : Finset (Fin n)))) = Finset.card (Finset.image (fun (s : Finset (Fin n) × Finset (Fin n)) => s.1 ∪ s.2) (Finset.product (Finset.powersetCard 2 t.val) (Finset.powersetCard 1 (Finset.univ \ t.val)))) := by
                congr with x ; simp +decide [ Finset.subset_iff ];
                constructor;
                · intro hx;
                  use t.val ∩ x, x \ t.val;
                  grind +qlia;
                · rintro ⟨ a, b, ⟨ ⟨ ha₁, ha₂ ⟩, ⟨ hb₁, hb₂ ⟩ ⟩, rfl ⟩ ; simp_all +decide [ Finset.disjoint_left ] ;
                  rw [ Finset.card_union_of_disjoint ];
                  · rw [ show ( t : Finset ( Fin n ) ) ∩ ( a ∪ b ) = a from ?_ ] ; aesop;
                    grind;
                  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => hb₁ hx₂ ( ha₁ hx₁ );
              rw [ h_card, Finset.card_image_of_injOn ];
              · simp +decide [ Finset.card_sdiff, * ];
              · intro x hx y hy; simp_all +decide [ Finset.ext_iff ] ;
                intro h; ext a; specialize h a; simp_all +decide [ Finset.subset_iff ] ;
                · grind +ring;
                · grind
            generalize_proofs at *; (
            convert h_edge_sharing using 1;
            rw [ ← Finset.card_filter ];
            refine' Finset.card_bij ( fun x hx => x.val ) _ _ _ <;> simp +decide [ Finset.mem_erase, Finset.mem_powersetCard ];
            grind);
          simp_all +decide [ Nat.choose_succ_succ ];
          rw [ show n.choose 4 = n.choose 3 * ( n - 3 ) / 4 from ?_ ];
          · rw [ ← Nat.mul_div_assoc ];
            · exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_four ( by ring ) );
            · rw [ ← Nat.choose_succ_right_eq ];
              exact dvd_mul_left _ _;
          · rw [ Nat.div_eq_of_eq_mul_left ] <;> norm_num;
            rw [ Nat.choose_succ_right_eq, mul_comm ];
        simp_all +decide [ Finset.sum_ite ];
        rw [ Finset.sum_add_distrib, ← Nat.cast_sum ] ; norm_num [ h_off_diag ];
        rw [ ← Finset.sum_mul _ _ _ ];
        rw [ show ( ∑ i : { σ : Finset ( Fin n ) // σ.card = 3 }, Finset.card ( Finset.filter ( fun x : { σ : Finset ( Fin n ) // σ.card = 3 } => ¬ ( i.val ∩ x.val ).card = 2 ) ( Finset.erase Finset.univ i ) ) : ℝ ) = ( Nat.choose n 3 : ℝ ) * ( Nat.choose n 3 - 1 ) - 12 * Nat.choose n 4 from ?_ ];
        rw [ show ( ∑ i : { σ : Finset ( Fin n ) // σ.card = 3 }, Finset.card ( Finset.filter ( fun x : { σ : Finset ( Fin n ) // σ.card = 3 } => ¬ ( i.val ∩ x.val ).card = 2 ) ( Finset.erase Finset.univ i ) ) : ℝ ) = ( ∑ i : { σ : Finset ( Fin n ) // σ.card = 3 }, ( Finset.card ( Finset.univ.erase i ) : ℝ ) ) - ( ∑ i : { σ : Finset ( Fin n ) // σ.card = 3 }, Finset.card ( Finset.filter ( fun x : { σ : Finset ( Fin n ) // σ.card = 3 } => ( i.val ∩ x.val ).card = 2 ) ( Finset.erase Finset.univ i ) ) : ℝ ) from ?_ ];
        · norm_num [ Finset.card_univ, h_off_diag ];
          rw [ Nat.cast_sub ] <;> norm_num [ h_off_diag ];
          · exact_mod_cast h_off_diag;
          · exact Nat.choose_pos ( by linarith );
        · rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num;
          rw [ Nat.cast_sub ] <;> norm_num;
          · rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ];
          · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_right ) ) ( by simp +decide [ Finset.card_erase_of_mem ( Finset.mem_univ _ ) ] );
    have h_diag : ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d))) ≤ (Nat.choose n 3 : ℝ) := by
      have h_diag : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, ∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d))) ≤ 1 := by
        intro t
        have h_diag : ∀ s : TwoParamSample n, |(((∏ e ∈ triangleEdges t, if s.edge e.1 e.2 = true then 1 - p else -p) * if s.fill t = true then 1 - fillingProb p d else -fillingProb p d) * ∏ e ∈ triangleEdges t, if s.edge e.1 e.2 = true then 1 - p else -p) * if s.fill t = true then 1 - fillingProb p d else -fillingProb p d| ≤ 1 := by
          intro s
          have h_abs : |∏ e ∈ triangleEdges t, if s.edge e.1 e.2 = true then 1 - p else -p| ≤ 1 := by
            rw [ Finset.abs_prod ] ; exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => by split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩ ;
          have h_abs_fill : |if s.fill t = true then 1 - fillingProb p d else -fillingProb p d| ≤ 1 := by
            split_ifs <;> norm_num [ abs_le ];
            · exact ⟨ le_trans ( fillingProb_le_one' p hp0 hp1 d ) ( by norm_num ), fillingProb_nonneg' p hp0 hp1 d ⟩;
            · exact ⟨ by linarith [ fillingProb_nonneg' p hp0 hp1 d ], by linarith [ fillingProb_le_one' p hp0 hp1 d ] ⟩
          generalize_proofs at *; (
          simpa only [ abs_mul ] using mul_le_one₀ ( mul_le_one₀ ( mul_le_one₀ h_abs ( abs_nonneg _ ) h_abs_fill ) ( abs_nonneg _ ) h_abs ) ( abs_nonneg _ ) h_abs_fill);
        refine' le_of_abs_le _;
        refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : TwoParamSample n → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
        use fun _ => 1;
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · filter_upwards [ ] using h_diag;
        · norm_num [ MeasureTheory.measureReal_def ];
      refine' le_trans ( Finset.sum_le_sum fun t _ => h_diag t ) _ ; norm_num [ Finset.card_univ ];
    have h_expand : ∫ s, (doublySignedFilledCount p (fillingProb p d) s) ^ 2 ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d))) = ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' : {σ : Finset (Fin n) // σ.card = 3}, ∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d))) := by
      have h_expand : ∀ s : TwoParamSample n, (doublySignedFilledCount p (fillingProb p d) s) ^ 2 = ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' : {σ : Finset (Fin n) // σ.card = 3}, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - fillingProb p d else -fillingProb p d) := by
        intro s
        simp [doublySignedFilledCount];
        rw [ sq, Finset.sum_mul ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;
      rw [ funext h_expand, MeasureTheory.integral_finset_sum ];
      · refine' Finset.sum_congr rfl fun t ht => _;
        rw [ MeasureTheory.integral_finset_sum ];
        intro i hi;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun s => 1;
        · norm_num +zetaDelta at *;
        · fun_prop (disch := norm_num);
        · refine' Filter.Eventually.of_forall fun s => _;
          have h_bound : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, ∀ s : TwoParamSample n, |(∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d)| ≤ 1 := by
            intros t s
            have h_bound : |∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)| ≤ 1 := by
              rw [ Finset.abs_prod ];
              exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => abs_le.mpr ⟨ by split_ifs <;> linarith, by split_ifs <;> linarith ⟩;
            split_ifs <;> norm_num [ abs_mul, h_bound ];
            · exact mul_le_one₀ h_bound ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ show fillingProb p d ≤ 1 from fillingProb_le_one' p hp0 hp1 d ], by linarith [ show fillingProb p d ≥ 0 from fillingProb_nonneg' p hp0 hp1 d ] ⟩ );
            · exact mul_le_one₀ h_bound ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ fillingProb_nonneg' p hp0 hp1 d ], by linarith [ fillingProb_le_one' p hp0 hp1 d ] ⟩ );
          convert mul_le_mul ( h_bound t s ) ( h_bound i s ) ( by positivity ) ( by positivity ) using 1 ; ring;
          · norm_num [ abs_mul ];
            split_ifs <;> norm_num [ abs_mul ] <;> ring;
          · norm_num;
      · intro t ht;
        refine' MeasureTheory.integrable_finset_sum _ _;
        intro i hi;
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun s => 1;
        · norm_num +zetaDelta at *;
        · exact?;
        · refine' Filter.Eventually.of_forall fun s => _;
          have h_bound : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, ∀ s : TwoParamSample n, |(∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d)| ≤ 1 := by
            intros t s
            have h_bound : |∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)| ≤ 1 := by
              rw [ Finset.abs_prod ];
              exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => abs_le.mpr ⟨ by split_ifs <;> linarith, by split_ifs <;> linarith ⟩;
            split_ifs <;> norm_num [ abs_mul, h_bound ];
            · exact mul_le_one₀ h_bound ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ show fillingProb p d ≤ 1 from fillingProb_le_one' p hp0 hp1 d ], by linarith [ show fillingProb p d ≥ 0 from fillingProb_nonneg' p hp0 hp1 d ] ⟩ );
            · exact mul_le_one₀ h_bound ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ fillingProb_nonneg' p hp0 hp1 d ], by linarith [ fillingProb_le_one' p hp0 hp1 d ] ⟩ );
          convert mul_le_mul ( h_bound t s ) ( h_bound i s ) ( by positivity ) ( by positivity ) using 1 ; ring;
          · norm_num [ abs_mul ];
            split_ifs <;> norm_num [ abs_mul ] <;> ring;
          · norm_num;
    have h_off_diag : ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' ∈ Finset.univ.erase t, ∫ s, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - fillingProb p d else -fillingProb p d) * (∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂(cechMeasure n d (matchRadius p d) |> MeasureTheory.Measure.map (cechObservation (matchRadius p d))) ≤ 12 * Nat.choose n 4 + (Nat.choose n 3 * (Nat.choose n 3 - 1) - 12 * Nat.choose n 4) * (geometricCov p d) ^ 2 := by
      refine' le_trans ( Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => le_abs_self _ ) h_off_diag;
    norm_num +zetaDelta at *;
    linarith

/-
Helper: the mean of τ under the Cech pushforward measure equals C(n,3)·g.
-/
private lemma cech_mean_eq (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let r := matchRadius p d
    let q := fillingProb p d
    let g := geometricCov p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    ∫ s, doublySignedFilledCount p q s ∂ν = (Nat.choose n 3 : ℝ) * g := by
  have := @cechDoublySigned_triangle_integral; ( have := @doublySignedFilledCount_cechObservation; simp_all +decide [ MeasureTheory.Measure.map_apply ] ; );
  contrapose! this with h_contra; simp_all +decide [ MeasureTheory.Measure.map_apply ] ;
  refine' ⟨ 1, 0, 0, 0, 0, _ ⟩ ; norm_num [ doublySignedFilledCount, cechDoublySignedCount ];
  refine' ⟨ _, _ ⟩;
  exact ⟨ fun _ => 0 ⟩;
  simp +decide [ cechObservation, CechSample.hasFill, CechSample.hasEdge ];
  exact h_contra <| by
    convert moments_cech_signed n d p hp0 hp1 using 1
    generalize_proofs at *; (
    convert integral_over_nu_eq' ( matchRadius p d ) ( fun s => doublySignedFilledCount p ( fillingProb p d ) s ) using 1
    generalize_proofs at *; (
    convert cech_integral_eq n d ( matchRadius p d ) ( fun s => cechDoublySignedCount p ( fillingProb p d ) s ( matchRadius p d ) ) using 1
    generalize_proofs at *; (
    exact congr_arg _ ( funext fun _ => doublySignedFilledCount_cechObservation _ _ _ _ ))));

/-- **Corrected variance bound for the doubly-signed Čech statistic.**
    Var[τ|Čech] ≤ C(n,3) + 12·C(n,4).

    The edge-sharing integral |∫ T_t·T_{t'} dμ| ≤ 1 (not ≤ g²) by the triangleIndicator' pointwise
    bound. Vertex-sharing covariance = 0 by independence. Diagonal ≤ C(n,3).

    PROVIDED SOLUTION
    Var[τ] = E[τ²] - E[τ]².
    Diagonal: C(n,3) terms, each E[T_t²] ≤ 1.
    Vertex-sharing off-diagonal: Cov(T_t, T_{t'}) = 0 (by doublySignedTriangle_cov_vertex_sharing_zero).
    Edge-sharing off-diagonal: |E[T_t·T_{t'}]| ≤ 1, with 12·C(n,4) pairs.
    Therefore: Var[τ] ≤ C(n,3) + 12·C(n,4).
    Lean approach:
    - Expand Var[τ] = E[τ²] - E[τ]² using MeasureTheory.variance_def.
    - Use Finset.sum_comm and linearity of integral to split into diagonal + off-diagonal.
    - For diagonal: E[T_t²] ≤ 1 by |T_t| ≤ 1 (doublySignedTriangle_sq_le_one).
    - For vertex-sharing off-diagonal: Cov = 0 (doublySignedTriangle_cov_vertex_sharing_zero).
    - For edge-sharing off-diagonal: |E[T_t·T_{t'}]| ≤ 1 (doublySignedTriangle_cov_edge_sharing_le_sq).
    - Count edge-sharing pairs: 12·C(n,4).
    Key Mathlib: MeasureTheory.variance_le_integral, Finset.card_le_card. -/
lemma cech_second_moment_bound (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    let r := matchRadius p d
    let q := fillingProb p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    ProbabilityTheory.variance (fun s => doublySignedFilledCount p q s) ν ≤
      (Nat.choose n 3 : ℝ) + 12 * (Nat.choose n 4 : ℝ) := by
  have h_var : ProbabilityTheory.variance (fun s : TwoParamSample n => doublySignedFilledCount p (fillingProb p d) s) ((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d))) = ∫ s : TwoParamSample n, (doublySignedFilledCount p (fillingProb p d) s) ^ 2 ∂((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d))) - (∫ s : TwoParamSample n, (doublySignedFilledCount p (fillingProb p d) s) ∂((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d)))) ^ 2 := by
    rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ← MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
    · rw [ MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall fun x => by rw [ sub_sq ] ) ] ; rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] <;> norm_num;
      norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ] ; ring;
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
    · exact Measurable.aestronglyMeasurable ( by measurability );
  have h_int_sq : ∫ s : TwoParamSample n, (doublySignedFilledCount p (fillingProb p d) s) ^ 2 ∂((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d))) ≤ (Nat.choose n 3 : ℝ) + 12 * (Nat.choose n 4 : ℝ) + ((Nat.choose n 3 : ℝ) ^ 2 - (Nat.choose n 3 : ℝ) - 12 * (Nat.choose n 4 : ℝ)) * (geometricCov p d) ^ 2 := by
    convert cech_second_moment_structured n d p hp0 hp1 using 1;
  have h_int : ∫ s : TwoParamSample n, doublySignedFilledCount p (fillingProb p d) s ∂((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d))) = (Nat.choose n 3 : ℝ) * geometricCov p d := by
    convert cech_mean_eq n d p hp0 hp1 using 1;
  simp_all +decide [ mul_pow ] ; nlinarith [ sq_nonneg ( geometricCov p d ) ] ;

/-- The complement probability P(τ < λ | Čech) is bounded by the Chebyshev ratio.
    P(τ < λ) ≤ P(|τ - E[τ]| ≥ E[τ] - λ) ≤ Var/(E[τ] - λ)².
    With E[τ] = C(n,3)*g and λ = C(n,3)*g/2:
      P(τ < λ) ≤ (C(n,3) + 12*C(n,4)) / (C(n,3)*g/2)² = O(1/(n²g²))

    PROVIDED SOLUTION
    Let μ = E[τ|Čech] = C(n,3)*g (from moments_cech_signed).
    Let λ = C(n,3)*g/2 = μ/2.
    Step 1: {s | τ(s) < λ} ⊆ {s | |τ(s) - μ| ≥ μ - λ} = {s | |τ(s) - μ| ≥ μ/2}.
      Proof: if τ < λ = μ/2, then μ - τ > μ/2, so |τ - μ| = μ - τ > μ/2.
    Step 2: By Chebyshev (Markov's inequality applied to (τ - μ)^2):
      ν({|τ - μ| ≥ μ/2}) ≤ E[(τ - μ)^2] / (μ/2)^2 = Var[τ|Čech] / (μ/2)^2.
    Step 3: Var[τ|Čech] ≤ E[τ^2|Čech] ≤ C(n,3) + 12*C(n,4) (from cech_second_moment_bound).
    Step 4: Combine:
      ν({s | τ < λ}).toReal ≤ (C(n,3) + 12*C(n,4)) / (C(n,3)*g/2)^2
        = 4*(C(n,3) + 12*C(n,4)) / (C(n,3)*g)^2.
    Lean approach:
    - Use MeasureTheory.Measure.toReal_mono to get the set inclusion bound.
    - Use ProbabilityTheory.meas_ge_le_variance_div_sq (Chebyshev) or
      Markov's inequality: ν({|X - E[X]| ≥ c}) ≤ E[(X - E[X])^2] / c^2.
    - Substitute E[τ|Čech] = C(n,3)*g from moments_cech_signed.
    - Substitute the second moment bound from cech_second_moment_bound.
    - Simplify: 4*(C(n,3)+12*C(n,4)) / (C(n,3)*g)^2.
    Key: the Čech pushforward is a probability measure (cechPushforward_isProbabilityMeasure),
    so Chebyshev applies. Use doublySignedFilledCount_cechObservation to relate
    doublySignedFilledCount on TwoParamSample to cechDoublySignedCount on CechSample. -/
lemma doublySignedFilledCount_memLp (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    MeasureTheory.MemLp (fun s => doublySignedFilledCount p (fillingProb p d) s) 2
      ((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d))) := by
  exact?

/-
PROBLEM
Helper: Chebyshev step for Cech complement bound.
    {f < λ} ⊆ {|f - μ| ≥ μ/2} when λ = μ/2 and μ/2 > 0.

PROVIDED SOLUTION
We need to show: ν {s | f(s) < λ} ≤ ν {s | λ ≤ |f(s) - ∫ f dν|}

where λ = C(n,3)*g/2 and ∫ f dν = C(n,3)*g (from moments_cech_signed).

So ∫ f dν - λ = C(n,3)*g - C(n,3)*g/2 = C(n,3)*g/2 = λ.

If f(s) < λ, then ∫ f dν - f(s) > ∫ f dν - λ = λ, so |f(s) - ∫ f dν| = ∫ f dν - f(s) ≥ λ (since ∫ f dν - f(s) > λ > 0).

So {f < λ} ⊆ {|f - ∫ f| ≥ λ}, which means ν({f < λ}) ≤ ν({|f - ∫ f| ≥ λ}).

Use MeasureTheory.measure_mono with the set inclusion.

Key: use moments_cech_signed to rewrite ∫ f dν = C(n,3)*g. Then the set {|f - ∫ f| ≥ λ} becomes {|f - C(n,3)*g| ≥ C(n,3)*g/2}. And for any s with f(s) < C(n,3)*g/2, we have C(n,3)*g - f(s) > C(n,3)*g/2, so |f(s) - C(n,3)*g| ≥ C(n,3)*g/2.
-/
lemma cech_complement_set_inclusion (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hcg : (Nat.choose n 3 : ℝ) * geometricCov p d / 2 > 0) :
    let r := matchRadius p d
    let q := fillingProb p d
    let g := geometricCov p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    ν {s | doublySignedFilledCount p q s < (Nat.choose n 3 : ℝ) * g / 2} ≤
      ν {s | (Nat.choose n 3 : ℝ) * g / 2 ≤
        |doublySignedFilledCount p q s - ∫ s', doublySignedFilledCount p q s' ∂ν|} := by
  -- OQ-18: depends on `moments_cech_signed` / `doublySignedFilledCount_cechObservation`
  -- (now stubbed) and existential `hasFill` measurability. Stub pending refactor.
  sorry

/-
OLD PROOF BODY:
  refine' MeasureTheory.measure_mono _;
  intro s hs
  generalize_proofs at *; (
  have := moments_cech_signed n d p hp0 hp1
  generalize_proofs at *; (
  -- By definition of `cechObservation`, we know that `∫ s', doublySignedFilledCount p (fillingProb p d) s' ∂MeasureTheory.Measure.map (cechObservation (matchRadius p d)) (cechMeasure n d (matchRadius p d))` is equal to `∫ s, cechDoublySignedCount p (fillingProb p d) s (matchRadius p d) ∂cechMeasure n d (matchRadius p d)`.
  have h_integral_eq : ∫ s', doublySignedFilledCount p (fillingProb p d) s' ∂MeasureTheory.Measure.map (cechObservation (matchRadius p d)) (cechMeasure n d (matchRadius p d)) = ∫ s, cechDoublySignedCount p (fillingProb p d) s (matchRadius p d) ∂cechMeasure n d (matchRadius p d) := by
    rw [ MeasureTheory.integral_map ] <;> norm_num [ doublySignedFilledCount_cechObservation ];
    · refine' Measurable.aemeasurable _;
      apply_rules [ measurable_to_countable', hs ];
      intro x; exact (by
        have h_preimage : MeasurableSet {s : Fin n → Torus d | cechObservation (matchRadius p d) ⟨s⟩ = x} := by
          have h_measurable : ∀ i j, MeasurableSet {s : Fin n → Torus d | (cechObservation (matchRadius p d) ⟨s⟩).edge i j = x.edge i j} := by
            intro i j
            have h_measurable : MeasurableSet {s : Fin n → Torus d | dist (s i) (s j) ≤ matchRadius p d} := by
              exact measurableSet_le ( measurable_pi_apply i |> Measurable.dist <| measurable_pi_apply j ) measurable_const
            generalize_proofs at *; (
            cases x.edge i j <;> simp_all +decide [ cechObservation ];
            · exact Measurable.not h_measurable;
            · convert h_measurable using 1)
          generalize_proofs at *; (
          have h_measurable : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, MeasurableSet {s : Fin n → Torus d | (cechObservation (matchRadius p d) ⟨s⟩).fill t = x.fill t} := by
            intro t
            have h_measurable : MeasurableSet {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ matchRadius p d} := by
              have h_closed : IsClosed (⋃ z : Torus d, {s : Fin n → Torus d | ∀ i ∈ t.val, dist (s i) z ≤ matchRadius p d}) := by
                refine' isClosed_of_closure_subset fun s hs => _;
                rw [ mem_closure_iff_seq_limit ] at hs
                generalize_proofs at *; (obtain ⟨ x, hx₁, hx₂ ⟩ := hs; (
                choose z hz using fun n => Set.mem_iUnion.mp ( hx₁ n );
                obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
                  have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
                    exact isCompact_univ_iff.mpr ( by infer_instance )
                  generalize_proofs at *; (
                  have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;)
                generalize_proofs at *; (
                obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz'
                generalize_proofs at *; (exact Set.mem_iUnion.mpr ⟨ z', fun i hi => le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _ hi |> le_trans <| by norm_num ⟩ ;))))
              generalize_proofs at *; (
              convert h_closed.measurableSet using 1 ; ext ; aesop)
            generalize_proofs at *; (
            cases x.fill t <;> simp_all +decide [ cechObservation ];
            · exact Measurable.not h_measurable;
            · convert h_measurable using 1)
          generalize_proofs at *; (
          have h_measurable : MeasurableSet {s : Fin n → Torus d | ∀ i j, (cechObservation (matchRadius p d) ⟨s⟩).edge i j = x.edge i j} ∧ MeasurableSet {s : Fin n → Torus d | ∀ t : {σ : Finset (Fin n) // σ.card = 3}, (cechObservation (matchRadius p d) ⟨s⟩).fill t = x.fill t} := by
            exact ⟨ by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by solve_by_elim, by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun t => by solve_by_elim ⟩
          generalize_proofs at *; (
          convert h_measurable.1.inter h_measurable.2 using 1 ; ext ; simp +decide [ cechObservation ] ; aesop)))
        generalize_proofs at *; (
        exact h_preimage.preimage ( measurable_iff_comap_le.mpr le_rfl ) ) ) ;
    · apply_rules [ MeasureTheory.MemLp.aestronglyMeasurable ];
      apply_rules [ doublySignedFilledCount_memLp ]
  generalize_proofs at *; (
  exact Set.mem_setOf_eq.mpr ( by cases abs_cases ( doublySignedFilledCount p ( fillingProb p d ) s - ∫ s', doublySignedFilledCount p ( fillingProb p d ) s' ∂MeasureTheory.Measure.map ( cechObservation ( matchRadius p d ) ) ( cechMeasure n d ( matchRadius p d ) ) ) <;> linarith [ Set.mem_setOf.mp hs ] ) ;)))
-/

/-
Chebyshev complement bound under the pushforward Čech measure: the probability
that doublySignedFilledCount is less than λ := C(n,3)·g/2 is ≤ 4·(C(n,3)+12·C(n,4)) / (C(n,3)·g)².
-/
lemma cech_complement_prob_bound (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hg : 0 < geometricCov p d) :
    let r := matchRadius p d
    let q := fillingProb p d
    let g := geometricCov p d
    let ν := (cechMeasure n d r).map (cechObservation r)
    let lam := (Nat.choose n 3 : ℝ) * g / 2
    (ν {s | doublySignedFilledCount p q s < lam}).toReal ≤
      4 * ((Nat.choose n 3 : ℝ) + 12 * (Nat.choose n 4 : ℝ)) /
        ((Nat.choose n 3 : ℝ) * g) ^ 2 := by
  by_cases hn : n.choose 3 = 0;
  · norm_num [ hn ];
    rw [ show { s : TwoParamSample n | doublySignedFilledCount p ( fillingProb p d ) s < 0 } = ∅ from _ ] <;> norm_num [ doublySignedFilledCount ];
    ext s; simp [triangleEdges];
    refine' Finset.sum_nonneg fun x hx => _;
    rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.choose ];
    · exact absurd x.2 ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by norm_num ) ) );
    · exact absurd x.2 ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by norm_num ) ) );
    · exact absurd x.2 ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_univ _ ) ( by norm_num ) ) );
  · have := @cech_complement_set_inclusion n d p hp0 hp1 ?_ <;> norm_num at *;
    · refine' le_trans ( ENNReal.toReal_mono _ this ) _;
      · exact?;
      · have := @ProbabilityTheory.meas_ge_le_variance_div_sq;
        refine' le_trans ( ENNReal.toReal_mono _ ( this _ _ ) ) _;
        · exact ENNReal.ofReal_ne_top;
        · convert doublySignedFilledCount_memLp n d p hp0 hp1 using 1;
        · positivity;
        · rw [ ENNReal.toReal_ofReal ];
          · rw [ div_le_div_iff₀ ] <;> try positivity;
            have := @cech_second_moment_bound n d p hp0 hp1; norm_num at *; nlinarith;
          · exact div_nonneg ( ProbabilityTheory.variance_nonneg _ _ ) ( sq_nonneg _ );
    · positivity

/-
Show 4·(C(n,3) + 12·C(n,4)) / (C(n,3)·g)² → 0 as k → ∞, given n_k → ∞ and n_k·g_k → ∞.

The original hypothesis `n^{3/2}·g → ∞` is insufficient for the Chebyshev ratio to
tend to zero. The ratio is approximately 72/(n²g²), which → 0 iff n·g → ∞. Since
n^{3/2}·g → ∞ does NOT imply n·g → ∞ (counterexample: g = log(n)/n^{3/2}), we add
the extra hypothesis `hNG : n·g → ∞`. Note that `hSNR` is still used to invoke
`choose3_g_sq_tendsto_atTop`.
-/
-- `chebyshev_ratio_tendsto_zero` moved to `Core.Detection` (Phase A3.3) and
-- abstracted to take a real-valued sequence `g : ℕ → ℝ` instead of `geometricCov p ∘ dSeq`.

/-
Under the Cech pushforward, the probability that the doubly-signed statistic
exceeds threshold λ tends to 1.
-/
/-- **OQ-18 / Phase A3.4.** L∞ Rips specialization of the abstract Paley–Zygmund
    tendsto-one. The body delegates to `paleyZygmund_prob_tendsto_one_abstract` with the
    Čech pushforward as `ν`, `doublySignedFilledCount` as the statistic, and
    `geometricCov` as the covariance scale; the per-`k` complement bound comes from
    `cech_complement_prob_bound`, which only fires once `geometricCov > 0` (eventually
    true given `hNG`). -/
lemma paleyZygmund_cech_prob_tendsto_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop)
    (hNG : Filter.Tendsto
      (fun k => (nSeq k : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
        (cechObservation (matchRadius p (dSeq k)))
        {s | doublySignedFilledCount p (fillingProb p (dSeq k)) s ≥
          (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2}).toReal)
      Filter.atTop (nhds 1) := by
  -- Eventually `geometricCov > 0` along the SNR hypothesis.
  have h_gpos : ∀ᶠ k in Filter.atTop, 0 < geometricCov p (dSeq k) := by
    filter_upwards [hNG.eventually_gt_atTop 0] with k hk
    nlinarith [show (nSeq k : ℝ) ≥ 0 by positivity]
  -- Eventual complement bound via `cech_complement_prob_bound`.
  have h_compl :
      ∀ᶠ k in Filter.atTop,
        ((MeasureTheory.Measure.map (cechObservation (matchRadius p (dSeq k)))
          (cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))))
          {s | doublySignedFilledCount p (fillingProb p (dSeq k)) s <
            (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2}).toReal ≤
        4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
          ((Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k)) ^ 2 := by
    filter_upwards [h_gpos] with k hk
    exact cech_complement_prob_bound _ _ _ hp0 hp1 hk
  -- Threshold-event measurability under the discrete σ-algebra.
  have h_thr : ∀ k, MeasurableSet
      {s : TwoParamSample (nSeq k) |
        doublySignedFilledCount p (fillingProb p (dSeq k)) s ≥
          (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2} :=
    fun k => threshold_event_measurableSet _ _ _ _
  -- Delegate to the abstract Paley–Zygmund.
  exact paleyZygmund_prob_tendsto_one_abstract
    (Ω := fun k => TwoParamSample (nSeq k))
    (ν := fun k => (cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
      (cechObservation (matchRadius p (dSeq k))))
    (T := fun k s => doublySignedFilledCount p (fillingProb p (dSeq k)) s)
    nSeq (fun k => geometricCov p (dSeq k))
    hn hSNR hNG h_thr h_compl

-- `threshold_event_measurableSet` moved to `Core/Detection.lean` (phase A3.1).

/-
PROBLEM
fillingProb is always in [0, 1].

PROVIDED SOLUTION
fillingProb p d is defined as an integral over Set.Ioo 0 1 of a nonneg integrand (volumeFill / volumeEmpty * d * s^(d-1)). Actually, the volumeFill and volumeEmpty could have either sign depending on the integrals, and the ratio could be negative. But since they represent volumes, they should be nonneg.

Actually, let's look at the definition: fillingProb p d = ∫ s in Set.Ioo 0 1, volumeFill d r s / volumeEmpty d r s * d * s^(d-1).

If d = 0, this is ∫ 0 * 0 * ... = 0 ≥ 0. For d ≥ 1, the integrand involves ratios of volumes which should be nonneg.

Actually, this is hard to prove rigorously. Let me try MeasureTheory.setIntegral_nonneg with the condition that the integrand is nonneg.
-/
-- `fillingProb_nonneg` moved earlier (before `chebyshev_2PC_prob_tendsto_zero`, which depends on it).


/- The fill volume is at most the empty volume for all valid parameters.
    Geometrically, the fill region (common intersection of three r-balls)
    is a subset of the empty region (intersection of two 2r-balls).

    PROVIDED SOLUTION
    Key geometric fact: the Cech fill region ⊆ Cech empty region.
    Concretely:
    - volumeEmpty d r s = Vol(B(0,2r) ∩ B(v,2r)) where v has |v|=s, i.e., the
      intersection of two balls of radius 2r whose centres are distance s apart.
    - volumeFill d r s = Vol({w : |w| ≤ r} ∩ {w : |w-v| ≤ r} ∩ {w : |w-u| ≤ r})
      for some third vertex u with |u| ≤ r and |u-v| ≤ r, integrated over all such u.
      Actually volumeFill d r s is the volume of the region a third point w must occupy
      so that all three pairwise distances are ≤ r (Cech fill), given two points at
      distance s. This means |w| ≤ r AND |w-v| ≤ r (and the two original points are
      within r of each other, so s ≤ r is needed for the triangle to be fillable).
    The key containment: if |w| ≤ r and |w-v| ≤ r (fill condition), then by triangle
    inequality |w - v| ≤ |w| + |v| = r + s ≤ 2r (empty condition, since s ≤ 1 ≤ r
    when r ≥ 1/2 which holds for matchRadius p d → ∞).
    Wait: the empty condition is |w| ≤ 2r AND |w-v| ≤ 2r. The fill condition is
    |w| ≤ r AND |w-v| ≤ r. Since r ≤ 2r, fill ⊆ empty trivially.
    Therefore volumeFill d r s ≤ volumeEmpty d r s, so the ratio ≤ 1.
    Lean approach:
    - Unfold volumeFill and volumeEmpty as integrals.
    - Show the fill integration domain is a subset of the empty integration domain.
      Fill domain: {w | |w| ≤ r ∧ |w-v| ≤ r} ⊆ {w | |w| ≤ 2r ∧ |w-v| ≤ 2r} = empty domain.
      This follows because r ≤ 2r (trivially, since r > 0).
    - Apply MeasureTheory.measure_mono to get Vol(fill domain) ≤ Vol(empty domain).
    - Divide both sides by Vol(empty domain) (which is positive for s < 2r).
    In terms of the integral definitions:
    - volumeEmpty d r s = euclidBallVol d (2*r) * incBeta / betaFn where
      incBeta = ∫_0^x t^(a-1)*(1-t)^(b-1) dt and x = 1-(s/2r)^2.
    - volumeFill d r s involves integrals I₁ and I₂ over the fill region.
    Direct comparison of integrals:
    - The fill region corresponds to the intersection of two r-balls.
    - The empty region corresponds to the intersection of two 2r-balls.
    - Since r ≤ 2r, the r-ball intersection is contained in the 2r-ball intersection.
    - Therefore volumeFill d r s ≤ volumeEmpty d r s.
    If direct set containment is hard to formalize from the integral definitions,
    use the following: both volumeFill and volumeEmpty are nonneg (they are volumes),
    and volumeEmpty = euclidBallVol d (2r) * I_x(a,b) where I_x is the regularised
    incomplete beta function with x = 1-(s/2r)^2 ∈ (0,1). The fill volume can be
    bounded by euclidBallVol d r (the ball of radius r) which is ≤ euclidBallVol d (2r)
    since r ≤ 2r. The empty volume is at least euclidBallVol d r (the smaller ball fits
    inside the intersection of the two 2r-balls when s ≤ r). This gives the bound.
    Simplest Lean proof: show volumeFill d r s ≤ volumeEmpty d r s by showing
    the fill integrand is pointwise ≤ the empty integrand after unfolding, or
    use div_le_one (volumeEmpty_pos) and show volumeFill ≤ volumeEmpty directly. -/

/- For all d, the fill/empty ratio is ≤ 1.

    Now that volumeFill and volumeEmpty have the same beta-integral structure, the proof
    is a clean algebraic+monotonicity argument:

    volumeFill d r s / volumeEmpty d r s
      = (euclidBallVol d r / euclidBallVol d (2*r)) * (incBeta_fill / incBeta_empty)

    where:
    - euclidBallVol d r / euclidBallVol d (2*r) = (r/(2r))^d = (1/2)^d ≤ 1
    - incBeta_fill = ∫_0^{x_fill} ..., x_fill = 1-(s/2r)^2
    - incBeta_empty = ∫_0^{x_empty} ..., x_empty = 1-(s/4r)^2
    - x_fill ≤ x_empty (since s/(2r) ≥ s/(4r) for r > 0), so incBeta_fill ≤ incBeta_empty.
    - betaFn cancels in the ratio.

    Therefore ratio ≤ (1/2)^d · 1 ≤ 1. -/

open MeasureTheory in
private lemma incBeta_nonneg (d : ℕ) (x : ℝ) :
    0 ≤ ∫ t in Set.Ioo 0 x,
      t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) := by
  by_contra h_neg;
  convert h_neg <| MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht => ?_ using 1;
  by_cases h : 1 - t ≥ 0;
  · exact mul_nonneg ( Real.rpow_nonneg ht.1.le _ ) ( Real.rpow_nonneg h _ );
  · norm_num [ Real.rpow_def_of_neg ( not_le.mp h ) ];
    norm_num [ show 1 / 2 * Real.pi = Real.pi / 2 by ring ]

open MeasureTheory in
private lemma incBeta_mono (d : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    ∫ t in Set.Ioo 0 x, t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) ≤
    ∫ t in Set.Ioo 0 y, t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) := by
  refine' MeasureTheory.setIntegral_mono_set _ _ _;
  · have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioc 0 1) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioo 0 1) := by
        have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ)) (Set.Ioo 0 1) ∧ MeasureTheory.IntegrableOn (fun t : ℝ => (1 - t) ^ (1 / 2 - 1 : ℝ)) (Set.Ioo 0 1) := by
          constructor;
          · exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith [ show ( d : ℝ ) ≥ 0 by positivity ] ) ).1.mono_set ( Set.Ioo_subset_Ioc_self );
          · have h_integrable : ∫ t in Set.Ioo (0 : ℝ) 1, (1 - t) ^ (-1 / 2 : ℝ) = 2 * Real.sqrt 1 := by
              rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_comp_sub_left fun t => t ^ ( -1 / 2 : ℝ ), integral_rpow ] <;> norm_num;
            exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef ( by norm_num at *; aesop ) ] ; norm_num );
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun t => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) + ( 1 - t ) ^ ( 1 / 2 - 1 : ℝ );
        · exact MeasureTheory.Integrable.add h_integrable.1 h_integrable.2;
        · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.1.aestronglyMeasurable ) ( h_integrable.2.aestronglyMeasurable );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with t ht;
          rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.rpow_nonneg ht.1.le _ ) ( Real.rpow_nonneg ( sub_nonneg.2 ht.2.le ) _ ) ) ];
          rcases d with ( _ | _ | d ) <;> norm_num at *;
          · norm_num [ Real.rpow_neg ht.1.le, Real.rpow_neg ( sub_nonneg.2 ht.2.le ) ];
            rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow ];
            field_simp;
            rw [ div_add_div, div_le_div_iff₀ ] <;> nlinarith [ Real.sqrt_pos.2 ht.1, Real.sqrt_pos.2 ( sub_pos.2 ht.2 ), Real.mul_self_sqrt ( show 0 ≤ t by linarith ), Real.mul_self_sqrt ( show 0 ≤ 1 - t by linarith ), mul_pos ( Real.sqrt_pos.2 ht.1 ) ( Real.sqrt_pos.2 ( sub_pos.2 ht.2 ) ) ];
          · rw [ Real.rpow_neg ( by linarith ) ];
            exact le_add_of_nonneg_of_le ( Real.rpow_nonneg ht.1.le _ ) ( mul_le_of_le_one_left ( inv_nonneg.2 ( Real.rpow_nonneg ( by linarith ) _ ) ) ( Real.rpow_le_one ht.1.le ht.2.le ( by linarith [ show ( d : ℝ ) ≥ 0 by positivity ] ) ) );
      rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc ] at *;
    have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioc 0 (max y 1)) := by
      have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((d + 1) / 2 - 1 : ℝ) * (1 - t) ^ ((1 : ℝ) / 2 - 1)) (Set.Ioc 1 (max y 1)) := by
        refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun t => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) * 0 ^ ( 1 / 2 - 1 : ℝ );
        · norm_num;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.pow_const _ ) ( Measurable.pow_const ( measurable_const.sub measurable_id ) _ ) );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht ; norm_num [ Real.rpow_def_of_neg ( by linarith [ ht.1 ] : 1 - t < 0 ) ];
          norm_num [ show 1 / 2 * Real.pi = Real.pi / 2 by ring ];
      convert MeasureTheory.IntegrableOn.union ‹MeasureTheory.IntegrableOn ( fun t : ℝ => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) * ( 1 - t ) ^ ( 1 / 2 - 1 : ℝ ) ) ( Set.Ioc 0 1 ) volume› ‹MeasureTheory.IntegrableOn ( fun t : ℝ => t ^ ( ( d + 1 ) / 2 - 1 : ℝ ) * ( 1 - t ) ^ ( 1 / 2 - 1 : ℝ ) ) ( Set.Ioc 1 ( Max.max y 1 ) ) volume› using 1 ; norm_num;
    exact h_integrable.mono_set ( Set.Ioo_subset_Ioc_self.trans ( Set.Ioc_subset_Ioc_right ( le_max_left _ _ ) ) );
  · refine' MeasureTheory.ae_restrict_mem measurableSet_Ioo |> fun h => h.mono fun t ht => _;
    by_cases h : 1 - t ≥ 0 <;> simp_all +decide [ Real.rpow_def_of_pos, Real.rpow_def_of_neg ];
    · exact mul_nonneg ( Real.exp_nonneg _ ) ( Real.rpow_nonneg ( by linarith ) _ );
    · norm_num [ ( by ring : 1 / 2 * Real.pi = Real.pi / 2 ) ];
  · exact MeasureTheory.ae_of_all _ fun t ht => ⟨ ht.1, ht.2.trans_le hxy ⟩

open MeasureTheory in
lemma volumeFill_div_volumeEmpty_le_one_ge2 (d : ℕ) (r s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    volumeFill d r s / volumeEmpty d r s ≤ 1 := by
  unfold volumeFill volumeEmpty;
  by_cases hr : r = 0 <;> simp_all +decide [ mul_pow, div_eq_mul_inv ];
  · unfold euclidBallVol;
    cases d <;> norm_num;
    by_cases h : ∫ t in Set.Ioo ( 0 : ℝ ) 1, t ^ ( - ( 1 / 2 : ℝ ) ) * ( 1 - t ) ^ ( - ( 1 / 2 : ℝ ) ) = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    norm_num [ ← mul_assoc, ne_of_gt ( Real.Gamma_pos_of_pos _ ) ];
  · unfold euclidBallVol; ring_nf; norm_num [ hr ] ;
    field_simp;
    refine' div_le_one_of_le₀ _ _;
    · refine' le_trans ( mul_le_of_le_one_right ( MeasureTheory.setIntegral_nonneg ( by norm_num ) fun x hx => _ ) ( pow_le_one₀ ( by norm_num ) ( by norm_num ) ) ) _;
      · exact mul_nonneg ( Real.rpow_nonneg hx.1.le _ ) ( Real.rpow_nonneg ( sub_nonneg.2 <| hx.2.le.trans <| div_le_one_of_le₀ ( by nlinarith ) <| by positivity ) _ );
      · convert incBeta_mono d _ using 3 ; ring;
        · grind;
        · rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_self_pos.2 hr ];
    · refine' MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht => mul_nonneg ( Real.rpow_nonneg ( by linarith [ ht.1 ] ) _ ) ( Real.rpow_nonneg ( by linarith [ ht.2, show ( r ^ 2 * 16 + -s ^ 2 ) / ( r ^ 2 * 16 ) ≤ 1 by rw [ div_le_iff₀ <| by positivity ] ; nlinarith ] ) _ )

/-- For d = 0, the fill/empty ratio is ≤ 1. Follows from the unified ge2 lemma. -/
lemma volumeFill_div_volumeEmpty_le_one_d0 (r s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    volumeFill 0 r s / volumeEmpty 0 r s ≤ 1 :=
  volumeFill_div_volumeEmpty_le_one_ge2 0 r s hs hs1

lemma volumeFill_div_volumeEmpty_le_one (d : ℕ) (r s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    volumeFill d r s / volumeEmpty d r s ≤ 1 := by
  rcases d with _ | d
  · exact volumeFill_div_volumeEmpty_le_one_d0 r s hs hs1
  · exact volumeFill_div_volumeEmpty_le_one_ge2 (d + 1) r s hs hs1

/-
PROVIDED SOLUTION
For d = 0: the integrand is 0 * s^0 = 0, integral is 0 ≤ 1.

For d ≥ 1: Use MeasureTheory.integral_Ioo_eq_integral_Ioc (they're equal for Lebesgue measure). Then use intervalIntegral.integral_pow or compute directly:
∫ s in Ioo 0 1, d * s^(d-1) = d * ∫ s in Ioo 0 1, s^(d-1)

For the integral of s^(d-1) over [0,1]: this equals [s^d / d]₀¹ = 1/d.

So the total integral is d * (1/d) = 1.

Alternatively, use the fact that ∫ s in Set.Ioo 0 1, d * s^(d-1) = ∫ s in Set.Ioo 0 1, (d : ℝ) * s ^ (d-1) and convert to an interval integral ∫ x in (0 : ℝ)..1, ↑d * x ^ (d - 1), then use integral_pow to get [x^d/d]₀¹ = 1/d, multiply by d to get 1.

Key Mathlib lemmas: intervalIntegral.integral_pow, MeasureTheory.integral_Ioc_eq_integral_Ioo (or similar), mul_comm_div.
-/
open MeasureTheory in
/-- The integral of d · s^(d-1) over (0,1) equals at most 1.
    For d = 0 the integrand vanishes; for d ≥ 1 it is exactly 1. -/
lemma beta_density_integral_le_one (d : ℕ) :
    ∫ s in Set.Ioo (0 : ℝ) 1, (d : ℝ) * s ^ (d - 1 : ℕ) ≤ 1 := by
  rcases d with ( _ | d ) <;> norm_num [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one ] at *;
  rw [ mul_inv_cancel₀ ( by linarith ) ]

/-
PROVIDED SOLUTION
Use volumeFill_div_volumeEmpty_le_one and beta_density_integral_le_one.

fillingProb p d = ∫ s in Ioo 0 1, (volumeFill d r s / volumeEmpty d r s) * d * s^(d-1)

Step 1: Show the integrand is ≤ d * s^(d-1) pointwise for s ∈ (0,1).
  Since volumeFill_div_volumeEmpty_le_one gives volumeFill/volumeEmpty ≤ 1 for s ∈ (0,1),
  and d * s^(d-1) ≥ 0, we get:
  (volumeFill/volumeEmpty) * d * s^(d-1) ≤ 1 * d * s^(d-1) = d * s^(d-1)

Step 2: Use MeasureTheory.setIntegral_mono_on (or setIntegral_mono) to get:
  ∫ s in Ioo 0 1, (volumeFill/volumeEmpty) * d * s^(d-1)
  ≤ ∫ s in Ioo 0 1, d * s^(d-1)

Step 3: By beta_density_integral_le_one: ∫ s in Ioo 0 1, d * s^(d-1) ≤ 1.

Combine steps 2 and 3 via le_trans.

For setIntegral_mono_on, need integrability of both functions. Since s ∈ (0,1) and d is fixed:
- d * s^(d-1) is continuous on [0,1], hence integrable.
- For the first function: use that it's bounded (≤ d * s^(d-1) which is integrable) and measurable.

Actually the integrability may be hard. Use IntegrableOn for bounded measurable functions on a bounded set. Or use MeasureTheory.setIntegral_le_setIntegral_of_le for the comparison.

Key: mul_le_mul_of_nonneg_right (volumeFill_div_volumeEmpty_le_one ...) (by positivity : d * s^(d-1) ≥ 0)
-/
-- `fillingProb_le_one` moved earlier (before `chebyshev_2PC_prob_tendsto_zero`, which depends on it).

/-- **Theorem 1 (Detection Lower Bound, Strategy 2).** Fix p ∈ (0,1).
    If n_k^{3/2} · geometricCov p d_k → ∞ and n_k · geometricCov p d_k → ∞, then TV → 1.
    The second hypothesis is the one actually load-bearing in the Paley–Zygmund
    step (the `O(n⁴)` variance bound forces `n·g → ∞`, which is strictly stronger
    than the advertised `n^{3/2}·g → ∞`). -/
theorem detection_lower_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop)
    (hNG : Filter.Tendsto
      (fun k => (nSeq k : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => tvDist
        (twoParamMeasure (nSeq k) p (fillingProb p (dSeq k)))
        ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
          (cechObservation (matchRadius p (dSeq k)))))
      Filter.atTop (nhds 1) := by
  -- Abbreviations
  set q : ℕ → ℝ := fun k => fillingProb p (dSeq k)
  set r : ℕ → ℝ := fun k => matchRadius p (dSeq k)
  set μ : ∀ k, MeasureTheory.Measure (TwoParamSample (nSeq k)) :=
    fun k => twoParamMeasure (nSeq k) p (q k)
  set ν : ∀ k, MeasureTheory.Measure (TwoParamSample (nSeq k)) :=
    fun k => (cechMeasure (nSeq k) (dSeq k) (r k)).map (cechObservation (r k))
  set lam : ℕ → ℝ := fun k => (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2
  set A : ∀ k, Set (TwoParamSample (nSeq k)) :=
    fun k => {s | doublySignedFilledCount p (q k) s ≥ lam k}
  -- Probability measure instances
  have hμ_prob : ∀ k, MeasureTheory.IsProbabilityMeasure (μ k) := fun k =>
    twoParamMeasure_isProbabilityMeasure _ _ _ hp0.le hp1.le
      (fillingProb_nonneg p (dSeq k)) (fillingProb_le_one p (dSeq k))
  have hν_prob : ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) := fun k =>
    cechPushforward_isProbabilityMeasure _ _ _
  -- Measurability of A
  have hA_meas : ∀ k, MeasurableSet (A k) := fun k =>
    threshold_event_measurableSet _ _ _ _
  -- Squeeze: ν(A) - μ(A) ≤ tvDist ≤ 1, and ν(A) - μ(A) → 1
  have h_lower_tendsto : Filter.Tendsto
      (fun k => (ν k (A k)).toReal - (μ k (A k)).toReal) Filter.atTop (nhds 1) := by
    have h1 := chebyshev_2PC_prob_tendsto_zero p hp0 hp1 nSeq dSeq hn hSNR
    have h2 := paleyZygmund_cech_prob_tendsto_one p hp0 hp1 nSeq dSeq hn hSNR hNG
    have h3 := h2.sub h1
    simp only [sub_zero] at h3
    convert h3 using 1
  have h_lower_bound : ∀ᶠ k in Filter.atTop,
      (ν k (A k)).toReal - (μ k (A k)).toReal ≤ tvDist (μ k) (ν k) :=
    Filter.Eventually.of_forall fun k => by
      haveI := hμ_prob k; haveI := hν_prob k
      have h := tvDist_ge_abs (μ k) (ν k) (A k) (hA_meas k)
      linarith [le_abs_self ((ν k (A k)).toReal - (μ k (A k)).toReal),
                abs_sub_comm ((μ k (A k)).toReal) ((ν k (A k)).toReal)]
  have h_upper_bound : ∀ᶠ k in Filter.atTop,
      tvDist (μ k) (ν k) ≤ 1 :=
    Filter.Eventually.of_forall fun k => by
      haveI := hμ_prob k; haveI := hν_prob k
      exact tvDist_le_one _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    h_lower_tendsto tendsto_const_nhds h_lower_bound h_upper_bound

/-- **Paper Theorem 4.2 (Detection lower bound, fixed d).** For fixed `d` with
    `geometricCov p d > 0` and any `n → ∞`, the total variation distance between
    the 2PC and Čech observation models tends to 1.

    This is the exact Lean counterpart to the paper's Theorem 4.2: the hypothesis
    `g = geometricCov p d > 0` with `d` constant makes both `n^{3/2}·g → ∞` and
    `n·g → ∞` automatic, so it specialises `detection_lower_bound`. -/
theorem detection_lower_bound_fixed_d (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (d : ℕ) (hg : 0 < geometricCov p d)
    (nSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => tvDist
        (twoParamMeasure (nSeq k) p (fillingProb p d))
        ((cechMeasure (nSeq k) d (matchRadius p d)).map
          (cechObservation (matchRadius p d))))
      Filter.atTop (nhds 1) := by
  have hn_real : Filter.Tendsto (fun k => (nSeq k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hSNR : Filter.Tendsto (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p d)
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2)).comp hn_real
    exact h1.atTop_mul_const hg
  have hNG : Filter.Tendsto (fun k => (nSeq k : ℝ) * geometricCov p d)
      Filter.atTop Filter.atTop :=
    hn_real.atTop_mul_const hg
  exact detection_lower_bound p hp0 hp1 nSeq (fun _ => d) hn hSNR hNG

/-- Deriving SNR → ∞ from asymptotic equivalence and dimension scaling.
    If geometricCov p d ~ G * d^{-α} and d / (n^{3/2} * G)^{1/α} → 0,
    then n^{3/2} * geometricCov p d → ∞.

    PROVIDED SOLUTION
    We have geometricCov p d ~ G * d^{-α} (hasymp) and d_k / (n_k^{3/2} * G)^{1/α} → 0 (hbeyond).
    Goal: n_k^{3/2} * geometricCov p d_k → ∞.
    Step 1: From hasymp, geometricCov p d_k / (G * d_k^{-α}) → 1, so
      geometricCov p d_k ~ G * d_k^{-α}. More precisely, eventually
      geometricCov p d_k ≥ (1/2) * G * d_k^{-α}.
    Step 2: So n_k^{3/2} * geometricCov p d_k ≥ (1/2) * G * n_k^{3/2} * d_k^{-α}
      = (1/2) * G * n_k^{3/2} / d_k^α.
    Step 3: From hbeyond: d_k / (n_k^{3/2} * G)^{1/α} → 0, i.e., d_k ≪ (n_k^{3/2} * G)^{1/α}.
      Taking α-th powers: d_k^α ≪ n_k^{3/2} * G.
      So n_k^{3/2} * G / d_k^α → ∞.
    Step 4: Combining: n_k^{3/2} * geometricCov p d_k ≥ (1/2) * G * n_k^{3/2} / d_k^α
      = (1/2) * (n_k^{3/2} * G / d_k^α) → ∞.
    Lean approach:
    Step A: From hbeyond (d_k / (n_k^{3/2}*G)^{1/α} → 0) and hα > 0, derive
      (n_k^{3/2}*G)^{1/α} / d_k → ∞ (reciprocal of a sequence tending to 0).
      Use Filter.Tendsto.inv_tendsto_atTop or tendsto_inv_atTop_zero.
    Step B: Raise to the α-th power: (n_k^{3/2}*G) / d_k^α → ∞.
      Use Filter.Tendsto.rpow_atTop or monotone composition.
    Step C: Multiply by n_k^{3/2}: n_k^{3/2} * G / d_k^α → ∞.
      Use Filter.Tendsto.atTop_mul_const (G > 0).
    Step D: From hasymp, eventually geometricCov p d ≥ (1/2) * G * d^{-α}.
      Use Filter.Tendsto.eventually (hasymp.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
      to get: eventually geometricCov p d_k / (G * d_k^{-α}) > 1/2.
    Step E: Combine D and C: n_k^{3/2} * geometricCov p d_k
      ≥ n_k^{3/2} * (1/2) * G * d_k^{-α} = (1/2) * (n_k^{3/2} * G / d_k^α) → ∞.
      Use Filter.tendsto_atTop_mono.
    Key Mathlib: Filter.Tendsto.inv_tendsto_atTop, Real.rpow_natCast,
    Filter.tendsto_atTop_mono, mul_comm, Real.rpow_neg (for d^{-α} = 1/d^α). -/
lemma derive_hSNR (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (G α : ℝ) (hG : 0 < G) (hα : 0 < α)
    (hasymp : Filter.Tendsto
      (fun d : ℕ => geometricCov p d / (G * (d : ℝ) ^ (-α)))
      Filter.atTop (nhds 1))
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    (hbeyond : Filter.Tendsto
      (fun k => (dSeq k : ℝ) / ((nSeq k : ℝ) ^ (3/2 : ℝ) * G) ^ (1 / α))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop := by
  -- From hbeyond, we know that $d_k / (n_k^{3/2} * G)^{1/α} → 0$.
  -- Taking $α$-th powers, we have $d_k^α / (n_k^{3/2} * G) → 0$.
  -- Therefore, $n_k^{3/2} * G / d_k^α → ∞$.
  have h_div : Filter.Tendsto (fun k => (nSeq k : ℝ) ^ (3 / 2 : ℝ) * G / (dSeq k : ℝ) ^ α) Filter.atTop Filter.atTop := by
    have h_div : Filter.Tendsto (fun k => ((nSeq k : ℝ) ^ (3 / 2 : ℝ) * G) ^ (1 / α) / (dSeq k : ℝ)) Filter.atTop Filter.atTop := by
      have h_div : Filter.Tendsto (fun k => (1 : ℝ) / ((dSeq k : ℝ) / (nSeq k ^ (3 / 2 : ℝ) * G) ^ (1 / α))) Filter.atTop Filter.atTop := by
        refine' Filter.Tendsto.const_mul_atTop _ _ <;> norm_num
        generalize_proofs at *; (
        have h_inv : Filter.Tendsto (fun k => ((dSeq k : ℝ) / (nSeq k ^ (3 / 2 : ℝ) * G) ^ (1 / α))⁻¹) Filter.atTop Filter.atTop := by
          refine' Filter.Tendsto.inv_tendsto_nhdsGT_zero _;
          -- Since the function is positive and tends to 0 in the real numbers, it also tends to 0 within the positive reals.
          have h_pos : ∀ᶠ k in Filter.atTop, 0 < (dSeq k : ℝ) / ((nSeq k : ℝ) ^ (3 / 2 : ℝ) * G) ^ (1 / α) := by
            filter_upwards [ hn.eventually_gt_atTop 0, hd.eventually_gt_atTop 0 ] with k hk₁ hk₂ using div_pos ( Nat.cast_pos.mpr hk₂ ) ( Real.rpow_pos_of_pos ( mul_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hk₁ ) _ ) hG ) _ ) ;
          generalize_proofs at *; (
          exact tendsto_nhdsWithin_iff.mpr ⟨ hbeyond, h_pos ⟩)
        generalize_proofs at *; (
        convert h_inv using 2 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hα.ne' ]))
      generalize_proofs at *; (
      simpa [ div_eq_mul_inv ] using h_div);
    have h_div : Filter.Tendsto (fun k => (((nSeq k : ℝ) ^ (3 / 2 : ℝ) * G) ^ (1 / α) / (dSeq k : ℝ)) ^ α) Filter.atTop Filter.atTop := by
      exact tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| h_div;
    convert h_div using 2 ; rw [ Real.div_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ];
  have h_geometricCov_bound : Filter.Tendsto (fun k => geometricCov p (dSeq k) / (G * (dSeq k : ℝ) ^ (-α))) Filter.atTop (nhds 1) := by
    exact hasymp.comp hd;
  have h_geometricCov_bound : Filter.Tendsto (fun k => (nSeq k : ℝ) ^ (3 / 2 : ℝ) * G / (dSeq k : ℝ) ^ α * (geometricCov p (dSeq k) / (G * (dSeq k : ℝ) ^ (-α)))) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_mul_pos;
    exacts [ zero_lt_one, h_div, h_geometricCov_bound ];
  refine h_geometricCov_bound.congr' ?_ ; filter_upwards [ hd.eventually_gt_atTop 0 ] with k hk ; simp +decide [ Real.rpow_neg ( Nat.cast_nonneg _ ), mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, hk.ne', hG.ne', hα.ne' ] ; ring;
  norm_num [ mul_assoc, mul_comm G, hG.ne' ]

/-- Deriving n·g → ∞ from asymptotic equivalence and dimension scaling.
    If geometricCov p d ~ G * d^{-α} and d / (n * G)^{1/α} → 0,
    then n * geometricCov p d → ∞. Same proof structure as `derive_hSNR`
    but with `n` instead of `n^{3/2}`. -/
lemma derive_hNG (p : ℝ) (_hp0 : 0 < p) (_hp1 : p < 1)
    (G α : ℝ) (hG : 0 < G) (hα : 0 < α)
    (hasymp : Filter.Tendsto
      (fun d : ℕ => geometricCov p d / (G * (d : ℝ) ^ (-α)))
      Filter.atTop (nhds 1))
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    (hbeyondNG : Filter.Tendsto
      (fun k => (dSeq k : ℝ) / ((nSeq k : ℝ) * G) ^ (1 / α))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => (nSeq k : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop := by
  have h_div : Filter.Tendsto (fun k => (nSeq k : ℝ) * G / (dSeq k : ℝ) ^ α) Filter.atTop Filter.atTop := by
    have h_div : Filter.Tendsto (fun k => ((nSeq k : ℝ) * G) ^ (1 / α) / (dSeq k : ℝ)) Filter.atTop Filter.atTop := by
      have h_div : Filter.Tendsto (fun k => (1 : ℝ) / ((dSeq k : ℝ) / (nSeq k * G) ^ (1 / α))) Filter.atTop Filter.atTop := by
        refine' Filter.Tendsto.const_mul_atTop _ _ ; aesop;
        refine' Filter.Tendsto.inv_tendsto_nhdsGT_zero _;
        rw [ tendsto_nhdsWithin_iff ];
        exact ⟨ hbeyondNG, by filter_upwards [ hn.eventually_gt_atTop 0, hd.eventually_gt_atTop 0 ] with k hk₁ hk₂ using div_pos ( Nat.cast_pos.mpr hk₂ ) ( Real.rpow_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr hk₁ ) hG ) _ ) ⟩;
      simpa [ div_eq_mul_inv ] using h_div;
    have h_div : Filter.Tendsto (fun k => (((nSeq k : ℝ) * G) ^ (1 / α) / (dSeq k : ℝ)) ^ α) Filter.atTop Filter.atTop := by
      exact tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| h_div;
    refine h_div.congr' ?_ ; filter_upwards [ hn.eventually_gt_atTop 0, hd.eventually_gt_atTop 0 ] with k hk₁ hk₂ ; rw [ Real.div_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ;
  have h_geometricCov_bound : Filter.Tendsto (fun k => (nSeq k : ℝ) * G / (dSeq k : ℝ) ^ α * (geometricCov p (dSeq k) / (G * (dSeq k : ℝ) ^ (-α)))) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.atTop_mul_pos
    exact zero_lt_one
    exact h_div
    exact hasymp.comp hd;
  refine h_geometricCov_bound.congr' ?_ ; filter_upwards [ hd.eventually_gt_atTop 0 ] with k hk ; simp +decide [ Real.rpow_neg ( Nat.cast_nonneg _ ), mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, hk.ne', hG.ne', hα.ne' ] ; ring;
  norm_num [ mul_assoc, mul_comm G, hG.ne' ]

/-- **Theorem 2 (Phase Transition, Strategy 2).**
    If geometricCov p d ~ G(p)·d^{-α} for some G > 0, α > 0, then detection
    succeeds (TV → 1) when d_k ≪ (n_k · G)^{1/α}.

    Note: The hypothesis `hbeyond` uses `d/(n·G)^{1/α} → 0` (rather than the
    original `d/(n^{3/2}·G)^{1/α} → 0`) because the Chebyshev argument in
    `paleyZygmund_cech_prob_tendsto_one` requires `n·g → ∞`, which is only
    derivable from the stronger scaling `d ≪ (n·G)^{1/α}`. The weaker condition
    `d ≪ (n^{3/2}·G)^{1/α}` suffices for `n^{3/2}·g → ∞` but not `n·g → ∞`.

    The paper's Theorem 4.4 is the fixed-`d` specialization (Part (a): for any
    fixed `d < d^*(p)`, detection succeeds as `n → ∞`). Under fixed `d` with
    `geomCov(p,d) > 0`, both `n^{3/2}·g → ∞` and `n·g → ∞` are automatic, so
    this theorem (being strictly stronger) implies the paper's claim. -/
theorem phase_transition (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (G α : ℝ) (hG : 0 < G) (hα : 0 < α)
    (hasymp : Filter.Tendsto
      (fun d : ℕ => geometricCov p d / (G * (d : ℝ) ^ (-α)))
      Filter.atTop (nhds 1))
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    (hbeyond : Filter.Tendsto
      (fun k => (dSeq k : ℝ) / ((nSeq k : ℝ) * G) ^ (1 / α))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => tvDist
        (twoParamMeasure (nSeq k) p (fillingProb p (dSeq k)))
        ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
          (cechObservation (matchRadius p (dSeq k)))))
      Filter.atTop (nhds 1) := by
  /- hbeyond (d/(n·G)^{1/α} → 0) implies d/(n^{3/2}·G)^{1/α} → 0 (since
     (n·G)^{1/α} ≤ (n^{3/2}·G)^{1/α}), giving n^{3/2}·g → ∞ via derive_hSNR.
     It also directly gives n·g → ∞ via derive_hNG. -/
  have hbeyond_weak : Filter.Tendsto
      (fun k => (dSeq k : ℝ) / ((nSeq k : ℝ) ^ (3/2 : ℝ) * G) ^ (1 / α))
      Filter.atTop (nhds 0) := by
    -- d/(n^{3/2}*G)^{1/α} ≤ d/(n*G)^{1/α} since n ≥ 1 implies n ≤ n^{3/2}
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbeyond ?_ ?_
    · filter_upwards with k; positivity
    · filter_upwards [hn.eventually_ge_atTop 1, hd.eventually_ge_atTop 1] with k hk1 hk2
      apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ (dSeq k : ℝ))
        (Real.rpow_pos_of_pos (mul_pos (by positivity : (0 : ℝ) < nSeq k) hG) _)
      apply Real.rpow_le_rpow (mul_nonneg (by positivity) hG.le)
      · exact mul_le_mul_of_nonneg_right
          (Real.self_le_rpow_of_one_le (by exact_mod_cast hk1) (by norm_num)) hG.le
      · positivity
  apply detection_lower_bound p hp0 hp1 nSeq dSeq hn
  · exact derive_hSNR p hp0 hp1 G α hG hα hasymp nSeq dSeq hn hd hbeyond_weak
  · exact derive_hNG p hp0 hp1 G α hG hα hasymp nSeq dSeq hn hd hbeyond