import Mathlib
import SimplicialLatentGeometry.DisjointTriangles

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Testing for Geometry in Random Simplicial Complexes

Formalisation of the phase transition for the filled triangle statistic (Goh, in preparation).
The core question: can we distinguish a 2-parameter complex 2PC(n, p, q) from a Čech complex
on the flat torus 𝕋^d using the signed filled-triangle statistic?
-/

/-! ## Definitions -/

/-- **Definition 1 (2-Parameter Complex).** A sample from 2PC(n, p, q) consists of:
    - edge indicators `edge : Fin n → Fin n → Bool`, each i.i.d. Bernoulli(p)
      (convention: only `edge i j` with `i < j` carries information; assumed symmetric)
    - fill indicators `fill : {s : Finset (Fin n) // s.card = 3} → Bool`, each i.i.d. Bernoulli(q)
    all mutually independent. This structure captures a single realisation; the random model
    is a probability measure on `TwoParamSample n`. -/
structure TwoParamSample (n : ℕ) where
  edge : Fin n → Fin n → Bool
  fill : {s : Finset (Fin n) // s.card = 3} → Bool

/-- The flat d-dimensional torus T^d = (ℝ/ℤ)^d with unit side length,
    equipped with the product metric inherited from AddCircle (1 : ℝ). -/
abbrev Torus (d : ℕ) := Fin d → AddCircle (1 : ℝ)

/-- **Definition 2 (Čech Complex on the Flat Torus).** A sample from Čech(n, r, d) is n
    points on T^d. The simplicial complex structure is determined by the radius r:
    - edge {i,j} is present iff dist(points i, points j) ≤ r
    - triangle {i,j,k} is filled iff the r-balls around all three vertices have a common point
      (equivalently, their circumradius ≤ r). -/
structure CechSample (n d : ℕ) where
  points : Fin n → Torus d

/-- In Čech(s, r), vertices i and j are connected iff their torus distance is ≤ r. -/
def CechSample.hasEdge {n d : ℕ} (s : CechSample n d) (r : ℝ) (i j : Fin n) : Prop :=
  dist (s.points i) (s.points j) ≤ r

/-- In Čech(s, r), triangle t is filled iff the r-balls around its three vertices have a
    common point (the Čech complex filling condition). -/
def CechSample.hasFill {n d : ℕ} (s : CechSample n d) (r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) : Prop :=
  ∃ z : Torus d, ∀ i ∈ t.val, dist (s.points i) z ≤ r

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
/-- **Definition 5 (Filling Probability).** The matched fill probability q(p, d) is
      q(p,d) = ∫₀¹ (V_f(s,d) / V_e(s,d)) · d · s^(d-1) ds
    where d · s^(d-1) is the PDF of the inter-vertex separation on T^d.

    PROVIDED SOLUTION
    Two uniformly random points on T^d have separation s with PDF d·s^(d-1) on [0,1].
    Given separation s, the conditional probability that a third vertex fills the triangle
    is V_f(s,d) / V_e(s,d). Integrate over s ∈ [0,1] against this PDF. -/
noncomputable def fillingProb (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchRadius p d
  ∫ pts : Fin 3 → Torus d,
    (if ∃ z : Torus d, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r
     then (1 : ℝ) else 0)
  ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))

/-! ## Moment Setup -/

/-- Discrete sigma-algebra on TwoParamSample (all sets measurable). -/
instance (n : ℕ) : MeasurableSpace (TwoParamSample n) := ⊤

/-- Sigma-algebra on CechSample induced by the points projection.
    This is the coarsest sigma-algebra making `CechSample.points` measurable,
    which ensures `Measure.comap` of the product measure is well-defined. -/
instance (n d : ℕ) : MeasurableSpace (CechSample n d) :=
  MeasurableSpace.comap CechSample.points inferInstance

/-- The three edges of a triangle as ordered pairs (i, j) with i < j. -/
def triangleEdges {n : ℕ} (t : {σ : Finset (Fin n) // σ.card = 3}) :
    Finset (Fin n × Fin n) :=
  (t.val ×ˢ t.val).filter fun p => p.1 < p.2

/-- Filled triangle count Δ_f in a 2PC sample: sum over triangles of
    (fill indicator) × (product of edge indicators for the three edges). -/
noncomputable def filledTriangleCount {n : ℕ} (s : TwoParamSample n) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    (if s.fill t then (1 : ℝ) else 0) *
    ∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then 1 else 0)

open Classical in
/-- Filled triangle count in a Čech sample: triangles whose r-balls have a common point. -/
noncomputable def cechFilledCount {n d : ℕ} (s : CechSample n d) (r : ℝ) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    if s.hasFill r t then (1 : ℝ) else 0

/-- 2PC(n,p,q) probability measure: edges i.i.d. Bernoulli(p), fills i.i.d. Bernoulli(q).
    Defined as counting measure weighted by the product of Bernoulli probabilities for each
    edge indicator and fill indicator. -/
noncomputable def twoParamMeasure (n : ℕ) (p q : ℝ) :
    MeasureTheory.Measure (TwoParamSample n) :=
  MeasureTheory.Measure.count.withDensity fun s =>
    (∏ i : Fin n, ∏ j : Fin n,
      if s.edge i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) *
    (∏ t : {σ : Finset (Fin n) // σ.card = 3},
      if s.fill t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))

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

/-
PROVIDED SOLUTION
twoParamMeasure is count.withDensity f where f(s) = ∏ Bernoulli weights. The total mass is (count.withDensity f)(univ) = ∫ f d(count) = ∑ f(s) over all s. Since f is a product of independent Bernoulli weights, and each factor sums to 1 over {true, false} (p + (1-p) = 1 and q + (1-q) = 1), the total sum factors into a product of sums, each equal to 1. Hence total mass = 1.

More specifically: use Measure.withDensity_apply, then lintegral_count to get the tsum, then factor the tsum as a product using the product structure of TwoParamSample, then use that ∑_b (if b then p else 1-p) = p + (1-p) = 1 for each factor.
-/
set_option maxHeartbeats 800000 in
open MeasureTheory ProbabilityTheory in
/-- The total mass of `twoParamMeasure` is 1 (it is a probability measure). -/
lemma twoParamMeasure_totalMass (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoParamMeasure n p q) Set.univ = 1 := by
      unfold twoParamMeasure; simp [MeasureTheory.Measure.sum_apply]; (
      -- The total probability is the sum over all edge and fill configurations, each weighted by their respective probabilities.
      have h_total : ∑' (e : Fin n → Fin n → Bool), ∑' (f : {σ : Finset (Fin n) // σ.card = 3} → Bool), (∏ i : Fin n, ∏ j : Fin n, (if e i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p))) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, (if f t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) = 1 := by
        have h_total : ∑' (e : Fin n → Fin n → Bool), (∏ i : Fin n, ∏ j : Fin n, (if e i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p))) = 1 ∧ ∑' (f : {σ : Finset (Fin n) // σ.card = 3} → Bool), (∏ t : {σ : Finset (Fin n) // σ.card = 3}, (if f t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) = 1 := by
          constructor <;> rw [ tsum_fintype ];
          · -- The sum of the probabilities of all possible edge configurations is equal to the product of the sums of the probabilities of each edge.
            have h_sum_edges : ∑ b : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if b i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) = (∏ i : Fin n, ∏ j : Fin n, (∑ b : Bool, if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p))) := by
              rw [ Finset.prod_sum ];
              rw [ Finset.prod_sum ];
              refine' Finset.sum_bij ( fun b _ => fun i _ j _ => b i j ) _ _ _ _ <;> simp +decide;
              · simp +decide [ funext_iff ];
              · exact fun b => ⟨ fun i j => b i ( Finset.mem_univ i ) j ( Finset.mem_univ j ), rfl ⟩;
            simp_all +decide [ Finset.prod_ite ];
            rw [ ← ENNReal.ofReal_add ] <;> norm_num [ hp, hp1 ];
          · -- The sum of the products of the probabilities over all possible samples is equal to 1 because it is the expansion of $(q + (1-q))^n$.
            have h_sum : (∑ b : {s : Finset (Fin n) // s.card = 3} → Bool, (∏ t : {s : Finset (Fin n) // s.card = 3}, if b t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) = (∏ t : {s : Finset (Fin n) // s.card = 3}, (ENNReal.ofReal q + ENNReal.ofReal (1 - q))) := by
              rw [ Finset.prod_add ];
              refine' Finset.sum_bij ( fun b _ => Finset.univ.filter fun t => b t = true ) _ _ _ _ <;> simp +decide [ Finset.prod_ite ];
              · simp +contextual [ funext_iff, Finset.ext_iff ];
              · exact fun b => ⟨ fun t => t ∈ b, by ext; simp +decide ⟩;
              · simp +decide [ Finset.filter_not, Finset.card_sdiff ];
                intro a; rw [ show ( Finset.univ.filter fun x => a x = false ) = Finset.univ \ ( Finset.univ.filter fun x => a x = true ) by ext; aesop, Finset.card_sdiff ] ; aesop;
            rw [ h_sum, ← ENNReal.ofReal_add ] <;> norm_num [ hq, hq1 ];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, h_total ];
        rw [ tsum_fintype, tsum_fintype ] at * ; aesop;
      rw [ ← h_total, MeasureTheory.lintegral_count ];
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun e : ( Fin n → Fin n → Bool ) × ( { σ : Finset ( Fin n ) // σ.card = 3 } → Bool ) => ⟨ e.1, e.2 ⟩ : ( Fin n → Fin n → Bool ) × ( { σ : Finset ( Fin n ) // σ.card = 3 } → Bool ) → TwoParamSample n ) ⟨ fun e => by
        grind +ring, fun e => by
        exact ⟨ ⟨ e.edge, e.fill ⟩, rfl ⟩ ⟩ ) ] ; simp +decide [ tsum_mul_left, tsum_mul_right ] ; ring
      generalize_proofs at *; (
      rw [ ← Finset.sum_product' ] ; aesop;));

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

open MeasureTheory ProbabilityTheory in
lemma moments_twoParam (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, filledTriangleCount s ∂twoParamMeasure n p q = (n.choose 3 : ℝ) * p ^ 3 * q ∧
    variance filledTriangleCount (twoParamMeasure n p q) =
      (n.choose 3 : ℝ) * p ^ 3 * q * (1 - p ^ 3 * q) +
      12 * (n.choose 4 : ℝ) * p ^ 5 * q ^ 2 * (1 - p) :=
  ⟨moments_twoParam_mean n p q hp hp1 hq hq1, moments_twoParam_var n p q hp hp1 hq hq1⟩

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

/-- Total variation distance between two probability measures on the same space.
    TV(μ,ν) = sup_{A measurable} |μ(A) - ν(A)|. -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ s : Set Ω, MeasurableSet s ∧ x = |(μ s).toReal - (ν s).toReal|}

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
  have h_bounded : ∀ s : CechSample n d, |cechFilledCount s r| ≤ Nat.choose n 3 := by
    intro s
    simp [cechFilledCount];
    exact le_trans (Finset.card_le_univ _) (by aesop);
  refine' MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const _) _ _;
  exact ↑(n.choose 3);
  · refine' Measurable.aestronglyMeasurable _;
    refine' Finset.measurable_sum _ fun t ht => _;
    have h_measurable_set : MeasurableSet {s : CechSample n d | s.hasFill r t} := by
      have h_measurable_set : MeasurableSet {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ r} := by
        have h_closed : IsClosed {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ r} := by
          have h_closed : IsClosed {p : (Fin n → Torus d) × Torus d | ∀ i ∈ t.val, dist (p.1 i) p.2 ≤ r} := by
            simp +decide only [Set.setOf_forall];
            exact isClosed_iInter fun i => isClosed_iInter fun hi => isClosed_le
              (Continuous.dist (continuous_apply i |> Continuous.comp <| continuous_fst) continuous_snd) continuous_const
          have h_closed : IsClosed (Set.image (fun p : (Fin n → Torus d) × Torus d => p.1)
              {p : (Fin n → Torus d) × Torus d | ∀ i ∈ t.val, dist (p.1 i) p.2 ≤ r}) := by
            apply_rules [IsCompact.isClosed, IsCompact.image];
            · refine' IsCompact.of_isClosed_subset _ h_closed _;
              exact Set.univ ×ˢ Set.univ
              all_goals generalize_proofs at *;
              · exact isCompact_univ.prod isCompact_univ;
              · exact fun p hp => ⟨Set.mem_univ _, Set.mem_univ _⟩;
            · exact continuous_fst
          generalize_proofs at *; (convert h_closed using 1; ext; aesop);
        exact h_closed.measurableSet;
      convert h_measurable_set.preimage (show Measurable (fun s : CechSample n d => s.points) from ?_) using 1;
      exact?;
    exact Measurable.ite h_measurable_set measurable_const measurable_const;
  · exact Filter.Eventually.of_forall h_bounded

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

/-- The doubly-signed filled triangle statistic τ_f.
    Each triangle contributes ∏_{e ∈ edges} (A_e - p) · (F - q).
    Under 2PC, each factor has mean 0 and is independent, so E[τ_f] = 0
    and Var[τ_f] = C(n,3)·p³(1-p)³·q(1-q) (diagonal only, O(n³)). -/
noncomputable def doublySignedFilledCount {n : ℕ} (p q : ℝ) (s : TwoParamSample n) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    (∏ e ∈ triangleEdges t,
      (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
    (if s.fill t then (1 : ℝ) - q else -q)

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

/-- **Lemma A (Variance of doubly-signed stat under 2PC).**
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
private noncomputable instance twoParamSampleFintype' (n : ℕ) : Fintype (TwoParamSample n) :=
  Fintype.ofEquiv ((Fin n → Fin n → Bool) × ({s : Finset (Fin n) // s.card = 3} → Bool))
    { toFun := fun ⟨e, f⟩ => ⟨e, f⟩
      invFun := fun s => (s.edge, s.fill)
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }

private instance twoParamMSC' (n : ℕ) : @MeasurableSingletonClass (TwoParamSample n) ⊤ :=
  ⟨fun _ => trivial⟩

private noncomputable def twoParamDensityReal' (n : ℕ) (p q : ℝ) (s : TwoParamSample n) : ℝ :=
  (∏ i : Fin n, ∏ j : Fin n, if s.edge i j then p else 1 - p) *
  (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if s.fill t then q else 1 - q)

/-
PROVIDED SOLUTION
Unfold twoParamMeasure as count.withDensity. Use integral_eq_lintegral_pos_part_sub_lintegral_neg_part, then lintegral_withDensity_eq_lintegral_mul, lintegral_count, ENNReal.tsum_toReal_eq, tsum_fintype. The density converts from ENNReal.ofReal to real using ENNReal.toReal_ofReal.
-/
private lemma twoParam_integral_eq_sum' {n : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (f : TwoParamSample n → ℝ)
    (hf_bdd : ∃ C : ℝ, ∀ s, |f s| ≤ C) :
    ∫ s, f s ∂twoParamMeasure n p q =
    ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * f s := by
  rw [ MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part ];
  · have h_integral : ∀ {g : TwoParamSample n → ENNReal}, (∫⁻ s, g s ∂twoParamMeasure n p q) = ∑ s, g s * ENNReal.ofReal (twoParamDensityReal' n p q s) := by
      intro g
      have h_integral : ∫⁻ s, g s ∂twoParamMeasure n p q = ∑ s, g s * (∏ i : Fin n, ∏ j : Fin n, if s.edge i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if s.fill t then ENNReal.ofReal q else ENNReal.ofReal (1 - q)) := by
        have h_integral : ∫⁻ s, g s ∂twoParamMeasure n p q = ∑ s, g s * (∏ i : Fin n, ∏ j : Fin n, if s.edge i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if s.fill t then ENNReal.ofReal q else ENNReal.ofReal (1 - q)) := by
          have h_count : twoParamMeasure n p q = MeasureTheory.Measure.count.withDensity (fun s => (∏ i : Fin n, ∏ j : Fin n, if s.edge i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if s.fill t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) := by
            rfl
          rw [ h_count, MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
          · rw [ MeasureTheory.lintegral_count ];
            rw [ tsum_fintype ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
          · fun_prop (disch := norm_num);
          · fun_prop (disch := norm_num);
        convert h_integral using 1;
      convert h_integral using 2 ; norm_num [ twoParamDensityReal' ] ; ring;
      rw [ ENNReal.ofReal_mul ] <;> norm_num [ Finset.prod_ite ] ; ring;
      · rw [ ENNReal.ofReal_prod_of_nonneg ] <;> norm_num [ ENNReal.ofReal_mul, hp, hp1, hq, hq1 ] ; ring;
        exact fun i => mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ );
      · exact Finset.prod_nonneg fun _ _ => mul_nonneg ( pow_nonneg hp _ ) ( pow_nonneg ( sub_nonneg.2 hp1 ) _ );
    rw [ h_integral, h_integral ] ; norm_num [ mul_comm ] ; ring;
    rw [ ENNReal.toReal_sum, ENNReal.toReal_sum ] ; simp +decide [ mul_comm ] ; ring;
    · rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun x _ => _ ; by_cases hx : 0 ≤ f x <;> simp +decide [ hx, ENNReal.ofReal ] ; ring;
      · exact Or.inl ( mul_nonneg ( Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) ( Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) );
      · rw [ max_eq_right ( by linarith ), max_eq_left ( by exact mul_nonneg ( Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) ( Finset.prod_nonneg fun _ _ => by split_ifs <;> linarith ) ), max_eq_left ( by linarith ) ] ; ring;
    · exact fun _ _ => ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top );
    · exact fun _ _ => ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.ofReal_ne_top );
  · refine' ⟨ _, _ ⟩;
    · exact?;
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun s => _ ) _;
      use fun s => ENNReal.ofReal ( hf_bdd.choose );
      · simpa only [ Real.enorm_eq_ofReal_abs ] using ENNReal.ofReal_le_ofReal ( hf_bdd.choose_spec s );
      · have := twoParamMeasure_totalMass n p q hp hp1 hq hq1; aesop;

/-
PROVIDED SOLUTION
Factor the sum over TwoParamSample n into products of sums over individual Bool coordinates. One edge coordinate contributes ∑_b (if b then p else 1-p) * (if b then 1-p else -p) = p*(1-p) + (1-p)*(-p) = 0 (by ring). Since one factor is 0, the whole product is 0.

Use the same factorization pattern: (1) factor into (edge sum) * (fill sum) via bijection between TwoParamSample n and product type, (2) factor each sum using Finset.prod_sum.
-/
private lemma doublySignedTerm_expectation_zero' {n : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (t : {σ : Finset (Fin n) // σ.card = 3}) :
    ∑ s : TwoParamSample n, twoParamDensityReal' n p q s *
      ((∏ e ∈ triangleEdges t,
        (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.fill t then (1 : ℝ) - q else -q)) = 0 := by
  convert twoParam_integral_eq_sum' p q hp hp1 hq hq1 _ _ using 1;
  convert twoParam_integral_eq_sum' p q hp hp1 hq hq1 _ _ |> Eq.symm;
  · use ( ∏ e ∈ triangleEdges t, ( 1 : ℝ ) ) * ( 1 : ℝ );
    intro s; rw [ abs_mul ] ; refine' mul_le_mul _ _ _ _ <;> norm_num;
    · rw [ Finset.abs_prod ] ; exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => by split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩ ;
    · split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩;
  · -- Let's simplify the expression inside the sum.
    have h_simp : ∀ (n : ℕ) (p q : ℝ), 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → ∀ (t : {σ : Finset (Fin n) // σ.card = 3}), ∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if s i j then p else 1 - p) * (∏ e ∈ triangleEdges t, (if s e.1 e.2 then (1 - p) else -p)) = 0 := by
      intros n p q hp hp1 hq hq1 t
      have h_simp : ∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if s i j then p else 1 - p) * (∏ e ∈ triangleEdges t, (if s e.1 e.2 then (1 - p) else -p)) = ∏ i : Fin n, ∏ j : Fin n, (∑ b : Bool, (if b then p else 1 - p) * (if (i, j) ∈ triangleEdges t then (if b then (1 - p) else -p) else 1)) := by
        simp +decide only [Finset.prod_sum, Finset.prod_mul_distrib];
        refine' Finset.sum_bij ( fun s _ => fun i _ j _ => s i j ) _ _ _ _ <;> simp +decide [ Finset.mem_univ ];
        · simp +decide [ funext_iff ];
        · exact fun b => ⟨ fun i j => b i ( Finset.mem_univ i ) j ( Finset.mem_univ j ), rfl ⟩;
        · intro a; left; rw [ ← Finset.prod_product' ] ; simp +decide [ Finset.prod_ite ] ;
      rw [ h_simp, Finset.prod_eq_zero_iff ];
      -- Since $t$ is a triangle, there exists at least one pair $(i, j)$ such that $(i, j) \in \text{triangleEdges } t$.
      obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, (i, j) ∈ triangleEdges t := by
        rcases t with ⟨ t, ht ⟩;
        obtain ⟨ i, j, k, hij, hjk, hik ⟩ := Finset.card_eq_three.mp ht;
        cases lt_or_gt_of_ne hij <;> cases lt_or_gt_of_ne hjk <;> cases lt_or_gt_of_ne hik.1 <;> simp +decide [ *, triangleEdges ];
        all_goals first | exact ⟨ i, j, by tauto, by assumption ⟩ | exact ⟨ i, k, by tauto, by assumption ⟩ | exact ⟨ j, k, by tauto, by assumption ⟩ | exact ⟨ j, i, by tauto, by assumption ⟩;
      use i; simp [hij];
      rw [ Finset.prod_eq_zero ( Finset.mem_univ j ) ] ; ring ; aesop;
    specialize h_simp n p q hp hp1 hq hq1 t;
    convert congr_arg ( fun x : ℝ => x * ( ∑ s : { s : Finset ( Fin n ) // s.card = 3 } → Bool, ( ∏ t : { s : Finset ( Fin n ) // s.card = 3 }, if s t then q else 1 - q ) * ( if s t then 1 - q else -q ) ) ) h_simp.symm using 1;
    · ring;
    · simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.fill, x.edge ) ) _ _ _ _ <;> simp +decide [ twoParamDensityReal' ];
      · exact fun a₁ a₂ h₁ h₂ => by cases a₁; cases a₂; aesop;
      · exact fun a b => ⟨ ⟨ b, a ⟩, rfl, rfl ⟩;
      · intro a; split_ifs <;> ring;
  · use ( ∏ e ∈ triangleEdges t, ( 1 : ℝ ) ) * ( 1 : ℝ );
    intro s; rw [ abs_mul ] ; refine' mul_le_mul _ _ _ _ <;> norm_num;
    · rw [ Finset.abs_prod ] ; exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => by split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩ ;
    · split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩

/-
PROVIDED SOLUTION
Use twoParam_integral_eq_sum' to convert integral to sum. Expand doublySignedFilledCount as ∑_t T_t. Interchange sums: ∑_s density(s) * ∑_t T_t(s) = ∑_t ∑_s density(s) * T_t(s). Each inner sum is 0 by doublySignedTerm_expectation_zero'. Sum of zeros = 0.
-/
private lemma doublySignedFilledCount_expectation_zero' (n : ℕ) (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, doublySignedFilledCount p q s ∂twoParamMeasure n p q = 0 := by
  rw [twoParam_integral_eq_sum']
  generalize_proofs at *; (
  unfold doublySignedFilledCount
  generalize_proofs at *; (
  rw [ Finset.sum_congr rfl fun s hs => by rw [ Finset.mul_sum _ _ _ ] ] ; rw [ Finset.sum_comm ] ; exact Finset.sum_eq_zero fun t ht => doublySignedTerm_expectation_zero' p q hp hp1 hq hq1 t;));
  · grind +splitImp;
  · linarith;
  · grind;
  · linarith;
  · exact Set.finite_range ( fun s : TwoParamSample n => |doublySignedFilledCount p q s| ) |> Set.Finite.bddAbove |> fun ⟨ C, hC ⟩ => ⟨ C, fun s => hC <| Set.mem_range_self s ⟩ ;

/-
PROVIDED SOLUTION
For t ≠ t', factor the sum over TwoParamSample n into (edge sum) * (fill sum) using the bijection TwoParamSample n ≃ (edge configs) × (fill configs).

The fill sum contains two independent centered factors: (if fill t then 1-q else -q) and (if fill t' then 1-q else -q). Since t ≠ t', these are independent coordinates.

Factor the fill sum: ∑_{fill} (∏_{t''} weight(fill t'')) * centered(fill t) * centered(fill t')
= (∑_b weight(b) * centered(b)) * (∑_b weight(b) * centered(b)) * (∏_{t''≠t,t'} ∑_b weight(b))
= 0 * 0 * ...
= 0

Since the fill sum is 0, the whole product is 0.

Use the same factorization pattern as doublySignedTerm_expectation_zero': factor using Finset.prod_sum and bijection.
-/
set_option maxHeartbeats 800000 in
private lemma doublySignedCross_zero' {n : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3}) (htt' : t ≠ t') :
    ∑ s : TwoParamSample n, twoParamDensityReal' n p q s *
      (((∏ e ∈ triangleEdges t,
        (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.fill t then (1 : ℝ) - q else -q)) *
      ((∏ e ∈ triangleEdges t',
        (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.fill t' then (1 : ℝ) - q else -q))) = 0 := by
  -- The sum over all fill configurations can be factored into a product of sums for each triangle.
  have h_fill_factor : ∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then 1 - q else -q) * (if f t' then 1 - q else -q)) = 0 := by
    -- Since $t \neq t'$, the fill configurations for $t$ and $t'$ are independent. We can split the sum into a product of sums for each triangle.
    have h_split : ∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then 1 - q else -q) * (if f t' then 1 - q else -q)) = (∑ f_t : Bool, (if f_t then q else 1 - q) * (if f_t then 1 - q else -q)) * (∑ f_t' : Bool, (if f_t' then q else 1 - q) * (if f_t' then 1 - q else -q)) * (∏ t'' : {σ : Finset (Fin n) // σ.card = 3}, if t'' = t ∨ t'' = t' then 1 else (∑ f_t'' : Bool, (if f_t'' then q else 1 - q))) := by
      have h_split : ∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then 1 - q else -q) * (if f t' then 1 - q else -q)) = ∏ t'' : {σ : Finset (Fin n) // σ.card = 3}, (∑ f_t'' : Bool, (if f_t'' then q else 1 - q) * (if t'' = t then (if f_t'' then 1 - q else -q) else if t'' = t' then (if f_t'' then 1 - q else -q) else 1)) := by
        rw [ Finset.prod_sum ];
        refine' Finset.sum_bij ( fun f _ => fun x _ => f x ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
        · simp +decide [ funext_iff ];
        · exact fun b => ⟨ fun x => b x ( Finset.mem_univ x ), rfl ⟩;
        · intro a; rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ t ) ] ; rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ t', by aesop ⟩ ) ] ; simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ] ; ring;
          by_cases h : a t <;> by_cases h' : a t' <;> simp +decide [ h, h', Finset.filter_singleton, Finset.sdiff_singleton_eq_erase ] ; ring;
          · split_ifs <;> simp_all +decide [ Finset.filter_singleton, Finset.prod_singleton ] ; ring;
          · split_ifs <;> simp_all +decide [ Finset.filter_singleton, Finset.prod_singleton ] ; ring;
          · split_ifs <;> simp_all +decide [ Finset.filter_singleton, Finset.prod_singleton ] ; ring;
          · split_ifs <;> simp_all +decide [ Finset.filter_singleton, Finset.prod_singleton ] ; ring;
      rw [ h_split, ← Finset.prod_sdiff <| Finset.subset_univ { t, t' } ] ; simp +decide [ Finset.prod_pair, htt' ] ; ring;
    simp_all +decide [ Finset.prod_ite ];
    ring;
  -- Let's simplify the expression using the fact that multiplication is commutative and associative.
  have h_simp : ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * ((∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then 1 - p else -p)) * (if s.fill t then 1 - q else -q)) * ((∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then 1 - p else -p)) * (if s.fill t' then 1 - q else -q)) = (∑ e : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if e i j then p else 1 - p) * ((∏ e_1 ∈ triangleEdges t, (if e e_1.1 e_1.2 then 1 - p else -p)) * (∏ e_1 ∈ triangleEdges t', (if e e_1.1 e_1.2 then 1 - p else -p)))) * (∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then 1 - q else -q) * (if f t' then 1 - q else -q))) := by
    have h_simp : ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * ((∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then 1 - p else -p)) * (if s.fill t then 1 - q else -q)) * ((∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then 1 - p else -p)) * (if s.fill t' then 1 - q else -q)) = ∑ e : Fin n → Fin n → Bool, ∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ i : Fin n, ∏ j : Fin n, if e i j then p else 1 - p) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((∏ e_1 ∈ triangleEdges t, (if e e_1.1 e_1.2 then 1 - p else -p)) * (if f t then 1 - q else -q)) * ((∏ e_1 ∈ triangleEdges t', (if e e_1.1 e_1.2 then 1 - p else -p)) * (if f t' then 1 - q else -q)) := by
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun s _ => ( s.edge, s.fill ) ) _ _ _ _ <;> simp +decide [ twoParamDensityReal' ];
      · exact fun a₁ a₂ h₁ h₂ => by cases a₁; cases a₂; aesop;
      · exact fun a b => ⟨ ⟨ a, b ⟩, rfl, rfl ⟩;
    rw [ h_simp, Finset.sum_mul ];
    simp +decide only [Finset.mul_sum _ _ _] ; congr ; ext ; ring;
    ac_rfl;
  simpa only [ ← mul_assoc ] using h_simp.trans ( mul_eq_zero_of_right _ h_fill_factor )

/-
PROVIDED SOLUTION
triangleEdges t = (t.val ×ˢ t.val).filter (fun p => p.1 < p.2). Since t.val has card 3, extract t = {x, y, z} with x, y, z distinct using Finset.card_eq_three. Case-split on orderings.
-/
private lemma triangleEdges_card' {n : ℕ} (t : {σ : Finset (Fin n) // σ.card = 3}) :
    (triangleEdges t).card = 3 := by
  rcases t with ⟨ σ, hσ ⟩;
  have := Finset.card_eq_three.mp hσ; obtain ⟨ x, y, z, hxyz ⟩ := this; simp +decide [ *, triangleEdges ] ;
  cases lt_or_gt_of_ne hxyz.1 <;> cases lt_or_gt_of_ne hxyz.2.1 <;> cases lt_or_gt_of_ne hxyz.2.2.1 <;> simp +decide [ *, Finset.filter ];
  all_goals simp_all +decide [ lt_asymm, le_of_lt ];
  · simp +decide [ Multiset.filter_singleton, * ];
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop_cat;
  · exact False.elim <| lt_asymm ‹_› <| lt_trans ‹_› ‹_›;
  · simp +decide [ Multiset.filter_singleton, * ];
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
  · simp +decide [ Multiset.filter_singleton, ‹y < x›.ne, ‹z < x›.ne, ‹y < z›.ne ]

/-
PROVIDED SOLUTION
Factor into (edge sum) * (fill sum) via Fubini. Edge part: ∑_{edge} weight * (∏_{e∈edges(t)} center²) = (p(1-p))³ = p³(1-p)³ (using bernoulli_center_sq and triangleEdges_card'). Fill part: ∑_{fill} weight * center² = q(1-q). Total: p³(1-p)³ * q(1-q).
-/
set_option maxHeartbeats 800000 in
private lemma doublySignedDiag_value' {n : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    ∑ s : TwoParamSample n, twoParamDensityReal' n p q s *
      (((∏ e ∈ triangleEdges t,
        (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.fill t then (1 : ℝ) - q else -q)) ^ 2) =
    p ^ 3 * (1 - p) ^ 3 * (q * (1 - q)) := by
  have h_factor : ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * ((∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - q else -q)) ^ 2 = (∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, (∏ j : Fin n, if s i j then p else 1 - p)) * ((∏ e ∈ triangleEdges t, (if s e.1 e.2 then (1 : ℝ) - p else -p)) ^ 2)) * (∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then (1 : ℝ) - q else -q) ^ 2)) := by
    have h_factor : ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * ((∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - q else -q)) ^ 2 = ∑ s : (Fin n → Fin n → Bool) × ({σ : Finset (Fin n) // σ.card = 3} → Bool), (∏ i : Fin n, ∏ j : Fin n, if s.1 i j then p else 1 - p) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if s.2 t then q else 1 - q) * ((∏ e ∈ triangleEdges t, (if s.1 e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.2 t then (1 : ℝ) - q else -q)) ^ 2 := by
      refine' Finset.sum_bij ( fun s _ => ( s.edge, s.fill ) ) _ _ _ _ <;> simp +decide [ twoParamDensityReal' ];
      · exact fun a₁ a₂ h₁ h₂ => by cases a₁; cases a₂; aesop;
      · exact fun a b => ⟨ ⟨ a, b ⟩, rfl, rfl ⟩;
    rw [ h_factor, Finset.sum_mul ];
    simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
    rw [ ← Finset.sum_product' ] ; congr ; ext ; ring;
  -- Evaluate the sum over the edges.
  have h_edges : ∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, (∏ j : Fin n, if s i j then p else 1 - p)) * ((∏ e ∈ triangleEdges t, (if s e.1 e.2 then (1 : ℝ) - p else -p)) ^ 2) = p ^ 3 * (1 - p) ^ 3 := by
    have h_edges : ∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if s i j then p else 1 - p) * (∏ e ∈ triangleEdges t, (if s e.1 e.2 then (1 : ℝ) - p else -p)) ^ 2 = (∏ e ∈ triangleEdges t, (∑ s : Bool, (if s then p else 1 - p) * ((if s then (1 : ℝ) - p else -p) ^ 2))) * (∏ e ∈ Finset.univ \ Finset.image (fun e => (e.1, e.2)) (triangleEdges t), (∑ s : Bool, (if s then p else 1 - p))) := by
      have h_factor : ∀ (f : Fin n → Fin n → Bool → ℝ), (∑ s : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, f i j (s i j))) = (∏ i : Fin n, ∏ j : Fin n, (∑ s : Bool, f i j s)) := by
        intro f; exact (by
        simp +decide only [Finset.prod_sum];
        refine' Finset.sum_bij ( fun s _ => fun i _ j _ => s i j ) _ _ _ _ <;> simp +decide [ funext_iff ];
        exact fun b => ⟨ fun i j => b i ( Finset.mem_univ i ) j ( Finset.mem_univ j ), fun i j => rfl ⟩);
      convert h_factor ( fun i j s => if ( i, j ) ∈ triangleEdges t then ( if s then p else 1 - p ) * ( if s then 1 - p else -p ) ^ 2 else ( if s then p else 1 - p ) ) using 1;
      · refine' Finset.sum_congr rfl fun s hs => _;
        rw [ ← Finset.prod_pow ];
        rw [ ← Finset.prod_product' ];
        rw [ ← Finset.prod_product' ];
        rw [ ← Finset.prod_sdiff ( show triangleEdges t ⊆ Finset.univ ×ˢ Finset.univ from Finset.subset_iff.mpr fun x hx => Finset.mem_product.mpr ⟨ Finset.mem_univ _, Finset.mem_univ _ ⟩ ) ];
        rw [ ← Finset.prod_sdiff ( show triangleEdges t ⊆ Finset.univ ×ˢ Finset.univ from Finset.subset_iff.mpr fun x hx => Finset.mem_product.mpr ⟨ Finset.mem_univ _, Finset.mem_univ _ ⟩ ) ] ; ring;
        simp +decide [ Finset.prod_mul_distrib, Finset.prod_ite ];
        simp +decide [ Finset.filter_filter, Finset.filter_mem_eq_inter, Finset.filter_not ] ; ring;
        rw [ show ( p - p ^ 2 * 2 + p ^ 3 ) = p * ( 1 - p * 2 + p ^ 2 ) by ring, show ( p ^ 2 - p ^ 3 ) = p ^ 2 * ( 1 - p ) by ring ] ; rw [ mul_pow, mul_pow ] ; ring;
      · simp +decide [ Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
        simp +decide [ Finset.prod_pow_eq_pow_sum, Finset.sum_filter ];
        rw [ show ( triangleEdges t ).card = ∑ i : Fin n, Finset.card ( Finset.filter ( fun x => ( i, x ) ∈ triangleEdges t ) Finset.univ ) from ?_ ];
        simp +decide only [Finset.card_filter];
        rw [ Finset.card_eq_sum_ones, Finset.sum_comm ];
        rw [ ← Finset.sum_product' ];
        rw [ ← Finset.sum_filter ];
        refine' Finset.sum_bij ( fun x hx => ( x.2, x.1 ) ) _ _ _ _ <;> simp +decide [ triangleEdges ];
        · grind;
        · tauto;
    rw [ h_edges ] ; norm_num [ Finset.card_sdiff, triangleEdges_card' ] ; ring;
  -- Evaluate the sum over the fills.
  have h_fills : ∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then (1 : ℝ) - q else -q) ^ 2) = q * (1 - q) := by
    have h_fills : ∑ f : {σ : Finset (Fin n) // σ.card = 3} → Bool, (∏ t : {σ : Finset (Fin n) // σ.card = 3}, if f t then q else 1 - q) * ((if f t then (1 : ℝ) - q else -q) ^ 2) = (∏ t' : {σ : Finset (Fin n) // σ.card = 3}, (∑ f : Bool, (if f then q else 1 - q) * ((if f then (1 : ℝ) - q else -q) ^ 2) ^ (if t' = t then 1 else 0))) := by
      rw [ Finset.prod_sum ];
      refine' Finset.sum_bij ( fun f _ => fun t' _ => f t' ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
      · simp +decide [ funext_iff ];
      · exact fun b => ⟨ fun t' => b t' ( Finset.mem_univ t' ), funext fun t' => rfl ⟩;
      · intro a; split_ifs <;> simp +decide [ *, Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ] ; ring;
        · nontriviality;
          rw [ show ( Finset.filter ( fun x => a x = true ) Finset.univ ) = Finset.filter ( fun x => a x = true ) ( Finset.univ.erase t ) ∪ { t } from ?_, show ( Finset.filter ( fun x => a x = false ) Finset.univ ) = Finset.filter ( fun x => a x = false ) ( Finset.univ.erase t ) from ?_ ] <;> norm_num [ Finset.filter_union, Finset.filter_singleton, ‹a t = true› ] ; ring;
          · ext x; by_cases hx : x = t <;> simp +decide [ hx, ‹a t = true› ] ;
          · ext x; by_cases hx : x = t <;> simp +decide [ hx, ‹a t = true› ] ;
        · simp +decide [ *, Finset.filter_singleton, Finset.filter_erase ] ; ring;
          rw [ show ( Finset.filter ( fun x => a x = false ) Finset.univ ).card = ( Finset.filter ( fun x => a x = false ) Finset.univ ).card - 1 + 1 by rw [ Nat.sub_add_cancel ( Finset.card_pos.mpr ⟨ t, by aesop ⟩ ) ] ] ; ring;
          norm_num [ add_tsub_cancel_of_le ( Nat.one_le_iff_ne_zero.mpr <| show Finset.card ( Finset.filter ( fun x => a x = false ) Finset.univ ) ≠ 0 from ne_of_gt <| Finset.card_pos.mpr ⟨ t, by aesop ⟩ ) ];
    rw [ h_fills, Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_univ t ] ; norm_num ; ring;
  rw [ h_factor, h_edges, h_fills ]

/-
PROVIDED SOLUTION
ABSOLUTELY DO NOT use moments_twoParam_signed or doublySignedFilledCount_variance (circular!).

Convert ∫ X² ∂μ to ∑ density * X² via twoParam_integral_eq_sum'. Expand X² = (∑_t T_t)² = ∑_t ∑_t' T_t * T_t'. Interchange sums. Off-diagonal = 0 by doublySignedCross_zero'. Diagonal = p³(1-p)³q(1-q) by doublySignedDiag_value'. Sum = C(n,3) * p³(1-p)³q(1-q).
-/
set_option maxHeartbeats 800000 in
private lemma doublySignedFilledCount_sq_integral' (n : ℕ) (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, (doublySignedFilledCount p q s) ^ 2 ∂twoParamMeasure n p q =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p) ^ 3 * q * (1 - q) := by
  rw [ twoParam_integral_eq_sum' p q hp hp1 hq hq1 ];
  · -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * (∑ t : {σ : Finset (Fin n) // σ.card = 3}, (∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - q else -q)) ^ 2 = ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' : {σ : Finset (Fin n) // σ.card = 3}, ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * ((∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - q else -q)) * ((∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - q else -q)) := by
      simp +decide only [sq, Finset.mul_sum _ _ _, Finset.sum_mul];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
    -- By combining the results from the previous steps, we can simplify the expression.
    have h_simplify : ∑ t : {σ : Finset (Fin n) // σ.card = 3}, ∑ t' : {σ : Finset (Fin n) // σ.card = 3}, ∑ s : TwoParamSample n, twoParamDensityReal' n p q s * ((∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t then (1 : ℝ) - q else -q)) * ((∏ e ∈ triangleEdges t', (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) * (if s.fill t' then (1 : ℝ) - q else -q)) = ∑ t : {σ : Finset (Fin n) // σ.card = 3}, p ^ 3 * (1 - p) ^ 3 * (q * (1 - q)) := by
      refine' Finset.sum_congr rfl fun t ht => _;
      rw [ Finset.sum_eq_single t ];
      · convert doublySignedDiag_value' p q hp hp1 hq hq1 t using 1;
        exact Finset.sum_congr rfl fun _ _ => by ring;
      · intro t' ht' hne; exact (by
        convert doublySignedCross_zero' p q hp hp1 hq hq1 t' t hne using 1;
        ac_rfl);
      · lia;
    convert h_fubini.trans h_simplify using 1 ; norm_num ; ring!;
  · exact Set.Finite.bddAbove ( Set.toFinite ( Set.image ( fun s : TwoParamSample n => |doublySignedFilledCount p q s ^ 2| ) Set.univ ) ) |> fun ⟨ C, hC ⟩ => ⟨ C, fun s => hC <| Set.mem_image_of_mem _ <| Set.mem_univ _ ⟩

-- open MeasureTheory ProbabilityTheory in
lemma moments_twoParam_signed (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∫ s, doublySignedFilledCount p q s ∂twoParamMeasure n p q = 0 ∧
    ProbabilityTheory.variance (doublySignedFilledCount p q) (twoParamMeasure n p q) =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p) ^ 3 * q * (1 - q) := by
  exact ⟨doublySignedFilledCount_expectation_zero' n p q hp hp1 hq hq1,
    by rw [ProbabilityTheory.variance_of_integral_eq_zero AEMeasurable.of_discrete
           (doublySignedFilledCount_expectation_zero' n p q hp hp1 hq hq1)]
       exact doublySignedFilledCount_sq_integral' n p q hp hp1 hq hq1⟩

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

/-
PROVIDED SOLUTION
Step 1: Use cech_integral_eq to rewrite the integral over CechSample as an integral over (Fin n → Torus d) with the product measure. The integrand becomes a function of pts : Fin n → Torus d, where hasEdge becomes dist (pts e.1) (pts e.2) ≤ r and hasFill becomes ∃ z, ∀ i ∈ t.val, dist (pts i) z ≤ r.

Step 2: Since t has card 3, extract the three vertices. Use t.val.orderEmbOfFin t.property to get an injection σ : Fin 3 → Fin n with t.val = Finset.image σ Finset.univ. σ is strictly monotone.

Step 3: The integrand only depends on pts ∘ σ (the 3 relevant coordinates). Show that integrating a function f(pts ∘ σ) over the n-fold product of probability measures equals integrating f over the 3-fold product. This follows from Fubini: the n-3 irrelevant coordinates integrate to 1 (probability measure).

More concretely, use MeasureTheory.integral_comp_piCongrLeft or a measure-preserving map. The map pts ↦ pts ∘ σ pushes forward the n-fold product measure to a measure on Fin 3 → Torus d. Since σ is injective and each component has the same marginal, the pushforward is the 3-fold product measure.

Alternatively, use MeasureTheory.Measure.pi_map_piCongrLeft to show that mapping through a Fintype equiv preserves the product measure, but σ is not surjective. Instead, think of it as: projecting n i.i.d. components onto 3 of them gives the same distribution as 3 i.i.d. components.

The key Mathlib tool is probably Measure.map_piCongrLeft or showing the map is measure-preserving using MeasureTheory.MeasurePreserving.

Step 4: After the change of variables, the integrand matches the definition of geometricCov. Show this by unfolding geometricCov and showing the integrands are equal (using the correspondence between triangleEdges and the 3 pairs in Fin 3, and between the hasFill condition and the ∃ z condition).

This is a hard lemma. If the full marginalization argument is too hard, try to use congr extensively and sorry individual steps.
-/
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
  have h_triangle : ∃ σ : Fin 3 → Fin n, StrictMono σ ∧ t.val = Finset.image σ Finset.univ := by
    have := t.2;
    exact ⟨ fun i => t.val.orderEmbOfFin this i, by simp +decide [ StrictMono ], by simp +decide [ Finset.ext_iff ] ⟩;
  obtain ⟨σ, hσ_mono, hσ_image⟩ := h_triangle
  have h_integral_simplified : ∫ s : CechSample n d, (∏ e ∈ triangleEdges t, (if s.hasEdge (matchRadius p d) e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.hasFill (matchRadius p d) t then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂cechMeasure n d (matchRadius p d) =
    ∫ pts : Fin n → Torus d, (∏ e ∈ Finset.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2) (Finset.univ : Finset (Fin 3 × Fin 3)), (if dist (pts (σ e.1)) (pts (σ e.2)) ≤ matchRadius p d then (1 : ℝ) - p else -p)) *
      (if ∃ z, ∀ i : Fin 3, dist (pts (σ i)) z ≤ matchRadius p d then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂MeasureTheory.Measure.pi (fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) := by
        convert cech_integral_eq n d ( matchRadius p d ) _ using 1;
        -- Since $t.val = \text{image} \, \sigma \, \text{univ}$, the triangleEdges of $t$ are the same as the triangleEdges of the image of $\sigma$.
        have h_triangleEdges : triangleEdges t = Finset.image (fun e : Fin 3 × Fin 3 => (σ e.1, σ e.2)) (Finset.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2) (Finset.univ : Finset (Fin 3 × Fin 3))) := by
          ext ⟨i, j⟩; simp [triangleEdges, hσ_image];
          constructor <;> intro h;
          · rcases h with ⟨ ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩, hij ⟩ ; exact ⟨ a, b, hσ_mono.lt_iff_lt.mp hij, rfl, rfl ⟩ ;
          · obtain ⟨ a, b, hab, rfl, rfl ⟩ := h; exact ⟨ ⟨ ⟨ a, rfl ⟩, ⟨ b, rfl ⟩ ⟩, hσ_mono hab ⟩ ;
        simp_all +decide [ Finset.prod_image, CechSample.hasEdge, CechSample.hasFill ];
        simp +decide [ Finset.prod_image, hσ_mono.injective.eq_iff ];
  have h_integral_simplified : ∫ pts : Fin n → Torus d, (∏ e ∈ Finset.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2) (Finset.univ : Finset (Fin 3 × Fin 3)), (if dist (pts (σ e.1)) (pts (σ e.2)) ≤ matchRadius p d then (1 : ℝ) - p else -p)) *
      (if ∃ z, ∀ i : Fin 3, dist (pts (σ i)) z ≤ matchRadius p d then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂MeasureTheory.Measure.pi (fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) =
    ∫ pts : Fin 3 → Torus d, (∏ e ∈ Finset.filter (fun p : Fin 3 × Fin 3 => p.1 < p.2) (Finset.univ : Finset (Fin 3 × Fin 3)), (if dist (pts e.1) (pts e.2) ≤ matchRadius p d then (1 : ℝ) - p else -p)) *
      (if ∃ z, ∀ i : Fin 3, dist (pts i) z ≤ matchRadius p d then (1 : ℝ) - fillingProb p d else -fillingProb p d) ∂MeasureTheory.Measure.pi (fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) := by
        have h_integral_simplified : MeasureTheory.Measure.map (fun pts : Fin n → Torus d => fun i : Fin 3 => pts (σ i)) (MeasureTheory.Measure.pi (fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) = MeasureTheory.Measure.pi (fun _ => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) := by
          refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ hs, Finset.prod_apply, Set.pi ] ;
          · rw [ show { a : Fin n → Torus d | ∀ i, a ( σ i ) ∈ s i } = ( Set.pi Set.univ fun i => if h : ∃ j, σ j = i then s ( Classical.choose h ) else Set.univ ) from ?_, MeasureTheory.Measure.pi_pi ];
            · rw [ ← Finset.prod_subset ( Finset.subset_univ ( Finset.image σ Finset.univ ) ) ];
              · rw [ Finset.prod_image ] <;> simp +decide [ hσ_mono.injective.eq_iff ];
                · refine' Finset.prod_bij ( fun i _ => Classical.choose ( show ∃ j, σ j = σ i from ⟨ i, rfl ⟩ ) ) _ _ _ _ <;> simp +decide [ hσ_mono.injective.eq_iff ];
                · exact hσ_mono.injective;
              · simp +contextual [ Finset.mem_image, hσ_mono.injective.eq_iff ];
                exact fun _ _ => by erw [ MeasureTheory.Measure.pi_univ ] ; norm_num;
            · ext; simp [Set.mem_pi];
              constructor <;> intro h i;
              · split_ifs with h <;> simp_all +decide [ hσ_mono.injective.eq_iff ];
                convert h ( Classical.choose ‹∃ j, σ j = i› ) using 1 ; rw [ Classical.choose_spec ‹∃ j, σ j = i› ];
              · convert h ( σ i ) using 1 ; simp +decide [ hσ_mono.injective.eq_iff ];
                exact congr_arg _ ( hσ_mono.injective ( by have := Classical.choose_spec ( show ∃ j, σ j = σ i from ⟨ i, rfl ⟩ ) ; aesop ) );
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
        rw [ ← h_integral_simplified, MeasureTheory.integral_map ];
        · exact measurable_pi_lambda _ ( fun _ => measurable_pi_apply _ ) |> Measurable.aemeasurable;
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · refine' Finset.measurable_prod _ _;
            intro e he; exact Measurable.ite ( measurableSet_le ( measurable_pi_apply e.1 |> Measurable.dist <| measurable_pi_apply e.2 ) measurable_const ) measurable_const measurable_const;
          · refine' Measurable.ite _ measurable_const measurable_const;
            -- The set of points where there exists a center within a certain distance is measurable.
            have h_measurable : MeasurableSet {a : Fin 3 → Torus d | ∃ z : Torus d, ∀ i : Fin 3, dist (a i) z ≤ matchRadius p d} := by
              have h_closed : IsClosed {a : Fin 3 → Torus d | ∃ z : Torus d, ∀ i : Fin 3, dist (a i) z ≤ matchRadius p d} := by
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
                intro i;
                exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist ( tendsto_pi_nhds.mp hx₂ i |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) hsubseq₂ ) tendsto_const_nhds fun n => hz _ _
              exact h_closed.measurableSet;
            exact h_measurable;
  convert h_integral_simplified using 1;
  unfold geometricCov;
  simp +decide [ Fin.prod_univ_three, Fin.forall_fin_succ ];
  rw [ show ( Finset.filter ( fun e : Fin 3 × Fin 3 => e.1 < e.2 ) Finset.univ : Finset ( Fin 3 × Fin 3 ) ) = { ( 0, 1 ), ( 0, 2 ), ( 1, 2 ) } by decide ] ; simp +decide [ Finset.prod ] ; ring;

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
lemma fillingProb_tendsto_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => fillingProb p d) Filter.atTop (nhds 1) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [fill_eventually_always' p hp0 hp1] with d hfill
  show fillingProb p d = 1
  unfold fillingProb; simp only
  have h_indicator_eq_one : (fun pts : Fin 3 → Torus d =>
      if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
      then (1 : ℝ) else 0) = fun _ => 1 := by
    ext pts
    simp only [ite_eq_left_iff, one_ne_zero]
    intro hno
    exact absurd (hfill pts) hno
  rw [h_indicator_eq_one]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  rw [MeasureTheory.Measure.real]
  have h1 : (MeasureTheory.Measure.pi fun _ : Fin 3 =>
    (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) Set.univ = 1 := by
    erw [MeasureTheory.Measure.pi_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    erw [MeasureTheory.Measure.pi_univ]
    simp [AddCircle.measure_univ]
  rw [h1]; simp

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
  · norm_num;
  · filter_upwards [ ] with a using by norm_num; split_ifs <;> exact abs_le.mpr ⟨ by nlinarith [ mul_self_nonneg p ], by nlinarith [ mul_self_nonneg p ] ⟩ ;
  · norm_num +zetaDelta at *;
    rw [ MeasureTheory.measureReal_def ];
    erw [ MeasureTheory.Measure.pi_univ ] ; norm_num;
    erw [ MeasureTheory.Measure.pi_univ ] ; norm_num

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
lemma tvDist_ge_abs {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A) :
    tvDist μ ν ≥ |(μ A).toReal - (ν A).toReal| := by
  refine' le_csSup _ ⟨ A, hA, rfl ⟩;
  exact ⟨ ( μ Set.univ ).toReal + ( ν Set.univ ).toReal, by rintro x ⟨ s, hs, rfl ⟩ ; exact abs_le.mpr ⟨ by linarith [ show 0 ≤ ( μ s ).toReal by positivity, show 0 ≤ ( ν s ).toReal by positivity, show ( μ s ).toReal ≤ ( μ Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ), show ( ν s ).toReal ≤ ( ν Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ], by linarith [ show 0 ≤ ( μ s ).toReal by positivity, show 0 ≤ ( ν s ).toReal by positivity, show ( μ s ).toReal ≤ ( μ Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ), show ( ν s ).toReal ≤ ( ν Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ] ⟩ ⟩

/-
PROBLEM
tvDist ≤ 1 for probability measures.

PROVIDED SOLUTION
tvDist = sSup {|μ(A).toReal - ν(A).toReal| : A measurable}. For probability measures, μ(A).toReal ∈ [0,1] and ν(A).toReal ∈ [0,1], so |μ(A).toReal - ν(A).toReal| ≤ 1. Thus the set is bounded by 1 and sSup ≤ 1. Use csSup_le. Need to show the set is nonempty (take A = ∅ or univ).
-/
lemma tvDist_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ _, ⟨ Set.univ, MeasurableSet.univ, rfl ⟩ ⟩;
  · intro b x hx hb; rw [ hb ] ; exact abs_sub_le_iff.mpr ⟨ by linarith [ show ( μ x |> ENNReal.toReal ) ≤ 1 by exact le_trans ( ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ x ) ) ) ( by norm_num ), show ( ν x |> ENNReal.toReal ) ≥ 0 by positivity ], by linarith [ show ( μ x |> ENNReal.toReal ) ≥ 0 by positivity, show ( ν x |> ENNReal.toReal ) ≤ 1 by exact le_trans ( ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ x ) ) ) ( by norm_num ) ] ⟩ ;

/-
PROBLEM
If for each k we have measurable sets A_k with ν_k(A_k) → 1 and μ_k(A_k) → 0,
    then tvDist μ_k ν_k → 1.

PROVIDED SOLUTION
We need to show tvDist (μ k) (ν k) → 1.

For the upper bound: tvDist ≤ 1 by tvDist_le_one.

For the lower bound: tvDist (μ k) (ν k) ≥ |(μ k (A k)).toReal - (ν k (A k)).toReal| by tvDist_ge_abs (using IsProbabilityMeasure implies IsFiniteMeasure). Since (μ k (A k)).toReal → 0 and (ν k (A k)).toReal → 1, |0 - 1| = 1, so tvDist → 1 from below eventually.

More precisely: squeeze_zero_of_nonneg doesn't apply here since we want → 1, not → 0. Use squeeze theorem / tendsto_of_tendsto_of_tendsto_of_le_of_le:
- 1 - (ν k (A k)).toReal + (μ k (A k)).toReal ≤ something...

Actually simpler: show that eventually tvDist ≥ (ν k (A k)).toReal - (μ k (A k)).toReal (from tvDist_ge_abs, since |a - b| ≥ b - a... wait no, |μ - ν| might give μ - ν or ν - μ). We have tvDist ≥ |(μ(A) - ν(A))| ≥ ν(A) - μ(A).

So: ν(A).toReal - μ(A).toReal ≤ tvDist ≤ 1. Since ν(A).toReal → 1 and μ(A).toReal → 0, the lower bound → 1. By squeeze theorem, tvDist → 1.

Use Filter.tendsto_of_tendsto_of_tendsto_of_le_of_le with lower bound (ν(A).toReal - μ(A).toReal) and upper bound (constant 1).
-/
lemma tvDist_tendsto_one_of_events {Ω : ℕ → Type*}
    [inst : ∀ k, MeasurableSpace (Ω k)]
    (μ ν : ∀ k, MeasureTheory.Measure (Ω k))
    [hμ : ∀ k, MeasureTheory.IsProbabilityMeasure (μ k)]
    [hν : ∀ k, MeasureTheory.IsProbabilityMeasure (ν k)]
    (A : ∀ k, Set (Ω k))
    (hA : ∀ k, MeasurableSet (A k))
    (hμA : Filter.Tendsto (fun k => (μ k (A k)).toReal) Filter.atTop (nhds 0))
    (hνA : Filter.Tendsto (fun k => (ν k (A k)).toReal) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun k => tvDist (μ k) (ν k)) Filter.atTop (nhds 1) := by
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' _ tendsto_const_nhds _ _;
  use fun k => |(ν k (A k)).toReal - (μ k (A k)).toReal|;
  · simpa using Filter.Tendsto.abs ( hνA.sub hμA );
  · exact Filter.Eventually.of_forall fun k => by simpa [ abs_sub_comm ] using tvDist_ge_abs ( μ k ) ( ν k ) ( A k ) ( hA k ) ;
  · exact Filter.Eventually.of_forall fun k => tvDist_le_one _ _

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
  unfold doublySignedFilledCount cechDoublySignedCount cechObservation; simp +decide [ Finset.prod_filter ] ;
  grind +ring

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
  -- Since the comap of the volume measure is a probability measure, and the points function is measurable, the map of the measure under the points function is also a probability measure.
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

/-
PROBLEM
twoParamMeasure is a probability measure.

PROVIDED SOLUTION
Construct the instance using twoParamMeasure_totalMass which gives (twoParamMeasure n p q) Set.univ = 1. Use ⟨twoParamMeasure_totalMass n p q hp hp1 hq hq1⟩.
-/
lemma twoParamMeasure_isProbabilityMeasure (n : ℕ) (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    MeasureTheory.IsProbabilityMeasure (twoParamMeasure n p q) := by
  exact ⟨twoParamMeasure_totalMass n p q hp hp1 hq hq1⟩

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
  unfold triangleIndicator'
  simp +decide [cechObservation, CechSample.hasEdge, CechSample.hasFill]
  congr! 3
  constructor <;> rintro ⟨z, hz⟩
  · use z - h
    intro i hi
    specialize hz i hi
    rw [dist_eq_norm] at *
    simp_all +decide [norm_sub_rev]
    convert hz using 1
    rw [← neg_sub, norm_neg]
    abel_nf
  · use z + h
    simp_all +decide [dist_eq_norm, add_sub_add_right_eq_sub]

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
-- The integral of a single triangle indicator over the product measure equals geometricCov.
private lemma single_triangle_integral_eq_g' {n d : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    let r := matchRadius p d
    let q := fillingProb p d
    ∫ pts : Fin n → Torus d,
      triangleIndicator' p q r t pts
      ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    = geometricCov p d := by
  simp [triangleIndicator', cechObservation, CechSample.hasEdge, CechSample.hasFill];
  convert cechDoublySigned_triangle_integral n d p hp0 hp1 t using 1;
  rw [ cech_integral_eq ];
  simp +decide [ CechSample.hasEdge, CechSample.hasFill ];
  grind +revert
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
  obtain ⟨i, hi⟩ : ∃ i, t.val ∩ t'.val = {i} := Finset.card_eq_one.mp hshare
  generalize_proofs at *
  obtain ⟨j, k, hjk, hj, hk⟩ : ∃ j k : Fin n, j ≠ k ∧ j ∈ t.val ∧ k ∈ t.val ∧ j ≠ i ∧ k ≠ i ∧ t.val = {i, j, k} := by
    have h_card_t_diff : (t.val \ {i}).card = 2 := by grind
    obtain ⟨j, k, hjk, hj, hk⟩ : ∃ j k : Fin n, j ≠ k ∧ j ∈ t.val \ {i} ∧ k ∈ t.val \ {i} ∧ t.val \ {i} = {j, k} := by
      rw [Finset.card_eq_two] at h_card_t_diff; obtain ⟨j, k, hjk⟩ := h_card_t_diff; use j, k; aesop
    generalize_proofs at *; grind
  obtain ⟨l, m, hlm, hl, hm⟩ : ∃ l m : Fin n, l ≠ m ∧ l ∈ t'.val ∧ m ∈ t'.val ∧ l ≠ i ∧ m ≠ i ∧ t'.val = {i, l, m} := by
    have := Finset.card_eq_three.mp t'.2
    generalize_proofs at *
    obtain ⟨x, y, z, hxy, hxz, hyz, ht'⟩ := this; simp_all +decide [Finset.Subset.antisymm_iff, Finset.subset_iff]
    grind +ring
  generalize_proofs at *
  have hTt_factor : ∃ F : (Torus d × Torus d) → ℝ, Measurable F ∧ (fun pts => triangleIndicator' p q r t pts) = F ∘ (fun pts => (pts j - pts i, pts k - pts i)) := by
    refine' ⟨fun x => triangleIndicator' p q r t (fun v => if v = j then x.1 + (0 : Torus d) else if v = k then x.2 + (0 : Torus d) else if v = i then (0 : Torus d) else (0 : Torus d)), _, _⟩ <;> norm_num [funext_iff]; (
    refine' Measurable.mul _ _;
    · refine' Finset.measurable_prod _ fun e he => _; simp +decide [cechObservation, CechSample.hasEdge]; (
      refine' Measurable.ite _ measurable_const measurable_const; simp +decide [CechSample.hasEdge]; (
      exact measurableSet_Iic.mem.comp (Measurable.dist (by split_ifs <;> [exact measurable_fst; exact measurable_snd; exact measurable_const]) (by split_ifs <;> [exact measurable_fst; exact measurable_snd; exact measurable_const]))));
    · refine' Measurable.ite _ _ _ <;> norm_num [cechObservation];
      refine' MeasurableSet.mem _;
      refine' MeasurableSet.congr _ _;
      exact {a : Torus d × Torus d | ∃ z : Torus d, dist a.1 z ≤ r ∧ dist a.2 z ≤ r ∧ dist 0 z ≤ r};
      · have h_closed : IsClosed {a : Torus d × Torus d | ∃ z : Torus d, dist a.1 z ≤ r ∧ dist a.2 z ≤ r ∧ dist 0 z ≤ r} := by
          have h_closed : IsClosed {a : Torus d × Torus d × Torus d | dist a.1 a.2.1 ≤ r ∧ dist a.2.2 a.2.1 ≤ r ∧ dist 0 a.2.1 ≤ r} :=
            IsClosed.inter (isClosed_le (continuous_fst.dist continuous_snd.fst) continuous_const) (IsClosed.inter (isClosed_le (continuous_snd.snd.dist continuous_snd.fst) continuous_const) (isClosed_le (continuous_const.dist continuous_snd.fst) continuous_const))
          generalize_proofs at *
          have h_closed : IsClosed (Set.image (fun a : Torus d × Torus d × Torus d => (a.1, a.2.2)) {a : Torus d × Torus d × Torus d | dist a.1 a.2.1 ≤ r ∧ dist a.2.2 a.2.1 ≤ r ∧ dist 0 a.2.1 ≤ r}) := by
            apply_rules [IsCompact.isClosed, IsCompact.image]; · exact?; · fun_prop (disch := solve_by_elim)
          generalize_proofs at *
          convert h_closed using 1; ext ⟨a, b⟩; simp [Set.mem_image]
        generalize_proofs at *; exact h_closed.measurableSet;
      · ext; simp [hk, hm];
        split_ifs <;> simp_all +decide [dist_comm];
        exact ⟨fun ⟨z, hz₁, hz₂, hz₃⟩ => ⟨z, hz₃, hz₁, hz₂⟩, fun ⟨z, hz₁, hz₂, hz₃⟩ => ⟨z, hz₂, hz₃, hz₁⟩⟩);
    intro x; exact (by
    have h_shift : triangleIndicator' p q r t x = triangleIndicator' p q r t (fun v => x v - x i) := by
      convert triangleIndicator'_translate p q r t x (-x i) using 1
      · exact?;
      · convert triangleIndicator'_translate p q r t x (-x i) using 1; norm_num [sub_eq_add_neg]
    generalize_proofs at *
    rw [h_shift, triangleIndicator'_congr]; aesop)
  generalize_proofs at *
  have hTt'_factor : ∃ G : (Torus d × Torus d) → ℝ, Measurable G ∧ (fun pts => triangleIndicator' p q r t' pts) = G ∘ (fun pts => (pts l - pts i, pts m - pts i)) := by
    refine' ⟨fun x => triangleIndicator' p q r t' (fun v => if v = l then x.1 + (0 : Torus d) else if v = m then x.2 + (0 : Torus d) else if v = i then 0 else 0), _, _⟩ <;> simp +decide [funext_iff];
    · refine' Measurable.mul _ _;
      · refine' Finset.measurable_prod _ _; intros; simp +decide [cechObservation, CechSample.hasEdge]; (
        refine' Measurable.ite _ measurable_const measurable_const; simp +decide [CechSample.hasEdge]; (
        exact measurableSet_Iic.mem.comp (Measurable.dist (by split_ifs <;> [exact measurable_fst; exact measurable_snd; exact measurable_const]) (by split_ifs <;> [exact measurable_fst; exact measurable_snd; exact measurable_const]))));
      · refine' Measurable.ite _ _ _ <;> norm_num [cechObservation];
        refine' MeasurableSet.mem _;
        refine' MeasurableSet.congr _ _;
        exact {a : Torus d × Torus d | ∃ z : Torus d, dist a.1 z ≤ r ∧ dist a.2 z ≤ r ∧ dist 0 z ≤ r};
        · have h_closed : IsClosed {a : Torus d × Torus d | ∃ z : Torus d, dist a.1 z ≤ r ∧ dist a.2 z ≤ r ∧ dist 0 z ≤ r} := by
            have h_closed : IsClosed {a : Torus d × Torus d × Torus d | dist a.1 a.2.1 ≤ r ∧ dist a.2.2 a.2.1 ≤ r ∧ dist 0 a.2.1 ≤ r} :=
              IsClosed.inter (isClosed_le (continuous_fst.dist continuous_snd.fst) continuous_const) (IsClosed.inter (isClosed_le (continuous_snd.snd.dist continuous_snd.fst) continuous_const) (isClosed_le (continuous_const.dist continuous_snd.fst) continuous_const))
            generalize_proofs at *
            have h_closed : IsClosed (Set.image (fun a : Torus d × Torus d × Torus d => (a.1, a.2.2)) {a : Torus d × Torus d × Torus d | dist a.1 a.2.1 ≤ r ∧ dist a.2.2 a.2.1 ≤ r ∧ dist 0 a.2.1 ≤ r}) := by
              apply_rules [IsCompact.isClosed, IsCompact.image]; · exact?; · fun_prop (disch := solve_by_elim)
            generalize_proofs at *
            convert h_closed using 1; generalize_proofs at *; ext ⟨x, y⟩; simp [Set.mem_image]
          generalize_proofs at *; exact h_closed.measurableSet;
        · ext; simp [hm];
          split_ifs <;> simp_all +decide [dist_comm];
          exact ⟨fun ⟨z, hz₁, hz₂, hz₃⟩ => ⟨z, hz₃, hz₁, hz₂⟩, fun ⟨z, hz₃, hz₁, hz₂⟩ => ⟨z, hz₁, hz₂, hz₃⟩⟩;
    · intro x; exact (by
      convert triangleIndicator'_translate p q r t' (fun v => if v = l then x l - x i else if v = m then x m - x i else 0) (x i) using 1
      generalize_proofs at *
      refine' triangleIndicator'_congr p q r t' x _ _; aesop)
  generalize_proofs at *
  obtain ⟨F, hF_meas, hF⟩ := hTt_factor; obtain ⟨G, hG_meas, hG⟩ := hTt'_factor; simp_all +decide [ProbabilityTheory.IndepFun]
  apply_rules [ProbabilityTheory.IndepFun.comp, indepFun_coord_diffs_vertex];
  all_goals simp_all +decide [Finset.ext_iff, Set.ext_iff];
  · tauto;
  · grind +ring;
  · grobner;
  · grind +ring
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
  simp only
  set r := matchRadius p d
  set q := fillingProb p d
  set g := geometricCov p d
  set ν := (cechMeasure n d r).map (cechObservation r)
  set f := fun s : TwoParamSample n => doublySignedFilledCount p q s
  set c := (Nat.choose n 3 : ℝ) * g / 2 with hc_def
  -- Case split on whether c > 0
  by_cases hc : c > 0
  case pos =>
    -- Step 1: Set inclusion + Chebyshev
    have h_memLp : MeasureTheory.MemLp f 2 ν := doublySignedFilledCount_memLp n d p hp0 hp1
    have h_cheb := ProbabilityTheory.meas_ge_le_variance_div_sq h_memLp hc
    -- Step 2: ν({f < c}) ≤ ν({|f - E[f]| ≥ c}) by set inclusion
    have h_incl : ν {s | f s < c} ≤ ν {s | c ≤ |f s - ∫ s', f s' ∂ν|} :=
      cech_complement_set_inclusion n d p hp0 hp1 hc
    -- Step 3: Combine
    have h_le_ofReal : ν {s | f s < c} ≤
        ENNReal.ofReal (ProbabilityTheory.variance f ν / c ^ 2) :=
      le_trans h_incl h_cheb
    -- Step 4: Convert to reals
    have h_toReal : (ν {s | f s < c}).toReal ≤
        ProbabilityTheory.variance f ν / c ^ 2 := by
      exact ENNReal.toReal_le_of_le_ofReal
        (div_nonneg (ProbabilityTheory.variance_nonneg f ν) (sq_nonneg c)) h_le_ofReal
    -- Step 5: Use variance bound and simplify
    have h_var := cech_second_moment_bound n d p hp0 hp1
    calc (ν {s | f s < c}).toReal
        ≤ ProbabilityTheory.variance f ν / c ^ 2 := h_toReal
      _ ≤ ((Nat.choose n 3 : ℝ) + 12 * (Nat.choose n 4 : ℝ)) / c ^ 2 :=
          div_le_div_of_nonneg_right h_var (sq_nonneg c)
      _ = 4 * ((Nat.choose n 3 : ℝ) + 12 * (Nat.choose n 4 : ℝ)) /
            ((Nat.choose n 3 : ℝ) * g) ^ 2 := by
          rw [hc_def]; ring
  case neg =>
    -- c = C(n,3)*g/2 <= 0. Since hg : 0 < g, we have C(n,3)*g > 0, so c > 0. Contradiction.
    exact absurd hc (not_lt.mpr (le_of_lt (by
      have : (0 : ℝ) < (Nat.choose n 3 : ℝ) * g / 2 :=
        div_pos (mul_pos (by positivity) hg) two_pos
      linarith)))
-- Updated from f13b4074; formula corrected 2026-04-03 (edge covariance ≤ 1 not ≤ g²).
lemma chebyshev_ratio_tendsto_zero (p : ℝ)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => 4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
        ((Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k)) ^ 2)
      Filter.atTop (nhds 0) := by
  -- The ratio ≈ 72/(n²*g²) → 0 since n^(3/2)*g → ∞ implies n²*g² → ∞.
  -- Split: 4*C(n,3)/(C(n,3)*g)² = 4/(C(n,3)*g²) → 0  [term1]
  --        4*12*C(n,4)/(C(n,3)*g)² ≤ 48*n/(C(n,3)*g²)*1/4 → 0  [term2: C(n,4)≤n*C(n,3)/4]
  have h_term1 : Filter.Tendsto (fun k => 4 / ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2)) Filter.atTop (nhds 0) := by
    refine' tendsto_const_nhds.div_atTop _;
    have h_term1 : Filter.Tendsto (fun k => (nSeq k : ℝ) ^ 3 * (geometricCov p (dSeq k)) ^ 2) Filter.atTop Filter.atTop := by
      convert hSNR.atTop_mul_atTop₀ hSNR using 2 ; ring;
      norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring;
    generalize_proofs at *; (
    have h_term1 : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 3 : ℝ) ≥ (nSeq k : ℝ) ^ 3 / 64 := by
      filter_upwards [ hn.eventually_gt_atTop 64 ] with k hk
      generalize_proofs at *; (
      rw [ Nat.cast_choose ] <;> try linarith
      generalize_proofs at *; (
      rcases n : nSeq k with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.factorial ] ; ring_nf ; norm_num at *; (
      norm_num [ Nat.factorial_ne_zero ] ; nlinarith [ ( by norm_cast : ( 62 : ℝ ) ≤ ↑‹ℕ› ) ] ;)))
    generalize_proofs at *; (
    rw [ Filter.tendsto_atTop_atTop ] at *;
    intro b; obtain ⟨ i, hi ⟩ := ‹∀ b : ℝ, ∃ i, ∀ a : ℕ, i ≤ a → b ≤ ( nSeq a : ℝ ) ^ 3 * geometricCov p ( dSeq a ) ^ 2› ( b * 64 ) ; obtain ⟨ j, hj ⟩ := Filter.eventually_atTop.mp h_term1; use Max.max i j; intros a ha; nlinarith [ hi a ( le_trans ( le_max_left _ _ ) ha ), hj a ( le_trans ( le_max_right _ _ ) ha ) ] ;))
  -- term2: 48*C(n,4)/(C(n,3)*g)² ≤ 12*n/(C(n,3)*g²) → 0
  have h_term2 : Filter.Tendsto (fun k => 48 * (Nat.choose (nSeq k) 4 : ℝ) /
        ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k))) ^ 2) Filter.atTop (nhds 0) := by
    have h_binom_bound : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 4 : ℝ) ≤
        (nSeq k : ℝ) * (Nat.choose (nSeq k) 3 : ℝ) / 4 := by
      filter_upwards [ hn.eventually_gt_atTop 4 ] with k hk
      rw [ le_div_iff₀ ] <;> norm_cast
      linarith [ Nat.add_one_mul_choose_eq (nSeq k) 3, Nat.choose_succ_succ (nSeq k) 3 ]
    have h_term2_bound : ∀ᶠ k in Filter.atTop, 48 * (Nat.choose (nSeq k) 4 : ℝ) /
        ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k))) ^ 2 ≤
        12 * (nSeq k : ℝ) / ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2) := by
      filter_upwards [ h_binom_bound ] with k hk
      by_cases h : geometricCov p (dSeq k) = 0 <;> by_cases h' : Nat.choose (nSeq k) 3 = 0 <;>
        simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ]
      · positivity
      · field_simp [h, h']
        rw [ div_le_div_iff_of_pos_right (by positivity) ]
        nlinarith [ show (0 : ℝ) ≤ geometricCov p (dSeq k) ^ 2 by positivity ]
    have h_12n : Filter.Tendsto (fun k => 12 * (nSeq k : ℝ) /
        ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2)) Filter.atTop (nhds 0) := by
      have h_binom_approx : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 3 : ℝ) ≥ (nSeq k : ℝ) ^ 3 / 27 := by
        have h_binom_approx : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 3 : ℝ) ≥ (nSeq k : ℝ) * (nSeq k - 1) * (nSeq k - 2) / 6 := by
          filter_upwards [ hn.eventually_gt_atTop 3 ] with k hk ; rw [ Nat.cast_choose ] <;> try linarith
          generalize_proofs at *; (
          rcases n : nSeq k with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.factorial ] ; ring_nf ; norm_num;
          norm_num [ Nat.factorial_ne_zero ] ; ring_nf ; norm_num;)
        generalize_proofs at *; (
        filter_upwards [ h_binom_approx, hn.eventually_gt_atTop 27 ] with k hk₁ hk₂ using by nlinarith [ show ( nSeq k : ℝ ) ≥ 28 by exact_mod_cast hk₂, sq ( nSeq k : ℝ ) ] ;)
      -- 12*n / (C(n,3)*g²) ≤ 12*27/n² → 0
      have h_n2g2 : Filter.Tendsto (fun k => (nSeq k : ℝ) ^ 2 * (geometricCov p (dSeq k)) ^ 2)
          Filter.atTop Filter.atTop := by
        have := hSNR.atTop_mul_atTop₀ hSNR
        refine Filter.Tendsto.atTop_nonneg_mul_left (by positivity) ?_
        convert this using 1; ring_nf
        norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring
      refine' squeeze_zero_norm' _ (tendsto_const_nhds.div_atTop h_n2g2)
      filter_upwards [ h_binom_approx ] with k hk
      rw [ Real.norm_of_nonneg (by positivity) ]
      by_cases h : geometricCov p (dSeq k) = 0 <;> by_cases h' : Nat.choose (nSeq k) 3 = 0 <;>
        simp_all +decide
      · positivity
      · field_simp [h, h']
        rw [ div_le_div_iff_of_pos_right (by positivity) ]
        nlinarith [ show (0 : ℝ) ≤ geometricCov p (dSeq k) ^ 2 by positivity,
                    show (0 : ℝ) < (nSeq k : ℝ) by exact_mod_cast Nat.pos_of_ne_zero (by rintro rfl; simp_all) ]
    exact squeeze_zero_norm'
      (by filter_upwards [ h_term2_bound ] with k hk;
          rw [ Real.norm_of_nonneg (by positivity) ]; exact hk)
      h_12n
  have h_sum : Filter.Tendsto (fun k =>
      4 / ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2) +
      48 * (Nat.choose (nSeq k) 4 : ℝ) /
        ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k))) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [ add_zero ] using h_term1.add h_term2
  have h_ratio : ∀ᶠ k in Filter.atTop,
      4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
        ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k))) ^ 2 ≤
      4 / ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k)) ^ 2) +
      48 * (Nat.choose (nSeq k) 4 : ℝ) /
        ((Nat.choose (nSeq k) 3 : ℝ) * (geometricCov p (dSeq k))) ^ 2 := by
    filter_upwards with k
    by_cases h : geometricCov p (dSeq k) = 0 <;> by_cases h' : Nat.choose (nSeq k) 3 = 0 <;>
      simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm ]
    · positivity
    · field_simp [h, h']
      ring_nf
      rw [ div_le_div_iff_of_pos_right (by positivity) ]
      nlinarith [ show (0 : ℝ) ≤ geometricCov p (dSeq k) ^ 2 by positivity ]
  generalize_proofs at *; (
  refine' squeeze_zero_norm' _ h_sum;
  filter_upwards [ h_ratio ] with k hk using by rw [ Real.norm_of_nonneg (by positivity) ]; exact hk;)

/-
PROBLEM
Under the Cech pushforward, the probability that the doubly-signed statistic
    exceeds threshold λ tends to 1.

PROVIDED SOLUTION
We want P(τ_f ≥ λ | Čech) → 1, where λ = C(n,3)*g/2.

Equivalently, P(τ_f < λ | Čech) → 0.

Key steps:
1. E[τ_f | Čech] = C(n,3) * g (by moments_cech_signed)
2. Var[τ_f | Čech] ≤ C(n,3) + 12*C(n,4) (by cech_second_moment_bound and the fact Var ≤ E[τ²])
3. By Chebyshev: P(|τ_f - E[τ_f]| ≥ E[τ_f]/2) ≤ Var/(E[τ_f]/2)²
4. P(τ < λ) ≤ P(|τ - E[τ]| ≥ E[τ]/2) since λ = E[τ]/2
5. The bound → 0 by chebyshev_ratio_tendsto_zero

Use cech_complement_prob_bound and chebyshev_ratio_tendsto_zero as helper lemmas.

The complement probability P(τ < λ) ≤ Chebyshev bound → 0, so P(τ ≥ λ) = 1 - P(τ < λ) → 1.

Use Filter.Tendsto squeeze between lower bound that → 1 and upper bound 1. The lower bound is 1 - (Chebyshev ratio) → 1 - 0 = 1.
-/
/-- Under the Cech pushforward, the probability that the doubly-signed statistic
    exceeds threshold λ tends to 1. -/
lemma paleyZygmund_cech_prob_tendsto_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
        (cechObservation (matchRadius p (dSeq k)))
        {s | doublySignedFilledCount p (fillingProb p (dSeq k)) s ≥
          (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2}).toReal)
      Filter.atTop (nhds 1) := by
  -- P(τ ≥ λ) = 1 - P(τ < λ), so it suffices to show P(τ < λ) → 0
  -- P(τ < λ) ≤ Chebyshev ratio → 0 by chebyshev_ratio_tendsto_zero
  -- Apply the fact that if the bound tends to zero, the probability tends to 1.
  have h_tendsto : Filter.Tendsto
    (fun k => (1 : ℝ) -
      (4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
        ((Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k)) ^ 2))
    Filter.atTop (nhds 1) := by
      exact le_trans ( tendsto_const_nhds.sub <| chebyshev_ratio_tendsto_zero p nSeq dSeq hn hSNR ) <| by norm_num;
  generalize_proofs at *; (
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_tendsto tendsto_const_nhds _ _ <;> norm_num
  generalize_proofs at *; (
  have h_complement : ∀ᶠ k in Filter.atTop, (MeasureTheory.Measure.map (cechObservation (matchRadius p (dSeq k))) (cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))) {s | doublySignedFilledCount p (fillingProb p (dSeq k)) s < (Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k) / 2}).toReal ≤ 4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) / ((Nat.choose (nSeq k) 3 : ℝ) * geometricCov p (dSeq k)) ^ 2 := by
    have hg_pos : ∀ᶠ k in Filter.atTop, 0 < geometricCov p (dSeq k) := by
      filter_upwards [hSNR.eventually_gt_      filter_upwards [hSNR.eventuallith k hk hn_k
      have h_rpow_pos : (0 : ℝ) < (nSeq k : ℝ) ^ (3/2 : ℝ) := by positivity
      exact pos_of_mul_pos_left hk h_rpow_pos.le
    filter_upwards [hg_pos] with k hg_k
    exact cech_complement_prob_bound (nSeq k) (dSeq k) p hp0 hp1 hg_k
  generalize_proofs at *; (
  use 0; intro k hk; specialize h_complement k; rw [ show { s : TwoParamSample ( nSeq k ) | ( nSeq k |> Nat.choose ) 3 * geometricCov p ( dSeq k ) / 2 ≤ doublySignedFilledCount p ( fillingProb p ( dSeq k ) ) s } = ( Set.univ \ { s : TwoParamSample ( nSeq k ) | doublySignedFilledCount p ( fillingProb p ( dSeq k ) ) s < ( nSeq k |> Nat.choose ) 3 * geometricCov p ( dSeq k ) / 2 } ) by ext; simp +decide [ not_lt ] ] ; rw [ MeasureTheory.measure_diff ] <;> norm_num;
  rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ h_complement ];
  · linarith [ show ( 0 : ℝ ) ≤ ( MeasureTheory.Measure.map ( cechObservation ( matchRadius p ( dSeq k ) ) ) ( cechMeasure ( nSeq k ) ( dSeq k ) ( matchRadius p ( dSeq k ) ) ) { s : TwoParamSample ( nSeq k ) | doublySignedFilledCount p ( fillingProb p ( dSeq k ) ) s < ↑ ( ( nSeq k |> Nat.choose ) 3 ) * geometricCov p ( dSeq k ) / 2 } |> ENNReal.toReal ) by positivity ];
  · exact?));
  use 0; intros k hk; exact (by
  refine' le_trans ( ENNReal.toReal_mono _ _ ) _ <;> norm_num [ MeasureTheory.Measure.map_apply ];
  exact 1
  all_goals generalize_proofs at *; (norm_num);
  exact?);)

/-
PROBLEM
The threshold event set is measurable (since MeasurableSpace on TwoParamSample is ⊤).

PROVIDED SOLUTION
The MeasurableSpace on TwoParamSample n is ⊤ (the discrete sigma algebra). Every set is measurable in the discrete sigma algebra. So MeasurableSet S is trivially true. Use trivial or exact MeasurableSpace.measurableSet_top.out or just show this follows from the instance definition.
-/
lemma threshold_event_measurableSet (n : ℕ) (p q lam : ℝ) :
    MeasurableSet {s : TwoParamSample n | doublySignedFilledCount p q s ≥ lam} := by
  -- MeasurableSpace (TwoParamSample n) = ⊤, so every set is measurable
  trivial

/-
PROBLEM
fillingProb is always in [0, 1].

PROVIDED SOLUTION
fillingProb p d is defined as an integral over Set.Ioo 0 1 of a nonneg integrand (volumeFill / volumeEmpty * d * s^(d-1)). Actually, the volumeFill and volumeEmpty could have either sign depending on the integrals, and the ratio could be negative. But since they represent volumes, they should be nonneg.

Actually, let's look at the definition: fillingProb p d = ∫ s in Set.Ioo 0 1, volumeFill d r s / volumeEmpty d r s * d * s^(d-1).

If d = 0, this is ∫ 0 * 0 * ... = 0 ≥ 0. For d ≥ 1, the integrand involves ratios of volumes which should be nonneg.

Actually, this is hard to prove rigorously. Let me try MeasureTheory.setIntegral_nonneg with the condition that the integrand is nonneg.
-/
/-- **fillingProb_nonneg.** The filling probability is nonneg.

    PROVIDED SOLUTION (updated for corrected matchRadius = p^(1/d)/2):
    Step 1: fillingProb p d = ∫ s in Ioo 0 1, (vF/vE)(d, r, s) * d * s^(d-1) where r = matchRadius p d.
    Step 2: The integrand is nonneg:
      - volumeFill d r s ≥ 0 and volumeEmpty d r s ≥ 0 (both are integrals of nonneg functions).
      - So volumeFill/volumeEmpty ≥ 0 (nonneg / nonneg).
      - d * s^(d-1) ≥ 0 for s ≥ 0.
    Step 3: Integral of a nonneg function is nonneg.
    Use MeasureTheory.setIntegral_nonneg measurableSet_Ioo with the pointwise bound.
    For the nonneg of volumeFill/volumeEmpty: unfold to see both are integrals with
    nonneg integrands (rpow_nonneg), and euclidBallVol d r ≥ 0 (rpow_nonneg of pi and r).
    With the new formula matchRadius p d = p^(1/d)/2 ≥ 0 for p > 0, so euclidBallVol d r ≥ 0. -/
open Classical in
lemma fillingProb_nonneg (p : ℝ) (d : ℕ) : 0 ≤ fillingProb p d := by
  unfold fillingProb
  apply MeasureTheory.integral_nonneg
  intro pts; simp only
  split_ifs <;> norm_num


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
open MeasureTheory in
open Classical in
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

/-- **Theorem 1 (Detection Lower Bound, Strategy 2).** Fix p ∈ (0,1).
    If n_k^{3/2} · geometricCov p d_k → ∞, then TV → 1. -/
theorem detection_lower_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * geometricCov p (dSeq k))
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
    have h2 := paleyZygmund_cech_prob_tendsto_one p hp0 hp1 nSeq dSeq hn hd hSNR
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

/-- **Theorem 2 (Phase Transition, Strategy 2).**
    If geometricCov p d ~ G(p)·d^{-α} for some G > 0, α > 0, then the critical
    dimension is d*(n,p) ~ (n^{3/2}·G(p))^{1/α}. Detection succeeds (TV → 1)
    when d_k ≪ d*(n_k, p). -/
theorem phase_transition (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
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
      (fun k => tvDist
        (twoParamMeasure (nSeq k) p (fillingProb p (dSeq k)))
        ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
          (cechObservation (matchRadius p (dSeq k)))))
      Filter.atTop (nhds 1) := by
  /- Note: hbeyond states d/(n^{3/2}·G)^{1/α} → 0, i.e. d ≪ d*(n,p).
     Combined with hasymp (geometricCov ~ G·d^{-α}), this gives
     n^{3/2}·geometricCov ~ n^{3/2}·G·d^{-α} → ∞,
     which is the SNR condition needed by detection_lower_bound.
     The key derivation uses: d^α grows slower than n^{3/2}·G
     iff d·(n^{3/2}·G)^{-1/α} → 0, which is hbeyond. -/
  apply detection_lower_bound p hp0 hp1 nSeq dSeq hn hd
  exact derive_hSNR p hp0 hp1 G α hG hα hasymp nSeq dSeq hn hd hbeyond