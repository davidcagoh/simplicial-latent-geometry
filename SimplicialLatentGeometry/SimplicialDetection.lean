import Mathlib

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
    the matching radius r(p, d) is the unique r ≥ 0 satisfying V_d(2r) = p.
    From V_d(2r) = π^(d/2)/Γ(d/2+1) · (2r)^d = p, solving for r gives
    r = (p · Γ(d/2+1) / π^(d/2))^(1/d) / 2.
    For d = 0, V_0(2r) = 1 for all r (degenerate case), so we set r = 0. -/
noncomputable def matchRadius (p : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0
  else (p * Real.Gamma ((d : ℝ) / 2 + 1) / Real.pi ^ ((d : ℝ) / 2)) ^
         ((1 : ℝ) / (d : ℝ)) / 2

open MeasureTheory in
/-- **Definition 4 (Empty Volume).** V_e(s, d) is the volume of the region a third point
    must occupy to form an *empty* 3-cycle in Cech(n, r, d), given two connected vertices
    at separation s. Equals V_d(2r) * I_{x}((d+1)/2, 1/2) where x = 1 - (s/2r)^2.

    V_e(s,d) is the intersection volume of two d-balls of radius 2r with centres separated
    by s. Using the regularised incomplete Beta function:
      V_e(s,d) = V_d(2r) * (integral_0^x t^(a-1)*(1-t)^(b-1) dt) / B(a,b),
    where a = (d+1)/2, b = 1/2, x = 1-(s/2r)^2, and B(a,b) = Gamma(a)*Gamma(b)/Gamma(a+b). -/
noncomputable def volumeEmpty (d : ℕ) (r s : ℝ) : ℝ :=
  let x := 1 - (s / (2 * r)) ^ 2
  let a := ((d : ℝ) + 1) / 2
  let b := (1 : ℝ) / 2
  -- Incomplete Beta integral: ∫₀ˣ t^(a-1) · (1-t)^(b-1) dt
  let incBeta := ∫ t in Set.Ioo 0 x, t ^ (a - 1) * (1 - t) ^ (b - 1)
  -- Beta function: B(a,b) = Γ(a)·Γ(b)/Γ(a+b)
  let betaFn := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)
  euclidBallVol d (2 * r) * incBeta / betaFn

open MeasureTheory in
/-- **Definition 4 (Fill Volume).** V_f(s, d) is the volume of the region a third point
    must occupy to form a *filled* triangle in Cech(n, r, d), given two connected vertices
    at separation s. See Lemma 2 for the explicit integral formula.

    Using the shell decomposition with normalised separation u = s/(2r) and the
    (d-1)-sphere surface area element S_{d-1}(x) = 2*pi^((d-1)/2)/Gamma((d-1)/2) * x^(d-2):
      V_f(s,d) = (2r)^d * 2 * (I1 + I2)
    where I1 = integral_0^sqrt(1-u^2) of (sqrt(1-x^2) - u/2) * S_{d-1}(x) dx
    and   I2 = integral_{u/2*sqrt(1-u^2)}^{1/2} of sqrt(1/4 - x^2) * S_{d-1}(x) dx. -/
noncomputable def volumeFill (d : ℕ) (r s : ℝ) : ℝ :=
  let u := s / (2 * r)   -- normalised separation
  -- Surface area of (d-2)-sphere of radius x (shell integrand)
  let sphereSurf := fun x : ℝ =>
    2 * Real.pi ^ (((d : ℝ) - 1) / 2) / Real.Gamma (((d : ℝ) - 1) / 2) * x ^ ((d : ℝ) - 2)
  let I₁ := ∫ x in Set.Ioo 0 (Real.sqrt (1 - u ^ 2)),
    (Real.sqrt (1 - x ^ 2) - u / 2) * sphereSurf x
  let I₂ := ∫ x in Set.Ioo (u / 2 * Real.sqrt (1 - u ^ 2)) (1 / 2),
    Real.sqrt (1 / 4 - x ^ 2) * sphereSurf x
  (2 * r) ^ d * (2 * (I₁ + I₂))

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
  ∫ s in Set.Ioo 0 1,
    volumeFill d r s / volumeEmpty d r s * (d : ℝ) * s ^ (d - 1)

/-! ## Moment Setup -/

/-- Discrete sigma-algebra on TwoParamSample (all sets measurable). -/
instance (n : ℕ) : MeasurableSpace (TwoParamSample n) := ⊤

/-- Discrete sigma-algebra on CechSample (all sets measurable). -/
instance (n d : ℕ) : MeasurableSpace (CechSample n d) := ⊤

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

open MeasureTheory ProbabilityTheory in
/-- Variance of filledTriangleCount under 2PC (corrected). -/
lemma moments_twoParam_var (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    variance filledTriangleCount (twoParamMeasure n p q) =
      (n.choose 3 : ℝ) * p ^ 3 * q * (1 - p ^ 3 * q) +
      12 * (n.choose 4 : ℝ) * p ^ 5 * q ^ 2 * (1 - p) := by
  sorry

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
    the degenerate case d=0 where euclidBallVol 0 (2r) = 1 and the formula fails. -/
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

open MeasureTheory in
/-- **Lemma 5 (Asymptotics of 𝔼[V_e]).** As d → ∞ with p ∈ (0,1) fixed,
    𝔼[V_e](p,d) ~ C(p)·d^{-β} for explicit C(p) > 0, β > 0.

    PROVIDED SOLUTION
    Write 𝔼[V_e] = V_d(2r)·∫₀¹ I_{sin²φ}((d+1)/2, 1/2)·d·s^(d-1) ds. As d → ∞ the
    integrand concentrates near s = 0 (the PDF d·s^(d-1) puts mass near 1, but the Ball
    volume V_d(2r) → 0). Expand the incomplete Beta function about the saddle point s = 0
    using a Laplace approximation: the integrand ~ A·exp(-d·f(s)) near the saddle. Evaluate
    the Gaussian integral to extract the polynomial prefactor C(p)·d^{-β}. -/
lemma asymptotics_expectedEmptyVol (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧
    Filter.Tendsto
      (fun d : ℕ => expectedEmptyVol d (matchRadius p d) / (C * (d : ℝ) ^ (-β)))
      Filter.atTop (nhds 1) := by
  sorry

open MeasureTheory in
/-- **Lemma 6 (Asymptotics of 𝔼[V_f]).** As d → ∞ with p ∈ (0,1) fixed,
    𝔼[V_f](p,d) ~ A(p)·d^{-γ} for explicit A(p) > 0, γ = γ(p) > 0.

    PROVIDED SOLUTION
    Apply the same steepest descent strategy to the double integral defining 𝔼[V_f]
    (integrating V_f(s,d) from Definition 4 against the separation PDF d·s^(d-1)):
      𝔼[V_f] = ∫₀¹ V_f(s,d)·d·s^(d-1) ds.
    Identify the saddle point of the exponent in V_f(s,d) (via the shell decomposition of
    Lemma 2), compute the Hessian contribution to extract A(p) and the decay rate γ(p). -/
lemma asymptotics_expectedFillVol (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ A γ : ℝ, 0 < A ∧ 0 < γ ∧
    Filter.Tendsto
      (fun d : ℕ => expectedFillVol d (matchRadius p d) / (A * (d : ℝ) ^ (-γ)))
      Filter.atTop (nhds 1) := by
  sorry

/-- **Corollary 1 (Decay of q*).** Substituting Lemmas 5 and 6 into Definition 5:
    q(p,d) ~ B(p)·d^{-δ} for explicit B(p) > 0, δ = δ(p) > 0.

    PROVIDED SOLUTION
    From Definition 5, q(p,d) = 𝔼[V_f]/𝔼[V_e] (up to the PDF normalisation). Substituting
    𝔼[V_f] ~ A·d^{-γ} (Lemma 6) and 𝔼[V_e] ~ C·d^{-β} (Lemma 5) gives
    q ~ (A/C)·d^{-(γ-β)}. Set B(p) = A(p)/C(p) and δ(p) = γ(p) - β(p). -/
lemma decay_fillingProb (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧
    Filter.Tendsto
      (fun d : ℕ => fillingProb p d / (B * (d : ℝ) ^ (-δ)))
      Filter.atTop (nhds 1) := by
  sorry

/-! ## Main Theorems -/

/-- Total variation distance between two probability measures on the same space.
    TV(μ,ν) = sup_{A measurable} |μ(A) - ν(A)|. -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ s : Set Ω, MeasurableSet s ∧ x = |(μ s).toReal - (ν s).toReal|}

/-! ### Infrastructure lemmas (for later submission) -/

/-- The matching radius satisfies V_d(2r) = p, by definition of matchRadius. -/
lemma matchRadius_spec (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) :
    euclidBallVol d (2 * matchRadius p d) = p := by sorry

/-- The Čech measure is a probability measure (product of Haar probability measures).
    Note: proving this from the comap definition requires showing CechSample.points is a
    MeasurableEmbedding, which in turn requires measurableSet_image' — that images of
    measurable sets (in source ⊤) land in the product sigma algebra on Fin n → Torus d.
    This is non-trivial and is deferred to Aristotle. -/
instance cechMeasure_isProbabilityMeasure (n d : ℕ) (r : ℝ) :
    MeasureTheory.IsProbabilityMeasure (cechMeasure n d r) := by sorry

/-- cechFilledCount is integrable under cechMeasure (it is bounded by C(n,3)).
    Proof: cechFilledCount is bounded by C(n,3) and the measure is finite (probability measure).
    Under a finite measure, bounded measurable functions are integrable.
    Deferred to Aristotle: needs IsFiniteMeasure from cechMeasure_isProbabilityMeasure. -/
lemma cechFilledCount_integrable (n d : ℕ) (r : ℝ) :
    MeasureTheory.Integrable (fun s => cechFilledCount s r) (cechMeasure n d r) := by sorry

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
  unfold cechSignedCount;
  constructor;
  · rw [ MeasureTheory.integral_sub ]
    · norm_num [ cechFilledCount_integrable ]; ring_nf
      grind +suggestions
    · exact cechFilledCount_integrable n d r
    · exact MeasureTheory.integrable_const _
  · have hmr := matchRadius_spec p d hp0 hp1
    convert cechFilledCount_variance n d r p (by rw [hr, hmr]) hp0 hp1 using 1
    · rw [ ProbabilityTheory.variance, ProbabilityTheory.variance ];
      rw [ ProbabilityTheory.evariance, ProbabilityTheory.evariance ];
      rw [ MeasureTheory.integral_sub ] <;> norm_num [ cechFilledCount_integrable ];
      apply_rules [ MeasureTheory.integrable_const ]

/-- **Theorem 1 (Detection Lower Bound).** Fix p ∈ (0,1). If along sequences (n_k, d_k)
    with n_k, d_k → ∞ we have n_k · 𝔼[V_f](p, d_k) → 0, then TV → 1 and the signed
    filled-triangle test achieves asymptotic power 1.

    PROVIDED SOLUTION
    By Lemma 7, SNR → ∞ along the sequence (the n² factor dominates the 𝔼[V_f] decay).
    Under Čech: Paley–Zygmund gives ℙ(Δ̃_f > λ_n) → 1 for any threshold λ_n = o(𝔼[Δ̃_f]).
    Under 2PC: Chebyshev gives ℙ(Δ̃_f > λ_n) ≤ Var/(λ_n)² → 0.
    Hence the test with threshold λ_n = 𝔼_Čech[Δ̃_f]/2 achieves both error → 0. -/
theorem detection_lower_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) * expectedFillVol (dSeq k) (matchRadius p (dSeq k)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k => tvDist
        (twoParamMeasure (nSeq k) p (fillingProb p (dSeq k)))
        ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
          (cechObservation (matchRadius p (dSeq k)))))
      Filter.atTop (nhds 1) := by
  sorry

/-- **Theorem 2 (Phase Transition Threshold).** With 𝔼[V_f] ~ A(p)·d^{-γ(p)} from Lemma 6,
    the critical dimension d*(n,p) defined by n·𝔼[V_f](p,d*) ≍ 1 satisfies
      d*(n,p) ≍ (n·A(p))^{1/γ(p)}.
    The signed filled-triangle test achieves TV → 1 when d ≪ d*(n,p).

    PROVIDED SOLUTION
    From n·A(p)·(d*)^{-γ(p)} ≍ 1, solve: d* ≍ (n·A(p))^{1/γ(p)}.
    When d = o(d*(n,p)): n·𝔼[V_f] ~ n·A·d^{-γ} ≫ n·A·(d*)^{-γ} ≍ 1, so n·𝔼[V_f] → ∞.
    Wait — recheck: n·𝔼[V_f] → 0 is the detection condition from Theorem 1.
    d ≪ d* means d^{-γ} ≫ (d*)^{-γ}, so n·𝔼[V_f] → ∞ (not 0). We need d ≫ d* for
    n·𝔼[V_f] → 0. Restate: detection succeeds when d ≫ d*(n,p). -/
theorem phase_transition (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (A γ : ℝ) (hA : 0 < A) (hγ : 0 < γ)
    (hasymp : Filter.Tendsto
      (fun d : ℕ => expectedFillVol d (matchRadius p d) / (A * (d : ℝ) ^ (-γ)))
      Filter.atTop (nhds 1))
    (nSeq dSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hd : Filter.Tendsto dSeq Filter.atTop Filter.atTop)
    -- d_k ≫ d*(n_k, p): the sequence lies beyond the critical dimension
    (hbeyond : Filter.Tendsto
      (fun k => (dSeq k : ℝ) / ((nSeq k : ℝ) * A) ^ (1 / γ))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => tvDist
        (twoParamMeasure (nSeq k) p (fillingProb p (dSeq k)))
        ((cechMeasure (nSeq k) (dSeq k) (matchRadius p (dSeq k))).map
          (cechObservation (matchRadius p (dSeq k)))))
      Filter.atTop (nhds 1) := by
  sorry