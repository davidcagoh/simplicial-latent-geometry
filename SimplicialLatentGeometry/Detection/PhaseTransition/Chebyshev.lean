import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.PhaseTransition.Chebyshev`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


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
