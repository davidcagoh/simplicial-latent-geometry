import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.Core.BetaIncomplete`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


/-! ### OQ-18 Rips reframe — corrected asymptotics

Under Rips on the sup-norm torus with matched-`p` radius `r = p^{1/d}/2`, the per-coord
3-clique probability is `γ(r) = 3r² + (3r-1)²` for `r ∈ (1/3, 1/2]` (audit doc
`my_theorems/oq18_math_audit.md`, session-63 addendum). Letting `r_d = p^{1/d}/2` we
have `γ(r_d) = 1 + 3·log(p)/d + O(1/d²)`, hence

  `fillingProb p d = γ(r_d)^d → exp(3 log p) = p^3`.

Plugging into the algebraic identity `geomCov = q[(1-p)^3 + p^3] − q^2` (proved by
`geometricCov_eq_deep`):

  `geomCov(p, d) → p^3 · [(1-p)^3 + p^3] − p^6 = p^3 (1-p)^3 > 0`.

So under Rips on `ℓ_∞` torus, both `fillingProb` and `geomCov` tend to strictly positive
constants, not zero. The dimensional-threshold story moves to Paper 2 (sphere + Čech).

The two lemmas below state the correct limits. Proofs are stubbed — they require
`TorusIntegrals` lemmas for `r ∈ (1/3, 1/2]` not yet developed (audit Table 2). -/

/-- The integral of the beta-like density d · s^{d-1} over (0,1) equals 1 for d ≥ 1. -/
lemma beta_density_integral (d : ℕ) (hd : 1 ≤ d) :
    ∫ s in Set.Ioo (0 : ℝ) 1, (d : ℝ) * s ^ (d - 1 : ℕ) = 1 := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le] <;> norm_num [hd]
  rw [zero_pow (by linarith), sub_zero, mul_div_cancel₀ _ (by positivity)]





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
lemma incBeta_nonneg (d : ℕ) (x : ℝ) :
    0 ≤ ∫ t in Set.Ioo 0 x,
      t ^ (((d : ℝ) + 1) / 2 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1) := by
  by_contra h_neg;
  convert h_neg <| MeasureTheory.setIntegral_nonneg measurableSet_Ioo fun t ht => ?_ using 1;
  by_cases h : 1 - t ≥ 0;
  · exact mul_nonneg ( Real.rpow_nonneg ht.1.le _ ) ( Real.rpow_nonneg h _ );
  · norm_num [ Real.rpow_def_of_neg ( not_le.mp h ) ];
    norm_num [ show 1 / 2 * Real.pi = Real.pi / 2 by ring ]



open MeasureTheory in
lemma incBeta_mono (d : ℕ) {x y : ℝ} (hxy : x ≤ y) :
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
