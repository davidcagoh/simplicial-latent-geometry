import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.PhaseTransition.Chebyshev
import SimplicialLatentGeometry.Detection.PhaseTransition.PaleyZygmund

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.PhaseTransition.Headline`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


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
