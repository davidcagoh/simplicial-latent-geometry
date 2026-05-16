import Mathlib
import SimplicialLatentGeometry.Core.Statistic

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Core / Detection — abstract detection chain

Phase A3 of the OQ-18 multi-paper refactor. Houses the geometry-agnostic pieces of the
detection theorem: total-variation distance, the squeeze lemma that turns event-probability
convergence into TV → 1, and the pure-arithmetic Chebyshev ratio bound.

The variance-side proofs (`paleyZygmund_*_prob_tendsto_one`, `cech_second_moment_bound`)
still live in `SimplicialDetection.lean` pending phase A3.4 — they depend on the concrete
n-point Lebesgue measure on `Torus^n`, which moves with the L∞ instance in A5. Once the
typeclass-parametric Paley–Zygmund is written, the concrete L∞ proof becomes a
specialization.

This module imports `Core.Statistic` only (the 2PC side) and is independent of any
geometric instance.
-/

/-! ## Total variation distance -/

/-- Total variation distance between two measures on `Ω`:
    `tvDist μ ν = sup { ||μ s| − |ν s|| : s measurable }`. -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ s : Set Ω, MeasurableSet s ∧ x = |(μ s).toReal - (ν s).toReal|}

/-- For any measurable `A`, `tvDist μ ν ≥ ||μ A| − |ν A||`. -/
lemma tvDist_ge_abs {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    (A : Set Ω) (hA : MeasurableSet A) :
    tvDist μ ν ≥ |(μ A).toReal - (ν A).toReal| := by
  refine' le_csSup _ ⟨ A, hA, rfl ⟩;
  exact ⟨ ( μ Set.univ ).toReal + ( ν Set.univ ).toReal, by rintro x ⟨ s, hs, rfl ⟩ ; exact abs_le.mpr ⟨ by linarith [ show 0 ≤ ( μ s ).toReal by positivity, show 0 ≤ ( ν s ).toReal by positivity, show ( μ s ).toReal ≤ ( μ Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ), show ( ν s ).toReal ≤ ( ν Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ], by linarith [ show 0 ≤ ( μ s ).toReal by positivity, show 0 ≤ ( ν s ).toReal by positivity, show ( μ s ).toReal ≤ ( μ Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ), show ( ν s ).toReal ≤ ( ν Set.univ ).toReal by exact ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ] ⟩ ⟩

/-- For probability measures, `tvDist μ ν ≤ 1`. -/
lemma tvDist_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ _, ⟨ Set.univ, MeasurableSet.univ, rfl ⟩ ⟩;
  · intro b x hx hb; rw [ hb ] ; exact abs_sub_le_iff.mpr ⟨ by linarith [ show ( μ x |> ENNReal.toReal ) ≤ 1 by exact le_trans ( ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ x ) ) ) ( by norm_num ), show ( ν x |> ENNReal.toReal ) ≥ 0 by positivity ], by linarith [ show ( μ x |> ENNReal.toReal ) ≥ 0 by positivity, show ( ν x |> ENNReal.toReal ) ≤ 1 by exact le_trans ( ENNReal.toReal_mono ( MeasureTheory.measure_ne_top _ _ ) ( MeasureTheory.measure_mono ( Set.subset_univ x ) ) ) ( by norm_num ) ] ⟩ ;

/-- If `μ_k(A_k) → 0` and `ν_k(A_k) → 1` for measurable witness events `A_k`, then
    `tvDist (μ_k) (ν_k) → 1`. The standard squeeze lemma underpinning detection results. -/
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

/-! ## Pure-arithmetic Chebyshev ratio

The variance ratio `4 · (C(n,3) + 12·C(n,4)) / (C(n,3) · g)^2 → 0` is a pure statement in
the real-valued sequence `g : ℕ → ℝ` — the actual `geomCov` plays no role beyond being
plugged in. We expose it as a standalone lemma so per-geometry detection proofs can call
it without reproving the arithmetic. -/

/-- The variance/threshold² ratio appearing in the Paley–Zygmund step tends to zero,
    assuming both `n·g → ∞` and `n^{3/2}·g → ∞`. Pure arithmetic in `n` and `g`. -/
lemma chebyshev_ratio_tendsto_zero (g : ℕ → ℝ)
    (nSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * g k)
      Filter.atTop Filter.atTop)
    (hNG : Filter.Tendsto
      (fun k => (nSeq k : ℝ) * g k)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => 4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
        ((Nat.choose (nSeq k) 3 : ℝ) * g k) ^ 2)
      Filter.atTop (nhds 0) := by
  refine' squeeze_zero_norm' _ _;
  use fun k => 288 / ( ( nSeq k : ℝ ) * g k ) ^ 2;
  · filter_upwards [ hn.eventually_gt_atTop 3, hNG.eventually_gt_atTop 0 ] with k hk₁ hk₂;
    rw [ Real.norm_of_nonneg ( by positivity ), div_le_div_iff₀ ];
    · have h_bound : (Nat.choose (nSeq k) 4 : ℝ) ≤ (nSeq k - 3) / 4 * (Nat.choose (nSeq k) 3 : ℝ) := by
        rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast;
        rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ Nat.add_one_mul_choose_eq ( nSeq k ) 3, Nat.choose_succ_succ ( nSeq k ) 3 ];
      have h_bound : (Nat.choose (nSeq k) 3 : ℝ) ≥ (nSeq k - 2) * (nSeq k - 1) * nSeq k / 6 := by
        rw [ Nat.cast_choose ] <;> try linarith;
        rcases n : nSeq k with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.factorial ];
        rw [ div_le_div_iff₀ ] <;> first | positivity | ring_nf ; norm_num;
      have h_bound : (Nat.choose (nSeq k) 3 : ℝ) * g k ^ 2 > 0 := by
        exact mul_pos ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ( sq_pos_of_pos ( by nlinarith [ show ( nSeq k : ℝ ) > 3 by norm_cast ] ) );
      nlinarith [ sq_nonneg ( ( nSeq k : ℝ ) - 3 ), mul_le_mul_of_nonneg_left ( show ( nSeq k : ℝ ) ≥ 4 by norm_cast ) h_bound.le ];
    · exact sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.choose_pos ( by linarith ) ) ) ( by nlinarith ) );
    · positivity;
  · exact tendsto_const_nhds.div_atTop ( Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| hNG )

/-- `C(n,3) · g² → ∞` whenever `n^{3/2} · g → ∞`. Pure-arithmetic helper, abstract over `g`.
    The concrete L∞ instance plugs in `g k = geometricCov p (dSeq k)`. -/
lemma choose3_g_sq_tendsto_atTop_abstract
    (g : ℕ → ℝ) (nSeq : ℕ → ℕ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * g k)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun k => (Nat.choose (nSeq k) 3 : ℝ) * (g k) ^ 2)
      Filter.atTop Filter.atTop := by
  have h_choose_bound : ∀ k, nSeq k ≥ 6 → (Nat.choose (nSeq k) 3 : ℝ) ≥ (nSeq k ^ 3 : ℝ) / 162 := by
    intro k hk; rw [ Nat.cast_choose ] <;> try linarith;
    rcases n : nSeq k with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.factorial ] ; ring_nf ; norm_num at *;
    norm_num [ Nat.factorial_ne_zero ] ; nlinarith [ ( by norm_cast : ( 3 : ℝ ) ≤ ↑‹ℕ› ) ] ;
  have h_bound_below : ∀ᶠ k in Filter.atTop, (Nat.choose (nSeq k) 3 : ℝ) * (g k) ^ 2 ≥ (nSeq k ^ 3 : ℝ) * (g k) ^ 2 / 162 := by
    filter_upwards [ hn.eventually_ge_atTop 6 ] with k hk using by nlinarith [ h_choose_bound k hk ] ;
  have h_div_inf : Filter.Tendsto (fun k => (nSeq k ^ 3 : ℝ) * (g k) ^ 2 / 162) Filter.atTop Filter.atTop := by
    have h_div_inf : Filter.Tendsto (fun k => ((nSeq k ^ (3 / 2 : ℝ) * g k) ^ 2) / 162) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const ( by norm_num ) ( Filter.tendsto_pow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| hSNR );
    convert h_div_inf using 2 ; ring ; norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring;
  exact Filter.tendsto_atTop_mono' Filter.atTop h_bound_below h_div_inf

/-! ## 2PC measure: total mass and probability-measure instance

These are properties of the universal 2PC null model, independent of any geometric
alternative. Extracted from `SimplicialDetection.lean` in phase A3.1.
-/

set_option maxHeartbeats 800000 in
open MeasureTheory ProbabilityTheory in
/-- The total mass of `twoParamMeasure` is 1 (it is a probability measure). -/
lemma twoParamMeasure_totalMass (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoParamMeasure n p q) Set.univ = 1 := by
      unfold twoParamMeasure; simp [MeasureTheory.Measure.sum_apply]; (
      have h_total : ∑' (e : Fin n → Fin n → Bool), ∑' (f : {σ : Finset (Fin n) // σ.card = 3} → Bool), (∏ i : Fin n, ∏ j : Fin n, (if e i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p))) * (∏ t : {σ : Finset (Fin n) // σ.card = 3}, (if f t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) = 1 := by
        have h_total : ∑' (e : Fin n → Fin n → Bool), (∏ i : Fin n, ∏ j : Fin n, (if e i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p))) = 1 ∧ ∑' (f : {σ : Finset (Fin n) // σ.card = 3} → Bool), (∏ t : {σ : Finset (Fin n) // σ.card = 3}, (if f t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) = 1 := by
          constructor <;> rw [ tsum_fintype ];
          · have h_sum_edges : ∑ b : Fin n → Fin n → Bool, (∏ i : Fin n, ∏ j : Fin n, if b i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) = (∏ i : Fin n, ∏ j : Fin n, (∑ b : Bool, if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p))) := by
              rw [ Finset.prod_sum ];
              rw [ Finset.prod_sum ];
              refine' Finset.sum_bij ( fun b _ => fun i _ j _ => b i j ) _ _ _ _ <;> simp +decide;
              · simp +decide [ funext_iff ];
              · exact fun b => ⟨ fun i j => b i ( Finset.mem_univ i ) j ( Finset.mem_univ j ), rfl ⟩;
            simp_all +decide [ Finset.prod_ite ];
            rw [ ← ENNReal.ofReal_add ] <;> norm_num [ hp, hp1 ];
          · have h_sum : (∑ b : {s : Finset (Fin n) // s.card = 3} → Bool, (∏ t : {s : Finset (Fin n) // s.card = 3}, if b t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))) = (∏ t : {s : Finset (Fin n) // s.card = 3}, (ENNReal.ofReal q + ENNReal.ofReal (1 - q))) := by
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

/-- `twoParamMeasure n p q` is a probability measure when `p, q ∈ [0,1]`. -/
lemma twoParamMeasure_isProbabilityMeasure (n : ℕ) (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    MeasureTheory.IsProbabilityMeasure (twoParamMeasure n p q) :=
  ⟨twoParamMeasure_totalMass n p q hp hp1 hq hq1⟩

/-! ## Trivial measurability under the discrete σ-algebra on `TwoParamSample` -/

/-- Threshold events on the 2PC sample are measurable (discrete σ-algebra). -/
lemma threshold_event_measurableSet (n : ℕ) (p q lam : ℝ) :
    MeasurableSet {s : TwoParamSample n | doublySignedFilledCount p q s ≥ lam} :=
  trivial

/-! ## Abstract Chebyshev tendsto

Geometry-agnostic version of `chebyshev_2PC_prob_tendsto_zero`: given a sequence of
per-`k` Chebyshev bounds on the 2PC measure and an SNR hypothesis on `g`, conclude that
the threshold exceedance probability tends to zero. Per-geometry instances supply the
per-`k` Chebyshev bound (typically from `chebyshev_single_bound` plus that geometry's
filling-probability range) and `g k = geomCov` for the geometry.
-/

/-- **Abstract Chebyshev tendsto.** If, for each `k`, the 2PC threshold-exceedance
    probability is bounded by the Chebyshev variance bound `Var/lam²`, and
    `n^{3/2} · g → ∞`, then the exceedance probability at threshold `C(n,3) · g / 2`
    tends to zero. Geometry-free: `g` and `q` are arbitrary sequences. -/
lemma chebyshev_prob_tendsto_zero_abstract
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (nSeq : ℕ → ℕ) (g q : ℕ → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∀ k, q k ≤ 1)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * g k)
      Filter.atTop Filter.atTop)
    (hChebyshev : ∀ k, ∀ lam : ℝ, 0 < lam →
      (twoParamMeasure (nSeq k) p (q k)
        {s | doublySignedFilledCount p (q k) s ≥ lam}).toReal ≤
      (Nat.choose (nSeq k) 3 : ℝ) * p ^ 3 * (1 - p) ^ 3 * (q k) * (1 - q k) / lam ^ 2) :
    Filter.Tendsto
      (fun k => (twoParamMeasure (nSeq k) p (q k)
        {s | doublySignedFilledCount p (q k) s ≥
          (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal)
      Filter.atTop (nhds 0) := by
  -- Strategy: bound by Chebyshev with lam = C(n,3)·g/2, then majorise the resulting
  -- ratio by  p³(1-p)³ / (C(n,3) · g²)  (using q(1-q) ≤ 1/4), which → 0 by
  -- choose3_g_sq_tendsto_atTop_abstract.
  have hC3_pos : ∀ᶠ k in Filter.atTop, (0 : ℝ) < (Nat.choose (nSeq k) 3 : ℝ) := by
    filter_upwards [hn.eventually_gt_atTop 3] with k hk
    exact Nat.cast_pos.mpr (Nat.choose_pos (by linarith))
  have hN_pos : ∀ᶠ k in Filter.atTop, (0 : ℝ) < (nSeq k : ℝ) ^ (3 / 2 : ℝ) := by
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    exact Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  have hg_pos : ∀ᶠ k in Filter.atTop, (0 : ℝ) < g k := by
    filter_upwards [hSNR.eventually_gt_atTop 0, hN_pos] with k h₁ h₂
    have : 0 < (nSeq k : ℝ) ^ (3 / 2 : ℝ) * g k := h₁
    exact (mul_pos_iff_of_pos_left h₂).mp this
  refine' squeeze_zero_norm' _ _
  use fun k => p ^ 3 * (1 - p) ^ 3 / ((Nat.choose (nSeq k) 3 : ℝ) * (g k) ^ 2)
  · filter_upwards [hC3_pos, hg_pos] with k hC3 hg
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hlam_pos : (0 : ℝ) < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2 := by positivity
    refine (hChebyshev k _ hlam_pos).trans ?_
    have hsq : ((Nat.choose (nSeq k) 3 : ℝ) * g k / 2) ^ 2 =
        (Nat.choose (nSeq k) 3 : ℝ) ^ 2 * (g k) ^ 2 / 4 := by ring
    rw [hsq]
    have h1mp_pos : 0 < 1 - p := by linarith
    have hp_pow_pos : 0 < p ^ 3 * (1 - p) ^ 3 :=
      mul_pos (pow_pos hp0 3) (pow_pos h1mp_pos 3)
    have hq_bound : (q k) * (1 - q k) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (q k - 1/2), hq0 k, hq1 k]
    have hg2_pos : 0 < (g k) ^ 2 := pow_pos hg 2
    have hC3sq_pos : 0 < (Nat.choose (nSeq k) 3 : ℝ) ^ 2 := pow_pos hC3 2
    have h_common : 0 < p ^ 3 * (1 - p) ^ 3 * (Nat.choose (nSeq k) 3 : ℝ) ^ 2 * (g k) ^ 2 :=
      mul_pos (mul_pos hp_pow_pos hC3sq_pos) hg2_pos
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp_pow_pos, hq_bound, hg2_pos, hC3sq_pos, h_common,
      sq (Nat.choose (nSeq k) 3 : ℝ), mul_self_nonneg (g k)]
  · -- numerator/denominator → 0: numerator bounded, denominator → ∞.
    have h_denom : Filter.Tendsto
        (fun k => (Nat.choose (nSeq k) 3 : ℝ) * (g k) ^ 2)
        Filter.atTop Filter.atTop :=
      choose3_g_sq_tendsto_atTop_abstract g nSeq hn hSNR
    exact tendsto_const_nhds.div_atTop h_denom

/-! ## Abstract Paley–Zygmund tendsto

Geometry-agnostic version of `paleyZygmund_cech_prob_tendsto_one`: given a sequence of
probability measures `ν k`, a real-valued statistic `T k`, and a per-`k` upper bound on the
lower-tail probability of `T k` (the form produced by Chebyshev applied to the second-moment
bound), conclude that the upper-tail probability at threshold `C(n,3) · g / 2` tends to one.

Per-geometry instances supply the per-`k` complement bound (typically from a
`*_second_moment_bound` lemma + Chebyshev) and `g k = geomCov` for that geometry.
-/

/-- **Abstract Paley–Zygmund tendsto.** If, for each `k`, the probability under `ν k` that
    `T k` falls below `C(n,3)·g/2` is bounded by the standard Chebyshev complement ratio
    `4·(C(n,3) + 12·C(n,4)) / (C(n,3)·g)²`, and both `n^{3/2}·g → ∞` and `n·g → ∞`, then
    the upper-tail probability tends to one. Geometry-free: `g` is an arbitrary real
    sequence; `ν k` is any probability measure on `Ω k`. -/
lemma paleyZygmund_prob_tendsto_one_abstract
    {Ω : ℕ → Type*} [inst : ∀ k, MeasurableSpace (Ω k)]
    (ν : ∀ k, MeasureTheory.Measure (Ω k))
    [hν : ∀ k, MeasureTheory.IsProbabilityMeasure (ν k)]
    (T : ∀ k, Ω k → ℝ)
    (nSeq : ℕ → ℕ) (g : ℕ → ℝ)
    (hn : Filter.Tendsto nSeq Filter.atTop Filter.atTop)
    (hSNR : Filter.Tendsto
      (fun k => (nSeq k : ℝ) ^ (3/2 : ℝ) * g k)
      Filter.atTop Filter.atTop)
    (hNG : Filter.Tendsto
      (fun k => (nSeq k : ℝ) * g k)
      Filter.atTop Filter.atTop)
    (hThrMeas : ∀ k, MeasurableSet
      {x : Ω k | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2})
    (hComplBound : ∀ᶠ k in Filter.atTop,
      (ν k {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal ≤
      4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
        ((Nat.choose (nSeq k) 3 : ℝ) * g k) ^ 2) :
    Filter.Tendsto
      (fun k => (ν k {x : Ω k | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal)
      Filter.atTop (nhds 1) := by
  -- Strategy: complement → 0 via Chebyshev ratio + the supplied bound;
  -- then upper tail = 1 − complement → 1.
  have h_compl_lt :
      Filter.Tendsto
        (fun k => (ν k {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal)
        Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ _
    use fun k => 4 * ((Nat.choose (nSeq k) 3 : ℝ) + 12 * (Nat.choose (nSeq k) 4 : ℝ)) /
        ((Nat.choose (nSeq k) 3 : ℝ) * g k) ^ 2
    · filter_upwards [hComplBound] with k hk
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact hk
    · simpa using chebyshev_ratio_tendsto_zero g nSeq hn hSNR hNG
  -- Total probability decomposition: ν({<}) + ν({≥}) = 1 for each k.
  have h_total : ∀ k,
      (ν k {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal +
      (ν k {x : Ω k | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal = 1 := by
    intro k
    have hLT : MeasurableSet {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} := by
      -- Complement of the ≥ set is measurable.
      have hcompl : {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} =
          {x : Ω k | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}ᶜ := by
        ext x; simp [not_le]
      rw [hcompl]; exact (hThrMeas k).compl
    have h_union :
        {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} ∪
        {x : Ω k | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} = Set.univ := by
      ext x; by_cases hx : T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2 <;> simp [hx]
      linarith
    have h_disj :
        Disjoint
          {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}
          {x : Ω k | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      have h1 : T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2 := hx
      have h2 : T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2 := hx'
      linarith
    have h_meas_sum :
        ν k ({x | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} ∪
             {x | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}) =
          ν k {x | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} +
          ν k {x | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} :=
      MeasureTheory.measure_union h_disj (hThrMeas k)
    have h_univ : ν k Set.univ = 1 := MeasureTheory.measure_univ
    have h_ne_top₁ :
        ν k {x | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have h_ne_top₂ :
        ν k {x | T k x ≥ (Nat.choose (nSeq k) 3 : ℝ) * g k / 2} ≠ ⊤ :=
      MeasureTheory.measure_ne_top _ _
    have h_real := congrArg ENNReal.toReal h_meas_sum
    rw [ENNReal.toReal_add h_ne_top₁ h_ne_top₂, h_union, h_univ] at h_real
    -- h_real : 1 = ν({<}).toReal + ν({≥}).toReal
    simp at h_real
    linarith
  -- Conclude: upper-tail = 1 − complement → 1 − 0 = 1.
  have h_one_sub :
      Filter.Tendsto
        (fun k => 1 - (ν k {x : Ω k | T k x < (Nat.choose (nSeq k) 3 : ℝ) * g k / 2}).toReal)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h_compl_lt
  refine h_one_sub.congr ?_
  intro k; linarith [h_total k]

/-! ## 2PC moments: signed-statistic expectation and variance

The signed statistic τ_f = Σ_t (A_{e1}-p)(A_{e2}-p)(A_{e3}-p)(F_t-q) has mean zero
and variance C(n,3)·p³(1-p)³·q(1-q) under the 2PC measure. These facts hold for any
geometric alternative and so live in Core. Extracted from SimplicialDetection.lean
in phase A3 cleanup (post-A3.4).
-/

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
