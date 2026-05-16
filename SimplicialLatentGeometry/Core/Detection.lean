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
