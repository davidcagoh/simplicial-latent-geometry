import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.DeepRegime.CechDoublySigned
import SimplicialLatentGeometry.Detection.PhaseTransition.SecondMoment

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.PhaseTransition.PaleyZygmund`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


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
  classical
  set r : ℝ := matchRadius p d with hr_def
  set q : ℝ := fillingProb p d with hq_def
  set g : ℝ := geometricCov p d with hg_def
  set ν : MeasureTheory.Measure (TwoParamSample n) :=
    (cechMeasure n d r).map (cechObservation r) with hν_def
  -- Step 1: identify the mean ∫ f dν = C(n,3)*g, by pushing through cechObservation.
  have h_mean : (∫ s', doublySignedFilledCount p q s' ∂ν) = (Nat.choose n 3 : ℝ) * g := by
    rw [hν_def,
        MeasureTheory.integral_map (cechObservation_measurable r).aemeasurable
          (Measurable.aestronglyMeasurable (by exact fun _ _ => trivial))]
    -- pointwise: doublySignedFilledCount _ _ (cechObservation r s) = cechDoublySignedCount p q s r
    rw [show
      (∫ s, doublySignedFilledCount p q (cechObservation r s) ∂cechMeasure n d r) =
      ∫ s, cechDoublySignedCount p q s r ∂cechMeasure n d r from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => doublySignedFilledCount_cechObservation p q r s)]
    -- moments_cech_signed gives the value
    have hm := moments_cech_signed n d p hp0 hp1
    exact hm
  -- Step 2: set inclusion {f < λ} ⊆ {|f - mean| ≥ λ}, where λ = C(n,3)*g/2 = mean/2.
  apply MeasureTheory.measure_mono
  intro s hs
  rw [Set.mem_setOf_eq] at hs ⊢
  rw [h_mean]
  -- hs : doublySignedFilledCount p q s < C(n,3)*g/2
  -- want : C(n,3)*g/2 ≤ |doublySignedFilledCount p q s - C(n,3)*g|
  have h_diff : doublySignedFilledCount p q s - (Nat.choose n 3 : ℝ) * g < -((Nat.choose n 3 : ℝ) * g / 2) := by
    linarith
  have : |doublySignedFilledCount p q s - (Nat.choose n 3 : ℝ) * g| ≥ (Nat.choose n 3 : ℝ) * g / 2 := by
    rw [abs_sub_comm]
    have h_pos_diff : (Nat.choose n 3 : ℝ) * g - doublySignedFilledCount p q s > (Nat.choose n 3 : ℝ) * g / 2 := by
      linarith
    have h_nn : 0 ≤ (Nat.choose n 3 : ℝ) * g - doublySignedFilledCount p q s := by
      linarith [hcg]
    rw [abs_of_nonneg h_nn]
    linarith
  exact this



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
      · exact MeasureTheory.measure_ne_top
          (MeasureTheory.Measure.map (cechObservation (matchRadius p d))
            (cechMeasure n d (matchRadius p d)))
          {s |
            ↑(n.choose 3) * geometricCov p d / 2 ≤
              |doublySignedFilledCount p (fillingProb p d) s -
                ∫ s', doublySignedFilledCount p (fillingProb p d) s' ∂MeasureTheory.Measure.map
                    (cechObservation (matchRadius p d)) (cechMeasure n d (matchRadius p d))|}
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
