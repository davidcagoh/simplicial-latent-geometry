import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.Independence.EdgeSharing
import SimplicialLatentGeometry.Detection.Independence.TriangleIndicators

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.PhaseTransition.SecondMoment`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


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
lemma cech_second_moment_structured (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
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
lemma cech_mean_eq (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
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
lemma doublySignedFilledCount_memLp (n d : ℕ) (p : ℝ) (_hp0 : 0 < p) (_hp1 : p < 1) :
    MeasureTheory.MemLp (fun s => doublySignedFilledCount p (fillingProb p d) s) 2
      ((cechMeasure n d (matchRadius p d)).map (cechObservation (matchRadius p d))) :=
  MeasureTheory.MemLp.of_discrete
