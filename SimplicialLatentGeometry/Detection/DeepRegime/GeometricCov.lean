import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.IntegralsAndMoments

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


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
    -- OQ-18 Rips refactor: fill indicator is now the Rips clique product
    -- (all 3 pairwise edges present), not the Čech nerve (∃ z, ...).
    let fill := if dist x₁ x₂ ≤ r ∧ dist x₁ x₃ ≤ r ∧ dist x₂ x₃ ≤ r
                then (1 : ℝ) - q else -q
    e₁₂ * e₁₃ * e₂₃ * fill
  ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))


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
  -- OQ-18 Rips refactor — Aristotle target (job db044b91). Verbatim Aristotle proof.
  convert congr_arg₂ ( · - · ) ( centered_edge_moment_fill p d hp0 hp1 hd hr ) ( congr_arg ( fun x : ℝ => fillingProb p d * x ) ( centered_edge_moment p d hp0 hp1 hd hr ) ) using 1 <;> ring!;
  · rw [ ← MeasureTheory.integral_const_mul ];
    convert MeasureTheory.integral_sub _ _ using 3;
    · grind +locals;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1 + p + p ^ 2 + p ^ 3 + p + p + p ^ 2 + p ^ 3 + 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.add _ _;
        · refine' Measurable.add _ _;
          · refine' Measurable.add _ _;
            · refine' Measurable.add _ _;
              · refine' Measurable.add _ _;
                · refine' Measurable.neg _;
                  refine' Measurable.mul _ _;
                  · refine' Measurable.mul _ _;
                    · exact Measurable.mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
                    · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) _;
                  · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
                · refine' Measurable.mul _ _;
                  · refine' Measurable.mul _ _;
                    · exact Measurable.mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
                    · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
                  · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) _;
              · refine' Measurable.sub _ _;
                · refine' Measurable.mul _ _;
                  · refine' Measurable.mul _ _;
                    · exact Measurable.mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
                    · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) _;
                  · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
                · refine' Measurable.mul _ _;
                  · refine' Measurable.mul _ _;
                    · exact Measurable.mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) measurable_const;
                    · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
                  · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
            · refine' Measurable.sub _ _;
              · refine' Measurable.neg _;
                refine' Measurable.mul _ _;
                · refine' Measurable.mul _ _;
                  · exact Measurable.mul ( Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _ ) measurable_const;
                  · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
                · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
              · refine' Measurable.mul _ _;
                · refine' Measurable.mul _ _;
                  · exact Measurable.mul ( Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const ) _ ) measurable_const;
                  · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) _;
                · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
          · refine' Measurable.mul _ _;
            · refine' Measurable.mul _ _;
              · refine' Measurable.mul _ _;
                · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _;
                · exact measurable_const;
              · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
            · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · refine' Measurable.mul _ _;
          · refine' Measurable.mul _ _;
            · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _;
            · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const ) _;
          · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
      · refine' Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ _, _ ⟩ <;> split_ifs <;> nlinarith [ pow_pos hp0 3 ];
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun a => 1 + p + p + p + p ^ 2 + p ^ 2 + p ^ 2 + p ^ 3 + 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.add, Measurable.neg, Measurable.mul, measurable_const ];
        all_goals apply_rules [ Measurable.ite, measurable_const, measurable_id, Measurable.dist, Measurable.mul, Measurable.add, Measurable.neg, Measurable.pow_const, MeasurableSet.mem ];
        all_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
      · refine' Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ _, _ ⟩ <;> split_ifs <;> nlinarith [ pow_pos hp0 3 ] ;
  · rw [ fillingProb_eq_low_r p d hp0 hp1 hd hr ] ; ring

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
-- OQ-16 / Track B stubs — sparse regime lower bound  (REMOVED 2026-05-19)
--
-- `geometricCov_lower_bound` and `geometricCov_lower_bound_explicit` were
-- derived from the OLD Čech-nerve closed form. Under Rips the closed form is
--   geomCov = q · ((1-p)^3 + p^3) − q^2
-- (see `geometricCov_eq_deep` / `geometricCov_eq`) and the Čech-form lower
-- bound `(1 − q)·(3r²)^d − 3p^3 ≤ geomCov` is no longer derivable.
--
-- Neither lemma had any downstream Lean caller (only doc references in
-- `my_theorems/job4_trackB_prompt.md` and `my_theorems/proof_strategy.md`).
-- A re-derived sparse-regime lower bound under Rips would need a separate
-- research pass — deferred. Lemmas deleted to keep the file sorry-free in
-- this region.
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



set_option maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
open Classical in
lemma cechDoublySigned_triangle_integral (n d : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    let r := matchRadius p d
    let q := fillingProb p d
    ∫ s, ((∏ e ∈ triangleEdges t,
      (if s.hasEdge r e.1 e.2 then (1 : ℝ) - p else -p)) *
    (if s.hasFill r t then (1 : ℝ) - q else -q)) ∂cechMeasure n d r =
      geometricCov p d := by
  classical
  show ∫ s, ((∏ e ∈ triangleEdges t,
        (if s.hasEdge (matchRadius p d) e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.hasFill (matchRadius p d) t
        then (1 : ℝ) - fillingProb p d else -fillingProb p d))
      ∂cechMeasure n d (matchRadius p d) = geometricCov p d
  set r : ℝ := matchRadius p d with hr_def
  set q : ℝ := fillingProb p d with hq_def
  -- Step 0: enumerate t.val by a strict-mono σ : Fin 3 → Fin n.
  set σ : Fin 3 → Fin n := fun i => t.val.orderEmbOfFin t.2 i with hσ_def
  have hσ_mono : StrictMono σ := (t.val.orderEmbOfFin t.2).strictMono
  have hσ_inj : Function.Injective σ := hσ_mono.injective
  have hσ_mem : ∀ i, σ i ∈ t.val := fun i => Finset.orderEmbOfFin_mem _ _ _
  have hσ_image : Finset.image σ Finset.univ = t.val := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact hσ_mem i
    · rw [Finset.card_image_of_injective _ hσ_inj]; simp [t.2]
  -- Step 1: rewrite cechMeasure integral as product-measure integral over Fin n → Torus d.
  rw [cech_integral_eq n d r (fun s => (∏ e ∈ triangleEdges t,
        (if s.hasEdge r e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if s.hasFill r t then (1 : ℝ) - q else -q))]
  -- Step 2: (·∘σ) is measure-preserving from Π_{Fin n} volume to Π_{Fin 3} volume.
  have h_comp_meas : Measurable (fun pts : Fin n → Torus d => pts ∘ σ) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have h_mp :
      MeasureTheory.MeasurePreserving (fun pts : Fin n → Torus d => pts ∘ σ)
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))))
        (MeasureTheory.Measure.pi
            (fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) := by
    refine ⟨h_comp_meas, ?_⟩
    refine (MeasureTheory.Measure.pi_eq ?_).symm
    intro s hs
    rw [MeasureTheory.Measure.map_apply h_comp_meas (MeasurableSet.univ_pi hs)]
    -- Rewrite preimage as a pi-set indexed by Fin n.
    have hpre :
        (fun pts : Fin n → Torus d => pts ∘ σ) ⁻¹' Set.univ.pi s =
          Set.univ.pi (fun j : Fin n =>
            if h : ∃ i : Fin 3, σ i = j then s (Classical.choose h) else Set.univ) := by
      ext pts
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff,
        Function.comp_apply]
      constructor
      · intro hp j
        by_cases hj : ∃ i : Fin 3, σ i = j
        · rw [dif_pos hj]
          have h_eq := Classical.choose_spec hj
          have := hp (Classical.choose hj)
          rw [h_eq] at this; exact this
        · rw [dif_neg hj]; trivial
      · intro hp i
        have hex : ∃ k : Fin 3, σ k = σ i := ⟨i, rfl⟩
        have hk : Classical.choose hex = i :=
          hσ_inj (Classical.choose_spec hex)
        have := hp (σ i)
        rw [dif_pos hex, hk] at this; exact this
    rw [hpre, MeasureTheory.Measure.pi_pi]
    -- Compute the product: σ-image contributes vol(s i); other indices contribute 1.
    rw [← Finset.prod_subset (Finset.image σ Finset.univ).subset_univ
          (s₂ := Finset.univ) (f := fun j : Fin n =>
            (MeasureTheory.volume : MeasureTheory.Measure (Torus d))
              (if h : ∃ i : Fin 3, σ i = j then s (Classical.choose h) else Set.univ))]
    · rw [Finset.prod_image (fun a _ b _ h => hσ_inj h)]
      refine Finset.prod_congr rfl ?_
      intro i _
      have hex : ∃ k : Fin 3, σ k = σ i := ⟨i, rfl⟩
      have hk : Classical.choose hex = i := hσ_inj (Classical.choose_spec hex)
      rw [dif_pos hex, hk]
    · intro j _ hj
      have : ¬ ∃ i : Fin 3, σ i = j := by
        rintro ⟨i, rfl⟩
        exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      rw [dif_neg this, MeasureTheory.measure_univ]
  -- Step 3: change variable via h_mp.
  -- The integrand factors through (·∘σ): both the edges (indexed by triangleEdges t) and
  -- the fill (indexed by t.val) only see coordinates in t.val = σ-image.
  -- Define the integrand as a function of `s' : Fin 3 → Torus d`.
  set F : (Fin 3 → Torus d) → ℝ := fun s' =>
    (∏ e ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun e => e.1 < e.2),
        (if dist (s' e.1) (s' e.2) ≤ r then (1 : ℝ) - p else -p)) *
    (if (∀ i j : Fin 3, dist (s' i) (s' j) ≤ r) then (1 : ℝ) - q else -q) with hF_def
  have hF_meas : Measurable F := by
    refine Measurable.mul ?_ ?_
    · refine Finset.measurable_prod _ (fun e _ => ?_)
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le
        ((measurable_pi_apply _).dist (measurable_pi_apply _)) measurable_const
    · refine Measurable.ite ?_ measurable_const measurable_const
      have h_set_eq :
          {a : Fin 3 → Torus d | ∀ i j : Fin 3, dist (a i) (a j) ≤ r} =
            ⋂ i : Fin 3, ⋂ j : Fin 3, {a : Fin 3 → Torus d | dist (a i) (a j) ≤ r} := by
        ext a; simp [Set.mem_iInter]
      rw [h_set_eq]
      refine MeasurableSet.iInter (fun i : Fin 3 => ?_)
      refine MeasurableSet.iInter (fun j : Fin 3 => ?_)
      exact measurableSet_le
        ((measurable_pi_apply _).dist (measurable_pi_apply _)) measurable_const
  -- Pointwise: the Fin n integrand equals F ∘ (·∘σ).
  have h_pointwise : ∀ pts : Fin n → Torus d,
      (∏ e ∈ triangleEdges t,
        (if (⟨pts⟩ : CechSample n d).hasEdge r e.1 e.2 then (1 : ℝ) - p else -p)) *
      (if (⟨pts⟩ : CechSample n d).hasFill r t then (1 : ℝ) - q else -q)
      = F (pts ∘ σ) := by
    intro pts
    -- Use `if_congr` to swap decidability instances and predicate forms.
    have h_edge_eq : ∀ e : Fin n × Fin n,
        (if (⟨pts⟩ : CechSample n d).hasEdge r e.1 e.2 then (1 : ℝ) - p else -p) =
        (if dist (pts e.1) (pts e.2) ≤ r then (1 : ℝ) - p else -p) := by
      intro e
      have hiff : (⟨pts⟩ : CechSample n d).hasEdge r e.1 e.2 ↔
          dist (pts e.1) (pts e.2) ≤ r := Iff.rfl
      by_cases he : (⟨pts⟩ : CechSample n d).hasEdge r e.1 e.2
      · rw [if_pos he, if_pos (hiff.mp he)]
      · rw [if_neg he, if_neg (mt hiff.mpr he)]
    have h_fill_eq :
        (if (⟨pts⟩ : CechSample n d).hasFill r t then (1 : ℝ) - q else -q) =
        (if (∀ i ∈ t.val, ∀ j ∈ t.val, dist (pts i) (pts j) ≤ r) then (1 : ℝ) - q else -q) := by
      have hiff : (⟨pts⟩ : CechSample n d).hasFill r t ↔
          (∀ i ∈ t.val, ∀ j ∈ t.val, dist (pts i) (pts j) ≤ r) := Iff.rfl
      by_cases hf : (⟨pts⟩ : CechSample n d).hasFill r t
      · rw [if_pos hf, if_pos (hiff.mp hf)]
      · rw [if_neg hf, if_neg (mt hiff.mpr hf)]
    rw [Finset.prod_congr rfl (fun e _ => h_edge_eq e), h_fill_eq]
    -- Reindex the edges-product.
    have h_te : triangleEdges t =
        Finset.image (fun e : Fin 3 × Fin 3 => (σ e.1, σ e.2))
          ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun e => e.1 < e.2)) := by
      unfold triangleEdges
      rw [show (t.val ×ˢ t.val) = Finset.image (fun e : Fin 3 × Fin 3 => (σ e.1, σ e.2))
          (Finset.univ ×ˢ Finset.univ) from ?_]
      · rw [Finset.filter_image]
        congr 1
        ext e
        simp [hσ_mono.lt_iff_lt]
      · rw [← hσ_image, ← Finset.prodMap_image_product σ σ Finset.univ Finset.univ]
        rfl
    rw [h_te]
    have h_prod_eq :
        (∏ e ∈ Finset.image (fun e : Fin 3 × Fin 3 => (σ e.1, σ e.2))
              ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun e => e.1 < e.2)),
            (if dist (pts e.1) (pts e.2) ≤ r then (1 : ℝ) - p else -p)) =
        ∏ e ∈ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun e => e.1 < e.2)),
            (if dist (pts (σ e.1)) (pts (σ e.2)) ≤ r then (1 : ℝ) - p else -p) := by
      rw [Finset.prod_image]
      intro a _ b _ hab
      have h1 : σ a.1 = σ b.1 := congrArg Prod.fst hab
      have h2 : σ a.2 = σ b.2 := congrArg Prod.snd hab
      exact Prod.ext (hσ_inj h1) (hσ_inj h2)
    rw [h_prod_eq]
    -- Fill predicate: ∀ i ∈ t.val, ∀ j ∈ t.val ↔ ∀ i j : Fin 3.
    have h_fill_iff :
        (∀ i ∈ t.val, ∀ j ∈ t.val, dist (pts i) (pts j) ≤ r)
          ↔ ∀ i j : Fin 3, dist (pts (σ i)) (pts (σ j)) ≤ r := by
      constructor
      · intro h i j; exact h (σ i) (hσ_mem i) (σ j) (hσ_mem j)
      · intro h i hi j hj
        rw [← hσ_image] at hi hj
        rcases Finset.mem_image.mp hi with ⟨a, _, rfl⟩
        rcases Finset.mem_image.mp hj with ⟨b, _, rfl⟩
        exact h a b
    simp only [hF_def, Function.comp_apply, h_fill_iff]
  -- Apply pointwise equality to rewrite the integral.
  refine (MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall h_pointwise)).trans ?_
  -- Push to Fin 3 → Torus d via h_mp + integral_map.
  rw [show (∫ pts : Fin n → Torus d, F (pts ∘ σ)
        ∂MeasureTheory.Measure.pi
          (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))) =
      ∫ s' : Fin 3 → Torus d, F s'
        ∂MeasureTheory.Measure.pi
          (fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) from by
    rw [← MeasureTheory.integral_map h_comp_meas.aemeasurable
          hF_meas.aestronglyMeasurable, h_mp.map_eq]]
  -- Now match `geometricCov p d`: same integrand structure.
  unfold geometricCov
  congr 1
  funext s'
  simp only [hF_def]
  -- Edge product: filter {(0,1),(0,2),(1,2)} → e₁₂ * e₁₃ * e₂₃.
  have h_filter :
      ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun e => e.1 < e.2)) =
        ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) := by decide
  rw [h_filter]
  -- Fill: ∀ i j ↔ pairwise three. Needs `r ≥ 0` so diagonal is automatic.
  -- Reduce to clique form via a direct enumeration of Fin 3 × Fin 3.
  have h_fill_clique :
      (∀ i j : Fin 3, dist (s' i) (s' j) ≤ r) ↔
        dist (s' 0) (s' 1) ≤ r ∧ dist (s' 0) (s' 2) ≤ r ∧ dist (s' 1) (s' 2) ≤ r ∧
          0 ≤ r := by
    constructor
    · intro h; refine ⟨h 0 1, h 0 2, h 1 2, ?_⟩
      have := h 0 0; rwa [dist_self] at this
    · rintro ⟨h01, h02, h12, hr⟩ i j
      fin_cases i <;> fin_cases j
      all_goals first
        | (rw [dist_self]; exact hr)
        | exact h01
        | exact h02
        | exact h12
        | (rw [dist_comm]; exact h01)
        | (rw [dist_comm]; exact h02)
        | (rw [dist_comm]; exact h12)
  -- Now r = matchRadius p d is ≥ 0; the extra `0 ≤ r` is true here.
  have hr_nn : 0 ≤ r := by
    show 0 ≤ matchRadius p d
    unfold matchRadius
    split_ifs with hd
    · exact le_refl 0
    · positivity
  have h_iff' : (∀ i j : Fin 3, dist (s' i) (s' j) ≤ r) ↔
      dist (s' 0) (s' 1) ≤ r ∧ dist (s' 0) (s' 2) ≤ r ∧ dist (s' 1) (s' 2) ≤ r := by
    rw [h_fill_clique]
    exact ⟨fun ⟨a, b, c, _⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c, hr_nn⟩⟩
  -- The fill `if` swap uses `if_pos`/`if_neg` to avoid Decidable-instance motive issues.
  have h_fill_swap :
      (if (∀ i j : Fin 3, dist (s' i) (s' j) ≤ r) then (1 : ℝ) - q else -q) =
      (if (dist (s' 0) (s' 1) ≤ r ∧ dist (s' 0) (s' 2) ≤ r ∧ dist (s' 1) (s' 2) ≤ r) then
        (1 : ℝ) - q else -q) := by
    by_cases h : (∀ i j : Fin 3, dist (s' i) (s' j) ≤ r)
    · rw [if_pos h, if_pos (h_iff'.mp h)]
    · rw [if_neg h, if_neg (mt h_iff'.mpr h)]
  rw [h_fill_swap]
  -- Edge product matches; expand and ring it out.
  show
    (∏ e ∈ ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)),
        (if dist (s' e.1) (s' e.2) ≤ r then (1 : ℝ) - p else -p)) *
      (if dist (s' 0) (s' 1) ≤ r ∧ dist (s' 0) (s' 2) ≤ r ∧ dist (s' 1) (s' 2) ≤ r
        then (1 : ℝ) - q else -q)
      = _
  rw [show ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) =
        insert ((0, 1) : Fin 3 × Fin 3)
          (insert ((0, 2) : Fin 3 × Fin 3) ({((1, 2) : Fin 3 × Fin 3)} : Finset _))
        from rfl]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
  ring



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
  classical
  -- Under the comap MS, edge and fill predicates are measurable via the helper.
  have h_points_meas :
      Measurable (CechSample.points : CechSample n d → Fin n → Torus d) :=
    fun x hx => ⟨x, hx, rfl⟩
  have h_edge_meas : ∀ i j : Fin n,
      MeasurableSet {s : CechSample n d | s.hasEdge r i j} := by
    intro i j
    exact measurableSet_le
      (((measurable_pi_apply i).comp h_points_meas).dist
        ((measurable_pi_apply j).comp h_points_meas))
      measurable_const
  -- Integrand measurability: product of indicator-style ifs.
  have h_fun_meas : Measurable (fun s : CechSample n d =>
      (∏ e ∈ triangleEdges t,
        (if s.hasEdge r e.1 e.2 then (1:ℝ) - p else -p)) *
        (if s.hasFill r t then (1:ℝ) - q else -q)) := by
    refine Measurable.mul ?_ ?_
    · exact Finset.measurable_prod _ (fun e _ =>
        Measurable.ite (h_edge_meas e.1 e.2) measurable_const measurable_const)
    · exact Measurable.ite (measurableSet_cechSample_hasFill n d r t)
        measurable_const measurable_const
  -- Pointwise bound: |edge term| ≤ |1-p|+|p|; |fill term| ≤ |1-q|+|q|.
  set Mp : ℝ := |1 - p| + |p|
  set Mq : ℝ := |1 - q| + |q|
  have h_edge_bound : ∀ (s : CechSample n d) (e : Fin n × Fin n),
      |if s.hasEdge r e.1 e.2 then (1:ℝ) - p else -p| ≤ Mp := by
    intro s e
    show |if s.hasEdge r e.1 e.2 then (1:ℝ) - p else -p| ≤ |1 - p| + |p|
    by_cases h : s.hasEdge r e.1 e.2
    · rw [if_pos h]; linarith [abs_nonneg p, abs_nonneg (1 - p), le_abs_self (1 - p)]
    · rw [if_neg h, abs_neg]; linarith [abs_nonneg (1 - p), le_abs_self p]
  have h_fill_bound : ∀ s : CechSample n d,
      |if s.hasFill r t then (1:ℝ) - q else -q| ≤ Mq := by
    intro s
    show |if s.hasFill r t then (1:ℝ) - q else -q| ≤ |1 - q| + |q|
    by_cases h : s.hasFill r t
    · rw [if_pos h]; linarith [abs_nonneg q, abs_nonneg (1 - q), le_abs_self (1 - q)]
    · rw [if_neg h, abs_neg]; linarith [abs_nonneg (1 - q), le_abs_self q]
  have hMp_nn : 0 ≤ Mp := by show 0 ≤ |1 - p| + |p|; positivity
  have hMq_nn : 0 ≤ Mq := by show 0 ≤ |1 - q| + |q|; positivity
  -- Product over a finset of bounded-by-Mp terms ≤ Mp^card.
  have h_prod_bound : ∀ s : CechSample n d,
      |∏ e ∈ triangleEdges t, (if s.hasEdge r e.1 e.2 then (1:ℝ) - p else -p)|
        ≤ Mp ^ (triangleEdges t).card := by
    intro s
    rw [← Finset.prod_const]
    refine (Finset.abs_prod _ _).le.trans ?_
    exact Finset.prod_le_prod (fun e _ => abs_nonneg _) (fun e _ => h_edge_bound s e)
  -- Combine into the overall bound.
  have h_bound : ∀ s : CechSample n d,
      ‖(∏ e ∈ triangleEdges t, (if s.hasEdge r e.1 e.2 then (1:ℝ) - p else -p)) *
        (if s.hasFill r t then (1:ℝ) - q else -q)‖
        ≤ Mp ^ (triangleEdges t).card * Mq := by
    intro s
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (h_prod_bound s) (h_fill_bound s) (abs_nonneg _) (by positivity)
  exact (MeasureTheory.integrable_const (Mp ^ (triangleEdges t).card * Mq)).mono'
    h_fun_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall h_bound)



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
