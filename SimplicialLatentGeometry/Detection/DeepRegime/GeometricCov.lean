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



