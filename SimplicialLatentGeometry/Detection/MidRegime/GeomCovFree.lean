import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.MidRegime.FreeIntegrals
import SimplicialLatentGeometry.Detection.MidRegime.Scaffold

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.MidRegime.GeomCovFree`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


/-
**Regime-free closed form for `geometricCov`.** Same conclusion as
    `geometricCov_eq_deep` but with no `matchRadius ≤ 1/4` hypothesis. Proof:
    expand the integrand, use Fubini to factor pairwise/single-edge integrals
    (each 1D torus ball has measure 2r for r ≤ 1/2, matched to give p),
    apply the algebraic identity `E·(E-p) = (1-p)·E` for 0/1 indicators.
-/
lemma geometricCov_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    geometricCov p d
    = fillingProb p d * ((1 - p) ^ 3 + p ^ 3) - fillingProb p d ^ 2 := by
  convert congr_arg₂ ( · - · ) ( centered_edge_moment_fill_free p d hp0 hp1 hd ) ( congr_arg ( fun x => fillingProb p d * x ) ( centered_edge_moment_free p d hp0 hp1 hd ) ) using 1;
  · unfold geometricCov; ring;
    rw [ ← MeasureTheory.integral_const_mul ] ; rw [ ← MeasureTheory.integral_neg ] ; rw [ ← MeasureTheory.integral_add ] ; congr ; ext ; ring;
    · grind;
    · refine' MeasureTheory.Integrable.neg _;
      refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1 + p ^ 3 + 3 * p ^ 2 + 3 * p + 1;
      · norm_num;
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.add, Measurable.neg, Measurable.mul, measurable_const ];
        all_goals apply_rules [ Measurable.ite, measurable_const, measurable_id, Measurable.mul, Measurable.dist, measurable_pi_apply ];
        all_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
      · refine' Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ _, _ ⟩ <;> split_ifs <;> nlinarith [ pow_pos hp0 3 ] ;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1 + 3 * p + 3 * p ^ 2 + p ^ 3;
      · norm_num +zetaDelta at *;
      · refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.add _ _;
        · refine' Measurable.add _ _;
          · refine' Measurable.add _ _;
            · refine' Measurable.add _ _;
              · refine' Measurable.add _ _;
                · refine' Measurable.neg _;
                  refine' Measurable.mul _ _;
                  · refine' Measurable.mul _ _;
                    · exact Measurable.mul measurable_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const );
                    · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
                  · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
                · refine' Measurable.sub _ _;
                  · refine' Measurable.neg _;
                    refine' Measurable.mul _ _;
                    · refine' Measurable.mul _ _;
                      · refine' Measurable.mul _ _;
                        · exact measurable_const;
                        · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _;
                      · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
                    · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
                  · refine' Measurable.mul _ _;
                    · refine' Measurable.mul _ _;
                      · exact Measurable.mul measurable_const ( Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _ );
                      · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
                    · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
              · refine' Measurable.mul _ _;
                · refine' Measurable.mul _ _;
                  · exact Measurable.mul measurable_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const );
                  · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
                · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
            · refine' Measurable.mul _ _;
              · refine' Measurable.mul _ _;
                · exact Measurable.const_mul ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _;
                · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
              · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
          · refine' Measurable.sub _ _;
            · refine' Measurable.mul _ _;
              · refine' Measurable.mul _ _;
                · exact Measurable.mul measurable_const ( Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const ) _ );
                · exact Measurable.ite ( measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
              · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
            · refine' Measurable.mul _ _;
              · refine' Measurable.mul _ _;
                · exact Measurable.mul measurable_const ( Measurable.ite ( measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const );
                · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
              · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · refine' Measurable.mul _ _;
          · refine' Measurable.mul _ _;
            · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const ) _;
            · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
          · exact Measurable.pow_const ( Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const ) _;
      · filter_upwards [ ] with x ; split_ifs <;> norm_num <;> ring_nf ;
        exacts [ abs_le.mpr ⟨ by nlinarith [ pow_pos hp0 3 ], by nlinarith [ pow_pos hp0 3 ] ⟩, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity, by positivity ];
  · ring



/-- **Closed-form difference tends to zero (Paper 1 headline bridge).**
    Trivial corollary of `geometricCov_eq` — the difference is identically 0
    for `d ≥ 1`, hence its `atTop` limit is 0. -/
lemma geometricCov_sub_closedForm_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto
      (fun d : ℕ => geometricCov p d -
        (fillingProb p d * ((1 - p)^3 + p^3) - (fillingProb p d)^2))
      Filter.atTop (nhds 0) := by
  have h_eventually_zero :
      ∀ᶠ d : ℕ in Filter.atTop,
        geometricCov p d -
          (fillingProb p d * ((1 - p)^3 + p^3) - (fillingProb p d)^2) = 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with d hd
    rw [geometricCov_eq p d hp0 hp1 hd]
    ring
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventually_zero)
    tendsto_const_nhds



/-- **OQ-18 Rips asymptotic (Paper 1 headline).** Under Rips with matched
    `p ∈ (0,1)` fixed, `geomCov(p, d) → p^3 (1-p)^3` as `d → ∞`. Replaces
    the false Čech-era `geometricCov_tendsto_zero`.

    Proof: combine `fillingProb_tendsto_pcubed` with the closed-form algebraic
    limit `q[(1-p)^3 + p^3] − q^2 → p^3((1-p)^3 + p^3) − p^6 = p^3 (1-p)^3` via
    polynomial continuity, then use the asymptotic-equivalence axiom
    `geometricCov_sub_closedForm_tendsto_zero` to transport. -/
lemma geometricCov_tendsto_pcubed_compcubed (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geometricCov p d) Filter.atTop
      (nhds (p^3 * (1-p)^3)) := by
  -- Closed-form sequence tends to the same limit by polynomial continuity.
  have h_q : Filter.Tendsto (fun d : ℕ => fillingProb p d) Filter.atTop (nhds (p^3)) :=
    fillingProb_tendsto_pcubed p hp0 hp1
  have h_closed :
      Filter.Tendsto
        (fun d : ℕ => fillingProb p d * ((1 - p)^3 + p^3) - (fillingProb p d)^2)
        Filter.atTop (nhds (p^3 * (1-p)^3)) := by
    have h_eq : p^3 * ((1 - p)^3 + p^3) - (p^3)^2 = p^3 * (1-p)^3 := by ring
    have := (h_q.mul_const ((1 - p)^3 + p^3)).sub (h_q.pow 2)
    simpa [h_eq] using this
  -- Transport via geomCov - closedForm → 0.
  have h_diff := geometricCov_sub_closedForm_tendsto_zero p hp0 hp1
  have h_combined :
      Filter.Tendsto
        (fun d : ℕ => (geometricCov p d -
            (fillingProb p d * ((1 - p)^3 + p^3) - (fillingProb p d)^2))
          + (fillingProb p d * ((1 - p)^3 + p^3) - (fillingProb p d)^2))
        Filter.atTop (nhds (0 + p^3 * (1-p)^3)) :=
    h_diff.add h_closed
  simpa [sub_add_cancel] using h_combined
