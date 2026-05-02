import Mathlib

/-!
# Helper lemmas for torus integral computations

This file provides the coordinate-factorisation infrastructure needed for
computing integrals over `Fin 3 → Torus d` that factorise across coordinates.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open MeasureTheory Measure Classical

abbrev T1 := AddCircle (1 : ℝ)

noncomputable instance T1.instIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure T1) where
  measure_univ := by simp [AddCircle.measure_univ]

/-! ## Indicator algebra -/

/-
Product of three 0-1 indicators equals indicator of conjunction.
-/
lemma indicator_mul_mul {α : Type*} (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (x : α) :
    (if P x then (1:ℝ) else 0) * (if Q x then (1:ℝ) else 0) * (if R x then (1:ℝ) else 0)
    = if P x ∧ Q x ∧ R x then 1 else 0 := by
  split_ifs <;> simp_all +decide

/-
Product of two 0-1 indicators equals indicator of conjunction.
-/
lemma indicator_mul_two {α : Type*} (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (x : α) :
    (if P x then (1:ℝ) else 0) * (if Q x then (1:ℝ) else 0)
    = if P x ∧ Q x then 1 else 0 := by
  split_ifs <;> aesop

/-! ## Volume of triangle region on AddCircle -/

/-- The set of triples on the circle where all pairwise distances are ≤ r. -/
def triangleSet (r : ℝ) : Set (Fin 3 → T1) :=
  {u | dist (u 0) (u 1) ≤ r ∧ dist (u 0) (u 2) ≤ r ∧ dist (u 1) (u 2) ≤ r}

/-- The set of triples where (0,1)-distance ≤ r and triple intersection nonempty. -/
def edgeFillSet (r : ℝ) : Set (Fin 3 → T1) :=
  {u | dist (u 0) (u 1) ≤ r ∧ ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r}

/-- The set of triples where the triple intersection of r-balls is nonempty. -/
def fillSet (r : ℝ) : Set (Fin 3 → T1) :=
  {u | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r}

/-! ### Real-line integral lemmas -/

/-
Key integral: ∫_{-r}^r (2r - |x|) dx = 3r². This is the area of [-r,r]² ∩ {|x-y|≤r}
    projected onto one axis.
-/
lemma integral_2r_minus_abs (r : ℝ) (hr0 : 0 ≤ r) :
    ∫ x in Set.Icc (-r) r, (2 * r - |x|) = 3 * r ^ 2 := by
  -- Split the integral at 0: ∫_{-r}^0 (2r - (-x)) dx + ∫_0^r (2r - x) dx.
  have h_split : ∫ x in Set.Icc (-r) r, (2 * r - |x|) = (∫ x in Set.Icc (-r) 0, (2 * r + x)) + (∫ x in Set.Icc 0 r, (2 * r - x)) := by
    have h_split : ∫ x in Set.Icc (-r) r, (2 * r - |x|) = (∫ x in Set.Icc (-r) 0, (2 * r - |x|)) + (∫ x in Set.Icc 0 r, (2 * r - |x|)) := by
      norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, hr0 ];
      rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
    exact h_split.trans ( congrArg₂ _ ( MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by rw [ abs_of_nonpos hx.2 ] ; ring ) ( MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by rw [ abs_of_nonneg hx.1 ] ) );
  rw [ h_split, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, ← intervalIntegral.integral_of_le, intervalIntegral.integral_add, intervalIntegral.integral_sub ] <;> norm_num <;> linarith

/-
Key integral: ∫_{-r}^r (4r - |x|) dx = 7r².
-/
lemma integral_4r_minus_abs (r : ℝ) (hr0 : 0 ≤ r) :
    ∫ x in Set.Icc (-r) r, (4 * r - |x|) = 7 * r ^ 2 := by
  -- Let's first split the integral into two parts: from -r to 0 and from 0 to r.
  have h_split : ∫ x in Set.Icc (-r) r, 4 * r - |x| = (∫ x in Set.Icc (-r) 0, 4 * r - |x|) + (∫ x in Set.Icc 0 r, 4 * r - |x|) := by
    norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, hr0 ];
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
  rw [ h_split, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc ];
  rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ abs_of_nonpos hx.2 ] ] ; rw [ ← intervalIntegral.integral_of_le ( by linarith ), MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ abs_of_nonneg hx.1.le ] ] ; rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; norm_num ; ring;
  rw [ intervalIntegral.integral_add, intervalIntegral.integral_sub ] <;> norm_num ; ring

/-- Key integral: ∫_{-r}^r 2*(2r - |x|) dx = 6r². Actually the fill is 12r² = 3*(2r)²
    by Stevens formula. Let's state it directly. -/
lemma stevens_formula (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    (12 : ℝ) * r ^ 2 = 3 * (2 * r) ^ 2 := by ring

/-
**Sim-A5 / Job 1b, Lemma 1.** Volume of the intersection of two closed balls
    on T1 = AddCircle 1: for r ≤ 1/4 and s = dist a b ≤ r,
    `volume(closedBall a r ∩ closedBall b r) = 2r - s`.
-/
lemma volume_closedBall_inter_T1 (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (a b : T1) (hs : dist a b ≤ r) :
    volume (Metric.closedBall a r ∩ Metric.closedBall b r)
    = ENNReal.ofReal (2 * r - dist a b) := by
  revert hs;
  -- By translation invariance of the measure, we can assume without loss of generality that $a = 0$.
  suffices h_trans : ∀ (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) (b : T1), dist 0 b ≤ r →
      volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall b r) = ENNReal.ofReal (2 * r - dist 0 b) by
        intro hs
        have h_eq : volume (Metric.closedBall a r ∩ Metric.closedBall b r) = volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (b - a) r) := by
          rw [ ← MeasureTheory.measure_preimage_add_right ];
          swap;
          exact a;
          simp +decide [ dist_eq_norm, sub_eq_add_neg ];
        convert h_trans r hr0 hr ( b - a ) _ using 1 <;> simp_all +decide [ dist_eq_norm' ];
  intro r hr0 hr b hb
  have h_lift : ∃ b' : ℝ, b = QuotientAddGroup.mk b' ∧ |b'| ≤ r := by
    obtain ⟨ b', hb' ⟩ := QuotientAddGroup.mk_surjective b;
    rw [ ← hb' ] at hb;
    norm_num [ dist_eq_norm, AddCircle.norm_eq ] at hb;
    refine' ⟨ b' - round b', _, _ ⟩ <;> norm_num [ hb' ];
    · norm_num [ sub_eq_add_neg, AddCircle ];
    · exact hb;
  obtain ⟨ b', rfl, hb' ⟩ := h_lift;
  have h_lift : volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b') r) = volume (Set.preimage (QuotientAddGroup.mk : ℝ → T1) (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b') r) ∩ Set.Ioc (-1 / 2) (1 / 2)) := by
    have h_lift : MeasureTheory.MeasurePreserving (QuotientAddGroup.mk : ℝ → T1) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc (-1 / 2) (1 / 2))) MeasureTheory.volume := by
      convert AddCircle.measurePreserving_mk 1 ( -1 / 2 ) using 1 ; norm_num;
    rw [ ← h_lift.measure_preimage ];
    · norm_num;
    · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_closedBall ) ( measurableSet_closedBall ) );
  -- The preimage of the intersection of the two closed balls under the quotient map is the intersection of the preimages of the closed balls.
  have h_preimage : Set.preimage (QuotientAddGroup.mk : ℝ → T1) (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b') r) ∩ Set.Ioc (-1 / 2) (1 / 2) = Set.Icc (-r) r ∩ Set.Icc (b' - r) (b' + r) ∩ Set.Ioc (-1 / 2) (1 / 2) := by
    ext x;
    simp +decide [ Metric.mem_closedBall, dist_eq_norm ];
    intro hx₁ hx₂; erw [ AddCircle.norm_eq, AddCircle.norm_eq ] ; norm_num [ abs_le ] ;
    constructor <;> intro h;
    · rcases u : round x with ⟨ _ | _ | u ⟩ <;> norm_num [ u ] at h ⊢;
      · rcases u : round ( x - b' ) with ⟨ _ | _ | u ⟩ <;> norm_num [ u ] at h ⊢;
        · grind;
        · constructor <;> constructor <;> linarith [ abs_le.mp hb' ];
        · constructor <;> constructor <;> linarith [ abs_le.mp hb' ];
        · constructor <;> constructor <;> linarith [ abs_le.mp hb' ];
      · linarith [ abs_le.mp hb' ];
      · linarith [ abs_le.mp hb' ];
      · linarith [ abs_le.mp hb' ];
    · norm_num [ show round x = 0 by exact round_eq_zero_iff.mpr ⟨ by linarith, by linarith ⟩, show round ( x - b' ) = 0 by exact round_eq_zero_iff.mpr ⟨ by linarith, by linarith ⟩ ] ; constructor <;> constructor <;> linarith;
  rw [ h_lift, h_preimage ];
  rw [ show ( Set.Icc ( -r ) r ∩ Set.Icc ( b' - r ) ( b' + r ) ∩ Set.Ioc ( -1 / 2 ) ( 1 / 2 ) ) = Set.Icc ( Max.max ( -r ) ( b' - r ) ) ( Min.min r ( b' + r ) ) from ?_ ];
  · norm_num [ dist_eq_norm, AddCircle.norm_eq ];
    rw [ show round b' = 0 by exact round_eq_zero_iff.mpr ⟨ by linarith [ abs_le.mp hb' ], by linarith [ abs_le.mp hb' ] ⟩ ] ; norm_num ; ring;
    cases max_cases ( -r ) ( b' - r ) <;> cases min_cases r ( b' + r ) <;> cases abs_cases b' <;> exact congr_arg _ ( by linarith );
  · grind +qlia

/-
**Sim-A5 / Job 1b, Lemma 2.** 1D triangle probability:
    `volume(triangleSet r) = 3r²` on (T1)³ for `r ≤ 1/4`.
-/
lemma volume_triangleSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (triangleSet r) = ENNReal.ofReal (3 * r ^ 2) := by
  -- The volume of the triangleSet r is equal to the integral of the product of the indicators of the closed balls.
  have h_volume : volume (triangleSet r) = ∫⁻ (u : Fin 3 → T1), (if dist (u 0) (u 1) ≤ r ∧ dist (u 0) (u 2) ≤ r ∧ dist (u 1) (u 2) ≤ r then 1 else 0) := by
    rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    exact?;
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) );
    · exact Filter.Eventually.of_forall fun x => by unfold triangleSet; aesop;
  -- By Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫⁻ (u : Fin 3 → T1), (if dist (u 0) (u 1) ≤ r ∧ dist (u 0) (u 2) ≤ r ∧ dist (u 1) (u 2) ≤ r then 1 else 0) = ∫⁻ (u0 : T1), ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), (if dist u0 u1 ≤ r ∧ dist u0 u2 ≤ r ∧ dist u1 u2 ≤ r then 1 else 0) := by
    have h_fubini : ∀ {f : (Fin 3 → T1) → ENNReal}, Measurable f → ∫⁻ (u : Fin 3 → T1), f u = ∫⁻ (u0 : T1), ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), f ![u0, u1, u2] := by
      intro f hf;
      have h_fubini : ∫⁻ (u : Fin 3 → T1), f u = ∫⁻ (u : T1 × T1 × T1), f ![u.1, u.2.1, u.2.2] := by
        have h_fubini : MeasureTheory.MeasureSpace.volume = MeasureTheory.Measure.map (fun u : T1 × T1 × T1 => ![u.1, u.2.1, u.2.2]) (MeasureTheory.Measure.prod (MeasureTheory.MeasureSpace.volume) (MeasureTheory.Measure.prod (MeasureTheory.MeasureSpace.volume) (MeasureTheory.MeasureSpace.volume))) := by
          simp +decide [ MeasureTheory.MeasureSpace.volume ];
          erw [ MeasureTheory.Measure.pi_eq ];
          intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · simp +decide [ Set.preimage, Fin.prod_univ_three ];
            simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
            erw [ show { a : T1 × T1 × T1 | a.1 ∈ s 0 } ∩ ( { a : T1 × T1 × T1 | a.2.1 ∈ s 1 } ∩ { a : T1 × T1 × T1 | a.2.2 ∈ s 2 } ) = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; simp +decide [ mul_assoc ];
          · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
          · exact MeasurableSet.univ_pi hs;
        rw [ h_fubini, MeasureTheory.lintegral_map ];
        · rfl;
        · exact hf;
        · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
      erw [ h_fubini, MeasureTheory.lintegral_prod ];
      · congr! 2;
        erw [ MeasureTheory.lintegral_prod ];
        exact hf.comp ( measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd ] ) |> Measurable.aemeasurable;
      · exact hf.aemeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ) );
    convert h_fubini _;
    refine' Measurable.ite _ measurable_const measurable_const;
    exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) );
  -- Fix $u_0$ and integrate over $u_1$ and $u_2$.
  have h_integral : ∀ u0 : T1, ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), (if dist u0 u1 ≤ r ∧ dist u0 u2 ≤ r ∧ dist u1 u2 ≤ r then 1 else 0) = ∫⁻ (u1 : T1), if dist u0 u1 ≤ r then ENNReal.ofReal (2 * r - dist u0 u1) else 0 := by
    intro u0; congr; ext u1; by_cases hu1 : dist u0 u1 ≤ r <;> simp +decide [ hu1 ] ;
    rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    change ∫⁻ u2 in Metric.closedBall u0 r ∩ Metric.closedBall u1 r, 1 = ENNReal.ofReal ( 2 * r - dist u0 u1 );
    · convert volume_closedBall_inter_T1 r hr0 hr u0 u1 hu1 using 1 ; norm_num;
    · exact measurableSet_closedBall.inter measurableSet_closedBall;
    · norm_num [ Filter.EventuallyEq, Set.indicator ];
      simp +decide only [dist_comm];
      exact Filter.Eventually.of_forall fun _ => trivial;
  -- The integral of (2r - |x|) over [-r, r] is 3r².
  have h_integral_value : ∫⁻ (x : ℝ) in Set.Icc (-r) r, ENNReal.ofReal (2 * r - |x|) = ENNReal.ofReal (3 * r ^ 2) := by
    rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · rw [ integral_2r_minus_abs ];
      linarith;
    · exact Continuous.integrableOn_Icc ( by continuity );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using sub_nonneg_of_le <| by cases abs_cases x <;> linarith [ hx.1, hx.2 ] ;
  -- By translation invariance, the integral over $u_1$ is the same for all $u_0$.
  have h_translation_invariance : ∀ u0 : T1, ∫⁻ (u1 : T1), (if dist u0 u1 ≤ r then ENNReal.ofReal (2 * r - dist u0 u1) else 0) = ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then ENNReal.ofReal (2 * r - dist 0 u1) else 0) := by
    intro u0
    have h_translation_invariance : ∀ f : T1 → ENNReal, (∫⁻ (u1 : T1), f u1) = (∫⁻ (u1 : T1), f (u1 + u0)) := by
      intro f;
      rw [ ← MeasureTheory.lintegral_add_right_eq_self ];
    convert h_translation_invariance _ using 3 ; norm_num [ dist_eq_norm ];
  -- The integral over $u_1$ is the same as the integral over $[-r, r]$.
  have h_integral_u1 : ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then ENNReal.ofReal (2 * r - dist 0 u1) else 0) = ∫⁻ (x : ℝ) in Set.Icc (-r) r, ENNReal.ofReal (2 * r - |x|) := by
    have h_integral_u1 : ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then ENNReal.ofReal (2 * r - dist 0 u1) else 0) = ∫⁻ (x : ℝ) in Set.Icc (-1 / 2) (1 / 2), (if |x| ≤ r then ENNReal.ofReal (2 * r - |x|) else 0) := by
      have h_integral_u1 : ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then ENNReal.ofReal (2 * r - dist 0 u1) else 0) = ∫⁻ (x : ℝ) in Set.Icc (-1 / 2) (1 / 2), (if dist 0 (QuotientAddGroup.mk x : T1) ≤ r then ENNReal.ofReal (2 * r - dist 0 (QuotientAddGroup.mk x : T1)) else 0) := by
        have h_integral_u1 : MeasureTheory.MeasurePreserving (fun x : ℝ => QuotientAddGroup.mk x : ℝ → T1) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (-1 / 2) (1 / 2))) MeasureTheory.volume := by
          convert AddCircle.measurePreserving_mk ( 1 : ℝ ) ( -1 / 2 ) using 1;
          norm_num [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ];
        rw [ ← h_integral_u1.lintegral_comp ];
        exact Measurable.ite ( measurableSet_le ( measurable_const.dist measurable_id' ) measurable_const ) ( Measurable.ennreal_ofReal ( measurable_const.sub ( measurable_const.dist measurable_id' ) ) ) measurable_const;
      convert h_integral_u1 using 1;
      norm_num [ dist_eq_norm, AddCircle.norm_eq ];
      rw [ MeasureTheory.lintegral_congr_ae ];
      filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx;
      norm_num [ round_eq ];
      rcases eq_or_ne ⌊x + 1 / 2⌋ 0 with h | h <;> norm_num [ h ];
      norm_num [ show x = 1 / 2 by exact le_antisymm hx.2 ( by exact le_of_not_gt fun h' => h <| Int.floor_eq_iff.mpr ⟨ by norm_num; linarith [ hx.1, hx.2 ], by norm_num; linarith [ hx.1, hx.2 ] ⟩ ) ] at *;
    rw [ h_integral_u1, ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
    · congr with x ; norm_num [ Set.indicator ] ; split_ifs <;> norm_num;
      · exact False.elim <| ‹¬ ( -r ≤ x ∧ x ≤ r ) › ⟨ by linarith [ abs_le.mp ‹_› ], by linarith [ abs_le.mp ‹_› ] ⟩;
      · cases abs_cases x <;> linarith;
      · exact False.elim <| ‹¬ ( - ( 1 / 2 ) ≤ x ∧ x ≤ 1 / 2 ) › ⟨ by linarith, by linarith ⟩;
    · norm_num;
    · norm_num;
  aesop

/-
Pure ℝ helper: the set {x | ∃ t, |t| ≤ r ∧ |t-b| ≤ r ∧ |t-x| ≤ r}
equals [b-2r, 2r] when 0 ≤ b ≤ 2r.
-/
lemma fill_fiber_real_nonneg (r b : ℝ) (hr0 : 0 ≤ r) (hb0 : 0 ≤ b) (hb : b ≤ 2 * r) :
    {x : ℝ | ∃ t, |t| ≤ r ∧ |t - b| ≤ r ∧ |t - x| ≤ r}
    = Set.Icc (b - 2 * r) (2 * r) := by
  -- Let's prove both inclusions.
  apply Set.eq_of_subset_of_subset;
  · exact fun x hx => by rcases hx with ⟨ t, ht₁, ht₂, ht₃ ⟩ ; constructor <;> linarith [ abs_le.mp ht₁, abs_le.mp ht₂, abs_le.mp ht₃ ] ;
  · intro x hx; use Min.min ( Max.max ( x - r ) ( b - r ) ) r; simp_all +decide [ abs_le ] ;
    grind

/-
The length of [b-2r, 2r] is 4r - b.
-/
lemma fill_fiber_real_length (r b : ℝ) (hr0 : 0 ≤ r) (hb0 : 0 ≤ b) (hb : b ≤ 2 * r) :
    volume (Set.Icc (b - 2 * r) (2 * r) : Set ℝ) = ENNReal.ofReal (4 * r - b) := by
  convert Real.volume_Icc using 1 ; ring

/-
Helper: volume of the "fill fiber" set. For fixed a, b ∈ T1 with
    dist a b ≤ 2r and r ≤ 1/4, the set of c such that
    closedBall(a,r) ∩ closedBall(b,r) ∩ closedBall(c,r) is nonempty
    has volume 4r - dist a b.

    On ℝ (via quotient): WLOG a=0, b=d with 0 ≤ d ≤ 2r.
    B(0,r) ∩ B(d,r) = [d-r, r]. The Minkowski sum
    ⋃_{z ∈ [d-r,r]} [z-r, z+r] = [d-2r, 2r], length = 4r - d.
    Since 4r ≤ 1, no wrap-around on the circle.

The fill fiber set equals a specific closedBall on T1.
On ℝ: ⋃_{z ∈ [b'-r, r]} B(z,r) = [b'-2r, 2r] = closedBall(b'/2, 2r - b'/2).
On T1: same since everything fits in [-1/2, 1/2] for r ≤ 1/4.

For |x| ≤ 1/2, the norm on AddCircle 1 is just |x|.
-/
lemma T1_norm_mk_of_abs_le (x : ℝ) (hx : |x| ≤ 1/2) :
    ‖(QuotientAddGroup.mk x : T1)‖ = |x| := by
  -- By definition of norm in AddCircle 1, we have ‖↑x‖ = |x - round x|.
  have h_norm : ‖(x : AddCircle (1 : ℝ))‖ = |x - round x * 1| := by
    grind +suggestions;
  rcases eq_or_ne ( round x ) 0 <;> simp_all +decide [ abs_le ];
  norm_num [ show x = 1 / 2 by linarith ] at *

/-
For |x - y| ≤ 1/2, the dist on T1 is |x - y|.
-/
lemma T1_dist_mk_of_abs_le (x y : ℝ) (hxy : |x - y| ≤ 1/2) :
    dist (QuotientAddGroup.mk x : T1) (QuotientAddGroup.mk y : T1) = |x - y| := by
  convert T1_norm_mk_of_abs_le ( x - y ) hxy using 1

lemma fill_fiber_subset_ball (r b' : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) (hb'0 : 0 ≤ b') (hb' : b' ≤ r) :
    {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist c z ≤ r}
    ⊆ Metric.closedBall (QuotientAddGroup.mk (b'/2) : T1) (2*r - b'/2) := by
  intro c hc
  obtain ⟨z, hz⟩ := hc
  have h1 : dist (QuotientAddGroup.mk (b' / 2) : T1) z ≤ r - b' / 2 := by
    have h1 : ∃ t : ℝ, |t| ≤ r ∧ dist (QuotientAddGroup.mk t : T1) z = 0 := by
      obtain ⟨ t, ht ⟩ := QuotientAddGroup.mk_surjective z;
      rw [ ← ht ] at hz ⊢; norm_num [ AddCircle.norm_eq ] at hz ⊢;
      exact ⟨ t - round t, by simpa using hz.1, by simp +decide [ sub_eq_iff_eq_add ] ⟩;
    obtain ⟨ t, ht₁, ht₂ ⟩ := h1; simp_all +decide [ dist_eq_norm ] ;
    have h1 : ‖(QuotientAddGroup.mk (b' / 2) : T1) - (QuotientAddGroup.mk t : T1)‖ = |b' / 2 - t| := by
      apply T1_norm_mk_of_abs_le;
      exact abs_le.mpr ⟨ by norm_num1 at *; linarith [ abs_le.mp ht₁ ], by norm_num1 at *; linarith [ abs_le.mp ht₁ ] ⟩;
    have h2 : ‖(QuotientAddGroup.mk b' : T1) - (QuotientAddGroup.mk t : T1)‖ = |b' - t| := by
      convert T1_dist_mk_of_abs_le b' t _ using 1;
      exact abs_le.mpr ⟨ by linarith [ abs_le.mp ht₁ ], by linarith [ abs_le.mp ht₁ ] ⟩;
    grind +revert;
  have := dist_triangle_right c ( QuotientAddGroup.mk ( b' / 2 ) ) z; norm_num at *; linarith;

lemma ball_subset_fill_fiber (r b' : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) (hb'0 : 0 ≤ b') (hb' : b' ≤ 2 * r) :
    Metric.closedBall (QuotientAddGroup.mk (b'/2) : T1) (2*r - b'/2)
    ⊆ {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist c z ≤ r} := by
  intro c hc
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c = QuotientAddGroup.mk c' ∧ |c' - b' / 2| ≤ 2 * r - b' / 2 := by
    rcases c with ⟨ c ⟩;
    erw [ Metric.mem_closedBall, dist_eq_norm ] at hc;
    erw [ AddCircle.norm_eq ] at hc;
    refine' ⟨ c - round ( c - b' / 2 ), _, _ ⟩ <;> norm_num at *;
    · erw [ QuotientAddGroup.eq ] ; norm_num [ AddSubgroup.mem_zmultiples_iff ];
      exact ⟨ -round ( c - b' / 2 ), by push_cast; ring ⟩;
    · grind;
  refine' ⟨ QuotientAddGroup.mk ( Max.max ( b' - r ) ( Min.min r c' ) ), _, _, _ ⟩ <;> simp_all +decide [ dist_eq_norm ];
  · rw [ AddCircle.norm_eq ];
    rw [ show round ( 1⁻¹ * max ( b' - r ) ( min r c' ) ) = 0 by exact round_eq_zero_iff.mpr ⟨ by cases max_cases ( b' - r ) ( min r c' ) <;> cases min_cases r c' <;> linarith, by cases max_cases ( b' - r ) ( min r c' ) <;> cases min_cases r c' <;> linarith ⟩ ] ; norm_num;
    grind;
  · erw [ QuotientAddGroup.norm_mk ];
    refine' le_trans ( Metric.infDist_le_dist_of_mem _ ) _ <;> norm_num [ dist_eq_norm ];
    exacts [ 0, by norm_num, by rw [ abs_le ] ; constructor <;> cases max_cases ( b' - r ) ( Min.min r c' ) <;> cases min_cases r c' <;> linarith ];
  · erw [ QuotientAddGroup.norm_mk ] at *;
    refine' le_trans ( Metric.infDist_le_dist_of_mem _ ) _ <;> norm_num [ dist_eq_norm ] at *;
    exacts [ 0, by norm_num, by rw [ abs_le ] ; constructor <;> cases max_cases ( b' - r ) ( Min.min r c' ) <;> cases min_cases r c' <;> linarith [ abs_le.mp hc'.2 ] ]

lemma fill_fiber_volume (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (a b : T1) (hd : dist a b ≤ r) :
    volume {c : T1 | ∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r}
    = ENNReal.ofReal (4 * r - dist a b) := by
  obtain ⟨b', hb'⟩ : ∃ b' : ℝ, |b'| ≤ r ∧ dist a b = |b'| ∧ b = a + QuotientAddGroup.mk b' := by
    -- By definition of distance on the circle, there exists some $b' \in [-1/2, 1/2]$ such that $b = a + b'$ and $|b'| = dist a b$.
    obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b = a + QuotientAddGroup.mk b' ∧ |b'| ≤ 1 / 2 ∧ dist a b = |b'| := by
      obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b = a + QuotientAddGroup.mk b' ∧ |b'| ≤ 1 / 2 := by
        obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b = a + QuotientAddGroup.mk b' := by
          obtain ⟨ x, hx ⟩ := QuotientAddGroup.mk_surjective a; obtain ⟨ y, hy ⟩ := QuotientAddGroup.mk_surjective b; use y - x; aesop;
        refine' ⟨ b' - ⌊b' + 1 / 2⌋, _, _ ⟩ <;> norm_num [ hb' ];
        · erw [ sub_eq_add_neg ] ; norm_num [ QuotientAddGroup.eq ];
        · exact abs_le.mpr ⟨ by linarith [ Int.floor_le ( b' + 1 / 2 ) ], by linarith [ Int.lt_floor_add_one ( b' + 1 / 2 ) ] ⟩;
      use b';
      simp_all +decide [ dist_eq_norm ];
      convert T1_norm_mk_of_abs_le b' _ using 1 ; norm_num at * ; linarith;
    exact ⟨ b', by linarith, hb'.2.2, hb'.1 ⟩;
  -- By translation invariance, we can assume without loss of generality that $a = 0$.
  suffices h_trans : volume {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist c z ≤ r} = ENNReal.ofReal (4 * r - |b'|) by
    have h_trans : volume {c : T1 | ∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r} = volume {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist c z ≤ r} := by
      have h_trans : ∀ c : T1, (∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r) ↔ (∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist (c - a) z ≤ r) := by
        intro c
        constructor
        intro h
        obtain ⟨z, hz⟩ := h
        use z - a
        simp [hz, hb'];
        · convert hz.2.1 using 1 ; rw [ hb'.2.2 ] ; abel_nf;
        · rintro ⟨ z, hz₁, hz₂, hz₃ ⟩ ; use z + a; simp_all +decide [ dist_eq_norm ] ;
          exact ⟨ by convert hz₂ using 1; abel_nf, by convert hz₃ using 1; abel_nf ⟩;
      rw [ show { c : T1 | ∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r } = ( fun c => c - a ) ⁻¹' { c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist ( QuotientAddGroup.mk b' ) z ≤ r ∧ dist c z ≤ r } by ext; aesop ];
      rw [ ← MeasureTheory.measure_preimage_add_right ];
      swap;
      exact a;
      simp +decide [ sub_eq_add_neg ];
    aesop;
  -- By the results of the previous steps, we know that the set is equal to the closed ball centered at $b'/2$ with radius $2r - b'/2$.
  have h_eq : {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist c z ≤ r} = Metric.closedBall (QuotientAddGroup.mk (b' / 2) : T1) (2 * r - |b'| / 2) := by
    refine' Set.Subset.antisymm _ _;
    · by_cases hb'_nonneg : 0 ≤ b';
      · convert fill_fiber_subset_ball r b' hr0 hr hb'_nonneg ( by linarith [ abs_of_nonneg hb'_nonneg ] ) using 1;
        rw [ abs_of_nonneg hb'_nonneg ];
      · have := fill_fiber_subset_ball r ( -b' ) hr0 hr ( by linarith ) ( by linarith [ abs_of_neg ( not_le.mp hb'_nonneg ) ] );
        simp_all +decide [ abs_of_neg, neg_div ];
        intro c hc; specialize this ( show ∃ z : T1, ‖z‖ ≤ r ∧ dist ( -↑b' ) z ≤ r ∧ dist ( -c ) z ≤ r from by
                                        obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := hc; use -z; simp_all +decide [ dist_neg ] ; ) ; simp_all +decide [ dist_neg ] ;
    · by_cases hb'_nonneg : 0 ≤ b';
      · convert ball_subset_fill_fiber r b' hr0 hr hb'_nonneg ( by linarith [ abs_of_nonneg hb'_nonneg ] ) using 1;
        rw [ abs_of_nonneg hb'_nonneg ];
      · have := ball_subset_fill_fiber r ( -b' ) hr0 hr ( by linarith ) ( by linarith [ abs_of_neg ( not_le.mp hb'_nonneg ) ] );
        intro c hc; specialize this ( show ( -c : T1 ) ∈ Metric.closedBall ( ↑ ( -b' / 2 ) ) ( 2 * r - -b' / 2 ) from ?_ ) ; simp_all +decide [ neg_div, dist_neg ] ;
        · linarith [ abs_of_neg hb'_nonneg ];
        · obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := this; use -z; simp_all +decide [ dist_neg ] ;
  rw [ h_eq, AddCircle.volume_closedBall ];
  rw [ min_eq_right ] <;> ring ; linarith [ abs_nonneg b' ]

lemma volume_edgeFillSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (edgeFillSet r) = ENNReal.ofReal (7 * r ^ 2) := by
  -- Examine the integrand, projected as a pushforward to the ℝ factor.
  have h_proj_lintegral : ∫⁻ x : T1, ∫⁻ y : T1, ∫⁻ z : T1, (if dist x y ≤ r ∧ ∃ a : T1, dist x a ≤ r ∧ dist y a ≤ r ∧ dist z a ≤ r then 1 else 0) ∂MeasureTheory.volume ∂MeasureTheory.volume ∂MeasureTheory.volume = ENNReal.ofReal (7 * r ^ 2) := by
    have h_proj_lintegral : ∫⁻ x : T1, ∫⁻ y : T1, (if dist x y ≤ r then ENNReal.ofReal (4 * r - dist x y) else 0) ∂MeasureTheory.volume ∂MeasureTheory.volume = ENNReal.ofReal (7 * r ^ 2) := by
      have h_proj_lintegral : ∫⁻ x : T1, ∫⁻ y : T1, (if dist x y ≤ r then ENNReal.ofReal (4 * r - dist x y) else 0) ∂MeasureTheory.volume ∂MeasureTheory.volume = ∫⁻ x : T1, ∫⁻ y : T1, (if dist 0 y ≤ r then ENNReal.ofReal (4 * r - dist 0 y) else 0) ∂MeasureTheory.volume ∂MeasureTheory.volume := by
        have h_translation_invariance : ∀ x : T1, ∫⁻ y : T1, (if dist x y ≤ r then ENNReal.ofReal (4 * r - dist x y) else 0) ∂MeasureTheory.volume = ∫⁻ y : T1, (if dist 0 y ≤ r then ENNReal.ofReal (4 * r - dist 0 y) else 0) ∂MeasureTheory.volume := by
          intro x;
          rw [ ← MeasureTheory.lintegral_add_right_eq_self ];
          swap;
          exact x;
          simp +decide [ dist_eq_norm, add_comm x ];
        aesop;
      -- Let's simplify the integral.
      have h_integral_simplified : ∫⁻ y : T1, (if dist 0 y ≤ r then ENNReal.ofReal (4 * r - dist 0 y) else 0) ∂MeasureTheory.volume = ∫⁻ y : ℝ in Set.Icc (-r) r, ENNReal.ofReal (4 * r - |y|) ∂MeasureTheory.volume := by
        have h_integral_simplified : ∫⁻ y : T1, (if dist 0 y ≤ r then ENNReal.ofReal (4 * r - dist 0 y) else 0) ∂MeasureTheory.volume = ∫⁻ y : ℝ in Set.Icc (-1 / 2) (1 / 2), (if dist 0 (QuotientAddGroup.mk y : T1) ≤ r then ENNReal.ofReal (4 * r - dist 0 (QuotientAddGroup.mk y : T1)) else 0) ∂MeasureTheory.volume := by
          have h_integral_simplified : ∫⁻ y : T1, (if dist 0 y ≤ r then ENNReal.ofReal (4 * r - dist 0 y) else 0) ∂MeasureTheory.volume = ∫⁻ y : ℝ in Set.Ico (-1 / 2) (1 / 2), (if dist 0 (QuotientAddGroup.mk y : T1) ≤ r then ENNReal.ofReal (4 * r - dist 0 (QuotientAddGroup.mk y : T1)) else 0) ∂MeasureTheory.volume := by
            have := @AddCircle.lintegral_preimage;
            specialize this 1 ( -1 / 2 ) ( fun y => if dist 0 y ≤ r then ENNReal.ofReal ( 4 * r - dist 0 y ) else 0 ) ; norm_num at *;
            rw [ ← this, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc ];
          rw [ h_integral_simplified, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Icc ];
        rw [ h_integral_simplified, ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
        · congr with x ; norm_num [ Set.indicator ];
          grind +suggestions;
        · norm_num;
        · norm_num;
      have h_integral_evaluated : ∫⁻ y : ℝ in Set.Icc (-r) r, ENNReal.ofReal (4 * r - |y|) = ENNReal.ofReal (∫ y in Set.Icc (-r) r, (4 * r - |y|)) := by
        rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · exact Continuous.integrableOn_Icc ( by continuity );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with y hy using sub_nonneg_of_le <| by cases abs_cases y <;> linarith [ hy.1, hy.2 ] ;
      have := integral_4r_minus_abs r hr0; simp_all +decide [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] ;
    convert h_proj_lintegral using 1;
    refine' MeasureTheory.lintegral_congr fun x => MeasureTheory.lintegral_congr fun y => _;
    split_ifs <;> simp_all +decide [ dist_comm ];
    · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      change ∫⁻ a in { c : T1 | ∃ a : T1, dist x a ≤ r ∧ dist y a ≤ r ∧ dist c a ≤ r }, 1 ∂MeasureTheory.volume = ENNReal.ofReal ( 4 * r - dist x y );
      · convert fill_fiber_volume r hr0 ( by norm_num at *; linarith ) x y ‹_› using 1;
        norm_num;
      · refine' IsClosed.measurableSet _;
        have h_closed : IsClosed (Set.image (fun p : T1 × T1 => p.2) {p : T1 × T1 | dist x p.1 ≤ r ∧ dist y p.1 ≤ r ∧ dist p.2 p.1 ≤ r}) := by
          apply_rules [ IsCompact.isClosed, IsCompact.image ];
          · refine' IsCompact.of_isClosed_subset ( isCompact_univ.prod isCompact_univ ) _ _;
            · exact IsClosed.inter ( isClosed_le ( continuous_const.dist continuous_fst ) continuous_const ) ( IsClosed.inter ( isClosed_le ( continuous_const.dist continuous_fst ) continuous_const ) ( isClosed_le ( continuous_snd.dist continuous_fst ) continuous_const ) );
            · exact fun p hp => ⟨ Set.mem_univ _, Set.mem_univ _ ⟩;
          · exact continuous_snd;
        convert h_closed using 1;
        ext; simp [Set.mem_image];
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
    · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_zero ];
      filter_upwards [ ] with z using if_neg <| not_and_of_not_left _ <| by linarith;
  rw [ ← h_proj_lintegral ];
  have h_volume_eq_lintegral : ∀ (S : Set (Fin 3 → T1)), MeasurableSet S → volume S = ∫⁻ (x : T1), ∫⁻ (y : T1), ∫⁻ (z : T1), (if (fun u : Fin 3 → T1 => ![u 0, u 1, u 2]) ![x, y, z] ∈ S then 1 else 0) ∂MeasureTheory.volume ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    intro S hS
    have h_volume_eq_lintegral : volume S = ∫⁻ (u : Fin 3 → T1), (if u ∈ S then 1 else 0) ∂MeasureTheory.volume := by
      erw [ MeasureTheory.lintegral_indicator ] <;> aesop;
    have h_volume_eq_lintegral : volume S = ∫⁻ (u : T1 × T1 × T1), (if (fun u : T1 × T1 × T1 => ![u.1, u.2.1, u.2.2]) u ∈ S then 1 else 0) ∂MeasureTheory.volume := by
      have h_volume_eq_lintegral : volume S = ∫⁻ (u : T1 × T1 × T1), (if (fun u : T1 × T1 × T1 => ![u.1, u.2.1, u.2.2]) u ∈ S then 1 else 0) ∂MeasureTheory.volume := by
        have h_equiv : (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → T1)) = MeasureTheory.Measure.map (fun u : T1 × T1 × T1 => ![u.1, u.2.1, u.2.2]) (MeasureTheory.volume : MeasureTheory.Measure (T1 × T1 × T1)) := by
          simp +decide [ MeasureTheory.MeasureSpace.volume ];
          erw [ MeasureTheory.Measure.pi_eq ];
          intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · simp +decide [ Set.preimage, Fin.prod_univ_three ];
            simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
            erw [ show { a : T1 × T1 × T1 | a.1 ∈ s 0 } ∩ ( { a : T1 × T1 × T1 | a.2.1 ∈ s 1 } ∩ { a : T1 × T1 × T1 | a.2.2 ∈ s 2 } ) = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; simp +decide [ mul_assoc ];
          · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
          · exact MeasurableSet.univ_pi hs
        rw [ h_volume_eq_lintegral, h_equiv, MeasureTheory.lintegral_map ];
        · exact Measurable.ite hS measurable_const measurable_const;
        · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
      convert h_volume_eq_lintegral using 1;
    erw [ h_volume_eq_lintegral, MeasureTheory.lintegral_prod ];
    · congr! 2;
      erw [ MeasureTheory.lintegral_prod ];
      · congr! 2;
      · refine' Measurable.aemeasurable _;
        refine' Measurable.ite _ measurable_const measurable_const;
        exact hS.preimage ( measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd ] );
    · exact Measurable.aemeasurable ( by exact Measurable.ite ( hS.preimage <| by exact Continuous.measurable <| by exact continuous_pi_iff.mpr fun i => by fin_cases i <;> [ exact continuous_fst; exact continuous_snd.fst; exact continuous_snd.snd ] ) measurable_const measurable_const );
  convert h_volume_eq_lintegral _ _;
  refine' MeasurableSet.inter _ _;
  · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
  · -- The set of points $z$ such that $dist(u_0, z) \leq r$, $dist(u_1, z) \leq r$, and $dist(u_2, z) \leq r$ is closed.
    have h_closed : IsClosed {u : Fin 3 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
      have h_closed : IsClosed {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
        exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
      have h_closed : IsClosed (Set.image (fun p : (Fin 3 → T1) × T1 => p.1) {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r}) := by
        apply_rules [ IsCompact.isClosed, IsCompact.image ];
        · exact IsCompact.of_isClosed_subset ( isCompact_univ ) h_closed ( Set.subset_univ _ );
        · exact continuous_fst;
      convert h_closed using 1;
      ext; simp [Set.mem_image];
    exact h_closed.measurableSet

/-- **Sim-A5 / Job 1b, Lemma 4.** 1D fill probability (Stevens 1939):
    `volume(fillSet r) = 12r²` on (T1)³ for `r ≤ 1/4`.

    PROVIDED SOLUTION
    Step 1. `fillSet r = {(u₀,u₁,u₂) : ∃ z, all three within r of z}`.
      By 1D Helly, this equals `{(u₀,u₁,u₂) : pairwise distances ≤ 2r}`
      restricted to `r ≤ 1/4` (so that `2r ≤ 1/2` and no wrap).
    Step 2. Stevens 1939 closed form for three uniform points on a circle of
      circumference 1, all in some arc of length `L = 2r`:
        `P[fill] = 3 · L² = 12 r²` for `L ≤ 1/2` (i.e. `r ≤ 1/4`).
      The factor 3 comes from disjoint events "u_i is the leftmost point in
      the covering arc" for i=0,1,2.
    Step 3. Lean route:
      (a) reduce via translation invariance to fix u 0 = 0;
      (b) compute the 2D integral over (x₁, x₂) ∈ T1² of the indicator
          `∃ z, |z|≤r ∧ |z-x₁|≤r ∧ |z-x₂|≤r`;
      (c) by `volume_closedBall_inter_T1`, conditional on x₁, the set of valid
          x₂ has measure `2r - |x₁| + ε` where ε accounts for second-arc; the
          full Stevens calculation gives 12r² total.
    Alternative: use `AddCircle.volume_arc_cover` if available, or model
    on Mathlib's `Probability.Distributions.Uniform` patterns.
-/
/-
Extended fill_fiber_volume for dist < 2r (strict). The formula 4r - dist is correct
for all dist < 2r when r ≤ 1/4; it fails only at dist = 2r with r = 1/4
(where wrap-around makes the fill fiber the whole circle).
For the integral computation, this boundary has measure 0.
-/
lemma fill_fiber_volume_lt (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (a b : T1) (hd : dist a b < 2 * r) :
    volume {c : T1 | ∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r}
    = ENNReal.ofReal (4 * r - dist a b) := by
  sorry

lemma volume_fillSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (fillSet r) = ENNReal.ofReal (12 * r ^ 2) := by
  sorry

/-! ## Coordinate factorisation -/

/-
Base case d=0: the coordinate-factored set is univ and volume is 1 = S^0.
-/
lemma volume_coordFactored_eq_pow_zero (S : Set (Fin 3 → T1)) (hS : MeasurableSet S) :
    volume ({pts : Fin 3 → (Fin 0 → T1) | ∀ i : Fin 0, (fun j : Fin 3 => pts j i) ∈ S} : Set (Fin 3 → Fin 0 → T1))
    = (volume S) ^ 0 := by
  simp +decide [ MeasureTheory.MeasureSpace.volume ];
  erw [ MeasureTheory.Measure.pi_univ ] ; norm_num

/-
The transpose map (fun f i j => f j i) is measurable from (Fin 3 → Fin d → T1) to (Fin d → Fin 3 → T1).
-/
lemma measurable_transpose (d : ℕ) :
    Measurable (fun (f : Fin 3 → Fin d → T1) (i : Fin d) (j : Fin 3) => f j i) := by
  fun_prop

/-
The transpose preserves the volume measure:
    map φ volume = volume where φ sends f to (fun i j => f j i).
-/
lemma volume_map_transpose (d : ℕ) :
    Measure.map (fun (f : Fin 3 → Fin d → T1) (i : Fin d) (j : Fin 3) => f j i) volume
    = (volume : Measure (Fin d → Fin 3 → T1)) := by
  apply MeasureTheory.Measure.ext;
  intro s hs
  by_contra h_contra;
  -- Since the measure is defined as the product of the measures on each coordinate, and the permutation of coordinates doesn't change the product measure, we have:
  have h_prod_measure : ∀ (s : Set (Fin d → Fin 3 → T1)), MeasurableSet s → (Measure.pi fun _ : Fin d => Measure.pi fun _ : Fin 3 => MeasureSpace.volume) s = (Measure.pi fun _ : Fin 3 => Measure.pi fun _ : Fin d => MeasureSpace.volume) (Set.preimage (fun f : Fin 3 → Fin d → T1 => fun i j => f j i) s) := by
    intro s hs
    have h_prod_measure : (Measure.pi fun _ : Fin d => Measure.pi fun _ : Fin 3 => MeasureSpace.volume) s = (Measure.pi (fun _ : Fin d × Fin 3 => MeasureSpace.volume)) (Set.preimage (fun f : Fin d × Fin 3 → T1 => fun i j => f (i, j)) s) := by
      have h_prod_measure : (Measure.pi (fun _ : Fin d × Fin 3 => MeasureSpace.volume)) = Measure.map (fun f : Fin d → Fin 3 → T1 => fun p : Fin d × Fin 3 => f p.1 p.2) (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin 3 => MeasureSpace.volume))) := by
        refine' MeasureTheory.Measure.pi_eq _;
        intro s hs; erw [ MeasureTheory.Measure.map_apply ];
        · rw [ show ( fun f p => f p.1 p.2 ) ⁻¹' Set.univ.pi s = Set.pi Set.univ fun i => Set.pi Set.univ fun j => s ( i, j ) from ?_ ];
          · rw [ MeasureTheory.Measure.pi_pi ];
            rw [ Finset.prod_congr rfl fun i _ => MeasureTheory.Measure.pi_pi _ _ ];
            rw [ ← Finset.prod_product' ];
            refine' Finset.prod_bij ( fun x _ => ( x.1, x.2 ) ) _ _ _ _ <;> simp +decide;
          · grind;
        · fun_prop;
        · exact MeasurableSet.univ_pi hs;
      rw [ h_prod_measure, Measure.map_apply ];
      · grind;
      · fun_prop;
      · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
    have h_prod_measure : (Measure.pi (fun _ : Fin d × Fin 3 => MeasureSpace.volume)) (Set.preimage (fun f : Fin d × Fin 3 → T1 => fun i j => f (i, j)) s) = (Measure.pi (fun _ : Fin 3 × Fin d => MeasureSpace.volume)) (Set.preimage (fun f : Fin 3 × Fin d → T1 => fun i j => f (j, i)) (Set.preimage (fun f : Fin d → Fin 3 → T1 => fun i j => f i j) s)) := by
      have h_prod_measure : Measure.pi (fun _ : Fin 3 × Fin d => MeasureSpace.volume) = Measure.map (fun f : Fin d × Fin 3 → T1 => fun p : Fin 3 × Fin d => f (p.2, p.1)) (Measure.pi (fun _ : Fin d × Fin 3 => MeasureSpace.volume)) := by
        refine' MeasureTheory.Measure.pi_eq _;
        intro s hs; erw [ MeasureTheory.Measure.map_apply ];
        · rw [ show ( fun f p => f ( p.2, p.1 ) ) ⁻¹' Set.univ.pi s = Set.univ.pi ( fun p => s ( p.2, p.1 ) ) from ?_, MeasureTheory.Measure.pi_pi ];
          · conv_rhs => rw [ ← Equiv.prod_comp ( Equiv.prodComm _ _ ) ] ;
            rfl;
          · grind;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · exact MeasurableSet.univ_pi hs;
      rw [ h_prod_measure, Measure.map_apply ];
      · grind;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
    convert h_prod_measure using 1;
    erw [ MeasureTheory.Measure.pi_eq ];
    rotate_right;
    exact MeasureTheory.Measure.map ( fun f : Fin 3 × Fin d → T1 => fun i j => f ( i, j ) ) ( MeasureTheory.Measure.pi fun _ : Fin 3 × Fin d => MeasureTheory.MeasureSpace.volume );
    · rw [ MeasureTheory.Measure.map_apply ];
      · congr! 1;
      · fun_prop;
      · exact measurable_pi_lambda _ ( fun _ => measurable_pi_lambda _ ( fun _ => measurable_pi_apply _ |> Measurable.comp <| measurable_pi_apply _ ) ) hs;
    · intro s hs; erw [ MeasureTheory.Measure.map_apply ];
      · convert MeasureTheory.Measure.pi_pi _ _ using 1;
        · rw [ MeasureTheory.Measure.pi_eq ];
          rotate_right;
          exact MeasureTheory.Measure.map ( fun f : Fin 3 → Fin d → T1 => fun p => f p.1 p.2 ) ( MeasureTheory.Measure.pi fun _ : Fin 3 => MeasureTheory.Measure.pi fun _ : Fin d => MeasureTheory.MeasureSpace.volume );
          · rw [ MeasureTheory.Measure.map_apply ];
            · congr! 1;
            · fun_prop;
            · simp +decide [ Set.preimage, hs ];
              exact Measurable.forall fun i => measurableSet_preimage ( measurable_pi_lambda _ fun j => measurable_pi_apply _ ) ( hs i ) |> MeasurableSet.mem;
          · intro s hs; erw [ MeasureTheory.Measure.map_apply ];
            · rw [ show ( fun f : Fin 3 → Fin d → T1 => fun p : Fin 3 × Fin d => f p.1 p.2 ) ⁻¹' Set.univ.pi s = Set.pi Set.univ fun i => Set.pi Set.univ fun j => s ( i, j ) from ?_ ];
              · rw [ MeasureTheory.Measure.pi_pi ];
                rw [ Finset.prod_congr rfl fun i _ => MeasureTheory.Measure.pi_pi _ _ ];
                rw [ Finset.prod_sigma' ];
                refine' Finset.prod_bij ( fun x _ => ( x.fst, x.snd ) ) _ _ _ _ <;> simp +decide;
                grind;
              · ext; simp [Set.mem_preimage, Set.mem_pi];
            · fun_prop;
            · exact MeasurableSet.univ_pi hs;
        · grind +suggestions;
      · fun_prop;
      · exact MeasurableSet.univ_pi hs;
  apply h_contra;
  rw [ MeasureTheory.Measure.map_apply ];
  · exact h_prod_measure s hs ▸ rfl;
  · exact measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ |> Measurable.comp <| measurable_pi_apply _;
  · exact hs

/-
The coordinate-factored set equals the preimage of a pi set under the transpose.
-/
lemma coordFactored_eq_preimage_pi (d : ℕ) (S : Set (Fin 3 → T1)) :
    ({pts : Fin 3 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ S} : Set (Fin 3 → Fin d → T1))
    = (fun (f : Fin 3 → Fin d → T1) (i : Fin d) (j : Fin 3) => f j i) ⁻¹' (Set.univ.pi (fun _ : Fin d => S)) := by
  ext; aesop;

/-
Inductive step: from d to d+1.
-/
lemma volume_coordFactored_eq_pow_succ (d : ℕ) (S : Set (Fin 3 → T1)) (hS : MeasurableSet S)
    (ih : volume ({pts : Fin 3 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ S} : Set (Fin 3 → Fin d → T1))
          = (volume S) ^ d) :
    volume ({pts : Fin 3 → (Fin (d + 1) → T1) | ∀ i : Fin (d + 1), (fun j : Fin 3 => pts j i) ∈ S} : Set (Fin 3 → Fin (d + 1) → T1))
    = (volume S) ^ (d + 1) := by
  rw [ coordFactored_eq_preimage_pi ];
  convert congr_arg ( fun x : ENNReal => x ) ( MeasureTheory.Measure.pi_pi ( fun _ => volume ) fun ( _ : Fin ( d + 1 ) ) => S ) using 1;
  · convert congr_arg ( fun x : MeasureTheory.Measure ( Fin ( d + 1 ) → Fin 3 → T1 ) => x ( Set.univ.pi fun _ => S ) ) ( volume_map_transpose ( d + 1 ) ) using 1;
    rw [ MeasureTheory.Measure.map_apply ];
    · exact measurable_transpose _;
    · exact MeasurableSet.univ_pi fun _ => hS;
  · norm_num

/-
Key factorisation: for a measurable set `S ⊆ Fin 3 → T1`,
    the volume of the coordinate-product set on `Fin 3 → Torus d`
    equals `(volume S) ^ d`.
-/
lemma volume_coordFactored_eq_pow (d : ℕ) (S : Set (Fin 3 → T1)) (hS : MeasurableSet S) :
    volume ({pts : Fin 3 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ S} : Set (Fin 3 → Fin d → T1))
    = (volume S) ^ d := by
  induction' d with d ih;
  · convert volume_coordFactored_eq_pow_zero S hS using 1;
  · exact volume_coordFactored_eq_pow_succ d S hS ih

/-! ## Connecting indicators to coordinate-factored sets -/

/-
The triangle set on Torus d equals the coordinate-factored triangle set.
-/
lemma triangleSet_torus_eq (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr : 0 ≤ r) :
    ({pts : Fin 3 → (Fin d → T1) | dist (pts 0) (pts 1) ≤ r ∧ dist (pts 0) (pts 2) ≤ r ∧ dist (pts 1) (pts 2) ≤ r} : Set (Fin 3 → Fin d → T1))
    = {pts : Fin 3 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ triangleSet r} := by
  ext;
  simp +decide [ dist_pi_le_iff, triangleSet ];
  constructor <;> intro h <;> simp_all +decide [ dist_pi_le_iff ]

/-
The fill set on Torus d equals the coordinate-factored fill set (for r ≤ 1/4).
-/
lemma fillSet_torus_eq (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ({pts : Fin 3 → (Fin d → T1) |
      ∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r} : Set (Fin 3 → Fin d → T1))
    = {pts : Fin 3 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ fillSet r} := by
  ext pts;
  constructor <;> intro h;
  · exact fun i => ⟨ h.choose i, by simpa using dist_le_pi_dist ( pts 0 ) h.choose i |> le_trans <| h.choose_spec.1, by simpa using dist_le_pi_dist ( pts 1 ) h.choose i |> le_trans <| h.choose_spec.2.1, by simpa using dist_le_pi_dist ( pts 2 ) h.choose i |> le_trans <| h.choose_spec.2.2 ⟩;
  · choose z hz using h;
    use z;
    simp_all +decide [ dist_pi_le_iff ]

/-
The edge-fill set on Torus d equals the coordinate-factored edge-fill set (for r ≤ 1/4).
-/
lemma edgeFillSet_torus_eq (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ({pts : Fin 3 → (Fin d → T1) |
      dist (pts 0) (pts 1) ≤ r ∧
      ∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r} : Set (Fin 3 → Fin d → T1))
    = {pts : Fin 3 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ edgeFillSet r} := by
  ext;
  unfold edgeFillSet; constructor <;> intro h <;> simp_all +decide [ dist_pi_le_iff ] ;
  · exact fun i => ⟨ h.2.choose i, h.2.choose_spec.1 i, h.2.choose_spec.2.1 i, h.2.choose_spec.2.2 i ⟩;
  · choose z hz using fun i => h i |>.2; use z; aesop;

/-! ## Main integral results -/

/-
Triangle integral = (3r²)^d.
-/
theorem integral_triangle_eq_pow (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫ pts : Fin 3 → (Fin d → T1),
      (if dist (pts 0) (pts 1) ≤ r then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ r then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ r then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Fin d → T1)))
    = (3 * r ^ 2) ^ d := by
  -- The integral of the indicator function is equal to the volume of the set it indicates.
  have h_volume : ∫ (pts : Fin 3 → Fin d → T1), (if dist (pts 0) (pts 1) ≤ r ∧ dist (pts 0) (pts 2) ≤ r ∧ dist (pts 1) (pts 2) ≤ r then 1 else 0) ∂Measure.pi (fun _ => MeasureSpace.volume) = (MeasureTheory.volume {pts : Fin 3 → Fin d → T1 | dist (pts 0) (pts 1) ≤ r ∧ dist (pts 0) (pts 2) ≤ r ∧ dist (pts 1) (pts 2) ≤ r}).toReal := by
    rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
    change (∫ x in { pts : Fin 3 → Fin d → T1 | dist ( pts 0 ) ( pts 1 ) ≤ r ∧ dist ( pts 0 ) ( pts 2 ) ≤ r ∧ dist ( pts 1 ) ( pts 2 ) ≤ r }, 1 ∂Measure.pi fun _ => volume) = _;
    · norm_num;
      rfl;
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) );
    · norm_num [ Filter.EventuallyEq, Set.indicator ];
  convert h_volume using 1;
  · grind;
  · rw [ triangleSet_torus_eq d hd r hr0 ];
    rw [ volume_coordFactored_eq_pow ];
    · rw [ volume_triangleSet r hr0 hr ] ; norm_num [ ENNReal.toReal_ofReal ( show 0 ≤ 3 * r ^ 2 by positivity ) ];
      rw [ ENNReal.toReal_ofReal ( sq_nonneg r ) ];
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) )

/-
Edge-fill integral = (7r²)^d.
-/
theorem integral_edgeFill_eq_pow (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫ pts : Fin 3 → (Fin d → T1),
      (if dist (pts 0) (pts 1) ≤ r then (1:ℝ) else 0) *
      (if ∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Fin d → T1)))
    = (7 * r ^ 2) ^ d := by
  convert congr_arg ENNReal.toReal ( volume_coordFactored_eq_pow d ( edgeFillSet r ) ?_ ) using 1;
  · convert integral_indicator _;
    any_goals exact { pts : Fin 3 → Fin d → T1 | dist ( pts 0 ) ( pts 1 ) ≤ r ∧ ∃ z : Fin d → T1, dist ( pts 0 ) z ≤ r ∧ dist ( pts 1 ) z ≤ r ∧ dist ( pts 2 ) z ≤ r };
    any_goals exact fun _ => 1;
    · split_ifs <;> aesop;
    · rw [ edgeFillSet_torus_eq ];
      · norm_num;
        rfl;
      · linarith;
      · exact RCLike.ofReal_nonneg.mp hr0;
      · linarith;
    · have h_measurable : MeasurableSet (edgeFillSet r) := by
        -- The edgeFillSet is measurable because it is defined by measurable conditions.
        have h_measurable : MeasurableSet {u : Fin 3 → T1 | dist (u 0) (u 1) ≤ r} ∧ MeasurableSet {u : Fin 3 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
          constructor;
          · exact measurableSet_le ( Continuous.measurable ( by continuity ) ) measurable_const;
          · -- The set of points $z$ such that $dist (u 0) z ≤ r$, $dist (u 1) z ≤ r$, and $dist (u 2) z ≤ r$ is closed.
            have h_closed : IsClosed {u : Fin 3 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
              have h_closed : IsClosed {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
                exact IsClosed.inter ( isClosed_le ( continuous_dist.comp <| Continuous.prodMk ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( continuous_dist.comp <| Continuous.prodMk ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( continuous_dist.comp <| Continuous.prodMk ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
              have h_closed : IsClosed (Set.image (fun p : (Fin 3 → T1) × T1 => p.1) {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r}) := by
                apply_rules [ IsCompact.isClosed, IsCompact.image ];
                · exact IsCompact.of_isClosed_subset ( isCompact_univ ) h_closed ( Set.subset_univ _ );
                · exact continuous_fst;
              convert h_closed using 1;
              ext; simp [Set.mem_image];
            exact h_closed.measurableSet;
        exact h_measurable.1.inter h_measurable.2;
      convert edgeFillSet_torus_eq d hd r hr0 hr ▸ show MeasurableSet { pts : Fin 3 → Fin d → T1 | ∀ i : Fin d, ( fun j : Fin 3 => pts j i ) ∈ edgeFillSet r } from ?_ using 1;
      simp +decide only [Set.setOf_forall];
      exact MeasurableSet.iInter fun i => h_measurable.preimage <| measurable_pi_lambda _ fun j => measurable_pi_apply i |> Measurable.comp <| measurable_pi_apply j;
  · rw [ volume_edgeFillSet r hr0 hr, ENNReal.toReal_pow ] ; norm_num [ hr0 ];
  · -- The edgeFillSet is measurable because it is defined by measurable conditions.
    have h_measurable : MeasurableSet {u : Fin 3 → T1 | dist (u 0) (u 1) ≤ r} ∧ MeasurableSet {u : Fin 3 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
      constructor;
      · exact measurableSet_le ( Continuous.measurable ( by continuity ) ) measurable_const;
      · -- The set of points $z$ such that $dist (u 0) z ≤ r$, $dist (u 1) z ≤ r$, and $dist (u 2) z ≤ r$ is closed.
        have h_closed : IsClosed {u : Fin 3 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
          have h_closed : IsClosed {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
            exact IsClosed.inter ( isClosed_le ( continuous_dist.comp <| Continuous.prodMk ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( continuous_dist.comp <| Continuous.prodMk ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( continuous_dist.comp <| Continuous.prodMk ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
          have h_closed : IsClosed (Set.image (fun p : (Fin 3 → T1) × T1 => p.1) {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r}) := by
            apply_rules [ IsCompact.isClosed, IsCompact.image ];
            · exact IsCompact.of_isClosed_subset ( isCompact_univ ) h_closed ( Set.subset_univ _ );
            · exact continuous_fst;
          convert h_closed using 1;
          ext; simp [Set.mem_image];
        exact h_closed.measurableSet;
    exact h_measurable.1.inter h_measurable.2

/-
Fill integral = (12r²)^d.
-/
theorem integral_fill_eq_pow (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫ pts : Fin 3 → (Fin d → T1),
      (if ∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Fin d → T1)))
    = (12 * r ^ 2) ^ d := by
  convert congr_arg ENNReal.toReal ( volume_coordFactored_eq_pow d ( fillSet r ) ( show MeasurableSet ( fillSet r ) from ?_ ) ) using 1;
  · convert MeasureTheory.integral_indicator ( show MeasurableSet { pts : Fin 3 → Fin d → T1 | ∃ z : Fin d → T1, dist ( pts 0 ) z ≤ r ∧ dist ( pts 1 ) z ≤ r ∧ dist ( pts 2 ) z ≤ r } from ?_ ) using 1;
    · rw [ ← fillSet_torus_eq d hd r hr0 hr ];
      norm_num;
      rfl;
    · have h_fillSet_measurable : MeasurableSet (fillSet r) := by
        refine' IsCompact.measurableSet _;
        -- The set of points $z$ such that $dist (u 0) z ≤ r$ is a closed ball in $T1$, which is compact.
        have h_closed_ball : ∀ u : Fin 3 → T1, IsCompact {z : T1 | dist (u 0) z ≤ r} := by
          intro u;
          convert ProperSpace.isCompact_closedBall ( u 0 ) r using 1;
          exact Set.ext fun x => by simp +decide [ dist_comm ] ;
        have h_closed_ball : IsCompact {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
          refine' IsCompact.of_isClosed_subset ( isCompact_univ.prod ( isCompact_univ ) ) _ _;
          · exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
          · grind +revert;
        convert h_closed_ball.image ( show Continuous fun p : ( Fin 3 → T1 ) × T1 => p.1 from continuous_fst ) using 1;
        ext; simp [fillSet];
      convert fillSet_torus_eq d hd r hr0 hr ▸ show MeasurableSet { pts : Fin 3 → Fin d → T1 | ∀ i : Fin d, ( fun j : Fin 3 => pts j i ) ∈ fillSet r } from ?_ using 1;
      simp +decide only [Set.setOf_forall];
      exact MeasurableSet.iInter fun i => h_fillSet_measurable.preimage <| measurable_pi_lambda _ fun j => measurable_pi_apply i |> Measurable.comp <| measurable_pi_apply j;
  · rw [ volume_fillSet r hr0 hr, ENNReal.toReal_pow, ENNReal.toReal_ofReal ( by positivity ) ];
  · refine' IsCompact.measurableSet _;
    -- The set of points $z$ such that $dist (u 0) z ≤ r$ is a closed ball in $T1$, which is compact.
    have h_closed_ball : ∀ u : Fin 3 → T1, IsCompact {z : T1 | dist (u 0) z ≤ r} := by
      intro u;
      convert ProperSpace.isCompact_closedBall ( u 0 ) r using 1;
      exact Set.ext fun x => by simp +decide [ dist_comm ] ;
    have h_closed_ball : IsCompact {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
      refine' IsCompact.of_isClosed_subset ( isCompact_univ.prod ( isCompact_univ ) ) _ _;
      · exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
      · grind +revert;
    convert h_closed_ball.image ( show Continuous fun p : ( Fin 3 → T1 ) × T1 => p.1 from continuous_fst ) using 1;
    ext; simp [fillSet]