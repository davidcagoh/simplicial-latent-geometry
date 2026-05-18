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

/-
**Sim-A5 / Job 1b, Lemma 4.** 1D fill probability (Stevens 1939):
    `volume(fillSet r) = 12r²` on (T1)³ for `r ≤ 1/4`.

Extended fill_fiber_volume for dist < 2r (strict). The formula 4r - dist is correct
for all dist < 2r when r ≤ 1/4; it fails only at dist = 2r with r = 1/4
(where wrap-around makes the fill fiber the whole circle).
For the integral computation, this boundary has measure 0.
-/
lemma fill_fiber_subset_ball_lt (r b' : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) (hb'0 : 0 ≤ b') (hb' : b' < 2 * r) :
    {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b' : T1) z ≤ r ∧ dist c z ≤ r}
    ⊆ Metric.closedBall (QuotientAddGroup.mk (b'/2) : T1) (2*r - b'/2) := by
  -- If $b' > r$, then for any $c$ in the set, there exists $z$ such that $dist 0 z \leq r$, $dist (QuotientAddGroup.mk b') z \leq r$, and $dist c z \leq r$.
  intro c hc
  obtain ⟨z, hz⟩ := hc;
  -- By translation invariance, we can shift the problem to the interval [0, 1).
  obtain ⟨z', hz'⟩ : ∃ z' : ℝ, z = QuotientAddGroup.mk z' ∧ |z' - b'| ≤ r ∧ |z'| ≤ r := by
    have hz' : ∃ z' : ℝ, z = QuotientAddGroup.mk z' ∧ |z'| ≤ r := by
      obtain ⟨z', hz'⟩ : ∃ z' : ℝ, z = QuotientAddGroup.mk z' ∧ |z'| ≤ r := by
        have hz'_exists : ∃ z' : ℝ, z = QuotientAddGroup.mk z' ∧ |z'| ≤ 1 / 2 := by
          obtain ⟨z', hz'⟩ : ∃ z' : ℝ, z = QuotientAddGroup.mk z' ∧ -1 / 2 ≤ z' ∧ z' < 1 / 2 := by
            obtain ⟨ z', hz' ⟩ := QuotientAddGroup.mk_surjective z;
            refine' ⟨ z' - ⌊z' + 1 / 2⌋, _, _, _ ⟩ <;> norm_num [ hz'.symm ];
            · norm_num [ sub_eq_add_neg, QuotientAddGroup.eq ];
            · exact Int.floor_le _;
            · linarith [ Int.lt_floor_add_one ( z' + 1 / 2 ) ];
          exact ⟨ z', hz'.1, abs_le.mpr ⟨ by linarith, by linarith ⟩ ⟩
        obtain ⟨ z', rfl, hz' ⟩ := hz'_exists; use z'; simp_all +decide [ dist_eq_norm ] ;
        convert hz.1 using 1;
        convert T1_norm_mk_of_abs_le z' ( by norm_num at *; linarith ) |> Eq.symm;
      use z';
    obtain ⟨ z', rfl, hz' ⟩ := hz'; use z'; simp_all +decide [ dist_eq_norm ] ;
    have hz'_dist : ‖(QuotientAddGroup.mk (z' - b') : T1)‖ ≤ r := by
      convert hz.2.1 using 1 ; norm_num [ norm_sub_rev ];
    rw [ AddCircle.norm_eq ] at hz'_dist;
    norm_num [ abs_le ] at *;
    constructor <;> linarith [ show ( round ( z' - b' ) : ℝ ) = 0 by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast ; linarith ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast ; linarith ) ];
  have h_dist : dist c (QuotientAddGroup.mk (b' / 2)) ≤ dist c z + dist z (QuotientAddGroup.mk (b' / 2)) := by
    exact dist_triangle _ _ _;
  have h_dist_z : dist z (QuotientAddGroup.mk (b' / 2)) ≤ |z' - b' / 2| := by
    rw [ hz'.1, T1_dist_mk_of_abs_le ];
    exact abs_le.mpr ⟨ by linarith [ abs_le.mp hz'.2.1, abs_le.mp hz'.2.2 ], by linarith [ abs_le.mp hz'.2.1, abs_le.mp hz'.2.2 ] ⟩;
  exact le_trans h_dist ( by cases abs_cases ( z' - b' / 2 ) <;> cases abs_cases ( z' - b' ) <;> cases abs_cases z' <;> linarith )

lemma fill_fiber_volume_lt (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (a b : T1) (hd : dist a b < 2 * r) :
    volume {c : T1 | ∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r}
    = ENNReal.ofReal (4 * r - dist a b) := by
  obtain ⟨b', hb'⟩ : ∃ b' : ℝ, |b'| < 2 * r ∧ b = a + QuotientAddGroup.mk b' := by
    obtain ⟨x, hx⟩ : ∃ x : ℝ, b = a + x ∧ |x| ≤ 1 / 2 := by
      obtain ⟨x, hx⟩ : ∃ x : ℝ, b = a + x := by
        obtain ⟨ x, hx ⟩ := QuotientAddGroup.mk_surjective b; obtain ⟨ y, hy ⟩ := QuotientAddGroup.mk_surjective a; use x - y; aesop;
      refine' ⟨ x - ⌊x + 1 / 2⌋, _, _ ⟩ <;> norm_num [ hx ];
      · norm_num [ sub_eq_add_neg ];
      · exact abs_le.mpr ⟨ by linarith [ Int.floor_le ( x + 1 / 2 ) ], by linarith [ Int.lt_floor_add_one ( x + 1 / 2 ) ] ⟩;
    use x;
    simp_all +decide [ dist_eq_norm ];
    convert hd using 1;
    convert T1_norm_mk_of_abs_le x ( by norm_num at *; linarith ) |> Eq.symm;
  -- By translation invariance, reduce to a = 0.
  suffices h_trans : volume {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b') z ≤ r ∧ dist c z ≤ r} = ENNReal.ofReal (4 * r - |b'|) by
    convert h_trans using 1;
    · rw [ ← MeasureTheory.measure_preimage_add_right ];
      congr! 1;
      swap;
      exact a;
      ext; simp [hb'];
      constructor <;> rintro ⟨ z, hz₁, hz₂, hz₃ ⟩;
      · use z - a;
        simp_all +decide [ dist_eq_norm, add_sub_assoc ];
        simp_all +decide [ norm_sub_rev, sub_eq_add_neg, add_assoc ];
        exact ⟨ by rw [ ← norm_neg ] ; convert hz₁ using 1; abel_nf, by convert hz₂ using 1; abel_nf ⟩;
      · use z + a;
        simp_all +decide [ dist_eq_norm, add_comm a ];
    · simp +decide [ hb'.2, dist_eq_norm ];
      rw [ T1_norm_mk_of_abs_le ] ; linarith [ abs_lt.mp hb'.1 ];
  have h_fill_fiber_subset : {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b') z ≤ r ∧ dist c z ≤ r} ⊆ Metric.closedBall (QuotientAddGroup.mk (b'/2) : T1) (2*r - |b'|/2) := by
    cases abs_cases b' <;> simp +decide [ *, neg_div ];
    · by_cases hb'_eq : b' = 2 * r;
      · linarith [ abs_lt.mp hb'.1 ];
      · convert fill_fiber_subset_ball_lt r b' hr0 hr ( by linarith ) ( lt_of_le_of_ne ( by linarith ) hb'_eq ) using 1;
        simp +decide [ dist_eq_norm ];
    · have := fill_fiber_subset_ball_lt r ( -b' ) hr0 hr ( by linarith ) ( by linarith );
      intro c hc; specialize this ( show ∃ z : T1, dist 0 z ≤ r ∧ dist ( QuotientAddGroup.mk ( -b' ) ) z ≤ r ∧ dist ( -c ) z ≤ r from by
                                      obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := hc; use -z; simp_all +decide [ dist_neg ] ; ) ; simp_all +decide [ dist_neg ] ;
      convert this using 1 <;> ring;
      norm_num [ dist_eq_norm ];
  have h_ball_subset : Metric.closedBall (QuotientAddGroup.mk (b'/2) : T1) (2*r - |b'|/2) ⊆ {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk b') z ≤ r ∧ dist c z ≤ r} := by
    by_cases hb'_nonneg : 0 ≤ b';
    · convert ball_subset_fill_fiber r b' hr0 hr hb'_nonneg ( by linarith [ abs_of_nonneg hb'_nonneg ] ) using 1;
      rw [ abs_of_nonneg hb'_nonneg ];
    · have h_neg : Metric.closedBall (QuotientAddGroup.mk (-b'/2) : T1) (2*r - |b'|/2) ⊆ {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist (QuotientAddGroup.mk (-b')) z ≤ r ∧ dist c z ≤ r} := by
        convert ball_subset_fill_fiber r ( -b' ) hr0 hr ( by linarith [ abs_of_neg ( not_le.mp hb'_nonneg ) ] ) ( by linarith [ abs_of_neg ( not_le.mp hb'_nonneg ) ] ) using 1;
        rw [ abs_of_neg ( not_le.mp hb'_nonneg ) ];
      intro c hc; specialize h_neg ( show -c ∈ Metric.closedBall ( QuotientAddGroup.mk ( -b' / 2 ) : T1 ) ( 2 * r - |b'| / 2 ) from ?_ ) ; simp_all +decide [ neg_div, dist_neg ] ;
      obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := h_neg; use -z; simp_all +decide [ dist_neg ] ;
  rw [ Set.Subset.antisymm h_fill_fiber_subset h_ball_subset ];
  rw [ AddCircle.volume_closedBall ] ; ring;
  rw [ min_eq_right ( by linarith [ abs_nonneg b' ] ) ]

/-
When dist a b > 2r on the circle (r ≤ 1/4), the balls B(a,r) and B(b,r) are disjoint,
    so no z can be within r of both.
-/
lemma fill_fiber_empty (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (a b : T1) (hd : dist a b > 2 * r) :
    {c : T1 | ∃ z : T1, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r} = ∅ := by
  rw [ Set.eq_empty_iff_forall_notMem ];
  intro c hc; obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := hc; linarith [ dist_triangle_right a b z ] ;

/-
Key real integral: ∫_{-2r}^{2r} (4r - |x|) dx = 12r².
-/
lemma integral_4r_minus_abs_wide (r : ℝ) (hr0 : 0 ≤ r) :
    ∫ x in Set.Icc (-(2*r)) (2*r), (4 * r - |x|) = 12 * r ^ 2 := by
  rw [ MeasureTheory.integral_sub ] <;> norm_num;
  · -- Split the integral into two parts: from -2r to 0 and from 0 to 2r.
    have h_split : ∫ x in Set.Icc (-(2 * r)) (2 * r), |x| = (∫ x in Set.Icc (-(2 * r)) 0, |x|) + (∫ x in Set.Icc 0 (2 * r), |x|) := by
      norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, hr0 ];
      rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
    rw [ h_split, MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => abs_of_nonpos hx.2, MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => abs_of_nonneg hx.1 ];
    rw [ MeasureTheory.integral_neg, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num <;> ring <;> norm_num [ hr0 ];
    ring;
  · fun_prop;
  · exact Continuous.integrableOn_Icc ( by continuity )

/-
The set {u : T1 | dist 0 u = 2*r} has measure zero on T1.
-/
lemma T1_dist_eq_measure_zero (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) (a : T1) :
    volume {u : T1 | dist a u = 2 * r} = 0 := by
  by_contra h_nonzero;
  -- The set {u : T1 | dist a u = 2 * r} is finite because it is a sphere in a 1-dimensional manifold.
  have h_finite : Set.Finite {u : T1 | dist a u = 2 * r} := by
    -- The set {u : T1 | dist a u = 2 * r} is finite because it is a sphere in a 1-dimensional manifold, which has at most 2 points.
    have h_finite : ∀ u : T1, dist a u = 2 * r → u = a + QuotientAddGroup.mk (2 * r) ∨ u = a - QuotientAddGroup.mk (2 * r) := by
      intro u hu
      have h_dist : ∃ x : ℝ, |x| = 2 * r ∧ u = a + QuotientAddGroup.mk x := by
        obtain ⟨x, hx⟩ : ∃ x : ℝ, u = a + QuotientAddGroup.mk x ∧ |x| ≤ 1 / 2 := by
          obtain ⟨x, hx⟩ : ∃ x : ℝ, u = a + QuotientAddGroup.mk x := by
            obtain ⟨ x, hx ⟩ := QuotientAddGroup.mk_surjective ( u - a );
            exact ⟨ x, by rw [ hx, add_sub_cancel ] ⟩;
          refine' ⟨ x - ⌊x + 1 / 2⌋, _, _ ⟩ <;> norm_num [ hx ];
          · norm_num [ sub_eq_add_neg, AddCircle ];
          · exact abs_le.mpr ⟨ by linarith [ Int.floor_le ( x + 1 / 2 ) ], by linarith [ Int.lt_floor_add_one ( x + 1 / 2 ) ] ⟩;
        have h_dist : dist a (a + QuotientAddGroup.mk x) = |x| := by
          convert T1_dist_mk_of_abs_le 0 x _ using 1 <;> norm_num [ hx.2 ];
        grind;
      obtain ⟨ x, hx, rfl ⟩ := h_dist; rcases eq_or_eq_neg_of_abs_eq hx with ( rfl | rfl ) <;> norm_num;
      exact Or.inr ( by abel1 );
    exact Set.Finite.subset ( Set.toFinite { a + QuotientAddGroup.mk ( 2 * r ), a - QuotientAddGroup.mk ( 2 * r ) } ) h_finite;
  have h_singleton : ∀ u : T1, volume {u} = 0 := by
    intro u; exact (by
    cases subsingleton_or_nontrivial T1 <;> simp_all +decide [ MeasureTheory.MeasureSpace.volume ];
    simp_all +decide [ SetLike.ext_iff ];
    rename_i h; specialize h ( 1 / 2 ) ; obtain ⟨ k, hk ⟩ := h; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> linarith;);
  exact h_nonzero <| by rw [ show { u : T1 | dist a u = 2 * r } = ⋃ u ∈ h_finite.toFinset, { u } by ext; aesop ] ; exact MeasureTheory.measure_biUnion_null_iff ( Finset.countable_toSet _ ) |>.2 fun u hu => h_singleton u;

/-
The fill fiber integrand equals ofReal(4r - dist) a.e. when restricted to {dist < 2r},
    and the complement {dist ≥ 2r} has measure zero except for the boundary {dist = 2r}
    which has measure zero. So the lintegral equals the integral of (4r - |x|) over [-2r, 2r].
-/
lemma fillSet_outer_integral (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫⁻ (u1 : T1), volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r}
    = ENNReal.ofReal (12 * r ^ 2) := by
  have h_step1 : ∫⁻ (u1 : T1), volume {c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r} ∂MeasureTheory.volume = ∫⁻ (u1 : T1) in {u1 : T1 | dist 0 u1 < 2 * r}, ENNReal.ofReal (4 * r - dist 0 u1) ∂MeasureTheory.volume := by
    rw [ ← MeasureTheory.lintegral_indicator ];
    · refine' MeasureTheory.lintegral_congr_ae _;
      refine' MeasureTheory.measure_mono_null _ _;
      exact { u1 : T1 | dist 0 u1 = 2 * r };
      · intro u hu; contrapose! hu; simp_all +decide [ Set.indicator ] ;
        split_ifs <;> simp_all +decide [ dist_eq_norm ];
        · convert fill_fiber_volume_lt r hr0 ( show r ≤ 1 / 4 by norm_num at *; linarith ) 0 u ( by simpa using by linarith ) using 1;
          · simp +decide [ dist_eq_norm ];
          · rw [ dist_zero_left ];
        · rw [ show { c : T1 | ∃ z : T1, ‖z‖ ≤ r ∧ ‖u - z‖ ≤ r ∧ ‖c - z‖ ≤ r } = ∅ from _ ] ; norm_num;
          exact Set.eq_empty_of_forall_notMem fun c hc => hu <| by obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := hc; linarith [ norm_sub_norm_le u z ] ;
      · convert T1_dist_eq_measure_zero r hr0 hr 0 using 1;
    · exact measurableSet_lt ( continuous_const.dist continuous_id' |> Continuous.measurable ) measurable_const;
  -- Step 2: Lift to ℝ using `AddCircle.lintegral_preimage` with a = -1/2.
  have h_step2 : ∫⁻ (u1 : T1) in {u1 : T1 | dist 0 u1 < 2 * r}, ENNReal.ofReal (4 * r - dist 0 u1) ∂MeasureTheory.volume = ∫⁻ (x : ℝ) in Set.Ioo (-2 * r) (2 * r), ENNReal.ofReal (4 * r - |x|) ∂MeasureTheory.volume := by
    have := @AddCircle.lintegral_preimage;
    convert ( this 1 ( -1 / 2 ) fun u1 => ENNReal.ofReal ( 4 * r - dist 0 u1 ) * ( if dist 0 u1 < 2 * r then 1 else 0 ) ) |> Eq.symm using 1;
    · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
      exact measurableSet_Iio.mem.comp measurable_norm;
    · rw [ ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
      grind +suggestions;
  convert h_step1.trans h_step2 using 1;
  rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
  · rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_sub ] <;> norm_num;
    · -- Evaluate the integral of $|x|$ over $[-2r, 2r]$.
      have h_abs : ∫ x in -(2 * r)..2 * r, |x| = (∫ x in -(2 * r)..0, |x|) + (∫ x in (0)..2 * r, |x|) := by
        rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
      rw [ h_abs, intervalIntegral.integral_congr fun x hx => abs_of_nonpos <| by linarith [ Set.mem_Icc.mp <| by simpa [ hr0 ] using hx ], intervalIntegral.integral_congr fun x hx => abs_of_nonneg <| by linarith [ Set.mem_Icc.mp <| by simpa [ hr0 ] using hx ] ] ; norm_num ; ring;
      rw [ intervalIntegral.integral_neg ] ; norm_num ; ring;
      rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_ofNat ];
    · exact Continuous.intervalIntegrable ( continuous_abs ) _ _;
  · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set <| Set.Ioo_subset_Icc_self;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using sub_nonneg_of_le <| by cases abs_cases x <;> linarith [ hx.1, hx.2 ] ;

lemma volume_fillSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (fillSet r) = ENNReal.ofReal (12 * r ^ 2) := by
  have h_fubini : volume {u : Fin 3 → AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} = ∫⁻ (u : AddCircle (1 : ℝ)), ∫⁻ (v : AddCircle (1 : ℝ)), ∫⁻ (w : AddCircle (1 : ℝ)), if ∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r then 1 else 0 := by
    have h_fubini : ∀ {f : (Fin 3 → AddCircle (1 : ℝ)) → ENNReal}, Measurable f → (∫⁻ u : Fin 3 → AddCircle (1 : ℝ), f u) = ∫⁻ u : AddCircle (1 : ℝ), ∫⁻ v : AddCircle (1 : ℝ), ∫⁻ w : AddCircle (1 : ℝ), f (fun i => if i = 0 then u else if i = 1 then v else w) := by
      intro f hf;
      have h_fubini : ∫⁻ (u : Fin 3 → AddCircle (1 : ℝ)), f u = ∫⁻ (u : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)), f (fun i => if i = 0 then u.1 else if i = 1 then u.2.1 else u.2.2) := by
        have h_fubini : MeasureTheory.MeasureSpace.volume = MeasureTheory.Measure.map (fun u : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => fun i : Fin 3 => if i = 0 then u.1 else if i = 1 then u.2.1 else u.2.2) (MeasureTheory.MeasureSpace.volume.prod (MeasureTheory.MeasureSpace.volume.prod MeasureTheory.MeasureSpace.volume)) := by
          refine' MeasureTheory.Measure.pi_eq _;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · simp +decide [ Fin.prod_univ_three, Set.preimage ];
            simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
            erw [ show { a : AddCircle 1 × AddCircle 1 × AddCircle 1 | a.1 ∈ s 0 } ∩ ( { a : AddCircle 1 × AddCircle 1 × AddCircle 1 | a.2.1 ∈ s 1 } ∩ { a : AddCircle 1 × AddCircle 1 × AddCircle 1 | a.2.2 ∈ s 2 } ) = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; simp +decide [ mul_assoc ];
          · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
          · exact MeasurableSet.univ_pi hs;
        rw [ h_fubini, MeasureTheory.lintegral_map ];
        · rfl;
        · exact hf;
        · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
      erw [ h_fubini, MeasureTheory.lintegral_prod ];
      · congr! 2;
        erw [ MeasureTheory.lintegral_prod ];
        exact hf.comp ( measurable_pi_lambda _ fun i => by fin_cases i <;> measurability ) |> Measurable.aemeasurable;
      · exact hf.aemeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ) );
    convert @h_fubini ( fun u => if ∃ z : AddCircle ( 1 : ℝ ), dist ( u 0 ) z ≤ r ∧ dist ( u 1 ) z ≤ r ∧ dist ( u 2 ) z ≤ r then 1 else 0 ) _ using 1;
    · erw [ MeasureTheory.lintegral_indicator ];
      · aesop;
      · -- The set of points $z$ such that $dist(u_0, z) \leq r$, $dist(u_1, z) \leq r$, and $dist(u_2, z) \leq r$ is closed.
        have h_closed : IsClosed {u : Fin 3 → AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
          have h_closed : IsClosed {p : (Fin 3 → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
            exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
          have h_closed : IsClosed (Set.image (fun p : (Fin 3 → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) => p.1) {p : (Fin 3 → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r}) := by
            apply_rules [ IsCompact.isClosed, IsCompact.image ];
            · have h_compact : IsCompact (Set.univ : Set (Fin 3 → AddCircle (1 : ℝ))) := by
                exact isCompact_univ;
              exact h_compact.prod ( isCompact_univ ) |> fun h => h.of_isClosed_subset h_closed fun p hp => by simp;
            · exact continuous_fst;
          convert h_closed using 1;
          ext; simp [Set.mem_image];
        exact h_closed.measurableSet;
    · refine' Measurable.ite _ measurable_const measurable_const;
      refine' IsClosed.measurableSet _;
      have h_closed : IsClosed {p : (Fin 3 → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
        exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
      have h_closed : IsClosed (Set.image (fun p : (Fin 3 → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) => p.1) {p : (Fin 3 → AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r}) := by
        apply_rules [ IsCompact.isClosed, IsCompact.image ];
        · have h_compact : IsCompact (Set.univ : Set (Fin 3 → AddCircle (1 : ℝ))) := by
            exact isCompact_univ;
          exact h_compact.prod ( isCompact_univ ) |> fun h => h.of_isClosed_subset h_closed fun p hp => by simp;
        · exact continuous_fst;
      convert h_closed using 1;
      ext; simp [Set.mem_image];
  have h_fubini : ∀ (u v : AddCircle (1 : ℝ)), ∫⁻ (w : AddCircle (1 : ℝ)), (if ∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r then 1 else 0) = volume {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} := by
    intro u v; erw [ MeasureTheory.lintegral_indicator ] ; aesop;
    -- The set {w | ∃ z, dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} is closed, hence measurable.
    have h_closed : IsClosed {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} := by
      have h_closed : IsClosed {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | dist u p.1 ≤ r ∧ dist v p.1 ≤ r ∧ dist p.2 p.1 ≤ r} := by
        exact IsClosed.inter ( isClosed_le ( continuous_const.dist continuous_fst ) continuous_const ) ( IsClosed.inter ( isClosed_le ( continuous_const.dist continuous_fst ) continuous_const ) ( isClosed_le ( continuous_snd.dist continuous_fst ) continuous_const ) );
      have h_closed : IsClosed (Set.image (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => p.2) {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | dist u p.1 ≤ r ∧ dist v p.1 ≤ r ∧ dist p.2 p.1 ≤ r}) := by
        apply_rules [ IsCompact.isClosed, IsCompact.image ];
        · exact IsClosed.isCompact h_closed;
        · exact continuous_snd;
      convert h_closed using 1 ; ext ; aesop;
    exact h_closed.measurableSet;
  have h_fubini : ∀ (u : AddCircle (1 : ℝ)), ∫⁻ (v : AddCircle (1 : ℝ)), volume {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} = ∫⁻ (v : AddCircle (1 : ℝ)), volume {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist 0 z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} := by
    intro u
    have h_translation_invariance : ∀ (v : AddCircle (1 : ℝ)), volume {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} = volume {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist 0 z ≤ r ∧ dist (v - u) z ≤ r ∧ dist w z ≤ r} := by
      intro v
      have h_translation_invariance : ∀ (w : AddCircle (1 : ℝ)), (∃ z : AddCircle (1 : ℝ), dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r) ↔ (∃ z : AddCircle (1 : ℝ), dist 0 z ≤ r ∧ dist (v - u) z ≤ r ∧ dist (w - u) z ≤ r) := by
        intro w
        constructor
        intro h
        obtain ⟨z, hz⟩ := h
        use z - u
        simp [hz];
        rintro ⟨ z, hz₁, hz₂, hz₃ ⟩ ; use z + u; simp_all +decide [ dist_eq_norm ] ;
        exact ⟨ by convert hz₂ using 1; abel_nf, by convert hz₃ using 1; abel_nf ⟩;
      rw [ show { w : AddCircle 1 | ∃ z : AddCircle 1, dist u z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r } = ( fun w => w - u ) ⁻¹' { w : AddCircle 1 | ∃ z : AddCircle 1, dist 0 z ≤ r ∧ dist ( v - u ) z ≤ r ∧ dist w z ≤ r } by ext; aesop ];
      have h_translation_invariance : ∀ (S : Set (AddCircle (1 : ℝ))), volume (S.preimage (fun w => w - u)) = volume S := by
        simp +decide [ sub_eq_add_neg ];
      exact h_translation_invariance _;
    simp +decide only [h_translation_invariance];
    rw [ eq_comm, ← MeasureTheory.lintegral_sub_right_eq_self ];
  have h_fubini : ∫⁻ (v : AddCircle (1 : ℝ)), volume {w : AddCircle (1 : ℝ) | ∃ z : AddCircle (1 : ℝ), dist 0 z ≤ r ∧ dist v z ≤ r ∧ dist w z ≤ r} = ENNReal.ofReal (12 * r ^ 2) := by
    convert fillSet_outer_integral r hr0 hr using 1;
  unfold fillSet; aesop;

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
def doubleFillSet (r : ℝ) : Set (Fin 4 → T1) :=
  {u | (∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r) ∧
       (∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 3) z ≤ r)}

/-
Key 1D integral: 2 * ∫_0^{2r} (4r - b)² db = 112/3 * r³.
This is the squared fill-fiber length integrated over the separation distribution.
-/
lemma integral_fill_fiber_sq_line (r : ℝ) (hr0 : 0 ≤ r) :
    2 * ∫ b in Set.Icc 0 (2 * r), (4 * r - b) ^ 2 = 112 / 3 * r ^ 3 := by
  rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_comp_sub_left fun x => x ^ 2 ] ; norm_num ; ring;

/-
Helper: the fill fiber volume squared integral on ℝ.
∫_{-2r}^{2r} (4r - |x|)^2 dx = 112/3 * r^3.
-/
lemma integral_4r_minus_abs_sq (r : ℝ) (hr0 : 0 ≤ r) :
    ∫ x in Set.Icc (-(2*r)) (2*r), (4 * r - |x|) ^ 2 = 112 / 3 * r ^ 3 := by
  -- Split the integral into two parts: from -2r to 0 and from 0 to 2r.
  have h_split : ∫ x in Set.Icc (-(2 * r)) (2 * r), (4 * r - |x|) ^ 2 = (∫ x in Set.Icc (-(2 * r)) 0, (4 * r + x) ^ 2) + (∫ x in Set.Icc 0 (2 * r), (4 * r - x) ^ 2) := by
    have h_split : ∫ x in Set.Icc (-(2 * r)) (2 * r), (4 * r - |x|) ^ 2 = (∫ x in Set.Icc (-(2 * r)) 0, (4 * r - |x|) ^ 2) + (∫ x in Set.Icc 0 (2 * r), (4 * r - |x|) ^ 2) := by
      norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, hr0 ];
      rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
    exact h_split.trans ( congrArg₂ _ ( MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by rw [ abs_of_nonpos hx.2 ] ; ring ) ( MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by rw [ abs_of_nonneg hx.1 ] ) );
  rw [ h_split, MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc ];
  norm_num [ add_sq, sub_sq, mul_pow, mul_comm, ← intervalIntegral.integral_of_le, hr0 ] ; ring

/-
Helper: the lintegral of fill_fiber_vol(0,u)^2 over T1 equals 112/3 * r^3 (for r ≤ 1/4).
Here fill_fiber_vol(a,b) = volume {c | ∃ z, dist a z ≤ r ∧ dist b z ≤ r ∧ dist c z ≤ r}.
-/
lemma lintegral_fill_fiber_sq_T1 (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫⁻ u : T1, (volume {c : T1 | ∃ z : T1, dist (0:T1) z ≤ r ∧ dist u z ≤ r ∧ dist c z ≤ r}) ^ 2
    = ENNReal.ofReal (112 / 3 * r ^ 3) := by
  have h_integral_eq : ∫⁻ (u : T1), volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist u z ≤ r ∧ dist c z ≤ r} ^ 2 = ∫⁻ (y : ℝ) in Set.Icc (-1 / 2) (1 / 2), volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (QuotientAddGroup.mk y : T1) z ≤ r ∧ dist c z ≤ r} ^ 2 := by
    have h_integral_eq : ∫⁻ (u : T1), volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist u z ≤ r ∧ dist c z ≤ r} ^ 2 = ∫⁻ (y : ℝ) in Set.Ico (-1 / 2) (1 / 2), volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (QuotientAddGroup.mk y : T1) z ≤ r ∧ dist c z ≤ r} ^ 2 := by
      have := @AddCircle.lintegral_preimage;
      convert this 1 ( -1 / 2 ) _ |> Eq.symm using 1;
      rw [ ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc ] ; norm_num;
    rw [ h_integral_eq, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Icc ];
  -- Apply the result from `fill_fiber_volume_lt` to rewrite the integrand.
  have h_integrand : ∀ᵐ y ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (-1 / 2) (1 / 2)), volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (QuotientAddGroup.mk y : T1) z ≤ r ∧ dist c z ≤ r} ^ 2 = ENNReal.ofReal ((4 * r - |y|) ^ 2) * (if |y| ≤ 2 * r then 1 else 0) := by
    have h_integrand : ∀ᵐ y ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (-1 / 2) (1 / 2)), |y| ≠ 2 * r → volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (QuotientAddGroup.mk y : T1) z ≤ r ∧ dist c z ≤ r} = ENNReal.ofReal (4 * r - |y|) * (if |y| ≤ 2 * r then 1 else 0) := by
      have h_integrand : ∀ y ∈ Set.Icc (-1 / 2) (1 / 2), |y| ≠ 2 * r → volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (QuotientAddGroup.mk y : T1) z ≤ r ∧ dist c z ≤ r} = ENNReal.ofReal (4 * r - |y|) * (if |y| ≤ 2 * r then 1 else 0) := by
        intro y hy hy_ne
        by_cases hy_le : |y| ≤ 2 * r;
        · have := fill_fiber_volume_lt r hr0 hr ( 0 : T1 ) ( QuotientAddGroup.mk y ) ?_ <;> norm_num at *;
          · rw [ this, if_pos hy_le, T1_norm_mk_of_abs_le ] ; norm_num [ abs_le ] at * ; constructor <;> linarith;
          · rw [ T1_norm_mk_of_abs_le ] <;> norm_num at * <;> cases abs_cases y <;> cases lt_or_gt_of_ne hy_ne <;> linarith;
        · have h_empty : {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (QuotientAddGroup.mk y : T1) z ≤ r ∧ dist c z ≤ r} = ∅ := by
            apply fill_fiber_empty r hr0 hr (QuotientAddGroup.mk 0) (QuotientAddGroup.mk y);
            rw [ T1_dist_mk_of_abs_le ] <;> norm_num at *;
            · lia;
            · cases abs_cases y <;> linarith;
          rw [ h_empty, MeasureTheory.measure_empty ] ; norm_num [ hy_le ];
      filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with y hy using h_integrand y hy;
    filter_upwards [ h_integrand, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( 2 * r ) ), MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( -2 * r ) ) ] with y hy₁ hy₂ hy₃;
    by_cases hy₄ : |y| = 2 * r <;> simp_all +decide [ ENNReal.ofReal_pow ];
    · cases abs_cases y <;> cases lt_or_gt_of_ne hy₂ <;> cases lt_or_gt_of_ne hy₃ <;> linarith;
    · split_ifs <;> norm_num [ ENNReal.ofReal_pow ];
      rw [ ENNReal.ofReal_pow ( by linarith ) ];
  rw [ h_integral_eq, MeasureTheory.lintegral_congr_ae h_integrand ];
  -- Apply the result from `integral_4r_minus_abs_sq` to conclude the proof.
  have h_integral_eq : ∫⁻ (y : ℝ) in Set.Icc (-2 * r) (2 * r), ENNReal.ofReal ((4 * r - |y|) ^ 2) = ENNReal.ofReal (112 / 3 * r ^ 3) := by
    rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · convert congr_arg ENNReal.ofReal ( integral_4r_minus_abs_sq r hr0 ) using 1;
      norm_num;
    · exact Continuous.integrableOn_Icc ( by continuity );
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  rw [ ← h_integral_eq, ← MeasureTheory.lintegral_indicator ];
  · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
    grind;
  · norm_num

lemma volume_doubleFillSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (doubleFillSet r) = ENNReal.ofReal (112 / 3 * r ^ 3) := by
  -- Express the volume as a double integral over u0 and u1.
  have h_volume : volume (doubleFillSet r) = ∫⁻ u0 : T1, ∫⁻ u1 : T1, (volume {c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r}) ^ 2 := by
    have h_volume : volume (doubleFillSet r) = ∫⁻ (u : Fin 4 → T1), (if (∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r) ∧ (∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 3) z ≤ r) then 1 else 0) := by
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      exact?;
      · apply_rules [ IsClosed.measurableSet, IsOpen.measurableSet ];
        refine' IsClosed.inter _ _;
        · refine' isClosed_of_closure_subset _;
          intro u hu;
          rw [ mem_closure_iff_seq_limit ] at hu;
          obtain ⟨ x, hx₁, hx₂ ⟩ := hu;
          choose z hz using hx₁;
          -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
          obtain ⟨z', hz'⟩ : ∃ z' : T1, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
            have h_compact : IsCompact (Set.univ : Set T1) := by
              exact isCompact_univ;
            have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
          obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
          use z';
          have h_dist : Filter.Tendsto (fun n => dist (x (subseq n) 0) (z (subseq n))) Filter.atTop (nhds (dist (u 0) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 1) (z (subseq n))) Filter.atTop (nhds (dist (u 1) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 2) (z (subseq n))) Filter.atTop (nhds (dist (u 2) z')) := by
            exact ⟨ Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 0 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 1 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 2 ) hsubseq₂ ⟩;
          exact ⟨ le_of_tendsto_of_tendsto' h_dist.1 tendsto_const_nhds fun n => hz _ |>.1, le_of_tendsto_of_tendsto' h_dist.2.1 tendsto_const_nhds fun n => hz _ |>.2.1, le_of_tendsto_of_tendsto' h_dist.2.2 tendsto_const_nhds fun n => hz _ |>.2.2 ⟩;
        · refine' isClosed_of_closure_subset _;
          intro u hu;
          rw [ mem_closure_iff_seq_limit ] at hu;
          obtain ⟨ x, hx₁, hx₂ ⟩ := hu;
          choose z hz using hx₁;
          -- Since $z_n$ is a sequence in a compact space, it has a convergent subsequence.
          obtain ⟨z', hz'⟩ : ∃ z' : T1, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
            have h_compact : IsCompact (Set.univ : Set T1) := by
              exact isCompact_univ;
            have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
          obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
          use z';
          have h_dist : Filter.Tendsto (fun n => dist (x (subseq n) 0) (z (subseq n))) Filter.atTop (nhds (dist (u 0) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 1) (z (subseq n))) Filter.atTop (nhds (dist (u 1) z')) ∧ Filter.Tendsto (fun n => dist (x (subseq n) 3) (z (subseq n))) Filter.atTop (nhds (dist (u 3) z')) := by
            exact ⟨ Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 0 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 1 ) hsubseq₂, Filter.Tendsto.dist ( tendsto_pi_nhds.mp ( hx₂.comp hsubseq₁.tendsto_atTop ) 3 ) hsubseq₂ ⟩;
          exact ⟨ le_of_tendsto_of_tendsto' h_dist.1 tendsto_const_nhds fun n => hz _ |>.1, le_of_tendsto_of_tendsto' h_dist.2.1 tendsto_const_nhds fun n => hz _ |>.2.1, le_of_tendsto_of_tendsto' h_dist.2.2 tendsto_const_nhds fun n => hz _ |>.2.2 ⟩;
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
        exact Filter.Eventually.of_forall fun x => by unfold doubleFillSet; aesop;
    have h_fubini : ∀ (f : (Fin 4 → T1) → ENNReal), Measurable f → ∫⁻ (u : Fin 4 → T1), f u = ∫⁻ (u0 : T1), ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), ∫⁻ (u3 : T1), f (fun i => if i = 0 then u0 else if i = 1 then u1 else if i = 2 then u2 else u3) := by
      intro f hf
      have h_fubini : ∫⁻ (u : Fin 4 → T1), f u = ∫⁻ (u : T1 × T1 × T1 × T1), f (fun i => if i = 0 then u.1 else if i = 1 then u.2.1 else if i = 2 then u.2.2.1 else u.2.2.2) := by
        have h_fubini : MeasureTheory.MeasureSpace.volume = MeasureTheory.Measure.map (fun u : T1 × T1 × T1 × T1 => fun i : Fin 4 => if i = 0 then u.1 else if i = 1 then u.2.1 else if i = 2 then u.2.2.1 else u.2.2.2) (MeasureTheory.Measure.prod (MeasureTheory.MeasureSpace.volume) (MeasureTheory.Measure.prod (MeasureTheory.MeasureSpace.volume) (MeasureTheory.Measure.prod (MeasureTheory.MeasureSpace.volume) (MeasureTheory.MeasureSpace.volume)))) := by
          refine' MeasureTheory.Measure.pi_eq _;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_four ] ;
          · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
            erw [ show { x : T1 × T1 × T1 × T1 | x.1 ∈ s 0 ∧ x.2.1 ∈ s 1 ∧ x.2.2.1 ∈ s 2 ∧ x.2.2.2 ∈ s 3 } = ( s 0 ×ˢ s 1 ×ˢ s 2 ×ˢ s 3 ) by ext ; aesop ] ; simp +decide [ mul_assoc ] ;
          · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd.fst; exact measurable_snd.snd.snd ] ;
          · exact MeasurableSet.univ_pi hs;
        rw [ h_fubini, MeasureTheory.lintegral_map ];
        · rfl;
        · exact hf;
        · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd.fst; exact measurable_snd.snd.snd ] ;
      erw [ h_fubini, MeasureTheory.lintegral_prod ];
      · congr! 2;
        erw [ MeasureTheory.lintegral_prod ];
        · congr! 2;
          erw [ MeasureTheory.lintegral_prod ];
          exact hf.comp ( measurable_pi_lambda _ fun i => by fin_cases i <;> measurability ) |> Measurable.aemeasurable;
        · exact hf.comp ( measurable_pi_lambda _ fun i => by fin_cases i <;> measurability ) |> Measurable.aemeasurable;
      · exact hf.aemeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd.fst; exact measurable_snd.snd.snd ] ) );
    rw [ h_volume, h_fubini ];
    · refine' MeasureTheory.lintegral_congr fun u0 => MeasureTheory.lintegral_congr fun u1 => _;
      simp +decide [ sq, Set.indicator ];
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      change ∫⁻ u2 in { c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r }, volume { c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r } = _;
      · simp +decide [ mul_comm ];
      · refine' IsClosed.measurableSet _;
        have h_closed : IsCompact {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} := by
          have h_closed : IsCompact {z : T1 | dist u0 z ≤ r} := by
            convert ProperSpace.isCompact_closedBall u0 r using 1;
            exact Set.ext fun x => by simp +decide [ dist_comm ] ;
          exact h_closed.inter_right ( isClosed_le ( continuous_const.dist continuous_id' ) continuous_const );
        have h_closed : IsClosed (Set.image (fun p : T1 × T1 => p.1) {p : T1 × T1 | p.2 ∈ {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} ∧ dist p.1 p.2 ≤ r}) := by
          apply_rules [ IsCompact.isClosed, IsCompact.image ];
          · have h_closed : IsCompact {p : T1 × T1 | p.2 ∈ {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} ∧ dist p.1 p.2 ≤ r} := by
              have h_closed : IsClosed {p : T1 × T1 | p.2 ∈ {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} ∧ dist p.1 p.2 ≤ r} := by
                exact IsClosed.inter ( h_closed.isClosed.preimage continuous_snd ) ( isClosed_le ( continuous_fst.dist continuous_snd ) continuous_const )
              exact IsCompact.of_isClosed_subset ( isCompact_univ.prod ‹IsCompact { z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r } › ) h_closed fun p hp => ⟨ Set.mem_univ _, hp.1 ⟩;
            exact h_closed;
          · exact continuous_fst;
        convert h_closed using 1;
        ext; simp [Set.mem_image];
        simp +decide only [and_assoc];
      · filter_upwards [ ] with u2 ; by_cases h : ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist u2 z ≤ r <;> simp +decide [ h ];
        rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
        change ∫⁻ u3 in { c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r }, 1 = _;
        · norm_num;
        · have h_closed : IsClosed {c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r} := by
            have h_compact : IsCompact {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} := by
              have h_compact : IsCompact {z : T1 | dist u0 z ≤ r} := by
                convert ProperSpace.isCompact_closedBall u0 r using 1;
                exact Set.ext fun x => by simp +decide [ dist_comm ] ;
              exact h_compact.inter_right ( isClosed_le ( continuous_const.dist continuous_id' ) continuous_const )
            have h_closed : IsClosed (Set.image (fun p : T1 × T1 => p.1) {p : T1 × T1 | p.2 ∈ {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} ∧ dist p.1 p.2 ≤ r}) := by
              apply_rules [ IsCompact.isClosed, IsCompact.image ];
              · have h_closed : IsCompact {p : T1 × T1 | p.2 ∈ {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} ∧ dist p.1 p.2 ≤ r} := by
                  have h_closed : IsClosed {p : T1 × T1 | p.2 ∈ {z : T1 | dist u0 z ≤ r ∧ dist u1 z ≤ r} ∧ dist p.1 p.2 ≤ r} := by
                    exact IsClosed.inter ( h_compact.isClosed.preimage continuous_snd ) ( isClosed_le ( continuous_fst.dist continuous_snd ) continuous_const )
                  exact IsCompact.of_isClosed_subset ( isCompact_univ.prod h_compact ) h_closed fun p hp => ⟨ Set.mem_univ _, hp.1 ⟩;
                exact h_closed;
              · exact continuous_fst;
            convert h_closed using 1;
            ext; simp [Set.mem_image];
            exact ⟨ fun ⟨ z, hz1, hz2, hz3 ⟩ => ⟨ z, ⟨ hz1, hz2 ⟩, hz3 ⟩, fun ⟨ z, ⟨ hz1, hz2 ⟩, hz3 ⟩ => ⟨ z, hz1, hz2, hz3 ⟩ ⟩;
          exact h_closed.measurableSet;
        · norm_num [ Filter.EventuallyEq, Set.indicator ];
    · refine' Measurable.ite _ measurable_const measurable_const;
      have h_measurable : MeasurableSet {a : Fin 4 → T1 | ∃ z : T1, dist (a 0) z ≤ r ∧ dist (a 1) z ≤ r ∧ dist (a 2) z ≤ r} := by
        have h_measurable : MeasurableSet {a : Fin 3 → T1 | ∃ z : T1, dist (a 0) z ≤ r ∧ dist (a 1) z ≤ r ∧ dist (a 2) z ≤ r} := by
          have h_measurable : IsClosed {a : Fin 3 → T1 | ∃ z : T1, dist (a 0) z ≤ r ∧ dist (a 1) z ≤ r ∧ dist (a 2) z ≤ r} := by
            have h_closed : IsClosed {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
              exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 2 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
            have h_closed : IsClosed (Set.image (fun p : (Fin 3 → T1) × T1 => p.1) {p : (Fin 3 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r}) := by
              apply_rules [ IsCompact.isClosed, IsCompact.image ];
              · exact IsCompact.of_isClosed_subset ( isCompact_univ ) h_closed ( Set.subset_univ _ );
              · exact continuous_fst;
            convert h_closed using 1;
            ext; simp [Set.mem_image];
          exact h_measurable.measurableSet;
        convert h_measurable.preimage ( show Measurable ( fun a : Fin 4 → T1 => fun i : Fin 3 => a ( Fin.castSucc i ) ) from measurable_pi_lambda _ fun _ => measurable_pi_apply _ ) using 1;
      have h_measurable : MeasurableSet {a : Fin 4 → T1 | ∃ z : T1, dist (a 0) z ≤ r ∧ dist (a 1) z ≤ r ∧ dist (a 3) z ≤ r} := by
        convert h_measurable.preimage ( show Measurable ( fun a : Fin 4 → T1 => fun i => if i = 0 then a 0 else if i = 1 then a 1 else if i = 2 then a 3 else a 2 ) from ?_ ) using 1;
        exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 1; exact measurable_pi_apply 3; exact measurable_pi_apply 2 ] ;
      exact MeasurableSet.inter ‹_› ‹_›;
  -- By translation invariance, the integral over u0 is trivial (IsProbabilityMeasure gives volume 1), so:
  have h_translation_invariance : ∀ u0 : T1, ∫⁻ u1 : T1, (volume {c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r}) ^ 2 = ∫⁻ u1 : T1, (volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r}) ^ 2 := by
    intro u0
    have h_translation_invariance : ∀ u1 : T1, volume {c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r} = volume {c : T1 | ∃ z : T1, dist (0 : T1) z ≤ r ∧ dist (u1 - u0) z ≤ r ∧ dist c z ≤ r} := by
      intro u1
      have h_translation_invariance : ∀ c : T1, (∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r) ↔ (∃ z : T1, dist 0 z ≤ r ∧ dist (u1 - u0) z ≤ r ∧ dist (c - u0) z ≤ r) := by
        intro c
        constructor
        intro h
        obtain ⟨z, hz⟩ := h
        use z - u0
        simp [hz];
        rintro ⟨ z, hz₁, hz₂, hz₃ ⟩ ; use z + u0; simp_all +decide [ dist_eq_norm ] ;
        exact ⟨ by convert hz₂ using 1; abel_nf, by convert hz₃ using 1; abel_nf ⟩;
      rw [ show { c : T1 | ∃ z : T1, dist u0 z ≤ r ∧ dist u1 z ≤ r ∧ dist c z ≤ r } = ( fun c => c - u0 ) ⁻¹' { c : T1 | ∃ z : T1, dist 0 z ≤ r ∧ dist ( u1 - u0 ) z ≤ r ∧ dist c z ≤ r } by ext; aesop ];
      convert MeasureTheory.measure_preimage_add_right _ u0 using 1;
      rotate_left;
      exact volume;
      · infer_instance;
      · rw [ ← MeasureTheory.measure_preimage_add_right ] ; norm_num;
        swap;
        exact u0;
        norm_num [ add_assoc ];
    simp +decide only [h_translation_invariance];
    rw [ eq_comm, ← MeasureTheory.lintegral_sub_right_eq_self ];
  have := lintegral_fill_fiber_sq_T1 r hr0 hr; aesop;

/-! ### Fin 4 coordinate factorisation -/

lemma volume_coordFactored4_eq_pow_zero (S : Set (Fin 4 → T1)) (hS : MeasurableSet S) :
    volume ({pts : Fin 4 → (Fin 0 → T1) | ∀ i : Fin 0, (fun j : Fin 4 => pts j i) ∈ S} : Set (Fin 4 → Fin 0 → T1))
    = (volume S) ^ 0 := by
  simp +decide [MeasureTheory.MeasureSpace.volume]
  erw [MeasureTheory.Measure.pi_univ]; norm_num

lemma measurable_transpose4 (d : ℕ) :
    Measurable (fun (f : Fin 4 → Fin d → T1) (i : Fin d) (j : Fin 4) => f j i) := by
  fun_prop

lemma volume_map_transpose4 (d : ℕ) :
    Measure.map (fun (f : Fin 4 → Fin d → T1) (i : Fin d) (j : Fin 4) => f j i) volume
    = (volume : Measure (Fin d → Fin 4 → T1)) := by
  apply MeasureTheory.Measure.ext
  intro s hs
  by_contra h_contra
  have h_prod_measure : ∀ (s : Set (Fin d → Fin 4 → T1)), MeasurableSet s → (Measure.pi fun _ : Fin d => Measure.pi fun _ : Fin 4 => MeasureSpace.volume) s = (Measure.pi (fun _ : Fin d × Fin 4 => MeasureSpace.volume)) (Set.preimage (fun f : Fin d × Fin 4 → T1 => fun i j => f (i, j)) s) := by
    intro s hs
    have h_prod_measure : (Measure.pi (fun _ : Fin d × Fin 4 => MeasureSpace.volume)) = Measure.map (fun f : Fin d → Fin 4 → T1 => fun p : Fin d × Fin 4 => f p.1 p.2) (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin 4 => MeasureSpace.volume))) := by
      apply MeasureTheory.Measure.pi_eq;
      intro s hs; erw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun f p => f p.1 p.2 ) ⁻¹' Set.univ.pi s = Set.pi Set.univ fun i => Set.pi Set.univ fun j => s ( i, j ) from ?_ ];
        · rw [ MeasureTheory.Measure.pi_pi ];
          rw [ Finset.prod_congr rfl fun i _ => MeasureTheory.Measure.pi_pi _ _ ];
          rw [ ← Finset.prod_product' ];
          refine' Finset.prod_bij ( fun x _ => ( x.1, x.2 ) ) _ _ _ _ <;> simp +decide;
        · ext; simp [Set.mem_preimage, Set.mem_pi];
      · fun_prop;
      · exact MeasurableSet.univ_pi hs;
    rw [ h_prod_measure, MeasureTheory.Measure.map_apply ];
    · congr! 1;
    · fun_prop;
    · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
  have h_prod_measure : (Measure.pi (fun _ : Fin d × Fin 4 => MeasureSpace.volume)) (Set.preimage (fun f : Fin d × Fin 4 → T1 => fun i j => f (i, j)) s) = (Measure.pi (fun _ : Fin 4 × Fin d => MeasureSpace.volume)) (Set.preimage (fun f : Fin 4 × Fin d → T1 => fun i j => f (j, i)) (Set.preimage (fun f : Fin d → Fin 4 → T1 => fun i j => f i j) s)) := by
    have h_prod_measure : Measure.pi (fun _ : Fin 4 × Fin d => MeasureSpace.volume) = Measure.map (fun f : Fin d × Fin 4 → T1 => fun p : Fin 4 × Fin d => f (p.2, p.1)) (Measure.pi (fun _ : Fin d × Fin 4 => MeasureSpace.volume)) := by
      refine' MeasureTheory.Measure.pi_eq _;
      intro s hs; erw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun f p => f ( p.2, p.1 ) ) ⁻¹' Set.univ.pi s = Set.univ.pi ( fun p => s ( p.2, p.1 ) ) from ?_, MeasureTheory.Measure.pi_pi ];
        · conv_rhs => rw [ ← Equiv.prod_comp ( Equiv.prodComm _ _ ) ] ;
          rfl;
        · grind;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · exact MeasurableSet.univ_pi hs;
    rw [ h_prod_measure, MeasureTheory.Measure.map_apply ];
    · lia;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
  convert h_prod_measure using 1;
  erw [ MeasureTheory.Measure.pi_eq ];
  rotate_right;
  exact MeasureTheory.Measure.map ( fun f : Fin 4 → Fin d → T1 => fun p => f p.2 p.1 ) ( MeasureTheory.Measure.pi fun _ : Fin 4 => MeasureTheory.Measure.pi fun _ : Fin d => MeasureTheory.MeasureSpace.volume );
  · rw [ MeasureTheory.Measure.map_apply ];
    · constructor <;> intro h <;> simp_all +decide [ Set.preimage ];
      convert h_contra _;
      rw [ MeasureTheory.Measure.map_apply ];
      · convert h using 1;
        convert ‹∀ s : Set ( Fin d → Fin 4 → T1 ), MeasurableSet s → ( Measure.pi fun x => Measure.pi fun x => volume ) s = ( Measure.pi fun x => volume ) { x | ( fun i j => x ( i, j ) ) ∈ s } › s hs using 1;
        exact h_prod_measure.symm;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ |> Measurable.comp <| measurable_pi_apply _;
      · lia;
    · fun_prop;
    · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
  · intro s hs; erw [ MeasureTheory.Measure.map_apply ];
    · rw [ show ( fun f p => f p.2 p.1 ) ⁻¹' Set.univ.pi s = Set.pi Set.univ fun i => Set.pi Set.univ fun j => s ( j, i ) from ?_ ];
      · rw [ MeasureTheory.Measure.pi_pi ];
        rw [ Finset.prod_congr rfl fun i _ => MeasureTheory.Measure.pi_pi _ _ ];
        rw [ ← Finset.prod_product' ];
        refine' Finset.prod_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp +decide;
      · ext; simp [Set.mem_preimage, Set.mem_pi];
        exact ⟨ fun h i j => h j i, fun h i j => h j i ⟩;
    · fun_prop;
    · exact MeasurableSet.univ_pi hs

lemma coordFactored4_eq_preimage_pi (d : ℕ) (S : Set (Fin 4 → T1)) :
    ({pts : Fin 4 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 4 => pts j i) ∈ S} : Set (Fin 4 → Fin d → T1))
    = (fun (f : Fin 4 → Fin d → T1) (i : Fin d) (j : Fin 4) => f j i) ⁻¹' (Set.univ.pi (fun _ : Fin d => S)) := by
  ext; aesop

lemma volume_coordFactored4_eq_pow_succ (d : ℕ) (S : Set (Fin 4 → T1)) (hS : MeasurableSet S)
    (ih : volume ({pts : Fin 4 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 4 => pts j i) ∈ S} : Set (Fin 4 → Fin d → T1))
          = (volume S) ^ d) :
    volume ({pts : Fin 4 → (Fin (d + 1) → T1) | ∀ i : Fin (d + 1), (fun j : Fin 4 => pts j i) ∈ S} : Set (Fin 4 → Fin (d + 1) → T1))
    = (volume S) ^ (d + 1) := by
  rw [coordFactored4_eq_preimage_pi]
  convert congr_arg (fun x : ENNReal => x) (MeasureTheory.Measure.pi_pi (fun _ => volume) fun (_ : Fin (d + 1)) => S) using 1
  · convert congr_arg (fun x : MeasureTheory.Measure (Fin (d + 1) → Fin 4 → T1) => x (Set.univ.pi fun _ => S)) (volume_map_transpose4 (d + 1)) using 1
    rw [MeasureTheory.Measure.map_apply]
    · exact measurable_transpose4 _
    · exact MeasurableSet.univ_pi fun _ => hS
  · norm_num

lemma volume_coordFactored4_eq_pow (d : ℕ) (S : Set (Fin 4 → T1)) (hS : MeasurableSet S) :
    volume ({pts : Fin 4 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 4 => pts j i) ∈ S} : Set (Fin 4 → Fin d → T1))
    = (volume S) ^ d := by
  induction' d with d ih
  · convert volume_coordFactored4_eq_pow_zero S hS using 1
  · exact volume_coordFactored4_eq_pow_succ d S hS ih

/-
The double-fill set on Torus d equals the coordinate-factored double-fill set (for r ≤ 1/4).
-/
lemma doubleFillSet_torus_eq (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ({pts : Fin 4 → (Fin d → T1) |
      (∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r) ∧
      (∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 3) z ≤ r)} : Set (Fin 4 → Fin d → T1))
    = {pts : Fin 4 → (Fin d → T1) | ∀ i : Fin d, (fun j : Fin 4 => pts j i) ∈ doubleFillSet r} := by
  ext pts;
  constructor <;> intro h <;> dsimp [doubleFillSet] at *;
  · intro i
    obtain ⟨z1, hz1⟩ := h.left
    obtain ⟨z2, hz2⟩ := h.right;
    refine' ⟨ ⟨ z1 i, _, _, _ ⟩, ⟨ z2 i, _, _, _ ⟩ ⟩ <;> simp_all +decide [ dist_pi_le_iff ];
  · choose z1 hz1 z2 hz2 using h;
    choose z3 hz3 using z1;
    refine' ⟨ ⟨ z3, _, _, _ ⟩, ⟨ hz1, _, _, _ ⟩ ⟩ <;> simp_all +decide [ dist_pi_le_iff ]

lemma doubleFillSet_measurableSet (r : ℝ) : MeasurableSet (doubleFillSet r) := by
  refine' MeasurableSet.inter _ _;
  · -- The set is closed under the continuous map that takes u to the distances from u 0, u 1, and u 2 to z. Therefore, the set is closed, and hence measurable.
    have h_closed : IsClosed {u : Fin 4 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 2) z ≤ r} := by
      refine' IsCompact.isClosed _;
      have h_closed : IsCompact {p : (Fin 4 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 2) p.2 ≤ r} := by
        refine' IsCompact.of_isClosed_subset ( isCompact_univ.prod ( isCompact_univ ) ) _ _;
        · exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply _ |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply _ |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply _ |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
        · exact fun p hp => ⟨ Set.mem_univ _, Set.mem_univ _ ⟩;
      convert h_closed.image ( show Continuous fun p : ( Fin 4 → T1 ) × T1 => p.1 from continuous_fst ) using 1 ; aesop;
    exact h_closed.measurableSet;
  · -- The set of points where there exists a z such that the distances to three fixed points are all less than or equal to r is closed.
    have h_closed : IsClosed {u : Fin 4 → T1 | ∃ z : T1, dist (u 0) z ≤ r ∧ dist (u 1) z ≤ r ∧ dist (u 3) z ≤ r} := by
      refine' IsCompact.isClosed _;
      have h_closed : IsCompact {p : (Fin 4 → T1) × T1 | dist (p.1 0) p.2 ≤ r ∧ dist (p.1 1) p.2 ≤ r ∧ dist (p.1 3) p.2 ≤ r} := by
        refine' IsClosed.isCompact _;
        exact IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 0 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( IsClosed.inter ( isClosed_le ( Continuous.dist ( continuous_apply 1 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) ( isClosed_le ( Continuous.dist ( continuous_apply 3 |> Continuous.comp <| continuous_fst ) continuous_snd ) continuous_const ) );
      convert h_closed.image ( continuous_fst ) using 1;
      ext; aesop;
    exact h_closed.measurableSet

/-! ## Mid-regime closed forms for `r ∈ (1/3, 1/2]` (OQ-18 reframe, session 65)

Under matched radius `r_d = p^{1/d}/2`, the regime `r ≤ 1/4` only covers small `d`. As
`d → ∞` we have `r_d → 1/2`, so the relevant asymptotic regime is `r ∈ (1/3, 1/2]`.

Per-coordinate 3-clique probability for three iid uniform points on T1 with threshold
`r ∈ (1/3, 1/2]`:

  `γ(r) := 3 r² + (3 r − 1)²`.

Verification:
- At `r = 1/3`: `γ = 3·(1/9) + 0 = 1/3`. Matches `3 r² = 1/3` (continuity with low-regime).
- At `r = 1/2`: `γ = 3/4 + (1/2)² = 1`. Matches the trivial fact that any two points on
  a circle of length 1 are within distance 1/2.

Derivation: condition on `u₁ = 0`. The pair-edge events `|u₂| ≤ r ∧ |u₃| ≤ r` give a
square of side `2r` for the joint distribution of `(u₂, u₃)`. The third edge
`|u₂ − u₃| ≤ r` (mod 1) is the union of the diagonal strip `|u₂ − u₃| ≤ r` and the
wraparound strips `|u₂ − u₃ − 1| ≤ r` ∪ `|u₂ − u₃ + 1| ≤ r`. For `r ≤ 1/4`, only the
diagonal strip intersects the square, giving area `3 r²`. For `r ∈ (1/3, 1/2]`, the
wraparound strips also clip the corners of the square, adding `(3r − 1)²`.

References: audit `my_theorems/oq18_math_audit.md` § "γ(r) for r ∈ (1/3, 1/2]";
session-63 entry in `wiki/decisions.md`.

These lemmas are scaffolding — proofs deferred to Aristotle (statement scope is the
same shape as the existing `volume_triangleSet` / `integral_triangle_eq_pow`). -/

/-- The mid-regime per-coordinate 3-clique probability `γ(r) = 3r² + (3r−1)²`. -/
noncomputable def gammaMid (r : ℝ) : ℝ := 3 * r ^ 2 + (3 * r - 1) ^ 2

@[simp] lemma gammaMid_apply (r : ℝ) : gammaMid r = 3 * r ^ 2 + (3 * r - 1) ^ 2 := rfl

/-- Continuity at the regime boundary `r = 1/3`: `γ(1/3) = 1/3 = 3·(1/3)²`. -/
lemma gammaMid_at_one_third : gammaMid (1/3) = 1/3 := by
  unfold gammaMid; ring

/-- Right endpoint: `γ(1/2) = 1` (any two points on T1 are within distance 1/2). -/
lemma gammaMid_at_one_half : gammaMid (1/2) = 1 := by
  unfold gammaMid; ring

/-- Algebraic identity used downstream: `γ(p^{1/d}/2) = 3·p^{2/d} − 3·p^{1/d} + 1`. -/
lemma gammaMid_of_matchRadius_form (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hd : 1 ≤ d) :
    gammaMid (p ^ ((d : ℝ)⁻¹) / 2)
      = 3 * p ^ ((2 : ℝ) * (d : ℝ)⁻¹) - 3 * p ^ ((d : ℝ)⁻¹) + 1 := by
  unfold gammaMid
  have hsq : p ^ ((d : ℝ)⁻¹) * p ^ ((d : ℝ)⁻¹) = p ^ ((2 : ℝ) * (d : ℝ)⁻¹) := by
    rw [← Real.rpow_add hp0]; congr 1; ring
  nlinarith [hsq]

/-! ### Helper lemmas for volume_triangleSet_mid -/

/-
Shared infrastructure: reduce the volume of `triangleSet r` on T1 to a real integral
    over `[-r, r]`, computing the measure of the intersection of two `r`-balls. Valid for
    any `0 ≤ r ≤ 1/2`.
-/
lemma volume_triangleSet_eq_real_integral (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/2) :
    volume (triangleSet r) = ∫⁻ (x : ℝ) in Set.Icc (-r) r,
      volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk x : T1) r) := by
  have h_volume : volume (triangleSet r) = ∫⁻ (u0 : T1), ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), (if dist u0 u1 ≤ r ∧ dist u0 u2 ≤ r ∧ dist u1 u2 ≤ r then 1 else 0) ∂volume ∂volume ∂volume := by
    -- The volume of the triangle set is equal to the integral of the indicator function over the set.
    have h_triangle_volume : volume (triangleSet r) = ∫⁻ (u : Fin 3 → T1), (if dist (u 0) (u 1) ≤ r ∧ dist (u 0) (u 2) ≤ r ∧ dist (u 1) (u 2) ≤ r then 1 else 0) ∂volume := by
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      exact?;
      · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) );
      · exact Filter.Eventually.of_forall fun x => by unfold triangleSet; aesop; ;
    have h_fubini : ∀ {f : (Fin 3 → T1) → ENNReal}, Measurable f → ∫⁻ (u : Fin 3 → T1), f u ∂volume = ∫⁻ (u0 : T1), ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), f (fun i => if i = 0 then u0 else if i = 1 then u1 else u2) ∂volume ∂volume ∂volume := by
      intro f hf;
      have h_fubini : ∀ {f : (Fin 3 → T1) → ENNReal}, Measurable f → ∫⁻ (u : Fin 3 → T1), f u ∂volume = ∫⁻ (u : T1 × T1 × T1), f (fun i => if i = 0 then u.1 else if i = 1 then u.2.1 else u.2.2) ∂(volume.prod (volume.prod volume)) := by
        intro f hf;
        have h_fubini : ∀ {f : (Fin 3 → T1) → ENNReal}, Measurable f → ∫⁻ (u : Fin 3 → T1), f u ∂volume = ∫⁻ (u : T1 × T1 × T1), f (fun i => if i = 0 then u.1 else if i = 1 then u.2.1 else u.2.2) ∂(volume.prod (volume.prod volume)) := by
          intro f hf
          have h_iso : (volume : Measure (Fin 3 → T1)) = Measure.map (fun u : T1 × T1 × T1 => fun i => if i = 0 then u.1 else if i = 1 then u.2.1 else u.2.2) (volume.prod (volume.prod volume)) := by
            simp +decide [ MeasureTheory.MeasureSpace.volume ];
            erw [ MeasureTheory.Measure.pi_eq ];
            intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three ] ;
            · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
              erw [ show { x : T1 × T1 × T1 | x.1 ∈ s 0 ∧ x.2.1 ∈ s 1 ∧ x.2.2 ∈ s 2 } = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; simp +decide [ mul_assoc ];
            · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
            · exact MeasurableSet.univ_pi hs
          rw [ h_iso, MeasureTheory.lintegral_map ];
          · exact hf;
          · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
        exact h_fubini hf;
      rw [ h_fubini hf, MeasureTheory.lintegral_prod ];
      · congr! 2;
        erw [ MeasureTheory.lintegral_prod ];
        exact hf.comp ( measurable_pi_lambda _ fun i => by fin_cases i <;> measurability ) |> Measurable.aemeasurable;
      · exact hf.aemeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ) );
    convert h_fubini _ using 1;
    exact Measurable.ite ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) <| MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) <| measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
  -- Fix u0: by translation invariance, the iterated integral doesn't depend on u0, so the outer u0 integral just multiplies by 1 (probability measure).
  have h_translation_invariance : ∀ (u0 : T1), ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), (if dist u0 u1 ≤ r ∧ dist u0 u2 ≤ r ∧ dist u1 u2 ≤ r then 1 else 0) ∂volume ∂volume = ∫⁻ (u1 : T1), ∫⁻ (u2 : T1), (if dist 0 u1 ≤ r ∧ dist 0 u2 ≤ r ∧ dist u1 u2 ≤ r then 1 else 0) ∂volume ∂volume := by
    intro u0
    have h_translation_invariance : ∀ (f : T1 → T1 → ENNReal), (∫⁻ (u1 : T1), ∫⁻ (u2 : T1), f u1 u2 ∂volume ∂volume) = (∫⁻ (u1 : T1), ∫⁻ (u2 : T1), f (u1 + u0) (u2 + u0) ∂volume ∂volume) := by
      intro f
      have h_translation_invariance : ∀ (g : T1 → ENNReal), ∫⁻ (u : T1), g u ∂volume = ∫⁻ (u : T1), g (u + u0) ∂volume := by
        intro g;
        rw [ ← MeasureTheory.lintegral_add_right_eq_self ];
      rw [ h_translation_invariance ];
      exact MeasureTheory.lintegral_congr fun u => h_translation_invariance _ ▸ rfl;
    convert h_translation_invariance _ using 4 ; norm_num [ dist_eq_norm ];
  -- For fixed u0 = 0, the inner u2 integral over {u2 : dist(0,u2) ≤ r ∧ dist(u1,u2) ≤ r} equals volume(closedBall(0,r) ∩ closedBall(u1,r)).
  have h_inner_integral : ∀ (u1 : T1), ∫⁻ (u2 : T1), (if dist 0 u2 ≤ r ∧ dist u1 u2 ≤ r then 1 else 0) ∂volume = volume (Metric.closedBall 0 r ∩ Metric.closedBall u1 r) := by
    intro u1; rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    change ∫⁻ x in Metric.closedBall 0 r ∩ Metric.closedBall u1 r, 1 ∂volume = volume ( Metric.closedBall 0 r ∩ Metric.closedBall u1 r );
    · norm_num;
    · exact measurableSet_closedBall.inter measurableSet_closedBall;
    · norm_num [ Filter.EventuallyEq, Set.indicator ];
      simp +decide only [dist_comm];
      exact Filter.Eventually.of_forall fun _ => trivial;
  -- Lift the T1 integral to ℝ: ∫_{x ∈ [-r,r]} volume(closedBall(0,r) ∩ closedBall(mk(x),r)) dx, using AddCircle.measurePreserving_mk and the fact that dist(0, mk(x)) = |x| for |x| ≤ r ≤ 1/2.
  have h_lift_integral : ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then volume (Metric.closedBall 0 r ∩ Metric.closedBall u1 r) else 0) ∂volume = ∫⁻ (x : ℝ) in Set.Icc (-r) r, volume (Metric.closedBall 0 r ∩ Metric.closedBall (QuotientAddGroup.mk x : T1) r) := by
    have h_lift_integral : ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then volume (Metric.closedBall 0 r ∩ Metric.closedBall u1 r) else 0) ∂volume = ∫⁻ (x : ℝ) in Set.Icc (-1 / 2) (1 / 2), (if |x| ≤ r then volume (Metric.closedBall 0 r ∩ Metric.closedBall (QuotientAddGroup.mk x : T1) r) else 0) := by
      have h_lift_integral : ∫⁻ (u1 : T1), (if dist 0 u1 ≤ r then volume (Metric.closedBall 0 r ∩ Metric.closedBall u1 r) else 0) ∂volume = ∫⁻ (x : ℝ) in Set.Ioc (-1 / 2) (1 / 2), (if dist 0 (QuotientAddGroup.mk x : T1) ≤ r then volume (Metric.closedBall 0 r ∩ Metric.closedBall (QuotientAddGroup.mk x : T1) r) else 0) := by
        have := AddCircle.measurePreserving_mk ( 1 : ℝ );
        specialize this ( -1 / 2 );
        rw [ ← this.lintegral_comp ] ; norm_num;
        refine' Measurable.ite _ _ measurable_const;
        · exact measurableSet_le ( measurable_const.dist measurable_id' ) measurable_const;
        · have h_measurable : Measurable (fun u1 : T1 => volume (Metric.closedBall 0 r ∩ Metric.closedBall u1 r)) := by
            have h_closedBall_measurable : MeasurableSet {p : T1 × T1 | p.1 ∈ Metric.closedBall 0 r ∧ p.1 ∈ Metric.closedBall p.2 r} := by
              simp +zetaDelta at *;
              exact MeasurableSet.mem ( MeasurableSet.inter ( measurableSet_le ( measurable_norm.comp measurable_fst ) measurable_const ) ( measurableSet_le ( measurable_fst.dist measurable_snd ) measurable_const ) )
            convert measurable_measure_prodMk_right h_closedBall_measurable using 1;
            infer_instance;
          convert h_measurable using 1;
      rw [ h_lift_integral, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc ];
      norm_num [ dist_eq_norm, AddCircle.norm_eq ];
      rw [ MeasureTheory.lintegral_congr_ae ];
      filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( -1 / 2 ) ), MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( 1 / 2 ) ) ] with x hx₁ hx₂ hx₃;
      norm_num [ show round x = 0 by exact round_eq_zero_iff.mpr ⟨ by linarith [ hx₁.1 ], by linarith [ hx₁.2, show x < 1 / 2 from lt_of_le_of_ne hx₁.2 hx₃ ] ⟩ ];
    rw [ h_lift_integral, ← MeasureTheory.lintegral_indicator, ← MeasureTheory.lintegral_indicator ];
    · congr with x ; norm_num [ Set.indicator ] ; split_ifs <;> norm_num;
      · exact False.elim <| ‹¬ ( -r ≤ x ∧ x ≤ r ) › ⟨ by linarith [ abs_le.mp ‹_› ], by linarith [ abs_le.mp ‹_› ] ⟩;
      · cases abs_cases x <;> linarith;
      · exact False.elim <| ‹¬ ( - ( 1 / 2 ) ≤ x ∧ x ≤ 1 / 2 ) › ⟨ by linarith, by linarith ⟩;
    · norm_num;
    · norm_num;
  simp_all +decide [ ← MeasureTheory.lintegral_indicator, Set.indicator_apply ];
  convert h_lift_integral using 1;
  congr! 1;
  ext u1; by_cases hu1 : ‖u1‖ ≤ r <;> simp +decide [ hu1, h_inner_integral ] ;

/-- Helper: dist(0, mk b) = |b| when |b| ≤ 1/2 on T1. -/
lemma T1_dist_zero_mk (b : ℝ) (hb : |b| ≤ 1/2) :
    dist (0 : T1) (QuotientAddGroup.mk b) = |b| := by
  simp [dist_eq_norm]
  exact T1_norm_mk_of_abs_le b hb

/-- Non-wrapping ball-intersection volume on T1 for `r > 1/4` with `|b| + 2r ≤ 1`.
    Volume of `closedBall 0 r ∩ closedBall (mk b) r` equals `2r − |b|`.

    The proof strategy is the **same preimage decomposition** used in the proved
    sibling `volume_closedBall_inter_T1_wrap` (just below in this file), but the
    "wrap piece" `Set.Icc (-r) (b + r − 1)` is now empty / measure-zero because
    `hno : |b| + 2r ≤ 1` forces `b + r − 1 ≤ −r` (in fact `b + r − 1 ≤ r − 1 < −r`
    using `r ≤ 1/2`). Mirror the wrap-case proof line-for-line and discharge the
    wrap piece via `Set.Icc_eq_empty` / measure-zero.

    PROVIDED SOLUTION
    Step 1 (WLOG b ≥ 0). By negation symmetry (`AddCircle` is a group, `closedBall`
      is symmetric under negation), reduce to the case `0 ≤ b ≤ r`, exactly as in
      `volume_closedBall_inter_T1_wrap`.

    Step 2 (preimage decomposition). Push the T1 volume back to ℝ via
      `AddCircle.measurePreserving_mk (1 : ℝ)` from `-1/2` (or restrict to
      `Set.Ioc (-1/2) (1/2)`). For `x ∈ Ioc (-1/2) (1/2)` and `0 ≤ b ≤ r ≤ 1/2`:
      • `‖(mk x : T1)‖ = |x|` via `T1_norm_mk_of_abs_le`.
      • `‖(mk x : T1) - (mk b : T1)‖ = |x − b|` when `x ≥ b − 1/2`, and
        `= |x − b + 1|` otherwise — same case split as in the wrap-case proof.
      The intersection's preimage in `Ioc (-1/2) (1/2)` equals
      `Set.Icc (b − r) r ∪ Set.Icc (−r) (b + r − 1)`.

    Step 3 (wrap piece is empty). From `hno : |b| + 2 * r ≤ 1` and the WLOG
      `0 ≤ b`, we get `b + 2r ≤ 1`, i.e. `b + r − 1 ≤ −r`. Hence
      `Set.Icc (−r) (b + r − 1) ⊆ {−r}` (or is outright empty), so its volume is 0.

    Step 4 (main piece is an interval). `Set.Icc (b − r) r` has length `2r − b = 2r − |b|`
      (using `0 ≤ b`). Volume equals `ENNReal.ofReal (2r − |b|)`.

    Step 5 (assemble). `volume (A ∪ B) = volume A + volume B` (disjoint up to
      measure zero) = `ENNReal.ofReal (2r − |b|) + 0`. Close.

    A faithful copy-edit of `volume_closedBall_inter_T1_wrap` (in the same file)
    should work: keep its `h_preimage` block verbatim, then replace
    `MeasureTheory.measure_union₀` with `volume (Icc (b−r) r) = ENNReal.ofReal (2r − b)`
    (`Real.volume_Icc`) and a measure-zero discharge of the wrap piece. -/
lemma volume_closedBall_inter_T1_nowrap_large (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/2)
    (hr4 : 1/4 < r) (b : ℝ) (hb : |b| ≤ r) (hno : |b| + 2 * r ≤ 1) :
    volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) =
    ENNReal.ofReal (2 * r - |b|) := by
  sorry

lemma volume_closedBall_inter_T1_nowrap (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/2)
    (b : ℝ) (hb : |b| ≤ r) (hno : |b| + 2 * r ≤ 1) :
    volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) =
    ENNReal.ofReal (2 * r - |b|) := by
  by_cases hr4 : r ≤ 1/4
  · -- Use the existing volume_closedBall_inter_T1
    have hd : dist (0 : T1) (QuotientAddGroup.mk b) = |b| :=
      T1_dist_zero_mk b (by linarith)
    have h := volume_closedBall_inter_T1 r hr0 hr4 0 (QuotientAddGroup.mk b) (by rw [hd]; exact hb)
    rw [hd] at h; exact h
  · exact volume_closedBall_inter_T1_nowrap_large r hr0 hr (by linarith) b hb hno

/-
Wrapping case: when `|b| + 2r > 1`, the intersection volume is `4r - 1`.
    The ball `closedBall(mk b, r)` wraps around T1, creating an extra intersection.
-/
lemma volume_closedBall_inter_T1_wrap (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/2)
    (b : ℝ) (hb : |b| ≤ r) (hwrap : 1 < |b| + 2 * r) :
    volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) =
    ENNReal.ofReal (4 * r - 1) := by
  -- Assume WLOG $b \geq 0$ (by negation symmetry).
  suffices h_wlog : ∀ {b : ℝ}, 0 ≤ b → b ≤ r → 1 < b + 2 * r → volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) = ENNReal.ofReal (4 * r - 1) by
    cases abs_cases b <;> simp_all +decide;
    convert h_wlog ( show 0 ≤ -b by linarith ) ( show -b ≤ r by linarith ) ( show 1 < -b + 2 * r by linarith ) using 1;
    rw [ ← MeasureTheory.measure_preimage_add_right ] ; norm_num;
    swap;
    exact ↑b;
    norm_num [ Set.inter_comm ];
  intros b hb_nonneg hb_le_r hb_gt_one
  have h_preimage : volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) = volume (Set.Icc (b - r) r ∪ Set.Icc (-r) (b + r - 1)) := by
    have h_preimage : ∀ x ∈ Set.Ioc (-1 / 2) (1 / 2), (QuotientAddGroup.mk x : T1) ∈ Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r ↔ x ∈ Set.Icc (b - r) r ∪ Set.Icc (-r) (b + r - 1) := by
      intro x hx
      have h_dist_x : ‖(QuotientAddGroup.mk x : T1)‖ = |x| := by
        exact T1_norm_mk_of_abs_le x ( abs_le.mpr ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩ )
      have h_dist_x_b : ‖(QuotientAddGroup.mk x : T1) - (QuotientAddGroup.mk b : T1)‖ = if x ≥ b - 1 / 2 then |x - b| else |x - b + 1| := by
        split_ifs <;> norm_num [ AddCircle.norm_eq ] at *;
        · convert T1_norm_mk_of_abs_le ( x - b ) _ using 1;
          grind +splitIndPred;
        · erw [ AddCircle.norm_eq ] ; norm_num [ round_eq ] ; ring;
          norm_num [ show ⌊1 / 2 + ( x - b ) ⌋ = -1 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] ; ring;
      split_ifs at h_dist_x_b <;> simp_all +decide [ abs_le ];
      · simp_all +decide [ dist_eq_norm ];
        grind;
      · norm_num [ dist_eq_norm ] at *;
        exact ⟨ fun h => Or.inr ⟨ by linarith, by cases abs_cases ( x - b + 1 ) <;> linarith ⟩, fun h => ⟨ ⟨ by cases h <;> linarith, by cases h <;> linarith ⟩, by cases h <;> cases abs_cases ( x - b + 1 ) <;> linarith ⟩ ⟩;
    have h_preimage : volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) = volume (Set.preimage (fun x : ℝ => QuotientAddGroup.mk x : ℝ → T1) (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) ∩ Set.Ioc (-1 / 2) (1 / 2)) := by
      have h_preimage : MeasureTheory.MeasurePreserving (fun x : ℝ => QuotientAddGroup.mk x : ℝ → T1) (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc (-1 / 2) (1 / 2))) (MeasureTheory.volume : MeasureTheory.Measure T1) := by
        convert AddCircle.measurePreserving_mk ( 1 : ℝ ) ( -1 / 2 ) using 1;
        norm_num;
      rw [ ← h_preimage.measure_preimage ];
      · norm_num;
      · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_closedBall ) ( measurableSet_closedBall ) );
    rw [ h_preimage ];
    rw [ show ( fun x : ℝ => QuotientAddGroup.mk x : ℝ → T1 ) ⁻¹' ( Metric.closedBall 0 r ∩ Metric.closedBall ( QuotientAddGroup.mk b : T1 ) r ) ∩ Set.Ioc ( -1 / 2 ) ( 1 / 2 ) = ( Set.Icc ( b - r ) r ∪ Set.Icc ( -r ) ( b + r - 1 ) ) ∩ Set.Ioc ( -1 / 2 ) ( 1 / 2 ) from ?_ ];
    · nontriviality;
      rw [ MeasureTheory.measure_congr ];
      rw [ MeasureTheory.ae_eq_set ];
      constructor <;> rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] <;> norm_num;
      · exact Filter.Eventually.of_forall fun x hx₁ hx₂ hx₃ hx₄ => by cases hx₁ <;> first | exact ⟨ by linarith, by linarith ⟩ | exact False.elim <| hx₄ ( by linarith ) |> not_lt_of_ge ( by linarith ) ;
      · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( -1 / 2 ) ), MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ( 1 / 2 ) ) ] with x hx₁ hx₂ using fun hx => ⟨ by cases hx <;> cases lt_or_gt_of_ne hx₁ <;> cases lt_or_gt_of_ne hx₂ <;> linarith, by cases hx <;> cases lt_or_gt_of_ne hx₁ <;> cases lt_or_gt_of_ne hx₂ <;> linarith ⟩;
    · grind;
  rw [ h_preimage, MeasureTheory.measure_union₀ ] <;> norm_num;
  · rw [ ← ENNReal.ofReal_add ] <;> ring <;> linarith;
  · refine' MeasureTheory.measure_mono_null _ _;
    exact { ( b + r - 1 ) };
    · exact fun x hx => by norm_num; linarith [ hx.1.1, hx.1.2, hx.2.1, hx.2.2 ] ;
    · norm_num [ MeasureTheory.MeasureSpace.volume ]

/-- Volume of the intersection of two `r`-balls on T1 for `r ≤ 1/2`.
    When the two balls don't wrap around each other (`|b| + 2r ≤ 1`), the intersection
    has volume `2r - |b|`. When wrapping occurs (`|b| + 2r > 1`), the volume is `4r - 1`. -/
lemma volume_closedBall_inter_T1_general (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/2)
    (b : ℝ) (hb : |b| ≤ r) :
    volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk b : T1) r) =
    ENNReal.ofReal (if |b| + 2 * r ≤ 1 then 2 * r - |b| else 4 * r - 1) := by
  split_ifs with h
  · exact volume_closedBall_inter_T1_nowrap r hr0 hr b hb h
  · exact volume_closedBall_inter_T1_wrap r hr0 hr b hb (by linarith)

/-
Real-analysis helper: the piecewise integral arising from the mid-regime ball
    intersection volume.
-/
lemma lintegral_piecewise_mid (r : ℝ) (hr_lo : 1/3 < r) (hr_hi : r ≤ 1/2) :
    ∫⁻ (x : ℝ) in Set.Icc (-r) r,
      ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1) =
    ENNReal.ofReal (gammaMid r) := by
  have h_split : ∫⁻ (x : ℝ) in Set.Icc (-r) r, ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1) = (∫⁻ (x : ℝ) in Set.Icc (-r) (-(1 - 2 * r)), ENNReal.ofReal (4 * r - 1)) + (∫⁻ (x : ℝ) in Set.Ioc (-(1 - 2 * r)) (1 - 2 * r), ENNReal.ofReal (2 * r - |x|)) + (∫⁻ (x : ℝ) in Set.Ioc (1 - 2 * r) r, ENNReal.ofReal (4 * r - 1)) := by
    have h_split : ∫⁻ (x : ℝ) in Set.Icc (-r) r, ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1) = (∫⁻ (x : ℝ) in Set.Icc (-r) (-(1 - 2 * r)), ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1)) + (∫⁻ (x : ℝ) in Set.Ioc (-(1 - 2 * r)) (1 - 2 * r), ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1)) + (∫⁻ (x : ℝ) in Set.Ioc (1 - 2 * r) r, ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1)) := by
      rw [ ← MeasureTheory.lintegral_union, ← MeasureTheory.lintegral_union ] <;> norm_num;
      · rw [ Set.Icc_union_Ioc_eq_Icc, Set.Icc_union_Ioc_eq_Icc ] <;> linarith;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2, hx₂.1 ] ;
      · grind +locals;
    rw [ h_split ];
    refine' congrArg₂ _ ( congrArg₂ _ _ _ ) _ <;> refine' MeasureTheory.setLIntegral_congr_fun _ _ <;> norm_num;
    · intro x hx; norm_num [ abs_of_nonpos ( by linarith [ hx.1, hx.2 ] : x ≤ 0 ) ] ;
      grind;
    · exact fun x hx => congr_arg _ ( if_pos <| by cases abs_cases x <;> linarith [ hx.1, hx.2 ] );
    · intro x hx; norm_num [ abs_of_nonneg ( by linarith [ hx.1 ] : 0 ≤ x ) ] ; split_ifs <;> norm_num ; linarith [ hx.1, hx.2 ] ;
  -- Compute the middle integral: $\int_{-(1-2r)}^{1-2r} (2r - |x|) \, dx$.
  have h_middle : ∫⁻ (x : ℝ) in Set.Ioc (-(1 - 2 * r)) (1 - 2 * r), ENNReal.ofReal (2 * r - |x|) = ENNReal.ofReal (4 * r * (1 - 2 * r) - (1 - 2 * r) ^ 2) := by
    rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
    · rw [ ← intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_sub ] <;> norm_num;
      · -- Evaluate the integral of $|x|$ over $[2r-1, 1-2r]$.
        have h_abs : ∫ x in (2 * r - 1)..1 - 2 * r, |x| = (∫ x in (2 * r - 1)..0, |x|) + (∫ x in (0)..1 - 2 * r, |x|) := by
          rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> exact Continuous.intervalIntegrable ( by continuity ) _ _;
        rw [ h_abs, intervalIntegral.integral_congr fun x hx => abs_of_nonpos <| by linarith [ Set.mem_Icc.mp <| by rwa [ Set.uIcc_of_le ( by linarith ) ] at hx ], intervalIntegral.integral_congr fun x hx => abs_of_nonneg <| by linarith [ Set.mem_Icc.mp <| by rwa [ Set.uIcc_of_le ( by linarith ) ] at hx ] ] ; norm_num ; ring;
        rw [ intervalIntegral.integral_neg ] ; norm_num ; ring;
      · exact Continuous.intervalIntegrable ( continuous_abs ) _ _;
    · exact Continuous.integrableOn_Ioc ( by continuity );
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using sub_nonneg_of_le <| by cases abs_cases x <;> linarith [ hx.1, hx.2 ] ;
  simp_all +decide [ gammaMid ];
  rw [ ← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul ] <;> ring <;> norm_num at * <;> try nlinarith;
  rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
  · rw [ ENNReal.toReal_add, ENNReal.toReal_mul ] <;> norm_num;
    · rw [ ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal ] <;> nlinarith;
    · exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( by norm_num );
  · exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( by norm_num )

lemma volume_triangleSet_mid (r : ℝ) (hr_lo : 1/3 < r) (hr_hi : r ≤ 1/2) :
    volume (triangleSet r) = ENNReal.ofReal (gammaMid r) := by
  rw [ volume_triangleSet_eq_real_integral r ( by linarith ) hr_hi, ← lintegral_piecewise_mid r hr_lo hr_hi ];
  -- Apply the lemma volume_closedBall_inter_T1_general to each x in the interval [-r, r].
  have h_apply_lemma : ∀ x ∈ Set.Icc (-r) r, volume (Metric.closedBall (0 : T1) r ∩ Metric.closedBall (QuotientAddGroup.mk x : T1) r) = ENNReal.ofReal (if |x| + 2 * r ≤ 1 then 2 * r - |x| else 4 * r - 1) := by
    exact fun x hx => volume_closedBall_inter_T1_general r ( by linarith ) hr_hi x ( by cases abs_cases x <;> linarith [ hx.1, hx.2 ] );
  rw [ MeasureTheory.lintegral_congr_ae ];
  filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using h_apply_lemma x hx

/-
**Mid-regime triangle integral.** Sibling of `integral_triangle_eq_pow`; the d-fold
    coordinate factorization is identical, only the per-coordinate value changes.

    Proof structure mirrors `integral_triangle_eq_pow`: reduce to
    `volume_coordFactored_eq_pow (volume_triangleSet_mid r ...)`. Aristotle target.
-/
theorem integral_triangle_eq_pow_mid (d : ℕ) (hd : 1 ≤ d) (r : ℝ)
    (hr_lo : 1/3 < r) (hr_hi : r ≤ 1/2) :
    ∫ pts : Fin 3 → (Fin d → T1),
      (if dist (pts 0) (pts 1) ≤ r then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ r then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ r then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Fin d → T1)))
    = (gammaMid r) ^ d := by
  have h_volume : ∫ (pts : Fin 3 → Fin d → T1), (if dist (pts 0) (pts 1) ≤ r ∧ dist (pts 0) (pts 2) ≤ r ∧ dist (pts 1) (pts 2) ≤ r then 1 else 0) ∂Measure.pi (fun _ => MeasureSpace.volume) = (MeasureTheory.volume {pts : Fin 3 → Fin d → T1 | dist (pts 0) (pts 1) ≤ r ∧ dist (pts 0) (pts 2) ≤ r ∧ dist (pts 1) (pts 2) ≤ r}).toReal := by
    rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
    change (∫ x in { pts : Fin 3 → Fin d → T1 | dist ( pts 0 ) ( pts 1 ) ≤ r ∧ dist ( pts 0 ) ( pts 2 ) ≤ r ∧ dist ( pts 1 ) ( pts 2 ) ≤ r }, 1 ∂Measure.pi fun _ => volume) = _;
    · aesop;
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) );
    · norm_num [ Filter.EventuallyEq, Set.indicator ];
  convert h_volume using 1;
  · grind;
  · rw [ triangleSet_torus_eq d hd r ( by linarith ), volume_coordFactored_eq_pow ] <;> norm_num [ volume_triangleSet_mid r hr_lo hr_hi ];
    · rw [ ENNReal.toReal_ofReal ( by positivity ) ];
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) )