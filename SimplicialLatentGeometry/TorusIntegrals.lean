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

/-- **Sim-A5 / Job 1b, Lemma 1.** Volume of the intersection of two closed balls
    on T1 = AddCircle 1: for r ≤ 1/4 and s = dist a b ≤ r,
    `volume(closedBall a r ∩ closedBall b r) = 2r - s`.

    PROVIDED SOLUTION
    Step 1. Use `AddCircle.volume_closedBall` (or the explicit measure on
      AddCircle 1) which gives `volume (closedBall a r) = ENNReal.ofReal (2r)`
      for `r ≤ 1/2`.
    Step 2. By translation invariance of Haar on AddCircle 1, WLOG `a = 0`.
      Then `closedBall 0 r ∩ closedBall b r` is the set of `x` with
      `‖x‖ ≤ r` and `‖x - b‖ ≤ r`. On the lift to ℝ this is the union of two
      disjoint arcs (or one arc, depending on orientation); since `s + r ≤ 2r ≤ 1/2`,
      the picture stays in a fundamental domain `(-1/2, 1/2]` with no wrap-around.
    Step 3. The 1D Lebesgue length of `{x ∈ ℝ : |x| ≤ r ∧ |x - s| ≤ r}` for
      `0 ≤ s ≤ r` is `2r - s` (intersect intervals `[-r,r]` and `[s-r, s+r]`).
    Step 4. Transfer back via the AddCircle ↔ ℝ quotient measure isomorphism
      (`AddCircle.measure_preserving_mk` or the integral form).
-/
lemma volume_closedBall_inter_T1 (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4)
    (a b : T1) (hs : dist a b ≤ r) :
    volume (Metric.closedBall a r ∩ Metric.closedBall b r)
    = ENNReal.ofReal (2 * r - dist a b) := by
  sorry

/-- **Sim-A5 / Job 1b, Lemma 2.** 1D triangle probability:
    `volume(triangleSet r) = 3r²` on (T1)³ for `r ≤ 1/4`.

    PROVIDED SOLUTION
    Step 1. Fubini over `u 0`: by translation invariance of Haar, fix `u 0 = 0`.
    Step 2. Conditional on `u 0`, the set `{(u₁, u₂) : dist(u₀,u₁) ≤ r ∧
      dist(u₀,u₂) ≤ r ∧ dist(u₁,u₂) ≤ r}` factors. Each of `u 1, u 2` lies in
      `closedBall (u 0) r` (length 2r); call their displacements x₁, x₂ ∈ [-r, r].
      The constraint `dist(u 1, u 2) ≤ r` becomes `|x₁ - x₂| ≤ r` (no wrap since
      `2r ≤ 1/2`).
    Step 3. The remaining 2D Lebesgue integral is
      `∫_{-r}^r ∫_{x₁ - r ≤ x₂ ≤ x₁ + r, x₂ ∈ [-r,r]} dx₂ dx₁
       = ∫_{-r}^r (2r - |x₁|) dx₁ = 3r²`
      (use `integral_2r_minus_abs` already proven above).
    Step 4. Since the outer Fubini integration over `u 0` contributes `volume(T1) = 1`,
      the total is `3r²`.
-/
lemma volume_triangleSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (triangleSet r) = ENNReal.ofReal (3 * r ^ 2) := by
  sorry

/-- **Sim-A5 / Job 1b, Lemma 3.** 1D edge-fill probability:
    `volume(edgeFillSet r) = 7r²` on (T1)³ for `r ≤ 1/4`.

    PROVIDED SOLUTION
    Step 1. By translation invariance, fix `u 0 = 0`.
    Step 2. Conditional on `u 0 = 0`, write x₁, x₂ ∈ T1 for u 1, u 2.
      Constraint A: `|x₁| ≤ r` (i.e., u 1 ∈ ball(u 0, r)).
      Constraint B: ∃ z, `|z| ≤ r ∧ |z - x₁| ≤ r ∧ |z - x₂| ≤ r`.
      Constraint B reduces to `|x₂ - z| ≤ r` for some z in the intersection
      `closedBall 0 r ∩ closedBall x₁ r`, i.e., z ∈ [max(-r, x₁-r), min(r, x₁+r)]
      (length `2r - |x₁|` by `volume_closedBall_inter_T1`).
    Step 3. Hence `x₂` ranges over the Minkowski sum of that interval with `[-r, r]`.
      Length: `(2r - |x₁|) + 2r = 4r - |x₁|`.
    Step 4. Integrate: `∫_{-r}^r (4r - |x₁|) dx₁ = 7r²`
      (use `integral_4r_minus_abs` already proven above).
-/
lemma volume_edgeFillSet (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    volume (edgeFillSet r) = ENNReal.ofReal (7 * r ^ 2) := by
  sorry

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