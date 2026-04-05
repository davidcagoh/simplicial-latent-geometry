import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! Helper lemma: functions depending on disjoint sets of coordinates are independent
    under a product measure. -/

noncomputable instance addCircle_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ))) := by
  constructor; simp

abbrev Torus' (d : ℕ) := Fin d → AddCircle (1 : ℝ)

noncomputable instance torus_isProbabilityMeasure (d : ℕ) :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure (Torus' d)) := by
  infer_instance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [MeasurableSpace α] (μα : MeasureTheory.Measure α)
  [MeasureTheory.IsProbabilityMeasure μα]

/-- If f depends only on coordinates in S and g depends only on coordinates in T,
    and S ∩ T = ∅, then f and g are independent under the product measure. -/
lemma indepFun_of_disjoint_dep
    {S T : Finset ι} (hST : Disjoint S T)
    {f g : (ι → α) → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf_dep : ∀ x y : ι → α, (∀ i ∈ S, x i = y i) → f x = f y)
    (hg_dep : ∀ x y : ι → α, (∀ i ∈ T, x i = y i) → g x = g y) :
    ProbabilityTheory.IndepFun f g (MeasureTheory.Measure.pi (fun _ : ι => μα)) := by
  have h_measurable_S : ∃ f_S : (S → α) → ℝ, Measurable f_S ∧ f = f_S ∘ (fun x : ι → α => fun i : S => x i) := by
    refine' ⟨ fun x => f ( fun i => if hi : i ∈ S then x ⟨ i, hi ⟩ else Classical.choice ( show Nonempty α from _ ) ), _, _ ⟩
    generalize_proofs at *;
    exact ⟨ Classical.choose ( MeasureTheory.nonempty_of_measure_ne_zero ( show μα Set.univ ≠ 0 by simp +decide ) ) ⟩;
    · exact hf.comp ( measurable_pi_lambda _ fun i => by split_ifs <;> [ exact measurable_pi_apply _ ; exact measurable_const ] );
    · ext x; specialize hf_dep x ( fun i => if hi : i ∈ S then x i else Classical.choice ( show Nonempty α from ⟨ Classical.choose ( MeasureTheory.nonempty_of_measure_ne_zero ( show μα Set.univ ≠ 0 by simp +decide ) ) ⟩ ) ) ; aesop;
  have h_measurable_T : ∃ g_T : (T → α) → ℝ, Measurable g_T ∧ g = g_T ∘ (fun x : ι → α => fun i : T => x i) := by
    refine' ⟨ fun x => g ( fun i => if hi : i ∈ T then x ⟨ i, hi ⟩ else Classical.choice ( show Nonempty α from _ ) ), _, _ ⟩
    generalize_proofs at *;
    exact?;
    · refine' hg.comp _;
      exact measurable_pi_lambda _ fun i => by split_ifs <;> [ exact measurable_pi_apply _ ; exact measurable_const ] ;
    · ext x; exact hg_dep _ _ fun i hi => by aesop;
  generalize_proofs at *;
  obtain ⟨ f_S, hf_S, hf ⟩ := h_measurable_S
  obtain ⟨ g_T, hg_T, hg ⟩ := h_measurable_T
  have h_indep : ProbabilityTheory.IndepFun (fun x : (ι → α) => fun i : S => x i) (fun x : (ι → α) => fun i : T => x i) (MeasureTheory.Measure.pi fun _ => μα) := by
    have := @ProbabilityTheory.iIndepFun_pi;
    specialize @this ι _ ( fun _ => α ) _ ( fun _ => μα ) _ ( fun _ => α ) _ ( fun i x => x ) ; simp_all +decide [ ProbabilityTheory.iIndepFun ];
    specialize this ( fun i => aemeasurable_id );
    convert this.indepFun_finset S T hST using 1;
    exact ⟨ fun h _ => h, fun h => h fun _ => measurable_pi_apply _ ⟩;
  rw [ hf, hg ] ; exact h_indep.comp hf_S hg_T;

/-! ## Measurability of the fill condition -/

/-
The set of point configurations where three points have a common r-ball is measurable.
    This is the fill condition for a triangle in the Čech complex.
-/
lemma measurableSet_hasFill {n d : ℕ} (r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    MeasurableSet {pts : Fin n → Torus' d | ∃ z : Torus' d, ∀ i ∈ t.val, dist (pts i) z ≤ r} := by
  -- The set {pts | ∃ z, ∀ i ∈ t.val, dist (pts i) z ≤ r} is the image of a closed set under a continuous projection.
  have h_closed : IsClosed {pts : (Fin n → Torus' d) × Torus' d | ∀ i ∈ t.val, dist (pts.1 i) pts.2 ≤ r} := by
    simp +decide only [Set.setOf_forall];
    refine' isClosed_biInter fun i hi => isClosed_le _ _;
    · fun_prop;
    · fun_prop;
  -- The projection of a closed set in a compact space is closed.
  have h_proj_closed : IsClosed (Set.image (fun pts : (Fin n → Torus' d) × Torus' d => pts.1) {pts : (Fin n → Torus' d) × Torus' d | ∀ i ∈ t.val, dist (pts.1 i) pts.2 ≤ r}) := by
    apply_rules [ IsCompact.isClosed, IsCompact.image ];
    · exact IsClosed.isCompact h_closed;
    · exact continuous_fst;
  convert h_proj_closed.measurableSet using 1 ; aesop
