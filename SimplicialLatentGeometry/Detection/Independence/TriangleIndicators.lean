import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.DeepRegime.CechDoublySigned

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.Independence.TriangleIndicators`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


-- The doubly-signed indicator for triangle t, viewed as a function of the torus points.
open Classical in
noncomputable def triangleIndicator' {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts : Fin n → Torus d) : ℝ :=
  let s := cechObservation r (CechSample.mk pts)
  (∏ e ∈ triangleEdges t,
    (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
  (if s.fill t then (1 : ℝ) - q else -q)



/-- Measurability of the triangle indicator. Moved up from below so that downstream
    covariance lemmas (vertex-sharing / disjoint cases) can cite it. -/
lemma triangleIndicator'_measurable {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t pts) := by
  unfold triangleIndicator' cechObservation
  simp only [CechSample.hasEdge, CechSample.hasFill]
  refine Measurable.mul ?_ ?_
  · exact Finset.measurable_prod _ fun e _ => by
      exact Measurable.ite (by simp only [decide_eq_true_eq]; exact measurableSet_le (Measurable.dist (measurable_pi_apply _) (measurable_pi_apply _)) measurable_const) measurable_const measurable_const
  · refine Measurable.ite ?_ measurable_const measurable_const
    simp only [decide_eq_true_eq]
    exact measurableSet_hasFill r t



lemma triangleIndicator'_translate {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts : Fin n → Torus d) (h : Torus d) :
    triangleIndicator' p q r t (fun i => pts i + h) = triangleIndicator' p q r t pts := by
  -- Translation invariance: both `hasEdge` and `hasFill` (Rips clique form) are
  -- defined via pairwise `dist (·) (·) ≤ r`, and `dist` is right-translation
  -- invariant on the abelian group `Torus d = Fin d → AddCircle 1`.
  unfold triangleIndicator' cechObservation
  simp only
  have h_edge_iff : ∀ i j : Fin n,
      (CechSample.mk (n := n) (d := d) (fun i => pts i + h)).hasEdge r i j ↔
        (CechSample.mk (n := n) (d := d) pts).hasEdge r i j := by
    intro i j
    unfold CechSample.hasEdge
    simp only [dist_add_right]
  have h_fill_iff :
      (CechSample.mk (n := n) (d := d) (fun i => pts i + h)).hasFill r t ↔
        (CechSample.mk (n := n) (d := d) pts).hasFill r t := by
    unfold CechSample.hasFill
    simp only
    refine ⟨fun H i hi j hj => ?_, fun H i hi j hj => ?_⟩
    · have := H i hi j hj; rwa [dist_add_right] at this
    · have := H i hi j hj; rwa [dist_add_right]
  congr 1
  · apply Finset.prod_congr rfl
    intro e _
    congr 1
    exact congrArg (· = true) (decide_eq_decide.mpr (h_edge_iff e.1 e.2))
  · congr 1
    exact congrArg (· = true) (decide_eq_decide.mpr h_fill_iff)



lemma triangleIndicator'_congr {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts pts' : Fin n → Torus d)
    (h : ∀ i ∈ t.val, pts i = pts' i) :
    triangleIndicator' p q r t pts = triangleIndicator' p q r t pts' := by
  unfold triangleIndicator'
  unfold cechObservation
  simp +decide [h, triangleEdges]
  congr! 3
  · unfold CechSample.hasFill
    aesop
  · unfold CechSample.hasEdge
    aesop
  · refine' Finset.prod_congr rfl fun x hx => _
    unfold CechSample.hasEdge
    aesop



-- Converting integral over ν to integral over product measure on torus points.
lemma integral_over_nu_eq' {n d : ℕ} (r : ℝ) (f : TwoParamSample n → ℝ) :
    let ν := (cechMeasure n d r).map (cechObservation r)
    ∫ s, f s ∂ν = ∫ pts : Fin n → Torus d,
      f (cechObservation r (CechSample.mk pts))
      ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d))) := by
  -- Rewrite the pushforward integral via `integral_map`, then use `cech_integral_eq`.
  show ∫ s, f s ∂((cechMeasure n d r).map (cechObservation r)) = _
  have hf_meas : Measurable f := fun _ _ => trivial
  rw [MeasureTheory.integral_map (cechObservation_measurable r).aemeasurable
        hf_meas.aestronglyMeasurable]
  exact cech_integral_eq n d r (fun s => f (cechObservation r s))



/-
OLD PROOF BODY:
  convert MeasureTheory.integral_map _ _ using 3;
  · exact?;
  · apply_rules [ Measurable.aemeasurable, measurable_to_countable' ];
    intro x
    have h_preimage : MeasurableSet {s : Fin n → Torus d | cechObservation r ⟨s⟩ = x} := by
      have h_measurable : ∀ i j, MeasurableSet {s : Fin n → Torus d | (cechObservation r ⟨s⟩).edge i j = x.edge i j} := by
        intro i j
        have h_measurable : MeasurableSet {s : Fin n → Torus d | dist (s i) (s j) ≤ r} := by
          exact measurableSet_le ( measurable_pi_apply i |> Measurable.dist <| measurable_pi_apply j ) measurable_const
        generalize_proofs at *; (
        cases x.edge i j <;> simp_all +decide [ cechObservation ];
        · exact Measurable.not h_measurable;
        · exact h_measurable)
      generalize_proofs at *; (
      have h_measurable : ∀ t : {σ : Finset (Fin n) // σ.card = 3}, MeasurableSet {s : Fin n → Torus d | (cechObservation r ⟨s⟩).fill t = x.fill t} := by
        intro t
        have h_measurable : MeasurableSet {s : Fin n → Torus d | ∃ z : Torus d, ∀ i ∈ t.val, dist (s i) z ≤ r} := by
          have h_measurable : IsClosed (⋃ z : Torus d, {s : Fin n → Torus d | ∀ i ∈ t.val, dist (s i) z ≤ r}) := by
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
        cases x.fill t <;> simp_all +decide [ cechObservation ];
        · exact Measurable.not h_measurable;
        · convert h_measurable using 1)
      generalize_proofs at *; (
      have h_measurable : MeasurableSet {s : Fin n → Torus d | ∀ i j, (cechObservation r ⟨s⟩).edge i j = x.edge i j} ∧ MeasurableSet {s : Fin n → Torus d | ∀ t : {σ : Finset (Fin n) // σ.card = 3}, (cechObservation r ⟨s⟩).fill t = x.fill t} := by
        exact ⟨ by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by solve_by_elim, by simpa only [ Set.setOf_forall ] using MeasurableSet.iInter fun t => by solve_by_elim ⟩
      generalize_proofs at *; (
      convert h_measurable.1.inter h_measurable.2 using 1
      generalize_proofs at *; (ext; simp [cechObservation]; exact ⟨ fun h => ⟨ fun i j => by simpa using congr_arg ( fun f => f.edge i j ) h, fun a b => by simpa using congr_arg ( fun f => f.fill ⟨ a, b ⟩ ) h ⟩, fun h => by cases x; aesop ⟩ ;))))
    generalize_proofs at *; (
    convert h_preimage.preimage _ using 1
    generalize_proofs at *; (exact measurable_iff_comap_le.mpr le_rfl));
  · exact?
-/

-- The integral of a single triangle indicator over the product measure equals geometricCov.
lemma single_triangle_integral_eq_g' {n d : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : {σ : Finset (Fin n) // σ.card = 3}) :
    let r := matchRadius p d
    let q := fillingProb p d
    ∫ pts : Fin n → Torus d,
      triangleIndicator' p q r t pts
      ∂MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    = geometricCov p d := by
  classical
  -- Pull back the (already-proved) cechMeasure-side identity via `cech_integral_eq`.
  have key :
      ∫ s, ((∏ e ∈ triangleEdges t,
          (if s.hasEdge (matchRadius p d) e.1 e.2 then (1 : ℝ) - p else -p)) *
        (if s.hasFill (matchRadius p d) t
          then (1 : ℝ) - fillingProb p d else -fillingProb p d))
        ∂cechMeasure n d (matchRadius p d) = geometricCov p d :=
    cechDoublySigned_triangle_integral n d p hp0 hp1 t
  rw [cech_integral_eq n d (matchRadius p d)
    (fun s => (∏ e ∈ triangleEdges t,
        (if s.hasEdge (matchRadius p d) e.1 e.2
          then (1 : ℝ) - p else -p)) *
      (if s.hasFill (matchRadius p d) t
        then (1 : ℝ) - fillingProb p d else -fillingProb p d))] at key
  -- Now `key`: ∫ pts ∂Measure.pi, Prop-if integrand on ⟨pts⟩.hasEdge/⟨pts⟩.hasFill = geometricCov.
  -- Show the `triangleIndicator'` integrand (Bool-if via cechObservation) equals it pointwise.
  refine Eq.trans (MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun pts => ?_))) key
  -- pointwise bridge: Bool-if = Prop-if
  show triangleIndicator' p (fillingProb p d) (matchRadius p d) t pts =
      (∏ e ∈ triangleEdges t,
          (if (⟨pts⟩ : CechSample n d).hasEdge (matchRadius p d) e.1 e.2
            then (1 : ℝ) - p else -p)) *
        (if (⟨pts⟩ : CechSample n d).hasFill (matchRadius p d) t
          then (1 : ℝ) - fillingProb p d else -fillingProb p d)
  unfold triangleIndicator'
  simp only
  -- Edge factor: cechObservation.edge i j = decide (hasEdge ...). Branch on hasEdge to swap.
  have h_edge_eq : ∀ e : Fin n × Fin n,
      (if (cechObservation (matchRadius p d) ⟨pts⟩).edge e.1 e.2 = true
        then (1 : ℝ) - p else -p) =
      (if (⟨pts⟩ : CechSample n d).hasEdge (matchRadius p d) e.1 e.2
        then (1 : ℝ) - p else -p) := by
    intro e
    by_cases he : (⟨pts⟩ : CechSample n d).hasEdge (matchRadius p d) e.1 e.2
    · have hb : (cechObservation (matchRadius p d)
          (⟨pts⟩ : CechSample n d)).edge e.1 e.2 = true := by
        show decide ((⟨pts⟩ : CechSample n d).hasEdge (matchRadius p d) e.1 e.2) = true
        exact decide_eq_true he
      rw [if_pos hb, if_pos he]
    · have hb : (cechObservation (matchRadius p d)
          (⟨pts⟩ : CechSample n d)).edge e.1 e.2 ≠ true := by
        show decide ((⟨pts⟩ : CechSample n d).hasEdge (matchRadius p d) e.1 e.2) ≠ true
        simp [decide_eq_true_iff, he]
      rw [if_neg hb, if_neg he]
  have h_fill_eq :
      (if (cechObservation (matchRadius p d) ⟨pts⟩).fill t = true
        then (1 : ℝ) - fillingProb p d else -fillingProb p d) =
      (if (⟨pts⟩ : CechSample n d).hasFill (matchRadius p d) t
        then (1 : ℝ) - fillingProb p d else -fillingProb p d) := by
    by_cases hf : (⟨pts⟩ : CechSample n d).hasFill (matchRadius p d) t
    · have hb : (cechObservation (matchRadius p d)
          (⟨pts⟩ : CechSample n d)).fill t = true := by
        show decide ((⟨pts⟩ : CechSample n d).hasFill (matchRadius p d) t) = true
        exact decide_eq_true hf
      rw [if_pos hb, if_pos hf]
    · have hb : (cechObservation (matchRadius p d)
          (⟨pts⟩ : CechSample n d)).fill t ≠ true := by
        show decide ((⟨pts⟩ : CechSample n d).hasFill (matchRadius p d) t) ≠ true
        simp [decide_eq_true_iff, hf]
      rw [if_neg hb, if_neg hf]
  -- The triangleIndicator' uses `if Bool then ... else ...` which desugars via `cond`.
  -- After `simp only` above, the Bool-form should already match `if · = true`.
  rw [Finset.prod_congr rfl (fun e _ => h_edge_eq e), h_fill_eq]



/-
Helper: triangleIndicator' factors through coordinate differences
-/
lemma triangleIndicator'_factor_coord_diffs {n d : ℕ} (p q r : ℝ)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (i j k : Fin n)
    (ht_eq : t.val = {i, j, k})
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ F : (Torus d × Torus d) → ℝ, Measurable F ∧
      ∀ pts : Fin n → Torus d,
        triangleIndicator' p q r t pts = F (pts j - pts i, pts k - pts i) := by
  -- Define F by applying triangleIndicator' to a sample whose nontrivial values are at j, k
  -- (with i mapped to 0). Translation invariance (`triangleIndicator'_translate`) + agreement
  -- on t.val (`triangleIndicator'_congr`) close the factorisation.
  refine ⟨fun xy : Torus d × Torus d =>
            triangleIndicator' p q r t
              (fun v => if v = j then xy.1 else if v = k then xy.2 else 0),
          ?_, ?_⟩
  · -- Measurability: inline (forward reference to `triangleIndicator'_measurable` blocked).
    -- Build the assembler `Torus d × Torus d → (Fin n → Torus d)` first, then compose
    -- with the standard measurability of `triangleIndicator'`.
    have hAssemble : Measurable
        (fun xy : Torus d × Torus d => fun v : Fin n =>
          (if v = j then xy.1 else if v = k then xy.2 else (0 : Torus d))) := by
      refine measurable_pi_lambda _ ?_
      intro v
      split_ifs
      · exact measurable_fst
      · exact measurable_snd
      · exact measurable_const
    -- Inline `triangleIndicator'` measurability (same proof as `triangleIndicator'_measurable`).
    have hTI : Measurable (fun pts : Fin n → Torus d => triangleIndicator' p q r t pts) := by
      unfold triangleIndicator' cechObservation
      simp only [CechSample.hasEdge, CechSample.hasFill]
      refine Measurable.mul ?_ ?_
      · exact Finset.measurable_prod _ fun e _ => by
          exact Measurable.ite (by
            simp only [decide_eq_true_eq]
            exact measurableSet_le (Measurable.dist (measurable_pi_apply _)
              (measurable_pi_apply _)) measurable_const)
            measurable_const measurable_const
      · refine Measurable.ite ?_ measurable_const measurable_const
        simp only [decide_eq_true_eq]
        exact measurableSet_hasFill r t
    exact hTI.comp hAssemble
  · intro pts
    -- Build the "centered at 0" auxiliary sample.
    set auxPts : Fin n → Torus d := fun v =>
      if v = j then pts j - pts i else if v = k then pts k - pts i else 0 with hauxPts_def
    -- Step 1: translation invariance under `pts i`.
    have h_translate :
        triangleIndicator' p q r t (fun v => auxPts v + pts i) =
        triangleIndicator' p q r t auxPts :=
      triangleIndicator'_translate p q r t auxPts (pts i)
    -- Step 2: `auxPts + pts i` agrees with `pts` on t.val = {i, j, k}.
    have h_agree : ∀ v ∈ t.val, pts v = auxPts v + pts i := by
      intro v hv
      rw [ht_eq] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · -- v = i
        simp [hauxPts_def, hij, hik]
      · -- v = j
        simp [hauxPts_def]
      · -- v = k
        simp [hauxPts_def, Ne.symm hjk]
    have h_congr : triangleIndicator' p q r t pts =
        triangleIndicator' p q r t (fun v => auxPts v + pts i) :=
      triangleIndicator'_congr p q r t pts (fun v => auxPts v + pts i) h_agree
    -- Step 3: combine.
    rw [h_congr, h_translate]



lemma triangleIndicator'_bound' {n d : ℕ} (p q r : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (t : {σ : Finset (Fin n) // σ.card = 3})
    (pts : Fin n → Torus d) :
    |triangleIndicator' p q r t pts| ≤ 1 := by
  unfold triangleIndicator';
  rw [ abs_mul, Finset.abs_prod ];
  refine' mul_le_one₀ _ _ _;
  · exact Finset.prod_le_one ( fun _ _ => abs_nonneg _ ) fun _ _ => abs_le.mpr ⟨ by split_ifs <;> linarith, by split_ifs <;> linarith ⟩;
  · positivity;
  · split_ifs <;> exact abs_le.mpr ⟨ by linarith, by linarith ⟩
