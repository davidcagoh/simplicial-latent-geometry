import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.Independence.TriangleIndicators

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.Independence.VertexIndep`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set

set_option maxHeartbeats 400000 in
lemma shear_measurePreserving_vertex {n d : ℕ} (i : Fin n) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    MeasureTheory.MeasurePreserving
      (fun pts : Fin n → Torus d => fun v => if v = i then pts v else pts v - pts i) μ μ := by
  refine' ⟨ _, _ ⟩;
  · exact measurable_pi_lambda _ fun _ => by split_ifs <;> [ exact measurable_pi_apply _; exact ( measurable_pi_apply _ |> Measurable.sub <| measurable_pi_apply _ ) ] ;
  · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
    intro s hs; rw [ MeasureTheory.Measure.map_apply ] ; (
    have h_preimage : (fun pts : Fin n → Torus d => fun v => if v = i then pts v else pts v - pts i) ⁻¹' Set.univ.pi s = {pts : Fin n → Torus d | pts i ∈ s i ∧ ∀ v ≠ i, pts v - pts i ∈ s v} := by
      grind;
    have h_split : (MeasureTheory.Measure.pi fun x => MeasureTheory.volume) {pts : Fin n → Torus d | pts i ∈ s i ∧ ∀ v ≠ i, pts v - pts i ∈ s v} = (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) {p : Torus d × ({j // j ≠ i} → Torus d) | p.1 ∈ s i ∧ ∀ j : {j // j ≠ i}, p.2 j - p.1 ∈ s j} := by
      have h_split : (MeasureTheory.Measure.pi fun x => MeasureTheory.volume) = MeasureTheory.Measure.map (fun p : Torus d × ({j // j ≠ i} → Torus d) => fun v => if h : v = i then p.1 else p.2 ⟨v, h⟩) (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) := by
        convert MeasureTheory.Measure.pi_eq _;
        · exact?;
        · intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · rw [ show ( fun p : Torus d × ( { j // j ≠ i } → Torus d ) => fun v => if h : v = i then p.1 else p.2 ⟨ v, h ⟩ ) ⁻¹' Set.univ.pi s = ( s i ) ×ˢ ( Set.pi Set.univ fun j : { j // j ≠ i } => s j ) from ?_ ];
            · simp +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ), MeasureTheory.Measure.pi_pi ];
              refine' congr rfl ( Finset.prod_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide [ Finset.mem_sdiff, Finset.mem_singleton ];
            · grind;
          · exact measurable_pi_lambda _ fun v => by split_ifs <;> [ exact measurable_fst; exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd ] ;
          · exact MeasurableSet.univ_pi hs;
      rw [ h_split, MeasureTheory.Measure.map_apply ];
      · congr with p ; aesop;
      · exact measurable_pi_lambda _ fun v => by split_ifs <;> [ exact measurable_fst; exact measurable_pi_apply _ |> Measurable.comp <| measurable_snd ] ;
      · simp +decide only [Set.setOf_and, Set.setOf_forall];
        refine' MeasurableSet.inter _ _;
        · exact measurable_pi_apply i ( hs i );
        · refine' MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => _;
          exact measurableSet_preimage ( measurable_pi_apply j |> Measurable.sub <| measurable_pi_apply i ) ( hs j );
    have h_fubini : (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) {p : Torus d × ({j // j ≠ i} → Torus d) | p.1 ∈ s i ∧ ∀ j : {j // j ≠ i}, p.2 j - p.1 ∈ s j} = ∫⁻ x in s i, ∏ j : {j // j ≠ i}, MeasureTheory.volume (s j) ∂MeasureTheory.volume := by
      have h_fubini : (MeasureTheory.Measure.prod (MeasureTheory.volume) (MeasureTheory.Measure.pi fun x => MeasureTheory.volume)) {p : Torus d × ({j // j ≠ i} → Torus d) | p.1 ∈ s i ∧ ∀ j : {j // j ≠ i}, p.2 j - p.1 ∈ s j} = ∫⁻ x in s i, (MeasureTheory.Measure.pi fun x => MeasureTheory.volume) {p : {j // j ≠ i} → Torus d | ∀ j : {j // j ≠ i}, p j - x ∈ s j} ∂MeasureTheory.volume := by
        rw [ MeasureTheory.Measure.prod_apply ];
        · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
          · congr with x ; aesop;
          · exact hs i;
        · simp +decide only [Set.setOf_and, Set.setOf_forall];
          refine' MeasurableSet.inter _ _;
          · exact measurableSet_preimage ( measurable_fst ) ( hs i );
          · refine' MeasurableSet.iInter fun j => _;
            exact measurableSet_preimage ( show Measurable fun x : Torus d × ( { j // j ≠ i } → Torus d ) => x.2 j - x.1 from Measurable.sub ( measurable_pi_apply _ |> Measurable.comp <| measurable_snd ) measurable_fst ) ( hs _ );
      rw [ h_fubini ];
      refine' MeasureTheory.lintegral_congr fun x => _;
      rw [ show { p : { j // j ≠ i } → Torus d | ∀ j : { j // j ≠ i }, p j - x ∈ s j } = ( Set.pi Set.univ fun j : { j // j ≠ i } => ( fun y => y - x ) ⁻¹' s j ) by ext; simp +decide [ Set.pi ] ];
      simp +decide [ sub_eq_add_neg ];
    simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ) ];
    rw [ mul_comm, ← Finset.prod_attach ];
    refine' congr rfl ( Finset.prod_bij ( fun x hx => x ) _ _ _ _ ) <;> aesop);
    · exact measurable_pi_lambda _ fun j => by split_ifs <;> [ exact measurable_pi_apply j; exact measurable_pi_apply j |> Measurable.sub <| measurable_pi_apply i ] ;
    · exact MeasurableSet.univ_pi hs


lemma indepFun_proj_pairs_vertex {n d : ℕ} (j k l m : Fin n)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts : Fin n → Torus d => (pts j, pts k))
      (fun pts : Fin n → Torus d => (pts l, pts m)) μ := by
  intro μ;
  have h_indep : ProbabilityTheory.iIndepFun (fun i : Fin n => fun pts : Fin n → Torus d => pts i) μ := by
    convert ProbabilityTheory.iIndepFun_pi _
    rotate_left
    exact?
    exacts [ fun i x => x, fun i => measurable_id.aemeasurable, rfl ]
  have := h_indep.indepFun_finset { j, k } { l, m } ; simp_all +decide [ ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul ] ;
  intro s t hs ht; specialize this ( Ne.symm hjl ) ( Ne.symm hkl ) ( Ne.symm hjm ) ( Ne.symm hkm ) ( fun i => measurable_pi_apply i ) ; simp_all +decide [ Set.preimage ] ;
  convert this ( ( fun f => ( f ⟨ j, by aesop ⟩, f ⟨ k, by aesop ⟩ ) ) ⁻¹' s ) ( ( fun f => ( f ⟨ l, by aesop ⟩, f ⟨ m, by aesop ⟩ ) ) ⁻¹' t ) _ _ using 1 <;> simp +decide [ Set.preimage ];
  · exact measurableSet_preimage ( measurable_pi_apply _ |> Measurable.prodMk <| measurable_pi_apply _ ) hs |> MeasurableSet.mem;
  · exact measurableSet_preimage ( measurable_pi_apply _ |> Measurable.prodMk <| measurable_pi_apply _ ) ht |> MeasurableSet.mem


lemma indepFun_comp_measurePreserving_vertex {Omega Alpha Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {μ : MeasureTheory.Measure Omega}
    {f : Omega → Alpha} {g : Omega → Beta} {Ψ : Omega → Omega}
    (hΨ : MeasureTheory.MeasurePreserving Ψ μ μ)
    (hf : Measurable f) (hg : Measurable g)
    (hind : ProbabilityTheory.IndepFun f g μ) :
    ProbabilityTheory.IndepFun (f ∘ Ψ) (g ∘ Ψ) μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at *
  intro s t hs ht
  have eq1 : (f ∘ Ψ) ⁻¹' s ∩ (g ∘ Ψ) ⁻¹' t = Ψ ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) := by
    ext x; simp [Set.mem_preimage, Set.mem_inter_iff]
  have eq2 : (f ∘ Ψ) ⁻¹' s = Ψ ⁻¹' (f ⁻¹' s) := by ext; simp
  have eq3 : (g ∘ Ψ) ⁻¹' t = Ψ ⁻¹' (g ⁻¹' t) := by ext; simp
  rw [eq1, eq2, eq3]
  rw [hΨ.measure_preimage ((hs.preimage hf).inter (ht.preimage hg)).nullMeasurableSet,
      hΨ.measure_preimage (hs.preimage hf).nullMeasurableSet,
      hΨ.measure_preimage (ht.preimage hg).nullMeasurableSet]
  exact hind s t hs ht


lemma indepFun_coord_diffs_vertex {n d : ℕ}
    (i j k l m : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m)
    (_hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (_hlm : l ≠ m) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts : Fin n → Torus d => (pts j - pts i, pts k - pts i))
      (fun pts : Fin n → Torus d => (pts l - pts i, pts m - pts i))
      μ := by
  intro μ
  let Ψ : (Fin n → Torus d) → (Fin n → Torus d) := fun pts v => if v = i then pts v else pts v - pts i
  have h_eq : (fun pts : Fin n → Torus d => (pts j - pts i, pts k - pts i)) =
      (fun pts : Fin n → Torus d => (pts j, pts k)) ∘ Ψ := by
    ext pts <;> simp [Ψ, hij.symm, hik.symm]
  have h'_eq : (fun pts : Fin n → Torus d => (pts l - pts i, pts m - pts i)) =
      (fun pts : Fin n → Torus d => (pts l, pts m)) ∘ Ψ := by
    ext pts <;> simp [Ψ, hil.symm, him.symm]
  rw [h_eq, h'_eq]
  exact indepFun_comp_measurePreserving_vertex
    (shear_measurePreserving_vertex i)
    (Measurable.prod (measurable_pi_apply j) (measurable_pi_apply k))
    (Measurable.prod (measurable_pi_apply l) (measurable_pi_apply m))
    (indepFun_proj_pairs_vertex j k l m hjl hjm hkl hkm)



/-
Helper: extract shared vertex and other vertices from two triangles sharing exactly one vertex
-/
lemma extract_vertices_of_card_inter_one {n : ℕ}
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 1) :
    ∃ i j k l m : Fin n,
      t.val = {i, j, k} ∧ t'.val = {i, l, m} ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      i ≠ l ∧ i ≠ m ∧ l ≠ m ∧
      j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m := by
  obtain ⟨ i, hi ⟩ := Finset.card_eq_one.mp hshare;
  -- Since t and t' are distinct and their intersection is {i}, we can extract the other elements from t and t'.
  obtain ⟨j, k, hjk⟩ : ∃ j k : Fin n, j ≠ k ∧ j ≠ i ∧ k ≠ i ∧ t.val = {i, j, k} := by
    have := Finset.card_eq_three.mp t.2;
    rcases this with ⟨ x, y, z, hxy, hxz, hyz, ht ⟩ ; simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ] ;
    grind
  obtain ⟨l, m, hlm⟩ : ∃ l m : Fin n, l ≠ m ∧ l ≠ i ∧ m ≠ i ∧ t'.val = {i, l, m} := by
    have h_card : (t'.val \ {i}).card = 2 := by
      grind;
    obtain ⟨ l, m, h ⟩ := Finset.card_eq_two.mp h_card;
    grind;
  grind +locals



/-
OLD PROOF BODY:
  refine' ⟨ fun xy => triangleIndicator' p q r t ( fun v => if v = i then 0 else if v = j then xy.1 else if v = k then xy.2 else 0 ), _, _ ⟩ <;> norm_num [ triangleIndicator' ];
  · refine' Measurable.ite _ _ _ <;> norm_num [ cechObservation ];
    · refine' MeasurableSet.mem _;
      refine' IsClosed.measurableSet _;
      simp +decide [ ht_eq, dist_comm ];
      simp +decide [ hij.symm, hik.symm, hjk.symm ];
      refine' isClosed_of_closure_subset _;
      intro a ha;
      rw [ mem_closure_iff_seq_limit ] at ha;
      obtain ⟨ x, hx₁, hx₂ ⟩ := ha;
      choose z hz using hx₁;
      -- Since $z_n$ is bounded, it has a convergent subsequence.
      obtain ⟨z', hz'⟩ : ∃ z' : Torus d, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun n => z (subseq n)) Filter.atTop (nhds z') := by
        have h_compact : IsCompact (Set.univ : Set (Torus d)) := by
          exact isCompact_univ_iff.mpr ( by infer_instance );
        have := h_compact.isSeqCompact fun n => Set.mem_univ ( z n ) ; aesop;
      obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hz';
      refine' ⟨ z', _, _, _ ⟩;
      · exact le_of_tendsto' ( hsubseq₂.norm ) fun n => hz _ |>.1;
      · exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist hsubseq₂ ( continuousAt_fst.tendsto.comp hx₂ |> Filter.Tendsto.comp <| hsubseq₁.tendsto_atTop ) ) tendsto_const_nhds fun n => hz _ |>.2.1;
      · exact le_of_tendsto_of_tendsto' ( Filter.Tendsto.dist hsubseq₂ ( continuous_snd.continuousAt.tendsto.comp ( hx₂.comp hsubseq₁.tendsto_atTop ) ) ) tendsto_const_nhds fun n => hz _ |>.2.2;
    · refine' Measurable.mul _ measurable_const;
      refine' Finset.measurable_prod _ _ ; intros ; simp +decide [ cechObservation ];
      unfold CechSample.hasEdge; simp +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
      refine' Measurable.ite _ _ _ <;> norm_num [ dist_eq_norm ];
      exact MeasurableSet.mem ( measurableSet_le ( measurable_norm.comp ( Measurable.sub ( by split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ] ) ( by split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ] ) ) ) measurable_const );
    · refine' Measurable.mul _ measurable_const;
      refine' Finset.measurable_prod _ fun e he => _;
      refine' Measurable.ite _ _ _ <;> norm_num [ cechObservation ];
      refine' Measurable.comp ( show Measurable fun x : ℝ => x ≤ r from measurableSet_Iic.mem ) _;
      refine' Measurable.dist _ _ <;> norm_num [ cechObservation ];
      · split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ];
      · split_ifs <;> [ exact measurable_const; exact measurable_fst; exact measurable_snd; exact measurable_const ];
  · intro pts; congr! 2; simp +decide [ cechObservation, triangleEdges ] ;
    · constructor <;> rintro ⟨ z, hz ⟩;
      · use z - pts i; simp_all +decide [ CechSample.hasFill ] ;
        aesop;
      · use z + pts i; simp_all +decide [ CechSample.hasFill ] ;
        split_ifs at hz <;> simp_all +decide [ dist_eq_norm, sub_eq_iff_eq_add ];
        exact ⟨ by convert hz.2.1 using 1; abel_nf, by convert hz.2.2 using 1; abel_nf ⟩;
    · refine' Finset.prod_congr rfl fun e he => _ ; simp +decide [ cechObservation ] ;
      unfold CechSample.hasEdge; simp +decide [ Finset.mem_product, Finset.mem_univ, * ] ;
      unfold triangleEdges at he; simp +decide [ Finset.mem_product, Finset.mem_univ, * ] at he;
      rcases he with ⟨ ⟨ he₁ | he₁ | he₁, he₂ | he₂ | he₂ ⟩, he₃ ⟩ <;> simp +decide [ he₁, he₂ ] at he₃ ⊢;
      all_goals simp +decide [ dist_eq_norm, norm_sub_rev, hij.symm, hik.symm, hjk.symm ] ;
    · refine' congr_arg₂ _ ( Finset.prod_congr rfl fun x hx => _ ) rfl ; simp +decide [ cechObservation ] ;
      simp +decide [ triangleEdges ] at hx ⊢;
      simp +decide [ ht_eq, CechSample.hasEdge ] at hx ⊢;
      rcases hx.1.1 with ( h | h | h ) <;> rcases hx.1.2 with ( j | j | j ) <;> simp +decide [ h, j ] at hx ⊢;
      all_goals simp +decide [ dist_eq_norm, norm_sub_rev, hij.symm, hik.symm, hjk.symm ] ;
-/

/-
When two triangles t, t' share exactly one vertex i, their triangle indicators
under the torus Haar measure μ are independent.
-/
set_option maxHeartbeats 800000 in
lemma vertex_sharing_indepFun' {n d : ℕ} (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (t t' : {σ : Finset (Fin n) // σ.card = 3})
    (htt' : t ≠ t')
    (hshare : (t.val ∩ t'.val).card = 1) :
    let r := matchRadius p d
    let q := fillingProb p d
    let μ := MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure (Torus d)))
    ProbabilityTheory.IndepFun
      (fun pts => triangleIndicator' p q r t pts)
      (fun pts => triangleIndicator' p q r t' pts) μ := by
  intro r q μ
  obtain ⟨i, j, k, l, m, ht_eq, ht'_eq, hij, hik, hjk, hil, him, hlm, hjl, hjm, hkl, hkm⟩ :=
    extract_vertices_of_card_inter_one t t' htt' hshare
  obtain ⟨F, hF_meas, hF_eq⟩ := triangleIndicator'_factor_coord_diffs p q r t i j k ht_eq hij hik hjk
  obtain ⟨G, hG_meas, hG_eq⟩ := triangleIndicator'_factor_coord_diffs p q r t' i l m ht'_eq hil him hlm
  have h_eq_F : (fun pts => triangleIndicator' p q r t pts) =
      F ∘ (fun pts : Fin n → Torus d => (pts j - pts i, pts k - pts i)) := by
    ext pts; exact hF_eq pts
  have h_eq_G : (fun pts => triangleIndicator' p q r t' pts) =
      G ∘ (fun pts : Fin n → Torus d => (pts l - pts i, pts m - pts i)) := by
    ext pts; exact hG_eq pts
  rw [h_eq_F, h_eq_G]
  exact (indepFun_coord_diffs_vertex i j k l m hij hik hil him hjk hjl hjm hkl hkm hlm).comp hF_meas hG_meas
