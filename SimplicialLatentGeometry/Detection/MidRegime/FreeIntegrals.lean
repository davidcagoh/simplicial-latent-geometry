import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.MidRegime.FreeIntegrals`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


/-- 1D edge set: the set of 3-tuples on T1 where points 0 and 1 are within distance r. -/
def edgeSet01 (r : ℝ) : Set (Fin 3 → T1) :=
  {f | dist (f 0) (f 1) ≤ r}



/-- 1D wedge set: the set of 3-tuples on T1 where both (0,1) and (0,2) edges are present. -/
def wedgeSet01 (r : ℝ) : Set (Fin 3 → T1) :=
  {f | dist (f 0) (f 1) ≤ r ∧ dist (f 0) (f 2) ≤ r}



open MeasureTheory in
lemma volume_edgeSet01 (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1 / 2) :
    volume (edgeSet01 r) = ENNReal.ofReal (2 * r) := by
  -- By Fubini's theorem, we can integrate over the first coordinate first.
  have h_fubini : volume (edgeSet01 r) = ∫⁻ (x : Fin 3 → T1), (if dist (x 0) (x 1) ≤ r then 1 else 0) ∂(MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (T1)))) := by
    rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    change volume (edgeSet01 r) = ∫⁻ x in edgeSet01 r, 1 ∂Measure.pi (fun _ => volume);
    · norm_num +zetaDelta at *;
      rfl;
    · exact measurableSet_le ( continuous_dist.measurable.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
    · exact Filter.Eventually.of_forall fun x => by simp +decide [ Set.indicator, edgeSet01 ] ;
  have h_fubini : ∫⁻ (x : Fin 3 → T1), (if dist (x 0) (x 1) ≤ r then 1 else 0) ∂(MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (T1)))) = ∫⁻ (x : T1), ∫⁻ (y : T1), ∫⁻ (z : T1), (if dist x y ≤ r then 1 else 0) ∂(volume : Measure (T1)) ∂(volume : Measure (T1)) ∂(volume : Measure (T1)) := by
    have h_fubini : ∀ {f : (Fin 3 → T1) → ENNReal}, Measurable f → ∫⁻ (x : Fin 3 → T1), f x ∂(MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (T1)))) = ∫⁻ (x : T1), ∫⁻ (y : T1), ∫⁻ (z : T1), f (fun i => if i = 0 then x else if i = 1 then y else z) ∂(volume : Measure (T1)) ∂(volume : Measure (T1)) ∂(volume : Measure (T1)) := by
      intro f hf
      have h_fubini : ∫⁻ (x : Fin 3 → T1), f x ∂(MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (T1)))) = ∫⁻ (x : T1 × T1 × T1), f (fun i => if i = 0 then x.1 else if i = 1 then x.2.1 else x.2.2) ∂(MeasureTheory.Measure.prod (volume : Measure (T1)) (MeasureTheory.Measure.prod (volume : Measure (T1)) (volume : Measure (T1)))) := by
        have h_fubini : MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (T1))) = MeasureTheory.Measure.map (fun x : T1 × T1 × T1 => fun i => if i = 0 then x.1 else if i = 1 then x.2.1 else x.2.2) (MeasureTheory.Measure.prod (volume : Measure (T1)) (MeasureTheory.Measure.prod (volume : Measure (T1)) (volume : Measure (T1)))) := by
          rw [ MeasureTheory.Measure.pi_eq ];
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three, hs ] ;
          · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
            erw [ show { x : T1 × T1 × T1 | x.1 ∈ s 0 ∧ x.2.1 ∈ s 1 ∧ x.2.2 ∈ s 2 } = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ; erw [ MeasureTheory.Measure.prod_prod ] ; ring;
          · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
          · exact MeasurableSet.univ_pi hs;
        rw [ h_fubini, MeasureTheory.lintegral_map ];
        · exact hf;
        · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
      erw [ h_fubini, MeasureTheory.lintegral_prod ];
      · congr! 2;
        erw [ MeasureTheory.lintegral_prod ];
        exact hf.comp ( measurable_pi_lambda _ fun i => by fin_cases i <;> measurability ) |> Measurable.aemeasurable;
      · exact hf.aemeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ) );
    convert h_fubini _ using 1;
    exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
  have h_fubini : ∀ x : T1, ∫⁻ (y : T1), (if dist x y ≤ r then 1 else 0) ∂(volume : Measure (T1)) = ENNReal.ofReal (min 1 (2 * r)) := by
    intro x
    have h_ball : ∫⁻ (y : T1), (if dist x y ≤ r then 1 else 0) ∂(volume : Measure (T1)) = ∫⁻ (y : T1) in Metric.closedBall x r, 1 ∂(volume : Measure (T1)) := by
      rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
      · simp +decide only [dist_comm];
      · exact measurableSet_closedBall;
    have := @AddCircle.volume_closedBall ( 1 : ℝ );
    exact h_ball.trans ( by simpa using this r );
  simp_all +decide [ min_eq_right ( show 2 * r ≤ 1 by linarith ) ]



open MeasureTheory in
lemma edgeSet01_measurable (r : ℝ) : MeasurableSet (edgeSet01 r) := by
  exact measurableSet_le (measurable_pi_apply 0 |>.dist (measurable_pi_apply 1)) measurable_const



open MeasureTheory in
lemma edgeSet01_torus_eq (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) :
    ({pts : Fin 3 → Torus d | dist (pts 0) (pts 1) ≤ r} : Set (Fin 3 → Torus d))
    = {pts | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ edgeSet01 r} := by
  ext; simp [edgeSet01, dist_pi_le_iff hr0]



open Classical MeasureTheory in
lemma edge_integral_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
  -- Since the edge set is measurable, we can apply the volume calculation.
  have h_edge_meas : MeasurableSet {pts : Fin 3 → Torus d | dist (pts 0) (pts 1) ≤ matchRadius p d} := by
    exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
  convert congr_arg ENNReal.toReal ( show MeasureTheory.Measure.pi ( fun _ : Fin 3 => MeasureTheory.volume ) { pts : Fin 3 → Torus d | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d } = ENNReal.ofReal p from ?_ ) using 1;
  · erw [ MeasureTheory.integral_indicator h_edge_meas ] ; norm_num;
    rfl;
  · rw [ ENNReal.toReal_ofReal hp0.le ];
  · convert volume_coordFactored_eq_pow d ( edgeSet01 ( matchRadius p d ) ) ( edgeSet01_measurable _ ) using 1;
    · convert rfl using 2;
      convert edgeSet01_torus_eq d hd ( matchRadius p d ) ( by
        exact le_of_lt ( matchRadius_pos' p d hp0 hd ) ) |> Eq.symm;
    · rw [ volume_edgeSet01 ];
      · rw [ ← ENNReal.ofReal_pow ];
        · rw [ matchRadius_spec p d hp0 hp1 hd ];
        · exact mul_nonneg zero_le_two ( le_of_lt ( matchRadius_pos' p d hp0 hd ) );
      · exact le_of_lt ( matchRadius_pos' p d hp0 hd );
      · exact?



open Classical MeasureTheory in
lemma edge_integral_02_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
  convert edge_integral_free p d hp0 hp1 hd using 1;
  -- The measure is invariant under the permutation of the coordinates.
  have h_perm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 1 2 i)) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
    refine' ⟨ _, _ ⟩;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
      intro s hs; erw [ MeasureTheory.Measure.map_apply ];
      · rw [ show ( fun pts i => pts ( Equiv.swap 1 2 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ fun i => s ( Equiv.swap 1 2 i ) from ?_ ];
        · rw [ MeasureTheory.Measure.pi_pi ];
          exact Equiv.prod_comp ( Equiv.swap 1 2 ) fun i => volume ( s i );
        · grind;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · exact MeasurableSet.univ_pi hs;
  rw [ ← h_perm.integral_comp ] ; norm_num [ Equiv.swap_apply_def ] ;
  · rfl;
  · constructor;
    · exact fun x y h => funext fun i => by simpa using congr_fun h ( Equiv.swap 1 2 i ) ; ;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · intro s hs;
      convert hs.preimage ( show Measurable ( fun pts : Fin 3 → Torus d => fun i => pts ( Equiv.swap 1 2 i ) ) from ?_ ) using 1;
      · ext; simp [Set.mem_image, Set.mem_preimage];
        exact ⟨ fun ⟨ x, hx, hx' ⟩ => by simpa [ ← hx' ] using hx, fun hx => ⟨ fun i => ‹Fin 3 → Torus d› ( Equiv.swap 1 2 i ), by simpa using hx, by ext i; simp +decide ⟩ ⟩;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _



open Classical MeasureTheory in
lemma edge_integral_12_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
  convert edge_integral_02_free p d hp0 hp1 hd using 1;
  -- By definition of permutation, we can rewrite the integral.
  have h_perm : ∀ (f : (Fin 3 → Torus d) → ℝ), ∫ pts : Fin 3 → Torus d, f pts ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))) = ∫ pts : Fin 3 → Torus d, f (fun i => pts (Equiv.swap 0 1 i)) ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))) := by
    intro f
    have h_perm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
      refine' ⟨ _, _ ⟩;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
        intro s hs; rw [ Measure.map_apply ] ;
        · rw [ show ( fun pts i => pts ( Equiv.swap 0 1 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 0 1 i ) ) from ?_ ];
          · rw [ MeasureTheory.Measure.pi_pi ];
            exact Equiv.prod_comp ( Equiv.swap 0 1 ) fun i => volume ( s i );
          · grind;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · exact MeasurableSet.univ_pi hs;
    rw [ ← h_perm.integral_comp ];
    constructor;
    · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
    · fun_prop;
    · intro s hs;
      rw [ Set.image_eq_preimage_of_inverse ];
      rotate_right;
      use fun pts => fun i => pts ( Equiv.swap 0 1 i );
      · exact h_perm.measurable hs;
      · exact fun x => by ext i; fin_cases i <;> rfl;
      · grind;
  exact Real.ext_cauchy
    (congrArg Real.cauchy
      (h_perm fun pts => if dist (pts 1) (pts 2) ≤ matchRadius p d then 1 else 0))



open MeasureTheory in
lemma volume_wedgeSet01 (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1 / 2) :
    volume (wedgeSet01 r) = ENNReal.ofReal (4 * r ^ 2) := by
  have h_volume_wedgeSet : volume (wedgeSet01 r) = ∫⁻ (f0 : T1), ∫⁻ (f1 : T1), ∫⁻ (f2 : T1), (if dist f0 f1 ≤ r ∧ dist f0 f2 ≤ r then 1 else 0) ∂volume ∂volume ∂volume := by
    have h_volume_wedgeSet : volume (wedgeSet01 r) = ∫⁻ (f : Fin 3 → T1), (if dist (f 0) (f 1) ≤ r ∧ dist (f 0) (f 2) ≤ r then 1 else 0) ∂Measure.pi (fun _ : Fin 3 => (volume : Measure T1)) := by
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      change volume (wedgeSet01 r) = ∫⁻ x in wedgeSet01 r, 1 ∂Measure.pi (fun _ : Fin 3 => (volume : Measure T1));
      · norm_num +zetaDelta at *;
        rfl;
      · exact measurableSet_le ( continuous_dist.measurable.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const |> MeasurableSet.inter <| measurableSet_le ( continuous_dist.measurable.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by unfold wedgeSet01; aesop; ;
    rw [h_volume_wedgeSet];
    have h_fubini : ∀ {f : (Fin 3 → T1) → ENNReal}, Measurable f → ∫⁻ (f' : Fin 3 → T1), f f' ∂Measure.pi (fun _ : Fin 3 => (volume : Measure T1)) = ∫⁻ (f0 : T1), ∫⁻ (f1 : T1), ∫⁻ (f2 : T1), f (fun i => if i = 0 then f0 else if i = 1 then f1 else f2) ∂volume ∂volume ∂volume := by
      intro f hf
      have h_fubini : ∫⁻ (f' : Fin 3 → T1), f f' ∂Measure.pi (fun _ : Fin 3 => (volume : Measure T1)) = ∫⁻ (f' : T1 × T1 × T1), f (fun i => if i = 0 then f'.1 else if i = 1 then f'.2.1 else f'.2.2) ∂Measure.prod (volume) (Measure.prod (volume) (volume)) := by
        have h_fubini : Measure.pi (fun _ : Fin 3 => (volume : Measure T1)) = Measure.map (fun f' : T1 × T1 × T1 => fun i => if i = 0 then f'.1 else if i = 1 then f'.2.1 else f'.2.2) (Measure.prod (volume) (Measure.prod (volume) (volume))) := by
          rw [ MeasureTheory.Measure.pi_eq ];
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three, hs ] ;
          · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
            erw [ show { x : T1 × T1 × T1 | x.1 ∈ s 0 ∧ x.2.1 ∈ s 1 ∧ x.2.2 ∈ s 2 } = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ; erw [ MeasureTheory.Measure.prod_prod ] ; ring;
          · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
          · exact MeasurableSet.univ_pi hs;
        rw [ h_fubini, MeasureTheory.lintegral_map ];
        · exact hf;
        · exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
      erw [ h_fubini, MeasureTheory.lintegral_prod ];
      · congr! 2;
        erw [ MeasureTheory.lintegral_prod ];
        exact hf.comp ( measurable_pi_lambda _ fun i => by fin_cases i <;> measurability ) |> Measurable.aemeasurable;
      · exact hf.aemeasurable.comp_aemeasurable ( by exact Measurable.aemeasurable ( by exact measurable_pi_lambda _ fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ) );
    convert h_fubini _ using 1;
    exact Measurable.ite ( MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) ) measurable_const measurable_const;
  -- The inner integrals over $f1$ and $f2$ are both equal to $2r$ since $r < 1/2$.
  have h_inner : ∀ f0 : T1, ∫⁻ (f1 : T1), (if dist f0 f1 ≤ r then 1 else 0) ∂volume = ENNReal.ofReal (2 * r) := by
    intro f0
    have h_inner : ∫⁻ (f1 : T1), (if dist f0 f1 ≤ r then 1 else 0) ∂volume = volume (Metric.closedBall f0 r) := by
      erw [ MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
      · congr with x ; simp +decide [ dist_comm ];
        exact Iff.rfl;
      · exact measurableSet_le ( measurable_const.dist measurable_id' ) measurable_const;
    rw [ h_inner, AddCircle.volume_closedBall ] ; norm_num [ hr0, hr ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · rw [ ENNReal.toReal_ofReal ] <;> linarith;
    · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( ENNReal.ofReal_ne_top );
  have h_inner2 : ∀ f0 : T1, ∫⁻ (f1 : T1), ∫⁻ (f2 : T1), (if dist f0 f1 ≤ r ∧ dist f0 f2 ≤ r then 1 else 0) ∂volume ∂volume = ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r) := by
    intro f0;
    rw [ ← h_inner f0, ← MeasureTheory.lintegral_const_mul' ];
    · congr with f1 ; by_cases h : dist f0 f1 ≤ r <;> simp +decide [ h ];
    · exact h_inner f0 ▸ ENNReal.ofReal_ne_top;
  rw [ h_volume_wedgeSet, MeasureTheory.lintegral_congr_ae ( Filter.Eventually.of_forall h_inner2 ) ] ; norm_num [ mul_assoc, mul_comm, mul_left_comm, hr0 ] ; ring;



open MeasureTheory in
lemma wedgeSet01_measurable (r : ℝ) : MeasurableSet (wedgeSet01 r) :=
  MeasurableSet.inter
    (measurableSet_le (measurable_pi_apply 0 |>.dist (measurable_pi_apply 1)) measurable_const)
    (measurableSet_le (measurable_pi_apply 0 |>.dist (measurable_pi_apply 2)) measurable_const)



open MeasureTheory in
lemma wedgeSet01_torus_eq (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) :
    ({pts : Fin 3 → Torus d | dist (pts 0) (pts 1) ≤ r ∧ dist (pts 0) (pts 2) ≤ r} : Set (Fin 3 → Torus d))
    = {pts | ∀ i : Fin d, (fun j : Fin 3 => pts j i) ∈ wedgeSet01 r} := by
  ext; simp [wedgeSet01, dist_pi_le_iff hr0]; constructor <;> intro h <;> simp_all [dist_pi_le_iff]



open Classical MeasureTheory in
lemma wedge_integral_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
  have h_volume : volume {pts : Fin 3 → Torus d | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d} = ENNReal.ofReal (p^2) := by
    convert volume_coordFactored_eq_pow d ( wedgeSet01 ( matchRadius p d ) ) ( wedgeSet01_measurable _ ) using 1;
    · rw [ wedgeSet01_torus_eq d hd ( matchRadius p d ) ( matchRadius_pos' p d hp0 hd |> le_of_lt ) ];
    · rw [ volume_wedgeSet01 ];
      · have h_matchRadius : (2 * matchRadius p d) ^ d = p := by
          exact?;
        rw [ show p ^ 2 = ( 4 * matchRadius p d ^ 2 ) ^ d by rw [ show ( 4 * matchRadius p d ^ 2 ) = ( 2 * matchRadius p d ) ^ 2 by ring, pow_right_comm ] ; rw [ h_matchRadius ] ] ; norm_num [ ENNReal.ofReal_pow ];
        rw [ ENNReal.ofReal_pow ] <;> norm_num [ ENNReal.ofReal_mul ];
        positivity;
      · exact le_of_lt ( matchRadius_pos' p d hp0 hd );
      · exact?;
  rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
  change (∫ x in { pts : Fin 3 → Torus d | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d ∧ dist ( pts 0 ) ( pts 2 ) ≤ matchRadius p d }, 1 ∂Measure.pi fun _ => volume) = p ^ 2;
  · convert congr_arg ENNReal.toReal h_volume using 1 ; norm_num [ hp0.le, hp1.le ];
    · rfl;
    · rw [ ENNReal.toReal_ofReal ( sq_nonneg p ) ];
  · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
  · filter_upwards [ ] with x using by rw [ Set.indicator_apply ] ; aesop;



open Classical MeasureTheory in
lemma wedge_integral_1center_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
  have h_perm : ∀ f : Fin 3 → Torus d, dist (f 0) (f 1) = dist (f 1) (f 0) ∧ dist (f 1) (f 2) = dist (f 2) (f 1) := by
    exact fun f => ⟨ dist_comm _ _, dist_comm _ _ ⟩;
  have h_perm : MeasureTheory.MeasurePreserving (fun f : Fin 3 → Torus d => fun i => f (Equiv.swap 0 1 i)) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
    refine' ⟨ _, _ ⟩;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
      intro s hs; rw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ hs, Fin.prod_univ_three ] ;
      · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
        erw [ show { x : Fin 3 → Torus d | x 1 ∈ s 0 ∧ x 0 ∈ s 1 ∧ x 2 ∈ s 2 } = ( Set.pi Set.univ fun i => if i = 0 then s 1 else if i = 1 then s 0 else s 2 ) by ext; simp +decide [ Fin.forall_fin_succ ] ; tauto ] ; erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · exact MeasurableSet.univ_pi hs;
  convert congr_arg ( fun x : ℝ => x ) ( wedge_integral_free p d hp0 hp1 hd ) using 1;
  rw [ ← h_perm.integral_comp ];
  · simp +decide [ Equiv.swap_apply_def ];
    simp +decide only [dist_comm];
  · constructor;
    · exact fun f g h => funext fun i => by simpa using congr_fun h ( Equiv.swap 0 1 i ) ; ;
    · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
    · intro s hs;
      convert hs.preimage ( show Measurable ( fun f : Fin 3 → Torus d => fun i => f ( Equiv.swap 0 1 i ) ) from ?_ ) using 1;
      · ext; simp [Set.mem_image, Set.mem_preimage];
        exact ⟨ fun ⟨ x, hx, hx' ⟩ => hx'.symm ▸ by simpa using hx, fun hx => ⟨ fun i => ‹Fin 3 → Torus d› ( Equiv.swap 0 1 i ), hx, by ext i; simp +decide ⟩ ⟩;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _



open Classical MeasureTheory in
lemma wedge_integral_2center_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
  convert wedge_integral_1center_free p d hp0 hp1 hd using 1;
  -- Since the measure is invariant under permutation of the coordinates, the integrals of the two functions are equal.
  have h_measure_invariant : ∀ (f : (Fin 3 → Torus d) → ℝ), (∫ pts, f pts ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) = (∫ pts, f (fun i => pts (Equiv.swap 1 2 i)) ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
    intro f
    apply Eq.symm;
    -- Apply the fact that the permutation is measure-preserving.
    have h_measure_preserving : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 1 2 i)) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
      refine' ⟨ _, _ ⟩;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
        intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ hs, Fin.prod_univ_three ] ;
        · rw [ show ( fun pts i => pts ( Equiv.swap 1 2 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 1 2 i ) ) from ?_ ];
          · rw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
          · grind;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · exact MeasurableSet.univ_pi hs;
    rw [ ← h_measure_preserving.integral_comp ];
    · exact congr_arg _ ( funext fun x => by congr; ext i; fin_cases i <;> rfl );
    · constructor;
      · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 1 2 i ) ;
      · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
      · intro s hs;
        convert hs.preimage ( show Measurable ( fun pts : Fin 3 → Torus d => fun i => pts ( Equiv.swap 1 2 i ) ) from ?_ ) using 1;
        · ext; simp [Set.mem_image, Set.mem_preimage];
          exact ⟨ fun ⟨ x, hx, hx' ⟩ => by simpa [ ← hx' ] using hx, fun hx => ⟨ fun i => ‹Fin 3 → Torus d› ( Equiv.swap 1 2 i ), by simpa using hx, by ext i; simp +decide ⟩ ⟩;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
  convert h_measure_invariant _ using 3 ; simp +decide [ dist_comm ];
  simp +decide [ dist_comm, Equiv.swap_apply_def ]



open Classical MeasureTheory in
lemma centered_edge_moment_fill_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
       (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
       (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0))
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (1 - p) ^ 3 * fillingProb p d := by
  have h_fill : fillingProb p d = ∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then 1 else 0)
       * (if dist (pts 0) (pts 2) ≤ matchRadius p d then 1 else 0)
       * (if dist (pts 1) (pts 2) ≤ matchRadius p d then 1 else 0))
      ∂Measure.pi (fun _ => volume) := by
    simp [fillingProb]
  rw [h_fill, ← MeasureTheory.integral_const_mul]; congr; ext; split_ifs <;> ring



open Classical MeasureTheory in
lemma centered_edge_moment_free (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = fillingProb p d - p ^ 3 := by
  have h_expand : ∀ (x₁ x₂ x₃ : ℝ), (x₁ - p) * (x₂ - p) * (x₃ - p) = x₁ * x₂ * x₃ - p * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) + p ^ 2 * (x₁ + x₂ + x₃) - p ^ 3 := by
    intros; ring;
  simp_all +decide [ MeasureTheory.integral_sub, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
  rw [ MeasureTheory.integral_sub, MeasureTheory.integral_add ];
  · rw [ MeasureTheory.integral_sub ] <;> norm_num [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const ];
    · rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
      · rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
        · rw [ show fillingProb p d = ∫ pts : Fin 3 → Torus d, ( if dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d then ( 1 : ℝ ) else 0 ) * ( if dist ( pts 0 ) ( pts 2 ) ≤ matchRadius p d then ( 1 : ℝ ) else 0 ) * ( if dist ( pts 1 ) ( pts 2 ) ≤ matchRadius p d then ( 1 : ℝ ) else 0 ) ∂Measure.pi fun _ => volume from ?_ ];
          · rw [ edge_integral_free, edge_integral_02_free, edge_integral_12_free ] <;> try linarith;
            rw [ show ( ∫ a : Fin 3 → Torus d, if dist ( a 0 ) ( a 2 ) ≤ matchRadius p d then if dist ( a 0 ) ( a 1 ) ≤ matchRadius p d then 1 else 0 else 0 ∂Measure.pi fun x => volume ) = p ^ 2 by
                  convert wedge_integral_free p d hp0 hp1 hd using 1;
                  exact congr_arg _ ( funext fun x => by split_ifs <;> ring ), show ( ∫ a : Fin 3 → Torus d, if dist ( a 1 ) ( a 2 ) ≤ matchRadius p d then if dist ( a 0 ) ( a 1 ) ≤ matchRadius p d then 1 else 0 else 0 ∂Measure.pi fun x => volume ) = p ^ 2 by
                                                                                                                                                                                                              convert wedge_integral_1center_free p d hp0 hp1 hd using 1;
                                                                                                                                                                                                              exact congr_arg _ ( funext fun x => by split_ifs <;> ring ), show ( ∫ a : Fin 3 → Torus d, if dist ( a 1 ) ( a 2 ) ≤ matchRadius p d then if dist ( a 0 ) ( a 2 ) ≤ matchRadius p d then 1 else 0 else 0 ∂Measure.pi fun x => volume ) = p ^ 2 by
                                                                                                                                                                                                                                                                                                                                                                                                          convert wedge_integral_2center_free p d hp0 hp1 hd using 1;
                                                                                                                                                                                                                                                                                                                                                                                                          exact congr_arg _ ( funext fun x => by split_ifs <;> ring ) ] ; ring;
            exact congr_arg _ ( funext fun x => by split_ifs <;> ring );
          · exact MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall fun x => by aesop );
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact MeasureTheory.integrable_const _;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.add _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num;
            · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 2 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact MeasureTheory.integrable_const _;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num;
          · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.add _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 1 |> Measurable.sub <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
  · refine' MeasureTheory.Integrable.sub _ _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.add _ _;
      · refine' MeasureTheory.Integrable.add _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 1 |> Measurable.sub <| measurable_pi_apply 2 ) ) measurable_const;
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 1 ) ) measurable_const;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · fun_prop;
      · exact measurableSet_le ( measurable_norm.comp ( measurable_pi_apply 0 |> Measurable.sub <| measurable_pi_apply 2 ) ) measurable_const;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun _ => 1 + p * 3 + p ^ 2 * 3;
    · norm_num [ MeasureTheory.integrable_const_iff ];
    · refine' Measurable.aestronglyMeasurable _;
      apply_rules [ Measurable.sub, Measurable.add, Measurable.mul, measurable_const ];
      all_goals apply_rules [ Measurable.ite, measurable_const ];
      all_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
    · refine' Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ _, _ ⟩ <;> split_ifs <;> nlinarith;
  · fun_prop
