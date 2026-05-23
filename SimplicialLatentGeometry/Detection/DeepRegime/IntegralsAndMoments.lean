import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.DeepRegime.IntegralsAndMoments`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


-- ────────────────────────────────────────────────────────────────────────────
-- OQ-16 / Track A: quantitative `geomCov` decay rate (sim-A5 packet, session 31).
-- See `analytic_decay_rate.md` and `requests/sim_A5_packet.md` for derivations.
-- ────────────────────────────────────────────────────────────────────────────

/-- **Helper: 1D-Helly trivialisation.** If two arcs share a common centre vertex,
    the triple intersection is automatically nonempty: pick `z = x₁`. -/
lemma wedge_implies_fill {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r) (x₁ x₂ x₃ : Torus d)
    (h12 : dist x₁ x₂ ≤ r) (h13 : dist x₁ x₃ ≤ r) :
    ∃ z : Torus d, dist x₁ z ≤ r ∧ dist x₂ z ≤ r ∧ dist x₃ z ≤ r := by
  refine ⟨x₁, ?_, ?_, ?_⟩
  · simp [dist_self]; exact hr0
  · rw [dist_comm]; exact h12
  · rw [dist_comm]; exact h13



open Classical MeasureTheory in
/-- **Sim-A5 / Job 1, Lemma 1.** Triangle (3-pairwise-edge) probability under Čech,
    deep regime `r ≤ 1/4`. Equals `(3 r²)^d` by sup-norm coordinate factorisation
    and the 1D area calculation: in each coordinate, the event "all 3 pairwise
    distances ≤ r" has probability `3 r²` (square `[-r,r]²` of area `4r²` minus
    two corner triangles of total area `r²`).

    PROVIDED SOLUTION
    Step 1: Apply `MeasureTheory.integral_fintype_prod` (or `volume_pi` + Fubini)
      to reduce the `Fin 3 → Torus d` integral to nested integrals over `Torus d`.
    Step 2: Use sup-norm coordinate decomposition (`Pi.dist_def`) to factor the
      indicator product across the `d` torus coordinates.
    Step 3: Per coordinate, condition on `u₁ = 0`. The event becomes
      `|u₂| ≤ r ∧ |u₃| ≤ r ∧ |u₂ - u₃| ≤ r` on the square `[-r,r]²`.
      Area of square: `4 r²`. Area cut by `|u₂ - u₃| ≤ r` constraint: two
      corner right-triangles of legs `r`, total area `r²`. Remaining area: `3 r²`.
    Step 4: Per-coordinate probability is `3 r²`. Raise to dth power. -/
lemma gamma_pow_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (3 * (matchRadius p d) ^ 2) ^ d := by
  convert integral_triangle_eq_pow d hd ( matchRadius p d ) ( by unfold matchRadius; positivity ) hr using 1



open Classical MeasureTheory in
/-- **Sim-A5 / Job 1, Lemma 2.** Single-edge ∧ fill probability under Čech,
    deep regime `r ≤ 1/4`. Equals `(7 r²)^d`.

    PROVIDED SOLUTION
    Step 1: Same coordinate factorisation as `gamma_pow_eq`. Per coordinate,
      we need `PP[|u₁ - u₂| ≤ r ∧ ∃ z : |u_i - z| ≤ r ∀ i]`.
    Step 2: Condition on `u₁ = 0, u₂ = s` with `|s| ≤ r`. The set of valid
      `z` is the overlap arc `[max(-r, s-r), min(r, s+r)]` of length `2r - |s|`.
      Then `u₃ ∈ B(z, r)` for some such `z` ⟺ `u₃ ∈ [s - 2r + |s|, 2r - |s|]`...
      wait — easier: `u₃ ∈ ⋃_z B(z, r) = [\min_z (z-r), \max_z (z+r)]
      = [\min(-r, s-r) - r, \max(r, s+r) + r]`. For `s ∈ [0, r]`, this is
      `[-2r + s, 2r]`... Length `4r - s` for `s ∈ [0, r]` (and `4r + s` for
      `s ∈ [-r, 0]`, equivalently `4r - |s|`).
    Step 3: Per-coordinate probability:
      `∫_{-r}^{r} (4r - |s|) ds = 2 ∫_0^r (4r - s) ds = 2(4r² - r²/2) = 7 r²`.
    Step 4: Raise to dth power. -/
lemma mu_e_pow_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (7 * (matchRadius p d) ^ 2) ^ d := by
  exact integral_edgeFill_eq_pow d hd ( matchRadius p d ) ( by unfold matchRadius; positivity ) hr



/-- **Filling probability closed form, Rips convention, deep regime `r ≤ 1/4`.**
    Under Rips, F_ijk = A_ij·A_ik·A_jk so `fillingProb p d` equals the triangle
    (3-clique) probability `(3r²)^d` from `gamma_pow_eq`. -/
lemma fillingProb_eq_low_r (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    fillingProb p d = (3 * (matchRadius p d) ^ 2) ^ d := by
  unfold fillingProb
  exact gamma_pow_eq p d hp0 hp1 hd hr



/-
────────────────────────────────────────────────────────────────────────────
Helper lemmas for geometricCov expansion
────────────────────────────────────────────────────────────────────────────
-/
open Classical MeasureTheory in
/-- The integral of a single edge indicator over the 3-point product measure
    equals the edge probability `p = (2r)^d`. -/
lemma edge_integral (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
  have h_volume_edge : volume ( {pts : Fin 3 → Torus d | dist (pts 0) (pts 1) ≤ matchRadius p d} ) = ENNReal.ofReal ( (2 * matchRadius p d) ^ d ) := by
    convert volume_coordFactored_eq_pow d ( { pts : Fin 3 → AddCircle ( 1 : ℝ ) | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d } ) _ using 1;
    · congr with x ; simp +decide [ dist_eq_norm ];
      rw [ pi_norm_le_iff_of_nonneg ];
      · rfl;
      · unfold matchRadius; positivity;
    · have h_volume_edge : volume ( {pts : Fin 3 → AddCircle ( 1 : ℝ ) | dist (pts 0) (pts 1) ≤ matchRadius p d} ) = ENNReal.ofReal (2 * matchRadius p d) := by
        have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d} = ∫⁻ (x : T1), volume {y : T1 | dist x y ≤ matchRadius p d} ∂volume := by
          have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d} = ∫⁻ (x : T1 × T1 × T1), (if dist x.1 x.2.1 ≤ matchRadius p d then 1 else 0) ∂volume := by
            have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d} = ∫⁻ (x : Fin 3 → T1), (if dist (x 0) (x 1) ≤ matchRadius p d then 1 else 0) ∂volume := by
              erw [ MeasureTheory.lintegral_indicator ];
              · aesop;
              · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
            rw [ h_volume ];
            have h_volume : MeasureTheory.MeasureSpace.volume = MeasureTheory.Measure.map (fun x : T1 × T1 × T1 => ![x.1, x.2.1, x.2.2]) (MeasureTheory.MeasureSpace.volume) := by
              simp +decide [ MeasureTheory.MeasureSpace.volume ];
              erw [ MeasureTheory.Measure.pi_eq ];
              intro s hs; erw [ MeasureTheory.Measure.map_apply ];
              · simp +decide [ Set.preimage, Fin.prod_univ_three ];
                simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
                erw [ show { a : T1 × T1 × T1 | a.1 ∈ s 0 } ∩ ( { a : T1 × T1 × T1 | a.2.1 ∈ s 1 } ∩ { a : T1 × T1 × T1 | a.2.2 ∈ s 2 } ) = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; simp +decide [ mul_assoc ];
              · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
              · exact MeasurableSet.univ_pi hs;
            rw [ h_volume, MeasureTheory.lintegral_map ];
            · rfl;
            · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
            · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
          erw [ h_volume, MeasureTheory.lintegral_prod ];
          · congr! 2;
            erw [ MeasureTheory.lintegral_prod ];
            · erw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
              exact?;
              · exact measurableSet_le ( measurable_const.dist measurable_id' ) measurable_const;
              · filter_upwards [ ] with x ; aesop;
            · exact Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_le ( measurable_const.dist measurable_fst ) measurable_const ) measurable_const measurable_const );
          · exact Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_le ( measurable_fst.dist measurable_snd.fst ) measurable_const ) measurable_const measurable_const );
        have h_volume : ∀ x : T1, volume {y : T1 | dist x y ≤ matchRadius p d} = ENNReal.ofReal (2 * matchRadius p d) := by
          intro x;
          convert volume_closedBall_inter_T1 ( matchRadius p d ) ( show 0 ≤ matchRadius p d from ?_ ) ( show matchRadius p d ≤ 1 / 4 from hr ) x x ?_ using 1 <;> norm_num [ dist_comm ];
          · exact congr_arg _ ( by ext; simp +decide [ dist_comm ] );
          · unfold matchRadius; positivity;
          · unfold matchRadius; positivity;
        aesop;
      rw [ h_volume_edge, ENNReal.ofReal_pow ( by exact mul_nonneg zero_le_two ( by unfold matchRadius; positivity ) ) ];
    · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
  convert congr_arg ENNReal.toReal h_volume_edge using 1;
  · erw [ MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    · rfl;
    · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const;
  · rw [ ENNReal.toReal_ofReal ( pow_nonneg ( mul_nonneg zero_le_two ( by unfold matchRadius; positivity ) ) _ ), matchRadius_spec p d hp0 hp1 hd ]



open Classical MeasureTheory in
/-- The integral of a wedge indicator (two edges sharing a vertex) over the
    3-point product measure equals `p²`, because the two edge events are
    conditionally independent given the shared vertex. -/
lemma wedge_integral (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
  have h_volume : (∫ (pts : Fin 3 → Torus d), (if dist (pts 0) (pts 1) ≤ matchRadius p d then 1 else 0) * (if dist (pts 0) (pts 2) ≤ matchRadius p d then 1 else 0) ∂Measure.pi fun _ => volume) = (4 * (matchRadius p d) ^ 2) ^ d := by
    convert volume_coordFactored_eq_pow d _ _ using 1;
    case convert_1 => exact { pts : Fin 3 → T1 | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d ∧ dist ( pts 0 ) ( pts 2 ) ≤ matchRadius p d };
    · rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
      change (∫ x in { pts : Fin 3 → Torus d | dist ( pts 0 ) ( pts 1 ) ≤ matchRadius p d ∧ dist ( pts 0 ) ( pts 2 ) ≤ matchRadius p d }, 1 ∂Measure.pi fun _ => volume) = _ ↔ _;
      · simp +decide [ MeasureTheory.measureReal_def ];
        rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
        convert Iff.rfl using 2;
        · congr! 2;
          ext; simp +decide [ dist_pi_le_iff ] ;
          rw [ dist_pi_le_iff, dist_pi_le_iff ] ; aesop;
          · unfold matchRadius; positivity;
          · unfold matchRadius; positivity;
        · have h_volume : volume {pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d} = ENNReal.ofReal (4 * (matchRadius p d) ^ 2) := by
            have h_volume : volume ({pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d}) = ∫⁻ (u1 : T1), volume ({c : T1 | dist u1 c ≤ matchRadius p d}) * volume ({c : T1 | dist u1 c ≤ matchRadius p d}) ∂volume := by
              have h_volume : volume ({pts : Fin 3 → T1 | dist (pts 0) (pts 1) ≤ matchRadius p d ∧ dist (pts 0) (pts 2) ≤ matchRadius p d}) = ∫⁻ (u1 : T1), volume ({c : T1 × T1 | dist u1 c.1 ≤ matchRadius p d ∧ dist u1 c.2 ≤ matchRadius p d}) ∂volume := by
                erw [ MeasureTheory.volume_pi ];
                erw [ MeasureTheory.Measure.pi_eq ];
                rotate_right;
                exact MeasureTheory.Measure.map ( fun x : T1 × T1 × T1 => ![x.1, x.2.1, x.2.2] ) ( MeasureTheory.Measure.prod ( MeasureTheory.MeasureSpace.volume ) ( MeasureTheory.Measure.prod ( MeasureTheory.MeasureSpace.volume ) ( MeasureTheory.MeasureSpace.volume ) ) );
                · rw [ MeasureTheory.Measure.map_apply ];
                  · erw [ MeasureTheory.Measure.prod_apply ];
                    · congr! 2;
                    · simp +decide [ Set.preimage ];
                      exact MeasurableSet.mem ( MeasurableSet.inter ( measurableSet_le ( measurable_fst.dist measurable_snd.fst ) measurable_const ) ( measurableSet_le ( measurable_fst.dist measurable_snd.snd ) measurable_const ) );
                  · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ];
                  · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
                · intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; norm_num [ Fin.prod_univ_three ] ;
                  · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
                    erw [ show { x : T1 × T1 × T1 | x.1 ∈ s 0 ∧ x.2.1 ∈ s 1 ∧ x.2.2 ∈ s 2 } = ( s 0 ×ˢ s 1 ×ˢ s 2 ) by ext ; aesop ] ; erw [ MeasureTheory.Measure.prod_prod ] ; erw [ MeasureTheory.Measure.prod_prod ] ; ring;
                  · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_fst; exact measurable_snd.fst; exact measurable_snd.snd ] ;
                  · exact MeasurableSet.univ_pi hs;
              convert h_volume using 3;
              erw [ ← MeasureTheory.Measure.prod_prod ];
              exact?;
            have h_volume : ∀ u1 : T1, volume ({c : T1 | dist u1 c ≤ matchRadius p d}) = ENNReal.ofReal (2 * matchRadius p d) := by
              intro u1;
              have h_volume : volume (Metric.closedBall u1 (matchRadius p d)) = ENNReal.ofReal (2 * matchRadius p d) := by
                rw [ two_mul, AddCircle.volume_closedBall ];
                grind;
              convert h_volume using 1;
              exact congr_arg _ ( by ext; simp +decide [ dist_comm ] );
            simp_all +decide [ mul_pow ];
            rw [ ENNReal.ofReal_pow ( by unfold matchRadius; positivity ) ] ; ring;
          rw [ h_volume, ENNReal.toReal_ofReal ( by positivity ) ];
      · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
      · filter_upwards [ ] with x using by rw [ Set.indicator_apply ] ; aesop;
    · exact MeasurableSet.inter ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const );
  convert h_volume using 1;
  rw [ show 4 * matchRadius p d ^ 2 = ( 2 * matchRadius p d ) ^ 2 by ring, ← pow_mul, Nat.mul_comm, pow_mul, matchRadius_spec p d hp0 hp1 hd ]



open Classical MeasureTheory in
/-- Algebraic identity: `p² · (7r²)^d = p³ · (7r/2)^d`,
    used to convert between the mu_e and half-radius forms. -/
lemma p_sq_mu_eq (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d) :
    p ^ 2 * (7 * (matchRadius p d) ^ 2) ^ d
    = p ^ 3 * (7 * matchRadius p d / 2) ^ d := by
  have h_match : p = (2 * matchRadius p d) ^ d := by
    exact?;
  rw [ show p ^ 3 = p ^ 2 * p by ring, h_match ] ; ring;
  rw [ show matchRadius p d ^ d * 2 ^ d = p by rw [ ← mul_pow, mul_comm ] ; exact h_match.symm ] ; ring;
  norm_num [ pow_mul', ← mul_pow ] ; ring



-- DEPRECATED (Sim-A5 / Job 2): the original `geometricCov_eq_deep` 8-term-collapse
-- closed form was disproved (wedge contributions don't vanish; the formula was off by
-- `-3p^3(1-q)`). Superseded by the session-75 regime-free closed form `geometricCov_eq`
-- and the headline `geometricCov_tendsto_pcubed_compcubed`. Removed 2026-05-19.

/-! ### Symmetric integral helpers -/

open Classical MeasureTheory in
/-- Integral of A₁₃ (edge indicator for vertices 0,2) equals p. By symmetry with edge_integral. -/
lemma edge_integral_02 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
      -- The swap is measure-preserving, so the integral of the composition is equal to the integral of the original function.
      have h_swap : MeasureTheory.MeasurePreserving (fun (pts : Fin 3 → Torus d) => fun i => pts (Equiv.swap 1 2 i)) (MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ *, Fin.prod_univ_three ] ;
          · rw [ show ( fun pts i => pts ( Equiv.swap 1 2 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 1 2 i ) ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
            · grind;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      convert edge_integral p d hp0 hp1 hd hr using 1;
      rw [ ← h_swap.integral_comp ];
      · rfl;
      · constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 1 2 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 1 2 i );
          · exact hs.preimage ( measurable_pi_lambda _ fun _ => measurable_pi_apply _ );
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;



open Classical MeasureTheory in
/-- Integral of A₂₃ (edge indicator for vertices 1,2) equals p. By symmetry with edge_integral. -/
lemma edge_integral_12 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p := by
      convert edge_integral_02 p d hp0 hp1 hd hr using 1;
      -- Apply the measure-preserving permutation to the integral.
      have h_perm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (Measure.pi (fun _ => volume)) (Measure.pi (fun _ => volume)) := by
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three ] ;
          · rw [ show ( fun pts : Fin 3 → Torus d => fun i => pts ( Equiv.swap 0 1 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 0 1 i ) ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
            · grind +qlia;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_perm.integral_comp ];
      · rfl;
      · refine' ⟨ _, _, _ ⟩;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 0 1 i );
          · exact h_perm.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;



open Classical MeasureTheory in
/-- Wedge integral for edges (0,1) and (1,2), sharing vertex 1, equals p². -/
lemma wedge_integral_1center (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
      have := @wedge_integral;
      convert this p d hp0 hp1 hd hr using 1;
      -- The permutation that swaps 0 and 1 and leaves 2 fixed is measure-preserving.
      have h_perm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (Measure.pi (fun _ : Fin 3 => volume)) (Measure.pi (fun _ : Fin 3 => volume)) := by
        refine' ⟨ _, _ ⟩;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three, hs ] ;
          · simp +decide [ Set.preimage, Fin.forall_fin_succ ];
            erw [ show { x : Fin 3 → Torus d | x 1 ∈ s 0 ∧ x 0 ∈ s 1 ∧ x 2 ∈ s 2 } = ( Set.pi Set.univ fun i => if i = 0 then s 1 else if i = 1 then s 0 else s 2 ) by ext; simp +decide [ Fin.forall_fin_succ ] ; tauto ] ; erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_perm.integral_comp ];
      · simp +decide [ dist_comm ];
        rfl;
      · constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 0 1 i );
          · exact h_perm.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;



open Classical MeasureTheory in
/-- Wedge integral for edges (0,2) and (1,2), sharing vertex 2, equals p². -/
lemma wedge_integral_2center (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = p ^ 2 := by
      -- The integral is invariant under permutation of the variables, so we canswap the variables.
      have h_perm : ∀ (f : (Fin 3 → Torus d) → ℝ), (∫ pts : Fin 3 → Torus d, f pts ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) = ∫ pts : Fin 3 → Torus d, f (pts ∘ (Equiv.swap 1 2)) ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) ) := by
        intro f
        have h_measure_preserving : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => pts ∘ (Equiv.swap 1 2)) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) (Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))) := by
          refine' ⟨ _, _ ⟩;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
            intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ hs, Fin.prod_univ_three ] ;
            · rw [ show ( fun pts : Fin 3 → Torus d => pts ∘ ⇑ ( Equiv.swap 1 2 ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 1 2 i ) ) from ?_ ];
              · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
              · ext; simp +decide [ Set.mem_univ_pi ] ;
                exact ⟨ fun h i => by simpa using h ( Equiv.swap 1 2 i ), fun h i => by simpa using h ( Equiv.swap 1 2 i ) ⟩;
            · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
            · exact MeasurableSet.univ_pi hs;
        rw [ ← h_measure_preserving.integral_comp ];
        constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 1 2 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts => pts ∘ ( Equiv.swap 1 2 );
          · exact h_measure_preserving.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;
      convert h_perm _ using 3 ; norm_num [ Equiv.swap_apply_def ];
      convert wedge_integral_1center p d hp0 hp1 hd hr |> Eq.symm using 3 ; norm_num [ dist_comm ];
      simp +decide [ dist_comm ]



open Classical MeasureTheory in
/-- Edge-fill integral for edge (0,2): ∫ A₁₃·F = (7r²)^d. By symmetry with mu_e_pow_eq. -/
lemma mu_e_pow_eq_02 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (7 * (matchRadius p d) ^ 2) ^ d := by
      convert mu_e_pow_eq p d hp0 hp1 hd hr using 1;
      -- The permutation is measure-preserving, so the integrals are equal.
      have h_measure_preserving : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => ![pts 0, pts 2, pts 1]) (Measure.pi fun _ => volume) (Measure.pi fun _ => volume) := by
        refine' ⟨ _, _ ⟩;
        · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 2; exact measurable_pi_apply 1 ] ;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ];
          · simp +decide [ Set.preimage, Fin.prod_univ_three ];
            simp +decide [ Fin.forall_fin_succ, Set.setOf_and ];
            erw [ show { a : Fin 3 → Torus d | a 0 ∈ s 0 } ∩ ( { a : Fin 3 → Torus d | a 2 ∈ s 1 } ∩ { a : Fin 3 → Torus d | a 1 ∈ s 2 } ) = ( Set.pi Set.univ fun i => if i = 0 then s 0 else if i = 1 then s 2 else s 1 ) by ext; simp +decide [ Fin.forall_fin_succ ] ; tauto ] ; erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
          · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 2; exact measurable_pi_apply 1 ] ;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_measure_preserving.integral_comp ];
      · simp +decide [ dist_comm ];
        simp +decide only [and_comm];
      · constructor;
        · exact fun x y h => by ext i; fin_cases i <;> have := congr_fun h 0 <;> have := congr_fun h 1 <;> have := congr_fun h 2 <;> aesop;
        · exact measurable_pi_iff.mpr fun i => by fin_cases i <;> [ exact measurable_pi_apply 0; exact measurable_pi_apply 2; exact measurable_pi_apply 1 ] ;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts => ![pts 0, pts 2, pts 1];
          · exact h_measure_preserving.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · intro pts; ext i; fin_cases i <;> rfl;



open Classical MeasureTheory in
/-- Edge-fill integral for edge (1,2): ∫ A₂₃·F = (7r²)^d. By symmetry with mu_e_pow_eq. -/
lemma mu_e_pow_eq_12 (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
      (if ∃ z : Torus d, dist (pts 0) z ≤ matchRadius p d ∧
                          dist (pts 1) z ≤ matchRadius p d ∧
                          dist (pts 2) z ≤ matchRadius p d
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (7 * (matchRadius p d) ^ 2) ^ d := by
      convert mu_e_pow_eq_02 p d hp0 hp1 hd hr using 1;
      -- By symmetry of the measure, we can swap the indices 0 and 1.
      have h_symm : MeasureTheory.MeasurePreserving (fun pts : Fin 3 → Torus d => fun i => pts (Equiv.swap 0 1 i)) (MeasureTheory.Measure.pi fun _ => MeasureTheory.volume) (MeasureTheory.Measure.pi fun _ => MeasureTheory.volume) := by
        refine' ⟨ _, _ ⟩;
        · fun_prop;
        · refine' ( MeasureTheory.Measure.pi_eq _ ).symm;
          intro s hs; erw [ MeasureTheory.Measure.map_apply ] ; simp +decide [ Fin.prod_univ_three ] ;
          · rw [ show ( fun pts : Fin 3 → Torus d => fun i => pts ( Equiv.swap 0 1 i ) ) ⁻¹' Set.univ.pi s = Set.pi Set.univ ( fun i => s ( Equiv.swap 0 1 i ) ) from ?_ ];
            · erw [ MeasureTheory.Measure.pi_pi ] ; simp +decide [ Fin.prod_univ_three ] ; ring!;
            · grind;
          · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
          · exact MeasurableSet.univ_pi hs;
      rw [ ← h_symm.integral_comp ] ; norm_num [ Equiv.swap_apply_def ] ; ring;
      · simp +decide [ and_comm, and_left_comm, and_assoc ];
      · constructor;
        · exact fun x y hxy => funext fun i => by simpa using congr_fun hxy ( Equiv.swap 0 1 i ) ;
        · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _;
        · intro s hs; rw [ Set.image_eq_preimage_of_inverse ];
          rotate_right;
          use fun pts i => pts ( Equiv.swap 0 1 i );
          · exact h_symm.measurable hs;
          · exact fun x => by ext i; fin_cases i <;> rfl;
          · exact fun x => by ext i; fin_cases i <;> rfl;



open Classical MeasureTheory in
/-- The centered third moment of edge indicators: ∫ (A₁₂-p)(A₁₃-p)(A₂₃-p) = γ - p³.
    Expands the product and uses gamma_pow_eq, wedge_integral, edge_integral. -/
lemma centered_edge_moment (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (3 * (matchRadius p d) ^ 2) ^ d - p ^ 3 := by
  -- Expand the integrand using the binomial theorem.
  have h_expand : ∀ pts : Fin 3 → Torus d, ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) - p) * ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) - p) * ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) - p) = (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) - p * ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) * (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0)) + p ^ 2 * ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0) + (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1 : ℝ) else 0)) - p ^ 3 := by
    intro pts; ring;
  rw [ MeasureTheory.integral_congr_ae ( Filter.Eventually.of_forall h_expand ), MeasureTheory.integral_sub, MeasureTheory.integral_add ];
  · rw [ MeasureTheory.integral_sub ];
    · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul ];
      rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
      · rw [ MeasureTheory.integral_add, MeasureTheory.integral_add ];
        · rw [ gamma_pow_eq, wedge_integral, wedge_integral_1center, wedge_integral_2center, edge_integral, edge_integral_02, edge_integral_12 ] ; norm_num ; ring;
          all_goals assumption;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
        · refine' MeasureTheory.Integrable.add _ _;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const;
          · refine' MeasureTheory.Integrable.indicator _ _;
            · norm_num [ MeasureTheory.integrable_const_iff ];
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num [ MeasureTheory.integrable_const_iff ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun a => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
          · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 1 ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
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
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
            · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
          · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun a => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun pts => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const;
      · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
    · refine' MeasureTheory.Integrable.const_mul _ _;
      refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
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
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun _ => 1;
        · norm_num [ MeasureTheory.integrable_const_iff ];
        · refine' Measurable.aestronglyMeasurable _;
          refine' Measurable.mul _ _;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
          · exact Measurable.ite ( measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 1 |> Measurable.prodMk <| measurable_pi_apply 2 ) ) measurable_const ) measurable_const measurable_const;
        · exact Filter.Eventually.of_forall fun x => by split_ifs <;> norm_num;
  · refine' MeasureTheory.Integrable.sub _ _;
    · refine' MeasureTheory.Integrable.mono' _ _ _;
      refine' fun _ => 1;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · refine' Measurable.aestronglyMeasurable _;
        apply_rules [ Measurable.mul, Measurable.ite, measurable_const ];
        · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
        · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
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
  · refine' MeasureTheory.Integrable.const_mul _ _;
    refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · exact measurableSet_le ( measurable_dist.comp ( measurable_pi_apply 0 |> Measurable.prodMk <| measurable_pi_apply 1 ) ) measurable_const;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num [ MeasureTheory.integrable_const_iff ];
      · exact measurableSet_le ( measurable_pi_apply 0 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
    · refine' MeasureTheory.Integrable.indicator _ _;
      · fun_prop;
      · exact measurableSet_le ( measurable_pi_apply 1 |> Measurable.dist <| measurable_pi_apply 2 ) measurable_const;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun pts => 1 + p * 3 + p ^ 2 * 3 + p ^ 3;
    · norm_num;
    · refine' Measurable.aestronglyMeasurable _;
      apply_rules [ Measurable.sub, Measurable.add, Measurable.mul, measurable_const ];
      all_goals apply_rules [ Measurable.ite, measurable_const ];
      all_goals exact measurableSet_le ( measurable_pi_apply _ |> Measurable.dist <| measurable_pi_apply _ ) measurable_const;
    · refine' Filter.Eventually.of_forall fun x => abs_le.mpr ⟨ _, _ ⟩ <;> split_ifs <;> nlinarith [ pow_pos hp0 3 ];
  · norm_num



open Classical MeasureTheory in
/-- Pointwise rewriting: (A₁₂-p)(A₁₃-p)(A₂₃-p)·F = A₁₂·A₁₃·A₂₃ - p(A₁₂·A₁₃ + A₁₂·A₂₃ + A₁₃·A₂₃)
    + p²(A₁₂·F + A₁₃·F + A₂₃·F) - p³·F.
    Uses wedge_implies_fill: if two edges sharing a vertex are present, then F=1,
    so wedge·F = wedge and triangle·F = triangle. -/
lemma integrand_fill_rewrite (d : ℕ) (r : ℝ) (p : ℝ) (hr0 : 0 ≤ r)
    (pts : Fin 3 → Torus d) :
    let A₁₂ := if dist (pts 0) (pts 1) ≤ r then (1:ℝ) else 0
    let A₁₃ := if dist (pts 0) (pts 2) ≤ r then (1:ℝ) else 0
    let A₂₃ := if dist (pts 1) (pts 2) ≤ r then (1:ℝ) else 0
    let F := if ∃ z : Torus d, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r
             then (1:ℝ) else 0
    (A₁₂ - p) * (A₁₃ - p) * (A₂₃ - p) * F =
    A₁₂ * A₁₃ * A₂₃
    - p * (A₁₂ * A₁₃ + A₁₂ * A₂₃ + A₁₃ * A₂₃)
    + p ^ 2 * (A₁₂ * F + A₁₃ * F + A₂₃ * F)
    - p ^ 3 * F := by
  by_cases h : ∃ z : Torus d, dist ( pts 0 ) z ≤ r ∧ dist ( pts 1 ) z ≤ r ∧ dist ( pts 2 ) z ≤ r <;> simp +decide [ h ] ; ring;
  · split_ifs <;> ring;
  · split_ifs <;> norm_num;
    · exact False.elim <| h <| wedge_implies_fill r hr0 _ _ _ ‹_› ‹_›;
    · exact False.elim <| h ⟨ pts 2, by assumption, by assumption, by simp +decide [ hr0 ] ⟩;
    · contrapose! h;
      use pts 1;
      simp_all +decide [ dist_comm ];
    · exact False.elim <| h <| wedge_implies_fill r hr0 _ _ _ ‹_› ‹_›



set_option maxHeartbeats 800000 in
open Classical MeasureTheory in
/-- **OQ-18 Rips refactor — Aristotle target.** Centered triple-edge moment times fill
    indicator. Under Rips, F = A₁₂·A₁₃·A₂₃, and the indicator identity X_e·A_e = (1-p)·A_e
    (since A_e ∈ {0,1}) gives
      ∫ (A₁₂-p)(A₁₃-p)(A₂₃-p) · F = (1-p)³ · q
    where q = fillingProb p d = (3r²)^d on r ≤ 1/4.

    Original statement (Čech existential nerve form, no longer correct): the indicator was
    `∃ z, ...` and the RHS was `(3r²)^d − 3p³ + 3p²·(7r²)^d − p³·q`. Under Rips, the indicator
    becomes the triangle product and the identity simplifies dramatically.

    See `my_theorems/oq18_math_audit.md` §"Centered edge identity" for the derivation. -/
lemma centered_edge_moment_fill (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 1 ≤ d)
    (hr : matchRadius p d ≤ 1/4) :
    (∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) - p) *
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then (1:ℝ) else 0) *
       (if dist (pts 0) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0) *
       (if dist (pts 1) (pts 2) ≤ matchRadius p d then (1:ℝ) else 0))
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d))))
    = (1 - p) ^ 3 * fillingProb p d := by
  -- OQ-18 Rips refactor — Aristotle target (job db044b91). Proof: pointwise identity
  -- X_e · A_e = (1-p) · A_e (since A_e is a 0/1 indicator), so the integrand reduces to
  -- (1-p)^3 · A_{12}·A_{13}·A_{23}, whose integral is (1-p)^3 · fillingProb.
  have h_fill : fillingProb p d = ∫ pts : Fin 3 → Torus d,
      ((if dist (pts 0) (pts 1) ≤ matchRadius p d then 1 else 0)
       * (if dist (pts 0) (pts 2) ≤ matchRadius p d then 1 else 0)
       * (if dist (pts 1) (pts 2) ≤ matchRadius p d then 1 else 0))
      ∂Measure.pi (fun _ => volume) := by
    simp [fillingProb]
  rw [h_fill, ← MeasureTheory.integral_const_mul]; congr; ext; split_ifs <;> ring

-- BEGIN dead-code old centered_edge_moment_fill proof body (commented out for Rips refactor)
example : True := by trivial
