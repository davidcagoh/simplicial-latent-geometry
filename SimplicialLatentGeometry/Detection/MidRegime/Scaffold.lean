import Mathlib
import SimplicialLatentGeometry.Core.Statistic
import SimplicialLatentGeometry.Core.Detection
import SimplicialLatentGeometry.DisjointTriangles
import SimplicialLatentGeometry.TorusIntegrals
import SimplicialLatentGeometry.Detection.Core.Types

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# `SimplicialLatentGeometry.Detection.MidRegime.Scaffold`

Extracted from `SimplicialDetection.lean` during the session-96 god-module split
(see `audits/simplicial-latent-geometry/README.md` and
`audits/REPORT-2026-05-23-simplicial-split.md`).
-/

open MeasureTheory ENNReal Finset Real Set


/-- **matchRadius_tendsto_half.** As dimension d → ∞, matchRadius p d → 1/2 from below.

    PROVIDED SOLUTION
    Step 1: matchRadius p d = p^(1/d)/2. Since p ∈ (0,1), p^(1/d) = exp(log(p)/d).
    Step 2: As d→∞, log(p)/d → 0, so exp(log(p)/d) → exp(0) = 1.
    Step 3: Therefore matchRadius p d → 1/2.
    Step 4: Use Filter.Tendsto.div_const and Real.tendsto_rpow_atTop or
            show p^(1/d) → 1 via Real.rpow_natCast and tendsto argument,
            then divide by 2. For d ≥ 1: matchRadius p d = p^(1/d)/2.
            p^(1/d) = Real.exp(Real.log p / d). As d → ∞, Real.log p / d → 0
            (since Real.log p < 0 for p ∈ (0,1)), so Real.exp(Real.log p / d) → 1.
            Therefore matchRadius p d = Real.exp(Real.log p / d) / 2 → 1/2. -/
lemma matchRadius_tendsto_half (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => matchRadius p d) Filter.atTop (nhds (1/2)) := by
  suffices h : Filter.Tendsto (fun d : ℕ => p ^ ((1:ℝ) / (d:ℝ)) / 2) Filter.atTop (nhds (1/2)) by
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with d hd
    simp [matchRadius, show d ≠ 0 by omega]
  apply Filter.Tendsto.div_const
  have h1 : Filter.Tendsto (fun d : ℕ => (1:ℝ) / (d:ℝ)) Filter.atTop (nhds 0) :=
    (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop)
  have h2 : Filter.Tendsto (fun _ : ℕ => p) Filter.atTop (nhds p) := tendsto_const_nhds
  have := Filter.Tendsto.rpow h2 h1 (Or.inl hp0.ne')
  rwa [Real.rpow_zero] at this



/-- **Filling probability closed form, Rips, mid regime `r ∈ (1/3, 1/2]`.** Sibling of
    `fillingProb_eq_low_r`. Delegates to `integral_triangle_eq_pow_mid` from
    `TorusIntegrals`. -/
lemma fillingProb_eq_mid_r (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1)
    (hr_lo : 1/3 < matchRadius p d) (hr_hi : matchRadius p d ≤ 1/2) (hd : 1 ≤ d) :
    fillingProb p d = (gammaMid (matchRadius p d)) ^ d := by
  unfold fillingProb
  exact integral_triangle_eq_pow_mid d hd (matchRadius p d) hr_lo hr_hi



/-- **matchRadius is eventually in the mid regime.** Since `matchRadius p d = p^{1/d}/2 → 1/2`
    as `d → ∞` (for fixed `p ∈ (0,1)`), for all sufficiently large `d` we have
    `matchRadius p d > 1/3` (and `≤ 1/2` always since `p^{1/d} ≤ 1`). -/
lemma matchRadius_eventually_mid (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d : ℕ in Filter.atTop, 1/3 < matchRadius p d ∧ matchRadius p d ≤ 1/2 := by
  -- p^(1/d) → p^0 = 1 as d → ∞ via continuity of x ↦ p^x at 0.
  have h_inv : Filter.Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have h_rpow : Filter.Tendsto (fun d : ℕ => p ^ ((1 : ℝ) / (d : ℝ))) Filter.atTop (nhds 1) := by
    have h_cont : ContinuousAt (fun x : ℝ => p ^ x) 0 :=
      Real.continuousAt_const_rpow (ne_of_gt hp0)
    have h0 : p ^ (0 : ℝ) = 1 := Real.rpow_zero p
    have := h_cont.tendsto.comp h_inv
    simpa [h0] using this
  -- eventually p^(1/d) > 2/3
  have h_gt : ∀ᶠ d : ℕ in Filter.atTop, (2 : ℝ) / 3 < p ^ ((1 : ℝ) / (d : ℝ)) :=
    h_rpow.eventually (eventually_gt_nhds (by norm_num : (2 : ℝ) / 3 < 1))
  filter_upwards [h_gt, Filter.eventually_ge_atTop (1 : ℕ)] with d hpd hd
  have hd_ne : d ≠ 0 := Nat.one_le_iff_ne_zero.mp hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h_le_one : p ^ ((1 : ℝ) / (d : ℝ)) ≤ 1 :=
    Real.rpow_le_one hp0.le hp1.le (by positivity)
  refine ⟨?_, ?_⟩
  · -- 1/3 < p^(1/d)/2
    have : matchRadius p d = p ^ ((1 : ℝ) / (d : ℝ)) / 2 := by
      unfold matchRadius; simp [hd_ne]
    rw [this]; linarith
  · -- p^(1/d)/2 ≤ 1/2
    have : matchRadius p d = p ^ ((1 : ℝ) / (d : ℝ)) / 2 := by
      unfold matchRadius; simp [hd_ne]
    rw [this]; linarith



/-
**The mid-regime gamma raised to the d-th power tends to `p^3`.**

    Math: `γ(p^{1/d}/2) = 3 p^{2/d} − 3 p^{1/d} + 1` (algebraic; see
    `gammaMid_of_matchRadius_form`). Taylor expansion at `1/d → 0`:
    `γ(r_d) = 1 + 3 (log p)/d + O(1/d²)`, so `d · log γ(r_d) → 3 log p`, hence
    `γ(r_d)^d → exp(3 log p) = p^3`.

    Aristotle target (analytic limit; uses Real.log_one_add_lt + Taylor).
-/
lemma gammaMid_matchRadius_pow_tendsto_pcubed (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => (gammaMid (matchRadius p d)) ^ d)
      Filter.atTop (nhds (p ^ 3)) := by
  -- Let $x = \log p$. We need to show $\lim_{d \to \infty} d \cdot (\gamma(r_d) - 1) = 3x$.
  set x := Real.log p
  set f := fun d : ℕ => d * (gammaMid (matchRadius p d) - 1)
  have h_lim : Filter.Tendsto f Filter.atTop (nhds (3 * x)) := by
    -- We'll use the fact that $gammaMid(r_d) = 3p^{2/d} - 3p^{1/d} + 1$.
    have h_gammaMid : ∀ d : ℕ, d ≠ 0 → gammaMid (matchRadius p d) = 3 * p^(2 / (d : ℝ)) - 3 * p^(1 / (d : ℝ)) + 1 := by
      intro d hd_ne; unfold matchRadius; norm_num [ hd_ne ] ; ring;
      rw [ Real.rpow_mul hp0.le ] ; norm_num;
    -- We'll use the fact that $d \cdot (p^{2/d} - 1)$ and $d \cdot (p^{1/d} - 1)$ tend to $2 \log p$ and $\log p$ respectively as $d \to \infty$.
    have h_lim : Filter.Tendsto (fun d : ℕ => d * (p^(2 / (d : ℝ)) - 1)) Filter.atTop (nhds (2 * x)) ∧ Filter.Tendsto (fun d : ℕ => d * (p^(1 / (d : ℝ)) - 1)) Filter.atTop (nhds (x)) := by
      have h_lim : Filter.Tendsto (fun t : ℝ => t⁻¹ * (p^t - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log p)) := by
        simpa [ div_eq_inv_mul, Real.rpow_def_of_pos hp0 ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( HasDerivAt.exp ( HasDerivAt.const_mul ( Real.log p ) ( hasDerivAt_id 0 ) ) ) ( hasDerivAt_const 0 1 ) );
      constructor;
      · have := h_lim.comp ( show Filter.Tendsto ( fun d : ℕ => 2 / ( d : ℝ ) ) Filter.atTop ( nhdsWithin 0 ( Set.Ioi 0 ) ) from ?_ );
        · convert this.const_mul 2 using 2 ; norm_num ; ring;
        · rw [ tendsto_nhdsWithin_iff ];
          exact ⟨ tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by norm_num; positivity ⟩ ⟩;
      · convert h_lim.comp ( show Filter.Tendsto ( fun d : ℕ => ( d : ℝ ) ⁻¹ ) Filter.atTop ( nhdsWithin 0 ( Set.Ioi 0 ) ) from ?_ ) using 2;
        · norm_num [ mul_comm ];
        · rw [ tendsto_nhdsWithin_iff ];
          exact ⟨ tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by simpa using hn ⟩ ⟩;
    convert Filter.Tendsto.congr' _ ( h_lim.1.const_mul 3 |> Filter.Tendsto.sub <| h_lim.2.const_mul 3 ) using 2 <;> norm_num ; ring;
    filter_upwards [ Filter.eventually_ne_atTop 0 ] with d hd using by rw [ show f d = ↑d * ( gammaMid ( matchRadius p d ) - 1 ) by rfl, h_gammaMid d hd ] ; ring;
  -- Using the continuity of the exponential function and the fact that $f(d) \to 3x$, we get $\lim_{d \to \infty} \exp(f(d)) = \exp(3x)$.
  have h_exp : Filter.Tendsto (fun d : ℕ => Real.exp (d * Real.log (gammaMid (matchRadius p d)))) Filter.atTop (nhds (Real.exp (3 * x))) := by
    refine' Real.continuous_exp.continuousAt.tendsto.comp _;
    have h_log : Filter.Tendsto (fun d : ℕ => Real.log (1 + (gammaMid (matchRadius p d) - 1)) / (gammaMid (matchRadius p d) - 1)) Filter.atTop (nhds 1) := by
      have h_log : Filter.Tendsto (fun y : ℝ => Real.log (1 + y) / y) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
        simpa [ div_eq_inv_mul ] using Real.hasDerivAt_log one_ne_zero |> HasDerivAt.tendsto_slope_zero;
      refine h_log.comp <| Filter.tendsto_inf.mpr ⟨ ?_, ?_ ⟩;
      · have := h_lim.div_atTop tendsto_natCast_atTop_atTop;
        exact this.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with d hd; aesop );
      · simp +zetaDelta at *;
        exact Filter.eventually_atTop.mp ( h_lim.eventually_ne ( show ( 3 * Real.log p ) ≠ 0 by linarith [ Real.log_le_sub_one_of_pos hp0 ] ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ by specialize hN n hn; aesop ⟩;
    have := h_log.mul h_lim;
    simp +zetaDelta at *;
    refine' this.congr' ( by filter_upwards [ h_log.eventually_ne one_ne_zero ] with d hd using by rw [ div_mul_eq_mul_div, div_eq_iff ( by aesop ) ] ; ring );
  convert h_exp.congr' _ using 2;
  · rw [ mul_comm, Real.exp_mul, Real.exp_log ] <;> norm_cast;
  · have h_pos : ∀ᶠ d in Filter.atTop, 0 < gammaMid (matchRadius p d) := by
      have h_pos : Filter.Tendsto (fun d : ℕ => matchRadius p d) Filter.atTop (nhds (1 / 2)) := by
        convert matchRadius_tendsto_half p hp0 hp1 using 1;
      exact h_pos.eventually ( lt_mem_nhds <| show 1 / 2 > 1 / 3 by norm_num ) |> fun h => h.mono fun d hd => by unfold gammaMid; nlinarith;
    filter_upwards [ h_pos ] with d hd using by rw [ Real.exp_nat_mul, Real.exp_log hd ] ;



/-- **OQ-18 Rips asymptotic.** Under Rips on the sup-norm torus with matched p ∈ (0,1)
    fixed, `fillingProb p d → p^3` as `d → ∞`. Replaces the Čech-era false statements
    `fillingProb_tendsto_one` / `fillingProb_tendsto_zero`.

    Proof chain:
    1. For sufficiently large `d`, `matchRadius p d ∈ (1/3, 1/2]` (`matchRadius_eventually_mid`).
    2. In that regime, `fillingProb p d = γ(r_d)^d` (`fillingProb_eq_mid_r`).
    3. `γ(r_d)^d → p^3` (`gammaMid_matchRadius_pow_tendsto_pcubed`). -/
lemma fillingProb_tendsto_pcubed (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => fillingProb p d) Filter.atTop (nhds (p^3)) := by
  -- Replace `γ(r_d)^d` with `fillingProb p d` eventually, then transport the limit.
  have h_eq : ∀ᶠ d : ℕ in Filter.atTop,
      (gammaMid (matchRadius p d)) ^ d = fillingProb p d := by
    filter_upwards [matchRadius_eventually_mid p hp0 hp1,
                    Filter.eventually_ge_atTop (1 : ℕ)] with d ⟨hlo, hhi⟩ hd
    exact (fillingProb_eq_mid_r p d hp0 hp1 hlo hhi hd).symm
  exact (gammaMid_matchRadius_pow_tendsto_pcubed p hp0 hp1).congr' h_eq



/-
Bound the absolute value of the three-edge-product integral by 1 on a
product of Haar probability measures on `Torus d`. Auxiliary for DCT-based
limit proofs.
-/
open MeasureTheory in
lemma edgeProduct_integral_bounded' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) :
    |∫ pts : Fin 3 → Torus d,
        (let r := matchRadius p d
         let x₁ := pts 0; let x₂ := pts 1; let x₃ := pts 2
         let e₁₂ := if dist x₁ x₂ ≤ r then (1 : ℝ) - p else -p
         let e₁₃ := if dist x₁ x₃ ≤ r then (1 : ℝ) - p else -p
         let e₂₃ := if dist x₂ x₃ ≤ r then (1 : ℝ) - p else -p
         e₁₂ * e₁₃ * e₂₃)
      ∂MeasureTheory.Measure.pi (fun _ : Fin 3 => (volume : Measure (Torus d)))| ≤ 1 := by
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ( Fin 3 → Torus d ) → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun _ => 1;
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _;
  · exact MeasureTheory.integrable_const _;
  · filter_upwards [ ] with x;
    norm_num [ abs_le ];
    split_ifs <;> constructor <;> nlinarith [ mul_nonneg hp0.le ( sq_nonneg p ), mul_nonneg hp0.le ( sq_nonneg ( 1 - p ) ) ];
  · norm_num [ MeasureTheory.Measure.pi_univ ]
