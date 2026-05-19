import Mathlib
import SimplicialLatentGeometry.Geometry.Common

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Geometry / Sphere — $S^{d-1}$ Čech instance (Paper 2)

The second concrete instance of `HomogeneousGeometricModel`. Implements detection on the
unit sphere $S^{d-1} \subset \mathbb{R}^d$ with uniform measure, using Čech fill (existential
common-ball) rather than Rips clique.

Strategic context (see `wiki/decisions.md` session-63 entries + local
`my_theorems/paper2_sphere_scoping.md`):

* On $\ell_\infty$ torus, Helly-2 collapses Čech to Rips and gives no dimensional barrier
  in the matched fixed-$p$ regime (Paper 1: $\text{geomCov} \to p^3(1-p)^3 > 0$).
* On $S^{d-1}$, Helly-$d$ preserves the Čech-Rips gap; concentration of measure forces
  caps to nearly hemispheres at matched $p$, but the existential Čech fill saturates
  ($q_{\text{Čech}} \to 1$) while Rips fill collapses ($q_{\text{Rips}} \to p^3$).
* The signal $\text{geomCov}_{\text{Čech}} \sim p^3 (1 - q_{\text{Čech}})$ vanishes
  super-exponentially: $1 - q_{\text{Čech}} \sim (3 z_p^2 / d)^{(d-2)/2}$ via the joint
  Gram-entry density $\propto (\det G)^{(d-4)/2}$ singularity at $\det G = 0$.
* Detection threshold: $d^*(n, p) = 3 \log n / \log\log n$, sub-logarithmic.

## Layout (this file)

* `SphereSetting` — dimension index `d : ℕ`, $d \ge 2$.
* `uniformOnSphere d` — uniform probability measure on $S^{d-1}$ (via Haar / $SO(d)$).
* `sphereEdge` — pairwise inner-product threshold.
* `matchedCap p d` — the cap half-angle realizing edge probability $p$.
* `sphereCech` — Čech fill (existential common cap).
* Aristotle targets: cap volume closed form, Gram-density tail asymptotic, $\text{geomCov}$
  closed form, and the `HomogeneousGeometricModel` instance hookup.

## Status

S1 skeleton (Phase A6 in the OQ-18 plan). All proof bodies are `sorry` pending
Aristotle dispatch. The asymptotic claims are stated against the math-precheck verdict
(session 63) and not the original audit's $\log n$ headline.
-/

namespace SphereGeometry

open MeasureTheory

/-! ## Point space: unit sphere in $\mathbb{R}^d$ -/

/-- The unit sphere $S^{d-1} \subset \mathbb{R}^d$, as the subtype carried by mathlib's
    `Metric.sphere`. Concretised 2026-05-19 to use the standard mathlib sphere instead of
    `{x // ‖x‖ = 1}` so that the radial-pushforward `Measure.toSphere` (HaarToSphere.lean)
    applies directly. -/
abbrev SpherePoint (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- Measurable-space structure inherited from `EuclideanSpace`. -/
instance (d : ℕ) : MeasurableSpace (SpherePoint d) := Subtype.instMeasurableSpace

/-- Uniform probability measure on $S^{d-1}$. Built from the standard Lebesgue measure on
    `EuclideanSpace ℝ (Fin d)` via mathlib's `Measure.toSphere` (radial pushforward; see
    `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`), then normalized to total
    mass 1. For `d ≤ 1` this is the zero measure (the underlying `toSphere` vanishes,
    so the normalization factor `μ univ⁻¹` is `⊤⁻¹ = 0`); consumers only quantify over
    `ValidRegime p d` which forces `5 ≤ d`. -/
noncomputable def uniformOnSphere (d : ℕ) : Measure (SpherePoint d) :=
  let μ : Measure (SpherePoint d) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
  (μ Set.univ)⁻¹ • μ

/-- The uniform measure is a probability measure whenever the sphere is non-trivial,
    i.e. `2 ≤ d`. Derives from the finite-measure instance on `Measure.toSphere` plus
    `toSphere_apply_univ`'s non-zero ball volume formula (`dim * vol(ball 0 1)`). -/
instance uniformOnSphere_isProb (d : ℕ) [hd : Fact (2 ≤ d)] :
    IsProbabilityMeasure (uniformOnSphere d) := by
  constructor
  unfold uniformOnSphere
  have h_dim_pos : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    exact lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hd.out
  haveI h_nontriv : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.finrank_pos_iff.mp h_dim_pos
  have h_ne : (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have h_finite :
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ ≠ ⊤ :=
    (measure_lt_top _ _).ne
  have h_pos :
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ ≠ 0 := by
    rwa [Measure.measure_univ_ne_zero]
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h_pos h_finite

/-- Uniform-sphere as `Fact (2 ≤ d)` is the natural form for typeclass synthesis; expose a
    direct version with explicit hypothesis for backward compatibility with the rest of
    this file (which threads `hd : 2 ≤ d` as an ordinary argument). -/
lemma uniformOnSphere_isProb' (d : ℕ) (hd : 2 ≤ d) :
    IsProbabilityMeasure (uniformOnSphere d) :=
  @uniformOnSphere_isProb d ⟨hd⟩

/-! ## Edge and fill predicates -/

/-- Two points on the sphere are within angular distance $\theta$ iff their Euclidean
    inner product is at least $\cos\theta$. We parameterize by `r := cos θ` directly. -/
def sphereEdge {d : ℕ} (r : ℝ) (x y : SpherePoint d) : Prop :=
  inner ℝ x.val y.val ≥ r

/-- Čech fill at scale `r`: three points lie in a common spherical cap of half-angle
    `arccos r`, i.e., there exists a center `z ∈ S^{d-1}` with all three inner products
    `⟨z, x_i⟩ ≥ r`. -/
def sphereCechFill {d : ℕ} (r : ℝ) (x₁ x₂ x₃ : SpherePoint d) : Prop :=
  ∃ z : SpherePoint d,
    inner ℝ z.val x₁.val ≥ r ∧ inner ℝ z.val x₂.val ≥ r ∧ inner ℝ z.val x₃.val ≥ r

/-! ## Cap probability — primitive quantity

The uniform probability that a single point lies in a spherical cap of cosine threshold
`r ∈ [-1, 1]` centred at a fixed pole. In dimension `d ≥ 2` this is
`(1/2) · I_{1-r²}((d-1)/2, 1/2)` when `r ≥ 0` by the standard incomplete-beta formula
(Li 2011, Eq. (3)). Axiomatized here pending a clean Mathlib formalization; the
constructive integral against `uniformOnSphere` is the natural body. -/
axiom capProb (d : ℕ) (r : ℝ) : ℝ

/-- Cap probability is in `[0, 1]` for any threshold and dimension. -/
axiom capProb_mem_unitInterval (d : ℕ) (r : ℝ) : 0 ≤ capProb d r ∧ capProb d r ≤ 1

/-- Monotone in the threshold: a higher cosine threshold gives a smaller cap. -/
axiom capProb_antitone (d : ℕ) : Antitone (capProb d)

/-- Endpoints. `r = -1` covers the whole sphere; `r = 1` is the pole. -/
axiom capProb_neg_one (d : ℕ) (hd : 2 ≤ d) : capProb d (-1) = 1
axiom capProb_one (d : ℕ) (hd : 2 ≤ d) : capProb d 1 = 0

/-- Continuity in the threshold (for `d ≥ 2`). Needed to invert via IVT. -/
axiom capProb_continuous (d : ℕ) (hd : 2 ≤ d) : Continuous (capProb d)

/-! ## Matched threshold

For two iid uniform points on $S^{d-1}$, the marginal edge probability at threshold
`r` is `2 · capProb d r · (1/2) = capProb d r` (rotate the first point to the pole).
The matched threshold `matchedCos p d` is the unique `r ∈ [-1, 1]` with
`capProb d r = p`. Existence + uniqueness from continuity + strict monotonicity. -/

/-- The matched cosine threshold realizing edge probability `p` in dimension `d`.
    Defined via classical choice on the existence axiom `matchedCos_exists`. -/
noncomputable def matchedCos (p : ℝ) (d : ℕ) : ℝ :=
  Classical.epsilon (fun r : ℝ => -1 ≤ r ∧ r ≤ 1 ∧ capProb d r = p)

/-- Existence of a matched threshold. Follows from IVT applied to the continuous
    monotone `capProb d` between values `1` at `-1` and `0` at `1`. -/
axiom matchedCos_exists (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 2 ≤ d) :
    ∃ r : ℝ, -1 ≤ r ∧ r ≤ 1 ∧ capProb d r = p

/-- The specification realized by `matchedCos`. -/
lemma matchedCos_spec (p : ℝ) (d : ℕ) (hp0 : 0 < p) (hp1 : p < 1) (hd : 2 ≤ d) :
    -1 ≤ matchedCos p d ∧ matchedCos p d ≤ 1 ∧ capProb d (matchedCos p d) = p := by
  unfold matchedCos
  exact Classical.epsilon_spec (matchedCos_exists p d hp0 hp1 hd)

/-- Asymptotic: $\text{matchedCos}(p, d) \sim z_p / \sqrt{d}$ as $d \to \infty$,
    where $z_p = \Phi^{-1}(1-p)$ is the standard normal quantile. Stated against
    an axiomatized normal-quantile constant `normalQuantile p`. -/
axiom normalQuantile : ℝ → ℝ

/-- **Cap-CLT + normal-quantile inversion (auxiliary axiom).**
    The Poincaré / CLT limit for spherical caps says that as $d \to \infty$,
    the spherical cap probability at cosine threshold $t / \sqrt{d}$ converges
    to $\Phi(-t)$. Inverting this uniformly: if a sequence of thresholds
    $r_d \in [-1, 1]$ satisfies `capProb d (r d) = p` for all sufficiently large
    $d$, then $\sqrt{d} \cdot r_d \to \Phi^{-1}(1 - p) = $ `normalQuantile (1 - p)`.
    Axiomatized pending Mathlib formalization of the CLT for spherical caps
    (Li 2011 / Poincaré limit) + continuous inversion of the normal CDF. -/
axiom capCLT_matched_inversion (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (r : ℕ → ℝ) (hr : ∀ᶠ d in Filter.atTop, capProb d (r d) = p) :
    Filter.Tendsto (fun d : ℕ => Real.sqrt d * r d) Filter.atTop
      (nhds (normalQuantile (1 - p)))

lemma matchedCos_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => Real.sqrt d * matchedCos p d) Filter.atTop
      (nhds (normalQuantile (1 - p))) := by
  apply capCLT_matched_inversion p hp0 hp1
  rw [Filter.eventually_atTop]
  exact ⟨2, fun d hd => (matchedCos_spec p d hp0 hp1 hd).2.2⟩

/-! ## Triangle (Čech-fill) probability and the asymptotic headline

The triangle (Rips/Čech) probabilities are axiomatized as functions of `(p, d)`; their
defining integral expressions live in the moonshot proof and are not yet ported. -/

/-- $q_{\text{Čech}}(p, d) = \Pr[\text{sphereCechFill at threshold matchedCos } p d]$.
    Defined as the measure (under the iid product of `uniformOnSphere d` on three points)
    of the Čech-fill event at the matched cosine threshold. Concretised 2026-05-19. -/
noncomputable def cechFillProb (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchedCos p d
  let ν := (uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))
  (ν {triple : SpherePoint d × SpherePoint d × SpherePoint d |
    sphereCechFill r triple.1 triple.2.1 triple.2.2}).toReal

/-- Rips clique probability under matched edge $p$: probability that all three pairwise
    edges are present at the matched cosine threshold. -/
noncomputable def ripsFillProb (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchedCos p d
  let ν := (uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))
  (ν {triple : SpherePoint d × SpherePoint d × SpherePoint d |
    sphereEdge r triple.1 triple.2.1 ∧
    sphereEdge r triple.1 triple.2.2 ∧
    sphereEdge r triple.2.1 triple.2.2}).toReal

open Classical in
/-- Geometric covariance under Čech fill on the sphere:
    `E[(A₁₂−p)(A₁₃−p)(A₂₃−p)(F^{Čech}−q_{Čech})]`. Closed form follows the four-moment
    decomposition `q_Rips(1−q_Čech) + 3p²(β−p)` with `β = E[A₁₂ · F^{Čech}]`. -/
noncomputable def geomCovCech (p : ℝ) (d : ℕ) : ℝ :=
  let r := matchedCos p d
  let q := cechFillProb p d
  let ν := (uniformOnSphere d).prod ((uniformOnSphere d).prod (uniformOnSphere d))
  ∫ triple, ((if sphereEdge r triple.1 triple.2.1 then (1:ℝ) - p else -p) *
             (if sphereEdge r triple.1 triple.2.2 then (1:ℝ) - p else -p) *
             (if sphereEdge r triple.2.1 triple.2.2 then (1:ℝ) - p else -p) *
             (if sphereCechFill r triple.1 triple.2.1 triple.2.2
                then (1:ℝ) - q else -q)) ∂ν

/-! ### Structural axioms for Paper 2 sphere asymptotics

The Paper 2 headlines (`cechFillProb_tail_asymptotic` and `geomCovCech_asymptotic`)
are derived from a small set of **named load-bearing structural axioms** capturing
the deep moonshot content: Wishart pushforward, joint Gram density, surface
concentration, algebraic decomposition. Each axiom is documented with its
mathematical content + reference to `paper2_sphere_scoping.md`. Future work
removes these by porting Wishart/incomplete-Beta machinery to Mathlib.

This architecture is preferred over bare-fact axioms (`cechFillProb_tail_asymptotic`
as axiom) because:
1. The audit trail names WHICH math content is unproven (Gram density, etc.)
   rather than just "the headline."
2. Multiple headlines derive from a common axiom layer (DRY).
3. Future ports replace axioms in dependency order, with each removal directly
   measurable. -/

/-- **Axiom (Wishart-derived Gram density tail).** For three iid uniform points
    on $S^{d-1}$ with $d \ge 5$, the joint density of the three pairwise inner
    products $(y_{12}, y_{13}, y_{23})$ is proportional to $(\det G)^{(d-4)/2}$
    where $G$ is the $3 \times 3$ Gram matrix. The vanishing at the boundary
    $\det G = 0$ forces a super-exponential tail: for the matched cosine
    threshold $r_d = $ `matchedCos p d`, the complement triple-cover probability
    is bounded above by `(3 (normalQuantile (1 - p))^2 / d)^((d-2)/2)` eventually.

    See `paper2_sphere_scoping.md` § "Tail computation" + § "Tightened rate analysis". -/
axiom cechFillProb_compl_le_gram_tail (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ d : ℕ in Filter.atTop,
      1 - cechFillProb p d ≤
        ((3 * (normalQuantile (1 - p))^2) / (d : ℝ))^(((d : ℝ) - 2) / 2)

/-- **Axiom (cechFillProb ≤ 1).** Each `cechFillProb p d` is a probability (sub-probability
    when `uniformOnSphere d` is not yet known to be a probability measure for `d ≤ 1`).
    Provable in principle now that `cechFillProb` is concrete — kept axiomatic pending the
    Subprobability-measure bound on the product (`(c⁻¹ * c) ≤ 1` cascade through three
    product factors), which is a non-trivial ENNReal arithmetic chain. -/
axiom cechFillProb_le_one (p : ℝ) (d : ℕ) : cechFillProb p d ≤ 1

/-- **Axiom (Rips-Čech algebraic decomposition, sphere).** The geometric covariance
    on the sphere admits the algebraic decomposition
    $\text{geomCov}_{\text{Čech}} = q_{\text{Rips}} \cdot (1 - q_{\text{Čech}})
       + 3 p^2 \cdot (\beta - p)$
    where $\beta := \mathbb E[A_{12} \cdot F^{\text{Čech}}]$ is the
    wedge-Čech joint moment. Combined with surface-concentration ($\beta - p
    \to -p \cdot c_d \cdot (1 - q_{\text{Čech}})$ with $c_d \to 0$ super-exp,
    SLOWER than $1 - q_{\text{Čech}}$) and Rips clique convergence
    ($q_{\text{Rips}} \to p^3$ on sphere), this gives
    $\text{geomCov}_{\text{Čech}} / (p^3 (1 - q_{\text{Čech}})) \to 1$.

    Stated here as a black-box ratio convergence; future work derives this from
    the Wishart density axiom + sphere clique probability axioms.

    See `paper2_sphere_scoping.md` § "Surface-concentration argument" +
    § "Sub-leading rate of $c_d$". -/
axiom geomCovCech_decomp_ratio_tendsto (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geomCovCech p d / (p ^ 3 * (1 - cechFillProb p d)))
      Filter.atTop (nhds 1)

/-- **Auxiliary fact.** For any $p \in (0, 1)$, the asymptotic upper bound
    `(3 (normalQuantile (1 - p))^2 / d)^((d-2)/2) → 0` as $d \to \infty$.
    Pure analytic statement — base tends to 0, exponent tends to $\infty$. -/
private lemma gram_tail_bound_tendsto_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto
      (fun d : ℕ => ((3 * (normalQuantile (1 - p))^2) / (d : ℝ))^(((d : ℝ) - 2) / 2))
      Filter.atTop (nhds 0) := by
  -- Strategy: let `a = 3 * (normalQuantile (1-p))^2 ≥ 0`. Squeeze the function `f d :=
  -- (a/d)^((d-2)/2)` between `0` and `a/d`. For `d ≥ a + 1` and `d ≥ 4` we have
  -- `0 ≤ a/d ≤ 1` and `1 ≤ (d-2)/2`, so by `Real.rpow_le_rpow_of_exponent_ge` (which
  -- requires `0 < base`, handled via case split on `a/d = 0`) the rpow at the larger
  -- exponent is dominated by the rpow at exponent 1, i.e. by `a/d` itself. Then
  -- `a/d → 0`, and the lower bound `0` is immediate from `Real.rpow_nonneg`.
  set a : ℝ := 3 * (normalQuantile (1 - p))^2 with ha_def
  have ha_nn : 0 ≤ a := by
    have : (0 : ℝ) ≤ 3 * (normalQuantile (1 - p))^2 := by positivity
    exact this
  -- Bound `a/d → 0`.
  have h_bd_to_zero : Filter.Tendsto (fun d : ℕ => a / (d : ℝ)) Filter.atTop (nhds 0) := by
    have h_inv : Filter.Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h_eq : (fun d : ℕ => a / (d : ℝ)) = (fun d : ℕ => a * (1 / (d : ℝ))) := by
      funext d; ring
    rw [h_eq, show (0 : ℝ) = a * 0 by ring]
    exact h_inv.const_mul a
  -- Squeeze.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_bd_to_zero
  · -- Lower bound: `0 ≤ (a/d)^((d-2)/2)`.
    refine Filter.Eventually.of_forall fun d => ?_
    exact Real.rpow_nonneg (by positivity) _
  · -- Upper bound: `(a/d)^((d-2)/2) ≤ a/d` eventually.
    have h_large_a : ∀ᶠ d : ℕ in Filter.atTop, a + 1 ≤ (d : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (a + 1)
    have h_large_4 : ∀ᶠ d : ℕ in Filter.atTop, 4 ≤ d := Filter.eventually_ge_atTop 4
    filter_upwards [h_large_a, h_large_4] with d hd_a hd_4
    have hd4 : (4 : ℝ) ≤ d := by exact_mod_cast hd_4
    have hd_pos : (0 : ℝ) < d := by linarith
    have h_ad_nn : 0 ≤ a / (d : ℝ) := div_nonneg ha_nn hd_pos.le
    have h_ad_le_one : a / (d : ℝ) ≤ 1 := by
      rw [div_le_one hd_pos]; linarith
    have h_exp_ge_one : (1 : ℝ) ≤ ((d : ℝ) - 2) / 2 := by linarith
    by_cases h_ad_zero : a / (d : ℝ) = 0
    · rw [h_ad_zero]
      rw [Real.zero_rpow (by linarith : ((d : ℝ) - 2) / 2 ≠ 0)]
    · have h_ad_pos : 0 < a / (d : ℝ) := h_ad_nn.lt_of_ne (Ne.symm h_ad_zero)
      have := Real.rpow_le_rpow_of_exponent_ge h_ad_pos h_ad_le_one h_exp_ge_one
      simpa using this

/-- **Tail asymptotic (Paper 2 headline part 1).** Derived from the Wishart
    Gram-density tail axiom + squeeze: $0 \le 1 - q_{\text{Čech}} \le $ Gram tail bound,
    and Gram tail bound $\to 0$. -/
theorem cechFillProb_tail_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => cechFillProb p d) Filter.atTop (nhds 1) := by
  -- Strategy: show `1 - cechFillProb p d → 0`, then transport via `1 - (1 - x) = x`.
  have h_compl_to_zero :
      Filter.Tendsto (fun d : ℕ => 1 - cechFillProb p d) Filter.atTop (nhds 0) := by
    -- Squeeze: 0 ≤ 1 - q ≤ Gram-tail bound, where bound → 0.
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (gram_tail_bound_tendsto_zero p hp0 hp1)
    · -- 0 ≤ 1 - cechFillProb p d eventually (always, by cechFillProb_le_one)
      exact Filter.Eventually.of_forall (fun d => by
        have := cechFillProb_le_one p d
        linarith)
    · exact cechFillProb_compl_le_gram_tail p hp0 hp1
  -- Now `1 - q → 0` ⇒ `q → 1`.
  have := (tendsto_const_nhds (x := (1:ℝ))).sub h_compl_to_zero
  simpa using this

/-- **GeomCov asymptotic (Paper 2 headline part 2).** Direct from the
    `geomCovCech_decomp_ratio_tendsto` structural axiom (which encodes the
    surface-concentration + algebraic decomposition). -/
theorem geomCovCech_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geomCovCech p d / (p ^ 3 * (1 - cechFillProb p d)))
      Filter.atTop (nhds 1) :=
  geomCovCech_decomp_ratio_tendsto p hp0 hp1

/-! ## CechSphereModel instance -/

/-- Validity regime for the sphere instance: $d \ge 5$ (so the Gram density vanishes at the
    boundary $\det G = 0$, enabling the super-exponential tail), $p \in (0, 1)$. -/
def SphereValidRegime (p : ℝ) (d : ℕ) : Prop :=
  0 < p ∧ p < 1 ∧ 5 ≤ d

/-- The sphere Čech instance of `CechSphereModel ℕ`. Wires the asymptotic theorem
    `geomCovCech_asymptotic` as the typeclass axiom.

    Note: this is **not** an instance of `HomogeneousGeometricModel` — the Rips closed form
    fails under Čech (see session-65 decision in `wiki/decisions.md`). The split typeclass
    architecture in `Geometry/Common.lean` keeps Rips and Čech models distinct. -/
noncomputable instance : CechSphereModel ℕ where
  Point d := SpherePoint d
  pointSpace _ := inferInstance
  μ d := uniformOnSphere d
  WellFormed d := 2 ≤ d
  isProb d hd := uniformOnSphere_isProb' d hd
  edge _ r x y := sphereEdge r x y
  matchR p d := matchedCos p d
  cechFillProb p d := cechFillProb p d
  geomCovCech p d := geomCovCech p d
  ValidRegime p d := SphereValidRegime p d
  geomCov_asymptotic := by
    intro p hp0 hp1
    exact geomCovCech_asymptotic p hp0 hp1

/-! ## Aristotle dispatch plan (S2–S6)

Phase | Target | Statement |
|---|---|---|
| S2 | Cap volume closed form | `volume(spherical_cap θ) = (1/2) · I_{sin² θ}((d-1)/2, 1/2)` |
| S3 | `matchedCos` exists and unique | inverse function of cap-volume formula |
| S4 | Joint Gram density | `f(y_{12}, y_{13}, y_{23}) ∝ (det G)^{(d-4)/2}` |
| S5 | Tail asymptotic | `Pr[det G ≤ t] ~ t^{(d-2)/2}` |
| S6 | GeomCov closed form | the four-moment decomposition + leading-order $p^3(1-q_{\text{Čech}})$ |

Each is an Aristotle job; expected difficulty moderate to high. References:
Wendel 1962, Anderson-Cook 1986, Li 2011 (cap formula), Reitzner 2010 (random polytopes).
-/

end SphereGeometry
