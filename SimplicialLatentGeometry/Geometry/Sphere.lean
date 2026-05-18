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

/-- The unit sphere $S^{d-1} \subset \mathbb{R}^d$ as a `Subtype` of vectors of norm 1. -/
abbrev SpherePoint (d : ℕ) := { x : EuclideanSpace ℝ (Fin d) // ‖x‖ = 1 }

/-- Measurable-space structure inherited from `EuclideanSpace`. -/
instance (d : ℕ) : MeasurableSpace (SpherePoint d) := Subtype.instMeasurableSpace

/-- Uniform probability measure on $S^{d-1}$. The canonical construction is the
    pushforward of Haar measure on $SO(d)$ acting on a basepoint, equivalently the
    normalized $(d-1)$-Hausdorff measure. Mathlib coverage of these is partial as of
    the current toolchain; we axiomatize existence + the `IsProbabilityMeasure` witness
    here pending a clean Mathlib formalization. The asymptotic theorems downstream
    quantify only over `ValidRegime p d` (which forces `5 ≤ d`), so the choice of
    representative measure for `d ≤ 1` (where `SpherePoint d` is empty or trivial)
    does not affect any consumer. -/
axiom uniformOnSphere (d : ℕ) : Measure (SpherePoint d)

/-- The uniform measure is a probability measure whenever the sphere is non-trivial,
    i.e. `2 ≤ d`. Axiomatized alongside `uniformOnSphere`. -/
axiom uniformOnSphere_isProb (d : ℕ) (hd : 2 ≤ d) : IsProbabilityMeasure (uniformOnSphere d)

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

/-- $q_{\text{Čech}}(p, d) = \Pr[\text{sphereCechFill at threshold matchedCos } p d]$. -/
axiom cechFillProb (p : ℝ) (d : ℕ) : ℝ

/-- Rips clique probability under matched edge $p$. -/
axiom ripsFillProb (p : ℝ) (d : ℕ) : ℝ

/-- Geometric covariance under Čech fill on the sphere:
    `E[(A₁₂−p)(A₁₃−p)(A₂₃−p)(F^{Čech}−q_{Čech})]`. Closed form follows the four-moment
    decomposition `q_Rips(1−q_Čech) + 3p²(β−p)` with `β = E[A₁₂ · F^{Čech}]`. -/
axiom geomCovCech (p : ℝ) (d : ℕ) : ℝ

/-- **Tail asymptotic (Paper 2 headline part 1).**
    $1 - q_{\text{Čech}}(p, d) \sim (3 z_p^2 / d)^{(d-2)/2}$ as $d \to \infty$ at fixed $p$.
    Super-exponential decay via the joint Gram-entry density singularity at $\det G = 0$.
    See `my_theorems/paper2_sphere_scoping.md` (§ Tightened rate analysis). -/
theorem cechFillProb_tail_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => cechFillProb p d) Filter.atTop (nhds 1) :=
  sorry

/-- **GeomCov asymptotic (Paper 2 headline part 2).**
    $\text{geomCov}_{\text{Čech}}(p, d) / (p^3 \cdot (1 - q_{\text{Čech}}(p, d))) \to 1$
    as $d \to \infty$ at fixed $p \in (0,1)$. Sign positive; leading coefficient $p^3$.
    Derivation: surface-concentration of the Gram density forces the cross-term
    $c_d := \Pr[A_{12} \mid F=0] \to 0$ super-exponentially (slower than $1 - q_{\text{Čech}}$),
    leaving the universal coefficient $p^3$. MC-verified at $d \in \{5, 7, 12\}$. -/
theorem geomCovCech_asymptotic (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Filter.Tendsto (fun d : ℕ => geomCovCech p d / (p ^ 3 * (1 - cechFillProb p d)))
      Filter.atTop (nhds 1) :=
  sorry

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
  isProb d hd := uniformOnSphere_isProb d hd
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
