import Mathlib
import SimplicialLatentGeometry.Core.Statistic

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Geometry / Common — abstract geometric models

Phase A2 of the OQ-18 multi-paper refactor. This module defines the typeclass abstraction
that the per-setting instances (L∞ Rips on torus, sphere `S^{d-1}`, L² Euclidean torus)
will instantiate. The detection theorem (`Core.Detection`, future Phase A3) is then phrased
once and used three times.

## Layout

* `GeometricModel Setting` — bare scaffolding: a `Setting`-indexed family of measurable
  point spaces with a probability measure, plus an edge predicate parameterised by a
  radius, and a `matchR : ℝ → Setting → ℝ` that aligns marginal edge probability with `p`.
* `HomogeneousGeometricModel Setting` — adds *axiomatic homogeneity*: the joint marginals
  on triples of i.i.d. points (`triangleProb`, `geomCov`) are exposed as instance fields,
  together with the Rips closed form `geomCov = q · ((1−p)^3 + p^3) − q^2` as an axiom
  conditioned on a per-setting `ValidRegime` predicate.

## Design notes

* We do **not** carry a measurable group action; instead each instance proves the joint
  marginals directly (the wiki calls this "axiomatic homogeneity"). The group-action
  refactor is deferred until the methodology paper (Paper 4) actually requires it.
* `ValidRegime p s` is a per-setting validity predicate (L∞ uses `1 ≤ d ∧ matchRadius p d ≤ 1/4`,
  the sphere instance will use a different cap-asymptotics condition). The closed form is
  asserted only under the regime; downstream detection theorems will assume it.
* `geomCov_closed_form` is the *only* nontrivial axiom — the rest are bookkeeping.

## Status

Phase A2 — typeclass + L∞ instance. Detection / variance extraction (A3, A4) builds on this.
-/

/-! ## Bare geometric scaffolding -/

/-- A `Setting`-indexed family of measurable point spaces with a probability measure, an
    edge predicate parameterised by a radius `r ∈ ℝ`, and a matched-radius function
    `matchR : ℝ → Setting → ℝ` aligning the marginal edge probability with `p`.

    `Setting` is typically `ℕ` (the dimension); for the sphere instance it can be a
    richer record carrying the dimension and the sphere radius. -/
class GeometricModel (Setting : Type*) where
  /-- The point space for parameter `s : Setting`. -/
  Point : Setting → Type*
  /-- Measurable-space structure on each point space. -/
  pointSpace : ∀ s, MeasurableSpace (Point s)
  /-- The probability measure on `Point s` (uniform, in all current instances). -/
  μ : ∀ s, MeasureTheory.Measure (Point s)
  /-- The measure is a probability measure. -/
  isProb : ∀ s, MeasureTheory.IsProbabilityMeasure (μ s)
  /-- Edge predicate: two points are at distance ≤ `r` for radius `r`. -/
  edge : ∀ s, ℝ → Point s → Point s → Prop
  /-- Matched radius: the `r ≥ 0` for which the marginal edge probability equals `p`. -/
  matchR : ℝ → Setting → ℝ

attribute [instance] GeometricModel.pointSpace GeometricModel.isProb

/-! ## Homogeneity axioms -/

/-- A `GeometricModel` together with named joint marginals and the Rips-form closed
    expression for `geomCov`. Concretely:

    * `triangleProb p s` — the marginal probability that three i.i.d. points form a
      Rips 3-clique at the matched radius. On L∞ this equals `(3 r²)^d`; on the sphere
      it is given by spherical-cap asymptotics; etc.
    * `geomCov p s` — the covariance
        `E[(A₁₂ − p)(A₁₃ − p)(A₂₃ − p)(F_{123} − q)]`
      under the geometric measure, where `F_{ijk} = A_{ij} · A_{ik} · A_{jk}` under Rips.
    * `geomCov_closed_form` — under the `ValidRegime`, the identity
        `geomCov = q · ((1−p)^3 + p^3) − q^2`
      with `q = triangleProb p s`. Derivation: see `simplicial-latent-geometry/my_theorems/
      oq18_math_audit.md` for the L∞ case; the same algebraic identity holds whenever
      `F = A₁₂ A₁₃ A₂₃` (which is the universal Rips clique identity).

    The `ValidRegime` predicate carries the per-setting validity conditions (matched
    radius small enough, dimension ≥ 1, etc.). Instances supply it; the abstract
    detection theorem in `Core.Detection` will quantify over a witness of `ValidRegime`. -/
class HomogeneousGeometricModel (Setting : Type*) extends GeometricModel Setting where
  /-- Triangle (3-clique) probability under the matched radius: `q(p,s)`. -/
  triangleProb : ℝ → Setting → ℝ
  /-- Geometric covariance: `E[(A₁₂−p)(A₁₃−p)(A₂₃−p)(F−q)]` under the geometric measure. -/
  geomCov : ℝ → Setting → ℝ
  /-- Per-setting validity predicate (e.g. matched radius small, dimension ≥ 1). -/
  ValidRegime : ℝ → Setting → Prop
  /-- The Rips-form closed identity. Holds in the valid regime; the instance proves it. -/
  geomCov_closed_form : ∀ {p : ℝ} {s : Setting}, ValidRegime p s →
      geomCov p s
        = triangleProb p s * ((1 - p) ^ 3 + p ^ 3) - triangleProb p s ^ 2

/-! ## Derived consequences

These follow purely from the closed form; instances inherit them for free. They will be
used by the abstract detection theorem in `Core.Detection`. -/

namespace HomogeneousGeometricModel

variable {Setting : Type*} [HomogeneousGeometricModel Setting]

/-- Decay-rate upper bound: `geomCov ≤ q · ((1−p)^3 + p^3)`. Immediate from the closed
    form via `q² ≥ 0`. Mirrors `geometricCov_decay_rate_le` in the legacy L∞ proof. -/
lemma geomCov_le_triangleProb_mul {p : ℝ} {s : Setting}
    (hv : HomogeneousGeometricModel.ValidRegime p s) :
    geomCov p s ≤ triangleProb p s * ((1 - p) ^ 3 + p ^ 3) := by
  have h := geomCov_closed_form (s := s) hv
  nlinarith [sq_nonneg (triangleProb p s)]

end HomogeneousGeometricModel

/-! ## Čech-on-sphere asymptotic model (Paper 2)

Session-65 split (see `paper2_sphere_scoping.md` and `wiki/decisions.md`): the Rips closed
form `geomCov = q[(1-p)³ + p³] − q²` is an exact algebraic identity that relies on
`F^{Rips} = A₁₂ A₁₃ A₂₃`. Under Čech fill on $S^{d-1}$ (Helly-$d$), the wedge⊆fill inclusion
is strict and the closed form is replaced by a **four-moment decomposition** with no
algebraic shortcut. The sub-leading rate analysis in `paper2_sphere_scoping.md` (§ Sub-leading
rate of $c_d$) gives the asymptotic form

  $\text{geomCov}_{\text{Čech}}(p, d) = p^3 \cdot (1 - q_{\text{Čech}}(p, d)) \cdot (1 + o(1))$

which is what this typeclass exposes as its sole axiom. Headline `d^*(n,p) = 3 log n / log log n`
follows once the typeclass is wired into the (forthcoming) abstract detection theorem.

### Why a separate class

Three concrete reasons (see `wiki/decisions.md` session-65):

1. Čech has no exact closed form (only asymptotic).
2. Four moments needed ($q_{\text{Rips}}, q_{\text{Čech}}, \beta, p$) vs three for Rips.
3. The Rips axiom would have to be weakened to admit Čech, losing the algebraic identity
   that the L∞ instance uses for `geometricCov_eq_deep`.

Detection theorems can still share a common abstract SNR criterion in `Core.Detection`;
that abstraction takes the signal sequence as data, not the model class. -/

/-- Čech-fill asymptotic model on a setting parameter ordered by `Filter.atTop`. Carries
    `cechFillProb p s = q_{Čech}(p, s)`, `geomCovCech p s = geomCov^{Čech}(p, s)`, a
    per-setting `ValidRegime`, and one axiom: the ratio
    `geomCovCech / (p^3 · (1 − cechFillProb))` tends to `1` along the directed setting.

    The current target instance is `Setting = ℕ` (sphere dimension). The `[Preorder]`
    + `[IsDirected]` requirements make `Filter.atTop` available. -/
class CechSphereModel (Setting : Type*) [Preorder Setting] extends GeometricModel Setting where
  /-- Čech-fill triangle probability $q_{\text{Čech}}(p, s)$ on three iid points. -/
  cechFillProb : ℝ → Setting → ℝ
  /-- Geometric covariance under Čech fill:
      `E[(A₁₂−p)(A₁₃−p)(A₂₃−p)(F^{Čech}−q_{Čech})]`. -/
  geomCovCech : ℝ → Setting → ℝ
  /-- Per-setting validity predicate (e.g. `5 ≤ d` so the Gram density vanishes at
      $\det G = 0$ and the super-exponential tail applies). -/
  ValidRegime : ℝ → Setting → Prop
  /-- **Asymptotic axiom.** Leading-order identity verified by MC at $d \in \{5,7,12\}$:
      `geomCovCech p s ∼ p^3 · (1 − cechFillProb p s)` as $s \to \infty$ at fixed $p$.
      Derivation: surface-concentration of the joint Gram density on $\{\det G = 0\}$
      forces the cross-term $c_d := \Pr[A_{12} \mid F=0] \to 0$ super-exponentially,
      leaving the universal coefficient $p^3$. See `paper2_sphere_scoping.md`. -/
  geomCov_asymptotic : ∀ {p : ℝ}, 0 < p → p < 1 →
      Filter.Tendsto (fun s => geomCovCech p s / (p ^ 3 * (1 - cechFillProb p s)))
        Filter.atTop (nhds 1)

/-! ### Notes on the tail rate

The super-exponential tail `1 − cechFillProb p d ∼ (3 z_p² / d)^{(d-2)/2}` is *not* exposed
as a typeclass field — it is an instance-specific theorem, proved per-setting (e.g., on
$S^{d-1}$ via the joint Gram density). Detection theorems consume only `geomCov_asymptotic`
plus an SNR criterion `n^{3/2} · (1 − cechFillProb) → ∞`; the per-instance tail rate is
used downstream to convert this into the explicit threshold $d^*(n, p) = 3 \log n / \log\log n$. -/
