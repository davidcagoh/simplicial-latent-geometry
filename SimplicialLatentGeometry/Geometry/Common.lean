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
