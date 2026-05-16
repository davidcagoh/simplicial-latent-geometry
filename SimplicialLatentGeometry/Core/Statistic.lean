import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Core / Statistic

Geometry-agnostic definitions for the detection program:

* The combinatorial null model `TwoParamSample n` (independent edge / fill indicators)
* Triangle-edge enumeration
* The unsigned filled-triangle count and the doubly-signed statistic τ_f, on the 2PC side
* The 2PC probability measure `twoParamMeasure n p q`

The Čech / Rips / sphere / Euclidean instantiations live in `SimplicialLatentGeometry.Geometry.*`
and supply the *alternative* model under each geometry. The detection theorem (in
`SimplicialLatentGeometry.Core.Detection`) is then stated against the universal 2PC null
and a geometric alternative, instantiated per setting.

Extraction note (Phase A1, OQ-18 core-extraction): originally these lived in
`SimplicialLatentGeometry.SimplicialDetection`. They are moved here verbatim — the imports
in the main file pull them back in. No namespace yet: namespacing is its own cleanup phase
to avoid touching every call site in the main file at extraction time.
-/

/-! ## 2PC sample type -/

/-- **Definition 1 (2-Parameter Complex).** A sample from 2PC(n, p, q) consists of:
    - edge indicators `edge : Fin n → Fin n → Bool`, each i.i.d. Bernoulli(p)
      (convention: only `edge i j` with `i < j` carries information; assumed symmetric)
    - fill indicators `fill : {s : Finset (Fin n) // s.card = 3} → Bool`, each i.i.d. Bernoulli(q)
    all mutually independent. This structure captures a single realisation; the random model
    is a probability measure on `TwoParamSample n`. -/
structure TwoParamSample (n : ℕ) where
  edge : Fin n → Fin n → Bool
  fill : {s : Finset (Fin n) // s.card = 3} → Bool

/-- Discrete sigma-algebra on TwoParamSample (all sets measurable). -/
instance (n : ℕ) : MeasurableSpace (TwoParamSample n) := ⊤

/-! ## Triangle / edge enumeration -/

/-- The three edges of a triangle as ordered pairs (i, j) with i < j. -/
def triangleEdges {n : ℕ} (t : {σ : Finset (Fin n) // σ.card = 3}) :
    Finset (Fin n × Fin n) :=
  (t.val ×ˢ t.val).filter fun p => p.1 < p.2

/-! ## Statistics on 2PC samples -/

/-- Filled triangle count Δ_f in a 2PC sample: sum over triangles of
    (fill indicator) × (product of edge indicators for the three edges).

    This is the unsigned statistic — Strategy 1 baseline. The detection program uses the
    doubly-signed variant `doublySignedFilledCount` (τ_f) below. -/
noncomputable def filledTriangleCount {n : ℕ} (s : TwoParamSample n) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    (if s.fill t then (1 : ℝ) else 0) *
    ∏ e ∈ triangleEdges t, (if s.edge e.1 e.2 then 1 else 0)

/-- **The doubly-signed filled triangle statistic τ_f, on 2PC.**
    Each triangle contributes ∏_{e ∈ edges} (A_e − p) · (F − q).
    Under 2PC, each factor has mean 0 and is independent, so E[τ_f] = 0
    and Var[τ_f] = C(n,3) · p³(1−p)³ · q(1−q) (diagonal only, O(n³)). -/
noncomputable def doublySignedFilledCount {n : ℕ} (p q : ℝ) (s : TwoParamSample n) : ℝ :=
  ∑ t : {σ : Finset (Fin n) // σ.card = 3},
    (∏ e ∈ triangleEdges t,
      (if s.edge e.1 e.2 then (1 : ℝ) - p else -p)) *
    (if s.fill t then (1 : ℝ) - q else -q)

/-! ## 2PC probability measure -/

/-- 2PC(n,p,q) probability measure: edges i.i.d. Bernoulli(p), fills i.i.d. Bernoulli(q).
    Defined as counting measure weighted by the product of Bernoulli probabilities for each
    edge indicator and fill indicator. -/
noncomputable def twoParamMeasure (n : ℕ) (p q : ℝ) :
    MeasureTheory.Measure (TwoParamSample n) :=
  MeasureTheory.Measure.count.withDensity fun s =>
    (∏ i : Fin n, ∏ j : Fin n,
      if s.edge i j then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) *
    (∏ t : {σ : Finset (Fin n) // σ.card = 3},
      if s.fill t then ENNReal.ofReal q else ENNReal.ofReal (1 - q))

