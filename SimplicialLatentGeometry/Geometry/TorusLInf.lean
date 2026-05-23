import Mathlib
import SimplicialLatentGeometry.Geometry.Common
import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Geometry / TorusLInf — L∞ Rips on the flat torus

The first concrete instance of `HomogeneousGeometricModel`. Wires the legacy definitions
in `SimplicialDetection.lean` (`Torus`, `matchRadius`, `fillingProb`, `geometricCov`,
`CechSample.hasEdge`) into the abstract typeclass.

The `geomCov` closed form is `geometricCov_eq_deep` (currently a named Aristotle target;
the instance inherits whatever sorry status that lemma has).

Setting type: `ℕ` (the dimension).
-/

/-! ## Validity regime for the L∞ Rips instance -/

/-- Per-instance validity predicate. The Rips-form closed identity for `geomCov` requires:

* `0 < p < 1` — non-degenerate edge probability;
* `1 ≤ d` — at least one torus coordinate (avoids the degenerate `matchRadius = 0` branch);
* `matchRadius p d ≤ 1/4` — the "deep regime" where `(3 r²)^d` is the marginal triangle
  probability and no Helly-2 saturation kicks in at the per-coordinate level.

This mirrors the hypothesis triple of `geometricCov_eq_deep`. -/
def TorusLInfValidRegime (p : ℝ) (d : ℕ) : Prop :=
  0 < p ∧ p < 1 ∧ 1 ≤ d ∧ matchRadius p d ≤ 1/4

/-! ## The L∞ Rips instance -/

/-- L∞ Rips on the flat torus, indexed by dimension `d : ℕ`. -/
noncomputable instance : HomogeneousGeometricModel ℕ where
  Point d := Torus d
  pointSpace _ := inferInstance
  μ _ := MeasureTheory.volume
  WellFormed _ := True
  isProb _ _ := inferInstance
  edge _ r x y := dist x y ≤ r
  matchR p d := matchRadius p d
  triangleProb p d := fillingProb p d
  geomCov p d := geometricCov p d
  ValidRegime p d := TorusLInfValidRegime p d
  geomCov_closed_form := by
    rintro p d ⟨hp0, hp1, hd, hr⟩
    exact geometricCov_eq_deep p d hp0 hp1 hd hr
