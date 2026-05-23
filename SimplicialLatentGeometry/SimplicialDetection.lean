import SimplicialLatentGeometry.Detection.Core.Types
import SimplicialLatentGeometry.Detection.Core.MeasureScaffold
import SimplicialLatentGeometry.Detection.Core.BetaIncomplete
import SimplicialLatentGeometry.Detection.DeepRegime.IntegralsAndMoments
import SimplicialLatentGeometry.Detection.DeepRegime.GeometricCov
import SimplicialLatentGeometry.Detection.MidRegime.Scaffold
import SimplicialLatentGeometry.Detection.MidRegime.FreeIntegrals
import SimplicialLatentGeometry.Detection.MidRegime.GeomCovFree
import SimplicialLatentGeometry.Detection.Independence.TriangleIndicators
import SimplicialLatentGeometry.Detection.Independence.VertexIndep
import SimplicialLatentGeometry.Detection.Independence.EdgeSharing
import SimplicialLatentGeometry.Detection.PhaseTransition.SecondMoment
import SimplicialLatentGeometry.Detection.PhaseTransition.PaleyZygmund
import SimplicialLatentGeometry.Detection.PhaseTransition.Chebyshev
import SimplicialLatentGeometry.Detection.PhaseTransition.Headline

/-!
# SimplicialDetection — Re-export shim

The original 5606-LOC `SimplicialDetection.lean` was split in session 96 per the
tier-3b audit recommendation in
[`audits/simplicial-latent-geometry/README.md`](../../audits/simplicial-latent-geometry/README.md).
The 15 sub-modules live under `SimplicialLatentGeometry/Detection/`:

- `Core/{Types, MeasureScaffold, BetaIncomplete}` — foundation
- `DeepRegime/{IntegralsAndMoments, GeometricCov}` — low-r Čech infrastructure
- `MidRegime/{Scaffold, FreeIntegrals, GeomCovFree}` — r ∈ (1/3,1/2] Rips refactor
- `Independence/{TriangleIndicators, VertexIndep, EdgeSharing}` — independence + covariance
- `PhaseTransition/{SecondMoment, PaleyZygmund, Chebyshev, Headline}` — detection chain

`DeepRegime/IntegralsAndMoments.lean` merges `DeepIntegrals + DeepCentered`
clusters per the audit's ≥ 8-edge bond rule (16 cross-cluster edges).

The umbrella `SimplicialLatentGeometry.lean` and the (one) external importer
`Geometry/TorusLInf.lean` are migrated to narrowest sub-module imports in the
same session, so this shim is vestigial — kept as a single-line meta-export
convenience.

See [`audits/REPORT-2026-05-23-simplicial-split.md`](../../audits/REPORT-2026-05-23-simplicial-split.md)
for the approach-evaluation report (predictions vs. actuals).
-/
