# CLAUDE.md

> **Current proof state and next priorities live in the wiki, not here.**
> Read `wiki/INDEX.md` first, then the top entry of `wiki/session-log.md`.
> This file contains only stable architectural context that doesn't change session-to-session.

## Project: Simplicial Latent Geometry

Formalizes the phase transition for the **doubly-signed filled triangle statistic** — the simplicial analogue of BDER (2016). Core question: distinguish a null 2-parameter complex 2PC(n,p,q) from a Čech complex on 𝕋^d using τ_f = Σ_t ∏_{e}(A_e−p)·(F_t−q).

**Proof strategy (Strategy 2):**
- Var[τ_f | 2PC] = C(n,3)·p³(1−p)³·q(1−q) — diagonal only, O(n³)
- E[τ_f | Čech] = C(n,3)·geometricCov p d
- Detection criterion: n^{3/2}·geometricCov p d → ∞

**Key open problem:** geomCov(p,d) = Θ(|log p|/d) — this decay rate is needed to make d*(n,p) ~ n^{3/2}|log p| rigorous (currently heuristic in §4.4). See wiki OQ-9.

Strategy 1 (unsigned variance-gap) was abandoned — `E[V_f](p,d) → L > 0` as d→∞, not 0.

## Repository

- `SimplicialLatentGeometry/SimplicialDetection.lean` — main proof (~3750 lines); Strategy 1 material at lines ~1–620 is reference-only; Strategy 2 starts at ~line 634
- `requests/proof_decisions_log.md` — chronological record; **update after every decision or submission**
- `my_theorems/paper.tex` — LaTeX paper (11pp, compiles clean); §4.4 is heuristic pending OQ-9
- `my_theorems/strategy2.md` — full strategy document

## Commands

```bash
lake build                                               # build whole project
lake build SimplicialLatentGeometry.SimplicialDetection  # elaborate main file

python ../stochastic-proofs-handbook/scripts/status.py                              # sorry count + job status
python ../stochastic-proofs-handbook/scripts/submit.py my_theorems/proof_strategy.md "Prove <lemma>" --dry-run
python ../stochastic-proofs-handbook/scripts/submit.py my_theorems/proof_strategy.md "Prove <lemma>"
python ../stochastic-proofs-handbook/scripts/retrieve.py
python ../stochastic-proofs-handbook/scripts/retrieve.py <project-id>
```

## Type Decisions (do not change)

| Object | Lean type |
|---|---|
| `MeasurableSpace (CechSample n d)` | `MeasurableSpace.comap CechSample.points inferInstance` |
| Edge indicators | `Fin n → Fin n → Bool` |
| Triangle indicators | `{σ : Finset (Fin n) // σ.card = 3} → Bool` |
| Torus | `Fin d → AddCircle (1 : ℝ)` |
| `matchRadius_spec` hypothesis | `hd : 1 ≤ d` (added by Aristotle) |
| `volumeEmpty` beta parameter | `x = 1 - (s / (2 * (2 * r))) ^ 2` — i.e. 1−(s/4r)² |
| `volumeFill` beta parameter | `x = 1 - (s / (2 * r)) ^ 2` — i.e. 1−(s/2r)² |

## volumeFill Definition (REFACTORED 2026-04-04)

The old shell-decomposition formula was geometrically incorrect. Replaced with the incomplete-beta formula:

```lean
-- volumeFill (beta formula for r-ball intersection):
volumeFill d r s = euclidBallVol d r * incBeta / betaFn
  where x = 1 - (s / (2 * r)) ^ 2

-- volumeEmpty (beta formula for 2r-ball intersection):
volumeEmpty d r s = euclidBallVol d (2*r) * incBeta / betaFn
  where x = 1 - (s / (2 * (2 * r))) ^ 2
```

- `volumeFill_eq_zero_d1` was **removed** — do NOT add back
- `volumeFill_div_volumeEmpty_le_one_ge2` covers **all d**
- Ratio proof strategy: `(1/2)^d · incBeta_fill/incBeta_empty ≤ 1`

## Dead-Code Sorries (do not touch)

- `fillingProb_eq_substituted` (~line 1375) — explicitly dead, false under new `fillingProb` definition
- `substituted_tendsto` (~line 1504) — kept for reference; not in proof chain
