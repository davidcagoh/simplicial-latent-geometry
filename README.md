# simplicial-latent-geometry

Lean 4 formalization of a phase transition for the doubly-signed filled triangle statistic — detecting a Čech complex on the flat torus against a null simplicial complex model. Part of the [Stochastic Proofs](../stochastic-proofs-handbook) workspace.

## Repository structure

| Path | Role |
|---|---|
| `SimplicialLatentGeometry/SimplicialDetection.lean` | Main proof (~3750 lines) |
| `my_theorems/paper.tex` | LaTeX paper (16pp) |
| `my_theorems/proof_strategy.md` | Active proof strategy / Aristotle spec |
| `literature/` | Reference PDFs |
| `requests/` | Aristotle submission prompts |
| `results/` | Aristotle result tarballs |

## Commands

```bash
lake build
lake build SimplicialLatentGeometry.SimplicialDetection

python ../stochastic-proofs-handbook/scripts/status.py
python ../stochastic-proofs-handbook/scripts/submit.py my_theorems/proof_strategy.md "Prove <lemma>"
python ../stochastic-proofs-handbook/scripts/retrieve.py [project-id]
```

## Setup

```bash
pip install aristotlelib pathspec python-dotenv
# API key in lean-workspace/.env — no per-project .env needed
lake build
```

Lean toolchain: `leanprover/lean4:v4.28.0` · Mathlib: `v4.28.0` · Shared cache: `../.lean-packages/`
