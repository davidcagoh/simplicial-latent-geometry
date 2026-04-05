# simplicial-latent-geometry

**simplicial-latent-geometry** is a Lean 4 formalization of a **simplicial latent geometry detection problem**, developed using an Aristotle-assisted proof workflow.

Unlike `automated-proofs`, which provides reusable infrastructure, this repository is a **mathematical case study**. Its purpose is to formalize a specific statistical and geometric argument inside Lean, clarify what has already been proved, and expose the hardest remaining gaps.

## Mathematical focus

The project studies a phase transition for a **doubly-signed filled triangle statistic**, used to distinguish a null simplicial complex model from a geometric ech complex on the torus.

At a high level, the proof strategy is to compare the null variance and the geometric expectation, and then derive a detection criterion of the form:

```text
 
```

## Repository role in the broader ecosystem

| Repository | Role |
|---|---|
| `automated-proofs` | Reusable proof workflow and infrastructure |
| `theorem-agents` | Agentic theorem orchestration and decomposition |
| `simplicial-latent-geometry` | Concrete mathematical formalization and research application |

## What this repository shows

| Area | Purpose |
|---|---|
| Real mathematical formalization | A substantive theorem-development project rather than a generic template |
| Proof-state transparency | Documents proved lemmas, open sorries, and blocked steps |
| Workflow realism | Shows where Aristotle helps, where it struggles, and where manual mathematics is still needed |

## Key files

| Path | Purpose |
|---|---|
| `SimplicialLatentGeometry/SimplicialDetection.lean` | Main theorem development |
| `my_theorems/strategy2.md` | Strategy note for the active proof plan |
| `help_from_aristotle/` | Submission history and decision logs |
| `scripts/` | Build, status, submission, and retrieval support |

## Workflow

```bash
lake build
lake build SimplicialLatentGeometry.SimplicialDetection
python scripts/status.py
python scripts/submit.py my_theorems/strategy2.md "Prove <lemma>" --dry-run
python scripts/submit.py my_theorems/strategy2.md "Prove <lemma>"
python scripts/retrieve.py
```

## Relationship to the Stochastic Proofs Handbook

This repository follows the broader conventions in the **Stochastic Proofs Handbook**, but the local repository files remain authoritative for project-specific mathematical details, type decisions, and proof-state tracking.

## Why keep this separate

This repository should remain separate because its value is not only the workflow. It is also the **mathematical object itself**: a concrete formalization effort with its own theorem structure, blocked lemmas, and research significance.
