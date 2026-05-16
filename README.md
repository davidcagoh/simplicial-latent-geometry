# simplicial-latent-geometry

Lean 4 formalization of a phase transition for the doubly-signed filled-triangle statistic — detecting a Čech complex on the flat torus against a random simplicial complex null. Part of the [lean-workspace](https://github.com/davidcagoh/lean-workspace) methodology workspace. Joint work with [Nicholas A. Cook](https://nickcook.org/) (Duke).

## Result

For a point cloud on the flat torus $\mathbb{T}^d$ with edge density $p$, define the random simplicial complex by including each triangle independently with probability $p^3$ (null) versus building it as a Čech complex on a hidden geometric structure (signal). The **doubly-signed filled-triangle statistic** $\tau_{ff}$ — a fill-pair contrast — distinguishes the two with vanishing error in a regime characterized by a **sharp finite critical dimension**:

$$d^*(p) = \left\lceil \frac{|\log p|}{\log(3/2)} \right\rceil$$

Above $d^*(p)$ detection is information-theoretically impossible; below it, $\tau_{ff}$ achieves a strictly better SNR than the natural fill statistic $\tau_f$. The geometric covariance has the closed form $\mathrm{geomCov}(p,d) \asymp (3/4)^d p^2$ deep in regime, and the sparse threshold is $p_n \gg n^{-3/4}$ for fixed $d$.

**Status.** 16pp paper at `my_theorems/paper.tex`. Main theorems (moments of $\tau_f$ and $\tau_{ff}$, detection lower bound, both phase regimes, sparse-regime limit) are sorry-free, including a 1000-line `TorusIntegrals.lean` that handles measure-theoretic moves at the leading edge of Mathlib coverage. arXiv submission pending math.* endorsement.

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
