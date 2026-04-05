# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with this repository.

## Project: Simplicial Latent Geometry

Formalizes the phase transition for the **doubly-signed filled triangle statistic** — the simplicial analogue of BDER (2016). Core question: distinguish a null 2-parameter complex 2PC(n,p,q) from a Čech complex on 𝕋^d using τ_f = Σ_t ∏_{e}(A_e−p)·(F_t−q).

**Proof strategy (Strategy 2):**
- Var[τ_f | 2PC] = C(n,3)·p³(1−p)³·q(1−q) — diagonal only, O(n³)
- E[τ_f | Čech] = C(n,3)·geometricCov p d
- Detection criterion: n^{3/2}·geometricCov p d → ∞

Strategy 1 (unsigned variance-gap) was abandoned — `E[V_f](p,d) → L > 0` as d→∞, not 0.

## Repository

- `SimplicialLatentGeometry/SimplicialDetection.lean` — main proof (~3750 lines); Strategy 1 material at lines ~1–620 is reference-only; Strategy 2 starts at ~line 634
- `help_from_aristotle/proof_decisions_log.md` — chronological record; **update after every decision or submission**
- `my_theorems/strategy2.md` — full strategy document

## Commands

```bash
lake build                                               # build whole project
lake build SimplicialLatentGeometry.SimplicialDetection  # elaborate main file

python ../scripts/status.py                              # sorry count + job status
python ../scripts/submit.py my_theorems/strategy2.md "Prove <lemma>" --dry-run
python ../scripts/submit.py my_theorems/strategy2.md "Prove <lemma>"
python ../scripts/retrieve.py
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

The old shell-decomposition formula was geometrically incorrect (gave ratio > 1 for d=2, confirmed by Aristotle). It has been replaced with the incomplete-beta formula, matching the structure of `volumeEmpty`:

```lean
-- volumeFill (NEW — beta formula for r-ball intersection):
volumeFill d r s = euclidBallVol d r * incBeta / betaFn
  where x = 1 - (s / (2 * r)) ^ 2

-- volumeEmpty (unchanged — beta formula for 2r-ball intersection):
volumeEmpty d r s = euclidBallVol d (2*r) * incBeta / betaFn
  where x = 1 - (s / (2 * (2 * r))) ^ 2
```

**Consequences:**
- `volumeFill_eq_zero_d1` was **removed** (was an artifact of the wrong formula — do NOT add back)
- `volumeFill_div_volumeEmpty_le_one_ge2` now covers **all d** (no `hd : 2 ≤ d` restriction)
- `volumeFill_div_volumeEmpty_le_one_d0` delegates to `volumeFill_div_volumeEmpty_le_one_ge2`
- Ratio proof strategy: `(1/2)^d · incBeta_fill/incBeta_empty ≤ 1` (x_fill ≤ x_empty since s/2r ≥ s/4r)

## Current Sorry State (2026-04-04)

`python ../scripts/status.py` reports **7 sorries**. Lines 381, 431, 631 are legacy Strategy 1 — do not touch.

**Active sorries:**

| Lemma | Line | Status |
|---|---|---|
| `substituted_tendsto` | ~1552 | Open — V_f/V_e → 1 as d→∞; paper §5 future work; axiomatize if needed |
| `volumeFill_div_le_one'` | ~2295 | Forward-ref stub; will close once ge2 is proved |
| `disjoint_triangles_indepFun` | ~2583 | **In flight** — job 60e73ec0 |
| `volumeFill_div_volumeEmpty_le_one_ge2` | ~3398 | **In flight** — job b91c8747 |

**When Aristotle emails:** `python ../scripts/retrieve.py`, then cherry-pick only the target lemma's proof body from each result (do not wholesale replace the file — Aristotle may re-sorry unrelated lemmas).

**After both jobs land:**
1. Merge `disjoint_triangles_indepFun` proof
2. Merge `volumeFill_div_volumeEmpty_le_one_ge2` proof
3. Close `volumeFill_div_le_one'` (~2295) by replacing `sorry` with:
   `exact volumeFill_div_volumeEmpty_le_one d r s hr hs hs1`
   (mechanical forward-ref fix, no new Aristotle job needed)
4. Only `substituted_tendsto` remains as a mathematical sorry

**Endgame:** only `substituted_tendsto` remains as a mathematical sorry (deep asymptotics, incomplete in paper §5).

---

## ⚠️ OPEN MATHEMATICAL CONUNDRUM (2026-04-04) — Read before touching asymptotics

**TL;DR:** `matchRadius` is defined with the wrong formula for the unit torus. The asymptotic chain `substituted_tendsto → fillingProb_tendsto_one → geometricCov_tendsto_zero → phase_transition` is currently broken, but the math IS true — it just needs a corrected `matchRadius` definition.

### The bug

`matchRadius p d` currently solves `euclidBallVol d (2r) = p`, where:
```
euclidBallVol d r = π^(d/2)/Γ(d/2+1) · r^d    (EUCLIDEAN ball formula)
```

On the unit sup-norm torus `Fin d → AddCircle (1:ℝ)` (Mathlib default), the ball volume is `(2r)^d` (not the Euclidean formula). The two differ by the factor `π^(d/2)/Γ(d/2+1)` — the volume of the Euclidean unit ball — which → 0 as d → ∞. So Lean's matchRadius compensates by sending r → ∞, blowing past the torus diameter (= 1/2) for large d.

**Numerical evidence (p=0.5):**

| d  | matchRadius (Lean) | actual edge prob on torus | correct r = p^(1/d)/2 |
|----|--------------------|--------------------------|----------------------|
| 1  | 0.125              | 0.25 (not 0.5!)          | 0.250                |
| 8  | 0.385              | 0.12 (not 0.5!)          | 0.459                |
| 20 | 0.580 > 1/2        | 1.00 (fully connected!)  | 0.483                |

**Consequences:**
- `matchRadius_tendsto_atTop` (proved) is correct per the definition, but the definition is wrong
- `fillingProb p d → 0` (not 1) — numerically confirmed
- `substituted_tendsto` (the only sorry) is FALSE as stated under current definitions
- `geometricCov_tendsto_zero` is effectively unproved (depends on `fillingProb_tendsto_one` which is false)

### The correct formula

For the unit sup-norm torus, torus ball volume = `(2r)^d`. Matching gives:
```
(2r)^d = p  →  r_correct = p^(1/d) / 2
```
With this, `r_correct → 1/2` from below as d → ∞. At r = 1/2, the ball covers the whole torus, fill probability → 1, and `geometricCov → (1-p)^3·(1-1) = 0`. ✓ The entire chain works.

**Correct Lean definition would be:**
```lean
noncomputable def matchRadius (p : ℝ) (d : ℕ) : ℝ :=
  if d = 0 then 0
  else p ^ ((1 : ℝ) / (d : ℝ)) / 2
```

### What needs resolving before the next agent touches asymptotics

1. **Confirm the intended torus metric.** Mathlib's default for `Fin d → AddCircle 1` is the **sup-norm** (L∞). If the paper intends the **L2 norm** instead, the correct ball volume formula is different (and harder to state), but the matchRadius formula changes accordingly. Ask David which metric the paper uses.

2. **If sup-norm:** change `matchRadius` to `p^(1/d)/2`. Then reprove `matchRadius_tendsto_atTop` (now r → 1/2, not ∞ — the lemma becomes FALSE; replace with `matchRadius_tendsto_half`), and reprove `geometricCov_eq_large_r` (needs r > 1/2, which is never achieved — needs modification).

3. **If L2 norm:** the torus metric needs an explicit `MetricSpace` instance override, and the ball volume is the Euclidean formula (approximately valid for r << √d/2). The asymptotic analysis is more subtle.

4. **Alternative approach:** prove `geometricCov_tendsto_zero` by a direct argument bypassing `fillingProb` entirely. For r close to 1/2, the fill probability (under the CORRECT radius) approaches 1, giving geometricCov → 0 directly.

### Build status (2026-04-04)

The file `SimplicialLatentGeometry/SimplicialDetection.lean` does NOT build cleanly — there are ~20 pre-existing errors (forward references, `exact?` placeholders from Aristotle, post-refactor breakage of old `volumeFill_measurable`). These are separate from the matchRadius issue. Key pre-existing errors:
- Lines 1885/1892: `choose3_g_sq_tendsto_atTop` and `chebyshev_single_bound` used before defined (forward refs; they're at lines 3639/3574)
- Lines 2228/2258: `exact?` placeholders (need actual proofs)
- Lines 1455/1471: `volumeFill_measurable` broken after volumeFill refactor
- Line 392: `moments_twoParam_var` referenced from active code but defined inside a comment block
