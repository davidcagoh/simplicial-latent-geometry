# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

---

## Project: Simplicial Latent Geometry

**Research context**

This project formalises results on **testing for geometry in random simplicial complexes** — the simplicial analogue of the Bubeck–Ding–Eldan–Rácz (BDER 2016) graph-geometry detection problem.

**The core question:** Given an observed simplicial complex on $n$ vertices, can we distinguish the null **2-parameter complex (2PC)** (edges i.i.d. with probability $p$; each 3-cycle independently filled with probability $q$) from the geometric alternative **Čech/Rips complex** (points uniform on $\mathbb{T}^d$ or $\mathbb{S}^{d-1}$, simplices formed by proximity)? What is the phase transition in $d$?

**Starting materials** are in `starting-point/`:
- `handoff-instructions.md` — full literature review (BDER 2016 through Bangachev–Bresler 2025) + detailed notes on Goh (PRUV 2023). Includes notation, open problems, and specific next steps.
- `new-literature-review.md` — structured literature survey with 61 references.
- `old-paper.pdf` — Goh (PRUV 2023): volume computations for $V_f, V_e$, parameter matching, expectation/variance of filled triangle count.

**Key objects to formalise:**
- The 2PC and Čech complex models and their parameter matching ($p = V_d(2r)$, $q = \mathbb{E}[V_f]/\mathbb{E}[V_e]$)
- Volume integrals $V_f(r,s)$ and $V_e(r,s)$ on the flat torus
- Expectation and variance of the filled triangle count $\Delta_f$ under both models
- The SNR argument: Čech variance is $O(n^4)$ vs 2PC variance $O(n^3)$, giving a detection threshold

**Goals (in priority order)**

1. **Parse and verify** — Submit Lean files with `sorry` placeholders to Aristotle, parse the returned `.tar.gz`, verify the proofs compile locally.
2. **Optimize** — Re-submit completed proofs with prompts like "Golf all the proofs: minimize tactic count and simplify where possible."
3. **Multi-agent proof space exploration** — Run multiple parallel Aristotle submissions with varied prompts/hints, compare outputs, and select the best proof strategy.

**Lean environment**

- **Entry point**: `SimplicialLatentGeometry.lean` — add imports here in dependency order
- **Source files**: `SimplicialLatentGeometry/` — add new `.lean` files here
- **Main proof file**: `SimplicialLatentGeometry/SimplicialDetection.lean` — 14 sorries covering all 6 definitions, 7 lemmas, and 2 theorems
- **Placeholder**: `SimplicialLatentGeometry/Basic.lean` — stub only (`def hello := "world"`); safe to ignore
- **Decisions log**: `help_from_aristotle/proof_decisions_log.md` — chronological record of type choices, Aristotle job outcomes, and Lean lessons earned in this project; update it after every significant decision or submission

**Skeleton convention**

Create `SimplicialLatentGeometry/<TheoremName>.lean`, then add the import to `SimplicialLatentGeometry.lean`:

```lean
import Mathlib
-- import SimplicialLatentGeometry.Lemmas         -- uncomment if helper lemmas exist
-- import SimplicialLatentGeometry.<Name>Helpers  -- uncomment if bridging helpers exist

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-! # <Paper Title> ... -/

/-! ## Definitions -/
/-! ## Lemmas -/
/-! ## Main Theorem -/
```

---

## Python Setup

Install dependencies once (Python 3.10+ required):

```bash
pip install aristotlelib pathspec python-dotenv
# or with uv:
uv pip install aristotlelib pathspec python-dotenv
```

Create `.env` in the project root:
```
ARISTOTLE_API_KEY=arstl_...
```

The `.env` file is `.gitignore`d — never commit it.

**Shared Mathlib cache** — `lakefile.toml` sets `packagesDir = "../.lean-packages"`. This means Mathlib (~7.7 GB) is downloaded one level up from the repo, shared across sibling projects. On first `lake build`, Lake downloads Mathlib into `../.lean-packages/`. If you keep multiple Lean projects in the same parent folder, they share the cache automatically.

---

## Scripts (Workflow)

Run all scripts from the project root (where `.env` lives).

### `status.py` — project dashboard

```bash
python scripts/status.py
```

Shows sorry count per `.lean` file with line numbers, and all tracked Aristotle submissions with live status, age, and prompt preview. Run this before doing anything else.

### `submit.py` — package and submit to Aristotle

```bash
# Always preview first
python scripts/submit.py my_theorems/Paper.md "Fill in all the sorries" --dry-run

# Then submit for real
python scripts/submit.py my_theorems/Paper.md "Fill in all the sorries"
```

- Packages only Lean project files (respects `.gitignore`, strips `results/`, `scripts/`, `my_theorems/`, `.claude/`, `.github/`, `help_from_aristotle/`, `memory/`, `reports/`).
- Writes `results/<id>.meta.json` to track the paper → job mapping.
- Exits immediately; Aristotle emails when done.

### `retrieve.py` — download and annotate results

```bash
python scripts/retrieve.py              # check all tracked jobs
python scripts/retrieve.py <project-id> # check a specific job
```

Run this when Aristotle emails you. Downloads completed jobs, writes `reports/<PaperName>_annotated.md` with inline callouts:
- `✓ Proved` — sorry filled
- `◑ Proved vacuously` — proved but non-substantively
- `⚠️ Needs revision` — sorry remains

### `watch.py` — adaptive background poller

```bash
python scripts/watch.py
```

Polls adaptively (5 min at 0–25%, 10 min at 25–50%, 15 min at 50–75%, 8 min at 75–99%). Auto-runs `retrieve.py` when a job completes.

### Typical session

```bash
python scripts/status.py
python scripts/submit.py my_theorems/Paper.md "Fill in all the sorries" --dry-run
python scripts/submit.py my_theorems/Paper.md "Fill in all the sorries"
# Wait for email, then:
python scripts/retrieve.py
```

---

## Lean 4 / Aristotle Workflow

### Paper → Lean skeleton → submission

**Step 1 — Create the Lean skeleton**

```lean
import Mathlib
-- import <Module>.Lemmas        -- uncomment if helper lemmas exist
-- import <Module>.<Name>Helpers -- uncomment if bridging helpers exist

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# <Paper Title>
<One-paragraph summary.>
-/

-- open scoped Matrix  -- add if matrices are used

/-! ## Definitions -/
/-! ## Lemmas -/
/-! ## Main Theorem -/
```

**Step 2 — Write PROVIDED SOLUTION docstrings**

Every sorry'd lemma must have a docstring with proof steps. Aristotle reads the header docstring — **not** comments inside `by` blocks.

```lean
/-- **Lemma N.M (Name).** Statement in plain English.

    PROVIDED SOLUTION
    Step 1: First proof step from the paper.
    Step 2: Key substitution or identity used.
    Step 3: Conclusion. -/
lemma my_lemma ... : ... := by
  sorry
```

The richer the PROVIDED SOLUTION steps, the better Aristotle's output. ODE/integral arguments especially benefit from detailed step-by-step hints.

**Step 3 — Factor out helper lemmas**

When a theorem needs classical results not in Mathlib (Grönwall, Rayleigh quotient bounds) or small bridging lemmas, create a separate `Lemmas.lean` or `<Name>Helpers.lean` with sorry'd lemmas and their own PROVIDED SOLUTION blocks. This lets Aristotle fill helpers and main proof in one submission. Import order in the entry file matters — list files in dependency order.

**Step 4 — Submit**

Always run `--dry-run` first to confirm the file list. Guidelines for scoping:
- ≤5 sorries in one file: usually fine as one job
- >5 sorries or sorries across multiple files: consider splitting by lemma cluster

**Effective prompts:**

| Goal | Prompt |
|---|---|
| Fill all sorries | `"Fill in all the sorries in this project"` |
| Single file | `"Fill in the sorries in <Module>/<File>.lean"` |
| Targeted | `"Fill in <LemmaA> and <LemmaB>. Each has a detailed PROVIDED SOLUTION."` |
| Golf proofs | `"Golf all the proofs: minimize tactic count and simplify where possible"` |
| Repair | `"Fix all compilation errors and linter warnings"` |

---

## Project-Specific Type Decisions

These choices were made for `SimplicialDetection.lean` and are not obvious from the math; check the decisions log before changing them.

| Object | Lean type chosen | Rejected alternative | Reason |
|---|---|---|---|
| Edge indicators | `Fin n → Fin n → Bool` | `Sym2 (Fin n) → Bool` | `⟦(a,b)⟧` is ambiguous without explicit `Sym2.Rel.setoid`; type ascription alone insufficient |
| Triangle indicators | `{σ : Finset (Fin n) // σ.card = 3} → Bool` | `Fin n → Fin n → Fin n → Bool` | Avoids ordering convention; cleaner |
| Triangle edges helper | `Finset (Fin n × Fin n)` filtered by `p.1 < p.2` | `Finset (Sym2 (Fin n))` | Same `Sym2` constructor issue |
| Torus | `Fin d → AddCircle (1 : ℝ)` | `PiLp 2 (fun _ : Fin d => AddCircle (1 : ℝ))` | `AddCircle` lacks `NormedAddCommGroup`; product `MetricSpace` (sup norm) suffices |
| `MeasurableSpace` on samples | `⊤` (discrete sigma-algebra) | Derived product instance | Discrete is valid and sidesteps instance search |
| TV distance comparison | Push `cechMeasure` forward via `cechObservation` to `TwoParamSample n` | Compare measures of different types | `tvDist` is homogeneous; both models must live on the same observable space |

**Lean 4 syntax lessons earned in this project** (not in the parent CLAUDE.md):

- **`corollary` is not a Lean 4 keyword** — use `lemma` or `theorem`.
- **`Sym2` constructor** — `⟦(a,b)⟧` is ambiguous; Lean cannot infer `Sym2.Rel.setoid` from a type ascription. Use `Sym2.mk` or avoid `Sym2` in definitions where you need to construct elements.
- **`Decidable` for `Prop` in `noncomputable def`** — `if P then x else y` for `P : Prop` needs `[Decidable P]` even in noncomputable code. Fix: put `open Classical in` **before** the docstring of the definition. Required for `cechFilledCount` and `cechSignedCount` (both use the existential `hasFill`).
- **`open X in` placement** — must appear before the docstring, same as `set_option maxHeartbeats N in`.

---

## Lean Type Conventions

| Mathematical object | Lean type |
|---|---|
| d×d real matrix | `Matrix (Fin d) (Fin d) ℝ` |
| Positive definite matrix | `Matrix.PosDef M` |
| Matrix inverse | `M⁻¹` (via `Matrix.nonsing_inv`) |
| Matrix trace | `Matrix.trace M` |
| Matrix transpose | `Mᵀ` (requires `open scoped Matrix` at top of file) |
| Matrix-vector product | `M.mulVec v` |
| Dot product | `dotProduct u v` (top-level — NOT `Matrix.dotProduct`) |
| Real square root | `Real.sqrt x` |
| Real power (non-integer exponent) | `Real.rpow x r` |
| Norm | `‖M‖` (operator norm via `NNNorm`) |
| Inner product | `inner u v` (from `InnerProductSpace`) |
| Finite sum | `∑ i : Fin n, f i` |
| ODE derivative | `deriv f t` (for `f : ℝ → X`) |
| Set interval | `Set.Icc a b`, `Set.Ioo a b` |

When unsure of the exact Mathlib lemma name, write a best-effort attempt and add `-- TODO: check Mathlib name`.

---

## Common Lean Proof Pitfalls (confirmed v4.29.0-rc6 / v4.28.0)

**ℕ truncation in exponents.** Never write `2 * (L - k) / L` where `L k : ℕ` — integer division truncates. Cast to `ℝ` first:

```lean
-- WRONG: exponent truncates (e.g. L=3, k=0 → 4/3 truncates to 1)
sigma ^ (2 * (L - k) / L)

-- RIGHT: exact rational exponent
Real.rpow sigma (2 * ((L : ℝ) - (k : ℝ)) / (L : ℝ))
```

**`Matrix.mulVec_mulVec` argument order.** The first explicit arg is `v` (the vector), not `M`. Use bare `← Matrix.mulVec_mulVec` without explicit args:

```lean
-- WRONG (passes matrix as v):
rw [← Matrix.mulVec_mulVec Wbar]
-- RIGHT (bare, rewrites first occurrence of (A*B)*ᵥv):
rw [← Matrix.mulVec_mulVec]
```

**Renamed lemmas in v4.29.0-rc6:**
- `pow_le_pow_left` → `pow_le_pow_left₀`
- `div_lt_div_iff` → `div_lt_div_iff₀`

**`λ` (Unicode U+03BB) in identifiers.** `λ` is a Lean 4 keyword — using it in an identifier (e.g. `hλr`) causes a parse error. Use `hLr`, `hlam`, etc.

**`let` bindings in return types.** A `let x := expr` in the return type of a lemma creates a local def visible in the goal, but `x` is not in scope during `exact`. Inline the full expression:

```lean
-- WRONG: "Unknown identifier 't_crit_leading'"
exact ⟨0, t_crit_leading, by simp, by simp⟩
-- RIGHT:
exact ⟨0, (L : ℝ) / (projectedCovariance dat eb r * ...), by simp, by simp⟩
```

**`set_option maxHeartbeats N in` placement.** Must appear **before** the docstring, not between the docstring and the declaration.

**Interval integral of 1.** `integral_one : ∫ _ in a..b, (1 : ℝ) = b - a` is in the top-level namespace (not `intervalIntegral`). Connect Ioo set integrals to interval integrals via `MeasureTheory.integral_Ioc_eq_integral_Ioo` then `intervalIntegral.integral_of_le`.

**`"Imports are out of date"` diagnostic in VS Code.** This is the LSP cache being stale after adding a new import. It is not a code error. Run `lake build` or "Restart File" in the editor to clear it.

---

## Workflow Lessons (Earned from JEPA proof rounds)

**If Aristotle disproves a lemma, the Lean statement is wrong — not just hard to prove.** A disproof means Aristotle found a counterexample; the hypotheses are under-constrained. Re-examine the hypotheses before re-submitting.

**Aristotle may add new hypotheses to lemmas.** After retrieving results, always read `ARISTOTLE_SUMMARY_<id>.md` and diff the returned `.lean` files against your local versions. Incorporate any added hypotheses before the next submission.

**When helpers are missing from Mathlib, create `Lemmas.lean` first.** Creating focused, well-scoped sorry targets with PROVIDED SOLUTION blocks in a separate helper file lets Aristotle tackle each gap separately.

**`OUT_OF_BUDGET` means partial results are available** — download them anyway with `retrieve.py` and see what was proved before re-submitting the remainder.

---

## Verified Mathlib API Patterns (v4.29.0-rc6)

```lean
-- Scoped notations requiring explicit open:
open scoped Matrix          -- enables Mᵀ for Matrix.transpose

-- FTC (interval integral, upper limit):
intervalIntegral.integral_hasDerivAt_right
  (hf : IntervalIntegrable f volume a b)
  (hmeas : StronglyMeasurableAtFilter f (nhds b) volume)
  (hb : ContinuousAt f b) : HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b

-- StronglyMeasurableAtFilter from ContinuousOn:
ContinuousOn.stronglyMeasurableAtFilter
  (hs : IsOpen s) (hf : ContinuousOn f s) :
  ∀ x ∈ s, StronglyMeasurableAtFilter f (nhds x) volume

-- Continuity of integral primitive:
intervalIntegral.continuousOn_primitive_interval' (h_int : IntervalIntegrable f μ b₁ b₂)
  (ha : a ∈ [[b₁, b₂]]) : ContinuousOn (fun b => ∫ x in a..b, f x) [[b₁, b₂]]

-- Antitone from nonpositive derivative:
antitoneOn_of_deriv_nonpos (hD : Convex ℝ D) (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (interior D))
  (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D

-- HasDerivAt for exp composition:
hB_da.neg.exp : HasDerivAt (fun x => Real.exp (-B x)) (Real.exp (-B s) * (-β s)) s

-- ContinuousOn.exp for real functions (use .rexp not .exp for Real.exp):
hB_cont.neg.rexp : ContinuousOn (fun x => Real.exp (-B x)) S

-- Division/exp identities:
Real.exp_neg : Real.exp (-x) = (Real.exp x)⁻¹
div_inv_eq_mul : a / b⁻¹ = a * b
le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b
div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c
```

---

## Lean Environment

Pinned to match Aristotle's fixed environment — proofs returned by Aristotle compile locally without porting.

- **Toolchain**: `leanprover/lean4:v4.28.0`
- **Mathlib**: `v4.28.0` / commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- **Lean options** (standard across all projects):
  - `pp.unicode.fun = true` — pretty-prints lambdas as `fun a ↦ b`
  - `relaxedAutoImplicit = false` — all variables must be explicitly declared
  - `weak.linter.mathlibStandardSet = true` — Mathlib standard linter active
  - `maxSynthPendingDepth = 3`

```bash
lake build                                               # build whole project
lake build SimplicialLatentGeometry.SimplicialDetection  # elaborate the main proof file
```

If a proof returned by Aristotle fails to compile locally, the issue is a hallucinated lemma name or syntax error in Aristotle's output — not a version mismatch.

---

## Aristotle API (aristotlelib)

- **Dashboard / docs**: https://aristotle.harmonic.fun/dashboard/docs/
- **Python package**: `aristotlelib` (Python 3.10+); upgrade: `pip install --upgrade aristotlelib`
- **API key**: `ARISTOTLE_API_KEY=arstl_...` in `.env`

```python
from aristotlelib import Project, ProjectStatus, AristotleAPIError

# Submit
project = await Project.create(prompt="Fill in the sorries", tar_file_path="./project.tar.gz")
project = await Project.create_from_directory(prompt="Fill in the sorries", project_dir=".")

# Monitor
await project.refresh()
print(project.status, project.percent_complete)

# Download when complete
path = await project.get_solution(destination="results/output.tar.gz")
path = await project.wait_for_completion(destination="results/output.tar.gz")

# List / retrieve existing
project = await Project.from_id("abc-123-def")
projects, next_key = await Project.list_projects(status=ProjectStatus.COMPLETE, limit=10)

# Cancel
await project.cancel()
```

**`ProjectStatus` enum:** `QUEUED` → `IN_PROGRESS` → `COMPLETE` | `COMPLETE_WITH_ERRORS` | `OUT_OF_BUDGET` | `FAILED` | `CANCELED`

Terminal statuses: `COMPLETE`, `COMPLETE_WITH_ERRORS`, `OUT_OF_BUDGET`, `FAILED`, `CANCELED`

### Aristotle CLI

```bash
aristotle submit "Fill in the sorries" --project-dir . --wait --destination output.tar.gz
aristotle list --status COMPLETE IN_PROGRESS --limit 20
aristotle result <project-id> --wait --destination output.tar.gz
aristotle cancel <project-id>
```

---

## Result File Structure

```
{project_id}_aristotle/
├── ARISTOTLE_SUMMARY_{project_id}.md  # read this first — what changed, what compiled
├── README.md                          # citation boilerplate
├── lake-manifest.json                 # pinned deps at Aristotle's versions
├── lakefile.toml                      # configured for v4.28.0
├── lean-toolchain                     # leanprover/lean4:v4.28.0
└── RequestProject/
    └── {TheoremName}.lean             # proven files (sorries filled)
```

Always read `ARISTOTLE_SUMMARY_*.md` first. Diff the returned `.lean` files against local versions — Aristotle may add hypotheses.
