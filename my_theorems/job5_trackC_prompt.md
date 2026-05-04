# Aristotle Job 5 — Track C: Double-Fill Joint Probability

## Goal

Prove `doubleFill_joint_prob` in `SimplicialLatentGeometry/SimplicialDetection.lean`.
This is the key lemma for the fill-pair statistic τ_ff.

## Mathematical Statement

For adjacent triangles `{1,2,3}` and `{1,2,4}` sharing edge `{1,2}`, under the Čech
model with radius `r`:

```
E[F_{123} · F_{124}] = (112/3 · r³)^d
```

The Lean stub (already in the file after "Track C stubs" comment):

```lean
lemma doubleFill_joint_prob (d : ℕ) (hd : 1 ≤ d) (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫ pts : Fin 4 → (Fin d → T1),
      (if (∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 2) z ≤ r) ∧
          (∃ z : Fin d → T1, dist (pts 0) z ≤ r ∧ dist (pts 1) z ≤ r ∧ dist (pts 3) z ≤ r)
       then (1:ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 4 => (volume : Measure (Fin d → T1)))
    = (112 / 3 * r ^ 3) ^ d := by
  sorry
```

## Proof Strategy

### Step 1 — New real-line lemma in `TorusIntegrals.lean`

Add alongside `integral_2r_minus_abs` and `integral_4r_minus_abs`:

```lean
/-- ∫_0^{2r} (4r - b)² · 2 db = 112/3 · r³ -/
lemma integral_fill_fiber_sq_line (r : ℝ) (hr0 : 0 ≤ r) :
    2 * ∫ b in Set.Icc (0:ℝ) (2*r), (4*r - b)^2 = 112/3 * r^3
```

Proof: antiderivative `-(4r-b)³/3`. Evaluated:
`[-(4r-b)³/3]_0^{2r} = -r³/3 - (-(4r)³/3) = -r³/3 + 64r³/3 = 63r³/3`... wait:
`-(4r-2r)³/3 - (-(4r-0)³/3) = -8r³/3 + 64r³/3 = 56r³/3`.
Times 2 = `112r³/3`. ✓

Use `intervalIntegral.integral_comp_sub_right` or direct computation matching
the style of `integral_2r_minus_abs` (split, antiderivative via `norm_num`).

### Step 2 — 1D squared fiber integral

The fill fiber at distance `b = dist(x1,x2)` on T1 (when `b ≤ 2r`) has length `4r - b`
(proved in `fill_fiber_volume` / `fill_fiber_real_length` in TorusIntegrals.lean).

For the 1D version: define
```lean
/-- ∫_{(x1,x2) ∈ T1²} (fill_fiber_length(x1,x2))² = 112/3 · r³ -/
lemma integral_fill_fiber_sq_T1 (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/4) :
    ∫ x : Fin 2 → T1, (fill_fiber_volume r (x 0) (x 1))^2 = 112/3 * r^3
```

Strategy: use translation invariance + substitution `b = dist(x 0, x 1)` to reduce to
`integral_fill_fiber_sq_line`. Pattern: same as how `fillSet_outer_integral` uses
`volume_closedBall_inter_T1` and integrates over the distance variable.

Concretely: use `MeasureTheory.integral_prod_eq` + translation invariance of T1 to get
∫_{x1} ∫_{x2} (fill_fiber(x1,x2))² = ∫_0^{2r} (4r-b)² · 2 db = 112/3 · r³.

### Step 3 — Fubini factorisation over coordinates

The fill condition on T^d (with sup-norm) factors per coordinate:
`∃ z : Fin d → T1, ∀ i ∈ {0,1,2}, dist (pts i) z ≤ r`
`↔ ∀ l : Fin d, ∃ zl : T1, ∀ i ∈ {0,1,2}, dist (pts i l) zl ≤ r`

So the joint fill event for pts 0,1,2 AND pts 0,1,3 becomes:
`∀ l, (fill_1D(pts 0 l, pts 1 l, pts 2 l)) ∧ (fill_1D(pts 0 l, pts 1 l, pts 3 l))`

Apply Fubini to factor over coordinates l, and within each coordinate apply independence
of pts 2 l and pts 3 l given pts 0 l, pts 1 l:

```
∫_{pts 0,1,2,3} = ∫_{pts 0,1} [∫_{pts 2} fill_{012}] · [∫_{pts 3} fill_{013}]
               = ∫_{pts 0,1} (fill_fiber_d(pts 0, pts 1))²
```

where `fill_fiber_d(x0,x1) = ∏_l fill_fiber_1D(x0 l, x1 l)`.

Then `∫_{pts 0,1} (fill_fiber_d)² = ∫_{pts 0,1} ∏_l (fill_fiber_1D)²`
`= ∏_l ∫_{x0^l, x1^l} (fill_fiber_1D)² = (112/3 · r³)^d`.

Use `MeasureTheory.Measure.pi_pi`, Fubini (`MeasureTheory.integral_prod`), and the
existing `volume_coordFactored_eq_pow` infrastructure or an analogous product lemma.

Key Lean references for the factorisation:
- `measurable_transpose` in TorusIntegrals.lean
- `volume_map_transpose` in TorusIntegrals.lean  
- `volume_coordFactored_eq_pow` in TorusIntegrals.lean
- `fillSet_outer_integral` in TorusIntegrals.lean (as template for the Fubini step)

## Files to modify

1. `SimplicialLatentGeometry/TorusIntegrals.lean` — add:
   - `integral_fill_fiber_sq_line` (new real-line integral)
   - `integral_fill_fiber_sq_T1` (1D torus version)

2. `SimplicialLatentGeometry/SimplicialDetection.lean` — prove:
   - `doubleFill_joint_prob` (the main target; stub is already there)

## Fingerprint checklist (no evasion)

- [ ] No `sorry`/`admit`/`native_decide` in new content
- [ ] The value `(112 / 3 * r ^ 3) ^ d` must be the literal RHS proved
- [ ] The 1D integral computation must be explicit (not absorbed into a witness)
- [ ] `integral_fill_fiber_sq_line` must compute `112/3 * r^3` via antiderivative arithmetic
- [ ] The Fubini step must genuinely condition on (pts 0, pts 1) and use independence of pts 2, pts 3
