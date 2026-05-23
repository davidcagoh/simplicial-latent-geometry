# Reply to Nick — Čech definition

> Draft. Send after Lean refactor + paper §2.2 rewrite are in flight so the
> commitment is backed by a concrete commit.

---

Hi Nick,

You're right — and the remark below doesn't address it. As written the model
isn't a simplicial complex: under the nerve-only $r$-ball convention,
$F_{ijk} = 1$ only forces pairwise distance $\le 2r$ while edges require
$\le r$, so downward closure fails.

Digging in surfaced a deeper issue. The Lean formalization works on the
sup-norm ($\ell_\infty$) flat torus, where $\ell_\infty$-balls are
axis-aligned boxes and Helly's theorem gives Helly number 2. So pairwise
intersection of $(r/2)$-balls already implies common intersection, and the
**Kahle Čech complex (K10 Def 1.4) coincides with the Vietoris–Rips complex
on this ambient space** — there's no genuine Čech-$\ne$-Rips distinction
to test. The current draft tried to preserve a non-trivial $F$ by weakening
the nerve to $r$-balls; that's what broke downward closure.

So there's a trilemma on $\ell_\infty$-torus: cannot simultaneously have
(i) sup-norm metric, (ii) standard nerve convention, (iii) Čech strictly
smaller than Rips. My thesis avoided this by working on Euclidean $\mathbb{R}^d$
(Helly number $d+1$, the two complexes genuinely differ). The Lean moved to
sup-norm to get coordinate factorization of the moment integrals, and the
distinction silently collapsed.

The honest reframe is **Rips vs 2PC**, not Čech vs 2PC:

- $F_{ijk} := A_{ij} \cdot A_{ik} \cdot A_{jk}$ — the clique indicator. The
  model is a clique (flag) complex, downward closed by construction. Your
  objection disappears.
- The signed statistic $\tau_f$, the matching $q = q(p,d)$, the detection
  regime ($\TV \to 1$ for $n^{3/2} \cdot |\mathrm{geomCov}(p,d)| \to \infty$),
  and the variance bounds are unchanged.
- The Lean catalog from Tracks A/B/C in Appendix A carries over without
  modification — those proofs were on edge joint laws and don't depend on the
  nerve convention.
- The matched fill probability simplifies: under Rips on $\ell_\infty$ with
  $r \le 1/4$, $q = (3r^2)^d$, which is exactly the existing `gamma_pow_eq`
  lemma.

The Čech-$\ne$-Rips story is a separate problem in a different ambient space
(Euclidean $\mathbb{R}^d$, or sphere $S^{d-1}$ with closed-form spherical
caps and Anderson–Cook 1986 triple-cap asymptotics). I'll flag it as
follow-up direction in §6 — acknowledging that on $\ell_\infty$ the two
complexes coincide is what Kahle K10 Def 1.4 + Björner 1995 force us to say,
and the reframed paper is sharper for being honest about it.

Revised draft incoming in a few days. Thanks — your comment is what surfaced
this, and the new framing is cleaner than the original.

David
