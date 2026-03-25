# Handoff Document: Testing for Geometry in Random Simplicial Complexes
*Prepared for continuation by a fresh Claude instance. Contains full literature review and detailed notes on the author's own research (Goh, PRUV 2023).*

---

## 1. The Core Problem

### 1.1 Background: Testing for Geometry in Random Graphs

The foundational problem, due to **Bubeck, Ding, Eldan, and Rácz (BDER, 2016)**, is:

> **Given a graph $G$ on $n$ vertices, can we distinguish $G \sim G(n,p)$ (Erdős–Rényi) from $G \sim G(n,p,d)$ (random geometric graph on $\mathbb{S}^{d-1}$)?**

In the RGG $G(n,p,d)$: sample $n$ vectors $x_1,\ldots,x_n \overset{\text{iid}}{\sim} \text{Unif}(\mathbb{S}^{d-1})$; connect $i \sim j$ iff $\langle x_i, x_j \rangle \geq \tau_{p,d}$ where $\tau_{p,d}$ is chosen so the marginal edge probability equals $p$. The question is the behavior of $\text{TV}(G(n,p), G(n,p,d))$ as $n, d \to \infty$.

**Main result (BDER Thm 1):**
- Dense regime ($p$ fixed): $\text{TV} \to 1$ if $d/n^3 \to 0$; $\text{TV} \to 0$ if $d/n^3 \to \infty$. **Phase transition at $d \asymp n^3$.**
- Sparse regime ($p = c/n$): $\text{TV} \to 1$ if $d/\log^3 n \to 0$.

**Key test statistic:** The *signed triangle count* $\tau(G) = \operatorname{Tr}((A - p(J-I))^3)$. Variance is $O(n^3)$ under $H_0$ vs. mean $\Theta(n^3/d)$ under $H_1$, giving SNR $\sim n^3/d$.

**Indistinguishability method:** Compare the RGG adjacency matrix (a function of a Wishart matrix $W(n,d)$) to the ER graph (a function of a GOE matrix). Proved $\text{TV}(W(n,d), \sqrt{d}M(n) + dI_n) \to 0$ when $d/n^3 \to \infty$.

---

## 2. Full Literature Review

### 2.1 BDER (2016) — Foundational Paper
- **Full title:** "Testing for high-dimensional geometry in random graphs"
- **Authors:** Sébastien Bubeck, Jian Ding, Ronen Eldan, Miklós Z. Rácz
- **Venue:** *Random Structures & Algorithms* 49(3), 2016 (arXiv: 1411.5713)
- **Key results:**
  - Dense phase transition at $d \asymp n^3$ (tight, both directions proved)
  - Signed triangle statistic achieves detection for $d \ll n^3$
  - Wishart–GOE comparison proves indistinguishability for $d \gg n^3$
  - Dimension estimation: $\text{TV}(G(n,1/2,d_1), G(n,1/2,d_2)) \geq 1 - C(d_1/n)^2$
  - **Conjecture 1:** For $p = c/n$, indistinguishability holds when $d \gg \log^3 n$

### 2.2 Liu, Mohanty, Schramm, Yang (LMSY, 2022) — Near-Resolution of Sparse Conjecture
- **Full title:** "Testing thresholds for high-dimensional sparse random geometric graphs"
- **Venue:** STOC 2022 (arXiv: 2111.11316)
- **Key results:**
  - For $p = \Theta(1/n)$: $\text{TV} \to 0$ if $d = \Omega(\log^{36} n)$ — exponential improvement over prior work
  - For general $p$: $\text{TV} \to 0$ if $d = \tilde{\Omega}(p^2 n^3)$
  - **Conjectured true threshold** at all $p$: $d \asymp (nH(p))^3$ where $H(p)$ is binary entropy
  - **Methods:**
    1. *Optimal transport on sphere*: sharp concentration for spherical cap intersections with arbitrary sets
    2. *Belief propagation / cavity method*: decay of correlations in conditional vector distributions given neighborhood structure
    3. *Stochastic domination coupling*: $G^- \subseteq G \subseteq G^+$ w.h.p. for $d = \tilde{\Omega}(p^2 n^2)$
- **Status vs. BDER Conjecture 1:** The gap between $\log^3 n$ (detection lower bound) and $\log^{36} n$ (indistinguishability) remains open; the conjecture is unresolved.

### 2.3 Brennan, Bresler, Nagaraj (BBN, 2020)
- **Venue:** *Probability Theory and Related Fields*
- **Key results:**
  - Extended BDER to full range of $p$
  - For $p = \Theta(1/n)$: $\text{TV} \to 0$ if $d \gg n^{3/2} \operatorname{polylog}(n)$
  - Method: chi-squared divergence of single edge marginal
  - Limitation: requires $d > n$; cannot reach the conjectured $d = \operatorname{polylog}(n)$ threshold

### 2.4 Eldan and Mikulincer (2020) — Anisotropic Model
- **Setting:** Gaussian latent vectors with arbitrary covariance (eigenvalue vector $\alpha$)
- **Key results:**
  - Detection possible when $n^3 \gg (\|\alpha\|_2 / \|\alpha\|_3)^6$
  - Impossibility when $n^3 \ll (\|\alpha\|_2 / \|\alpha\|_4)^4$
  - Gap between $\ell^3$ and $\ell^4$ norms left open

### 2.5 Brennan, Bresler, Huang (BBH, 2024)
- **Venue:** *Random Structures & Algorithms*
- **Key result:** Closed the anisotropic gap — proved impossibility when $n^3 \ll (\|\alpha\|_2 / \|\alpha\|_3)^6$
- **Status:** Fully resolves the Eldan–Mikulincer conjecture

### 2.6 Bangachev and Bresler — Series of Papers (2023–2025)

**Random Algebraic Graphs (RSA 2025):**
- Defines $\text{RAG}(n, \mathcal{G}, \sigma, p)$: vertices are uniform elements of an algebraic group $\mathcal{G}$; edge probability $\sigma(x_i x_j^{-1})$
- Captures spherical RGG, torus RGG, hypercube RGG as special cases
- Unified Fourier-analytic detection framework via characters of $\mathcal{G}$

**Fourier Coefficients of Spherical RGG (STOC 2024):**
- Novel two-step strategy: (1) localize dependence to "fragile edges"; (2) apply noise operator
- Gives tight low-degree polynomial lower bounds for detection
- Key implication: signed triangles are essentially optimal among degree-3 polynomials for spherical RGG

**$L^\infty$ Geometry and Suboptimality of Triangles (COLT 2024):**
- For RGG on torus with $L^\infty$ distance: signed 4-cycle count is **strictly stronger** than signed triangles
- **Implication:** Triangles are *not* universally optimal — the right statistic depends on the underlying geometry
- This is directly relevant to the simplicial complex generalization: the optimal substructure to count may depend on the manifold

**Sandwiching RGG and Erdős–Rényi (STOC 2025):**
- Poly-time coupling: $G(n, p(1-\tilde{O}(\sqrt{np/d}))) \subseteq \text{RGG}(n,\mathbb{S}^{d-1},p) \subseteq G(n, p(1+\tilde{O}(\sqrt{np/d})))$ edgewise w.h.p. when $d \gg np$
- Applications: sharp thresholds for monotone properties, robust testing, enumeration

### 2.7 Adjacent Work

**Liu and Rácz (2021/2023):**
- Noisy RGG phase transition
- Unified "latent space graphs" framework with Fourier-based indistinguishability criteria

**Rácz and Richey (2019); Bubeck and Ganguly (2018):**
- Wishart–GOE transition at higher resolution
- Entropic CLT for Wishart matrices

**Michielan, Stegehuis et al. (2025):**
- Geometry detection in scale-free (inhomogeneous) random graphs
- Weighted triangles for sparse regime, signed triangles for denser regime

**Papamichalis et al. (arXiv:2510.06136):**
- MDS-based hypothesis tests for Euclidean vs. hyperbolic latent geometry

**Mao, Wein, Zhang (COLT 2023, IEEE TIT 2024):**
- Detection-recovery gap for planted dense cycles

**Dhawan, Mao, Wein (RSA 2025):**
- Detect planted dense $r$-uniform subhypergraph in $G^r(n,p)$ via low-degree polynomial tests of adjacency tensor
- **Note:** This is planted structure detection, not latent geometry testing — the null is a random hypergraph, not a geometric one

**Bobrowski and Kahle (JACT 2018):**
- Survey on probabilistic topology of random geometric simplicial complexes (Čech/Vietoris–Rips)
- Covers Betti numbers, homological phase transitions in fixed low dimension
- **Note:** Different question from high-dimensional indistinguishability — does not study TV thresholds

**Leal, Eidi, Jost (2020):**
- Forman–Ricci and Ollivier–Ricci curvature for directed hypergraphs
- Detects connectivity motifs vs. random null model
- Heuristic; no sharp TV thresholds proved

---

## 3. Summary Table of Graph Case

| Setting | Detection lower bound | Indistinguishability upper bound | Status |
|---|---|---|---|
| Dense RGG on sphere | $d \ll n^3$ (signed triangles) | $d \gg n^3$ (Wishart–GOE) | **Tight** |
| Sparse RGG ($p = c/n$) | $d \ll \log^3 n$ (triangles) | $d \gg \log^{36} n$ (BP + OT) | **Nearly tight** (conj: $\log^3 n$) |
| Anisotropic Gaussian RGG | $n^3 \gg (\|\alpha\|_2/\|\alpha\|_3)^6$ | same | **Tight** |
| $L^\infty$ torus RGG | signed 4-cycle optimal | — | **Resolved (low-degree)** |

---

## 4. The Simplicial Complex Extension — Open Problem

### 4.1 Problem Formulation

The direct analogue of the Bubeck problem for simplicial complexes:

**Null hypothesis $H_0$:** A 2-parameter complex (2PC) with parameters $(p, q)$:
- Each pair of vertices connected independently with probability $p$
- Each 3-cycle independently "filled" with probability $q$

**Alternative hypothesis $H_1$:** A random geometric simplicial complex (Čech or Rips) in ambient dimension $d$:
- Sample $n$ points uniformly in some space (sphere $\mathbb{S}^{d-1}$, flat torus $\mathbb{T}^d$, etc.)
- Connect pairs within distance $r$ (giving marginal edge probability $p$)
- Fill triangles according to the geometric rule (Čech: circumradius $\leq r/2$; Rips: all 3-cycles automatically filled, so $q=1$)

**Central question:** What is the phase transition in $d$ (as a function of $n, p$) for $\text{TV}(H_0, H_1)$?

### 4.2 Key Differences from the Graph Case

1. The closure property of simplicial complexes creates rich dependency structure between filled triangles absent in the graph edge case
2. The Wishart–GOE matrix comparison approach does not obviously generalize to adjacency tensors
3. The optimal test statistic is unclear — Bangachev–Bresler show that even in the graph case the optimal statistic depends on geometry ($L^2$ vs $L^\infty$)
4. Computational-statistical gaps (as in Dhawan–Mao–Wein) may appear
5. The parameter $q$ in the 2PC null must be matched to the geometric complex's filling probability, which requires non-trivial volume calculations

### 4.3 Status

**Entirely open** as of the literature survey (through early 2025). No paper has established a TV phase transition for the simplicial complex testing problem.

---

## 5. Goh (PRUV 2023) — Author's Own Work

*Title:* "Testing for Geometry in 2-Parameter Random Simplicial Complexes"  
*Advisor:* Nicholas Cook (Duke University)  
*Venue:* PRUV (Program for Research for Undergraduates and Visiting students), Sep 2023  
*Underlying space:* High-dimensional flat torus $\mathbb{T}^d$

### 5.1 Setup and Models

**2-Parameter Complex (2PC)** — the null model:
- $n$ vertices; each pair connected with probability $p \in [0,1]$
- Each resulting 3-cycle independently filled with probability $q \in [0,1]$
- Generalizes: Linial–Meshulam ($p=1$), flag complex ($q=1$)

**Čech Complex** — the geometric alternative:
- $n$ points in metric space with parameter $r$
- Edge $\{i,j\}$ if $d(i,j) \leq r$
- Filled triangle $\{i,j,k\}$ if the circumradius of triangle $\leq r/2$ (equivalently, $\bigcap_{i,j,k} B_{r/2}(i) \neq \emptyset$)

**Rips Complex** — an alternative geometric model:
- Same edge rule as Čech
- But every 3-cycle is automatically filled ($q=1$)
- Simpler but geometrically coarser than Čech

### 5.2 Matching Parameters Between Models

To test fairly, set the 2PC parameters to match the geometric complex.

**Matching $p$:** Normalize the ambient space volume to 1. Then $p = V_d(2r)$, the volume of a $d$-ball of radius $2r$. This gives $r = \frac{\Gamma(n/2+1)^{1/d}}{2\sqrt{\pi}} p^{1/d}$.

**Matching $q$ (Rips):** Trivial — $q = 1$.

**Matching $q$ (Čech):** Non-trivial. Given two connected vertices at separation $s$, define:
- $V_f(r,s)$: volume of the region where a third point must land to *fill* the triangle (Event F)
- $V_e(r,s)$: volume of the region where a third point must land to form an *empty* 3-cycle (Event E)

Then $q = \mathbb{E}[V_f] / \mathbb{E}[V_e]$, integrated over the distribution of $s$.

### 5.3 Volume Computations

**$[V_e]$ (two hyperspherical caps of radius $2r$, centers separated by $s$):**
$$[V_e] = V_d(2r) \cdot I_{\sin^2 \varphi}\!\left(\frac{d+1}{2}, \frac{1}{2}\right)$$
where $I_z(a,b)$ is the regularized incomplete Beta function and $\varphi = \arccos(s/2r)$.

**$[V_f]$ ($r$-neighborhood of the union of two small caps):**
$$[V_f] = 2\!\left(\int_0^{\sqrt{1-s^2/4}}\!\!\left(\sqrt{1-x^2} - \frac{s}{2}\right) S_{d-1}\,dx + \int_{0.5\sqrt{1-s^2}}^{0.5}\!\!\sqrt{0.25-x^2}\cdot S_{d-1}\,dx\right)$$
where $S_{d-1} = \frac{2\pi^{(d-1)/2} x^{d-2}}{\Gamma((d-1)/2)}$ is the surface area element of the $(d-1)$-sphere.

**PDF of separation $s$:** On the flat torus with unit volume, $\text{pdf}(s) = d \cdot s^{d-1}$.

**Main integral for $q$:**
$$q = \int_0^1 \frac{[V_f]}{[V_e]} \cdot d s^{d-1}\,ds$$

### 5.4 Expectation and Variance of Filled Triangle Count

**In 2PC:**
$$\mathbb{E}[\Delta_f] = \binom{n}{3} p^3 q, \qquad \operatorname{Var}[\Delta_f] = \binom{n}{3} p^3 q(1-p^3 q)$$

**In Čech complex:**

Let $\mathbb{E}[V_f]$ denote the expectation of $[V_f]$ over the distribution of $s$. Then:
$$\mathbb{E}[\Delta_f] = \binom{n}{3} p \cdot \mathbb{E}[V_f]$$
$$\operatorname{Var}[\Delta_f] = \binom{n}{3}\operatorname{Var}(I_f) + 12\binom{n}{4}\operatorname{Cov}(I_{f_1}, I_{f_2})$$
where the covariance is over pairs of triangles sharing exactly one edge (the only source of dependence), giving:
$$\operatorname{Cov}(I_{f_1}, I_{f_2}) = (p - p^2) \cdot \mathbb{E}[V_f]^2$$

**Comparative table (leading order):**

| | 2PC | Čech |
|---|---|---|
| $\mathbb{E}[\Delta_f]$ | $n^3 p^3 q$ | $n^3 p \cdot \square$ |
| $\operatorname{Var}[\Delta_f]$ | $n^3 p^3 q$ | $n^4 p \cdot \square^2$ |

where $\square = \mathbb{E}[V_f]$.

The **key structural observation**: the Čech variance is $O(n^4)$ while the 2PC variance is $O(n^3)$. Detection is possible when the gap in means dominates the noise:
$$\frac{n^3 p \mathbb{E}[V_f]}{n^4(p-p^2)\mathbb{E}[V_f]^2} = \frac{1}{n(1-p)\mathbb{E}[V_f]} \to \infty$$

and testing becomes impossible when $\frac{1}{n(1-p)\mathbb{E}[V_f]} \to 0$.

**The critical open step:** $\mathbb{E}[V_f]$ as a function of $p$ and $d$ has not been computed in closed form. Numerical evidence shows $q \to 0$ as $d \to \infty$, and that $\mathbb{E}[V_f]$ is defined only for dimensions below approximately $n_{\log p}$ (a logarithmic function of $p$).

### 5.5 Numerical Findings

- For $d=3$ with $q=0.757$: the Čech variance is numerically confirmed to be substantially larger than the 2PC variance, with the $n^4$ term dominating both
- The difference in expected filled triangle count $\binom{n}{3}(\mathbb{E}[V_f] - p^2)$ is visibly non-negligible for $d = 1, 2, 3, 4$
- $q$ is numerically decreasing in $d$

### 5.6 Stated Future Directions (from the paper)

1. **Derive leading-order asymptotics for $\mathbb{E}[V_f]$ in terms of $n, p, d$** — this would concretize the phase transition threshold for the filled triangle statistic
2. **Test on $\mathbb{S}^{d-1}$ (sphere) instead of flat torus** — more natural for comparison to BDER; requires different volume calculations
3. **Find better statistics:** the "flapwheel" substructure and the "skin of a tetrahedron" are mentioned as candidates with potentially greater power than filled triangles
4. **Signed version of the statistic** — not developed, but likely necessary for the indistinguishability direction by analogy with signed triangles in BDER

### 5.7 Assessment of the Work

**Strengths:**
- First direct attempt at the Bubeck-type testing problem for simplicial complexes
- Correct geometric setup: matching $(p,q)$ parameters between 2PC and Čech is the right first step
- The volume decomposition into $V_f$ and $V_e$ is clean and computable in principle
- The $n^4$ variance observation for the Čech complex is structurally analogous to the signed triangle variance inflation in RGGs

**Weaknesses / gaps:**
- Analysis restricted to flat torus; extension to $\mathbb{S}^{d-1}$ (the natural setting) is open
- The detection criterion is an informal SNR heuristic, not a TV lower bound in the BDER sense
- The "signed" version of the filled triangle statistic (subtracting the 2PC mean) is not developed; this is likely necessary for rigorous indistinguishability
- Closed-form asymptotics for $q(p,d)$ are absent; the actual phase transition threshold (analogue of $d \asymp n^3$) is not stated

---

## 6. Open Problems and Research Directions

### 6.1 Immediate (extending Goh 2023)
- Compute leading-order asymptotics for $q = q(p,d)$ on the flat torus — determine whether $q \sim d^{-\alpha}$ for some $\alpha$, or decays faster
- Extend to $\mathbb{S}^{d-1}$ — the sphere requires a different PDF for separation $s$ (related to Gegenbauer/Legendre polynomials)
- Formalize the detection lower bound as a TV statement
- Develop the signed filled triangle statistic and compute its variance under both models

### 6.2 Medium-term
- Determine the phase transition threshold $d^*(n,p)$ for the Čech/Rips complex — is it $n^3$ (like the graph case), or something different due to the stronger geometric constraints for simplex formation?
- Investigate flapwheel and tetrahedron-skin statistics — motivated by the Bangachev–Bresler result that the optimal substructure depends on the geometry
- Indistinguishability direction — the Wishart–GOE method doesn't obviously generalize; a tensor analogue may be needed

### 6.3 Long-term
- Full characterization of the TV phase transition for random geometric simplicial complexes at all dimensions and densities
- Computational-statistical gaps: is there a regime where information-theoretically detection is possible but computationally hard? (Motivated by Dhawan–Mao–Wein for hypergraphs)
- Extension to higher-dimensional simplices ($k$-simplices for $k \geq 3$)
- Connection to TDA: does geometry detectability relate to persistence of homological features?

---

## 7. Key Notation Reference

| Symbol | Meaning |
|---|---|
| $G(n,p)$ | Erdős–Rényi graph |
| $G(n,p,d)$ | Random geometric graph on $\mathbb{S}^{d-1}$ |
| $\text{TV}(\mu,\nu)$ | Total variation distance |
| $\tau(G)$ | Signed triangle count $= \operatorname{Tr}((A-p(J-I))^3)$ |
| 2PC$(p,q)$ | 2-parameter simplicial complex |
| Čech$(r,d)$ | Čech complex with parameter $r$ in $\mathbb{R}^d$ / $\mathbb{T}^d$ |
| Rips$(r,d)$ | Rips complex (all 3-cycles filled, $q=1$) |
| $\Delta_f$ | Count of filled triangles |
| $V_f, V_e$ | Volumes of "fill" and "empty 3-cycle" regions |
| $q$ | 3-cycle-filling probability ($= V_f / V_e$ in Čech) |
| $S_{d-1}$ | Surface area element of $(d-1)$-sphere |
| $I_z(a,b)$ | Regularized incomplete Beta function |

---

## 8. Instructions for Continuing Claude Instance

You are receiving this document as a research handoff. The goal is to continue the literature review and mathematical development of the testing-for-geometry problem for random simplicial complexes.

**What has been done:**
- Full survey of the graph case literature (BDER 2016 through Bangachev–Bresler 2025)
- Detailed analysis of Goh (PRUV 2023), the first work on the simplicial complex case
- Identification of open problems at all levels

**What to do next:**
1. Search for any papers citing BDER (2016) or Liu et al. (2022) that address simplicial complexes or hypergraphs — the field moves fast and there may be 2024–2025 work not captured here
2. Investigate the integral $\mathbb{E}[V_f] = \int_0^1 [V_f(r,t)] \cdot 2t \,dt$ more carefully — a Laplace method or steepest descent argument as $d \to \infty$ may yield the asymptotics
3. Look into whether the Bangachev–Bresler algebraic graph framework (random algebraic graphs, STOC 2024/RSA 2025) extends naturally to simplicial complexes via Fourier analysis on groups
4. The key papers to find and read are: any 2024–2025 work by Goh and Cook, and any work on the "random flag complex" testing problem

**Tone and context:** The user is a Master's student in Applied Computing (Applied Mathematics) at the University of Toronto, familiar with probability theory, random matrix theory, and high-dimensional geometry at a graduate level.
