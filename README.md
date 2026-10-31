
# Lanzarini Krylov-Jacobi

## Lean 4 Formalization of Finite-Dimensional Jacobi Dynamics

**Author:** Valentino Lanzarini  
**Affiliation:** Independent Mathematical Researcher  
**Project status:** Research in progress  
**Latest CI-verified checkpoint on development branch `research/p75-centered-derivative`:** **P82.3** (Lean 4 Verification #225, commit `65e4762`)  
**Latest development candidate:** **P82.4a** (commit `a4c1c46`; not yet included in the main CI compilation and theorem audit)  
**Latest verified checkpoint on `main`:** **P74.2**  
**Development branch:** [`research/p75-centered-derivative`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/research/p75-centered-derivative)  
**Lean:** v4.24.0  
**mathlib:** v4.24.0  
**Documentation status date:** 31 October 2026

**Research preprint:** [Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics](https://doi.org/10.5281/zenodo.23163367)  
**Repository:** [lanzarini-krylov-lean.](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)  
**Verification workflow:** [Lean 4 Verification](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml)

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**

---

## Research Mission: From the Preprint to Formal Mathematical Verification

**Research preprint:** [Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics](https://doi.org/10.5281/zenodo.23163367)

### Scientific question

**How do the local coefficients of a Jacobi Hamiltonian determine whether Krylov complexity saturates its quantum speed limit, and how does the system depart from saturation at short times?**

This repository develops a Lean 4 formalization of the mathematical structures investigated in the associated preprint. The goal is not merely to formalize a known speed-limit inequality, but to examine the **short-time saturation deficit**, its leading coefficients, its local Jacobi defect structure, and finite-chain boundary behavior.

### Mathematical strategy

For a finite real symmetric Jacobi Hamiltonian $H$, consider the physical evolution

$$
\psi(t)=e^{-itH}\psi_0.
$$

In the encoded finite coordinate basis, define the Krylov number operator $N$ and the observables

$$
K(t)=\langle\psi(t),N\psi(t)\rangle,
\qquad
V_K(t)=\langle\psi(t),N^2\psi(t)\rangle-K(t)^2.
$$

A foundational energy-variance speed limit is

$$
(K'(t))^2\le 4V_K(t)V_H(t).
$$

For the relevant initial-state specialization, the proposed saturation deficit is

$$
D(t)=1-\frac{[K'(t)]^2}{4b_1^2V_K(t)},
$$

where the denominator must be strictly positive. The research aims to derive the leading short-time behavior directly from physical evolution, without assuming the coefficient to be proved.

### Verified progress and current boundary

The recorded Lean development includes physical evolution and complexity derivatives (P73–P74), centered-state and speed-limit identities (P75–P76), energy conservation and residual identities (P77–P78), algebraic jets and physical Gram bridges (P79–P81), and physical evolution jets and observables (P82.2–P82.3).

**Latest recorded CI-verified checkpoint on `research/p75-centered-derivative`: P82.3 (not merged into `main`).** The P82.4a physical residual is a **candidate awaiting explicit CI compilation and axiom auditing**. Development-branch verification must not be confused with integration into `main`.

### Open mathematical target

For the four-site Jacobi model detailed in Section 6, set

$$
\Omega_0=s^2-3q^2+3p^2.
$$

The proposed short-time result is

$$
\boxed{\lim_{t\to0}\frac{D(t)}{t^6}
=\frac{q^2}{576}\left(4\Omega_0^2+s^2\delta^2\right)}.
$$

**This is a research target, not yet a Lean-verified theorem about the physical evolution.** Establishing it requires the lower-order derivative cancellations, the exact physical coefficient, positivity of the denominator, and the normalized limit. Further work concerns the general local-defect hierarchy, finite-chain terminal cases, and extensions beyond finite dimension.

### Why formal verification?

Lean 4 makes theorem statements, assumptions, and proof dependencies explicit and independently inspectable. Successful compilation and axiom auditing support the precise encoded statements; they do **not** establish mathematical novelty, general equivalence with the intended physical interpretation, or independent peer review.

**Scientific objective:** Build a formally verified mathematical foundation for the Krylov speed-limit saturation and local-defect results investigated in the preprint, while clearly distinguishing established theorems from open research objectives.

**[Preprint DOI](https://doi.org/10.5281/zenodo.23163367)** · **[Source code](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)** · **[Lean verification workflow](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml)**

---

## 1. Scientific Status

This repository develops Lean 4 formalizations of finite-dimensional real Jacobi dynamics, quantum evolution, Krylov observables, variance inequalities, physical derivatives, and related residual identities.

The latest **CI-verified checkpoint on the development branch `research/p75-centered-derivative`** is **P82.3**, supported by successful GitHub Actions **Lean 4 Verification #225** at commit [`65e4762`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/65e4762). The recorded workflow compiled `P82_3_PhysicalObservables.lean` and audited its four specified declarations. Their reported dependencies were limited to `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.

The subsequently added [`P82_4a_PhysicalResidual.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P82_4a_PhysicalResidual.lean) introduces a physical R0 speed-residual candidate. GitHub Actions **#226** succeeded at commit [`a4c1c46`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/a4c1c46), but the inspected workflow compiles only through P82.3. **That green run is not evidence that P82.4a compiled or passed an axiom audit.**

The latest verified checkpoint integrated into `main` is **P74.2**. Later development-branch results must not be described as merged into `main` without an independently checked merge and verification run.

The physical eighth-order residual coefficient and the normalized sixth-order saturation-deficit limit are **not yet established as Lean theorems**. The repository does not establish the mathematical novelty of the preprint or constitute independent peer review.

---

## 2. Mathematical Framework

Let $H$ be a finite real symmetric Jacobi Hamiltonian, with real diagonal entries and nearest-neighbor off-diagonal couplings. The physical evolution is

$$
\psi(t)=e^{-itH}\psi_0,
\qquad
\dot{\psi}(t)=-iH\psi(t).
$$

The Krylov number operator in the encoded finite index basis is

$$
N=\operatorname{diag}(0,1,\ldots,n-1).
$$

For a normalized state, the intended observables are

$$
K(t)=\langle\psi(t),N\psi(t)\rangle,
$$

$$
V_K(t)=\langle\psi(t),N^2\psi(t)\rangle-K(t)^2,
$$

$$
E(t)=\langle\psi(t),H\psi(t)\rangle,
\qquad
V_H(t)=\|(H-E(t)I)\psi(t)\|^2.
$$

These equations give the intended mathematical interpretation; the actual Lean definitions and theorem hypotheses determine the formal scope.

**Basis-identification limitation:** the encoded number operator acts in the finite `Fin n` coordinate basis. The repository has not established a general theorem identifying that basis with the Lanczos basis for an arbitrary Hamiltonian and initial state.

**Dimensional limitation:** the current verified development is finite-dimensional. No general semi-infinite or unbounded-operator theorem follows from these files.

---

## 3. Formal Verification History

The following table distinguishes historical milestones, development-branch theorems, and the current unverified candidate. “Verified” refers to the specific recorded CI compilation and axiom audits, not to an independent assessment of the preprint's originality.

| Checkpoint | Formalization or result | Evidence status |
| --- | --- | --- |
| P51–P55 | Jacobi Hamiltonians and unitary evolution | Earlier development history |
| P56–P64 | Krylov observables, moments, and variance | Earlier development history |
| P65–P69 | Complex Gram and Lagrange identities | Earlier development history |
| P70 | Real-part Gram-gap identity | Earlier development history |
| P71 | Centered-state variance identity | Historical CI record |
| P72 | Complexity differentiation and matrix exponential derivatives | Historical CI record |
| P73.1 | Physical propagator derivative | Historical CI record |
| P73.2 | Physical evolved-state derivative | Historical CI record |
| P74.1 | Componentwise state derivatives | Audited in #225 |
| P74.2 | Physical Krylov complexity derivative | Audited in #225; last verified `main` checkpoint |
| P75.1 | Centered-state orthogonality | Audited in #225 |
| P75.2a | Physical velocity orthogonality | Audited in #225 |
| P75.2b | Centered physical complexity derivative | Audited in #225 |
| P75.3 | Quadratic speed estimate | Audited in #225 |
| P75.4 | Physical derivative speed bound | Audited in #225 |
| P76.1 | Energy variance nonnegativity | Audited in #225 |
| P76.2 | Energy variance identities | Audited in #225 |
| P76.3 | Energy second-moment representation | Audited in #225 |
| P76.4 | Centered energy orthogonality | Audited in #225 |
| P76.5 | Centered velocity inner-product identity | Audited in #225 |
| P76.5b | Centered velocity norm identity | Audited in #225 |
| P76.6 | Energy-variance speed bound | Audited in #225; earlier #159 success |
| P77.1a | Jacobi Hamiltonian and propagator commutation | Audited in #225 |
| P77.1b | Hamiltonian intertwining with physical evolution | Audited in #225 |
| P77.2 | Energy-pair and energy-mean conservation | Audited in #225 |
| P78.1 | Exact speed-residual identity and nonnegativity | Audited in #225 |
| P78.2 | Physical speed-channel derivative and residual identity | Audited in #225 |
| P79 R0 | Algebraic minor, Gram-jet, and deficit-jet identities | Audited in #225; not the physical coefficient derivation |
| P80.1 | Iterated physical-evolution derivatives | Audited in #225 |
| P81.1 | Physical Jacobi powers $H^1$ through $H^4$ and initial derivatives | Audited in #225 |
| P81.2a | Physical Gram bridge and product rule | Audited in #225 |
| P81.2b | Initial physical state and observable data | Audited in #225 |
| P81.2b1 | Physical acceleration | Audited in #225 |
| P81.2b2 | Physical raw-minor derivative | Audited in #225 |
| P81.2b3 | Physical Krylov derivative bridge | Audited in #225 |
| P81.2b3b | Centered-minor decomposition | Audited in #225 |
| P82.2 | Physical evolution jets | Audited in #225 |
| P82 NormSqProbe | Complex norm-square derivative lemma | Audited in #225 |
| **P82.3** | Physical second moment and variance: zero values and first derivatives | **Latest audited development-branch checkpoint: #225** |
| **P82.4a** | Physical R0 residual definition, derivative bridge, and zero-value candidate | **Not yet compiled or audited by the inspected main workflow** |

The verified development results beyond P74.2 are recorded on `research/p75-centered-derivative`, not asserted here to be integrated into `main`.

---

## 4. Foundational Energy-Variance Speed Limit: P76.6

The theorem [`Lanzarini.p76_6_energy_speed_limit`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P76_6_EnergySpeedLimit.lean) establishes, under its encoded finite-dimensional and normalization assumptions, the physical derivative and a variance-based bound:

$$
(K'(t))^2\le 4V_K(t)V_H(t).
$$

Equivalently, for nonnegative variances,

$$
|K'(t)|\le 2\sqrt{V_K(t)V_H(t)}.
$$

The proof builds on physical differentiation, centered states, Gram inequalities, centered energy, physical velocity, and energy-variance identities. The desired inequality is not introduced as an assumption.

This is a formalization of a variance-based speed-limit result, **not** a claim to have discovered a new universal physical law.

---

## 5. Physical Evolution, Gram Bridges, and Observables: P77–P82.3

### 5.1. Conservation and physical residuals: P77–P78

The development includes Hamiltonian–propagator commutation, Hamiltonian intertwining, energy conservation, and exact physical speed-residual identities:

- [`P77_1a_PropagatorCommutes.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P77_1a_PropagatorCommutes.lean)
- [`P77_1b_HamiltonianIntertwining.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P77_1b_HamiltonianIntertwining.lean)
- [`P77_2_EnergyMeanConservation.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P77_2_EnergyMeanConservation.lean)
- [`P78_1_ExactSpeedResidual.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P78_1_ExactSpeedResidual.lean)
- [`P78_2_PhysicalSpeedResidual.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P78_2_PhysicalSpeedResidual.lean)

These identities are useful prerequisites; they do not themselves prove the required short-time coefficient.

### 5.2. Algebraic jets versus physical jets: P79–P81

[`P79_R0_CoefficientJet.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P79_R0_CoefficientJet.lean) contains audited algebraic formulas for R0 minors, a Gram jet, and a deficit jet. Those formulas must **not** be treated as a substitute for deriving the coefficient from the actual evolved state.

[`P80_1_TrueEvolutionJets.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P80_1_TrueEvolutionJets.lean) formalizes iterated physical derivatives. The P81 series establishes Hamiltonian powers, initial derivatives, physical Gram bridges, acceleration, raw-minor differentiation, and centered-minor decomposition.

### 5.3. Physical observables: P82.2 and P82.3

- [`P82_2_PhysicalJets.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P82_2_PhysicalJets.lean): physical state jets and their initial values.
- [`P82_NormSqProbe.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P82_NormSqProbe.lean): a complex norm-square derivative lemma.
- [`P82_3_PhysicalObservables.lean`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/P82_3_PhysicalObservables.lean): initial values and first derivatives for the physical second moment and variance.

The four P82.3 declarations audited in #225 are:

    Lanzarini.p82_3_M2_zero
    Lanzarini.p82_3_V_zero
    Lanzarini.p82_3_M2_hasDerivAt
    Lanzarini.p82_3_V_hasDerivAt

Each was reported with only the three standard Lean axioms listed in Section 7.

### 5.4. Physical R0 speed-residual candidate: P82.4a

At commit [`a4c1c46`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/a4c1c46), `P82_4a_PhysicalResidual.lean` introduced:

    p82_4a_Kdot
    p82_4a_F
    p82_4a_K_derivative
    p82_4a_F_identity
    p82_4a_F_zero

The candidate defines the physical residual by

$$
F(t)=4p^2V_K(t)-[K'(t)]^2,
$$

where the proposed `Kdot` expression is built from the evolved state and physical velocity. Its source does not import the P79 coefficient formula.

**Verification boundary:** successful run #226 did not include this file in its module loop or required-theorem audit. Its definitions and theorems therefore remain **pending explicit CI verification**. In particular, a zero-value candidate is not a proof of cancellation through order seven or of the order-eight coefficient.

---

## 6. R0 Model and Outstanding Short-Time Coefficient

The four-site Jacobi model under study is

$$
H=\begin{pmatrix}
0&p&0&0\\
p&0&q&0\\
0&q&0&s\\
0&0&s&\delta
\end{pmatrix},
\qquad
\psi_0=e_0,
\qquad
N=\operatorname{diag}(0,1,2,3).
$$

Let

$$
K(t)=\sum_{j=0}^{3}j|\psi_j(t)|^2,
\qquad
V_K(t)=\sum_{j=0}^{3}j^2|\psi_j(t)|^2-K(t)^2,
$$

$$
F(t)=4p^2V_K(t)-[K'(t)]^2,
\qquad
D(t)=\frac{F(t)}{4p^2V_K(t)}
$$

where the denominator is strictly positive. Define

$$
\Omega_0=s^2-3q^2+3p^2.
$$

**Research target, not yet a Lean-certified theorem:** under suitable explicit coupling and regularity assumptions, derive from the physical evolution

$$
F^{(k)}(0)=0\quad(0\le k\le7),
$$

$$
\frac{F^{(8)}(0)}{8!}
=\frac{p^4q^2}{144}\left(4\Omega_0^2+s^2\delta^2\right),
$$

and then justify

$$
\lim_{t\to0}\frac{V_K(t)}{t^2}=p^2,
\qquad
\lim_{t\to0}\frac{D(t)}{t^6}
=\frac{q^2}{576}\left(4\Omega_0^2+s^2\delta^2\right).
$$

The derivation must establish the needed positivity for nonzero sufficiently small $t$, avoid circular use of the target coefficient, and treat degeneracies and terminal cases separately. The displayed coefficient is a **candidate under investigation**, not an independently certified mathematical discovery.

---

## 7. Lean Verification Evidence and Axiom Audit

### 7.1. Verified development checkpoint: P82.3

GitHub Actions **Lean 4 Verification #225**, on the development branch `research/p75-centered-derivative`, commit [`65e4762`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/65e4762), completed successfully. The supplied CI log shows compilation through P82.3 and a required-theorem audit concluding:

    PASS p82_normSq_probe: ['Classical.choice', 'Quot.sound', 'propext']
    PASS p82_3_M2_zero: ['Classical.choice', 'Quot.sound', 'propext']
    PASS p82_3_V_zero: ['Classical.choice', 'Quot.sound', 'propext']
    PASS p82_3_M2_hasDerivAt: ['Classical.choice', 'Quot.sound', 'propext']
    PASS p82_3_V_hasDerivAt: ['Classical.choice', 'Quot.sound', 'propext']
    All required theorem axiom audits passed.

The standard reported axioms were:

    propext
    Classical.choice
    Quot.sound

The recorded required-theorem audit did not report `sorryAx` for these declarations. This is evidence about the audited declarations and recorded run, not a blanket guarantee about every possible statement or branch state.

### 7.2. P82.4a status and next verification gate

Run **#226** succeeded at commit [`a4c1c46`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/a4c1c46), but the inspected [`lean.yml`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/.github/workflows/lean.yml) ended its compilation and source-audit lists at `P82_3_PhysicalObservables`.

Before claiming P82.4a is verified, a new run must:

1. Explicitly compile `P82_4a_PhysicalResidual.lean`.
2. Include it in the forbidden-placeholder/source audit.
3. Require axiom output for `p82_4a_K_derivative`, `p82_4a_F_identity`, and `p82_4a_F_zero`.
4. Reject unexpected axioms, including `sorryAx`.
5. Finish successfully on the exact commit being reported.

Only after this gate should the README's latest verified development-branch checkpoint be advanced to P82.4a. This does not imply a merge into `main`.

### 7.3. Limits of CI evidence

A successful Lean compilation verifies the encoded theorem relative to its dependencies. It does **not** establish novelty, independent peer review, the equivalence of all encoded objects with the intended physics, or completion of the preprint.

---

## 8. Reproducibility and Verification Records

The project specifies:

    Lean 4: v4.24.0
    mathlib: v4.24.0

Relevant files include [`lean-toolchain`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/lean-toolchain), [`lakefile.toml`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/lakefile.toml), and [`.github/workflows/lean.yml`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./blob/research/p75-centered-derivative/.github/workflows/lean.yml).

The workflow resolves mathlib dependencies using `lake update` and retrieves the cache. A previously identified reproducibility limitation was the absence of a committed `lake-manifest.json` at the P76.6 audit checkpoint. A dependency lockfile and an exact commit remain important for independently repeating the result; the lockfile's status at later commits should be checked rather than assumed.

Selected historical records:

| Milestone | GitHub Actions record |
| --- | --- |
| P71 | [Run 39044208215](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) |
| P72.3a | [Run 39140660849](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849) |
| P73.1 | [Run 39153415923](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923) |
| P73.2 | [Run 39248613293](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293) |
| P74.2 | [Run 39399857938](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) |
| P76.6 | [Run 40004543470](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470) |
| P82.3 | [Verification #225 / workflow](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml), development-branch commit [`65e4762`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/65e4762) |
| P82.4a candidate | [Verification #226 / workflow](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml), commit [`a4c1c46`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/a4c1c46); **module not included** |

The intended integration commit should be reviewed and verified before merging development changes into `main`.

---

## 9. Remaining Mathematical Research

### 9.1. Physical eighth-order coefficient

The decisive next task is to extract the eighth-order physical speed-residual coefficient from derivatives of the actual evolved state and prove all lower-order cancellations. The P79 algebraic coefficient formula must not be imported as the desired conclusion.

### 9.2. Positive denominator and normalized deficit

For the first coupling $b_1$, the proposed saturation deficit is

$$
D(t)=1-\frac{[K'(t)]^2}{4b_1^2V_K(t)},
$$

only where the denominator is nonzero. The positive-denominator argument and the normalized limit must be proved, not inferred merely from a formal quotient.

### 9.3. Finite-depth local defects

Using the preprint's indexing convention,

$$
c_j=b_j^2,\qquad c_0=0,
$$

$$
\Omega_r=c_{r+3}-3c_{r+2}+3c_{r+1}-c_r,
\qquad
\delta_r=a_{r+3}-a_0.
$$

The proposed hierarchy requires explicit prefix assumptions, correct coupling indices, finite-chain boundary conventions, positivity conditions, exact leading coefficients, remainder bounds, and independent verification. None of these conclusions follows from P76.6 alone.

### 9.4. Finite-chain rigidity and terminal cases

Rigidity claims and terminal boundary cases require their own statements and proofs. Nonterminal formulas must not be extended to terminal chains without justification.

### 9.5. Semi-infinite Jacobi dynamics and Lanczos equivalence

Extensions to semi-infinite, potentially unbounded Jacobi operators require additional operator-theoretic hypotheses. General equivalence with a Lanczos basis is also not established by the current finite-coordinate formalization.

---

## 10. Research Preprint and Scientific Interpretation

**Title:** *Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics*  
**Author:** Valentino Lanzarini  
**DOI:** [10.5281/zenodo.23163367](https://doi.org/10.5281/zenodo.23163367)

The preprint and the Lean repository are distinct scientific artifacts. Verified Lean lemmas support precisely their encoded statements; they do not automatically establish every theorem, hypothesis, coefficient, or interpretation in the preprint.

In particular, the full local-defect hierarchy, physical eighth-order residual coefficient, normalized sixth-order deficit limit, terminal rigidity results, and semi-infinite extensions are not presented here as completed Lean formalizations.

Claims of novelty and priority require independent literature comparison and specialist evaluation.

---

## 11. Scientific Integrity

The project follows these principles:

1. No fabricated numerical, symbolic, or Lean verification results.
2. No `sorry` or `admit` in claimed completed proofs.
3. No new axioms that simply assert the desired conclusion.
4. No weakening of statements solely to obtain a green CI run.
5. No claim that a module is verified unless the recorded workflow actually compiled and audited it.
6. Explicit distinction among numerical checks, symbolic computations, Lean proofs, and external peer review.
7. Reproducible source commits and accessible verification records.
8. No unsupported claims of originality, priority, or universal validity.
9. Independent checking of the correspondence between the encoded theorem and the intended mathematical statement.
10. No changes to the published preprint or verified `main` branch solely on the basis of an unverified development candidate.

---

## 12. Copyright and Permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Third-party dependencies remain subject to their respective licenses.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas, or theorems.

---

## 13. AI-Assisted Research and Author

Artificial intelligence tools have assisted the development, checking, and formalization of this project. AI assistance does not constitute independent peer review. The author remains responsible for reviewing mathematical claims, code, documentation, and scientific conclusions.

Formal verification and independent scientific evaluation are complementary but distinct processes.

**Valentino Lanzarini**  
Independent Mathematical Researcher  
Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Preprint:** https://doi.org/10.5281/zenodo.23163367  
**Repository:** https://github.com/vlanzarini80-source/lanzarini-krylov-lean.  
**Verification workflow:** https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**
