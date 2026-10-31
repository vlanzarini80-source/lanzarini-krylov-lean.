
# Lanzarini Krylov-Jacobi

## Lean 4 Formalization of Finite-Dimensional Jacobi Dynamics

**Author:** Valentino Lanzarini  
**Affiliation:** Independent Mathematical Researcher  
**Project status:** Research in progress  
**Latest verified development checkpoint:** P82.3
**Latest candidate awaiting CI verification:** P82.4a
**Latest checkpoint on main:** P74.2  
**Lean:** v4.24.0  
**mathlib:** v4.24.0  
**Date of audit:** 23 October 2026

**Research preprint:**  
https://doi.org/10.5281/zenodo.23163367


**Repository:** [GitHub repository](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)


**Copyright © 2026 Valentino Lanzarini. All rights reserved.**

---

## 1. Scientific Status

This repository contains a Lean 4 formalization of finite-dimensional real Jacobi dynamics, unitary quantum evolution, Krylov observables, and related variance inequalities.

The latest verified development milestone is **P76.6**, established on the branch:

`research/p75-centered-derivative`

The corresponding GitHub Actions verification is:

**Run #159: SUCCESS**

https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470

Verified commit:

`178b6a0f57c18708ac0818b76d411fc630311969`

The latest verified checkpoint integrated into `main` is P74.2.

**P76.6 has not yet been merged into main.**

The formal development does not establish the novelty of the preprint's local-defect hierarchy, nor does it constitute independent peer review.

---

## 2. Mathematical Framework

Consider a finite real symmetric Jacobi Hamiltonian H.

Its diagonal coefficients are real numbers, and its off-diagonal coefficients couple adjacent sites.

The corresponding quantum evolution is:

$$
\psi(t)=e^{-itH}\psi_0.
$$

The state satisfies:

$$
\dot{\psi}(t)=-iH\psi(t).
$$

The Krylov number operator is the diagonal matrix:

$$
N=\mathrm{diag}(0,1,\ldots,n-1).
$$

For a normalized state, Krylov complexity is:

$$
K(t)=\langle\psi(t),N\psi(t)\rangle.
$$

The Krylov variance is:

$$
V_K(t)=
\langle\psi(t),N^2\psi(t)\rangle
-K(t)^2.
$$

The energy expectation is:

$$
E(t)=\langle\psi(t),H\psi(t)\rangle.
$$

The energy variance is:

$$
V_H(t)=
\|(H-E(t)I)\psi(t)\|^2.
$$

These formulas describe the intended mathematical interpretation. The exact Lean definitions and hypotheses determine the formal scope.

The current development concerns finite-dimensional Jacobi matrices.

It does not establish a general infinite-dimensional result or a Lanczos basis-equivalence theorem for arbitrary Hamiltonians.

---

## 3. Formal Verification History

The development has progressed through the following milestones.

| Checkpoint | Main result |
| --- | --- |
| P51-P55 | Jacobi Hamiltonians and unitary evolution |
| P56-P64 | Krylov observables, moments, and variance |
| P65-P69 | Complex Gram and Lagrange identities |
| P70 | Real-part Gram-gap identity |
| P71 | Centered-state variance identity |
| P72 | Complexity differentiation and matrix exponential derivatives |
| P73.1 | Physical propagator derivative |
| P73.2 | Physical evolved-state derivative |
| P74.1 | Componentwise state derivatives |
| P74.2 | Physical Krylov complexity derivative |
| P75.1 | Centered-state orthogonality |
| P75.2a | Physical velocity orthogonality |
| P75.2b | Centered physical complexity derivative |
| P75.3 | Quadratic speed estimate |
| P75.4 | Physical derivative speed bound |
| P76.1 | Energy variance definition |
| P76.2 | Energy variance identities |
| P76.3 | Energy second-moment representation |
| P76.4 | Centered energy orthogonality |
| P76.5 | Centered velocity inner-product identity |
| P76.5b | Centered velocity norm identity |
| P76.6 | Complete energy-variance speed bound |

P75 and P76 are verified on the development branch.

They are not yet part of the verified main branch.

---

## 4. Main Development Result: P76.6

The verified Lean theorem is:

`Lanzarini.p76_6_energy_speed_limit`

Source file:

`P76_6_EnergySpeedLimit.lean`

The theorem assumes a finite-dimensional Jacobi evolution and a normalized initial state.

It establishes the existence of the physical derivative of Krylov complexity and proves the quadratic energy-variance bound.

In mathematical notation:

$$
|K'(t)|^2
\leq
4V_K(t)V_H(t).
$$

Equivalently:

$$
|K'(t)|
\leq
2\sqrt{V_K(t)V_H(t)}.
$$

The proof uses previously established results concerning:

- Physical Krylov complexity differentiation.
- Centered Krylov states.
- Complex Gram inequalities.
- Centered energy.
- Physical velocity.
- Energy variance.

The desired inequality is not introduced as an assumption.

This is a formalization of a classical type of variance-based speed limit.

It is not presented as a newly discovered universal physical law.

---

## 5. Lean Verification Evidence

GitHub Actions run #159 completed successfully on 23 October 2026.

The verification workflow explicitly compiled:

`P76_6_EnergySpeedLimit.lean`

The recorded axiom audit for the final theorem was:

```text
'Lanzarini.p76_6_energy_speed_limit'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency was reported for this theorem.

The workflow also checked the earlier declarations included in its verification sequence.

This establishes that the formal theorem compiled under the recorded Lean environment and depends only on the listed axioms.

It does not establish:

- Mathematical originality.
- Independent peer review.
- Correctness of every informal interpretation.
- Formal verification of the entire preprint.
- Validity of an unproved infinite-dimensional extension.

---

## 6. Reproducibility

The project uses:

```text
Lean 4: v4.24.0
mathlib: v4.24.0
```

The repository contains:

```text
lean-toolchain
lakefile.toml
.github/workflows/lean.yml
```

The GitHub Actions workflow installs the Lean environment, resolves dependencies, and compiles the required source files.

At the audited P76.6 commit, no committed `lake-manifest.json` was present.

A reviewed dependency lockfile would improve reproducibility.

The exact source commit and successful CI logs are the authoritative verification records.

---

## 7. Remaining Mathematical Research

### 7.1. Initial-state speed limit

The next objective is to specialize the energy-variance speed limit to the initial-state assumptions used in the preprint.

This requires the appropriate energy conservation and first-coupling identities.

The specialization must preserve all necessary normalization, dimension, and coupling hypotheses.

### 7.2. Saturation deficit

For the first physical coupling b_1, the proposed saturation deficit is:

$$
D(t)=
1-\frac{K'(t)^2}
{4b_1^2V_K(t)}.
$$

The denominator must be nonzero wherever this expression is used.

The behavior near zero variance requires a separate mathematical treatment.

The nonnegativity and short-time expansion of this deficit are not yet established as Lean theorems.

### 7.3. Finite-depth local defects

In the preprint's indexing convention, define:

$$
c_j=b_j^2.
$$

With the boundary convention:

$$
c_0=0.
$$

The off-diagonal defect is:

$$
\Omega_r=
c_{r+3}-3c_{r+2}
+3c_{r+1}-c_r.
$$

The diagonal defect is:

$$
\delta_r=a_{r+3}-a_0.
$$

The proposed hierarchy relates the first nonzero saturation-deficit coefficient to these two defect mechanisms.

Its mathematical treatment requires:

- Explicit prefix assumptions.
- Correct coupling-index conventions.
- Finite-chain boundary conditions.
- Positivity hypotheses where necessary.
- Exact leading coefficients.
- Rigorous remainder estimates.
- Independent mathematical verification.

These results are not consequences of P76.6 alone.

### 7.4. Finite-chain rigidity

The proposed rigidity results require separate proofs.

Terminal boundary cases must be treated explicitly.

### 7.5. Semi-infinite Jacobi dynamics

The existing finite-dimensional results do not establish corresponding theorems for unbounded semi-infinite Jacobi operators.

Such extensions require additional operator-theoretic assumptions and proofs.

---

## 8. Verification Records

Selected historical records:

**P71:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215

**P72.3a:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849

**P73.1:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923

**P73.2:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293

**P74.2:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938

**P76.6:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470

The development branch must be merged into main only after review and successful verification of the intended integration commit.

---

## 9. Research Preprint

**Title:**  
Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics

**Author:**  
Valentino Lanzarini

**DOI:**  
https://doi.org/10.5281/zenodo.23163367

The preprint and the Lean formalization are separate scientific artifacts.

The Lean repository currently verifies foundational results through the energy-variance speed bound.

The complete local-defect hierarchy remains a research objective.

The project does not claim that GitHub Actions, AI assistance, or formal verification establish worldwide mathematical novelty.

Independent literature comparison and specialist review remain necessary.

---

## 10. Scientific Integrity

The project follows these principles:

1. No fabricated experimental or verification results.
2. No `sorry` or `admit` in claimed completed proofs.
3. No artificial axioms asserting the desired conclusion.
4. No weakening of theorem statements to obtain a successful compilation.
5. Explicit distinction between development and main-branch verification.
6. Reproducible source commits and verification records.
7. No unsupported originality or priority claims.
8. Independent review of the correspondence between formal and informal mathematics.

A Lean verification establishes that the encoded statement follows from its formal foundations.

It does not independently establish the novelty of the mathematical statement.

---

## 11. Copyright and Permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Third-party dependencies remain subject to their respective licenses.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas, or theorems.

---

## 12. AI-Assisted Research

Artificial intelligence tools have assisted the development and formalization of this project.

AI assistance does not constitute independent peer review.

The author remains responsible for reviewing mathematical claims, documentation, and scientific conclusions.

Formal verification and independent scientific evaluation are complementary but distinct processes.

---

Development Checkpoint — 31 October 2026

Branch: "research/p75-centered-derivative"

P82.3 — Verified Physical Observables

GitHub Actions Lean 4 Verification #225 completed successfully at commit "65e4762".

The verification workflow compiled "P82_3_PhysicalObservables.lean", including the initial-value and first-derivative theorems for the physical second moment and Krylov variance.

The reported theorem dependencies were limited to the standard Lean axioms:

- "propext"
- "Classical.choice"
- "Quot.sound"

No "sorryAx" dependencies were reported for the audited P82.3 declarations.

P82.4a — Physical Speed Residual Candidate

The file "P82_4a_PhysicalResidual.lean" was introduced at commit "a4c1c46".

GitHub Actions Verification #226 completed successfully. However, the workflow did not explicitly compile or audit this new module.

Consequently, P82.4a must not yet be described as formally verified.

Outstanding Mathematical Objectives

The next formalization stages are:

1. Derive the eighth-order coefficient of the physical R0 speed residual directly from finite-dimensional Jacobi evolution.
2. Establish the required lower-order cancellations without assuming the target coefficient.
3. Prove positivity of the normalization denominator in a suitable punctured neighborhood of zero.
4. Establish the normalized sixth-order short-time saturation-deficit limit.
5. Extend the verified analysis to higher defect depths and finite-chain terminal cases.

The algebraic coefficient identities developed in P79 must remain logically distinct from the physical-evolution derivation.

Scientific Status and Limitations

Lean verification establishes the correctness of the formal statements under their explicitly encoded assumptions.

It does not independently establish the mathematical novelty of the results, equivalence with every statement in the associated preprint, or external peer review.

The complete eighth-order physical-residual coefficient and normalized saturation-deficit limit remain open formalization objectives.

---

## 13. Author

**Valentino Lanzarini**

Independent Mathematical Researcher

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

Research preprint:

https://doi.org/10.5281/zenodo.23163367

Repository:

[GitHub repository](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**
