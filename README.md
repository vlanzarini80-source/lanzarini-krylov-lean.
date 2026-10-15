
# Lanzarini Krylov–Jacobi

### Lean 4 Formalization of Jacobi Matrices and Krylov Quantum Dynamics

**Author:** Valentino Lanzarini  
**Status:** Research in progress  
**Framework:** Lean 4 + mathlib  
**Latest verified milestone:** P61  
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

**Repository:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

**Research preprint:**  
https://doi.org/10.5281/zenodo.23163367

---

## 1. Project Overview

This repository contains an ongoing Lean 4 formalization of finite-dimensional Jacobi dynamics, quantum evolution, and Krylov complexity.

The project supports independent mathematical research on local defects in Krylov speed-limit saturation.

Its objective is to translate mathematical statements into machine-checkable definitions and proofs, making assumptions and logical dependencies explicit.

**Verified progress:** Foundational results through P61 have passed the configured Lean verification workflow.

**Latest confirmed P61 verification:**

- Workflow: Lean 4 Verification #63
- Commit: `f7bde4f`
- Date: October 15, 2026
- Result: PASS

**Important scientific distinction:** The central local-defect hierarchy theorem from the research preprint has not yet been formally verified in Lean.

Successful compilation does not establish mathematical novelty, independent peer review, or correctness of claims not encoded in the verified theorems.

---

## 2. Mathematical Framework

Consider a finite-dimensional real Jacobi matrix:

$$
H=
\begin{pmatrix}
a_0 & b_0 & 0 & \cdots & 0\\
b_0 & a_1 & b_1 & \ddots & \vdots\\
0 & b_1 & a_2 & \ddots & 0\\
\vdots & \ddots & \ddots & \ddots & b_{n-2}\\
0 & \cdots & 0 & b_{n-2} & a_{n-1}
\end{pmatrix}.
$$

For real Jacobi coefficients,

$$
H^{\mathsf T}=H.
$$

After embedding into complex matrices,

$$
H^\dagger=H.
$$

The evolution generator is

$$
G(t)=-itH,
$$

and the propagator is

$$
U(t)=\exp(-itH).
$$

The Lean formalization proves

$$
U(0)=I
$$

and

$$
U(t)^\dagger U(t)=I.
$$

Thus the propagator is unitary for every real time in the finite-dimensional setting considered.

---

## 3. Verified Mathematical Results

The following milestones have passed the configured Lean verification workflow.

### P51: Anti-self-adjoint generator

The evolution generator satisfies

$$
G(t)^\dagger=-G(t).
$$

Lean theorem:

`jacobiEvolutionGenerator_conjTranspose`

### P52: Unitary quantum propagator

$$
U(t)^\dagger U(t)=I.
$$

Lean theorem:

`jacobiPropagator_unitary`

### P53: Norm conservation

For every initial state and real time,

$$
\|\psi(t)\|^2=\|\psi(0)\|^2.
$$

Lean theorem:

`jacobiNormSq_state`

No initial normalization assumption is required.

### P54: Inner-product conservation

For arbitrary states $\psi$ and $\phi$,

$$
\langle U(t)\psi,U(t)\phi\rangle
=
\langle\psi,\phi\rangle.
$$

Lean theorem:

`jacobiInner_state_pair`

### P55: Orthogonality preservation

If

$$
\langle\psi,\phi\rangle=0,
$$

then

$$
\langle U(t)\psi,U(t)\phi\rangle=0.
$$

Lean theorem:

`jacobiState_orthogonality`

### P56: Krylov number operator and expectation

Define the Krylov number operator

$$
N=\operatorname{diag}(0,1,\ldots,n-1).
$$

The Krylov complexity is

$$
K(\psi)=
\sum_{j=0}^{n-1}j|\psi_j|^2.
$$

The verified expectation identity is

$$
\langle\psi,N\psi\rangle=K(\psi).
$$

Lean theorems:

- `krylovNumberOperator_mulVec`
- `krylovComplexity_expectation`
- `krylovComplexityAt_zero`

### P57: Nonnegativity of Krylov complexity

For every finite-dimensional complex state,

$$
K(\psi)\geq0.
$$

The same property holds for the evolved state at every real time.

Lean theorems:

- `krylovComplexity_nonneg`
- `krylovComplexityAt_nonneg`

### P58: Second Krylov moment

Define

$$
K_2(\psi)=
\sum_{j=0}^{n-1}j^2|\psi_j|^2.
$$

The formalization proves

$$
K_2(\psi)\geq0
$$

for arbitrary finite-dimensional complex states.

It also proves nonnegativity under Jacobi evolution and the initial-time identity.

Lean theorems:

- `krylovSecondMoment_nonneg`
- `krylovSecondMomentAt_nonneg`
- `krylovSecondMomentAt_zero`

### P59: Krylov variance and normalization

Define the variance expression

$$
V(\psi)=K_2(\psi)-K(\psi)^2.
$$

For normalized states, this is the variance of the Krylov number distribution.

The formalization also establishes that Jacobi evolution preserves normalization:

$$
\|\psi(0)\|^2=1
\implies
\|\psi(t)\|^2=1.
$$

Lean theorems:

- `krylovVarianceAt_zero`
- `jacobiState_normalized`

The variance expression is defined for arbitrary states, but its nonnegativity is asserted only under the appropriate normalization assumption.

### P60: Centered variance and nonnegativity

For a normalized state,

$$
V(\psi)=
\sum_{j=0}^{n-1}
(j-K(\psi))^2|\psi_j|^2.
$$

Consequently,

$$
V(\psi)\geq0.
$$

This nonnegativity also holds at every real time under Jacobi evolution for normalized initial states.

Lean theorems:

- `krylovVariance_centered`
- `krylovVariance_nonneg`
- `krylovVarianceAt_nonneg`

### P61: Zero-variance equivalence

For normalized states,

$$
V(\psi)=0
\iff
\sum_{j=0}^{n-1}
(j-K(\psi))^2|\psi_j|^2=0.
$$

The formalization also establishes the centered variance identity and its zero-variance equivalence at every real time under Jacobi evolution.

Lean theorems:

- `krylovVariance_eq_zero_iff_centered`
- `krylovVarianceAt_centered`
- `krylovVarianceAt_eq_zero_iff_centered`

**Scope:** P61 establishes the equivalence with the vanishing centered sum. It does not yet establish the stronger single-site concentration characterization.

These are verified foundational results. They do not yet establish the central local-defect hierarchy theorem of the research preprint.

---

## 4. Repository Structure

| File | Purpose |
| --- | --- |
| `Main.lean` | Initial verification checks |
| `Jacobi2.lean` | Two-site Jacobi matrix and symmetry |
| `JacobiGeneral.lean` | General integer Jacobi entries and symmetry |
| `JacobiReal.lean` | Finite real Jacobi matrix and symmetry |
| `JacobiEvolution.lean` | Complex Hamiltonian and evolution generator |
| `MatrixExpProbe.lean` | Propagator, unitarity and conservation properties |
| `KrylovNumber.lean` | Krylov operator, complexity, moments, variance and zero-variance identities |
| `lean-toolchain` | Lean compiler toolchain |
| `lakefile.toml` | Mathlib dependency configuration |
| `.github/workflows/lean.yml` | Automated verification workflow |

---

## 5. Formal Verification Environment

The project uses:

- Lean compiler: `leanprover/lean4:v4.24.0`
- Mathlib dependency: `leanprover-community/mathlib`, revision `v4.24.0`
- Lake
- GitHub Actions

The configured workflow compiles the Lean source files in dependency order.

Verification history:

https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions

Latest confirmed P61 milestone:

**GitHub Actions #63 — commit `f7bde4f` — PASS.**

A successful workflow run confirms that the configured Lean checks succeeded for the corresponding commit.

For stronger reproducibility, the exact dependency lockfile and commit revision should be retained when preparing an archival release.

A separate audit of axiomatic dependencies, precise formal assumptions and mathematical correspondence with the preprint remains important.

---

## 6. Indexing Convention

The Lean formalization uses zero-based indices through `Fin n`.

For a Jacobi matrix of dimension `n`, the diagonal coefficients are indexed by

$$
a_0,\ldots,a_{n-1}.
$$

In the Lean implementation, `b i` couples site `i` to site `i+1` only when `i+1 < n`.

Consequently, only `n-1` off-diagonal coupling coefficients occur in the matrix.

The final value of the function `b : Fin n → ℝ` does not contribute to the Jacobi matrix.

The research preprint may use one-based Lanczos indexing, where the first physical coupling is denoted by $b_1$.

For valid coupling indices, the correspondence is

$$
b_j^{\mathrm{research}}
=
b_{j-1}^{\mathrm{Lean}},
\qquad
1\leq j\leq n-1.
$$

This indexing correspondence must be applied explicitly in future formalizations of finite differences, local defects and boundary conditions.

No equality between differently indexed coefficients should be assumed without a proved translation.

---

## 7. Krylov Complexity and Variance

For the evolved state,

$$
\psi(t)=U(t)\psi(0),
$$

the time-dependent Krylov complexity is

$$
K(t)=
\sum_{j=0}^{n-1}j|\psi_j(t)|^2.
$$

The second moment is

$$
K_2(t)=
\sum_{j=0}^{n-1}j^2|\psi_j(t)|^2.
$$

For normalized states, the variance is

$$
V(t)=K_2(t)-K(t)^2.
$$

The centered identity is

$$
V(t)=
\sum_{j=0}^{n-1}
(j-K(t))^2|\psi_j(t)|^2.
$$

These definitions and identities are represented in the verified Lean development through P61.

The time derivatives and speed-limit deficit are not yet formally established in this repository.

---

## 8. Krylov Speed-Limit Deficit

The broader research investigates the dimensionless expression

$$
D(t)=
1-\frac{\dot K(t)^2}{4b_1^2V(t)},
$$

where $b_1$ denotes the first coupling in the one-based research convention.

This expression is defined only where

$$
b_1\neq0,
\qquad
V(t)>0.
$$

Interpreting $D(t)$ as a nonnegative speed-limit deficit additionally requires a proof of the relevant inequality

$$
\dot K(t)^2\leq4b_1^2V(t)
$$

under explicitly stated dynamical assumptions.

The formalization will require:

1. Differentiability of Jacobi quantum evolution.
2. Differentiability of Krylov complexity.
3. A precise speed-limit inequality with its hypotheses.
4. Explicit treatment of zero-variance cases.
5. Finite-dimensional boundary conditions.
6. Short-time expansions and rigorous remainder estimates.

Neither the displayed speed-limit inequality nor the deficit formula has yet been formally proved in this Lean repository.

These expressions describe the research objective, not an established result of the current formal verification.

---

## 9. Local-Defect Hierarchy

The research investigates local finite-difference defects of squared Lanczos coefficients.

Using the research convention,

$$
c_j=b_j^2,
$$

a third finite-difference expression is

$$
\Omega_r=
c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
$$

The goal is to investigate how local coefficient constraints affect short-time loss of Krylov speed-limit saturation.

The exact hypotheses, coefficient indexing, finite-dimensional boundary conditions and asymptotic remainder estimates must be formalized and checked.

The expression above is presented as research context. Its relationship to the complete hierarchy and the applicable coefficient range must be specified in the formal development.

**The central local-defect hierarchy theorem is not yet a completed Lean theorem.**

The research preprint and the machine-checked foundational development must therefore be distinguished.

---

## 10. Research Roadmap

### Completed

- P51: Anti-self-adjoint evolution generator.
- P52: Unitary quantum propagator.
- P53: Conservation of norm.
- P54: Conservation of inner products.
- P55: Preservation of orthogonality.
- P56: Krylov number operator and expectation.
- P57: Nonnegativity of Krylov complexity.
- P58: Second Krylov moment.
- P59: Variance expression and normalization preservation.
- P60: Centered variance and nonnegativity.
- P61: Zero-variance equivalences.

### Next formalization targets

- P62: Single-site concentration under zero variance.
- Time derivatives of Jacobi evolution and Krylov complexity.
- Krylov speed-limit inequality.
- Rigorous definition and analysis of the speed-limit deficit.
- Local finite-difference defects.
- Short-time expansions with controlled remainder estimates.
- Finite-dimensional boundary-case verification.
- Formalization of the central local-defect hierarchy theorem.

These next targets are not yet verified Lean theorems.

---

## 11. Scientific Status and Limitations

This repository does not currently claim:

- A complete Lean proof of the central local-defect theorem.
- Independent peer-review certification.
- Established worldwide mathematical priority.
- Resolution of an established open mathematical problem.
- A new universal quantum speed limit.

The verified foundational results and the proposed research contribution must be evaluated separately.

Formal proof verification establishes correctness of the encoded statements relative to the Lean environment, definitions, assumptions and accepted dependencies.

It does not independently establish the originality of those statements or their complete correspondence with the published research.

The project aims to advance through reproducible, machine-checkable milestones while keeping unresolved scientific questions explicit.

---

## 12. Research Preprint

**Title:** Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics

**Author:** Valentino Lanzarini

**Zenodo DOI:**  
https://doi.org/10.5281/zenodo.23163367

The preprint and this repository are related research artifacts.

The formalization remains incomplete relative to the full mathematical content of the preprint.

---

## 13. Copyright and Permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place original materials in the public domain.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas or theorems.

Third-party dependencies remain subject to their respective licenses.

---

## 14. AI-Assisted Research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not presented as independent peer review or scientific certification.

Mathematical claims must be evaluated through explicit proofs, reproducible checks and independent scientific scrutiny.

---

## 15. Author

**Valentino Lanzarini**

Independent Mathematical Researcher

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Research:**  
https://doi.org/10.5281/zenodo.23163367

**GitHub:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

---

Copyright © 2026 Valentino Lanzarini. All rights reserved.
