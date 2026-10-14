
# Lanzarini Krylov–Jacobi

### Lean 4 Formalization of Jacobi Matrices and Krylov Quantum Dynamics

**Author:** Valentino Lanzarini  
**Status:** Research in progress  
**Framework:** Lean 4 + mathlib  
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

**Repository:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

**Research preprint:**  
https://doi.org/10.5281/zenodo.23163367

---

## 1. Project Overview

This repository contains an ongoing formalization of mathematical structures associated with independent research on Krylov–Jacobi dynamics, quantum evolution, and local defects in Krylov speed-limit saturation.

The objective is to translate mathematical statements into machine-checkable Lean 4 definitions and proofs, making assumptions and logical dependencies explicit.

The repository has successfully verified the foundational results through P56.

**Important:** The central local-defect hierarchy theorem of the research preprint has not yet been formally verified in Lean.

Successful compilation does not establish mathematical novelty, independent peer review, or correctness of statements not represented by the compiled theorems.

## 2. Mathematical Framework

We consider a finite-dimensional real Jacobi matrix:

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

The matrix satisfies:

$$
H^{\mathsf T}=H.
$$

After embedding into complex matrices:

$$
H^\dagger=H.
$$

The quantum evolution generator is:

$$
G(t)=-itH.
$$

The propagator is:

$$
U(t)=\exp(-itH).
$$

The Lean formalization proves:

$$
U(0)=I,
$$

and

$$
U(t)^\dagger U(t)=I.
$$

The propagator is therefore unitary for every real time in the finite-dimensional setting considered.

## 3. Verified Mathematical Results

The following results have passed the configured Lean verification workflow.

### P51: Anti-self-adjoint generator

The evolution generator satisfies:

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

For every initial state and real time:

$$
\|\psi(t)\|^2=\|\psi(0)\|^2.
$$

Lean theorem:

`jacobiNormSq_state`

No initial normalization assumption is required.

### P54: Inner-product conservation

For arbitrary states $\psi$ and $\phi$:

$$
\langle U(t)\psi,U(t)\phi\rangle
=
\langle\psi,\phi\rangle.
$$

Lean theorem:

`jacobiInner_state_pair`

### P55: Orthogonality preservation

If:

$$
\langle\psi,\phi\rangle=0,
$$

then:

$$
\langle U(t)\psi,U(t)\phi\rangle=0.
$$

Lean theorem:

`jacobiState_orthogonality`

### P56: Krylov number operator and expectation

The Krylov number operator is:

$$
N=\operatorname{diag}(0,1,\ldots,n-1).
$$

The Krylov complexity is:

$$
K(\psi)=
\sum_{j=0}^{n-1}j|\psi_j|^2.
$$

The formalized expectation identity is:

$$
\langle\psi,N\psi\rangle=K(\psi).
$$

Lean theorems:

- `krylovNumberOperator_mulVec`
- `krylovComplexity_expectation`
- `krylovComplexityAt_zero`

The P56 verification passed GitHub Actions workflow run #53, commit `44fcec5`.

These are verified foundational results. They do not yet establish the central asymptotic theorem of the research preprint.

## 4. Repository Structure

| File | Purpose |
| --- | --- |
| `Main.lean` | Initial formal verification check |
| `Jacobi2.lean` | Two-site Jacobi matrix and symmetry |
| `JacobiGeneral.lean` | General integer Jacobi entries and symmetry |
| `JacobiReal.lean` | Finite real Jacobi matrix and symmetry |
| `JacobiEvolution.lean` | Complex Hamiltonian and evolution generator |
| `MatrixExpProbe.lean` | Propagator, unitarity, norm and inner-product conservation |
| `KrylovNumber.lean` | Number operator, Krylov complexity and expectation |
| `lean-toolchain` | Lean compiler version |
| `lakefile.toml` | Mathlib dependency |
| `.github/workflows/lean.yml` | Automated theorem verification |

## 5. Formal Verification Environment

The project uses:

- Lean 4.24.0
- Mathlib v4.24.0
- Lake
- GitHub Actions

The verification workflow compiles the Lean source files in dependency order.

Verification history:

https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions

A successful workflow run confirms that the configured Lean checks succeeded for the corresponding commit.

For stronger reproducibility, dependency lockfiles and the precise commit revision should be retained when preparing an archival release.

## 6. Indexing Convention

The Lean formalization uses zero-based indices through `Fin n`.

In the Lean Jacobi matrix, `b i` couples site `i` to site `i+1`.

Some research formulas use one-based indexing for the Lanczos coefficients, where the first coupling is called $b_1$.

Therefore, the correspondence between Lean indices and preprint indices must be explicitly established before formalizing the local-defect hierarchy.

No equality between differently indexed coefficients should be assumed without a proved translation.

## 7. Krylov Complexity and Variance

The time-dependent Krylov complexity is:

$$
K(t)=
\sum_{j=0}^{n-1}j|\psi_j(t)|^2.
$$

Its second moment is:

$$
K_2(t)=
\sum_{j=0}^{n-1}j^2|\psi_j(t)|^2.
$$

For normalized states, the variance is:

$$
V(t)=K_2(t)-K(t)^2.
$$

The current repository formalizes the complexity expectation, but not yet the second moment or variance.

These are planned next steps.

## 8. Krylov Speed-Limit Deficit

The broader research investigates:

$$
D(t)=
1-\frac{\dot K(t)^2}{4b_1^2V(t)}.
$$

This expression requires appropriate assumptions, including a nonzero denominator.

Its formalization will require:

1. Time differentiability of the evolved state.
2. Differentiability of Krylov complexity.
3. A rigorous definition of variance.
4. The applicable speed-limit inequality.
5. Explicit treatment of zero-variance and boundary cases.

The deficit formula is currently research context, not a verified Lean theorem in this repository.

## 9. Local-Defect Hierarchy

The research investigates local finite-difference defects of the squared Lanczos coefficients.

Using the research convention:

$$
c_j=b_j^2,
$$

a third finite-difference defect is:

$$
\Omega_r=
c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
$$

The goal is to formally investigate how local coefficient constraints affect short-time loss of Krylov speed-limit saturation.

The exact assumptions, indexing, finite-dimensional boundary conditions, and asymptotic remainder terms must be formalized and checked.

The main local-defect hierarchy is not yet a completed Lean theorem.

## 10. Research Roadmap

### Completed

- P51: Anti-self-adjoint evolution generator.
- P52: Unitary quantum propagator.
- P53: Conservation of norm.
- P54: Conservation of inner products.
- P55: Preservation of orthogonality.
- P56: Krylov number operator and expectation.

### Next formalization targets

- P57: Nonnegativity of Krylov complexity.
- P58: Second Krylov moment.
- P59: Variance for normalized states.
- Time derivatives of quantum evolution and Krylov complexity.
- Speed-limit inequality and deficit.
- Local finite-difference defects.
- Short-time expansions and remainder estimates.
- Boundary-case verification.
- Central local-defect hierarchy theorem.

The P57–P59 labels are development targets, not completed proofs.

## 11. Scientific Status and Limitations

The repository does not currently claim:

- A complete Lean proof of the central research theorem.
- Independent peer-review certification.
- Worldwide mathematical priority.
- Resolution of an established open mathematical problem.
- A new universal quantum speed limit.

The verified foundational results and the proposed research contribution must be evaluated separately.

Formal proof verification establishes logical correctness of the encoded statements relative to the Lean environment and its dependencies.

It does not independently establish the originality of those statements or their complete correspondence with the published research.

## 12. Research Preprint

**Title:** Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics

**Author:** Valentino Lanzarini

**Zenodo DOI:**  
https://doi.org/10.5281/zenodo.23163367

The preprint and this repository are related research artifacts.

The formalization is incomplete relative to the full mathematical content of the preprint.

## 13. Copyright and Permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing, or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place original materials in the public domain.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas, or theorems.

Third-party dependencies remain subject to their respective licenses.

## 14. AI-Assisted Research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not presented as independent peer review or scientific certification.

Mathematical claims must be evaluated through explicit proofs, reproducible checks, and independent scientific scrutiny.

## 15. Author

**Valentino Lanzarini**

Independent Mathematical Research

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Research:**  
https://doi.org/10.5281/zenodo.23163367

**GitHub:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

---

Copyright © 2026 Valentino Lanzarini. All rights reserved.
