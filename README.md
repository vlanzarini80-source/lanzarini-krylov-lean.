
# Lanzarini Krylov–Jacobi

### Lean 4 Formalization of Jacobi Matrices and Krylov Quantum Dynamics

**Author:** Valentino Lanzarini  
**Status:** Research in progress  
**Framework:** Lean 4 + mathlib  
**Copyright:** © 2026 Valentino Lanzarini. **All rights reserved.**

**Repository:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

**Research preprint:**  
https://doi.org/10.5281/zenodo.23163367

---

## 1. Project Overview

This repository contains an ongoing formalization project associated with independent mathematical research on Krylov–Jacobi dynamics, quantum evolution, and local defects in Krylov speed-limit saturation.

The objective is to translate mathematical definitions and proofs into machine-checkable Lean 4 code, making assumptions and logical dependencies explicit.

**Important:** Only statements accepted by the Lean compiler in a successful verification run are considered formally checked.

The main research theorem has not yet been formally verified in Lean.

## 2. Mathematical Framework

We consider a finite-dimensional real Jacobi matrix:

$$
H =
\begin{pmatrix}
a_0 & b_0 & 0 & \cdots & 0 \\
b_0 & a_1 & b_1 & \ddots & \vdots \\
0 & b_1 & a_2 & \ddots & 0 \\
\vdots & \ddots & \ddots & \ddots & b_{n-2} \\
0 & \cdots & 0 & b_{n-2} & a_{n-1}
\end{pmatrix}.
$$

Here the diagonal entries and nearest-neighbor couplings are real.

The real Jacobi matrix satisfies the symmetry identity:

$$
H^{\mathsf T}=H.
$$

After embedding into complex matrices, the Hamiltonian self-adjointness property is:

$$
H^\dagger=H.
$$

The quantum evolution generator is defined as:

$$
G(t)=-itH.
$$

The corresponding propagator is:

$$
U(t)=\exp(-itH).
$$

The zero-time identities are:

$$
G(0)=0,
$$

$$
U(0)=I_n.
$$

These zero-time identities have passed a previous Lean verification run.

A future formalization objective is to establish unitarity:

$$
U(t)^\dagger U(t)=I_n.
$$

Unitarity is not yet a completed Lean theorem in this repository.

## 3. Current Formalization

The repository includes:

- Finite-dimensional real Jacobi matrix definitions.
- Symmetry of Jacobi matrix entries.
- Real matrix transpose and conjugate-transpose identities.
- Complex representation of the Jacobi Hamiltonian.
- Quantum evolution generator.
- Matrix-exponential definition of the propagator.
- Zero-time generator identity.
- Zero-time propagator identity.

The complex Hamiltonian self-adjointness proof is part of the ongoing development.

Its latest verification status must be checked in GitHub Actions.

## 4. Repository Structure

| File | Purpose |
| --- | --- |
| `Main.lean` | Formalization entry and checks |
| `Jacobi2.lean` | Jacobi-related formalization |
| `JacobiGeneral.lean` | General Jacobi structures |
| `JacobiReal.lean` | Real Jacobi matrix and symmetry |
| `JacobiEvolution.lean` | Complex Hamiltonian and generator |
| `MatrixExpProbe.lean` | Matrix exponential and zero-time identities |
| `lean-toolchain` | Lean toolchain configuration |
| `lakefile.toml` | Mathlib dependency configuration |
| `.github/workflows/lean.yml` | Automated verification workflow |

## 5. Formal Verification

The project uses:

- Lean 4
- mathlib
- Lake
- GitHub Actions

**Lean version:** 4.24.0  
**Mathlib revision:** v4.24.0

The verification workflow is located at:

`.github/workflows/lean.yml`

A successful GitHub Actions run confirms that the configured Lean checks succeeded for the corresponding commit.

It does not certify mathematical novelty, independent peer review, or claims not represented by verified Lean statements.

## 6. Krylov Research Framework

The broader research studies Krylov expectation, variance, and the loss of speed-limit saturation.

A central research quantity is:

$$
D(t)=1-\frac{\bigl(\dot K(t)\bigr)^2}{4b_1^2V(t)}.
$$

Where:

- $K(t)$ is the Krylov expectation.
- $V(t)$ is the Krylov variance.
- $b_1$ is the first Lanczos coupling in the research convention.
- The expression requires appropriate assumptions, including a nonzero denominator.

The indexing convention in the research formula may differ from the zero-based indexing used in the Lean matrix definitions.

**This deficit expression is research context, not a theorem already verified in this repository.**

## 7. Research Roadmap

The planned formal verification stages are:

1. Self-adjointness of the complex Jacobi Hamiltonian.
2. Anti-self-adjointness of the evolution generator.
3. Unitarity of the quantum propagator.
4. Formal definition of Krylov expectation.
5. Formal definition of Krylov variance.
6. Formal definition of the speed-limit deficit.
7. Verification of candidate local-defect identities.
8. Verification of hypotheses and boundary cases.
9. Formal verification of candidate research theorems.

These are research objectives, not completed claims.

## 8. Scientific Status and Limitations

**The main local-defect research theorem has not yet been formally verified in Lean.**

This repository does not claim:

- Resolution of an established open mathematical problem.
- A complete Lean proof of the main research theorem.
- Independent peer-review certification.
- Worldwide mathematical priority.
- A new universal quantum speed limit.

Formal proof verification and assessment of scientific originality are distinct processes.

The purpose of this project is to support reproducibility, mathematical scrutiny, and transparent research development.

## 9. Related Research

**Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics**

**Author:** Valentino Lanzarini

**Zenodo DOI:**  
https://doi.org/10.5281/zenodo.23163367

The preprint and this repository are related research artifacts.

The repository does not currently formalize every statement in the preprint.

## 10. Reproducibility

The repository contains:

- `lean-toolchain`
- `lakefile.toml`
- `.github/workflows/lean.yml`

The project uses the pinned Lean and mathlib environment.

The verification commands are defined in the GitHub Actions workflow.

Successful compilation establishes acceptance of the checked Lean declarations for that specific revision.

## 11. Copyright and Permissions

**Copyright © 2026 Valentino Lanzarini.**

**ALL RIGHTS RESERVED.**

This repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing, or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place the original materials in the public domain.

Copyright protects original expression, but does not grant exclusive ownership of mathematical facts, ideas, or theorems.

Third-party software dependencies remain subject to their respective licenses.

For permission requests, contact the repository owner through GitHub.

## 12. AI-Assisted Research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not presented as independent peer review or scientific certification.

Mathematical claims must be evaluated through explicit proofs, reproducible checks, and independent scientific scrutiny.

## 13. Author

**Valentino Lanzarini**

Independent Mathematical Research

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Research:**  
https://doi.org/10.5281/zenodo.23163367

**GitHub:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**
 
