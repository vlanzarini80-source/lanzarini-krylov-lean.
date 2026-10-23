
# Lanzarini Krylov–Jacobi

### Lean 4 formalization of finite-dimensional Jacobi dynamics and Krylov observables

**Author:** Valentino Lanzarini, Independent Mathematical Researcher  
**Status:** Research in progress  
**Latest verified development checkpoint:** **P76.6**, branch `research/p75-centered-derivative`, GitHub Actions **#159: SUCCESS**, 23 October 2026  
**Latest checkpoint integrated into `main`:** **P74.2**, GitHub Actions **#117: SUCCESS**, 20 October 2026  
**Environment:** Lean 4 `v4.24.0`; mathlib revision declared as `v4.24.0`  
**Preprint:** https://doi.org/10.5281/zenodo.23163367  
**Repository:** https://github.com/vlanzarini80-source/lanzarini-krylov-lean.  
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

> **Scientific scope.** P76.6 establishes, for the encoded finite-dimensional real Jacobi evolution and normalized initial state, the existence of the physical derivative of Krylov complexity and an energy-variance speed bound. This is a machine-checked formalization of a classical type of uncertainty/speed-limit inequality, **not** evidence of a new universal physical law. The saturation-deficit asymptotics, finite-depth local-defect hierarchy, and semi-infinite extensions are **not yet formalized as verified Lean theorems**. The development branch has **not** been merged into `main`.

## 1. Verification status and reproducible evidence

| Item | Verified record |
| --- | --- |
| Latest development theorem | `Lanzarini.p76_6_energy_speed_limit` |
| Development branch | `research/p75-centered-derivative` |
| Development commit | `178b6a0f57c18708ac0818b76d411fc630311969` |
| GitHub Actions | [#159, SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470) |
| Workflow step | `Verify Lean proofs through P76.6`, SUCCESS |
| Reported axioms of P76.6 | `[propext, Classical.choice, Quot.sound]` |
| Latest `main` checkpoint | P74.2, [Actions #117](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) |
| `main` head checked on 23 Oct 2026 | `9afa5e714c53616f9ea55aac16552a7c25a7209a` |

The P76.6 job log was inspected: the theorem compiled and its `#print axioms` output contained only the three standard Lean axioms listed above. The workflow checks for `sorryAx` in the recorded proof logs. These are **declaration-specific checks**, not a full audit of all historical declarations or the informal-to-formal translation.

**Branch distinction:** A successful development-branch run does not mean that P76.6 has been merged into `main` or verified on `main`.

## 2. Mathematical setting

Let `n : ℕ` and `a b : Fin n → ℝ` define a finite real symmetric Jacobi matrix `H`, with diagonal entries `a` and nearest-neighbor off-diagonal entries `b`. The foundational definitions permit arbitrary real coefficients; positive interior couplings must be explicitly assumed wherever needed.

The state evolves according to

$$
\psi(t)=e^{-itH}\psi_0, \qquad \dot\psi(t)=-iH\psi(t).
$$

For the chosen Jacobi coordinate basis, define the Krylov number operator and its moments by

$$
N=\operatorname{diag}(0,1,\ldots,n-1),\qquad
K(t)=\langle\psi(t),N\psi(t)\rangle,
$$

$$
V_K(t)=\langle\psi(t),N^2\psi(t)\rangle-K(t)^2.
$$

For normalized states, define the energy expectation and variance by

$$
E(t)=\langle\psi(t),H\psi(t)\rangle,\qquad
V_H(t)=\|(H-E(t)I)\psi(t)\|^2.
$$

The Lean formalization uses `jacobiNormSq`, `jacobiInner`, `krylovComplexityAt`, `krylovVarianceAt`, and `p76_energyVarianceAt`. Their exact definitions and the encoded hypotheses, rather than these explanatory formulas alone, determine the theorem's scope.

**Index convention:** Lean's `b 0` is the first physical edge coupling, called `b_1` in the preprint. The final entry of the `Fin n` coupling function is unused. This convention matters for finite-depth defects and boundary cases.

**Basis limitation:** The repository does not establish a general Lanczos-basis equivalence for arbitrary Hamiltonians and initial vectors. Its Krylov interpretation is specific to the chosen Jacobi-chain coordinates.

## 3. Verified development milestones

| Checkpoint | Content | Main source(s) |
| --- | --- | --- |
| P51–P55 | Finite Jacobi Hamiltonian, anti-Hermitian generator, unitary evolution, norm/inner-product conservation | `JacobiReal.lean`, `JacobiEvolution.lean`, `MatrixExpProbe.lean` |
| P56–P64 | Krylov number operator, moments, normalized variance, zero-variance support | `KrylovNumber.lean` |
| P65–P71 | Complex Gram/Lagrange identities, Gram gap, centered-state variance | `KrylovGram.lean`, `KrylovLagrange.lean`, `KrylovGap.lean` |
| P72 | Algebraic increment, conditional derivative, complex-time exponential derivative | `KrylovGap.lean`, `P72_3a_Minimal.lean` |
| P73.1–P73.2 | Physical propagator and evolved-state derivatives | `P73_RealTime.lean`, `P73_2_State.lean` |
| P74.1–P74.2 | Component derivatives and physical Krylov complexity derivative | `P74_1_Components.lean`, `P74_2_KrylovDerivative.lean` |
| P75.1–P75.2b | Centered-state orthogonality, velocity orthogonality, centered physical derivative | `P75_1_Orthogonality.lean`, `P75_2a_VelocityOrthogonality.lean`, `P75_2b_CenteredDerivative.lean` |
| P75.3–P75.4 | Quadratic Gram bound and physical derivative speed bound | `P75_3_QuadraticSpeedBound.lean`, `P75_4_DerivativeSpeedBound.lean` |
| P76.1–P76.3 | Centered energy variance, identities, second-moment representation | `P76_1_EnergyVariance.lean`, `P76_2_EnergyVarianceIdentity.lean`, `P76_3_EnergySecondMoment.lean` |
| P76.4–P76.5b | Centered energy orthogonality, velocity inner product, norm/variance bridge | `P76_4_CenteredEnergySpeed.lean`, `P76_5_CenteredVelocity.lean`, `P76_5b_CenteredVelocityNorm.lean` |
| **P76.6** | **Physical derivative and complete energy-variance speed bound** | **`P76_6_EnergySpeedLimit.lean`** |

P75–P76.6 are verified on the **development branch** by the workflow ending at run #159. P74.2 is the latest verified checkpoint on `main` as of the stated audit date. Milestone numbering is not a percentage of completion of the preprint.

## 4. Main theorem: P76.6

The exact Lean declaration is:

`Lanzarini.p76_6_energy_speed_limit`

Its parameters include `n : ℕ`, `a b : Fin n → ℝ`, `t : ℝ`, `psi : Fin n → ℂ`, and the normalization hypothesis `jacobiNormSq psi = 1`.

The theorem states that there exists a real `d` such that

$$
\operatorname{HasDerivAt}(K,d,t)
\quad\text{and}\quad
d^2\leq 4V_K(t)V_H(t).
$$

Equivalently, using uniqueness of the derivative,

$$
\boxed{|K'(t)|^2\leq4\,V_K(t)\,V_H(t).}
$$

The proof derives the derivative from `p75_centered_derivative`, uses `p75_centered_quadratic_bound`, the centered velocity inner-product identity, the physical velocity bridge, and the centered-velocity norm/energy-variance identity. The desired inequality is **not** an input hypothesis.

The inequality is a finite-dimensional variance speed limit. It does not by itself establish the preprint's stronger initial-state specialization with the first coupling, saturation conditions, or local-defect coefficients. No novelty or worldwide priority is claimed for this classical type of bound.

## 5. Formal integrity and verification policy

The project requires:

1. Exact mathematical statements and explicit assumptions before proof development.
2. No `sorry`, `admit`, artificial axioms, or assumptions equivalent to the conclusion.
3. Explicit compilation of every new source file in GitHub Actions.
4. `#print axioms` inspection for each claimed final declaration.
5. Rejection of `sorryAx` in relevant proof logs.
6. No weakening or substitution of theorem statements merely to obtain CI success.
7. Separate development-branch and post-merge `main` verification records.
8. Independent mathematical and bibliographic review before novelty claims.

The P76.6 audit output was:

```text
'Lanzarini.p76_6_energy_speed_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This establishes what the Lean declaration depends on, **not** that the entire preprint is correct or original. A CI success also does not replace review of the mathematical meaning of the definitions.

## 6. Reproducibility

The repository includes:

```text
lean-toolchain       leanprover/lean4:v4.24.0
lakefile.toml        mathlib revision v4.24.0
.github/workflows/lean.yml
```

The workflow invokes `lake update` and `lake exe cache get` before compiling source files. At the audited P76.6 commit, **no committed `lake-manifest.json` was present** in the repository tree. Committing a reviewed dependency manifest would strengthen exact reproducibility. The successful workflow and its commit are the current authoritative compilation record.

The separate `p72-minimal.yml` workflow is a historical, branch-limited test and **not** a second independent P76.6 verification.

## 7. Research obligations not yet formally proved

### 7.1. Initial-state speed limit

For the preprint's initial vector at the first Jacobi site, establish the necessary energy conservation and first-coupling identity under the exact coupling, normalization and dimension hypotheses. Only then specialize the P76.6 inequality to the preprint's `b_1` bound.

### 7.2. Saturation deficit

Define and study, on a domain where the denominator is nonzero,

$$
D(t)=1-\frac{K'(t)^2}{4b_1^2V_K(t)}.
$$

Prove the denominator conditions, nonnegativity, and any extension through `t=0` separately. The quotient is not automatically defined at zero variance.

### 7.3. Finite-depth local defects

In the preprint convention, let `c_j=b_j^2`, with `c_0=0`, and define

$$
\Omega_r=c_{r+3}-3c_{r+2}+3c_{r+1}-c_r,
\qquad \delta_r=a_{r+3}-a_0.
$$

The proposed first nonzero saturation-deficit coefficient involves **both** off-diagonal and diagonal defects, with prefix assumptions and finite-boundary cases. The exact leading coefficient, remainder estimate, positivity conditions and terminal cases remain research claims requiring a separate formal proof and independent audit. They must not be inferred from P76.6.

### 7.4. Further limitations

Not yet formalized: the complete finite-depth defect hierarchy; local rigidity; the full short-time expansion; a general Lanczos basis-identification theorem; and semi-infinite unbounded Jacobi operators with their domain and self-adjointness requirements.

## 8. Selected verification history

| Checkpoint | Record | Scope |
| --- | --- | --- |
| P71 | [Actions #84](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) | Historical verification |
| P72.3a | [Actions #98](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849) | Historical verification |
| P73.1 | [Actions #103](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923) | Post-merge `main` |
| P73.2 | [Actions #109](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293) | Post-merge `main` |
| P74.2 | [Actions #117](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) | Post-merge `main` |
| P76.5b | Actions #157 | Development branch |
| **P76.6** | **[Actions #159](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470)** | **Development branch, SUCCESS** |

## 9. Preprint and scientific interpretation

**Title:** *Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics*  
**Author:** Valentino Lanzarini  
**DOI:** https://doi.org/10.5281/zenodo.23163367

The preprint and Lean repository are distinct scientific artifacts. Lean verifies precisely encoded statements under their definitions and assumptions; it does not independently certify the correctness of every informal interpretation, novelty, priority, or peer-review status. The local-defect hierarchy remains the principal research target.

## 10. Copyright and AI assistance

Copyright © 2026 Valentino Lanzarini. **All rights reserved.**

The public repository is accessible for inspection and scientific discussion. No general open-source license is granted for original code or documentation. Third-party dependencies retain their respective licenses. Copyright protects original expression, not mathematical facts or theorems themselves.

AI tools have assisted the development and formalization. AI assistance is not independent peer review. The author remains responsible for scientific claims and publication decisions.

## 11. Author

**Valentino Lanzarini**  
Independent Mathematical Researcher  
Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

Preprint: https://doi.org/10.5281/zenodo.23163367  
GitHub: https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**
