
# Lanzarini Krylov–Jacobi

### Lean 4 formalization of finite-dimensional Jacobi dynamics and Krylov observables

**Author:** Valentino Lanzarini, Independent Mathematical Researcher  
**Project status:** Research in progress  
**Latest reported machine-verified checkpoint:** **P74.2 (main, GitHub Actions #117: SUCCESS)**  
**Environment:** Lean 4 `v4.24.0` and mathlib `v4.24.0`  
**Research preprint:** https://doi.org/10.5281/zenodo.23163367  
**Repository:** [GitHub repository](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)  
**Latest development checkpoint:** P76.6 (verified on `research/p75-centered-derivative`; not yet merged into `main`) 
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

> **Scientific status.** This repository contains machine-checked foundational results concerning finite-dimensional real Jacobi matrices, unitary quantum evolution, Krylov moments and variance, complex Gram identities, and the physical time derivative of Krylov complexity.
>
> The reported P74.2 checkpoint establishes the derivative of Krylov complexity along finite-dimensional Jacobi evolution.
>
> **The centered physical Krylov derivative, complete dispersion speed limit, saturation-deficit expansion and finite-depth local-defect hierarchy are not yet established as verified Lean theorems.**
>
> Successful Lean verification establishes that the encoded statements follow from their formal definitions, hypotheses and accepted foundations. It does not establish mathematical originality, complete correspondence with the research preprint or independent peer review.

---

---

## Scientific Update — P75 to P76.6

**Updated:** 24 October 2026  
**Author:** Valentino Lanzarini  
**Lean:** v4.24.0  
**mathlib:** v4.24.0

### Verified development status

The historical README documents the formal development through P74.2 on `main`.

Subsequent development has established additional results through P76.6 on the branch:

`research/p75-centered-derivative`

**Verification records:**

- P74.2 on `main`: GitHub Actions #117 — SUCCESS
- P76.6 development: GitHub Actions #159 — SUCCESS
- P76.6 development: GitHub Actions #163 — SUCCESS

**Important:** P76.6 has not yet been verified as merged into `main`.

### P75: Centered Krylov derivative

The P75 development establishes centered-state orthogonality, physical velocity orthogonality, the centered physical Krylov derivative, and quadratic speed estimates.

For a normalized evolved state, let

$$
u(t)=(N-K(t)I)\psi(t).
$$

The centered physical derivative is

$$
K'(t)=
2\operatorname{Re}
\langle u(t),\dot{\psi}(t)\rangle.
$$

The relevant source files are:

```text
P75_1_Orthogonality.lean
P75_2a_VelocityOrthogonality.lean
P75_2b_CenteredDerivative.lean
P75_3_QuadraticSpeedBound.lean
P75_4_DerivativeSpeedBound.lean
```

### P76: Energy variance and centered velocity

For a normalized state, define

$$
E(t)=\langle\psi(t),H\psi(t)\rangle
$$

and

$$
V_H(t)=
\|(H-E(t)I)\psi(t)\|^2.
$$

The centered velocity is

$$
v_c(t)=-i(H-E(t)I)\psi(t).
$$

Its squared norm satisfies

$$
\|v_c(t)\|^2=V_H(t).
$$

The relevant source files are:

```text
P76_1_EnergyVariance.lean
P76_2_EnergyVarianceIdentity.lean
P76_3_EnergySecondMoment.lean
P76_4_CenteredEnergySpeed.lean
P76_5_CenteredVelocity.lean
P76_5b_CenteredVelocityNorm.lean
```

### P76.6: Energy-variance speed limit

**Verified declaration:**

```lean
Lanzarini.p76_6_energy_speed_limit
```

**Source:**

```text
P76_6_EnergySpeedLimit.lean
```

The theorem establishes that, for normalized finite-dimensional Jacobi evolution, there exists a real derivative \(d\) of Krylov complexity at time \(t\) satisfying

$$
d^2\leq4V_K(t)V_H(t).
$$

Equivalently,

$$
\boxed{
(K'(t))^2\leq4V_K(t)V_H(t)
}
$$

The theorem uses the centered physical derivative, Gram inequalities, and the centered-energy variance identities.

The desired inequality is not assumed as a hypothesis.

### Formal verification

GitHub Actions:

- https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470
- https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40018524509

The recorded axiom dependencies of the final declaration are:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` was reported in the audited declaration dependencies.

### Remaining mathematical obligations

The following are not yet verified Lean theorems:

1. The first-basis energy-variance identity \(V_H=b_1^2\).
2. The first-coupling Krylov speed-limit specialization.
3. The saturation-deficit definition and its precise domain.
4. The short-time saturation-deficit expansion.
5. The finite-depth mixed local-defect hierarchy.
6. The finite-chain rigidity theorem.
7. The semi-infinite Jacobi extension.
8. General Lanczos basis equivalence.

The research preprint's proposed local-defect expansion remains a separate mathematical claim requiring further formal proof and independent review.

### Scientific limitations

Lean verification establishes the encoded theorem relative to its definitions, assumptions, and foundational axioms.

It does not establish:

- Mathematical novelty.
- Worldwide scientific priority.
- Independent peer review.
- Correctness of every informal interpretation.
- Validity of unformalized preprint claims.

The original historical documentation below remains part of the repository record.

---

## 1. Latest verified formalization checkpoint

### 1.1. P74.2: Physical Krylov complexity derivative

The latest reported successful verification is P74.2, integrated into the repository's `main` branch.

| Item | Verification record |
| --- | --- |
| Checkpoint | **P74.2** |
| Branch | `main` |
| Status | GitHub Actions #117: SUCCESS |
| Date | 20 October 2026 |
| Pull Request | [PR #3, merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3) |
| Post-merge verification | [GitHub Actions #117](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) |
| Development verification | [GitHub Actions #116](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39374579575) |
| Reported merge commit | `3cc284d942bb73b977315fe5096033ce9ec37d42` |
| Lean toolchain | `leanprover/lean4:v4.24.0` |
| mathlib | `v4.24.0` |
| P74.1 source | `P74_1_Components.lean` |
| P74.2 source | `P74_2_KrylovDerivative.lean` |

These records identify the reported successful checkpoint. They should be rechecked against the corresponding GitHub workflow and source commit when performing an independent audit.

### 1.2. Exact Lean declarations

The P74.1 declarations are:

```lean
Lanzarini.p74_jacobiState_component_hasDerivAt
Lanzarini.p74_jacobiState_parts_hasDerivAt
```

The P74.2 declaration is:

```lean
Lanzarini.p74_krylovComplexityAt_hasDerivAt
```

P74.1 establishes componentwise differentiability of the evolved Jacobi state, including the real and imaginary coordinate derivatives.

P74.2 combines these results with the previously verified conditional Krylov differentiation theorem.

The resulting theorem concerns the actual finite-dimensional Jacobi evolution, rather than an arbitrary curve with assumed coordinate derivatives.

### 1.3. Mathematical statement

Let H be the finite-dimensional complex representation of a real symmetric Jacobi Hamiltonian.

Define the propagator and evolved state by

```text
U(t) = exp(-itH)

psi(t) = U(t) psi_0
```

The physical state derivative is

```text
d psi(t)/dt = (-iH) psi(t).
```

Define finite-dimensional Krylov complexity by

```text
K(t) = sum_{j=0}^{n-1} j |psi_j(t)|^2.
```

The P74.2 derivative identity is

```text
dK(t)/dt
  = 2 sum_{j=0}^{n-1}
      j Re(conj(psi_j(t)) (-iH psi(t))_j).
```

In mathematical notation, the same result is:

```math
\frac{dK(t)}{dt}
=
2\sum_{j=0}^{n-1}
j\,\mathrm{Re}
\left(
\overline{\psi_j(t)}
(-iH\psi(t))_j
\right).
```

This derivative identity does not require normalization of the initial state.

Normalization becomes essential when interpreting the centered second moment as a probability variance and deriving the intended physical speed limit.

### 1.4. Formal proof dependencies

P74.2 uses previously established results:

1. P72.2: Conditional componentwise differentiation of Krylov complexity.
2. P73.2: Derivative of the evolved Jacobi state.
3. P74.1: Complex-coordinate and real/imaginary component derivatives.

The desired physical Krylov derivative is not introduced as a hypothesis.

The recorded P74 axiom audit reports:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` was reported in the recorded dependencies of the three P74 declarations.

This is a declaration-specific axiom report, not an exhaustive independent audit of every theorem in the repository.

### 1.5. Meaning of the checkpoint

P74.2 completes an important foundational connection:

```text
Jacobi Hamiltonian
        |
        v
Unitary propagator
        |
        v
Evolved state derivative
        |
        v
Coordinate derivatives
        |
        v
Physical Krylov complexity derivative
```

This is a machine-checked formalization of a standard finite-dimensional dynamical identity.

It is not, by itself, a new physical law or a proof of the preprint's main local-defect hierarchy.

---

## 2. Mathematical framework and conventions

### 2.1. Finite real Jacobi matrices

For a finite dimension `n`, the formalization uses real coefficient functions:

```lean
a b : Fin n → ℝ
```

The Jacobi matrix has entries

```text
H[i,i]     = a_i
H[i,i+1]   = b_i
H[i+1,i]   = b_i
```

whenever the adjacent indices exist.

All remaining entries are zero.

The foundational definitions allow arbitrary real diagonal and off-diagonal coefficients.

Positive physical couplings are not automatically imposed by the basic matrix definitions.

Such positivity assumptions must be explicitly supplied in the theorems that require them.

### 2.2. Coupling index conventions

Lean uses zero-based `Fin n` indices.

The input `b i` couples sites `i` and `i+1`, where the adjacent pair exists.

The final entry of the `Fin n` coupling input is unused.

In the preprint, the first physical coupling is called `b_1`.

The correspondence is:

```text
b_j (preprint) = b_(j-1) (Lean)

1 <= j <= n-1
```

These conventions must be preserved when formalizing local defects and boundary terms.

### 2.3. Krylov basis identification

The operator named `krylovNumberOperator` acts on the chosen coordinate basis.

The repository does not yet formalize a general Lanczos algorithm or establish that this basis is the Krylov basis generated by an arbitrary Hamiltonian and initial state.

The physical interpretation therefore depends on the Jacobi-chain setting and the appropriate basis-identification hypotheses.

A general basis-equivalence theorem remains outside the present formalization.

### 2.4. Finite-dimensional evolution

The complex Jacobi Hamiltonian generates the propagator:

```math
U(t)=\exp(-itH).
```

The evolved state is:

```math
\psi(t)=U(t)\psi_0.
```

The formalization establishes finite-dimensional unitarity and conservation of norms and inner products.

P73.1 proves:

```math
U'(t)=(-iH)U(t).
```

P73.2 proves:

```math
\psi'(t)=(-iH)\psi(t).
```

P74.1 establishes the corresponding coordinate derivatives.

P74.2 establishes the physical Krylov complexity derivative.

These results do not imply the corresponding unbounded-operator statements in infinite dimensions.

### 2.5. Infinite-dimensional limitation

The repository does not yet provide a complete formalization of an unbounded Jacobi operator on the Hilbert space of square-summable sequences indexed by nonnegative integers.

It does not establish the general self-adjointness, operator-domain or weighted-estimate results needed for the corresponding semi-infinite problem.

Those questions must be treated separately.

---

## 3. Verified theorem development through P74.2

The milestone numbers describe the development history.

They do not represent a percentage of completion of the preprint's main theorem.

| Checkpoint | Formalized content | Source |
| --- | --- | --- |
| P51–P55 | Hermitian finite Jacobi Hamiltonian, anti-Hermitian generator, unitary propagator, norm and inner-product conservation | `JacobiReal.lean`, `JacobiEvolution.lean`, `MatrixExpProbe.lean` |
| P56–P59 | Krylov number operator, complexity, second moment, algebraic variance and normalization preservation | `KrylovNumber.lean` |
| P60–P61 | Centered variance, nonnegativity under normalization and zero-variance equivalences | `KrylovNumber.lean` |
| P62–P64 | Support restrictions and unique occupied level for normalized zero-variance states | `KrylovNumber.lean` |
| P65–P69 | Complex Gram coordinates, Gram sum and finite complex Lagrange identity | `KrylovGram.lean`, `KrylovLagrange.lean` |
| P70 | Exact real-part Gram-gap identity and nonnegativity | `KrylovGap.lean` |
| P71 | Centered-state norm and normalized Krylov variance bridge | `KrylovGap.lean` |
| P72.1 | Exact algebraic increment of Krylov complexity | `KrylovGap.lean` |
| P72.2 | Conditional componentwise Krylov complexity derivative | `KrylovGap.lean` |
| P72.3a.1 | Jacobi evolution generator factorization | `KrylovGap.lean` |
| P72.3a.2 | Complex-time representation of the propagator | `KrylovGap.lean` |
| P72.3a.3 | Complex-time matrix exponential derivative | `KrylovGap.lean` |
| P73.1 | Real-time Jacobi propagator derivative | `P73_RealTime.lean` |
| P73.2 | Real-time derivative of the evolved Jacobi state | `P73_2_State.lean` |
| P74.1 | Evolved-state complex, real and imaginary coordinate derivatives | `P74_1_Components.lean` |
| P74.2 | Physical Krylov complexity derivative along finite Jacobi evolution | `P74_2_KrylovDerivative.lean` |

The reported P74.2 workflow completed successfully on `main`.

### 3.1. Krylov moments and variance

For a finite complex state, define:

```math
K(\psi)=\sum_{j=0}^{n-1}j|\psi_j|^2.
```

The second moment is:

```math
K_2(\psi)=\sum_{j=0}^{n-1}j^2|\psi_j|^2.
```

The algebraic variance expression is:

```math
V(\psi)=K_2(\psi)-K(\psi)^2.
```

The expression `V` is defined for arbitrary finite vectors.

Its interpretation as a probability variance requires normalization:

```math
\|\psi\|^2=1.
```

Under this hypothesis, Lean proves:

```math
V(\psi)
=
\sum_{j=0}^{n-1}
(j-K(\psi))^2|\psi_j|^2
\ge 0.
```

A normalized zero-variance state has precisely one occupied Krylov level.

This is a finite-distribution theorem, not the local-defect hierarchy of the preprint.

### 3.2. Complex Gram/Lagrange identity: P69

For arbitrary finite complex vectors `u` and `v`, define:

```math
G(u,v)
=
\sum_{0\le i<j<n}
|u_i v_j-u_j v_i|^2.
```

The formalized classical identity is:

```math
G(u,v)
=
\|u\|^2\|v\|^2
-
|\langle u,v\rangle|^2
\ge 0.
```

Each unordered pair is counted once.

The determinant coordinate contains no complex conjugation.

This identity is classical and is not presented as a new mathematical discovery.

### 3.3. Real-part Gram gap: P70

For arbitrary finite complex vectors, the formalization establishes:

```math
\begin{aligned}
&\|u\|^2\|v\|^2
-
\left(\mathrm{Re}\langle u,v\rangle\right)^2\\
&\qquad =
G(u,v)
+
\left(\mathrm{Im}\langle u,v\rangle\right)^2
\ge 0.
\end{aligned}
```

This is an exact algebraic identity.

Its physical specialization requires the appropriate dynamical arguments.

### 3.4. Centered-state/variance bridge: P71

Define the Krylov number operator:

```math
N=\mathrm{diag}(0,1,\ldots,n-1).
```

For a normalized state, define:

```math
u=(N-K(\psi)I)\psi.
```

The formalization establishes:

```math
\|u\|^2=V(\psi).
```

The same identity holds along the finite Jacobi evolution when the initial state is normalized.

The Gram-gap identity is also specialized to the centered evolved state and an arbitrary auxiliary vector.

P71 therefore supplies the variance component required for the later speed-limit proof.

It does not itself establish that speed limit.

### 3.5. Krylov complexity differentiation: P72.1–P72.2

P72.1 proves an exact algebraic increment identity.

P72.2 establishes the derivative of Krylov complexity for a general time-dependent complex state under explicitly supplied componentwise differentiability hypotheses.

For a differentiable curve:

```math
\frac{dK(t)}{dt}
=
2\sum_{j=0}^{n-1}
j\,\mathrm{Re}
\left(
\overline{\psi_j(t)}
\dot{\psi}_j(t)
\right).
```

At P72.2, this was a conditional differentiation theorem.

**P74.2 subsequently establishes the corresponding theorem for actual finite-dimensional Jacobi evolution.**

### 3.6. Complex-time matrix exponential derivative: P72.3a

P72.3a.1 establishes factorization of the Jacobi evolution generator.

P72.3a.2 connects the real-time propagator with the complex-time matrix exponential.

P72.3a.3 establishes:

```math
\frac{d}{dz}\exp(zA)=A\exp(zA),
\qquad A=-iH.
```

The result uses the relevant mathlib matrix-exponential differentiation theorem.

Historical verification:

- [GitHub Actions #98: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849)
- Source commit: `702256d89e7623eafcabd188911166eaddb08c7a`
- Recorded axioms: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx` in the recorded declaration dependencies.

This is a standard mathematical ingredient.

### 3.7. Real-time Jacobi propagator derivative: P73.1

P73.1 proves:

```math
\frac{d}{dt}U(t)=(-iH)U(t).
```

The proof derives the real-time result from the complex-time derivative.

The physical propagator derivative is not assumed as a hypothesis.

Verified declaration:

```lean
Lanzarini.p73_jacobiPropagator_hasDerivAt
```

Historical records:

- [GitHub Actions #101: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527474)
- Original proof commit: `a291e152b9ea3feed8f7c0608ae8eaca33700298`
- [Pull Request #1: merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/1)
- [Post-merge GitHub Actions #103: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923)
- Merge commit: `677985738a8e82aca8327ad3cc241ef8bc5e695d`

Recorded axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

### 3.8. Real-time evolved Jacobi state derivative: P73.2

P73.2 establishes:

```math
\frac{d}{dt}\psi(t)=(-iH)\psi(t).
```

The proof uses the P73.1 propagator derivative and the continuous linear map applying a matrix to a fixed initial state.

The theorem does not assume the desired state derivative.

The result does not require state normalization.

Verified declaration:

```lean
Lanzarini.p73_jacobiState_hasDerivAt
```

Historical records:

- [GitHub Actions #108: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39204261981)
- Original proof commit: `9489b44a880688790e6dc65d422d90755d57a341`
- [Pull Request #2: merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/2)
- [Post-merge GitHub Actions #109: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293)
- Merge commit: `4e288ae3ce35e3f99c5630dd3fb436b30c3a36c9`

Recorded axiom dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

P73.2 is the foundational state derivative used by P74.1.

### 3.9. Jacobi-state component derivatives: P74.1

P74.1 establishes coordinatewise differentiability of the evolved state.

Verified declarations:

```lean
Lanzarini.p74_jacobiState_component_hasDerivAt
Lanzarini.p74_jacobiState_parts_hasDerivAt
```

For the finite-dimensional evolution:

```math
\psi(t)=e^{-itH}\psi_0,
```

the complex-coordinate derivative is:

```math
\frac{d}{dt}\psi_j(t)
=
(-iH\psi(t))_j.
```

The corresponding derivatives of the real and imaginary coordinate parts are also formally established.

These results follow from the previously verified P73.2 state derivative.

The desired component derivatives are not assumed.

P74.1 provides the componentwise differentiability required to specialize the P72.2 complexity derivative to the physical evolution.

### 3.10. Physical Krylov complexity derivative: P74.2

P74.2 establishes the physical time derivative of finite-dimensional Krylov complexity.

Verified declaration:

```lean
Lanzarini.p74_krylovComplexityAt_hasDerivAt
```

Define:

```math
K(t)=\sum_{j=0}^{n-1}j|\psi_j(t)|^2,
```

where:

```math
\psi(t)=e^{-itH}\psi_0.
```

The verified physical derivative is:

```math
\frac{dK(t)}{dt}
=
2\sum_{j=0}^{n-1}
j\,\mathrm{Re}
\left(
\overline{\psi_j(t)}
(-iH\psi(t))_j
\right).
```

The proof follows from:

1. P72.2: Conditional componentwise Krylov differentiation.
2. P73.2: Derivative of the evolved Jacobi state.
3. P74.1: Complex, real and imaginary coordinate derivatives.

The desired physical Krylov derivative is not assumed.

No normalization hypothesis is required for this specific derivative identity.

**This completes P74.2, not the centered derivative or the physical speed-limit theorem.**

---

## 4. Repository structure

The reported formal development contains the following source files and supporting configuration.

| File | Purpose |
| --- | --- |
| `Main.lean` | Initial Lean verification check |
| `Jacobi2.lean` | Two-site integer Jacobi matrix and symmetry |
| `JacobiGeneral.lean` | Finite integer-valued Jacobi entries and symmetry |
| `JacobiReal.lean` | Finite real Jacobi Hamiltonian |
| `JacobiEvolution.lean` | Complex Hamiltonian and evolution generator |
| `MatrixExpProbe.lean` | Finite propagator, unitarity and conservation |
| `KrylovNumber.lean` | Number operator, moments, variance and normalization |
| `KrylovGram.lean` | Complex Gram coordinates and nonnegative Gram sum |
| `KrylovLagrange.lean` | Finite complex Lagrange identity |
| `KrylovGap.lean` | Gram gap, centered variance, complexity differentiation and complex-time derivative |
| `P72_3a_Minimal.lean` | Isolated complex-time derivative verification |
| `P73_RealTime.lean` | P73.1 propagator derivative |
| `P73_2_State.lean` | P73.2 state derivative |
| `P74_1_Components.lean` | P74.1 component derivatives |
| `P74_2_KrylovDerivative.lean` | P74.2 physical Krylov complexity derivative |
| `lean-toolchain` | Lean toolchain version |
| `lakefile.toml` | mathlib dependency specification |
| `.github/workflows/lean.yml` | Main Lean verification workflow |
| `.github/workflows/p72-minimal.yml` | Historical isolated P72 verification workflow |

The P74.1 and P74.2 files were reported as explicitly compiled by the successful post-merge GitHub Actions #117 workflow.

The exact workflow commands and source tree should be inspected when independently reproducing this checkpoint.

---

## 5. Historical verification and reproducibility

### 5.1. Historical P71 checkpoint

| Item | Record |
| --- | --- |
| Checkpoint | P71 |
| Date | 17 October 2026 |
| Verification | [GitHub Actions #84: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) |
| Source commit | `85f799e6defae7f9106a10c4fd9f780d27cf2b4f` |
| Lean | `v4.24.0` |
| mathlib configuration | `v4.24.0` |
| Reported mathlib revision | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |

The P71 workflow compiled ten Lean files.

The source files inspected at that checkpoint contained no reported `sorry`, `admit` or locally declared artificial axioms.

The complete axiom dependencies of every historical declaration were not separately audited at P71.

### 5.2. P73.1 checkpoint

P73.1 was integrated through Pull Request #1 on 18 October 2026.

The post-merge verification was GitHub Actions #103.

### 5.3. P73.2 checkpoint

P73.2 was integrated through Pull Request #2 on 19 October 2026.

The post-merge verification was GitHub Actions #109.

### 5.4. P74.2 checkpoint

P74.1 and P74.2 were integrated through Pull Request #3 on 20 October 2026.

The reported post-merge verification was GitHub Actions #117.

The reported merge commit was:

```text
3cc284d942bb73b977315fe5096033ce9ec37d42
```

The recorded axiom dependencies for the three P74 declarations contain the standard Lean axioms:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` was reported in these declaration dependencies.

### 5.5. Dependency reproducibility

At the earlier P73.2 checkpoint, the repository was reported not to contain a committed `lake-manifest.json`.

The workflow used `lake update`.

The current presence or absence of a dependency manifest should be checked against the actual P74.2 source commit rather than inferred from the historical P73.2 state.

A committed and reviewed dependency lockfile would improve reproducibility.

Successful workflow logs, source commits and compiler configurations remain essential parts of the verification record.

No unobserved dependency revision is asserted here.

---

## 6. Formal integrity and axiom policy

The project follows a strict verification policy.

### 6.1. Prohibited proof shortcuts

Verified checkpoints must not depend on:

- `sorry`
- `admit`
- Artificial project-specific axioms
- Circular hypotheses containing the desired conclusion
- Replacing a physical theorem with an unrelated conditional statement
- Unverified PASS claims
- Files omitted from the actual CI compilation sequence

The exact theorem statements, definitions and hypotheses must be preserved when repairing proofs.

A successful compiler result for a weakened or different statement is not evidence that the original statement was proved.

### 6.2. Axiom audit

The following declarations have reported axiom checks:

```lean
#print axioms Lanzarini.krylovComplexity_increment
#print axioms Lanzarini.krylovComplexity_hasDerivAt_components
#print axioms Lanzarini.jacobiEvolutionGenerator_time_factor
#print axioms Lanzarini.jacobiPropagator_complex_time_eq
#print axioms Lanzarini.jacobiComplexTimeExp_hasDerivAt
#print axioms Lanzarini.p73_jacobiPropagator_hasDerivAt
#print axioms Lanzarini.p73_jacobiState_hasDerivAt
#print axioms Lanzarini.p74_jacobiState_component_hasDerivAt
#print axioms Lanzarini.p74_jacobiState_parts_hasDerivAt
#print axioms Lanzarini.p74_krylovComplexityAt_hasDerivAt
```

The recorded outputs list:

```text
[propext, Classical.choice, Quot.sound]
```

for these selected declarations.

The P74 reports contain no `sorryAx`.

This does not constitute an exhaustive audit of every historical theorem.

Additional audits should inspect:

```lean
#print axioms Lanzarini.krylovLagrange_finite
#print axioms Lanzarini.krylovGram_realPart_gap
#print axioms Lanzarini.krylovCenteredState_normSq
#print axioms Lanzarini.krylovCenteredState_gap_at
```

The results of these additional probes must not be reported as completed until their actual outputs have been inspected.

### 6.3. Verification procedure

Every future milestone should follow this procedure:

1. Freeze the intended mathematical statement.
2. Check all definitions and assumptions.
3. Develop the proof in a separate branch.
4. Compile the new source file explicitly.
5. Inspect the theorem's actual axiom dependencies.
6. Confirm that no artificial proof shortcuts were introduced.
7. Verify the complete dependency chain.
8. Merge only after successful verification.
9. Run the complete workflow again on `main`.
10. Record the exact verified commit and workflow.
11. Compare the formal statement with the intended mathematical theorem.
12. Distinguish formal verification from independent scientific review.

A development-branch success does not automatically certify the merged `main` branch.

---

## 7. Next research checkpoint: P75

**Status: Not yet verified.**

P75 is dedicated to the centered physical Krylov derivative.

It is the next step toward the finite-dimensional Krylov dispersion speed limit.

### 7.1. Mathematical target

For a normalized evolved state, define:

```math
K(t)=\langle\psi(t),N\psi(t)\rangle.
```

Let the centered Krylov vector be:

```math
u(t)=(N-K(t)I)\psi(t).
```

The target identity is:

```math
\frac{dK(t)}{dt}
=
2\,\mathrm{Re}
\langle u(t),\dot{\psi}(t)\rangle.
```

The inner-product convention must be checked against the exact Lean definitions.

The identity requires the normalization condition:

```math
\|\psi(t)\|^2=1.
```

The previously verified unitarity theorem provides norm conservation from a normalized initial state.

### 7.2. Mathematical proof strategy

First, use the P74.2 physical complexity derivative to obtain:

```math
\dot K(t)
=
2\,\mathrm{Re}
\langle N\psi(t),\dot{\psi}(t)\rangle.
```

Second, use norm conservation and state differentiability to establish:

```math
\mathrm{Re}
\langle\psi(t),\dot{\psi}(t)\rangle=0.
```

Then:

```math
\begin{aligned}
\dot K(t)
&=
2\,\mathrm{Re}
\langle N\psi(t),\dot{\psi}(t)\rangle\\
&=
2\,\mathrm{Re}
\langle
(N-K(t)I)\psi(t),
\dot{\psi}(t)
\rangle.
\end{aligned}
```

The proof must explicitly justify the real-inner-product convention and scalar manipulations used in Lean.

No desired centered identity may be introduced as a hypothesis.

### 7.3. Required Lean dependencies

P75 should reuse the established theorems for:

- Unitary Jacobi evolution.
- Norm conservation.
- Centered Krylov state.
- Normalized Krylov variance.
- Physical state derivative P73.2.
- Physical complexity derivative P74.2.

Any additional lemma must be proved from the existing formal framework.

### 7.4. P75 acceptance criteria

P75 may be declared verified only when:

1. The intended centered identity is precisely encoded.
2. The normalization hypothesis is explicit.
3. The proof uses the actual evolved Jacobi state.
4. No circular derivative assumption is introduced.
5. The theorem compiles under Lean 4 and mathlib.
6. Its axiom dependencies are inspected.
7. The development workflow succeeds.
8. The theorem is merged into `main`.
9. The post-merge verification succeeds.

Until then, **P75 remains a research target**.

---

## 8. Remaining scientific proof obligations

### 8.1. Centered physical derivative

Complete P75.

This is the immediate next step.

### 8.2. Energy variance and velocity norm

Establish the conserved physical quantity required for the Krylov dispersion speed limit.

For an initial state at the first basis vector, the centered energy fluctuation must be handled correctly.

A nonzero diagonal entry contributes to the energy expectation but does not automatically increase the energy variance by its square.

The formal proof must preserve this distinction.

### 8.3. Physical dispersion speed limit

Use the verified Gram identity, centered variance and physical derivative to establish the finite-dimensional bound.

Under the preprint's initial-state assumptions, the intended bound involves the first physical coupling `b_1`.

The result must include all necessary normalization, coupling and domain hypotheses.

This is not yet a verified Lean theorem.

### 8.4. Saturation-deficit definition and domain

Define:

```math
D(t)
=
1-
\frac{\dot K(t)^2}
{4b_1^2V(t)}.
```

The denominator must be proved nonzero wherever the quotient is used.

The physical nonnegativity statement must be derived from the appropriate speed-limit inequality.

The behavior at `t = 0` requires a separately justified extension or asymptotic treatment.

### 8.5. Finite-depth local defects

Formalize the diagonal and off-diagonal obstruction mechanisms.

In the preprint's coupling convention, define:

```math
c_0=0,\qquad c_j=b_j^2.
```

The third-difference defect is:

```math
\Omega_r
=
c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
```

The diagonal defect is:

```math
a_{r+3}-a_0.
```

These defects must be studied with the correct prefix conditions, coupling positivity and finite-chain boundaries.

### 8.6. Mixed finite-depth expansion

The preprint states a mixed diagonal/off-diagonal local-defect formula.

For `r >= 0`, set:

```math
m=r+3.
```

Under the appropriate finite-chain dimension and positivity assumptions, together with the prefix conditions:

```math
a_0=a_1=\cdots=a_{m-1}
```

and:

```math
\Omega_0=\cdots=\Omega_{r-1}=0,
```

where the latter condition is empty for `r = 0`, the preprint states:

```math
\begin{aligned}
D(t)
={}&
\frac{\prod_{j=2}^{m-1}c_j}
{[(m+1)!]^2}\\
&\cdot
\left[
4\Omega_r^2+
c_m(a_m-a_0)^2
\right]t^{2m}\\
&+O_H(t^{2m+2}).
\end{aligned}
```

This formula is a **research-preprint claim, not yet a machine-verified Lean theorem**.

The diagonal defect must not be silently removed from the general real-Jacobi statement.

Any terminal-boundary specialization requires its own hypotheses and proof.

### 8.7. Main finite-chain theorem

Formalize the precise counterpart of Theorem 8.1 in the research preprint.

The proof must preserve:

- The initial state.
- The finite-chain dimension conditions.
- Positive interior couplings.
- Diagonal prefix assumptions.
- Off-diagonal defect prefix assumptions.
- Boundary conventions.
- Leading coefficients.
- Remainder estimates.

### 8.8. Local rigidity

Formalize the finite-depth rigidity criterion associated with Theorem 9.1.

The terminal edges and coupling hypotheses must be handled explicitly.

### 8.9. Semi-infinite extension

Treat infinite-dimensional Jacobi operators separately.

Required topics include:

- Operator domains.
- Self-adjointness.
- Strongly continuous unitary evolution.
- Number-operator domain preservation.
- Weighted estimates.
- Conditions permitting differentiation of unbounded observables.

No semi-infinite conclusion is inferred from the existing finite-dimensional Lean development.

---

## 9. Research preprint and scientific target

**Title:** Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics

**Author:** Valentino Lanzarini

**DOI:** https://doi.org/10.5281/zenodo.23163367

The published preprint and the machine-checked Lean development are related but distinct scientific artifacts.

The central research target is the finite-depth hierarchy describing the first nonzero obstruction to saturation of the Krylov dispersion speed limit for general real Jacobi dynamics.

The proposed hierarchy includes two mechanisms:

1. Off-diagonal third-difference defects.
2. Diagonal inhomogeneity defects.

The main finite-chain hierarchy, its remainder estimates and its rigidity consequences have not yet been completely formalized in Lean.

The preprint must be evaluated independently for mathematical correctness, prior art and originality.

Successful verification of foundational Lean lemmas does not establish the novelty of the preprint's central research claims.

---

## 10. Scientific status and limitations

### 10.1. Established formalization

The reported successful checkpoints establish foundational results concerning:

- Finite real Jacobi matrices.
- Finite-dimensional unitary evolution.
- Norm and inner-product conservation.
- Krylov complexity and moments.
- Normalized Krylov variance.
- Zero-variance support restrictions.
- Complex Gram and Lagrange identities.
- Real-part Gram-gap identity.
- Centered-state/variance identity.
- Conditional Krylov complexity differentiation.
- Complex-time matrix exponential differentiation.
- Real-time propagator differentiation.
- Real-time evolved-state differentiation.
- Evolved-state coordinate differentiation.
- Physical Krylov complexity differentiation.

### 10.2. Not yet established in Lean

The repository does not yet claim a completed formal proof of:

- The centered physical Krylov derivative P75.
- The complete physical Krylov dispersion speed limit.
- The saturation-deficit nonnegativity theorem.
- The short-time saturation-deficit expansion.
- The full finite-depth local-defect hierarchy.
- The finite-chain rigidity criterion.
- The semi-infinite Jacobi extension.
- The general Lanczos basis-identification theorem.

### 10.3. Scientific interpretation

The foundational matrix-exponential and Schrödinger derivative identities are standard mathematical results.

Their formalization provides a verified infrastructure for studying the intended Krylov observables.

The possible mathematical originality of the finite-depth local-defect hierarchy remains a separate question requiring literature comparison and specialist review.

The project does not claim a new universal quantum speed limit.

The project does not claim worldwide mathematical priority based solely on GitHub Actions or AI-assisted analysis.

The project does not treat checkpoint numbers as a measure of mathematical completion.

---

## 11. Verification history

| Milestone | GitHub Actions | Status |
| --- | --- | --- |
| P71 | [#84](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) | SUCCESS |
| P72.3a | [#98](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849) | SUCCESS |
| P73.1 development | [#101](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527474) | SUCCESS |
| P73.1 main | [#103](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923) | SUCCESS |
| P73.2 development | [#108](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39204261981) | SUCCESS |
| P73.2 main | [#109](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293) | SUCCESS |
| P74 development | [#116](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39374579575) | SUCCESS |
| P74.2 main | [#117](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) | SUCCESS |
| P75 | Not yet assigned | NOT VERIFIED |

The status entries summarize the supplied verification history.

The corresponding GitHub logs and source commits are the authoritative records for reproduction.

---

## 12. Copyright and permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place original materials in the public domain.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas or theorems.

Third-party dependencies remain subject to their respective licenses.

---

## 13. AI-assisted research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not presented as independent peer review or scientific certification.

Mathematical claims must be evaluated through explicit proofs, reproducible checks and independent scientific scrutiny.

The author remains responsible for reviewing the research claims, published documentation and scope of the conclusions.

Automated theorem verification provides evidence for the validity of precisely encoded formal statements relative to Lean's foundations.

It does not independently certify mathematical originality or the accuracy of every translation from informal mathematics.

---

## 14. Author

**Valentino Lanzarini**

Independent Mathematical Researcher

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Research preprint:**  
https://doi.org/10.5281/zenodo.23163367

**GitHub:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**
