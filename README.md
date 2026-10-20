
# Lanzarini Krylov–Jacobi

### Lean 4 formalization of finite-dimensional Jacobi dynamics and Krylov observables

**Author:** Valentino Lanzarini, Independent Mathematical Researcher  
**Project status:** Research in progress  
**Latest verified formalization checkpoint:** **P74.2 (main, GitHub Actions #117: SUCCESS)**  
**Environment:** Lean 4 `v4.24.0` and mathlib `v4.24.0`  
**Research preprint:** https://doi.org/10.5281/zenodo.23163367  
**Repository:** [Open the GitHub repository](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/main)  
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

> **Scientific status.** This repository contains machine-checked foundational theorems about finite-dimensional Jacobi matrices, unitary evolution, Krylov moments and variance, complex Gram identities, matrix-exponential differentiation, the real-time Schrödinger equation, componentwise state derivatives, and the physical derivative of finite-dimensional Krylov complexity.
>
> **The main finite-depth local-defect hierarchy of the research preprint has not yet been formalized in Lean.**
>
> Successful GitHub Actions verification establishes that Lean accepted the encoded statements and proofs in the configured environment. It does not establish scientific originality, independent peer review, or verification of every claim in the preprint.

**Official integration history:**

- P72.3a.3 and P73.1 were integrated into `main` through [Pull Request #1](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/1) on 18 October 2026.
- P73.2 was integrated through [Pull Request #2](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/2) on 19 October 2026.
- P74.1 and P74.2 were integrated through [Pull Request #3](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3) on 20 October 2026.

**Latest reported post-merge verification:** [GitHub Actions #117: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938).

---

## 1. Latest verified checkpoint and reproducibility

### 1.1. Current verified checkpoint: P74.2

| Item | Verification record |
| --- | --- |
| Milestone | **P74.2** |
| Branch | `main` |
| Date | 20 October 2026 |
| Pull Request | [PR #3: merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3) |
| Post-merge verification | [GitHub Actions #117: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) |
| Development verification | [GitHub Actions #116: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39374579575) |
| Verified merge commit | `3cc284d942bb73b977315fe5096033ce9ec37d42` |
| Lean toolchain | `leanprover/lean4:v4.24.0` |
| mathlib configuration | `v4.24.0` |
| New source files | `P74_1_Components.lean`, `P74_2_KrylovDerivative.lean` |
| Recorded axiom dependencies | `[propext, Classical.choice, Quot.sound]` |
| `sorryAx` in the recorded P74 theorem dependencies | Not present |

The latest verified milestone establishes the physical derivative of finite-dimensional Krylov complexity along Jacobi evolution.

For

$$
\psi(t)=e^{-itH}\psi_0,
$$

define

$$
K(t)=\sum_{j=0}^{n-1}j|\psi_j(t)|^2.
$$

The formalized derivative identity is

$$
\boxed{
\frac{dK(t)}{dt}
=
2\sum_{j=0}^{n-1}
j\,\operatorname{Re}
\left(
\overline{\psi_j(t)}
(-iH\psi(t))_j
\right).
}
$$

This result follows from previously verified componentwise differentiation and the physical Jacobi-state derivative.

The desired physical derivative is not assumed as a hypothesis.

No normalization assumption is required for this particular identity.

**P74.2 does not yet establish the centered derivative identity, the Krylov dispersion speed limit, or the finite-depth local-defect hierarchy.**

### 1.2. Historical verified checkpoints

| Milestone | Verification | Source or merge commit |
| --- | --- | --- |
| P71 | [GitHub Actions #84: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) | `85f799e6defae7f9106a10c4fd9f780d27cf2b4f` |
| P72.3a.3 | [GitHub Actions #98: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849) | `702256d89e7623eafcabd188911166eaddb08c7a` |
| P73.1 | [GitHub Actions #103: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923) | `677985738a8e82aca8327ad3cc241ef8bc5e695d` |
| P73.2 | [GitHub Actions #109: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293) | `4e288ae3ce35e3f99c5630dd3fb436b30c3a36c9` |
| P74.2 | [GitHub Actions #117: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) | `3cc284d942bb73b977315fe5096033ce9ec37d42` |

The historical P71 verification used Lean 4 `v4.24.0` and mathlib `v4.24.0`.

Its CI log recorded the mathlib revision:

`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`

At P71, the source files compiled by the workflow were inspected for `sorry`, `admit`, and locally declared `axiom` statements. None were found.

The P73.1 and P73.2 milestones introduced additional verified derivative statements and explicit axiom audits.

The P74.2 milestone extends the formalization to the physical Krylov complexity derivative.

Milestone labels describe the development history. They do not measure percentage completion of the main research theorem.

### 1.3. Dependency reproducibility

The previously documented repository state did not include a committed `lake-manifest.json`.

The CI configuration executed `lake update`.

The dependency-lock status should be checked against the current P74.2 commit.

A reviewed and committed dependency manifest would improve environmental reproducibility if it remains absent.

The historical workflow logs, verified commits, source files and toolchain declarations provide verification records.

No unobserved dependency revision is asserted.

---

## 2. Mathematical framework and conventions

For a finite dimension `n`, the code defines a real symmetric tridiagonal Jacobi matrix using:

`a b : Fin n → ℝ`

Its entries are

$$
H_{ii}=a_i,
\qquad
H_{i,i+1}=H_{i+1,i}=b_i.
$$

All other entries vanish.

The coupling formula applies only to valid adjacent indices.

The foundational definitions allow arbitrary real diagonal and off-diagonal coefficients.

The positivity of physical couplings is not built into the general definitions.

Specific results requiring positive interior couplings must state those hypotheses explicitly.

### 2.1. Index conventions

Lean uses zero-based `Fin n` indices.

The off-diagonal input `b i` couples sites `i` and `i+1`, where the adjacent pair exists.

The last entry of the `Fin n` coupling input is unused.

In the preprint, the first physical coupling is called $b_1$.

The correspondence is

$$
b_j^{\mathrm{preprint}}
=
b_{j-1}^{\mathrm{Lean}},
\qquad
1\le j\le n-1.
$$

These conventions must be preserved when formalizing local defects and boundary terms.

### 2.2. Krylov basis identification

The operator named `krylovNumberOperator` acts on the chosen coordinate basis.

The repository does not yet formalize a general Lanczos algorithm or prove that this coordinate basis is the Krylov basis generated by an arbitrary Hamiltonian and initial state.

Identifying the Jacobi-chain basis with a genuine Lanczos/Krylov basis requires the appropriate construction and hypotheses.

### 2.3. Finite-dimensional Jacobi evolution

For the complex representation of the Jacobi Hamiltonian,

$$
U(t)=\exp(-itH),
$$

and

$$
\psi(t)=U(t)\psi_0.
$$

The finite-dimensional propagator is formally proved unitary.

The repository establishes preservation of norms, inner products and orthogonality.

P73.1 establishes

$$
U'(t)=(-iH)U(t).
$$

P73.2 establishes

$$
\psi'(t)=(-iH)\psi(t).
$$

P74.1 establishes the corresponding component derivatives.

P74.2 establishes the physical derivative of Krylov complexity along this evolution.

No normalization assumption is required for the propagator derivative, state derivative, or the P74.2 complexity derivative.

### 2.4. Infinite-dimensional scope

The repository does not yet define and establish the required self-adjointness properties of a general unbounded Jacobi operator on

$$
\ell^2(\mathbb N_0).
$$

Infinite-dimensional evolution requires separate treatment of operator domains, differentiability, weighted estimates and the domain of the number operator.

None of these extensions follows automatically from the finite-dimensional results.

---

## 3. Verified theorem development through P74.2

| Checkpoints | Formalized content | Source files |
| --- | --- | --- |
| P51–P55 | Hermitian finite Jacobi Hamiltonian, anti-Hermitian generator, unitary propagator, norm, inner-product and orthogonality preservation | `JacobiReal.lean`, `JacobiEvolution.lean`, `MatrixExpProbe.lean` |
| P56–P59 | Krylov number operator, complexity, second moment, algebraic variance and normalization preservation | `KrylovNumber.lean` |
| P60–P61 | Centered variance, normalized variance nonnegativity and zero-variance equivalences | `KrylovNumber.lean` |
| P62–P64 | Zero-variance support constraints and unique occupied Krylov level | `KrylovNumber.lean` |
| P65–P69 | Complex Gram coordinates, finite Gram sum and Lagrange identity | `KrylovGram.lean`, `KrylovLagrange.lean` |
| P70 | Exact real-part Gram-gap identity and nonnegativity | `KrylovGap.lean` |
| P71 | Centered-state norm/variance identity and evolved-state specialization | `KrylovGap.lean` |
| P72.1 | Exact algebraic increment of Krylov complexity | `KrylovGap.lean` |
| P72.2 | Conditional componentwise Krylov differentiation | `KrylovGap.lean` |
| P72.3a.1–P72.3a.3 | Generator factorization, complex-time propagator representation and matrix-exponential derivative | `KrylovGap.lean` |
| P73.1 | Real-time Jacobi propagator derivative | `P73_RealTime.lean` |
| P73.2 | Real-time evolved Jacobi-state derivative | `P73_2_State.lean` |
| **P74.1** | **Complex, real and imaginary component derivatives of the physical state** | `P74_1_Components.lean` |
| **P74.2** | **Physical Krylov complexity derivative along Jacobi evolution** | `P74_2_KrylovDerivative.lean` |

The Lean declarations include:

- `Lanzarini.jacobiEvolutionGenerator_conjTranspose`
- `Lanzarini.jacobiPropagator_unitary`
- `Lanzarini.jacobiNormSq_state`
- `Lanzarini.jacobiInner_state_pair`
- `Lanzarini.krylovComplexity_expectation`
- `Lanzarini.krylovVariance_centered`
- `Lanzarini.krylovVariance_zero_existsUnique_occupied`
- `Lanzarini.krylovGramSum_nonneg`
- `Lanzarini.krylovLagrange_finite`
- `Lanzarini.krylovGram_realPart_gap`
- `Lanzarini.krylovGram_realPart_gap_nonneg`
- `Lanzarini.krylovCenteredState_normSq`
- `Lanzarini.krylovCenteredState_normSq_at`
- `Lanzarini.krylovCenteredState_gap_at`
- `Lanzarini.krylovComplexity_increment`
- `Lanzarini.krylovComplexity_hasDerivAt_components`
- `Lanzarini.jacobiEvolutionGenerator_time_factor`
- `Lanzarini.jacobiPropagator_complex_time_eq`
- `Lanzarini.jacobiComplexTimeExp_hasDerivAt`
- `Lanzarini.p73_jacobiPropagator_hasDerivAt`
- `Lanzarini.p73_jacobiState_hasDerivAt`
- `Lanzarini.p74_jacobiState_component_hasDerivAt`
- `Lanzarini.p74_jacobiState_parts_hasDerivAt`
- `Lanzarini.p74_krylovComplexityAt_hasDerivAt`

### 3.1. Krylov moments and normalization

For a finite vector

$$
\psi\in\mathbb C^n,
$$

define

$$
K(\psi)=\sum_{j=0}^{n-1}j|\psi_j|^2,
$$

$$
K_2(\psi)=\sum_{j=0}^{n-1}j^2|\psi_j|^2,
$$

and

$$
V(\psi)=K_2(\psi)-K(\psi)^2.
$$

The code defines the algebraic expression $V$ for arbitrary finite vectors.

The interpretation as a variance requires normalization:

$$
\|\psi\|^2=1.
$$

Under this hypothesis, Lean proves

$$
\boxed{
V(\psi)
=
\sum_{j=0}^{n-1}
(j-K(\psi))^2|\psi_j|^2
\ge0.
}
$$

If a normalized state has zero variance, Lean proves that precisely one index has positive squared amplitude.

This is a finite Krylov-level distribution property.

It is not the finite-depth local-defect hierarchy.

### 3.2. Complex Gram/Lagrange identity: P69

For arbitrary finite vectors

$$
u,v\in\mathbb C^n,
$$

define

$$
G(u,v)
=
\sum_{0\le i<j<n}
|u_iv_j-u_jv_i|^2.
$$

The following classical identity is formalized:

$$
\boxed{
G(u,v)
=
\|u\|^2\|v\|^2
-
|\langle u,v\rangle|^2
\ge0.
}
$$

Each unordered pair is counted once.

The determinant coordinate contains no conjugation.

P69 does not assert that this classical identity is new.

### 3.3. Real-part Gram gap: P70

For arbitrary finite complex vectors,

$$
\boxed{
\|u\|^2\|v\|^2
-
\bigl(\operatorname{Re}\langle u,v\rangle\bigr)^2
=
G(u,v)
+
\bigl(\operatorname{Im}\langle u,v\rangle\bigr)^2
\ge0.
}
$$

This is an algebraic identity.

Its physical specialization requires the appropriate dynamical arguments.

### 3.4. Centered-state/variance bridge: P71

Let

$$
N=\operatorname{diag}(0,1,\ldots,n-1),
$$

and set

$$
u=(N-K(\psi))\psi.
$$

For a normalized state, Lean proves

$$
\boxed{
\|u\|^2=V(\psi).
}
$$

The same identity is established for the evolved state when the initial state is normalized.

The real-part Gram gap is also applied to the centered evolved state and an arbitrary auxiliary complex vector.

This provides a formal foundation for the planned speed-limit proof.

### 3.5. Krylov complexity differentiation: P72.1–P72.2

P72.1 establishes an exact algebraic increment formula for finite-dimensional Krylov complexity.

P72.2 establishes the derivative formula for a general complex-state curve with explicitly assumed componentwise differentiability.

For a differentiable curve,

$$
\frac{dK}{dt}
=
2\sum_{j=0}^{n-1}
j\operatorname{Re}
\left(
\overline{\psi_j(t)}
\dot\psi_j(t)
\right).
$$

At P72.2, this was a conditional differentiation theorem.

**P74.2 subsequently establishes the corresponding theorem for actual finite-dimensional Jacobi evolution.**

### 3.6. Complex-time matrix exponential derivative: P72.3a

P72.3a.1 establishes factorization of the Jacobi evolution generator.

P72.3a.2 connects the real-time propagator with the complex-time matrix exponential.

P72.3a.3 establishes

$$
\boxed{
\frac{d}{dz}\exp(zA)
=
A\exp(zA),
\qquad A=-iH.
}
$$

The proof uses the matrix operator-norm structure and matrix-exponential differentiation machinery available in mathlib.

**Historical verification:**

- [GitHub Actions #98: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849)
- Source commit: `702256d89e7623eafcabd188911166eaddb08c7a`
- Recorded axioms: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx` in the recorded theorem dependencies.

This is a standard analytical ingredient, not a new discovery.

### 3.7. Real-time Jacobi propagator derivative: P73.1

P73.1 establishes

$$
\boxed{
\frac{d}{dt}U(t)=(-iH)U(t).
}
$$

The verified declaration is

`Lanzarini.p73_jacobiPropagator_hasDerivAt`

The proof derives the real-time result from the complex-time derivative using mathlib's differentiability machinery.

No normalization assumption is required.

The propagator derivative is not assumed as a hypothesis.

**Verification record:**

- [GitHub Actions #101: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527474)
- Source commit: `a291e152b9ea3feed8f7c0608ae8eaca33700298`
- [PR #1: merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/1)
- [GitHub Actions #103 on main: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923)
- Merge commit: `677985738a8e82aca8327ad3cc241ef8bc5e695d`
- Recorded axioms: `[propext, Classical.choice, Quot.sound]`

### 3.8. Real-time Schrödinger state derivative: P73.2

P73.2 establishes the derivative of

$$
\psi(t)=U(t)\psi_0.
$$

The verified identity is

$$
\boxed{
\frac{d}{dt}\psi(t)=(-iH)\psi(t).
}
$$

The proof uses the P73.1 propagator derivative and the continuous linear map applying a matrix to the fixed initial state.

It then uses associativity of matrix-vector multiplication.

The exact Lean theorem is:

```lean
theorem p73_jacobiState_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    HasDerivAt
      (fun s : ℝ => jacobiState n a b s psi)
      (((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi))
      t
```

The theorem does not assume the desired state derivative.

No normalization assumption is required.

**Verification record:**

- [GitHub Actions #108: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39204261981)
- Verified proof commit: `9489b44a880688790e6dc65d422d90755d57a341`
- Source: `P73_2_State.lean`
- Recorded axioms: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx` in the recorded theorem dependencies.
- [PR #2: merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/2)
- [GitHub Actions #109: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293)
- Merge commit: `4e288ae3ce35e3f99c5630dd3fb436b30c3a36c9`

This is a standard finite-dimensional Schrödinger evolution identity.

Its formalization provides a rigorous connection between the matrix propagator and the evolving state.

It does not constitute a new physical law.

### 3.9. Jacobi-state component derivatives: P74.1

**Source file:** `P74_1_Components.lean`

The verified declarations are:

```lean
Lanzarini.p74_jacobiState_component_hasDerivAt
Lanzarini.p74_jacobiState_parts_hasDerivAt
```

For finite-dimensional Jacobi evolution,

$$
\psi(t)=e^{-itH}\psi_0,
$$

the complex-coordinate derivative is

$$
\boxed{
\frac{d}{dt}\psi_j(t)
=
(-iH\psi(t))_j.
}
$$

The corresponding real and imaginary coordinate derivatives are also formally established.

These results follow from the previously verified P73.2 state derivative.

The desired component derivatives are not assumed.

P74.1 provides the componentwise differentiability required to specialize the P72.2 complexity derivative to the physical evolution.

### 3.10. Physical Krylov complexity derivative: P74.2

**Source file:** `P74_2_KrylovDerivative.lean`

**Verified declaration:**

```lean
Lanzarini.p74_krylovComplexityAt_hasDerivAt
```

Define

$$
K(t)=\sum_{j=0}^{n-1}j|\psi_j(t)|^2,
$$

where

$$
\psi(t)=e^{-itH}\psi_0.
$$

The verified physical derivative is

$$
\boxed{
\frac{dK(t)}{dt}
=
2\sum_{j=0}^{n-1}
j\operatorname{Re}
\left(
\overline{\psi_j(t)}
(-iH\psi(t))_j
\right).
}
$$

The proof follows from:

1. P72.2: conditional componentwise Krylov differentiation.
2. P73.2: derivative of the evolved Jacobi state.
3. P74.1: complex, real and imaginary coordinate derivatives.

The desired physical Krylov derivative is not assumed.

No normalization assumption is required for this specific derivative identity.

**Official verification record:**

- [Pull Request #3: merged](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3)
- [Development GitHub Actions #116: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39374579575)
- [Post-merge GitHub Actions #117: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938)
- Verified merge commit: `3cc284d942bb73b977315fe5096033ce9ec37d42`

The recorded P74 axiom dependencies are

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears in the reported dependencies of the three P74 declarations.

**Scientific limitation:** P74.2 establishes the physical complexity derivative in finite dimensions.

It does not yet establish the centered derivative identity, the complete Krylov dispersion speed-limit inequality, the saturation-deficit expansion, or the finite-depth local-defect hierarchy.

---

## 4. Repository structure

| File | Purpose |
| --- | --- |
| `Main.lean` | Initial Lean verification check |
| `Jacobi2.lean` | Two-site integer Jacobi matrix and symmetry |
| `JacobiGeneral.lean` | Finite integer-valued Jacobi entries and symmetry |
| `JacobiReal.lean` | Finite real Jacobi Hamiltonian |
| `JacobiEvolution.lean` | Complex Hamiltonian and anti-Hermitian evolution generator |
| `MatrixExpProbe.lean` | Finite propagator, unitarity and conservation theorems |
| `KrylovNumber.lean` | Number operator, moments, normalized variance and zero-variance constraints |
| `KrylovGram.lean` | Complex Gram coordinates and nonnegative Gram sum |
| `KrylovLagrange.lean` | Finite-dimensional complex Lagrange identity |
| `KrylovGap.lean` | P70–P72.3a foundational identities and differentiation |
| `P72_3a_Minimal.lean` | Isolated complex-time matrix-exponential verification |
| `P73_RealTime.lean` | P73.1 real-time Jacobi propagator derivative |
| `P73_2_State.lean` | P73.2 evolved Jacobi-state derivative |
| `P74_1_Components.lean` | P74.1 componentwise state derivatives |
| `P74_2_KrylovDerivative.lean` | P74.2 physical Krylov complexity derivative |
| `lean-toolchain` | Lean toolchain specification |
| `lakefile.toml` | mathlib dependency specification |
| `.github/workflows/lean.yml` | Main GitHub Actions verification workflow |
| `.github/workflows/p72-minimal.yml` | Separate verification workflow for the isolated P72.3a proof |

The P74 post-merge verification explicitly compiled the two new P74 source files.

The exact current workflow contents should be consulted when reproducing the compilation sequence.

---

## 5. Verification environment and integrity policy

The repository uses Lean 4, mathlib, Lake and GitHub Actions.

The historical P71 workflow #84 compiled ten Lean files in dependency order.

Workflow #103 on `main` compiled eleven Lean files through P73.1.

Workflow #109 on `main` compiled twelve Lean files through P73.2.

The P74 post-merge workflow #117 compiled the updated development, including the two P74 source files.

**Latest reported verification:**

[Lean 4 Verification #117 on main: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938)

Verified merge commit:

```text
3cc284d942bb73b977315fe5096033ce9ec37d42
```

### 5.1. Proof integrity requirements

Future formalization work must follow these rules:

1. Freeze the theorem statement before repairing a proof.
2. Compare the mathematical hypotheses against the previously verified version.
3. Audit definitions on which the theorem depends.
4. Confirm that every new source file is compiled by the official CI workflow.
5. Retain commit history and failed-run evidence where possible.
6. Verify normalization, positivity, coupling indices and finite boundaries.
7. Record actual `#print axioms` output for selected declarations.
8. Do not introduce `sorry`, `admit`, artificial axioms or circular hypotheses.
9. Preserve the mathematical meaning of declarations during proof repairs.
10. Verify new developments on a separate branch before integration.
11. Require successful post-merge verification on `main`.
12. Do not claim the preprint's main theorem has been formalized until its precise statement and proof have been checked.
13. Do not interpret checkpoint numbers as percentages of mathematical completion.
14. Distinguish formal verification from scientific novelty and peer review.

### 5.2. Axiom audit

The recorded P74 theorem probes are:

```lean
#print axioms Lanzarini.p74_jacobiState_component_hasDerivAt
#print axioms Lanzarini.p74_jacobiState_parts_hasDerivAt
#print axioms Lanzarini.p74_krylovComplexityAt_hasDerivAt
```

The reported dependencies are:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears in the recorded dependencies of these declarations.

Earlier recorded probes include:

```lean
#print axioms Lanzarini.krylovComplexity_increment
#print axioms Lanzarini.krylovComplexity_hasDerivAt_components
#print axioms Lanzarini.jacobiEvolutionGenerator_time_factor
#print axioms Lanzarini.jacobiPropagator_complex_time_eq
#print axioms Lanzarini.jacobiComplexTimeExp_hasDerivAt
#print axioms Lanzarini.p73_jacobiPropagator_hasDerivAt
#print axioms Lanzarini.p73_jacobiState_hasDerivAt
```

Their recorded outputs list:

```text
[propext, Classical.choice, Quot.sound]
```

These reports concern the specified declarations.

They are not an exhaustive axiom audit of every theorem in the repository.

Additional probes may inspect:

```lean
#print axioms Lanzarini.krylovLagrange_finite
#print axioms Lanzarini.krylovGram_realPart_gap
#print axioms Lanzarini.krylovCenteredState_normSq
#print axioms Lanzarini.krylovCenteredState_gap_at
```

The dedicated record for these additional probes remains pending.

No unobserved audit result is claimed.

### 5.3. Branch and integration policy

The officially verified P74.2 checkpoint is integrated into the default branch:

```text
main
```

Historical integrations:

- PR #1: P72.3a.3 and P73.1.
- PR #2: P73.2.
- PR #3: P74.1 and P74.2.

The former development branches remain available for historical traceability where retained in the repository.

Future research milestones should be developed separately and merged only after their complete verification and axiom checks pass.

A successful development-branch workflow does not itself certify the merged branch.

---

## 6. Scientific target and unverified steps

The research preprint studies the loss of saturation of a Krylov dispersion speed limit for real Jacobi evolution initialized at the first basis state

$$
\psi_0=e_0.
$$

In the preprint's one-based coupling convention, define

$$
c_0=0,
\qquad
c_j=b_j^2,
$$

and

$$
\boxed{
\Omega_r
=
c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
}
$$

Where the denominator is nonzero, the preprint's dimensionless saturation deficit is

$$
\boxed{
D(t)
=
1-
\frac{\dot K(t)^2}{4b_1^2V(t)}.
}
$$

The normalized deficit is studied for sufficiently small nonzero times, together with its appropriate short-time extension at zero.

Its nonnegativity depends on establishing the required dispersion speed-limit inequality under the correct dynamical assumptions.

### 6.1. Mixed finite-depth local-defect formula

The preprint states a mixed finite-depth local-defect expansion.

For

$$
r\ge0,
\qquad
m=r+3,
$$

consider a finite real Jacobi chain with dimension

$$
d\ge m+1,
$$

positive interior couplings, and initial state $e_0$.

Assume

$$
a_0=a_1=\cdots=a_{m-1},
$$

and

$$
\Omega_0=\cdots=\Omega_{r-1}=0,
$$

where the defect condition is empty for $r=0$.

The preprint states the leading mixed form

$$
\boxed{
D(t)
=
\frac{\displaystyle\prod_{j=2}^{m-1}c_j}
{[(m+1)!]^2}
\left[
4\Omega_r^2+
c_m(a_m-a_0)^2
\right]
t^{2m}
+
O_H(t^{2m+2}).
}
$$

The diagonal defect $a_m-a_0$ is part of the general finite-dimensional research claim.

The simplified expression involving only $\Omega_r^2$ is not an unconditional version of the mixed real-Jacobi result.

In terminal-boundary settings, the relevant boundary and positivity assumptions must be checked separately.

**This expansion is stated in the research preprint but has not yet been formalized as a Lean theorem in the repository.**

The complete hierarchy, remainder estimates, rigidity statements and any infinite-dimensional extension remain subject to further mathematical verification.

### 6.2. Completed foundational derivative steps

The following results are verified:

- P72.1: exact increment of finite-dimensional Krylov complexity.
- P72.2: conditional componentwise complexity differentiation.
- P72.3a.1: factorization of the Jacobi evolution generator.
- P72.3a.2: complex-time representation of the propagator.
- P72.3a.3: complex-time matrix-exponential derivative.
- P73.1: real-time propagator derivative.
- P73.2: real-time evolved-state derivative.
- P74.1: physical componentwise state derivatives.
- P74.2: physical Krylov complexity derivative.

These are machine-checked foundational results.

They do not yet prove the central local-defect hierarchy of the preprint.

---

## 7. Next research checkpoint: P75

### 7.1. Centered physical Krylov derivative

**Status: NOT YET VERIFIED**

The next formalization objective is the centered physical Krylov derivative.

For a normalized initial state,

$$
\|\psi_0\|^2=1,
$$

unitary evolution preserves normalization:

$$
\|\psi(t)\|^2=1.
$$

Let

$$
N=\operatorname{diag}(0,1,\ldots,n-1),
$$

and

$$
K(t)=\sum_{j=0}^{n-1}j|\psi_j(t)|^2.
$$

Define the centered state

$$
u(t)=(N-K(t))\psi(t).
$$

The target identity is

$$
\boxed{
\dot K(t)
=
2\operatorname{Re}
\langle u(t),\dot\psi(t)\rangle.
}
$$

For the physical Jacobi evolution,

$$
\dot\psi(t)=(-iH)\psi(t).
$$

The corresponding physical target is

$$
\boxed{
\dot K(t)
=
2\operatorname{Re}
\left\langle
(N-K(t))\psi(t),
(-iH)\psi(t)
\right\rangle.
}
$$

The precise inner-product convention must match the definitions used in Lean.

Because the real part is invariant under complex conjugation, the corresponding reversed inner-product ordering gives the same real quantity.

### 7.2. Mathematical proof strategy

First, use the P74.2 physical complexity derivative to obtain

$$
\dot K(t)
=
2\operatorname{Re}
\langle N\psi(t),\dot\psi(t)\rangle.
$$

Second, use norm conservation and state differentiability to establish

$$
\operatorname{Re}
\langle\psi(t),\dot\psi(t)\rangle=0.
$$

Then

$$
\begin{aligned}
2\operatorname{Re}
\langle(N-K(t))\psi(t),\dot\psi(t)\rangle
&=
2\operatorname{Re}
\langle N\psi(t),\dot\psi(t)\rangle\\
&\quad-
2K(t)\operatorname{Re}
\langle\psi(t),\dot\psi(t)\rangle\\
&=\dot K(t).
\end{aligned}
$$

This is the mathematical proof target.

The Lean implementation must derive the identity from previously verified theorems without introducing circular assumptions.

### 7.3. P75 acceptance criteria

P75 may be declared verified only when:

1. Its precise theorem statement is encoded in Lean.
2. The proof compiles in the configured Lean/mathlib environment.
3. It uses the physical derivative and normalization conservation theorems.
4. No circular hypotheses are introduced.
5. Its actual axiom dependencies are recorded.
6. The new file is explicitly compiled by the official CI workflow.
7. Development-branch verification succeeds.
8. The proof is integrated into `main`.
9. Post-merge verification succeeds.

**P75 is not yet verified.**

---

## 8. Subsequent formal proof obligations

### 8.1. Energy and velocity norm

Establish the conserved quantity required by the Krylov dispersion speed limit under the initial-state assumptions of the preprint.

For the Jacobi evolution initialized at $e_0$, the relevant velocity norm must be derived from the Hamiltonian and conserved quantities, not assumed.

### 8.2. Physical Krylov speed-limit inequality

Combine the centered derivative, normalized variance and Gram/Cauchy–Schwarz inequality.

The intended intermediate inequality is

$$
|\dot K(t)|
\le
2\sqrt{V(t)}\,\|\dot\psi(t)\|.
$$

Under the preprint's initial-state assumptions and the appropriate conserved velocity norm, derive the physical bound involving the first coupling $b_1$.

The centered energy fluctuation and the possible diagonal energy contribution must be treated correctly.

This is not yet a verified Lean theorem.

### 8.3. Saturation-deficit definition and domain

Define

$$
D(t)
=
1-
\frac{\dot K(t)^2}{4b_1^2V(t)}
$$

with explicit nonzero-denominator conditions.

Prove the relevant nonnegativity statement on its justified domain.

### 8.4. Finite-depth local defects

Formalize the diagonal and off-diagonal defects, finite-chain boundary conventions, leading Taylor coefficients and required remainder estimates.

### 8.5. Main finite-chain theorem

Prove the precise counterpart of Theorem 8.1 in the research preprint.

All mathematical hypotheses and finite-boundary conditions must be preserved.

### 8.6. Local rigidity

Formalize the finite-depth rigidity criterion corresponding to Theorem 9.1.

The hypotheses on positive couplings and terminal edges must be explicit.

### 8.7. Semi-infinite extension

Treat unbounded operator domains, self-adjointness, weighted estimates and infinite-dimensional evolution separately.

These remain research objectives, not verified Lean milestones.

---

## 9. Scientific status and limitations

The project currently establishes the physical derivative of finite-dimensional Krylov complexity through P74.2.

It does **not** claim:

- A completed Lean proof of the centered physical Krylov derivative.
- A completed Lean proof of the physical Krylov dispersion speed limit.
- A completed Lean proof of the saturation-deficit expansion.
- A completed Lean proof of the finite-depth local-defect hierarchy.
- A completed Lean proof of the main rigidity theorem.
- A new universal quantum speed limit.
- Independent peer-review certification.
- Established worldwide mathematical priority.
- Formal validity for arbitrary unbounded Jacobi operators.
- That milestone counts measure percentage completion of the research objective.

The finite-dimensional Schrödinger state derivative and Krylov complexity derivative are standard consequences of the dynamical framework.

Their formalization establishes checked infrastructure for studying the more specialized local-defect claims.

Lean verifies proofs relative to the precise encoded statements, definitions, assumptions and accepted foundations.

Scientific evaluation also requires the encoded theorem to match the intended mathematical claim.

That correspondence remains an explicit audit responsibility.

The mathematical novelty of the local-defect hierarchy remains subject to independent literature analysis and specialist review.

---

## 10. Research preprint

**Title:** Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics  
**Author:** Valentino Lanzarini  
**DOI:** https://doi.org/10.5281/zenodo.23163367

The published preprint and the machine-checked formal development are related but distinct scientific artifacts.

The preprint presents the proposed finite-depth hierarchy describing the first nonzero obstruction to saturation of the Krylov dispersion bound.

The proposed hierarchy combines:

- Off-diagonal third-difference defects, measured by $\Omega_r$.
- Diagonal inhomogeneity, measured by $a_{r+3}-a_0$.

The Lean repository currently contains verified foundational results through P74.2.

The main finite-chain theorem, its remainder estimates and its rigidity consequences have not yet been fully formalized.

---

## 11. Copyright and permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place original materials in the public domain.

Copyright protects original expression but does not confer exclusive ownership of mathematical facts, ideas or theorems.

Third-party dependencies remain subject to their respective licenses.

---

## 12. AI-assisted research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not presented as independent peer review or scientific certification.

Mathematical claims must be evaluated through explicit proofs, reproducible checks and independent scientific scrutiny.

The author remains responsible for reviewing the research claims, the published documentation and the scope of the conclusions.

Automated theorem verification provides evidence for the validity of the encoded statements relative to Lean's foundations.

It does not independently establish scientific originality or certify every translation from informal mathematics into formal code.

---

## 13. Author

**Valentino Lanzarini**

Independent Mathematical Researcher

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Research:**  
https://doi.org/10.5281/zenodo.23163367

**GitHub:**  
[Repository on GitHub](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/main)

---

Copyright © 2026 Valentino Lanzarini. All rights reserved.
