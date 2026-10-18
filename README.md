
# Lanzarini Krylov–Jacobi

### Lean 4 formalization of finite-dimensional Jacobi dynamics and Krylov observables

**Author:** Valentino Lanzarini, Independent Mathematical Researcher  
**Project status:** Research in progress  
**Latest verified formalization checkpoint:** **P73.1 (test branch, GitHub Actions #101: SUCCESS)**  
**Environment:** Lean 4 `v4.24.0` and mathlib `v4.24.0`  
**Research preprint:** https://doi.org/10.5281/zenodo.23163367  
**Repository:** [Open the GitHub repository](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/main)  
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

> **Scientific status.** The repository contains machine-checked foundational theorems about **finite-dimensional** Jacobi matrices, unitary evolution, Krylov moments and variance, complex Gram identities, and the derivative of the finite-dimensional Jacobi propagator. **The main finite-depth local-defect hierarchy from the preprint has not yet been formalized in Lean.** Passing GitHub Actions checks establishes that Lean accepted the encoded statements and proofs, not that all the preprint's claims are formalized, original, or independently peer reviewed.

**Branch status:** The verified P72.3a.3 and P73.1 developments currently reside on `p72-3a-proof-test`. They have not yet been merged into `main`. The corresponding full verification record is GitHub Actions #101.

---

## 1. Latest verified checkpoint and reproducibility

### 1.1. Current verified checkpoint: P73.1

| Item | Verified record |
| --- | --- |
| Milestone | **P73.1** |
| Verification | [GitHub Actions #101, `verify`: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527474) |
| Exact source commit | [`a291e152b9ea3feed8f7c0608ae8eaca33700298`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/a291e152b9ea3feed8f7c0608ae8eaca33700298) |
| Date | 18 October 2026 |
| Verified branch | `p72-3a-proof-test` |
| Lean toolchain | `leanprover/lean4:v4.24.0` |
| mathlib configuration | `v4.24.0` in `lakefile.toml` |
| Files checked | All **eleven** `.lean` files explicitly compiled by `.github/workflows/lean.yml`, including `KrylovGap.lean` and `P73_RealTime.lean` |
| Isolated derivative verification | [P72.3a Minimal Derivative Verification #7: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527416) |
| P73.1 axiom audit | `[propext, Classical.choice, Quot.sound]` |
| `sorryAx` in the P73.1 theorem | Not present in the recorded `#print axioms` output |
| Default branch | Not yet updated to this checkpoint |

The exact declaration verified in P73.1 is:

```lean
Lanzarini.p73_jacobiPropagator_hasDerivAt
```

This theorem establishes the real-time derivative of the propagator

\[
U(t)=\exp(-itH)
\]

in the finite-dimensional Jacobi setting:

\[
\frac{d}{dt}U(t)=(-iH)U(t).
\]

The theorem follows from the already verified complex-time matrix exponential derivative and the restriction of complex differentiability to real time.

The statement does **not** assume the desired derivative as a hypothesis.

It is a result about the **propagator**, not yet the complete Schrödinger time-derivative theorem for the evolving state.

The GitHub Actions #101 log records:

```text
'Lanzarini.p73_jacobiPropagator_hasDerivAt'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are standard foundational axioms in the Lean/mathlib environment. No additional project-specific axiom or `sorryAx` is reported for this declaration.

The successful workflow also compiles the preceding theorem files.

The verification does not establish originality, independent peer review, or equivalence between all formalized statements and the complete research preprint.

### 1.2. Historical verified checkpoint: P71

The original P71 verification record is preserved.

| Item | Verified record |
| --- | --- |
| Milestone | **P71** |
| Verification | [GitHub Actions #84, `verify`: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) |
| Exact source commit | [`85f799e6defae7f9106a10c4fd9f780d27cf2b4f`](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/85f799e6defae7f9106a10c4fd9f780d27cf2b4f) |
| Date | 17 October 2026 |
| Lean toolchain | `leanprover/lean4:v4.24.0` |
| mathlib configuration | `v4.24.0` in `lakefile.toml` |
| mathlib revision in the #84 CI log | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |
| Files checked | All **ten** `.lean` files explicitly compiled by `.github/workflows/lean.yml`, including `KrylovGap.lean` |

The source files compiled at P71 were inspected for `sorry`, `admit`, and locally declared `axiom` statements; none were found.

At the P71 checkpoint, the outputs of `#print axioms` for the central declarations had not yet been recorded as a separate verification checkpoint.

The subsequent P72.3a.3 and P73.1 checks record the axiomatic dependencies of their respective declarations, but do not constitute an exhaustive audit of every historical theorem.

### 1.3. Dependency reproducibility

**Dependency-lock caveat:** The repository currently does **not** contain a committed `lake-manifest.json`.

The CI workflow executes `lake update`. The mathlib revision reported for the historical P71 run comes from its actual CI log.

A reviewed, committed dependency manifest remains a reproducibility task.

The successful source commits, workflow definitions and execution logs provide reproducible verification records, but a dependency lockfile would improve environmental traceability.

No dependency revision beyond those explicitly established by the available records is asserted here.

---

## 2. Mathematical framework and conventions

For a finite dimension `n`, the code defines a real symmetric tridiagonal Jacobi matrix using `a b : Fin n → ℝ`:

$$
H_{ii}=a_i,\qquad H_{i,i+1}=H_{i+1,i}=b_i.
$$

All other matrix entries vanish. The coupling formula is understood only for valid adjacent indices.

The foundational Lean definitions allow **arbitrary real** diagonal and off-diagonal coefficients. The positivity of physical couplings is **not** built into those definitions. Conditions such as positive interior couplings belong to specific results in the research preprint and must be explicitly included when formalizing those results.

**Basis-identification caveat:** The operator named `krylovNumberOperator` acts on the chosen coordinate basis `Fin n`. The repository does not yet formalize a general Lanczos algorithm or prove that this coordinate basis is the Krylov basis generated by an arbitrary Hamiltonian and initial state. Identifying the Jacobi-chain basis with a genuine Lanczos/Krylov basis requires the appropriate construction and hypotheses.

Lean uses zero-based `Fin n` indices. The off-diagonal input `b i` couples site `i` to site `i+1`, and its last entry is unused. In the preprint the first physical coupling is called $b_1$; its correspondence with the Lean input is:

$$
b_j^{\mathrm{preprint}}=b_{j-1}^{\mathrm{Lean}},\qquad 1\le j\le n-1.
$$

For the complex representation of the finite Jacobi Hamiltonian, the code uses:

$$
U(t)=\exp(-itH),\qquad \psi(t)=U(t)\psi_0.
$$

The finite-dimensional propagator is proved unitary. The formalization establishes preservation of the norm, inner product and orthogonality.

P73.1 additionally establishes the real-time derivative of the propagator, with the correct sign convention:

$$
U'(t)=(-iH)U(t).
$$

These statements do **not** depend on a proof of any infinite-dimensional operator-domain result.

**Infinite-dimensional scope:** This repository does not yet define an unbounded Jacobi operator on $\ell^2(\mathbb N_0)$ or prove its self-adjointness. Defining $e^{-itH}$ and ensuring that $\psi(t)$ belongs to the domain of the number operator $N$ can require additional hypotheses and domain arguments. None of those extensions should be inferred from the finite-dimensional Lean results.

---

## 3. Verified theorems through P73.1

The milestone labels describe the development history; **they do not measure percentage completion of the research theorem**.

| Checkpoints | Actual formalized content | Source file(s) |
| --- | --- | --- |
| **P51–P55** | Hermitian finite Jacobi Hamiltonian, anti-Hermitian evolution generator, unitary propagator, preservation of norms, inner products and orthogonality | `JacobiReal.lean`, `JacobiEvolution.lean`, `MatrixExpProbe.lean` |
| **P56–P59** | Krylov number operator, complexity, second moment, algebraic variance, and preservation of normalization | `KrylovNumber.lean` |
| **P60–P61** | Centered-variance identity, variance nonnegativity under normalization and zero-variance equivalences | `KrylovNumber.lean` |
| **P62–P64** | Support constraints under zero variance; a normalized zero-variance state has exactly one occupied Krylov level | `KrylovNumber.lean` |
| **P65–P69** | Complex Gram coordinates and finite Gram sum; Lagrange identity for finite complex vectors | `KrylovGram.lean`, `KrylovLagrange.lean` |
| **P70** | Exact real-part Gram-gap identity and its nonnegativity | `KrylovGap.lean` |
| **P71** | Norm of the centered state equals normalized Krylov variance, including along the time evolution; specialization of the Gram-gap identity with an arbitrary auxiliary vector | `KrylovGap.lean` |
| **P72.1** | Exact algebraic increment of Krylov complexity | `KrylovGap.lean` |
| **P72.2** | Derivative of Krylov complexity for a curve with explicitly assumed componentwise differentiability | `KrylovGap.lean` |
| **P72.3a.1** | Factorization of the existing Jacobi evolution generator as a real-time scalar multiplied by the constant generator $-iH$ | `KrylovGap.lean` |
| **P72.3a.2** | Expression of the real-time Jacobi propagator as the restriction of the complex-time matrix exponential | `KrylovGap.lean` |
| **P72.3a.3** | Complex-time derivative of the finite-dimensional Jacobi matrix exponential | `KrylovGap.lean` |
| **P73.1** | Real-time derivative of the finite-dimensional Jacobi propagator | `P73_RealTime.lean` |

The P72.3a.3 and P73.1 results have passed the full verification workflow on the test branch. They have not yet been merged into `main`.

The actual Lean declaration names include:

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

### 3.1. Krylov moments and the normalization hypothesis

For a finite vector $\psi\in\mathbb C^n$, define

$$
K(\psi)=\sum_{j=0}^{n-1}j|\psi_j|^2,\qquad
K_2(\psi)=\sum_{j=0}^{n-1}j^2|\psi_j|^2,
$$

and the algebraic expression

$$
V(\psi)=K_2(\psi)-K(\psi)^2.
$$

The code **defines** this expression for arbitrary finite vectors. The centered-variance formula and the interpretation of $V$ as the variance of a probability distribution require the explicit hypothesis $\|\psi\|^2=1$. Under that hypothesis, Lean proves:

$$
V(\psi)=\sum_{j=0}^{n-1}(j-K(\psi))^2|\psi_j|^2\ge0.
$$

If a normalized state's variance is zero, Lean also proves that precisely one index has positive squared amplitude. This is a property of the finite Krylov-level distribution; it is **not** the central local-defect hierarchy.

### 3.2. Complex Gram/Lagrange identity (P69)

For arbitrary finite vectors $u,v\in\mathbb C^n$, define

$$
G(u,v)=\sum_{i=0}^{n-1}\sum_{j=i+1}^{n-1}|u_i v_j-u_j v_i|^2.
$$

The following **classical identity** is formalized:

$$
G(u,v)=\|u\|^2\|v\|^2-|\langle u,v\rangle|^2\ge0.
$$

Each unordered pair is counted once, and the determinant coordinate $u_iv_j-u_jv_i$ contains no conjugation. P69 does not assert that this classical identity is new.

### 3.3. Real-part Gram gap (P70)

For arbitrary $u,v\in\mathbb C^n$, the code proves

$$
\|u\|^2\|v\|^2-\bigl(\mathrm{Re}\langle u,v\rangle\bigr)^2
=G(u,v)+\bigl(\mathrm{Im}\langle u,v\rangle\bigr)^2\ge0.
$$

This is an algebraic identity, not yet a quantum speed-limit theorem.

### 3.4. Centered-state/variance bridge (P71)

Let $N$ denote the diagonal matrix with entries $0,1,\ldots,n-1$, and set

$$
u=(N-K(\psi))\psi.
$$

For a **normalized** state, Lean proves

$$
\|u\|^2=V(\psi).
$$

The same identity is proved for the state $\psi(t)=U(t)\psi_0$ when the initial state is normalized. The P70 gap identity is also applied to that centered evolved state and **any auxiliary complex vector** $v$.

P71 alone does not identify this auxiliary vector with the Schrödinger time derivative. That identification requires an additional dynamical theorem.

### 3.5. Krylov complexity differentiation (P72.1–P72.2)

P72.1 establishes an exact algebraic increment formula for the finite-dimensional Krylov complexity.

P72.2 proves a derivative formula for a general time-dependent complex state when the real and imaginary parts of each coordinate are differentiable with the explicitly supplied coordinate derivatives.

Schematically, for a differentiable curve $\psi(t)$,

$$
\frac{d}{dt}K(\psi(t))
=
2\sum_{j=0}^{n-1}
j\,\mathrm{Re}
\left(
\overline{\psi_j(t)}\,\dot\psi_j(t)
\right).
$$

The Lean theorem includes explicit coordinatewise differentiability hypotheses.

**Scope limitation:** P72.2 does not independently prove that the physical Jacobi-evolved state satisfies those hypotheses. This requires the later state-evolution derivative theorem.

### 3.6. Complex-time matrix exponential derivative (P72.3a)

P72.3a.1 establishes the factorization of the existing Jacobi evolution generator.

P72.3a.2 connects the real-time propagator to the corresponding complex-time matrix exponential.

P72.3a.3 proves the complex derivative

$$
\frac{d}{dz}\exp(zA)=A\exp(zA),
\qquad A=-iH,
$$

for the finite-dimensional Jacobi matrix.

The result uses the matrix operator-norm structure required by mathlib and a verified matrix-exponential derivative theorem.

**Verified record:**

- [GitHub Actions #98: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849)
- Source commit: `702256d89e7623eafcabd188911166eaddb08c7a`
- `#print axioms` result: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx` in the recorded axiom dependency output.

The result is a standard analytical ingredient used by the formal development. It is not presented as a new discovery.

### 3.7. Real-time Jacobi propagator derivative (P73.1)

P73.1 converts the established complex-time derivative into a real-time derivative.

The verified statement is

$$
\frac{d}{dt}U(t)=(-iH)U(t).
$$

Here $H$ is the finite-dimensional complex representation of the real Jacobi matrix and

$$
U(t)=\exp(-itH).
$$

The proof derives the real-time result from the complex-time derivative using the real-to-complex differentiability machinery available in mathlib.

No normalization assumption is needed for this matrix-valued derivative statement.

No physical time-evolution derivative is assumed as a hypothesis.

**Verified record:**

- [GitHub Actions #101: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527474)
- Commit: `a291e152b9ea3feed8f7c0608ae8eaca33700298`
- Source: `P73_RealTime.lean`
- `#print axioms` result: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx` in the recorded axiom dependency output.

**Important distinction:** P73.1 proves the derivative of the matrix propagator. The theorem asserting

$$
\frac{d}{dt}\psi(t)=-iH\psi(t)
$$

for $\psi(t)=U(t)\psi_0$ has **not yet been formalized in this repository**.

That is the next logical proof obligation.

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
| `KrylovGap.lean` | P70–P72.3a: Gram gap, variance bridge, complexity differentiation and complex-time derivative |
| `P72_3a_Minimal.lean` | Isolated verification of the complex-time matrix exponential derivative |
| `P73_RealTime.lean` | P73.1: real-time Jacobi propagator derivative |
| `lean-toolchain` | Lean toolchain version |
| `lakefile.toml` | mathlib dependency specification |
| `.github/workflows/lean.yml` | Explicit compilation sequence used by the main GitHub Actions verification |
| `.github/workflows/p72-minimal.yml` | Separate verification workflow for the isolated P72.3a proof |

The additional P72 and P73 source files and the dedicated verification workflow currently belong to the verified test branch.

---

## 5. Verification environment and integrity policy

The repository uses Lean 4, mathlib, Lake and GitHub Actions.

The historical P71 workflow #84 compiled ten Lean files in dependency order and verified the foundational theorems through P71.

The subsequent full verification workflow #101 compiled eleven Lean files in dependency order, including `KrylovGap.lean` and `P73_RealTime.lean`.

The separate P72.3a verification workflow also completed successfully.

**Latest completed verification:**

[Lean 4 Verification #101: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39144527474)

The recorded source commit is:

```text
a291e152b9ea3feed8f7c0608ae8eaca33700298
```

The verification applies to that exact source state on the test branch.

To audit future proof repairs:

1. **Freeze the theorem statement first.** When a proof is corrected, compare the statement and hypotheses against the earlier commit; changing them means changing the theorem.
2. Check **all definitions that the statement depends on**, not only the displayed theorem text.
3. Confirm that the new file is included in the actual CI commands. A green workflow does not certify files it omitted.
4. Retain commit history and failed-run evidence where possible; old failures do not invalidate a later correct proof.
5. Independently check the correspondence between the encoded Lean statement and the research preprint, including normalization, coupling indices and boundaries.
6. Audit axiomatic dependencies for selected declarations using `#print axioms`; report the actual output, not an assumed list.
7. Do not interpret milestone counts as a measure of mathematical completion.
8. Do not introduce `sorry`, `admit`, artificial axioms or circular hypotheses to force verification.
9. Preserve the mathematical meaning of each declaration while repairing proofs.
10. Compile every new theorem explicitly in GitHub Actions before assigning it a verified checkpoint.
11. Keep experimental developments separate from the official branch until the complete verification passes.
12. Do not claim formalization of the preprint's main theorem until its precise mathematical statement and proof have been encoded and checked.

### 5.1. Axiom audit

The following declarations have explicit axiom reports in the successful #101 workflow:

```lean
#print axioms Lanzarini.krylovComplexity_increment
#print axioms Lanzarini.krylovComplexity_hasDerivAt_components
#print axioms Lanzarini.jacobiEvolutionGenerator_time_factor
#print axioms Lanzarini.jacobiPropagator_complex_time_eq
#print axioms Lanzarini.jacobiComplexTimeExp_hasDerivAt
#print axioms Lanzarini.p73_jacobiPropagator_hasDerivAt
```

The recorded output for each lists the standard Lean axioms:

```text
[propext, Classical.choice, Quot.sound]
```

This confirms the reported axiom dependencies of these specific declarations, not those of every theorem in the repository.

A further audit may inspect:

```lean
#print axioms Lanzarini.krylovLagrange_finite
#print axioms Lanzarini.krylovGram_realPart_gap
#print axioms Lanzarini.krylovCenteredState_normSq
#print axioms Lanzarini.krylovCenteredState_gap_at
```

The dedicated record of these four axiom probes is still **pending**. No unobserved result is claimed.

### 5.2. Branch and integration policy

The latest verified P73.1 source state is on:

```text
p72-3a-proof-test
```

The default branch is:

```text
main
```

The test branch has passed the full workflow but has not yet been merged into `main`.

Before integration:

- Update this README on the test branch.
- Confirm that the complete workflow remains successful.
- Compare the proposed source changes with `main`.
- Review the Pull Request.
- Merge the verified development without discarding the historical records.
- Verify the resulting `main` branch independently.

A successful test-branch workflow is not automatically a successful default-branch workflow.

---

## 6. Scientific target and unverified steps

The preprint studies the loss of saturation of a Krylov dispersion speed limit for a real Jacobi evolution **initialized at the first basis state** $e_0$.

In the **preprint's one-based coupling convention**, define $c_0=0$, $c_j=b_j^2$, and

$$
\Omega_r=c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
$$

Where the denominator is nonzero, the preprint's dimensionless saturation deficit is

$$
D(t)=1-\frac{\dot K(t)^2}{4b_1^2V(t)}.
$$

The normalized deficit is studied for sufficiently small $t\ne0$ (with its short-time extension at $0$). Its nonnegativity depends on establishing the appropriate dispersion speed-limit inequality under the correct dynamical assumptions.

**Mixed finite-depth local-defect formula stated in the preprint, not yet proved in Lean.** For $r\ge0$, write $m=r+3$ and take a finite real Jacobi chain with dimension $d\ge m+1$, positive interior couplings and the stated initial state $e_0$. Under the prefix conditions

$$
a_0=a_1=\cdots=a_{m-1},\qquad
\Omega_0=\cdots=\Omega_{r-1}=0,
$$

where the defect condition is empty for $r=0$, the preprint gives the leading mixed form

$$
D(t)=\frac{\displaystyle\prod_{j=2}^{m-1}c_j}{[(m+1)!]^2}
\bigl[4\Omega_r^2+c_m(a_m-a_0)^2\bigr]
\,t^{2m}+O_H(t^{2m+2}).
$$

The **diagonal defect** $a_m-a_0$ is part of this general finite-dimensional research claim. The simplified expression involving only $\Omega_r^2$ is not an unconditional statement of the mixed real-Jacobi result. In a terminal-boundary setting, the relevant boundary and positivity assumptions must be checked separately.

**The full local-defect hierarchy, its remainder estimates, the short-time rigidity statements and any infinite-dimensional extension are not formalized in the current Lean repository.**

The preprint states research results; CI verifies only the theorems that appear in the code. Neither AI review nor Lean compilation by itself establishes novelty or independent peer review.

### 6.1. Completed foundational derivative steps

The following steps are verified:

- Exact increment of finite-dimensional Krylov complexity (P72.1).
- Derivative formula for a componentwise differentiable complex-state curve, under explicit differentiability hypotheses (P72.2).
- Factorization of the Jacobi evolution generator (P72.3a.1).
- Complex-time representation of the propagator (P72.3a.2).
- Complex-time matrix exponential derivative (P72.3a.3).
- Real-time propagator derivative (P73.1).

These are genuine formalized results but do not yet prove the preprint's central local-defect hierarchy.

### 6.2. Next formal proof obligations

The next proof obligations are:

1. **P73.2: Schrödinger state derivative.** Derive
   $$
   \frac{d}{dt}\psi(t)=-iH\psi(t)
   $$
   from the verified propagator derivative and the existing definition of `jacobiState`.

2. **Physical Krylov complexity derivative.** Apply the componentwise differentiation theorem to the actual Jacobi-evolved state, with the correct normalized-state hypotheses.

3. **Energy and velocity norm.** Establish the conserved quantity required by the dispersion speed limit under the initial-state assumptions of the preprint.

4. **Finite-dimensional speed-limit inequality.** Prove the required bound using the already formalized Gram identity, centered variance and physical time derivative.

5. **Deficit definition and domain.** Define the normalized deficit with an explicit proof that its denominator is nonzero where used.

6. **Finite-depth local defects.** Formalize the diagonal and off-diagonal obstructions, including their index conventions, finite-chain boundaries and leading Taylor coefficients.

7. **Main finite-chain result.** Prove the precise counterpart of Theorem 8.1 in the research preprint.

8. **Local rigidity.** Formalize the finite-depth rigidity criterion of Theorem 9.1, explicitly preserving the hypotheses on positive couplings and terminal edges.

9. **Semi-infinite extension.** Treat unbounded operator domains, essential self-adjointness and weighted estimates separately from the finite-dimensional results.

Except for the explicitly completed foundational steps, these are **research targets, not verified Lean milestones**.

The next milestone must not assume the Schrödinger equation or the desired speed-limit inequality as a hypothesis merely to make a proof compile.

---

## 7. Scientific status and limitations

The current project **does not claim**:

- A completed Lean proof of the main local-defect hierarchy theorem.
- A completed Lean proof of the Schrödinger equation for the evolved state.
- A completed Lean proof of the physical Krylov dispersion speed limit.
- A new universal quantum speed limit.
- Independent peer-review certification or established worldwide mathematical priority.
- Formal validity for arbitrary unbounded Jacobi operators.
- That the number of PASS milestones measures percentage completion of the scientific objective.

Lean checks proofs relative to the **precise encoded statements**, accepted foundations, definitions and assumptions.

Scientific evaluation also requires the mathematical encoding to match the intended theorem and its physical setting.

This correspondence remains an explicit, ongoing audit task.

The repository's finite-dimensional formalization should not be interpreted as an automatic verification of the semi-infinite statements in the preprint.

The mathematical novelty of any claimed local-defect hierarchy remains subject to independent analysis of the literature and specialist review.

---

## 8. Research preprint

**Title:** Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics  
**Author:** Valentino Lanzarini  
**DOI:** https://doi.org/10.5281/zenodo.23163367

The published preprint and this machine-checked foundational development are related but distinct scientific artifacts.

The formalization is still incomplete relative to the full preprint.

The central research target is the finite-depth hierarchy describing the first nonzero obstruction to saturation of the Krylov dispersion bound for general real Jacobi dynamics.

The proposed hierarchy combines two distinct mechanisms:

- Off-diagonal third-difference defects, measured by $\Omega_r$.
- Diagonal inhomogeneity, measured by $a_{r+3}-a_0$.

The preprint's main finite-chain theorem and rigidity criterion must be formalized with their precise hypotheses before a machine-verified version of those research claims can be asserted.

---

## 9. Copyright and permissions

Copyright © 2026 Valentino Lanzarini.

**All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place original materials in the public domain.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas or theorems.

Third-party dependencies remain subject to their respective licenses.

---

## 10. AI-assisted research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not presented as independent peer review or scientific certification.

Mathematical claims must be evaluated through explicit proofs, reproducible checks and independent scientific scrutiny.

The author remains responsible for reviewing the research claims, the published documentation and the scope of the conclusions.

Automated theorem verification provides evidence of the validity of the encoded formal statements relative to Lean's foundations, but does not independently certify scientific originality or the accuracy of every translation from informal mathematics.

---

## 11. Author

**Valentino Lanzarini**

Independent Mathematical Researcher

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Research:**  
https://doi.org/10.5281/zenodo.23163367

**GitHub:**  
[Repository on GitHub](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/main)

---

Copyright © 2026 Valentino Lanzarini. All rights reserved.
