Lanzarini Krylov–Jacobi

Lean 4 formalization of finite-dimensional Jacobi dynamics and Krylov observables

Author: Valentino Lanzarini, Independent Mathematical Researcher
Project status: Research in progress
Latest verified formalization checkpoint: P74.2 (main, GitHub Actions #117: SUCCESS)
Environment: Lean 4 "v4.24.0" and mathlib "v4.24.0"
Research preprint: https://doi.org/10.5281/zenodo.23163367
Repository: "Open the GitHub repository" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/main)
Copyright: © 2026 Valentino Lanzarini. All rights reserved.

«Scientific status. This repository contains machine-checked foundational theorems concerning finite-dimensional Jacobi matrices, unitary evolution, Krylov moments and variance, complex Gram identities, matrix-exponential differentiation, real-time Schrödinger evolution, componentwise state derivatives, and the physical derivative of finite-dimensional Krylov complexity.

The principal finite-depth local-defect hierarchy of the research preprint has not yet been formalized in Lean.

Successful GitHub Actions verification establishes that Lean accepted the encoded declarations and their proofs within the configured environment. It does not establish scientific originality, independent peer review, or verification of every claim in the preprint.»

Official integration history:

- P72.3a.3 and P73.1 were integrated into "main" through "Pull Request #1" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/1) on 18 October 2026.
- P73.2 was integrated through "Pull Request #2" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/2) on 19 October 2026.
- P74.1 and P74.2 were integrated through "Pull Request #3" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3) on 20 October 2026.

The latest reported post-merge verification is "GitHub Actions #117: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938).

---

1. Latest verified checkpoint and reproducibility

1.1. Current checkpoint: P74.2

Item| Verification record
Milestone| P74.2
Branch| "main"
Date| 20 October 2026
Pull Request| "PR #3: merged" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3)
Post-merge verification| "GitHub Actions #117: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938)
Development verification| "GitHub Actions #116: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39374579575)
Verified merge commit| "3cc284d942bb73b977315fe5096033ce9ec37d42"
Lean toolchain| "leanprover/lean4:v4.24.0"
mathlib configuration| "v4.24.0"
New source files| "P74_1_Components.lean", "P74_2_KrylovDerivative.lean"
Recorded axiom dependencies| "[propext, Classical.choice, Quot.sound]"
"sorryAx" in the recorded P74 theorem dependencies| Not present

The latest checkpoint establishes the physical derivative of finite-dimensional Krylov complexity along Jacobi evolution.

For

$$
\psi(t)=e^{-itH}\psi_0,
$$

define

$$
K(t)=\sum_{j=0}^{n-1}j|\psi_j(t)|^2.
$$

The verified derivative identity is

$$
\boxed{
\frac{dK(t)}{dt}

2\sum_{j=0}^{n-1}
j,\operatorname{Re}
\left(
\overline{\psi_j(t)}
(-iH\psi(t))_j
\right).
}
$$

This result is derived from the previously formalized componentwise differentiation theorem and the physical Jacobi-state derivative.

The desired derivative is not assumed as a hypothesis.

No normalization assumption is required for this particular identity.

P74.2 does not yet establish the centered derivative identity or the Krylov dispersion speed limit.

1.2. Historical verification checkpoints

Milestone| Verification| Commit or record
P71| "GitHub Actions #84: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215)| "85f799e6defae7f9106a10c4fd9f780d27cf2b4f"
P72.3a.3| "GitHub Actions #98: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849)| "702256d89e7623eafcabd188911166eaddb08c7a"
P73.1| "GitHub Actions #103: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923)| "677985738a8e82aca8327ad3cc241ef8bc5e695d"
P73.2| "GitHub Actions #109: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293)| "4e288ae3ce35e3f99c5630dd3fb436b30c3a36c9"
P74.2| "GitHub Actions #117: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938)| "3cc284d942bb73b977315fe5096033ce9ec37d42"

These records document successive verification checkpoints. They do not represent percentages of completion of the central research theorem.

1.3. Dependency reproducibility

The previously documented repository state did not include a committed "lake-manifest.json".

The CI configuration used "lake update".

The historical P71 workflow reported mathlib revision:

"f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

The dependency-lock status should be rechecked against the current P74.2 commit.

A reviewed and committed dependency manifest remains a recommended reproducibility improvement if it is still absent.

---

2. Mathematical framework and conventions

For finite dimension "n", the repository defines a real symmetric tridiagonal Jacobi matrix using

a b : Fin n → ℝ

with entries

$$
H_{ii}=a_i,
\qquad
H_{i,i+1}=H_{i+1,i}=b_i.
$$

All other entries vanish.

The foundational definitions allow arbitrary real diagonal and off-diagonal coefficients.

Positive interior couplings are not imposed globally by the definitions. They must be included explicitly in theorems requiring irreducible Jacobi chains.

2.1. Index conventions

Lean uses zero-based indices.

The input "b i" couples sites "i" and "i+1", where this adjacent pair exists. The final entry of the "Fin n" coupling input is unused.

The preprint uses one-based physical coupling indices:

$$
b_j^{\mathrm{preprint}}

b_{j-1}^{\mathrm{Lean}},
\qquad 1\le j\le n-1.
$$

These conventions must be preserved when formalizing finite-depth defects and boundary terms.

2.2. Krylov basis identification

The formalized number operator acts on the selected coordinate basis.

The repository does not yet formalize a general Lanczos algorithm or establish that this basis is the Krylov basis generated by an arbitrary Hamiltonian and initial state.

The physical interpretation therefore applies to the Jacobi-chain setting under the appropriate basis-identification hypotheses.

2.3. Finite-dimensional evolution

The complex Jacobi Hamiltonian generates

$$
U(t)=\exp(-itH),
$$

and the evolved state is

$$
\psi(t)=U(t)\psi_0.
$$

The finite-dimensional propagator is formally proved unitary.

Consequently, the formalization includes preservation of norms, inner products and orthogonality.

The real-time propagator derivative is

$$
U'(t)=(-iH)U(t).
$$

The evolved-state derivative is

$$
\psi'(t)=(-iH)\psi(t).
$$

Both are established in finite dimensions without requiring normalization for these derivative statements.

2.4. Infinite-dimensional scope

The repository does not yet establish a general self-adjoint unbounded Jacobi operator on

$$
\ell^2(\mathbb N_0).
$$

Infinite-dimensional extensions require separate treatment of operator domains, self-adjointness, differentiability, weighted estimates and the domain of the Krylov number operator.

No infinite-dimensional result is inferred from the finite-dimensional verification.

---

3. Verified theorem development through P74.2

Checkpoints| Formalized content| Source files
P51–P55| Hermitian finite Jacobi Hamiltonian, anti-Hermitian generator, unitary propagator, norm and inner-product preservation| "JacobiReal.lean", "JacobiEvolution.lean", "MatrixExpProbe.lean"
P56–P59| Krylov number operator, complexity, second moment, algebraic variance and normalization preservation| "KrylovNumber.lean"
P60–P61| Centered variance, normalized variance nonnegativity and zero-variance equivalences| "KrylovNumber.lean"
P62–P64| Zero-variance support constraints and unique occupied Krylov level| "KrylovNumber.lean"
P65–P69| Complex Gram coordinates, Gram sum and finite-dimensional Lagrange identity| "KrylovGram.lean", "KrylovLagrange.lean"
P70| Exact real-part Gram-gap identity and nonnegativity| "KrylovGap.lean"
P71| Centered-state norm/variance identity and time-evolved specialization| "KrylovGap.lean"
P72.1| Exact algebraic increment of Krylov complexity| "KrylovGap.lean"
P72.2| Conditional componentwise Krylov differentiation| "KrylovGap.lean"
P72.3a.1–P72.3a.3| Generator factorization, complex-time propagator representation and matrix-exponential derivative| "KrylovGap.lean"
P73.1| Real-time Jacobi propagator derivative| "P73_RealTime.lean"
P73.2| Real-time evolved Jacobi-state derivative| "P73_2_State.lean"
P74.1| Componentwise complex, real and imaginary state derivatives| "P74_1_Components.lean"
P74.2| Physical Krylov complexity derivative along Jacobi evolution| "P74_2_KrylovDerivative.lean"

3.1. Krylov moments and variance

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

The algebraic expression is defined for arbitrary finite vectors.

For normalized states,

$$
|\psi|^2=1,
$$

the formalization establishes

$$
\boxed{
V(\psi)

\sum_{j=0}^{n-1}
(j-K(\psi))^2|\psi_j|^2
\ge0.
}
$$

For a normalized zero-variance state, precisely one Krylov level has positive squared amplitude.

This is a finite-distribution property and does not establish the local-defect hierarchy.

3.2. Complex Gram and Lagrange identity: P69

For arbitrary

$$
u,v\in\mathbb C^n,
$$

define

$$
G(u,v)

\sum_{0\le i<j<n}
|u_iv_j-u_jv_i|^2.
$$

The formalization establishes the classical identity

$$
\boxed{
G(u,v)

|u|^2|v|^2

|\langle u,v\rangle|^2
\ge0.
}
$$

Each unordered pair is counted once.

This identity is classical and is not presented as a new mathematical discovery.

3.3. Real-part Gram gap: P70

For arbitrary finite complex vectors,

$$
\boxed{
|u|^2|v|^2

\bigl(\operatorname{Re}\langle u,v\rangle\bigr)^2

G(u,v)
+
\bigl(\operatorname{Im}\langle u,v\rangle\bigr)^2
\ge0.
}
$$

This is an exact algebraic identity.

Its later specialization to physical Krylov evolution requires additional dynamical arguments.

3.4. Centered-state variance bridge: P71

Let

$$
N=\operatorname{diag}(0,1,\ldots,n-1)
$$

and define

$$
u=(N-K(\psi))\psi.
$$

For normalized states, Lean proves

$$
\boxed{
|u|^2=V(\psi).
}
$$

The corresponding identity is established along unitary Jacobi evolution when the initial state is normalized.

The real-part Gram gap is also specialized to the centered evolved state and an arbitrary auxiliary vector.

This provides a formal algebraic foundation for the future speed-limit derivation.

3.5. Krylov complexity differentiation: P72.1–P72.2

P72.1 establishes an exact algebraic increment formula.

P72.2 establishes a conditional derivative formula for a complex-state curve with explicitly supplied coordinatewise differentiability hypotheses.

For a differentiable curve,

$$
\frac{dK}{dt}

2\sum_{j=0}^{n-1}
j\operatorname{Re}
\left(
\overline{\psi_j(t)}\dot\psi_j(t)
\right).
$$

At P72.2 this was a conditional statement.

P74.2 subsequently completes its specialization to the actual finite-dimensional Jacobi evolution.

3.6. Complex-time matrix exponential: P72.3a

P72.3a.1 establishes the factorization of the evolution generator.

P72.3a.2 connects the real-time propagator with the complex-time exponential.

P72.3a.3 establishes

$$
\boxed{
\frac{d}{dz}\exp(zA)

A\exp(zA),
\qquad A=-iH.
}
$$

The proof uses the relevant matrix operator-norm and exponential differentiation machinery in mathlib.

Historical verification:

- GitHub Actions #98: SUCCESS.
- Source commit: "702256d89e7623eafcabd188911166eaddb08c7a".
- Recorded axioms: "[propext, Classical.choice, Quot.sound]".
- No "sorryAx" in the recorded dependencies.

This is a standard analytical ingredient, not a claim of mathematical novelty.

3.7. Real-time propagator derivative: P73.1

P73.1 establishes

$$
\boxed{
\frac{d}{dt}U(t)=(-iH)U(t).
}
$$

The proof derives the real-time identity from the complex-time matrix-exponential derivative.

Lean declaration:

Lanzarini.p73_jacobiPropagator_hasDerivAt

Verification:

- GitHub Actions #101: SUCCESS on the development branch.
- GitHub Actions #103: SUCCESS on "main".
- Pull Request #1: merged.
- Recorded axioms: "[propext, Classical.choice, Quot.sound]".

No normalization hypothesis or circular propagator-derivative hypothesis is required.

3.8. Real-time Schrödinger state derivative: P73.2

For

$$
\psi(t)=U(t)\psi_0,
$$

P73.2 establishes

$$
\boxed{
\frac{d}{dt}\psi(t)=(-iH)\psi(t).
}
$$

The proof uses the P73.1 propagator derivative and the continuous linear map applying a matrix to the fixed initial state.

The exact Lean theorem is:

theorem p73_jacobiState_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    HasDerivAt
      (fun s : ℝ => jacobiState n a b s psi)
      (((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi))
      t

Verification:

- GitHub Actions #108: SUCCESS.
- GitHub Actions #109: SUCCESS on "main".
- Pull Request #2: merged.
- Verified merge commit: "4e288ae3ce35e3f99c5630dd3fb436b30c3a36c9".
- Recorded axioms: "[propext, Classical.choice, Quot.sound]".

The result establishes a standard finite-dimensional Schrödinger evolution identity in the repository's formal framework.

It does not constitute a new physical law.

3.9. Jacobi-state component derivatives: P74.1

Source: "P74_1_Components.lean"

The following declarations are reported as verified:

Lanzarini.p74_jacobiState_component_hasDerivAt
Lanzarini.p74_jacobiState_parts_hasDerivAt

For the evolved state

$$
\psi(t)=e^{-itH}\psi_0,
$$

the component derivative is

$$
\boxed{
\frac{d}{dt}\psi_j(t)

(-iH\psi(t))_j.
}
$$

The real and imaginary coordinate derivatives are also formally established.

P74.1 derives these statements from P73.2.

It does not assume the desired component derivatives.

This milestone connects the vector-valued Schrödinger derivative with the coordinatewise differentiability requirements of P72.2.

3.10. Physical Krylov complexity derivative: P74.2

Source: "P74_2_KrylovDerivative.lean"

Verified declaration:

Lanzarini.p74_krylovComplexityAt_hasDerivAt

Define

$$
K(t)=\sum_{j=0}^{n-1}j|\psi_j(t)|^2
$$

for the physical Jacobi evolution

$$
\psi(t)=e^{-itH}\psi_0.
$$

P74.2 establishes

$$
\boxed{
\dot K(t)

2\sum_{j=0}^{n-1}
j\operatorname{Re}
\left(
\overline{\psi_j(t)}
(-iH\psi(t))_j
\right).
}
$$

The proof combines:

1. P72.2, the conditional componentwise differentiation theorem.
2. P73.2, the physical evolved-state derivative.
3. P74.1, the coordinatewise complex, real and imaginary derivatives.

The physical derivative is derived rather than introduced as a hypothesis.

No state normalization assumption is required for this derivative identity.

Official verification:

- "PR #3: merged" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./pull/3).
- "Development workflow #116: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39374579575).
- "Post-merge workflow #117: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938).
- Merge commit: "3cc284d942bb73b977315fe5096033ce9ec37d42".

The recorded P74 theorem dependencies are

[propext, Classical.choice, Quot.sound]

No "sorryAx" appears in the reported dependencies of the three P74 declarations.

Scientific interpretation: P74.2 closes the foundational gap between conditional differentiation of Krylov complexity and the actual finite-dimensional Jacobi evolution.

It does not yet establish the centered derivative identity, the physical dispersion speed limit or the finite-depth local-defect hierarchy.

---

4. Repository structure

File| Purpose
"Main.lean"| Initial Lean verification check
"Jacobi2.lean"| Two-site integer Jacobi matrix and symmetry
"JacobiGeneral.lean"| Finite integer-valued Jacobi entries and symmetry
"JacobiReal.lean"| Finite real Jacobi Hamiltonian
"JacobiEvolution.lean"| Complex Hamiltonian and anti-Hermitian generator
"MatrixExpProbe.lean"| Propagator, unitarity and conservation theorems
"KrylovNumber.lean"| Number operator, moments, normalized variance and support constraints
"KrylovGram.lean"| Complex Gram coordinates and nonnegative Gram sum
"KrylovLagrange.lean"| Finite complex Lagrange identity
"KrylovGap.lean"| P70–P72.3a foundational identities and derivatives
"P72_3a_Minimal.lean"| Isolated complex-time matrix-exponential verification
"P73_RealTime.lean"| P73.1 propagator derivative
"P73_2_State.lean"| P73.2 evolved-state derivative
"P74_1_Components.lean"| P74.1 componentwise derivatives
"P74_2_KrylovDerivative.lean"| P74.2 physical Krylov complexity derivative
"lean-toolchain"| Lean toolchain specification
"lakefile.toml"| mathlib dependency configuration
".github/workflows/lean.yml"| Main GitHub Actions verification workflow
".github/workflows/p72-minimal.yml"| Isolated P72.3a verification workflow

The P74 post-merge verification record reports successful compilation of both new P74 source files.

The current workflow contents should be consulted when reproducing the exact compilation sequence.

---

5. Verification environment and scientific integrity

The project uses Lean 4, mathlib, Lake and GitHub Actions.

Historical verification milestones include:

- P71: GitHub Actions #84.
- P73.1: GitHub Actions #103.
- P73.2: GitHub Actions #109.
- P74.2: GitHub Actions #117.

The latest reported successful checkpoint is

"GitHub Actions #117 on main: SUCCESS" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938)

at commit

3cc284d942bb73b977315fe5096033ce9ec37d42

5.1. Proof integrity policy

Every future formalization milestone must follow these requirements:

1. Preserve the mathematical statement when repairing its proof.
2. Audit all relevant definitions and hypotheses.
3. Compile every new source file in the official verification workflow.
4. Record the exact verified commit.
5. Preserve historical verification and failure records.
6. Audit selected declarations using "#print axioms".
7. Never introduce "sorry", "admit", artificial axioms or circular hypotheses to force a successful compilation.
8. Check normalization and positivity assumptions explicitly.
9. Verify coupling-index and finite-boundary conventions.
10. Separate successful development-branch checks from post-merge verification.
11. Avoid interpreting milestone numbers as a percentage of research completion.
12. Distinguish formal verification from independent scientific review.

5.2. Axiom audit

The recorded P74 axiom probes concern:

#print axioms Lanzarini.p74_jacobiState_component_hasDerivAt
#print axioms Lanzarini.p74_jacobiState_parts_hasDerivAt
#print axioms Lanzarini.p74_krylovComplexityAt_hasDerivAt

Their reported dependencies are

[propext, Classical.choice, Quot.sound]

No "sorryAx" is reported for these declarations.

Earlier recorded probes include:

#print axioms Lanzarini.krylovComplexity_increment
#print axioms Lanzarini.krylovComplexity_hasDerivAt_components
#print axioms Lanzarini.jacobiEvolutionGenerator_time_factor
#print axioms Lanzarini.jacobiPropagator_complex_time_eq
#print axioms Lanzarini.jacobiComplexTimeExp_hasDerivAt
#print axioms Lanzarini.p73_jacobiPropagator_hasDerivAt
#print axioms Lanzarini.p73_jacobiState_hasDerivAt

The earlier recorded outputs also list

[propext, Classical.choice, Quot.sound]

These reports apply to the specified declarations.

They do not constitute an exhaustive axiom audit of every historical theorem.

Additional audits remain appropriate for:

#print axioms Lanzarini.krylovLagrange_finite
#print axioms Lanzarini.krylovGram_realPart_gap
#print axioms Lanzarini.krylovCenteredState_normSq
#print axioms Lanzarini.krylovCenteredState_gap_at

No result is asserted for an unexecuted audit.

5.3. Branch integration policy

The official checkpoint is integrated into

main

The next milestone must be developed separately, verified, reviewed and merged only after successful checks.

A green development-branch workflow does not itself certify the merged branch.

---

6. Scientific target: finite-depth local-defect hierarchy

The research preprint studies the loss of saturation of a Krylov dispersion speed limit for real Jacobi dynamics initialized at the first basis state

$$
\psi_0=e_0.
$$

In the preprint's one-based coupling convention, define

$$
c_0=0,\qquad c_j=b_j^2,
$$

and the third-difference defect

$$
\boxed{
\Omega_r

c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
}
$$

Where the denominator is nonzero, the preprint defines the dimensionless saturation deficit

$$
\boxed{
D(t)

1-
\frac{\dot K(t)^2}{4b_1^2V(t)}.
}
$$

The short-time analysis concerns sufficiently small nonzero times and the appropriate extension at zero.

Nonnegativity of this deficit requires the relevant physical dispersion speed-limit inequality and its assumptions.

6.1. Mixed finite-depth defect formula

The preprint states a mixed finite-depth local-defect expansion.

For

$$
r\ge0,\qquad m=r+3,
$$

consider a finite real Jacobi chain of dimension

$$
d\ge m+1
$$

with positive interior couplings and initial state $e_0$.

Assume the prefix conditions

$$
a_0=a_1=\cdots=a_{m-1}
$$

and

$$
\Omega_0=\cdots=\Omega_{r-1}=0,
$$

where the latter condition is empty for $r=0$.

The preprint states the leading expansion

$$
\boxed{
D(t)

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

This expression contains two mechanisms:

- Off-diagonal third-difference defects $\Omega_r$.
- Diagonal inhomogeneity $a_m-a_0$.

The diagonal term is part of the general mixed real-Jacobi claim.

The expression involving only $\Omega_r^2$ is not an unconditional version of the mixed formula.

Finite-chain boundaries, terminal couplings and positivity assumptions must be treated explicitly.

This expansion is a claim of the research preprint and has not yet been established as a Lean theorem in this repository.

The formula, its hypotheses, its remainder and its claimed novelty remain subject to independent mathematical audit.

6.2. Completed foundational formalization

The verified development now includes:

- Finite-dimensional unitary Jacobi evolution.
- Krylov moments and normalized variance.
- Complex Gram and Lagrange identities.
- Real-part Gram-gap identity.
- Centered-state variance identity.
- Conditional complexity differentiation.
- Complex-time matrix-exponential differentiation.
- Real-time propagator differentiation.
- Physical evolved-state differentiation.
- Componentwise physical state differentiation.
- Physical Krylov complexity differentiation, P74.2.

These ingredients are necessary for the planned formal development but do not by themselves prove the central finite-depth hierarchy.

---

7. Next research checkpoint: P75

7.1. Centered physical Krylov derivative

Status: NOT YET VERIFIED

The next milestone is the centered physical Krylov derivative identity.

For a normalized initial state,

$$
|\psi_0|^2=1,
$$

unitary evolution gives

$$
|\psi(t)|^2=1.
$$

Let

$$
N=\operatorname{diag}(0,1,\ldots,n-1)
$$

and

$$
K(t)=\langle\psi(t),N\psi(t)\rangle,
$$

using the appropriate inner-product convention.

Define

$$
u(t)=(N-K(t))\psi(t).
$$

The target is

$$
\boxed{
\dot K(t)

2\operatorname{Re}
\langle u(t),\dot\psi(t)\rangle.
}
$$

For the physical Jacobi evolution,

$$
\dot\psi(t)=(-iH)\psi(t).
$$

Consequently, the intended centered physical form is

$$
\boxed{
\dot K(t)

2\operatorname{Re}
\langle
(N-K(t))\psi(t),
(-iH)\psi(t)
\rangle.
}
$$

The inner-product ordering must match the convention used by the formalized Lean definitions. For this real-part identity, conjugate symmetry permits the corresponding reversed ordering.

7.2. Mathematical proof strategy

The proof should proceed from already established results.

First, use P74.2 to obtain

$$
\dot K(t)

2\operatorname{Re}
\langle N\psi(t),\dot\psi(t)\rangle.
$$

Second, use the normalization conservation theorem to establish

$$
\operatorname{Re}
\langle\psi(t),\dot\psi(t)\rangle=0.
$$

Then

$$
\begin{aligned}
2\operatorname{Re}
\langle (N-K(t))\psi(t),\dot\psi(t)\rangle
&=
2\operatorname{Re}
\langle N\psi(t),\dot\psi(t)\rangle\
&\quad-
2K(t)\operatorname{Re}
\langle\psi(t),\dot\psi(t)\rangle\
&=\dot K(t).
\end{aligned}
$$

This is the mathematical target.

The corresponding Lean proof must preserve the exact definitions, scalar conventions and normalization hypotheses.

No theorem may assume the desired centered derivative as a hypothesis.

7.3. P75 acceptance criteria

P75 can be declared verified only after:

1. The precise theorem statement is encoded.
2. Its proof compiles under Lean 4 and mathlib.
3. The proof uses the established physical derivative and normalization results.
4. No circular hypothesis is introduced.
5. The theorem's axiomatic dependencies are recorded.
6. The official workflow explicitly compiles the new file.
7. The development branch passes verification.
8. The change is merged into "main".
9. A post-merge workflow passes successfully.

Until these conditions are met, P75 remains a research target.

---

8. Subsequent formal proof obligations

Following P75, the planned work includes:

8.1. Energy and velocity norm

Establish the conserved energy-related quantity required for the Krylov dispersion speed limit under the preprint's initial-state assumptions.

The relation between the physical state derivative, its norm and the relevant initial coupling must be proved with explicit hypotheses.

8.2. Physical Krylov speed limit

Combine the centered derivative, normalized variance and Gram/Cauchy–Schwarz inequality.

The intended form is

$$
|\dot K(t)|
\le
2\sqrt{V(t)},|\dot\psi(t)|.
$$

Under the specific Jacobi initial-state hypotheses and the corresponding conserved velocity norm, derive the relevant bound involving the first coupling $b_1$.

This is not yet a verified Lean result.

8.3. Saturation deficit

Define

$$
D(t)=1-\frac{\dot K(t)^2}{4b_1^2V(t)}
$$

on an explicitly justified domain.

The formalization must establish nonvanishing denominators wherever division is used.

8.4. Finite-depth local defects

Formalize diagonal and off-diagonal defects, finite-chain boundaries, coupling-index conventions and leading Taylor coefficients.

8.5. Main finite-chain theorem

Formalize the precise mathematical counterpart of Theorem 8.1 in the research preprint, preserving all necessary assumptions and remainder estimates.

8.6. Local rigidity

Formalize the finite-depth rigidity criterion corresponding to Theorem 9.1, including positive couplings and terminal-boundary conditions.

8.7. Semi-infinite extension

Treat self-adjointness, unbounded operator domains, weighted estimates and infinite-dimensional evolution separately.

These remain research obligations, not completed Lean milestones.

---

9. Scientific status and limitations

The current formalization establishes the finite-dimensional physical Krylov complexity derivative through P74.2.

It does not claim:

- A completed Lean proof of the centered physical Krylov derivative.
- A completed Lean proof of the Krylov dispersion speed limit.
- A completed Lean proof of the saturation-deficit expansion.
- A completed Lean proof of the finite-depth local-defect hierarchy.
- A completed Lean proof of the preprint's main rigidity theorem.
- General validity for unbounded semi-infinite Jacobi operators.
- A new universal quantum speed limit.
- Independent peer-review certification.
- Established worldwide mathematical priority.
- That successful compilation verifies every scientific claim in the preprint.

The formalized Schrödinger derivative and physical Krylov complexity derivative are standard consequences of the finite-dimensional dynamical framework.

Their formalization supplies checked mathematical infrastructure for investigating the more specialized local-defect claims.

Scientific validity requires agreement between the intended mathematical theorem and the exact Lean encoding.

Scientific novelty requires independent comparison with prior literature.

These remain distinct verification responsibilities.

---

10. Research preprint

Title: Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics
Author: Valentino Lanzarini
DOI: https://doi.org/10.5281/zenodo.23163367

The preprint and this Lean repository are related but distinct scientific artifacts.

The preprint presents the proposed finite-depth local-defect hierarchy for real Jacobi dynamics.

The Lean repository currently provides formally verified foundational results through the physical Krylov complexity derivative P74.2.

The main local-defect theorem, its remainder estimates and its rigidity consequences have not yet been fully translated into machine-checked proofs.

---

11. Copyright and permissions

Copyright © 2026 Valentino Lanzarini.

All rights reserved.

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Except where applicable law or GitHub's Terms of Service permit otherwise, copying, modifying, redistributing, sublicensing or commercially exploiting the original code or documentation requires prior permission from the copyright holder.

Public visibility does not place original materials in the public domain.

Copyright protects original expression but does not confer exclusive ownership of mathematical facts, ideas or theorems.

Third-party dependencies remain subject to their respective licenses.

---

12. AI-assisted research

This research and its formalization have been developed with assistance from artificial intelligence tools.

AI assistance is not represented as independent peer review or scientific certification.

Mathematical claims require explicit proofs, reproducible checks and independent scientific scrutiny.

The author remains responsible for reviewing the research claims, the published documentation and the scope of the conclusions.

Automated theorem verification provides evidence for the validity of the encoded statements relative to the accepted formal foundations.

It does not independently establish originality or certify every translation from informal mathematics into Lean.

---

13. Author

Valentino Lanzarini

Independent Mathematical Researcher

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

Research:
https://doi.org/10.5281/zenodo.23163367

GitHub:
"Repository on GitHub" (https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/main)

---

Copyright © 2026 Valentino Lanzarini. All rights reserved.
