
# Lanzarini Krylov-Jacobi

## Lean 4 Formalization of Finite-Dimensional Jacobi Dynamics

**Author:** Valentino Lanzarini  
**Affiliation:** Independent Mathematical Researcher  
**Project status:** Research in progress  
**Latest recorded CI-verified checkpoint on development branch:** P83.4b  
**Verification record:** Lean 4 Verification #283, commit `d448949`  
**Latest known verified checkpoint on `main`:** P74.2  
**Development branch:** `research/p75-centered-derivative`  
**Lean:** v4.24.0  
**mathlib:** v4.24.0  
**Documentation status:** 7 November 2026  

**Research preprint:** *Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics*

**Repository:** [lanzarini-krylov-lean.](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)

**Verification workflow:** [Lean 4 Verification](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml)

**Preprint DOI:** [10.5281/zenodo.23163367](https://doi.org/10.5281/zenodo.23163367)

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**

---

# Research Mission: From the Preprint to Formal Mathematical Verification

## Scientific Question

How do the local coefficients of a Jacobi Hamiltonian determine whether Krylov complexity saturates its quantum speed limit, and how does the system depart from saturation at short times?

This repository develops a Lean 4 formalization of mathematical structures investigated in the associated preprint.

The objective is to examine:

- The foundational energy-variance speed-limit inequality.
- The short-time saturation deficit.
- The leading physical coefficients of that deficit.
- The local Jacobi defect structure.
- Finite-chain boundary behavior.
- The distinction between algebraic identities and physical evolution.
- The formal verification of mathematical statements under explicit hypotheses.

## Mathematical Strategy

For a finite real symmetric Jacobi Hamiltonian \(H\), consider the physical evolution

$$
\psi(t)=e^{-itH}\psi_0.
$$

In the encoded finite coordinate basis, define the Krylov number operator \(N\) and observables

$$
K(t)=\langle\psi(t),N\psi(t)\rangle,
$$

$$
V_K(t)=\langle\psi(t),N^2\psi(t)\rangle-K(t)^2.
$$

A foundational energy-variance speed limit is

$$
(K'(t))^2\leq 4V_K(t)V_H(t).
$$

For the relevant initial-state specialization, the proposed saturation deficit is

$$
D(t)=1-\frac{[K'(t)]^2}{4b_1^2V_K(t)},
$$

where the denominator must be strictly positive.

The research aims to derive the leading short-time behavior directly from physical evolution, without assuming the coefficient to be proved.

## Verified Progress and Current Boundary

The recorded Lean development includes:

- **P73–P74:** Physical evolution and complexity derivatives.
- **P75–P76:** Centered-state identities and speed-limit inequalities.
- **P77–P78:** Energy conservation and residual identities.
- **P79–P81:** Algebraic jets and physical Gram bridges.
- **P82:** Physical jets, observables, and residual derivatives.
- **P83:** Physical Gram-minor identities and fourth-order centering cancellation.

The latest recorded full-workflow checkpoint on `research/p75-centered-derivative` is **P83.4b**, associated with Lean 4 Verification #283 and commit `d448949`.

The supplied CI evidence reports successful module compilation through P83.4b and a successful required-theorem axiom audit.

The development-branch result must not be confused with integration into `main`.

## Open Mathematical Target

For the four-site Jacobi model detailed in Section 6, set

$$
\Omega_0=s^2-3q^2+3p^2.
$$

The proposed short-time result is

$$
\boxed{
\lim_{t\to0}\frac{D(t)}{t^6}
=
\frac{q^2}{576}
\left(4\Omega_0^2+s^2\delta^2\right)
}.
$$

**Status: Open research target, not a Lean-verified theorem about the complete physical evolution.**

Establishing this result requires:

1. Lower-order physical derivative cancellations.
2. Derivation of the exact physical coefficient.
3. Strict positivity of the denominator near zero.
4. Justification of the normalized limit.
5. Explicit treatment of degenerate couplings and terminal cases.

Further research concerns the general local-defect hierarchy, finite-chain rigidity, and extensions beyond finite dimension.

## Why Formal Verification?

Lean 4 makes theorem statements, assumptions, and proof dependencies explicit and independently inspectable.

Successful compilation and axiom auditing support the precise encoded statements.

They do not establish:

- Mathematical novelty.
- General equivalence with the intended physical interpretation.
- Independent peer review.
- Completion of every theorem in the associated preprint.

**Scientific objective:** Build a formally verified mathematical foundation for Krylov speed-limit saturation and local-defect results while clearly distinguishing established theorems from open research objectives.

---

# 1. Scientific Status

This repository develops Lean 4 formalizations of finite-dimensional real Jacobi dynamics, quantum evolution, Krylov observables, variance inequalities, physical derivatives, and related residual identities.

The current recorded development-branch verification milestone is **P83.4b**, associated with:

| Field | Recorded value |
|---|---|
| Workflow | Lean 4 Verification |
| Run | #283 |
| Commit | `d448949` |
| Branch | `research/p75-centered-derivative` |
| Reported result | SUCCESS |
| Required-theorem axiom audit | PASS |

The recorded workflow explicitly compiled the relevant P83 fourth-order dependencies:

- `P83_LeibnizSecond_Candidate.lean`
- `P83_LeibnizLocal_Candidate.lean`
- `P83_LocalFourthCancellation_Candidate.lean`
- `P83_4b_W13CenteringFourthCancellation.lean`

Its source and required-theorem axiom audits passed according to the supplied CI record.

The reported axioms for the fourth-order cancellation declarations were limited to:

```text
propext
Classical.choice
Quot.sound
```

## What P83.4b Establishes

Under the theorem's explicitly stated local regularity and vanishing-jet hypotheses, the fourth derivative at zero of the W13 centering correction vanishes.

It does not independently establish:

- All required hypotheses from physical Jacobi evolution.
- The fourth derivative of the complete physical centered Gram minor.
- The physical eighth-order residual coefficient.
- The normalized sixth-order saturation-deficit limit.

The latest verified checkpoint known on `main` is P74.2.

Results on the development branch are not described as merged into `main`.

The repository does not establish the novelty of the preprint or constitute independent peer review.

---

# 2. Mathematical Framework

Let \(H\) be a finite real symmetric Jacobi Hamiltonian with real diagonal entries and nearest-neighbor off-diagonal couplings.

The physical evolution is

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
$$

$$
V_H(t)=\left\|(H-E(t)I)\psi(t)\right\|^2.
$$

These equations describe the intended mathematical interpretation.

The actual Lean definitions and theorem hypotheses determine the formal scope.

## Basis-Identification Limitation

The encoded number operator acts in the finite `Fin n` coordinate basis.

The repository has not established a general theorem identifying this basis with the Lanczos basis for an arbitrary Hamiltonian and initial state.

## Dimensional Limitation

The currently recorded verified development is finite-dimensional.

No general semi-infinite or unbounded-operator theorem follows from these files.

---

# 3. Formal Verification History

The following table distinguishes historical milestones from development-branch results.

**Verified** refers to recorded CI compilation and axiom auditing, not an independent assessment of the preprint's originality.

| Checkpoint | Formalization or result | Evidence status |
|---|---|---|
| P51–P55 | Jacobi Hamiltonians and unitary evolution | Earlier development history |
| P56–P64 | Krylov observables, moments, and variance | Earlier development history |
| P65–P69 | Complex Gram and Lagrange identities | Earlier development history |
| P70 | Real-part Gram-gap identity | Earlier development history |
| P71 | Centered-state variance identity | Historical CI record |
| P72 | Complexity differentiation and matrix exponential derivatives | Historical CI record |
| P73.1 | Physical propagator derivative | Historical CI record |
| P73.2 | Physical evolved-state derivative | Historical CI record |
| P74.1 | Componentwise state derivatives | Audited in historical full CI |
| P74.2 | Physical Krylov complexity derivative | Latest known verified `main` checkpoint |
| P75.1 | Centered-state orthogonality | Audited in full CI |
| P75.2a | Physical velocity orthogonality | Audited in full CI |
| P75.2b | Centered physical complexity derivative | Audited in full CI |
| P75.3 | Quadratic speed estimate | Audited in full CI |
| P75.4 | Physical derivative speed bound | Audited in full CI |
| P76.1 | Energy variance nonnegativity | Audited in full CI |
| P76.2 | Energy variance identities | Audited in full CI |
| P76.3 | Energy second-moment representation | Audited in full CI |
| P76.4 | Centered energy orthogonality | Audited in full CI |
| P76.5 | Centered velocity inner-product identity | Audited in full CI |
| P76.5b | Centered velocity norm identity | Audited in full CI |
| P76.6 | Energy-variance speed bound | Audited; earlier #159 success |
| P77.1a | Jacobi Hamiltonian and propagator commutation | Audited in full CI |
| P77.1b | Hamiltonian intertwining with physical evolution | Audited in full CI |
| P77.2 | Energy-pair and energy-mean conservation | Audited in full CI |
| P78.1 | Exact speed-residual identity and nonnegativity | Audited in full CI |
| P78.2 | Physical speed-channel derivative and residual identity | Audited in full CI |
| P79 R0 | Algebraic minor, Gram-jet, and deficit-jet identities | Audited; not the physical coefficient derivation |
| P80.1 | Iterated physical-evolution derivatives | Audited in full CI |
| P81.1 | Physical Jacobi powers \(H^1\) through \(H^4\) and initial derivatives | Audited in full CI |
| P81.2a | Physical Gram bridge and product rule | Audited in full CI |
| P81.2b | Initial physical state and observable data | Audited in full CI |
| P81.2b1 | Physical acceleration | Audited in full CI |
| P81.2b2 | Physical raw-minor derivative | Audited in full CI |
| P81.2b3 | Physical Krylov derivative bridge | Audited in full CI |
| P81.2b3b | Centered-minor decomposition | Audited in full CI |
| P82.2 | Physical evolution jets | Audited in full CI |
| P82 NormSqProbe | Complex norm-square derivative lemma | Audited in full CI |
| P82.3 | Physical second moment and variance: zero values and first derivatives | Audited in #225 and later full CI |
| P82.4a | Physical R0 residual definition, derivative bridge, and zero value | Compiled and audited in later full CI |
| P82.4b | Physical residual derivative | Compiled and audited in later full CI |
| P82.4c | Physical acceleration bridge | Compiled and audited in later full CI |
| P82.5 | Physical Krylov acceleration | Compiled and audited in later full CI |
| P82.6 | Physical residual derivatives | Compiled and audited in later full CI |
| P82.7 | Initial residual cancellation | Compiled and audited in later full CI |
| P83.1 | Physical Gram and Jacobi-power jets | Compiled and audited in later full CI |
| P83.2 | Physical minor acceleration | Compiled and audited in later full CI |
| P83.3 | Centered Gram derivative and centering-correction bridge | Compiled and audited in #283 |
| P83.4a | W13 physical fourth-jet numerator algebraic identity | Compiled and audited in #283; not the complete physical minor derivative |
| P83 Leibniz | Local second- and third-order product derivative rules | Compiled and audited in #283 |
| P83 local fourth | Fourth-order product cancellation under local smoothness and vanishing jets | Compiled and audited in #283 |
| P83.4b | Fourth derivative of W13 centering correction vanishes under seven explicit hypotheses | Full CI #283 PASS; axiom audit PASS; development branch only |

The results beyond P74.2 are recorded on `research/p75-centered-derivative`.

They are not asserted here to be integrated into `main`.

---

# 4. Foundational Energy-Variance Speed Limit: P76.6

The theorem

```lean
Lanzarini.p76_6_energy_speed_limit
```

establishes, under its encoded finite-dimensional and normalization assumptions, a variance-based bound:

$$
(K'(t))^2\leq 4V_K(t)V_H(t).
$$

Equivalently, for nonnegative variances,

$$
|K'(t)|\leq 2\sqrt{V_K(t)V_H(t)}.
$$

The proof builds on:

- Physical differentiation.
- Centered states.
- Gram inequalities.
- Centered energy.
- Physical velocity.
- Energy-variance identities.

The desired inequality is not introduced as an assumption.

This is a formalization of a variance-based speed-limit result, not a claim to have discovered a new universal physical law.

---

# 5. Physical Evolution, Gram Bridges, and Observables: P77–P83.4b

## 5.1. Conservation and Physical Residuals: P77–P78

The development includes Hamiltonian–propagator commutation, Hamiltonian intertwining, energy conservation, and exact physical speed-residual identities.

Relevant files:

```text
P77_1a_PropagatorCommutes.lean
P77_1b_HamiltonianIntertwining.lean
P77_2_EnergyMeanConservation.lean
P78_1_ExactSpeedResidual.lean
P78_2_PhysicalSpeedResidual.lean
```

These identities are useful prerequisites.

They do not themselves prove the required short-time coefficient.

## 5.2. Algebraic Jets Versus Physical Jets: P79–P81

`P79_R0_CoefficientJet.lean` contains audited algebraic formulas for R0 minors, a Gram jet, and a deficit jet.

Those formulas must not be treated as a substitute for deriving the coefficient from the actual evolved state.

`P80_1_TrueEvolutionJets.lean` formalizes iterated physical derivatives.

The P81 series establishes:

- Hamiltonian powers.
- Initial physical derivatives.
- Physical Gram bridges.
- Physical acceleration.
- Raw-minor differentiation.
- Centered-minor decomposition.

## 5.3. Physical Observables and Residual Derivatives: P82

### P82.2

`P82_2_PhysicalJets.lean`

Physical state jets and their initial values.

### P82 NormSqProbe

`P82_NormSqProbe.lean`

Complex norm-square derivative lemma.

### P82.3

`P82_3_PhysicalObservables.lean`

Initial values and first derivatives for the physical second moment and variance.

### P82.4a

`P82_4a_PhysicalResidual.lean`

Physical R0 residual definitions and identities.

### P82.4b–P82.7

Physical residual derivative and acceleration bridges, and initial residual cancellation.

The four P82.3 declarations audited in historical run #225 are:

```lean
Lanzarini.p82_3_M2_zero
Lanzarini.p82_3_V_zero
Lanzarini.p82_3_M2_hasDerivAt
Lanzarini.p82_3_V_hasDerivAt
```

P82.4a was not compiled in the earlier #226 workflow, despite that run being green.

Later full-workflow verification explicitly included P82.4a and subsequent modules.

This historical limitation is preserved to avoid attributing verification to the wrong run.

## 5.4. Fourth-Order W13 Centering: P83

### P83.4a: Physical Fourth-Jet Numerator

`P83_4a_W13PhysicalFourthJetNumerator.lean`

This module proves an algebraic identity involving physical Jacobi-power jets, with expression

$$
-i\delta p^2qs.
$$

**Scope:** This is a numerator/jet identity.

It is not, by itself, the fourth derivative of the complete physical W13 centered Gram minor.

### P83 Local Leibniz Rule

`P83_LeibnizLocal_Candidate.lean`

This module develops a local third-order Leibniz rule.

### P83 Local Fourth-Order Cancellation

`P83_LocalFourthCancellation_Candidate.lean`

This module proves a local fourth-order product cancellation under `ContDiffAt ℝ 4` hypotheses and vanishing lower-order jets.

### P83.4b: W13 Centering Fourth-Order Cancellation

`P83_4b_W13CenteringFourthCancellation.lean`

This module applies the cancellation lemma to the physical W13 centering correction.

Its theorem retains the original seven hypotheses:

- Two fourth-order local smoothness assumptions.
- Two initial Krylov jets.
- Three initial raw-minor jets.

The formal conclusion is

$$
\left.
\frac{d^4}{dt^4}
\bigl(K(t)R_{13}(t)\bigr)
\right|_{t=0}
=0
$$

under those hypotheses.

The supplied full CI #283 record reports successful compilation and axiom auditing.

The remaining physical bridge must derive the necessary hypotheses from Jacobi evolution and connect the algebraic numerator to the complete centered minor.

---

# 6. R0 Model and Outstanding Short-Time Coefficient

The four-site Jacobi model under study is

$$
H=
\begin{pmatrix}
0 & p & 0 & 0\\
p & 0 & q & 0\\
0 & q & 0 & s\\
0 & 0 & s & \delta
\end{pmatrix},
$$

with

$$
\psi_0=e_0,
\qquad
N=\operatorname{diag}(0,1,2,3).
$$

Define

$$
K(t)=\sum_{j=0}^{3}j|\psi_j(t)|^2,
$$

$$
V_K(t)=
\sum_{j=0}^{3}j^2|\psi_j(t)|^2-K(t)^2,
$$

$$
F(t)=4p^2V_K(t)-[K'(t)]^2,
$$

and

$$
D(t)=\frac{F(t)}{4p^2V_K(t)},
$$

where the denominator must be strictly positive.

Define

$$
\Omega_0=s^2-3q^2+3p^2.
$$

## Research Target

Under suitable explicit coupling and regularity assumptions, derive from physical evolution

$$
F^{(k)}(0)=0
\qquad
(0\leq k\leq 7),
$$

and

$$
\boxed{
\frac{F^{(8)}(0)}{8!}
=
\frac{p^4q^2}{144}
\left(4\Omega_0^2+s^2\delta^2\right)
}.
$$

Then justify

$$
\lim_{t\to0}\frac{V_K(t)}{t^2}=p^2,
$$

and

$$
\boxed{
\lim_{t\to0}\frac{D(t)}{t^6}
=
\frac{q^2}{576}
\left(4\Omega_0^2+s^2\delta^2\right)
}.
$$

**Status: Research target, not yet a Lean-certified theorem.**

The derivation must:

1. Establish positivity for sufficiently small nonzero \(t\).
2. Avoid circular use of the target coefficient.
3. Prove the lower-order cancellations.
4. Derive the coefficient from actual physical evolution.
5. Treat degeneracies and terminal cases separately.

The displayed coefficient is a candidate under investigation, not an independently certified mathematical discovery.

---

# 7. Lean Verification Evidence and Axiom Audit

## 7.1. Historical Checkpoint: P82.3

GitHub Actions Lean 4 Verification #225, on `research/p75-centered-derivative`, commit `65e4762`, completed successfully according to the recorded evidence.

The audit included:

```text
PASS p82_normSq_probe:
['Classical.choice', 'Quot.sound', 'propext']

PASS p82_3_M2_zero:
['Classical.choice', 'Quot.sound', 'propext']

PASS p82_3_V_zero:
['Classical.choice', 'Quot.sound', 'propext']

PASS p82_3_M2_hasDerivAt:
['Classical.choice', 'Quot.sound', 'propext']

PASS p82_3_V_hasDerivAt:
['Classical.choice', 'Quot.sound', 'propext']
```

All required theorem axiom audits passed.

The subsequently added P82.4a candidate was not included in run #226's compile/audit list.

A green CI run must never be used to claim verification of a module it did not compile.

## 7.2. Current Full-Workflow Checkpoint: P83.4b

Recorded verification:

| Property | Value |
|---|---|
| Workflow | Lean 4 Verification |
| Run | #283 |
| Branch | `research/p75-centered-derivative` |
| Commit | `d448949` |
| Reported status | SUCCESS |
| Required-theorem axiom audit | PASS |

The supplied CI logs include:

```text
=== Compiling P83_4a_W13PhysicalFourthJetNumerator.lean ===

'Lanzarini.p83_4a_w13_fourth_jet_numerator'
depends on axioms:
[propext, Classical.choice, Quot.sound]

=== Compiling P83_LeibnizSecond_Candidate.lean ===

'Lanzarini.p83_leibniz_second'
depends on axioms:
[propext, Classical.choice, Quot.sound]

'Lanzarini.p83_leibniz_third'
depends on axioms:
[propext, Classical.choice, Quot.sound]

=== Compiling P83_LeibnizLocal_Candidate.lean ===

'Lanzarini.p83_local_leibniz_third'
depends on axioms:
[propext, Classical.choice, Quot.sound]

=== Compiling P83_LocalFourthCancellation_Candidate.lean ===

'Lanzarini.p83_local_fourth_product_zero'
depends on axioms:
[propext, Classical.choice, Quot.sound]

=== Compiling P83_4b_W13CenteringFourthCancellation.lean ===

'Lanzarini.p83_4b_w13_centering_fourth_zero'
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The workflow's **Audit source files and required theorem axioms** step passed.

The recorded allowed axioms are:

```text
propext
Classical.choice
Quot.sound
```

The reported fourth-order declarations did not depend on `sorryAx`.

Linter warnings about unused simplification arguments or unnecessary tactic sequencing do not invalidate compilation.

Such warnings may be cleaned up in a separate, tested commit.

### Scope of Verification

The audit supports the statements and dependencies actually encoded in the compiled Lean files.

It does not prove:

- The complete DOI preprint.
- A general physical fourth-derivative coefficient.
- The eighth-order physical residual coefficient.
- The normalized sixth-order deficit limit.
- Mathematical novelty.

## 7.3. Next Verification Gate

The next target is a theorem that:

1. Derives the necessary W13 initial jets from physical Jacobi evolution.
2. Derives the required local smoothness conditions.
3. Connects the P83.4a algebraic numerator to the actual physical fourth derivative.
4. Identifies the complete centered-minor fourth derivative.
5. Does not assume the desired coefficient.
6. Does not import P79 as the source of the physical coefficient.

The verification gate requires:

- An explicit Lean source file.
- Successful Lean compilation.
- Required-theorem axiom audit.
- Exact commit evidence.
- Exact GitHub Actions run evidence.

Only then should the physical bridge be marked verified.

## 7.4. Limits of CI Evidence

Successful Lean compilation verifies the encoded theorem relative to its dependencies and accepted logical foundations.

It does not establish:

- Scientific novelty.
- Independent peer review.
- Equivalence of every encoded object with the intended physical model.
- Completion of the preprint.

---

# 8. Reproducibility and Verification Records

The project specifies:

```text
Lean 4: v4.24.0
mathlib: v4.24.0
```

Relevant files include:

```text
lean-toolchain
lakefile.toml
.github/workflows/lean.yml
```

The workflow resolves mathlib dependencies using `lake update` and retrieves the cache.

A previously identified reproducibility limitation was the absence of a committed `lake-manifest.json` at the P76.6 audit checkpoint.

A dependency lockfile and an exact commit remain important for independently repeating the result.

The lockfile's status at later commits must be checked rather than assumed.

## Selected Historical Verification Records

| Milestone | GitHub Actions record |
|---|---|
| P71 | [Run 39044208215](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) |
| P72.3a | [Run 39140660849](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849) |
| P73.1 | [Run 39153415923](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923) |
| P73.2 | [Run 39248613293](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293) |
| P74.2 | [Run 39399857938](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) |
| P76.6 | [Run 40004543470](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470) |
| P82.3 | Verification #225, commit `65e4762` |
| P82.4a historical candidate | Verification #226, commit `a4c1c46`; module not included at that time |
| P83.4b | Verification #283, commit `d448949`; full compilation and audit PASS |

## Repository Links

- [Repository](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)
- [Development branch](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/research/p75-centered-derivative)
- [Lean verification workflow](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml)
- [GitHub Actions history](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions)
- [Recorded P83.4b commit](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./commit/d448949)
- [Research preprint](https://doi.org/10.5281/zenodo.23163367)

The intended integration commit should be reviewed and verified before merging development changes into `main`.

---

# 9. Remaining Mathematical Research

## 9.1. Complete Physical W13 Fourth Derivative

Use the verified P83.4b centering cancellation as one component.

Then:

1. Derive the required initial conditions from Jacobi evolution.
2. Establish the required local regularity.
3. Connect the P83.4a algebraic numerator to the actual physical fourth derivative.
4. Identify the complete centered W13 minor derivative.

Do not assume the target coefficient.

Do not substitute the P79 algebraic coefficient formula for its physical derivation.

## 9.2. Physical Eighth-Order Residual Coefficient

The decisive later task is to extract the eighth-order physical speed-residual coefficient from derivatives of the actual evolved state.

All lower-order cancellations must be proved.

The intended target is

$$
\frac{F^{(8)}(0)}{8!}
=
\frac{p^4q^2}{144}
\left(4\Omega_0^2+s^2\delta^2\right).
$$

This remains unverified as a complete physical Lean theorem.

## 9.3. Positive Denominator and Normalized Deficit

For the first coupling \(b_1\), the proposed saturation deficit is

$$
D(t)=1-\frac{[K'(t)]^2}{4b_1^2V_K(t)},
$$

only where the denominator is nonzero.

The positive-denominator argument and normalized limit must be proved.

They must not be inferred merely from a formal quotient.

## 9.4. Finite-Depth Local Defects

Using the preprint's indexing convention,

$$
c_j=b_j^2,
\qquad
c_0=0,
$$

and

$$
\Omega_r
=
c_{r+3}-3c_{r+2}+3c_{r+1}-c_r,
$$

$$
\delta_r=a_{r+3}-a_0.
$$

The proposed hierarchy requires:

- Explicit prefix assumptions.
- Correct coupling indices.
- Finite-chain boundary conventions.
- Positivity conditions.
- Exact leading coefficients.
- Remainder bounds.
- Independent verification.

None of these conclusions follows from P76.6 or P83.4b alone.

## 9.5. Finite-Chain Rigidity and Terminal Cases

Rigidity claims and terminal boundary cases require their own statements and proofs.

Nonterminal formulas must not be extended to terminal chains without justification.

## 9.6. Semi-Infinite Jacobi Dynamics and Lanczos Equivalence

Extensions to semi-infinite, potentially unbounded Jacobi operators require additional operator-theoretic hypotheses.

General equivalence with a Lanczos basis is also not established by the current finite-coordinate formalization.

---

# 10. Research Preprint and Scientific Interpretation

**Title:** *Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics*

**Author:** Valentino Lanzarini

**DOI:** [10.5281/zenodo.23163367](https://doi.org/10.5281/zenodo.23163367)

The preprint and the Lean repository are distinct scientific artifacts.

Verified Lean lemmas support precisely their encoded statements.

They do not automatically establish every theorem, hypothesis, coefficient, or interpretation in the preprint.

In particular, the following are not presented as completed Lean formalizations:

- Full local-defect hierarchy.
- Complete physical W13 fourth derivative.
- Physical eighth-order residual coefficient.
- Normalized sixth-order deficit limit.
- Terminal rigidity results.
- Semi-infinite extensions.

Claims of novelty and priority require independent literature comparison and specialist evaluation.

---

# 11. Scientific Integrity

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

The research process prioritizes mathematical correctness, reproducibility, and falsifiability over the number of completed checkpoints.

---

# 12. Copyright and Permissions

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**

The repository is publicly accessible for inspection and scientific discussion.

No general open-source license is granted for the original source code or documentation.

Third-party dependencies remain subject to their respective licenses.

Copyright protects original expression but does not grant exclusive ownership of mathematical facts, ideas, or theorems.

---

# 13. AI-Assisted Research and Author

Artificial intelligence tools have assisted the development, checking, and formalization of this project.

AI assistance does not constitute independent peer review.

The author remains responsible for reviewing mathematical claims, code, documentation, and scientific conclusions.

Formal verification and independent scientific evaluation are complementary but distinct processes.

## Author

**Valentino Lanzarini**  
Independent Mathematical Researcher

**Research areas:**

Krylov Dynamics | Jacobi Operators | Quantum Evolution | Formal Verification

**Preprint:**  
https://doi.org/10.5281/zenodo.23163367

**Repository:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean.

**Development branch:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./tree/research/p75-centered-derivative

**Verification workflow:**  
https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/workflows/lean.yml

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**

**Project status: Research in progress.**

**Latest recorded development-branch verification checkpoint: P83.4b.**

**Next mathematical objective: Complete the physical W13 fourth-derivative bridge from Jacobi evolution without assuming the target coefficient.**
