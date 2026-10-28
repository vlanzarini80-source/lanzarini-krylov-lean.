
# Lanzarini Krylov–Jacobi

### Lean 4 formalization of finite-dimensional Jacobi dynamics and Krylov observables

**Author:** Valentino Lanzarini, Independent Mathematical Researcher  
**Status:** Active scientific research; central preprint theorem not yet fully formalized  
**Documentation audit:** 27 October 2026  
**Environment:** Lean 4 `v4.24.0`, mathlib `v4.24.0`  
**Preprint:** [Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics](https://doi.org/10.5281/zenodo.23163367)  
**Repository:** [Lanzarini Krylov–Jacobi](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)  
**Copyright:** © 2026 Valentino Lanzarini. All rights reserved.

> **Verified status, with branches distinguished:** the most advanced verified checkpoint on `main` is **P74.2**, [GitHub Actions #117](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938). The development branch `research/p75-centered-derivative` has reached **P81.2a**, certified by [GitHub Actions #197](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40569405991). P75–P81.2a **are not merged into `main`**. This README reports verified development without claiming that the code is present on the default branch.
>
> **Not yet proved in Lean:** the physical fourth-order Gram-minor coefficients, the saturation-deficit limit, the general finite-depth local-defect hierarchy and the finite-chain rigidity theorem. A green CI result does not establish mathematical novelty or independent peer review.

## 1. Current machine-verified checkpoints

| Branch | Milestone | Evidence | Meaning |
| --- | --- | --- | --- |
| `main` | P74.2 | [Actions #117: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) | Physical Krylov-complexity derivative |
| `research/p75-centered-derivative` | P81.2a | [Actions #197: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40569405991) | Six physical Gram-bridge theorems compiled and axiom-audited |
| Next development target | P81.2b | No certified run | Fourth-order coefficients from the **actual** physical Jacobi evolution |
| Central preprint theorem | Finite-depth hierarchy | Not yet certified | Open mathematical objective |

Verified development commit:

```text
bfbf772ab6b4f3b1b5de062553da1c8fd798f8e8
```

The #197 workflow explicitly compiled `P81_2a_PhysicalGramBridge.lean` and completed its named-theorem axiom audit. The six declarations each reported only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency was reported for these declarations. This is a declaration-specific audit, **not** a proof of every statement in the preprint.

### The six verified P81.2a theorems

```lean
Lanzarini.p81_2_energyMean_zero
Lanzarini.p81_2_centeredVelocity_eq
Lanzarini.p81_2_minor_physical_bridge
Lanzarini.p81_2_minor_algebra
Lanzarini.p81_2_minor_product_rule
Lanzarini.p81_2_state_hasDerivAt
```

They establish a bridge between the actual four-site Jacobi evolution, the centered-energy velocity and the relevant Gram coordinates, as well as a first-order product rule. **They do not establish the fourth-order Taylor coefficients of the physical minors.**

## 2. Mathematical framework

Let `H` be a finite real symmetric Jacobi Hamiltonian and `ψ₀` an initial complex state. Its evolution satisfies

$$
\psi(t)=e^{-itH}\psi_0,
$$

$$
\frac{d\psi(t)}{dt}=-iH\psi(t).
$$

In the chosen finite Jacobi-chain coordinate basis, let

$$
N=\mathrm{diag}(0,1,\ldots,n-1).
$$

For a normalized state, the Krylov complexity, Krylov variance, mean energy and energy variance are

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

Introduce the centered vectors

$$
u(t)=(N-K(t)I)\psi(t),
$$

$$
v(t)=-i(H-E(t)I)\psi(t).
$$

The centered physical derivative is

$$
K'(t)=2\,\mathrm{Re}\,\langle u(t),v(t)\rangle.
$$

**GitHub display fix:** `\mathrm{Re}` is used for the real part, rather than the `\operatorname{Re}` macro that caused an error in the previous README. Mathematical expressions are written in separate `$$` blocks so GitHub can render them correctly.

The basic formalization is finite-dimensional. It does not yet provide general semi-infinite unbounded-operator results or prove that the chosen coordinate basis equals an arbitrary Hamiltonian's Lanczos basis. Lean uses zero-based `Fin n` indices; the first physical preprint coupling `b_1` is the Lean coupling between sites 0 and 1.

## 3. Formal development history

| Milestone | Verified scope | Main sources |
| --- | --- | --- |
| P51–P55 | Real Jacobi Hamiltonian; unitary finite evolution and conservation | `JacobiReal.lean`, `JacobiEvolution.lean`, `MatrixExpProbe.lean` |
| P56–P64 | Krylov number operator, moments, variance, normalized support | `KrylovNumber.lean` |
| P65–P69 | Complex Gram coordinates and finite Lagrange identity | `KrylovGram.lean`, `KrylovLagrange.lean` |
| P70–P72 | Real-part Gram gap, centered variance and derivative groundwork | `KrylovGap.lean` |
| P73.1–P73.2 | Propagator and physical state derivatives | `P73_RealTime.lean`, `P73_2_State.lean` |
| P74.1–P74.2 | Componentwise and physical Krylov-complexity derivatives | `P74_1_Components.lean`, `P74_2_KrylovDerivative.lean` |
| P75.1–P75.4 | Centered orthogonality, derivative and speed estimates | `P75_1_Orthogonality.lean` through `P75_4_DerivativeSpeedBound.lean` |
| P76.1–P76.6 | Energy variance, centered velocity and speed bound | `P76_1_EnergyVariance.lean` through `P76_6_EnergySpeedLimit.lean` |
| P77.1a–P77.2 | Hamiltonian intertwining and energy-mean conservation | `P77_1a_PropagatorCommutes.lean` through `P77_2_EnergyMeanConservation.lean` |
| P78.1–P78.2 | Exact Gram residual and connection to physical derivative | `P78_1_ExactSpeedResidual.lean`, `P78_2_PhysicalSpeedResidual.lean` |
| P79 (`r=0`) | Algebraic identities for **candidate** minor coefficients | `P79_R0_CoefficientJet.lean` |
| P80.1 | Iterated derivatives of actual Jacobi evolution | `P80_1_TrueEvolutionJets.lean` |
| P81.1 | Actual four-site Hamiltonian powers through fourth order | `P81_1_JacobiPhysicalPowers.lean` |
| **P81.2a** | **Physical Gram bridge and first-order product rule** | **`P81_2a_PhysicalGramBridge.lean`** |

All development-only rows above refer to the development branch and the corresponding successful compilation. Checkpoint numbers do not measure what percentage of the central theorem is proved.

## 4. Foundational verified mathematical results

### 4.1. Gram/Lagrange identity and real-part gap

For finite complex vectors `u`, `v`, define the Gram-minor sum

$$
G(u,v)=\sum_{i=0}^{n-1}\sum_{j=i+1}^{n-1}\left|u_i v_j-u_j v_i\right|^2.
$$

The classical finite complex Lagrange identity is

$$
G(u,v)=\|u\|^2\|v\|^2-|\langle u,v\rangle|^2.
$$

Consequently,

$$
\|u\|^2\|v\|^2-
\bigl(\mathrm{Re}\,\langle u,v\rangle\bigr)^2
=G(u,v)+\bigl(\mathrm{Im}\,\langle u,v\rangle\bigr)^2.
$$

These are standard identities, not claimed as novel mathematical discoveries.

### 4.2. Physical Krylov derivative (P74.2)

The actual finite-dimensional Jacobi evolution satisfies

$$
K'(t)=2\sum_{j=0}^{n-1}j\,\mathrm{Re}
\left(\overline{\psi_j(t)}(-iH\psi(t))_j\right).
$$

P74.2 is verified on `main`. This differentiation identity itself does not require normalization; normalization is needed for the later probability-variance interpretation.

### 4.3. Energy-variance speed estimate (P76.6)

For normalized Jacobi evolution, the verified development-branch theorem `Lanzarini.p76_6_energy_speed_limit` establishes

$$
\bigl(K'(t)\bigr)^2\leq 4V_K(t)V_H(t).
$$

This is a finite-dimensional, variance-based speed bound of a standard type, not a newly claimed universal law.

### 4.4. Exact physical speed residual (P78.1–P78.2)

For normalized evolution, let `d(t)` be the actual physical Krylov derivative. The verified identity has the structure

$$
4V_K(t)V_H(t)-d(t)^2
=4G(u(t),v(t))
+4\bigl(\mathrm{Im}\,\langle u(t),v(t)\rangle\bigr)^2.
$$

Both right-hand contributions are nonnegative. This is an exact physical residual identity, **not yet an asymptotic coefficient theorem**.

### 4.5. Candidate fourth-order coefficients (P79)

The file `P79_R0_CoefficientJet.lean` proves exact **algebraic identities for separately defined candidate jets**. With `p,q,s` the first three couplings and `δ` the relevant diagonal difference, its depth-zero defect is

$$
\Omega_0=s^2-3q^2+3p^2.
$$

The squared candidate minor coefficient is algebraically factorized as

$$
C_{\mathrm{Gram}}^{\mathrm{candidate}}
=\frac{p^4q^2}{576}\left(4\Omega_0^2+s^2\delta^2\right).
$$

With `p` nonzero, the **defined algebraic normalized candidate** equals

$$
C_{\mathrm{norm}}^{\mathrm{candidate}}
=\frac{q^2}{576}\left(4\Omega_0^2+s^2\delta^2\right).
$$

**P79 does not show that these candidates are the Taylor coefficients of the actual physical Gram minors or of the physical saturation deficit.** That bridge is the pending P81.2b task.

### 4.6. Actual dynamics and four-site Hamiltonian (P80.1–P81.1)

P80.1 proves statements relating iterated real-time state derivatives to powers of the actual Jacobi evolution generator. P81.1 specializes to the four-site Hamiltonian

$$
H=\begin{pmatrix}
0&p&0&0\\
p&0&q&0\\
0&q&0&s\\
0&0&s&\delta
\end{pmatrix}
$$

and the initial basis vector `e₀`. It derives Hamiltonian powers through `H⁴e₀` and the corresponding physical initial derivatives. Its six theorem audits were verified before P81.2a.

### 4.7. Physical Gram bridge (P81.2a)

In this four-site specialization, the conserved energy mean of the specified initial state is proved to be zero. Therefore the centered-energy velocity coincides with the physical velocity generated by `-iH`. The physical Gram coordinates agree with the centered-energy coordinates used in the residual; the algebraic minor decomposition retains the time-dependent Krylov mean. A first-order product rule and the actual physical state derivative are also established.

The first attempt at compiling P81.2a, [Actions #196](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40567202521), failed and produced a `sorryAx` dependency after an unresolved proof. The corrected [Actions #197](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40569405991) explicitly compiled P81.2a and passed all six named axiom audits. The failure was not concealed or treated as a PASS.

**P81.2a stops before the fourth-order Taylor calculation.**

## 5. Scientific target: the saturation deficit

For the first physical coupling `b₁`, the preprint studies

$$
D(t)=1-\frac{\bigl(K'(t)\bigr)^2}{4b_1^2V_K(t)}.
$$

This quotient requires a nonzero denominator. Its behavior at `t=0` requires a separate limit or extension. Passing from the general verified energy-variance bound to this specialized expression requires the appropriate initial-state, normalization, coupling and variance identities in the formal context.

Using the preprint convention `c_j=b_j²` and `c₀=0`, define

$$
\Omega_r=c_{r+3}-3c_{r+2}+3c_{r+1}-c_r.
$$

The diagonal local-defect mechanism involves `a_{r+3}-a_0`. Under suitable dimension, positivity, prefix and terminal-boundary conditions, the preprint proposes a hierarchy whose first candidate nonzero deficit order is `t^(2r+6)`. Its complete exact coefficient and rigidity consequences are **research claims**, not yet fully Lean-certified conclusions.

Open obligations include:

1. Derive actual fourth-order physical Gram-minor coefficients without inserting their expected values as hypotheses.
2. Prove all lower-order cancellations, including those involving the Krylov mean.
3. Account for every other minor and the imaginary residual channel.
4. Establish a correct analytical remainder and the actual depth-zero limit of the deficit.
5. Prove general finite-depth locality, possible mixed contributions, terminal cases and rigidity.
6. Treat the semi-infinite operator setting and arbitrary Lanczos bases separately.

## 6. Next objective: P81.2b

The next formal milestone is precisely the **derivation of the physical fourth-order Gram-minor jets**, starting from the true Jacobi evolution:

1. Reuse the P81.1 Hamiltonian-power and initial-derivative results.
2. Derive the Krylov mean and centered-state derivatives with actual product rules.
3. Derive the Gram-minor derivatives through fourth order.
4. Prove vanishing of every preceding order where mathematically claimed.
5. Derive the physical coefficients independently, and **only then** compare them with P79's candidate algebra.
6. Establish the nonzero-denominator domain and justified Taylor remainder needed for the deficit limit.

No desired coefficient may be introduced as a lemma hypothesis. No proof checkpoint is certified before a GitHub Action actually compiles the named results and its axiom audit succeeds.


## 7. Research History and Machine-Verified Checkpoints

### 7.1. Introduction: From the First Jacobi Proofs to the Research Frontier

The Lanzarini Krylov–Jacobi project is an independent mathematical research initiative developed by Valentino Lanzarini.

The Lean 4 repository was initialized on 12 October 2026 to construct a formally verified mathematical framework for finite-dimensional Jacobi dynamics, quantum evolution, Krylov observables and speed-limit saturation.

The research preprint is available at:

https://doi.org/10.5281/zenodo.23163367

The formalization proceeded through several stages.

**Stage I: Mathematical foundations**

The initial work introduced finite Jacobi matrices, their symmetry and complex representations, the evolution generator, matrix exponentials and the unitary propagator.

Formal verification was configured using Lean 4, mathlib and GitHub Actions.

**Stage II: Krylov observables**

The development established finite-dimensional Krylov complexity, moments, variance, normalization properties and zero-variance support results.

**Stage III: Gram identities and physical derivatives**

The project formalized complex Gram/Lagrange identities, centered-state variance, and derivatives of the Jacobi propagator, evolving state and Krylov complexity.

**Stage IV: Physical speed-limit framework**

The subsequent development established centered physical derivatives, energy-variance identities, speed bounds, energy conservation and exact Gram-based physical residual identities.

**Stage V: Local-defect coefficient investigation**

The latest work developed algebraic candidate coefficients for the depth-zero local-defect case, formal derivatives of the actual Jacobi evolution, four-site Hamiltonian powers and a physical Gram-minor bridge.

The current certified development checkpoint is P81.2a.

The next objective is P81.2b: deriving the fourth-order physical Gram-minor coefficients directly from Jacobi evolution.

**Scientific limitation:** the complete saturation-deficit hierarchy proposed in the research preprint has not yet been proved in Lean. The foundational results are not presented as evidence of worldwide mathematical novelty.

---

### 7.2. Initial Formal Development: 12–13 October 2026

Before the numbered P51 milestone, the project established its original Lean infrastructure and finite Jacobi foundations.

These steps were verified using GitHub Actions.

| Date | Initial development | GitHub verification |
| --- | --- | --- |
| 12 Oct 2026 | Lean 4 installation and first automated theorem verification | [Actions #2: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38297517117) |
| 12 Oct 2026 | Jacobi matrix entries and symmetry | [Actions #6: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38298941947) |
| 12 Oct 2026 | Finite real Jacobi matrix formalization | [Actions #11: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38300689272) |
| 13 Oct 2026 | Matrix exponential and evolution checks | [Actions #23: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38432979610) |
| 13 Oct 2026 | Further complex Jacobi matrix verification | [Actions #28: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38442634027) |

These successful workflows document the development that preceded the numbered P51 research milestone.

There is no claim that fifty separately numbered P1–P50 theorems were certified.

---

### 7.3. Mathematical Checkpoints: P51–P74.2

The following checkpoints were developed and verified during the foundational phase.

| Checkpoint | Mathematical development | GitHub verification |
| --- | --- | --- |
| P51–P52 | Jacobi Hamiltonian and unitary propagator | [#35: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38564356941) |
| P53–P55 | Norm, inner-product and orthogonality conservation | [#46: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38617582830) |
| P56–P64 | Krylov moments, variance and zero-variance support | [#68: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/38930795218) |
| P65–P69 | Complex Gram coordinates and finite Lagrange identity | [#80: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39039294687) |
| P70 | Exact real-part Gram-gap identity | [#83: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39042822303) |
| P71 | Centered Krylov state and variance bridge | [#84: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39044208215) |
| P72.1–P72.2 | Exact complexity increment and conditional derivative | [#89: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39108316304) |
| P72.3a | Complex-time matrix-exponential derivative | [#98: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39140660849) |
| P73.1 | Physical Jacobi propagator derivative | [#103: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39153415923) |
| P73.2 | Physical evolved-state derivative | [#109: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39248613293) |
| P74.1–P74.2 | Coordinate derivatives and physical Krylov-complexity derivative | [#117: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39399857938) |

P72.3a was also verified on a dedicated test branch.

The subsequent P73 and P74 results were integrated into `main` through reviewed development and successful post-merge workflows.

**P74.2 remains the latest mathematical checkpoint integrated and verified on `main` in the inspected repository state.**

---

### 7.4. Research Development: P75–P81.2a

The following results were developed on the branch:

`research/p75-centered-derivative`

| Checkpoint | Mathematical development | GitHub verification |
| --- | --- | --- |
| P75.1–P75.3 | Centered orthogonality, physical derivative and quadratic estimates | [#135: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39723529933) |
| P75.4 | Physical derivative speed bound | [#137: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39724698501) |
| P76.1–P76.5b | Energy variance and centered-velocity identities | [#157: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/39992902430) |
| P76.6 | Finite-dimensional energy-variance speed bound | [#159: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40004543470) |
| P77.1a | Hamiltonian and propagator commutation | [#179: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40219331707) |
| P77.1b | Hamiltonian intertwining with state evolution | [#181: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40272241027) |
| P77.2 | Conservation of the energy expectation | [#183: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40323940960) |
| P78.1 | Exact Gram-based speed residual | [#185: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40371272890) |
| P78.2 | Connection to the actual physical derivative | [#187: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40386259022) |
| P79 (`r=0`) | Algebraic identities for candidate Gram-minor coefficients | [#191: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40453775330) |
| P80.1 | Iterated derivatives of actual Jacobi evolution | [#191: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40453775330) |
| P81.1 | Physical four-site Jacobi Hamiltonian powers | [#193: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40496991584) |
| **P81.2a** | **Physical Gram-minor bridge and first-order product rule** | **[#197: SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40569405991)** |

The P79 and P80.1 modules were both explicitly compiled in GitHub Actions #191.

P81.1 was explicitly compiled and audited in #193.

P81.2a was explicitly compiled and passed its six named theorem axiom audits in #197.

These links provide a reproducible verification history, subject to the precise theorem statements and checks executed at each commit.

---

### 7.5. Latest Certified Checkpoint: P81.2a

**GitHub Actions:** [#197 — SUCCESS](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40569405991)

**Verified commit:**

`bfbf772ab6b4f3b1b5de062553da1c8fd798f8e8`

**Source file:**

`P81_2a_PhysicalGramBridge.lean`

The workflow compiled the actual P81.2a module and checked these six declarations:

```lean
Lanzarini.p81_2_energyMean_zero
Lanzarini.p81_2_centeredVelocity_eq
Lanzarini.p81_2_minor_physical_bridge
Lanzarini.p81_2_minor_algebra
Lanzarini.p81_2_minor_product_rule
Lanzarini.p81_2_state_hasDerivAt
```

The recorded axiom dependencies for all six declarations contain only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` dependency was reported for these declarations.

Earlier workflows #194 and #195 succeeded but did not yet compile P81.2a as a new verified module.

Workflow #196 attempted the complete compilation and failed.

The subsequent correction was compiled successfully in #197.

**P81.2a is therefore a machine-verified checkpoint.**

However, P81.2a does not yet prove the physical fourth-order coefficients of the Gram minors.

---

### 7.6. Historical GitHub Actions Statistics

**Repository verification snapshot: 28 October 2026**

| Category | Recorded executions |
| --- | ---: |
| Total GitHub Actions runs | 174 |
| Successful runs | 138 |
| Failed runs | 36 |

These numbers include:

- Mathematical source verification.
- Repeated proof and dependency checks.
- Workflow configuration and diagnostics.
- Documentation updates.
- Development and main-branch executions.

A successful workflow does not necessarily represent a new theorem.

The table above therefore identifies representative mathematical checkpoints rather than treating every green run as an independent discovery.

[Open complete GitHub Actions history](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions)

---

### 7.7. Current Scientific Status

**Verified development frontier:** P81.2a.

**Latest verified checkpoint integrated on `main`:** P74.2.

**Development branch:** `research/p75-centered-derivative`.

**Next checkpoint:** P81.2b.

The current formal development has established significant foundational results for finite Jacobi dynamics, physical Krylov derivatives, energy-variance speed bounds and exact Gram-based residual identities.

The remaining central mathematical challenge is to derive the physical fourth-order Gram-minor coefficients from the actual Jacobi evolution.

This requires proving the preceding Taylor-coefficient cancellations, accounting for all Gram minors and the imaginary residual channel, and justifying the necessary asymptotic remainder.

Only after that derivation can the candidate algebraic formulas from P79 be compared rigorously with the physical coefficients.

The subsequent goal is to investigate the general finite-depth local-defect hierarchy, including diagonal and off-diagonal defects, mixed contributions, terminal cases and rigidity.

These central results must not be declared formally proved before their corresponding Lean theorems have been compiled and independently audited.

**Formal verification establishes the encoded mathematical statements relative to Lean's accepted foundations. It does not establish mathematical originality, worldwide priority or independent peer review.**

Research preprint:

https://doi.org/10.5281/zenodo.23163367

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**


## 8. Reproducibility and formal-integrity policy

The research branch uses:

```text
lean-toolchain                  Lean 4 v4.24.0
lakefile.toml                  mathlib v4.24.0
.github/workflows/lean.yml     compilation and axiom audit
```

At the audit date, `lake-manifest.json` was not committed in the inspected branch roots; the workflow runs `lake update` and retrieves cached mathlib artifacts. Thus the recorded run is concrete verification evidence, but a reviewed lockfile would improve exact dependency-snapshot reproducibility.

Research policy:

- No `sorry`, `admit`, `sorryAx` or unjustified extra axioms in completed proofs.
- No circular hypotheses containing the conclusion to be proved.
- No weakening of theorem statements to obtain a green build.
- Explicit compilation of new modules and `#print axioms` checks of their theorem dependencies.
- Preservation of original proof statements, source commits, workflow logs and failures.
- Separate treatment of formal verification, physical interpretation, mathematical novelty and independent peer review.
- Development code must be reviewed and tested again before or after merging into `main`.

## 9. Repository organization and branch policy

The default branch `main` contains the foundational files through `P74_2_KrylovDerivative.lean`. On `research/p75-centered-derivative`, the later research modules include:

```text
P76_6_EnergySpeedLimit.lean
P77_1a_PropagatorCommutes.lean
P77_1b_HamiltonianIntertwining.lean
P77_2_EnergyMeanConservation.lean
P78_1_ExactSpeedResidual.lean
P78_2_PhysicalSpeedResidual.lean
P79_R0_CoefficientJet.lean
P80_1_TrueEvolutionJets.lean
P81_1_JacobiPhysicalPowers.lean
P81_2a_PhysicalGramBridge.lean
```

**Updating this README on `main` is a documentation change, not a code merge.** The new development results remain available on their branch until a separate reviewed merge and post-merge verification.

## 10. Scientific limitations and independent review

Standard results such as the finite-dimensional Schrödinger equation derivative, Gram/Lagrange identity and variance speed bound are not claimed to be new discoveries. The originality and correctness of the proposed local-defect hierarchy remain separate questions requiring rigorous proof, literature comparison and specialist review.

AI-assisted proof development is not independent peer review. A successful Lean proof establishes that the **encoded statement**, under its precise hypotheses and foundational axioms, follows in the formal system. It does not automatically validate the whole preprint or any unformalized scientific claim.

## 11. Copyright and permissions

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**

The repository is publicly visible for inspection and scientific discussion. At this audit no general project `LICENSE` file was present in the inspected repository roots. Public visibility by itself is not a general open-source license. Third-party dependencies remain subject to their own licenses. Copyright protects original expression subject to applicable law, not exclusive ownership of mathematical facts, ideas or theorems.

## 12. Author and references

**Valentino Lanzarini**  
Independent Mathematical Researcher  
Krylov Dynamics · Jacobi Operators · Quantum Evolution · Formal Verification

**Preprint:** [Local Defect Hierarchies for Krylov Speed-Limit Saturation in General Real Jacobi Dynamics](https://doi.org/10.5281/zenodo.23163367)  
**Repository:** [Lanzarini Krylov–Jacobi](https://github.com/vlanzarini80-source/lanzarini-krylov-lean.)  
**Latest certified development run:** [GitHub Actions #197](https://github.com/vlanzarini80-source/lanzarini-krylov-lean./actions/runs/40569405991)

---

**Copyright © 2026 Valentino Lanzarini. All rights reserved.**
