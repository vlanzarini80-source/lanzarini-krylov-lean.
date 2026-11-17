
import P84_4j_PhysicalEnergyVariance_Candidate

namespace Lanzarini

/-!
P84.4k: exact physical Gram identity.

The three bridge hypotheses of P84.4h
are discharged using P84.4i and P84.4j.

All six Jacobi parameters remain free.
No Taylor coefficients are inserted.
No P79.
No sorry, admit, or new axioms.
-/

/--
Exact Gram decomposition of the physical
four-site Krylov speed deficit.
-/
theorem p84_4k_exact_physical_gram_identity
    (p q r d e f t : ℝ) :
    p84_4c2_D p q r d e f t =
      4 * krylovGramSum
        (krylovCenteredState
          (jacobiState 4
            (p84_a d e f)
            (p84_b p q r)
            t p81_e0))
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy 4
              (p84_a d e f)
              (p84_b p q r)
              (jacobiState 4
                (p84_a d e f)
                (p84_b p q r)
                t p81_e0)) j) +
      4 * (jacobiInner
        (krylovCenteredState
          (jacobiState 4
            (p84_a d e f)
            (p84_b p q r)
            t p81_e0))
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy 4
              (p84_a d e f)
              (p84_b p q r)
              (jacobiState 4
                (p84_a d e f)
                (p84_b p q r)
                t p81_e0)) j)).im ^ 2 := by

  exact p84_4h_physical_gram_bridge
    p q r d e f t
    p84_4j_initial_norm
    (p84_4i_variance_bridge
      p q r d e f t)
    (p84_4j_physical_energy_variance
      p q r d e f t)
    (p84_4i_speed_bridge
      p q r d e f t
      p84_4j_initial_norm)

#print axioms p84_4k_exact_physical_gram_identity

end Lanzarini
