
import P84_4h_PhysicalGramBridge_Candidate
import P78_2_PhysicalSpeedResidual

namespace Lanzarini

/-!
P84.4i: discharge two hypotheses of P84.4h.

1. Identify the physical four-site Krylov variance.
2. Identify the physical speed with the P78 channel.

No Taylor coefficients.
No P79.
No sorry, admit, or new axioms.

Candidate: requires independent Lean CI verification.
-/

theorem p84_4i_variance_bridge
    (p q r d e f t : ℝ) :
    p84_4c1_V p q r d e f t =
      krylovVarianceAt 4
        (p84_a d e f)
        (p84_b p q r)
        t p81_e0 := by
  rfl

theorem p84_4i_speed_bridge
    (p q r d e f t : ℝ)
    (hnorm : jacobiNormSq p81_e0 = 1) :
    p84_4c2_J p q r d e f t =
      p78_speedChannelAt 4
        (p84_a d e f)
        (p84_b p q r)
        t p81_e0 := by

  have hphysical :=
    p84_4c3_K_hasDerivAt
      p q r d e f t

  have hchannel :=
    p78_2_speedChannel_derivative
      4
      (p84_a d e f)
      (p84_b p q r)
      t
      p81_e0
      hnorm

  change
    HasDerivAt
      (p84_4c1_K p q r d e f)
      (p78_speedChannelAt 4
        (p84_a d e f)
        (p84_b p q r)
        t p81_e0)
      t at hchannel

  have h1 := hphysical.deriv
  have h2 := hchannel.deriv

  exact h1.symm.trans h2

#print axioms p84_4i_variance_bridge
#print axioms p84_4i_speed_bridge

end Lanzarini
