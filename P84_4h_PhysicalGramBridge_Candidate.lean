
import P78_1_ExactSpeedResidual
import P84_4d1_PhysicalObservableBridge

namespace Lanzarini

/-!
P84.4h: conditional transfer of the existing P78 Gram identity
into the physical four-site deficit.

This theorem does not prove its three bridge hypotheses.
The physical energy variance equality must be established
separately.

No P79.
No inserted Taylor coefficient.
No new axioms.
-/

theorem p84_4h_physical_gram_bridge
    (p q r d e f t : ℝ)
    (hnorm : jacobiNormSq p81_e0 = 1)
    (hvariance :
      p84_4c1_V p q r d e f t =
        krylovVarianceAt 4
          (p84_a d e f) (p84_b p q r) t p81_e0)
    (henergy :
      p76_energyVarianceAt 4
        (p84_a d e f) (p84_b p q r) t p81_e0 = p ^ 2)
    (hspeed :
      p84_4c2_J p q r d e f t =
        p78_speedChannelAt 4
          (p84_a d e f) (p84_b p q r) t p81_e0) :
    p84_4c2_D p q r d e f t =
      4 * krylovGramSum
        (krylovCenteredState
          (jacobiState 4
            (p84_a d e f) (p84_b p q r) t p81_e0))
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy 4
              (p84_a d e f) (p84_b p q r)
              (jacobiState 4
                (p84_a d e f) (p84_b p q r)
                t p81_e0)) j) +
      4 * (jacobiInner
        (krylovCenteredState
          (jacobiState 4
            (p84_a d e f) (p84_b p q r) t p81_e0))
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy 4
              (p84_a d e f) (p84_b p q r)
              (jacobiState 4
                (p84_a d e f) (p84_b p q r)
                t p81_e0)) j)).im ^ 2 := by

  have h := p78_1_exact_speed_residual
    4 (p84_a d e f) (p84_b p q r)
    t p81_e0 hnorm

  change
    4 * p ^ 2 * p84_4c1_V p q r d e f t -
      (p84_4c2_J p q r d e f t) ^ 2 = _

  rw [hvariance, hspeed, ← henergy]

  convert h using 1 <;> ring

#print axioms p84_4h_physical_gram_bridge

end Lanzarini
