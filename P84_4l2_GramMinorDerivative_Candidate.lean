
import P84_4l1_InitialGramMinors_Candidate

namespace Lanzarini

/-!
P84.4l.2: derivative of a physical Gram minor.

The derivative formula is obtained from
the product rule.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/-- Product-rule derivative of a 2x2 minor. -/
theorem p84_4l2_minor_hasDerivAt
    (a b c d : ℝ → ℂ)
    (t : ℝ)
    (ha : HasDerivAt a (deriv a t) t)
    (hb : HasDerivAt b (deriv b t) t)
    (hc : HasDerivAt c (deriv c t) t)
    (hd : HasDerivAt d (deriv d t) t) :
    HasDerivAt
      (fun s => a s * b s - c s * d s)
      (deriv a t * b t +
        a t * deriv b t -
        (deriv c t * d t +
          c t * deriv d t))
      t := by
  exact (ha.mul hb).sub (hc.mul hd)

/--
At a point where a and c vanish,
the derivative simplifies without
assuming any further cancellation.
-/
theorem p84_4l2_minor_derivative_at_zero
    (a b c d : ℝ → ℂ)
    (ha : HasDerivAt a (deriv a 0) 0)
    (hb : HasDerivAt b (deriv b 0) 0)
    (hc : HasDerivAt c (deriv c 0) 0)
    (hd : HasDerivAt d (deriv d 0) 0)
    (ha0 : a 0 = 0)
    (hc0 : c 0 = 0) :
    deriv
      (fun t => a t * b t - c t * d t)
      0 =
      deriv a 0 * b 0 -
        deriv c 0 * d 0 := by
  have h :=
    p84_4l2_minor_hasDerivAt
      a b c d 0 ha hb hc hd
  have hderiv := h.deriv
  rw [ha0, hc0] at hderiv
  simpa using hderiv

#print axioms p84_4l2_minor_hasDerivAt
#print axioms p84_4l2_minor_derivative_at_zero

end Lanzarini
