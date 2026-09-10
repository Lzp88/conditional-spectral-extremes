import Mathlib

/-!
Exact deterministic identities and inequalities from Section 5.2 of
the paper.

This file proves the algebra actually used by the argument. It does NOT
prove Fourier inversion, smoothing/total variation, the constrained-kernel
mass estimate, either probabilistic moment estimate, or the main theorem.
No analytic or probabilistic lemma is introduced as an axiom.
-/

namespace ConditionalSpectralAudit.MomentAlgebra

/-- Source lines 1010-1011, using the specified terminal level y. -/
theorem terminal_tilt_cancellation (a r lam Q s : Real) (hs : s ≠ 0) :
    -s * ((a - r + lam * Q) / s) + lam * Q = -a + r := by
  field_simp [hs]
  ring

/-- The exact first-moment normalizing exponential. -/
theorem mu_identity (a r lam Q s : Real) (hs : s ≠ 0) :
    Real.exp (-s * ((a - r + lam * Q) / s) + lam * Q) =
      Real.exp (-a + r) := by
  rw [terminal_tilt_cancellation a r lam Q s hs]

/-- Source lines 998-1002: inverse height tilt times noise weight. -/
theorem inverse_tilt_noise_weight (s X U y : Real) :
    Real.exp (-s * X) * Real.exp (-s * U) =
      Real.exp (-s * y) * Real.exp (-s * (X + U - y)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The terminal test function to which TV is applied is at most one. -/
theorem terminal_weight_le_one (s W y : Real) (hs : 0 ≤ s) (hW : y ≤ W) :
    Real.exp (-s * (W - y)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith

/-- Its lower bound on the width-one terminal window. -/
theorem terminal_weight_lower (s W y : Real) (hs : 0 ≤ s) (hW : W ≤ y + 1) :
    Real.exp (-s) ≤ Real.exp (-s * (W - y)) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Source lines 1051-1063: the exact second-moment exponent cancellation,
    stated with precisely the frontier/barrier identity used there. -/
theorem near_exponent_cancellation
    (s y B lam S Q a G : Real)
    (hB : s * B = a + lam * S - s * G) :
    (-2 * s * y + s * B + lam * S + 2 * lam * (Q - S)) -
        2 * (-s * y + lam * Q) = a - s * G := by
  rw [hB]
  ring

/-- Same identity, with the actual formula B=(a+lambda*S)/s-G. -/
theorem near_exponent_from_frontier
    (s y lam S Q a G : Real) (hs : s ≠ 0) :
    (-2 * s * y + s * ((a + lam * S) / s - G) +
      lam * S + 2 * lam * (Q - S)) -
        2 * (-s * y + lam * Q) = a - s * G := by
  apply near_exponent_cancellation
  field_simp [hs]

/-- Source lines 1065-1069: the arithmetic area cancels the a_k scale. -/
theorem near_area_exponent (a aPrev Delta : Real) :
    Real.exp a * Real.exp (-aPrev + Delta) =
      Real.exp (a - aPrev + Delta) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- An exact finite inequality underlying source line 1006.
    The lower bound on p is explicit, not asserted without proof. -/
theorem relative_error_bound
    (m L J C p : Real) (hL : 0 < L)
    (hmL : m ≤ L) (hp : L ^ (-C) ≤ p) :
    m * L ^ (-J) / p ^ 2 ≤ L ^ (1 - J + 2 * C) := by
  have hlower : 0 < L ^ (-C) := Real.rpow_pos_of_pos hL _
  have hp0 : 0 < p := lt_of_lt_of_le hlower hp
  calc
    m * L ^ (-J) / p ^ 2 ≤ L * L ^ (-J) / (L ^ (-C)) ^ 2 := by
      gcongr
    _ = L ^ ((1 + -J) - (-C * 2)) := by
      rw [Real.rpow_sub hL, Real.rpow_add hL, Real.rpow_one,
        Real.rpow_mul hL.le, Real.rpow_two]
    _ = L ^ (1 - J + 2 * C) := by
      congr 1
      ring

/-- The selected J leaves more than eleven negative powers of L. -/
theorem relative_error_exponent (J C : Real) (hJ : 2 * C + 12 < J) :
    1 - J + 2 * C < -11 := by
  linarith

/-- Source lines 967 and 1069, including the class-count loss L. -/
theorem near_sum_exponent
    (sMin g u2 u3 A0 C : Real)
    (hg : 2 * u2 + u3 + A0 + 2 * C + 12 < sMin * g) :
    1 + 2 * u2 + u3 + A0 - sMin * g + 2 * C < -11 := by
  linarith

/-- Source lines 852-853, worst-case d=2 Fourier tail integration. -/
theorem smoothing_outer_exponent
    (d u1 J : Real) (hd : d ≤ 2) (hu1 : J + 160 < 9 * u1) :
    10 * d + 90 - 9 * u1 < -J - 50 := by
  linarith

/-- Source lines 851 and 855, including a conservative q≤L loss. -/
theorem smoothing_inner_exponent
    (alpha u2 u1 J : Real)
    (hu2 : 6 * u1 + J + 30 < alpha * u2) :
    6 * u1 - alpha * u2 + 1 < -J - 29 := by
  linarith

/-- Source lines 951-954: the prefactor outside the geometric sum. -/
theorem integrated_bad_arc_exponent
    (u2 u3 rStar rho A0 : Real) (hA0 : 0 ≤ A0) (hrho : rho ≤ 1)
    (hr : u2 + u3 + A0 + 2 < rStar) :
    u2 + u3 - rStar + rho * A0 < -2 := by
  nlinarith

/-- Source line 1108: a sufficient upper-tail exponent choice. -/
theorem upper_tail_exponent (sMin C1 : Real) (hC1 : 1 < sMin * C1) :
    1 - sMin * C1 < 0 := by
  linarith

#print axioms terminal_tilt_cancellation
#print axioms mu_identity
#print axioms inverse_tilt_noise_weight
#print axioms terminal_weight_le_one
#print axioms terminal_weight_lower
#print axioms near_exponent_cancellation
#print axioms near_exponent_from_frontier
#print axioms near_area_exponent
#print axioms relative_error_bound
#print axioms relative_error_exponent
#print axioms near_sum_exponent
#print axioms smoothing_outer_exponent
#print axioms smoothing_inner_exponent
#print axioms integrated_bad_arc_exponent
#print axioms upper_tail_exponent

end ConditionalSpectralAudit.MomentAlgebra
