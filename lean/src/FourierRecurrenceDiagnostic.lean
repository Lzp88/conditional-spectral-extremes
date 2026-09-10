import Mathlib

/-!
A local diagnostic for the displayed quotient recurrence in source lines
750-753 of the paper.

The coefficient sequence below is the elementary sequence of
2 - 2*cos(2*pi*t). The file also proves its actual normalized-Haar Fourier
representation for the squared norm |1-e(t)|^2 on R/Z. It does NOT prove
the manuscript's general Gamma coefficient formula or uniform Fourier tail.

Lean totalizes division: 0/0=0. The failed quotient identity below is
therefore a formal inequality between totalized expressions. In ordinary
mathematics the left side is undefined. The denominator-free recurrence
has neither defect and does determine a sequence when s>0.
-/

namespace ConditionalSpectralAudit.FourierRecurrenceDiagnostic

open MeasureTheory

local instance : Fact (0 < (1 : Real)) := ⟨by norm_num⟩

def phiTwoCoefficients (j : Int) : Real :=
  if j = 0 then 2 else if j = 1 ∨ j = -1 then -1 else 0

theorem zero_coefficients_at_two_and_three :
    phiTwoCoefficients 2 = 0 ∧ phiTwoCoefficients 3 = 0 := by
  norm_num [phiTwoCoefficients]

/-- The manuscript's RHS at s=2, j=3 is exactly 1/4. -/
theorem quotient_rhs_at_two_three :
    -(1 + (2 : Real) / 2 - 3) / ((2 : Real) / 2 + 3) = 1 / 4 := by
  norm_num

/-- Thus even Lean's totalized division does not validate the displayed
    unrestricted quotient formula at s=2, j=3. -/
theorem quotient_recurrence_fails_at_two_three :
    phiTwoCoefficients 3 / phiTwoCoefficients 2 ≠
      -(1 + (2 : Real) / 2 - 3) / ((2 : Real) / 2 + 3) := by
  norm_num [phiTwoCoefficients]

/-- The correct recurrence, retaining every zero coefficient, for j>=1. -/
theorem phiTwo_denominator_free_recurrence (j : Int) (hj : 1 ≤ j) :
    ((2 : Real) / 2 + (j : Real)) * phiTwoCoefficients j =
      -(1 + (2 : Real) / 2 - (j : Real)) * phiTwoCoefficients (j - 1) := by
  by_cases hj1 : j = 1
  · subst j
    norm_num [phiTwoCoefficients]
  by_cases hj2 : j = 2
  · subst j
    norm_num [phiTwoCoefficients]
  have hj0 : j ≠ 0 := by omega
  have hjm1 : j ≠ -1 := by omega
  have hp0 : j - 1 ≠ 0 := by omega
  have hp1 : j - 1 ≠ 1 := by omega
  have hpm1 : j - 1 ≠ -1 := by omega
  simp [phiTwoCoefficients, hj0, hj1, hjm1, hp0, hp1, hpm1]

/-- Taking quotients is valid only after supplying the missing nonzero
    previous-coefficient hypothesis, along with a nonzero multiplier. -/
theorem quotient_from_denominator_free
    (s j current previous : Real)
    (hden : s / 2 + j ≠ 0) (hprev : previous ≠ 0)
    (hrec : (s / 2 + j) * current = -(1 + s / 2 - j) * previous) :
    current / previous = -(1 + s / 2 - j) / (s / 2 + j) := by
  apply (div_eq_div_iff hprev hden).2
  nlinarith [hrec]

/-- The safe recurrence determines the entire nonnegative-index sequence
    from its zero coefficient, including cases with later zero values. -/
theorem denominator_free_uniqueness
    (s : Real) (hs : 0 < s) (c d : Nat → Real) (hzero : c 0 = d 0)
    (hc : ∀ n : Nat,
      (s / 2 + ((n + 1 : Nat) : Real)) * c (n + 1) =
        -(1 + s / 2 - ((n + 1 : Nat) : Real)) * c n)
    (hd : ∀ n : Nat,
      (s / 2 + ((n + 1 : Nat) : Real)) * d (n + 1) =
        -(1 + s / 2 - ((n + 1 : Nat) : Real)) * d n) :
    ∀ n : Nat, c n = d n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      have hden : s / 2 + ((n + 1 : Nat) : Real) ≠ 0 := by positivity
      apply mul_left_cancel₀ hden
      rw [hc n, hd n, ih]

/-- The actual squared log-sine base on the circle R/Z, embedded in C.
    Its Fourier coefficients below use mathlib's normalized Haar integral. -/
noncomputable def phiTwoOnCircle (t : AddCircle (1 : Real)) : Complex :=
  ((‖(1 : Complex) - fourier 1 t‖ ^ 2 : Real) : Complex)

/-- This function is exactly the manuscript's |1-exp(2*pi*i*t)|^2. -/
theorem phiTwoOnCircle_real (t : Real) :
    phiTwoOnCircle (t : AddCircle (1 : Real)) =
      ((‖(1 : Complex) - Complex.exp ((2 * Real.pi * t : Real) * Complex.I)‖ ^ 2 : Real) : Complex) := by
  have he : fourier 1 (t : AddCircle (1 : Real)) =
      Complex.exp ((2 * Real.pi * t : Real) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [phiTwoOnCircle, he]

/-- Exact three-term Fourier-polynomial expansion, including at roots. -/
theorem phiTwoOnCircle_expansion (t : AddCircle (1 : Real)) :
    phiTwoOnCircle t =
      2 * fourier 0 t + (-1) * fourier 1 t + (-1) * fourier (-1) t := by
  have hz : starRingEnd Complex (fourier 1 t) * fourier 1 t = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.normSq_eq_norm_sq, fourier_apply, Circle.norm_coe,
      one_pow, Complex.ofReal_one]
  unfold phiTwoOnCircle
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [map_sub, map_one, fourier_neg, fourier_zero, mul_one]
  linear_combination hz

theorem scaled_fourier_integrable (c : Complex) (j : Int) :
    Integrable (fun t : AddCircle (1 : Real) => c * fourier j t)
      AddCircle.haarAddCircle := by
  apply (continuous_const.mul (fourier j).continuous).integrable_of_hasCompactSupport
  exact HasCompactSupport.of_compactSpace _

/-- Genuine Fourier-integral identity at s=2; the sequence is no longer
    merely assumed to be the coefficient sequence. -/
theorem phiTwo_actual_fourier_coefficients (j : Int) :
    fourierCoeff phiTwoOnCircle j = (phiTwoCoefficients j : Complex) := by
  have h0 := scaled_fourier_integrable 2 0
  have h1 := scaled_fourier_integrable (-1) 1
  have hm1 := scaled_fourier_integrable (-1) (-1)
  have hexp : phiTwoOnCircle =
      (fun t : AddCircle (1 : Real) => (2 : Complex) * fourier 0 t) +
      (fun t : AddCircle (1 : Real) => (-1 : Complex) * fourier 1 t) +
      (fun t : AddCircle (1 : Real) => (-1 : Complex) * fourier (-1) t) := by
    funext t
    exact phiTwoOnCircle_expansion t
  rw [hexp, fourierCoeff.add (h0.add h1) hm1, fourierCoeff.add h0 h1]
  simp only [Pi.add_apply]
  rw [fourierCoeff.const_mul, fourierCoeff.const_mul, fourierCoeff.const_mul,
    fourierCoeff_fourier 0, fourierCoeff_fourier 1, fourierCoeff_fourier (-1)]
  by_cases hj0 : j = 0
  · subst j
    norm_num [phiTwoCoefficients]
  by_cases hj1 : j = 1
  · subst j
    norm_num [phiTwoCoefficients]
  by_cases hjm1 : j = -1
  · subst j
    norm_num [phiTwoCoefficients]
  simp [phiTwoCoefficients, hj0, hj1, hjm1]

/-- The same result with the normalized Haar integral written explicitly. -/
theorem phiTwo_actual_fourier_integral (j : Int) :
    (∫ t : AddCircle (1 : Real), fourier (-j) t * phiTwoOnCircle t
      ∂AddCircle.haarAddCircle) = (phiTwoCoefficients j : Complex) := by
  simpa only [fourierCoeff, smul_eq_mul] using phiTwo_actual_fourier_coefficients j

/-- The minimally corrected manuscript recurrence, with the actual
    Fourier integrals, in the diagnostic case s=2. -/
theorem phiTwo_actual_denominator_free_recurrence (j : Int) (hj : 1 ≤ j) :
    ((2 : Complex) / 2 + (j : Complex)) * fourierCoeff phiTwoOnCircle j =
      -(1 + (2 : Complex) / 2 - (j : Complex)) *
        fourierCoeff phiTwoOnCircle (j - 1) := by
  rw [phiTwo_actual_fourier_coefficients, phiTwo_actual_fourier_coefficients]
  have h := congrArg (fun x : Real => (x : Complex))
    (phiTwo_denominator_free_recurrence j hj)
  push_cast at h
  exact h

/-- The local failure with the actual Fourier coefficients, rather than
    only an independently specified finite-support sequence. -/
theorem actual_fourier_quotient_failure :
    fourierCoeff phiTwoOnCircle 3 / fourierCoeff phiTwoOnCircle 2 ≠
      (1 / 4 : Complex) := by
  rw [phiTwo_actual_fourier_coefficients, phiTwo_actual_fourier_coefficients]
  norm_num [phiTwoCoefficients]

#print axioms zero_coefficients_at_two_and_three
#print axioms quotient_rhs_at_two_three
#print axioms quotient_recurrence_fails_at_two_three
#print axioms phiTwo_denominator_free_recurrence
#print axioms quotient_from_denominator_free
#print axioms denominator_free_uniqueness
#print axioms phiTwoOnCircle_real
#print axioms phiTwoOnCircle_expansion
#print axioms scaled_fourier_integrable
#print axioms phiTwo_actual_fourier_coefficients
#print axioms phiTwo_actual_fourier_integral
#print axioms phiTwo_actual_denominator_free_recurrence
#print axioms actual_fourier_quotient_failure

end ConditionalSpectralAudit.FourierRecurrenceDiagnostic
