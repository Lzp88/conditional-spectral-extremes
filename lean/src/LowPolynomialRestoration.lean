import CycleLogFields
import LowGoodSet

/-! Deterministic recovery of the low factors in the actual polynomial.
The lower estimate uses an actual non-root angle in the low good set. -/
noncomputable section
open MeasureTheory Set Polynomial
open scoped Real BigOperators
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.ArithmeticArcs ConditionalSpectralAudit.FourierHarmonic

theorem lowCyclePolynomial_boundary_upper {q : Nat} (j : Fin q → Nat) (z : Complex) (hz : ‖z‖=1) :
    ‖(lowCyclePolynomial j).eval z‖ ≤ (2 : Real)^q := by
  unfold lowCyclePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, norm_prod]
  have hf (v : Fin q) : ‖(1 : Complex)-z^(j v)‖ ≤ (2 : Real) :=
    (norm_sub_le (1 : Complex) (z^(j v))).trans (by norm_num [norm_pow, hz])
  have hh := Finset.prod_le_prod (s := Finset.univ) (fun (v : Fin q) _ => norm_nonneg ((1 : Complex)-z^(j v)))
    (fun (v : Fin q) _ => hf v)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh

theorem low_polynomial_restoration_upper {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v)
    (P : Polynomial Complex) (hP : P ≠ 0) :
    Real.log (circleNorm (lowCyclePolynomial j*P)) ≤ Real.log (circleNorm P)+(q : Real)*Real.log 2 := by
  have hprod : circleNorm (lowCyclePolynomial j*P) ≤ (2 : Real)^q*circleNorm P := by
    apply circleNorm_le
    intro z hz
    rw [Polynomial.eval_mul, norm_mul]
    exact mul_le_mul (lowCyclePolynomial_boundary_upper j z hz) (norm_eval_le_circleNorm P z hz)
      (norm_nonneg _) (by positivity)
  have hp := circleNorm_pos (lowCyclePolynomial j*P) (mul_ne_zero (lowCyclePolynomial_ne_zero j hj) hP)
  have hPn := circleNorm_pos P hP
  have hh := Real.log_le_log hp hprod
  rw [Real.log_mul (by positivity) hPn.ne', Real.log_pow] at hh
  linarith

theorem low_polynomial_restoration_lower {q : Nat} (j : Fin q → Nat) (_hj : ∀ v, 0 < j v)
    (P : Polynomial Complex) (_hP : P ≠ 0) (u H : Real) (t : Torus)
    (ht : ∀ v, j v • t ≠ 0) (hgood : t ∈ lowGoodSet j u)
    (hPt : P.eval (fourier 1 t) ≠ 0) (hheight : H ≤ Real.log ‖P.eval (fourier 1 t)‖) :
    H-u ≤ Real.log (circleNorm (lowCyclePolynomial j*P)) := by
  have hl := lowCyclePolynomial_eval_nonzero j t ht
  have hnorm : 0 < ‖(lowCyclePolynomial j*P).eval (fourier 1 t)‖ := by
    rw [Polynomial.eval_mul, norm_mul]
    exact mul_pos (norm_pos_iff.mpr hl) (norm_pos_iff.mpr hPt)
  have hle := Real.log_le_log hnorm (norm_eval_le_circleNorm (lowCyclePolynomial j*P) (fourier 1 t) (by
    exact Circle.norm_coe _))
  rw [Polynomial.eval_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hl) (norm_ne_zero_iff.mpr hPt),
    lowCyclePolynomial_log_eval j t ht] at hle
  change -u ≤ lowLogSineField j t at hgood
  linarith

#print axioms low_polynomial_restoration_upper
#print axioms low_polynomial_restoration_lower
end ConditionalSpectralExtremes
