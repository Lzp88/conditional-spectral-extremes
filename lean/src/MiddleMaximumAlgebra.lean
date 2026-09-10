import PolynomialCircleMoment
import TiltedLogSine

/-! Exact cancellation of the middle-moment exponential normalizer in
the spectral maximum tail, at the manuscript's upper threshold. -/
noncomputable section
open scoped Real
namespace ConditionalSpectralExtremes

theorem middle_threshold_exponential (s b x C : Real) (Q : Nat)
    (hs : 0 < s) (hb : 0 < b) (hx : 0 < x) :
    Real.exp (s*((Real.log b+lambda s*Q)/s+C*Real.log x)) =
      b*logSineA s^Q*x^(s*C) := by
  have he : s*((Real.log b+lambda s*Q)/s+C*Real.log x) =
      Real.log b+(Q : Real)*lambda s+Real.log x*(s*C) := by field_simp
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log hb, Real.exp_nat_mul,
    ← logSineA_eq_exp_lambda s (by linarith), Real.rpow_def_of_pos hx]

theorem middle_maximum_tail_cancellation (s S b x C ε : Real) (Q : Nat)
    (hs : 0 < s) (hb : 0 < b) (hx : 0 < x) (hQ : 0 < Q) :
    logSineA s^Q*(1+ε)/(polynomialMomentConstant S/(b*Q)*
      Real.exp (s*((Real.log b+lambda s*Q)/s+C*Real.log x))) =
      (1+ε)*Q/polynomialMomentConstant S*x^(-s*C) := by
  rw [middle_threshold_exponential s b x C Q hs hb hx]
  have hA := logSineA_pos s (by linarith : -1 < s)
  have hc := polynomialMomentConstant_pos S
  have hQr : (Q : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ
  rw [show -s*C=-(s*C) by ring, Real.rpow_neg hx.le]
  field_simp

theorem middle_maximum_scale_bound (x K c s C Q : Real)
    (hx : 1 ≤ x) (hK : 0 ≤ K) (hc : 0 < c) (_hQ : 0 ≤ Q) (hQK : Q ≤ K*x)
    (hC : 3 ≤ s*C) : 2*Q/c*x^(-s*C) ≤ (2*K/c)*x^(-2 : Real) := by
  have hp : 0 < x := by linarith
  have he : x^(-s*C) ≤ x^(-3 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc
    _ ≤ (2*(K*x)/c)*x^(-3 : Real) :=
      mul_le_mul (div_le_div_of_nonneg_right (by linarith) hc.le) he
        (Real.rpow_nonneg hp.le _) (by positivity)
    _ = (2*K/c)*(x*x^(-3 : Real)) := by ring
    _ = (2*K/c)*x^(-2 : Real) := by
      congr 1
      calc
        x*x^(-3 : Real) = x^(1 : Real)*x^(-3 : Real) := by rw [Real.rpow_one]
        _ = x^(-2 : Real) := by rw [← Real.rpow_add hp]; norm_num

#print axioms middle_maximum_scale_bound
#print axioms middle_threshold_exponential
#print axioms middle_maximum_tail_cancellation
end ConditionalSpectralExtremes
