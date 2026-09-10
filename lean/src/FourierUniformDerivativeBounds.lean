import FourierDerivativeBounds

/-! Uniform endpoint envelopes for the actual complex kernel derivatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace ConditionalSpectralAudit.FourierDerivative
open FourierTail

theorem first_derivative_endpoint (z : Complex) (hz : 0 < z.re)
    {α t : Real} (ha1 : α ≤ 1) (haz : α ≤ z.re) (ht : t ∈ Ioo (0:Real) 1) :
    ‖circlePhiDerivative z t‖ ≤
      ((2 : Real)^z.re*‖z‖*Real.pi)*(t^(α-1)+(1-t)^(α-1)) := by
  have hs := sine_rpow_le_endpoint_powers ht
    (show α-1≤0 by linarith) (show α-1≤z.re-1 by linarith)
  have hc := Real.abs_cos_le_one (Real.pi*t)
  have hp := Real.rpow_nonneg (sine_pos_interior ht).le (z.re-1)
  calc
    ‖circlePhiDerivative z t‖=
      ((2 : Real)^z.re*‖z‖*Real.pi)*Real.sin (Real.pi*t)^(z.re-1)*
        |Real.cos (Real.pi*t)| := by rw [circlePhiDerivative_norm z hz ht]; ring
    _ ≤ ((2 : Real)^z.re*‖z‖*Real.pi)*Real.sin (Real.pi*t)^(z.re-1)*1 := by
      gcongr
    _ ≤ _ := by rw [mul_one]; gcongr

theorem second_derivative_endpoint (z : Complex)
    {α t : Real} (ha1 : α ≤ 1) (haz : α ≤ z.re) (ht : t ∈ Ioo (0:Real) 1) :
    ‖circlePhiSecondExpression z t‖ ≤
      ((2 : Real)^z.re*‖z‖*Real.pi^2*(‖z-1‖+1))*(t^(α-2)+(1-t)^(α-2)) := by
  have hs1 := sine_rpow_le_endpoint_powers ht
    (show α-2≤0 by linarith) (show α-2≤z.re-2 by linarith)
  have hs2 := sine_rpow_le_endpoint_powers ht
    (show α-2≤0 by linarith) (show α-2≤z.re by linarith)
  calc
    ‖circlePhiSecondExpression z t‖ ≤
      (2 : Real)^z.re*‖z‖*Real.pi^2*
        (‖z-1‖*Real.sin (Real.pi*t)^(z.re-2)+Real.sin (Real.pi*t)^z.re) :=
      circlePhiSecondExpression_norm_le z ht
    _ ≤ (2 : Real)^z.re*‖z‖*Real.pi^2*
        (‖z-1‖*(t^(α-2)+(1-t)^(α-2))+(t^(α-2)+(1-t)^(α-2))) := by gcongr
    _ = _ := by ring

theorem uniform_scalar_derivative_factors {z : Complex} {P : Real}
    (hz : 0 ≤ z.re) (hP : z.re ≤ P) :
    (2 : Real)^z.re*‖z‖*Real.pi ≤
      ((2 : Real)^P*(P+2)*Real.pi)*(1+|z.im|)^2 ∧
    (2 : Real)^z.re*‖z‖*Real.pi^2*(‖z-1‖+1) ≤
      ((2 : Real)^P*(P+2)^2*Real.pi^2)*(1+|z.im|)^2 := by
  have hP0 : 0 ≤ P := hz.trans hP
  have hn : ‖z‖ ≤ P+|z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_nonneg hz]
    linarith
  have hn1 : ‖z-1‖+1 ≤ P+|z.im|+2 := by
    have h := norm_sub_le z (1 : Complex)
    rw [norm_one] at h
    linarith
  have hU : ‖z‖ ≤ (P+2)*(1+|z.im|) := by nlinarith [abs_nonneg z.im]
  have hU1 : ‖z-1‖+1 ≤ (P+2)*(1+|z.im|) := by nlinarith [abs_nonneg z.im]
  have hpow : (2 : Real)^z.re ≤ (2 : Real)^P :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hP
  constructor
  · calc
      _ ≤ (2 : Real)^P*((P+2)*(1+|z.im|))*Real.pi := by gcongr
      _ ≤ ((2 : Real)^P*(P+2)*Real.pi)*(1+|z.im|)^2 := by
        have hu : 1+|z.im| ≤ (1+|z.im|)^2 := by nlinarith [abs_nonneg z.im]
        have hp : 0 ≤ (2 : Real)^P*(P+2)*Real.pi := by positivity
        nlinarith
  · calc
      _ ≤ (2 : Real)^P*((P+2)*(1+|z.im|))*Real.pi^2*((P+2)*(1+|z.im|)) := by gcongr
      _ = _ := by ring

theorem actual_uniform_derivative_endpoint_bounds (pmin P α : Real)
    (hpa : 0 < α) (hap : α < pmin) (ha1 : α < 1) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      ∀ t ∈ Ioo (0 : Real) 1,
        ‖circlePhiDerivative z t‖ ≤
          C*(1+|z.im|)^2*(t^(α-1)+(1-t)^(α-1)) ∧
        ‖circlePhiSecondExpression z t‖ ≤
          C*(1+|z.im|)^2*(t^(α-2)+(1-t)^(α-2)) := by
  let C1 := (2 : Real)^P*(P+2)*Real.pi
  let C2 := (2 : Real)^P*(P+2)^2*Real.pi^2
  have hP : 0 < P := (hpa.trans hap).trans_le hpP
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  refine ⟨C1+C2+1,by positivity,?_⟩
  intro z hzp hzP t ht
  have hz : 0 < z.re := (hpa.trans hap).trans_le hzp
  have hb := uniform_scalar_derivative_factors hz.le hzP
  constructor
  · apply (first_derivative_endpoint z hz ha1.le (hap.le.trans hzp) ht).trans
    have hs : 0 ≤ t^(α-1)+(1-t)^(α-1) :=
      add_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _)
    apply mul_le_mul_of_nonneg_right _ hs
    exact hb.1.trans (mul_le_mul_of_nonneg_right (by dsimp [C1]; linarith) (sq_nonneg _))
  · apply (second_derivative_endpoint z ha1.le (hap.le.trans hzp) ht).trans
    have hs : 0 ≤ t^(α-2)+(1-t)^(α-2) :=
      add_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (by linarith [ht.2]) _)
    apply mul_le_mul_of_nonneg_right _ hs
    exact hb.2.trans (mul_le_mul_of_nonneg_right (by dsimp [C2]; linarith) (sq_nonneg _))

#print axioms first_derivative_endpoint
#print axioms second_derivative_endpoint
#print axioms uniform_scalar_derivative_factors
#print axioms actual_uniform_derivative_endpoint_bounds
end ConditionalSpectralAudit.FourierDerivative
