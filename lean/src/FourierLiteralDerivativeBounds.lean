import FourierUniformDerivativeBounds

/-! Literal endpoint exponents pmin-1 and pmin-2 from the manuscript's
Fourier proof, including pmin above one or two and linear first-derivative
dependence on the imaginary marker. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierDerivative
open FourierTail

def endpointPowerConstant (r : Real) : Real := 1+Real.pi^|r|

theorem endpointPowerConstant_ge_one (r : Real) : 1 ≤ endpointPowerConstant r := by
  unfold endpointPowerConstant
  exact le_add_of_nonneg_right (Real.rpow_nonneg Real.pi_pos.le _)

theorem sine_rpow_le_left_literal {t r p : Real} (ht : 0 < t) (ht2 : t ≤ 1/2)
    (hrp : r ≤ p) :
    Real.sin (Real.pi*t)^p ≤ endpointPowerConstant r*t^r := by
  have hti : t ∈ Ioo (0:Real) 1 := ⟨ht,by linarith⟩
  have hs := Real.rpow_le_rpow_of_exponent_ge (sine_pos_interior hti) (Real.sin_le_one _) hrp
  have htP : 0 ≤ t^r := Real.rpow_nonneg ht.le _
  by_cases hr : r ≤ 0
  · exact hs.trans ((Real.rpow_le_rpow_of_nonpos ht (sine_ge_left_distance ht ht2) hr).trans
      (by nlinarith [endpointPowerConstant_ge_one r]))
  · have hr0 : 0 ≤ r := le_of_not_ge hr
    have hsin := Real.sin_le (show 0 ≤ Real.pi*t by positivity)
    have hm := Real.rpow_le_rpow (sine_pos_interior hti).le hsin hr0
    rw [Real.mul_rpow Real.pi_pos.le ht.le] at hm
    have hpC : Real.pi^r ≤ endpointPowerConstant r := by
      unfold endpointPowerConstant
      rw [abs_of_nonneg hr0]
      linarith
    exact hs.trans (hm.trans (mul_le_mul_of_nonneg_right hpC htP))

theorem uniform_first_derivative_scalar_linear {z : Complex} {P : Real}
    (hz : 0 ≤ z.re) (hP : z.re ≤ P) :
    (2:Real)^z.re*‖z‖*Real.pi ≤ ((2:Real)^P*(P+2)*Real.pi)*(1+|z.im|) := by
  have hP0 : 0 ≤ P := hz.trans hP
  have hn : ‖z‖ ≤ P+|z.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz] at hh
    linarith
  have hU : ‖z‖ ≤ (P+2)*(1+|z.im|) := by nlinarith [abs_nonneg z.im]
  have hpow : (2:Real)^z.re ≤ (2:Real)^P :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hP
  calc
    _ ≤ (2:Real)^P*((P+2)*(1+|z.im|))*Real.pi := by gcongr
    _ = _ := by ring

theorem first_derivative_literal_left {pmin P : Real} (hp : 0 < pmin)
    (z : Complex) (hzp : pmin ≤ z.re) (hzP : z.re ≤ P)
    {t : Real} (ht : 0 < t) (ht2 : t ≤ 1/2) :
    ‖circlePhiDerivative z t‖ ≤
      ((2:Real)^P*(P+2)*Real.pi*endpointPowerConstant (pmin-1))*(1+|z.im|)*t^(pmin-1) := by
  have hz : 0 < z.re := hp.trans_le hzp
  have hti : t ∈ Ioo (0:Real) 1 := ⟨ht,by linarith⟩
  have hs := sine_rpow_le_left_literal ht ht2 (show pmin-1 ≤ z.re-1 by linarith)
  have hc := Real.abs_cos_le_one (Real.pi*t)
  have hscalar := uniform_first_derivative_scalar_linear hz.le hzP
  have hB : 0 ≤ endpointPowerConstant (pmin-1)*t^(pmin-1) :=
    mul_nonneg (le_trans zero_le_one (endpointPowerConstant_ge_one _)) (Real.rpow_nonneg ht.le _)
  calc
    ‖circlePhiDerivative z t‖ = ((2:Real)^z.re*‖z‖*Real.pi)*
      Real.sin (Real.pi*t)^(z.re-1)*|Real.cos (Real.pi*t)| := by
        rw [circlePhiDerivative_norm z hz hti]
        ring
    _ ≤ ((2:Real)^z.re*‖z‖*Real.pi)*Real.sin (Real.pi*t)^(z.re-1) := by
      have hh := Real.rpow_nonneg (sine_pos_interior hti).le (z.re-1)
      nlinarith [mul_nonneg (show 0 ≤ (2:Real)^z.re*‖z‖*Real.pi by positivity) hh]
    _ ≤ ((2:Real)^z.re*‖z‖*Real.pi)*(endpointPowerConstant (pmin-1)*t^(pmin-1)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (((2:Real)^P*(P+2)*Real.pi)*(1+|z.im|))*(endpointPowerConstant (pmin-1)*t^(pmin-1)) :=
      mul_le_mul_of_nonneg_right hscalar hB
    _ = _ := by ring

theorem second_derivative_literal_left {pmin P : Real} (hp : 0 < pmin)
    (z : Complex) (hzp : pmin ≤ z.re) (hzP : z.re ≤ P)
    {t : Real} (ht : 0 < t) (ht2 : t ≤ 1/2) :
    ‖circlePhiSecondExpression z t‖ ≤
      ((2:Real)^P*(P+2)^2*Real.pi^2*endpointPowerConstant (pmin-2))*
        (1+|z.im|)^2*(t^(pmin-2)+1) := by
  have hz : 0 < z.re := hp.trans_le hzp
  have hti : t ∈ Ioo (0:Real) 1 := ⟨ht,by linarith⟩
  have hs := sine_rpow_le_left_literal ht ht2 (show pmin-2 ≤ z.re-2 by linarith)
  have hs0 := Real.rpow_le_one (sine_pos_interior hti).le (Real.sin_le_one _) hz.le
  have hC := endpointPowerConstant_ge_one (pmin-2)
  have htp : 0 ≤ t^(pmin-2) := Real.rpow_nonneg ht.le _
  have hA : 0 ≤ (2:Real)^z.re*‖z‖*Real.pi^2 := by positivity
  have hi : ‖z-1‖*(endpointPowerConstant (pmin-2)*t^(pmin-2))+1 ≤
      (‖z-1‖+1)*endpointPowerConstant (pmin-2)*(t^(pmin-2)+1) := by
    nlinarith [norm_nonneg (z-1),
      mul_nonneg (le_trans zero_le_one hC) htp,
      mul_nonneg (le_trans zero_le_one hC) (norm_nonneg (z-1))]
  have hB : 0 ≤ endpointPowerConstant (pmin-2)*(t^(pmin-2)+1) := by positivity
  calc
    ‖circlePhiSecondExpression z t‖ ≤ (2:Real)^z.re*‖z‖*Real.pi^2*
      (‖z-1‖*Real.sin (Real.pi*t)^(z.re-2)+Real.sin (Real.pi*t)^z.re) :=
        circlePhiSecondExpression_norm_le z hti
    _ ≤ (2:Real)^z.re*‖z‖*Real.pi^2*(‖z-1‖*(endpointPowerConstant (pmin-2)*t^(pmin-2))+1) := by
      gcongr
    _ ≤ (2:Real)^z.re*‖z‖*Real.pi^2*((‖z-1‖+1)*endpointPowerConstant (pmin-2)*(t^(pmin-2)+1)) :=
      mul_le_mul_of_nonneg_left hi hA
    _ = ((2:Real)^z.re*‖z‖*Real.pi^2*(‖z-1‖+1))*(endpointPowerConstant (pmin-2)*(t^(pmin-2)+1)) := by ring
    _ ≤ (((2:Real)^P*(P+2)^2*Real.pi^2)*(1+|z.im|)^2)*
      (endpointPowerConstant (pmin-2)*(t^(pmin-2)+1)) :=
        mul_le_mul_of_nonneg_right (uniform_scalar_derivative_factors hz.le hzP).2 hB
    _ = _ := by ring

theorem actual_uniform_literal_derivative_bounds (pmin P : Real) (hp : 0 < pmin) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      ∀ t : Real, 0 < t → t ≤ 1/2 →
        ‖circlePhiDerivative z t‖ ≤ C*(1+|z.im|)*t^(pmin-1) ∧
        ‖circlePhiSecondExpression z t‖ ≤ C*(1+|z.im|)^2*(t^(pmin-2)+1) := by
  let C1 := (2:Real)^P*(P+2)*Real.pi*endpointPowerConstant (pmin-1)
  let C2 := (2:Real)^P*(P+2)^2*Real.pi^2*endpointPowerConstant (pmin-2)
  have hP : 0 < P := hp.trans_le hpP
  have hC1 : 0 ≤ C1 := by dsimp [C1,endpointPowerConstant]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2,endpointPowerConstant]; positivity
  refine ⟨C1+C2+1,by positivity,?_⟩
  intro z hzp hzP t ht ht2
  constructor
  · apply (first_derivative_literal_left hp z hzp hzP ht ht2).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact mul_le_mul_of_nonneg_right (by dsimp [C1]; linarith) (by positivity)
  · apply (second_derivative_literal_left hp z hzp hzP ht ht2).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by dsimp [C2]; linarith) (sq_nonneg _)

theorem circlePhiDerivative_norm_reflection (z : Complex) (hz : 0 < z.re)
    {t : Real} (ht : t ∈ Ioo (0:Real) 1) :
    ‖circlePhiDerivative z (1-t)‖=‖circlePhiDerivative z t‖ := by
  rw [circlePhiDerivative_norm z hz (show 1-t ∈ Ioo (0:Real) 1 by constructor <;> linarith [ht.1,ht.2]),
    circlePhiDerivative_norm z hz ht]
  simp only [show Real.pi*(1-t)=Real.pi-Real.pi*t by ring, Real.sin_pi_sub,
    Real.cos_pi_sub, abs_neg]

theorem circlePhiSecondExpression_reflection (z : Complex) (t : Real) :
    circlePhiSecondExpression z (1-t)=circlePhiSecondExpression z t := by
  simp only [circlePhiSecondExpression,show Real.pi*(1-t)=Real.pi-Real.pi*t by ring,
    Real.sin_pi_sub,Real.cos_pi_sub,Complex.ofReal_neg,neg_sq]

theorem actual_uniform_literal_derivative_bounds_two_sides (pmin P : Real)
    (hp : 0 < pmin) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      (∀ t : Real, 0 < t → t ≤ 1/2 →
        ‖circlePhiDerivative z t‖ ≤ C*(1+|z.im|)*t^(pmin-1) ∧
        ‖circlePhiSecondExpression z t‖ ≤ C*(1+|z.im|)^2*(t^(pmin-2)+1)) ∧
      (∀ t : Real, 1/2 ≤ t → t < 1 →
        ‖circlePhiDerivative z t‖ ≤ C*(1+|z.im|)*(1-t)^(pmin-1) ∧
        ‖circlePhiSecondExpression z t‖ ≤ C*(1+|z.im|)^2*((1-t)^(pmin-2)+1)) := by
  obtain ⟨C,hC,h⟩ := actual_uniform_literal_derivative_bounds pmin P hp hpP
  refine ⟨C,hC,?_⟩
  intro z hzp hzP
  refine ⟨h z hzp hzP,?_⟩
  intro t ht2 ht1
  have hh := h z hzp hzP (1-t) (by linarith) (by linarith)
  rw [circlePhiDerivative_norm_reflection z (hp.trans_le hzp)
    (show t ∈ Ioo (0:Real) 1 from ⟨by linarith,ht1⟩),
    circlePhiSecondExpression_reflection] at hh
  exact hh

#print axioms sine_rpow_le_left_literal
#print axioms first_derivative_literal_left
#print axioms second_derivative_literal_left
#print axioms actual_uniform_literal_derivative_bounds
#print axioms circlePhiDerivative_norm_reflection
#print axioms circlePhiSecondExpression_reflection
#print axioms actual_uniform_literal_derivative_bounds_two_sides
end ConditionalSpectralAudit.FourierDerivative
