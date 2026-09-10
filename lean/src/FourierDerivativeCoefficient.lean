import FourierAbsoluteContinuity

/-! The actual derivative Fourier-coefficient identity used in the
manuscript's integration-by-parts proof, including frequency zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierDerivative
open FourierTail
local instance : Fact (0 < (1 : Real)) := ⟨by norm_num⟩

def circlePhiDerivativeOnCircle (z : Complex) : AddCircle (1 : Real) → Complex :=
  AddCircle.liftIoc 1 0 (circlePhiDerivative z)

theorem circlePhiDerivativeOnCircle_coe (z : Complex) {t : Real}
    (ht : t ∈ Ioc (0 : Real) 1) :
    circlePhiDerivativeOnCircle z (t : AddCircle (1 : Real))=circlePhiDerivative z t := by
  apply AddCircle.liftIoc_coe_apply
  simpa only [zero_add] using ht

theorem circlePhiDerivative_fourierCoeff (z : Complex) (hz : 0 < z.re) (j : Int) :
    fourierCoeff (circlePhiDerivativeOnCircle z) j=
      (2*(Real.pi : Complex)*Complex.I*(j : Complex))*complexCoefficient z j := by
  let f : Real → Complex := fun t => fourier (-j) (t : AddCircle (1 : Real))
  let c : Complex := -2*(Real.pi : Complex)*Complex.I*(j : Complex)
  have hf : Continuous f := (fourier (-j)).continuous.comp (AddCircle.continuous_mk' 1)
  have hfd (t : Real) : HasDerivAt f (c*f t) t := by
    simpa only [f,c,Complex.ofReal_one,div_one] using hasDerivAt_fourier_neg 1 j t
  have hgd (t : Real) (ht : t ∈ Ioo (0 : Real) 1) :
      HasDerivAt (circlePhiLift z) (circlePhiDerivative z t) t :=
    (circlePhiLift_hasDerivAt z hz ht).differentiableAt.hasDerivAt
  have hg1 : circlePhiLift z 1=0 := by
    have h := circlePhiLift_periodic z 0
    simpa only [zero_add,circlePhiLift_zero z hz] using h
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := circlePhiLift z) (u' := fun t => c*f t) (v' := circlePhiDerivative z)
    (a := (0 : Real)) (b := 1) hf.continuousOn (circlePhiLift_continuous z hz).continuousOn
    (fun t _ => hfd t)
    (fun t ht => hgd t (by simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using ht))
    ((continuous_const.mul hf).intervalIntegrable 0 1) (circlePhiDerivative_intervalIntegrable z hz)
  simp only [hg1,circlePhiLift_zero z hz,mul_zero,sub_zero,zero_sub,mul_assoc,
    intervalIntegral.integral_const_mul] at hip
  rw [circlePhiDerivativeOnCircle,fourierCoeff_liftIoc_eq,fourierCoeffOn_eq_integral,
    complexCoefficient,fourierCoeff_eq_intervalIntegral (complexPhi z) j 0]
  simp only [zero_add,sub_zero,one_div_one,one_smul,smul_eq_mul]
  dsimp only [f,c,circlePhiLift] at hip
  simp only [fourier_coe_apply,zero_add,sub_zero,Complex.ofReal_one,div_one] at hip ⊢
  convert! hip using 1
  ring

#print axioms circlePhiDerivativeOnCircle_coe
#print axioms circlePhiDerivative_fourierCoeff
end ConditionalSpectralAudit.FourierDerivative
