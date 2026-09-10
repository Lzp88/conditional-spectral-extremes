import SmoothingCrudeError
import SmoothingAsymptoticTools

/-! Actual ceiling cutoff and exact power bookkeeping for the smoothing error. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace ConditionalSpectralAudit.FourierHarmonic

def smoothingKernelEnvelope (C x u₁ u₂ u₃ α : Real) : Real :=
  C*(1+x^u₁)^4*((integrationFrequencyCutoff x u₂ : Real)^(-α)+Real.exp (-(u₃*Real.log x)))

theorem smoothing_kernel_power_bound (C x u₁ u₂ u₃ α : Real)
    (hC : 0 ≤ C) (hx : 1 ≤ x) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hα : 0 ≤ α) :
    smoothingKernelEnvelope C x u₁ u₂ u₃ α ≤
      16*C*(x^(4*u₁-u₂*α)+x^(4*u₁-u₃)) := by
  have hp : 0 < x := by linarith
  have hT : 1 ≤ x^u₁ := Real.one_le_rpow hx hu₁
  have hR := integration_cutoff_negative_power x u₂ α hx hu₂ hα
  have hExp : Real.exp (-(u₃*Real.log x)) = x^(-u₃) := by
    rw [show -(u₃*Real.log x)=(-u₃)*Real.log x by ring, exp_log_scale x (-u₃) hp]
  have hT4 : (x^u₁)^4=x^(4*u₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1
    ring
  unfold smoothingKernelEnvelope
  rw [hExp]
  calc
    _ ≤ C*(2*x^u₁)^4*(x^(-u₂*α)+x^(-u₃)) := by gcongr; linarith
    _ = _ := by
      rw [mul_pow, hT4,
        show 4*u₁-u₂*α=4*u₁+(-u₂*α) by ring,
        show 4*u₁-u₃=4*u₁+(-u₃) by ring, Real.rpow_add hp, Real.rpow_add hp]
      ring

theorem smoothing_frequency_core_power_bound (C x u₁ u₂ u₃ α E : Real) (q : Nat)
    (_hC : 0 ≤ C) (hx : 1 ≤ x) (hE : 0 ≤ E) (hq : (q : Real) ≤ x)
    (hbound : E ≤ 16*C*(x^(4*u₁-u₂*α)+x^(4*u₁-u₃))) :
    4*(x^2)^2*(4*(x^u₁)^2*(4*q*E)) ≤
      1024*C*(x^(5+6*u₁-u₂*α)+x^(5+6*u₁-u₃)) := by
  have hp : 0 < x := by linarith
  have hT2 : (x^u₁)^2=x^(2*u₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    congr 1
    ring
  have he (b : Real) : x^(5+6*u₁-b) = (x^2)^2*(x^u₁)^2*x*x^(4*u₁-b) := by
    rw [show 5+6*u₁-b=(4+2*u₁+1)+(4*u₁-b) by ring,
      Real.rpow_add hp, Real.rpow_add hp, Real.rpow_add hp,
      Real.rpow_ofNat, Real.rpow_one, ← hT2]
    ring
  calc
    _ ≤ 4*(x^2)^2*(4*(x^u₁)^2*(4*x*(16*C*(x^(4*u₁-u₂*α)+x^(4*u₁-u₃))))) := by gcongr
    _ = _ := by rw [he (u₂*α), he u₃]; ring

theorem smoothing_frequency_tail_power (x u₁ : Real) (hx : 0 < x) :
    4*(x^2)^2*(4*(2*(x^(-10 : Real)/10)⁻¹^10*(x^u₁)^(-9 : Real)/9)*((200/9 : Real)/x^(-10 : Real))) =
      ((6400/81 : Real)*10^10)*x^(114-9*u₁) := by
  have hδ : (x^(-10 : Real))⁻¹=x^(10 : Real) := by rw [Real.rpow_neg hx.le, inv_inv]
  have hN : (x^(-10 : Real)/10)⁻¹^10=(10 : Real)^10*x^(100 : Real) := by
    rw [inv_div, div_eq_mul_inv, hδ, mul_pow,
      ← Real.rpow_natCast (x^(10 : Real)) 10, ← Real.rpow_mul hx.le]
    norm_num
  have hT : (x^u₁)^(-9 : Real)=x^(-9*u₁) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  have hK : (x^2)^2=x^(4 : Real) := by rw [Real.rpow_ofNat]; ring
  rw [hN, hT, div_eq_mul_inv (200/9), hδ, hK]
  calc
    _ = ((6400/81 : Real)*10^10)*(x^(4 : Real)*x^(100 : Real)*x^(-9*u₁)*x^(10 : Real)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      congr 1
      ring

#print axioms smoothing_frequency_core_power_bound
#print axioms smoothing_frequency_tail_power
end ConditionalSpectralAudit.FourierHarmonic
