import ComplexLogSineMellin
import TiltedLogSineNonlattice

/-! Actual complex integrability and the exact tilted characteristic function. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Real Complex

namespace ConditionalSpectralExtremes

theorem actual_complex_mellin_integrable (z : Complex) (hz : -1 < z.re) :
    Integrable (ConditionalSpectralAudit.FourierTail.complexPhi z)
      AddCircle.haarAddCircle := by
  have hi := integrable_cexp_mul_of_re_mem_integrableExpSet
    logSine_measurable.aemeasurable (logSine_exp_integrable z.re hz)
  exact hi.congr (complexPhi_eq_exp_logSine_ae z).symm

theorem logSineFourierLaplace_eq_Gamma (β t : Real) (hβ : -1 < β) :
    logSineFourierLaplace (β, t) = complexLogSineA ((β : Complex) + t * Complex.I) := by
  have he : logSineFourierLaplace (β, t) =
      complexMGF id logSineLaw ((β : Complex) + t * Complex.I) := by
    unfold logSineFourierLaplace complexMGF
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [logSineFourierLaplaceIntegrand, id_eq, Complex.ofReal_exp,
      Complex.ofReal_mul]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  exact logSineLaw_complexMGF_eq_Gamma (by simpa using hβ)

theorem tiltedLogSineLaw_charFun_eq_Gamma (β t : Real) (hβ : -1 < β) :
    charFun (tiltedLogSineLaw β) t =
      complexLogSineA ((β : Complex) + t * Complex.I) / (logSineA β : Complex) := by
  rw [tiltedLogSineLaw_charFun_eq_fourierLaplace β t hβ,
    logSineFourierLaplace_eq_Gamma β t hβ, logSineA_eq_exp_lambda β hβ]
  simp only [Complex.real_smul, Real.exp_neg, Complex.ofReal_inv]
  ring

#print axioms actual_complex_mellin_integrable
#print axioms tiltedLogSineLaw_charFun_eq_Gamma
end ConditionalSpectralExtremes
