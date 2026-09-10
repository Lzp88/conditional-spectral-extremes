import LowFieldBadMeasure

/-! The exact cumulant bound from the actual log-sine moment. -/
noncomputable section
open MeasureTheory
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.ArithmeticArcs

theorem lambda_le_s_log_two (s : Real) (hs : 0 ≤ s) : lambda s ≤ s*Real.log 2 := by
  have hd : -1 < s := by linarith
  have hA : logSineA s ≤ Real.exp (s*Real.log 2) := by
    rw [← logSine_integral_exp s hd]
    calc
      _ ≤ ∫ _t : Torus, Real.exp (s*Real.log 2) ∂haar :=
        integral_mono (logSine_exp_integrable s hd) (integrable_const _) (fun t =>
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (logSine_le_log_two t) hs))
      _ = _ := by simp
  have hh := Real.log_le_log (logSineA_pos s hd) hA
  rw [log_logSineA s hd, Real.log_exp] at hh
  exact hh

#print axioms lambda_le_s_log_two
end ConditionalSpectralExtremes
