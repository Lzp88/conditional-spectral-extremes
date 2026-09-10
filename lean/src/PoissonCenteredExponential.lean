import PoissonExponentialFactorial

/-! The exact centered Poisson exponential moment, at every real tilt. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

def centeredPoisson (r : ℝ≥0) (n : ℕ) : ℝ := (n : ℝ)-(r : ℝ)

theorem centeredPoisson_exp_factor (r : ℝ≥0) (t : ℝ) (n : ℕ) :
    Real.exp (t*centeredPoisson r n) = Real.exp (-t*(r : ℝ))*Real.exp (t*(n : ℝ)) := by
  rw [← Real.exp_add]
  congr 1
  unfold centeredPoisson
  ring

theorem centeredPoisson_exp_integrable (r : ℝ≥0) (t : ℝ) :
    Integrable (fun n => Real.exp (t*centeredPoisson r n)) (poissonMeasure r) := by
  simp_rw [centeredPoisson_exp_factor]
  exact (poisson_exp_integrable r t).const_mul _

theorem centeredPoisson_mgf (r : ℝ≥0) (t : ℝ) :
    mgf (centeredPoisson r) (poissonMeasure r) t = Real.exp ((r : ℝ)*(Real.exp t-1-t)) := by
  unfold mgf
  simp_rw [centeredPoisson_exp_factor]
  rw [integral_const_mul, poisson_exp_integral, ← Real.exp_add]
  congr 1
  ring

theorem centeredPoisson_mgf_ge_one (r : ℝ≥0) (t : ℝ) :
    1 ≤ mgf (centeredPoisson r) (poissonMeasure r) t := by
  rw [centeredPoisson_mgf, Real.one_le_exp_iff]
  exact mul_nonneg r.coe_nonneg (by linarith [Real.add_one_le_exp t])

#print axioms centeredPoisson_exp_factor
#print axioms centeredPoisson_exp_integrable
#print axioms centeredPoisson_mgf
#print axioms centeredPoisson_mgf_ge_one

end ConditionalSpectralExtremes.BlockCounts
