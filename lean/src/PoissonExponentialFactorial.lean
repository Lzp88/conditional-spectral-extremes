import Mathlib

/-! Actual Poisson exponential and factorial moments, proved by the
convergent defining series. No moment formula is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem poisson_exp_hasSum (r : ℝ≥0) (t : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ)*
      Real.exp (t*(n : ℝ))) (Real.exp ((r : ℝ)*(Real.exp t-1))) := by
  have he (n : ℕ) : Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ)*Real.exp (t*(n : ℝ)) =
      Real.exp (-(r : ℝ))*(((r : ℝ)*Real.exp t)^n/(n.factorial : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [mul_comm t (n : ℝ)]
    ring
  simp_rw [he]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*Real.exp t)).mul_left (Real.exp (-(r : ℝ)))
  rw [← Real.exp_eq_exp_ℝ] at hh
  convert! hh using 1
  rw [← Real.exp_add]
  congr 1
  ring

theorem poisson_exp_integrable (r : ℝ≥0) (t : ℝ) :
    Integrable (fun n : ℕ => Real.exp (t*(n : ℝ))) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  convert (poisson_exp_hasSum r t).summable using 1
  funext n
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem poisson_exp_integral (r : ℝ≥0) (t : ℝ) :
    (∫ n : ℕ, Real.exp (t*(n : ℝ)) ∂poissonMeasure r) =
      Real.exp ((r : ℝ)*(Real.exp t-1)) := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_exp_hasSum r t).tsum_eq

theorem poisson_factorial_shift (r : ℝ≥0) (l n : ℕ) :
    Real.exp (-(r : ℝ))*(r : ℝ)^(n+l)/((n+l).factorial : ℝ)*
      ((n+l).descFactorial l : ℝ) =
        (r : ℝ)^l*(Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ)) := by
  have hf : (n.factorial : ℝ)*((n+l).descFactorial l : ℝ) = ((n+l).factorial : ℝ) := by
    have hh := Nat.factorial_mul_descFactorial (show l ≤ n+l by omega)
    rw [Nat.add_sub_cancel] at hh
    exact_mod_cast hh
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hnl : ((n+l).factorial : ℝ) ≠ 0 := by positivity
  rw [pow_add]
  field_simp
  linear_combination (r : ℝ)^n*(r : ℝ)^l*hf

theorem poisson_factorial_hasSum (r : ℝ≥0) (l : ℕ) :
    HasSum (fun n : ℕ => Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ)*
      (n.descFactorial l : ℝ)) ((r : ℝ)^l) := by
  let f := fun n : ℕ => Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ)*(n.descFactorial l : ℝ)
  have hz : ∑ i ∈ Finset.range l, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    dsimp [f]
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hi), Nat.cast_zero, mul_zero]
  have hh : HasSum (fun n => f (n+l)) ((r : ℝ)^l) := by
    dsimp only [f]
    simp_rw [poisson_factorial_shift]
    simpa only [mul_one] using (hasSum_one_poissonMeasure r).mul_left ((r : ℝ)^l)
  change HasSum f ((r : ℝ)^l)
  apply (hasSum_nat_add_iff' l).mp
  simpa only [hz, sub_zero] using hh

theorem poisson_factorial_integrable (r : ℝ≥0) (l : ℕ) :
    Integrable (fun n : ℕ => (n.descFactorial l : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  convert (poisson_factorial_hasSum r l).summable using 1
  funext n
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

theorem poisson_factorial_integral (r : ℝ≥0) (l : ℕ) :
    (∫ n : ℕ, (n.descFactorial l : ℝ) ∂poissonMeasure r) = (r : ℝ)^l := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (poisson_factorial_hasSum r l).tsum_eq

#print axioms poisson_exp_hasSum
#print axioms poisson_exp_integrable
#print axioms poisson_exp_integral
#print axioms poisson_factorial_shift
#print axioms poisson_factorial_hasSum
#print axioms poisson_factorial_integrable
#print axioms poisson_factorial_integral

end ConditionalSpectralExtremes.BlockCounts
