import PoissonExponentialFactorial

/-! Actual centered second and fourth Poisson moments, with integrability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem cast_descFactorial_succ_real (n l : ℕ) :
    (n.descFactorial (l+1) : ℝ) = ((n : ℝ)-(l : ℝ))*(n.descFactorial l : ℝ) := by
  rw [Nat.descFactorial_succ, Nat.cast_mul]
  by_cases hl : l ≤ n
  · rw [Nat.cast_sub hl]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < l), Nat.cast_zero, mul_zero, mul_zero]

theorem centered_square_factorials (r : ℝ) (n : ℕ) :
    ((n : ℝ)-r)^2 = (n.descFactorial 2 : ℝ)+(1-2*r)*(n.descFactorial 1 : ℝ)+r^2 := by
  rw [Nat.cast_descFactorial_two, Nat.descFactorial_one]
  ring

theorem centered_fourth_factorials (r : ℝ) (n : ℕ) :
    ((n : ℝ)-r)^4 = (n.descFactorial 4 : ℝ)+(6-4*r)*(n.descFactorial 3 : ℝ)+
      (7-12*r+6*r^2)*(n.descFactorial 2 : ℝ)+
      (1-4*r+6*r^2-4*r^3)*(n.descFactorial 1 : ℝ)+r^4 := by
  have h3 : (n.descFactorial 3 : ℝ) = ((n : ℝ)-2)*((n : ℝ)*((n : ℝ)-1)) := by
    rw [show 3 = 2+1 by norm_num, cast_descFactorial_succ_real, Nat.cast_descFactorial_two, Nat.cast_ofNat]
  have h4 : (n.descFactorial 4 : ℝ) = ((n : ℝ)-3)*(((n : ℝ)-2)*((n : ℝ)*((n : ℝ)-1))) := by
    rw [show 4 = 3+1 by norm_num, cast_descFactorial_succ_real, h3, Nat.cast_ofNat]
  rw [h4, h3, Nat.cast_descFactorial_two, Nat.descFactorial_one]
  ring

theorem poisson_centered_square_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => ((n : ℝ)-(r : ℝ))^2) (poissonMeasure r) := by
  simp_rw [centered_square_factorials]
  exact ((poisson_factorial_integrable r 2).add
    ((poisson_factorial_integrable r 1).const_mul (1-2*(r : ℝ)))).add (integrable_const _)

theorem poisson_centered_fourth_integrable (r : ℝ≥0) :
    Integrable (fun n : ℕ => ((n : ℝ)-(r : ℝ))^4) (poissonMeasure r) := by
  simp_rw [centered_fourth_factorials]
  exact ((((poisson_factorial_integrable r 4).add
    ((poisson_factorial_integrable r 3).const_mul (6-4*(r : ℝ)))).add
      ((poisson_factorial_integrable r 2).const_mul (7-12*(r : ℝ)+6*(r : ℝ)^2))).add
        ((poisson_factorial_integrable r 1).const_mul (1-4*(r : ℝ)+6*(r : ℝ)^2-4*(r : ℝ)^3))).add (integrable_const _)

theorem poisson_centered_square_integral (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ)-(r : ℝ))^2 ∂poissonMeasure r) = (r : ℝ) := by
  have h2 := poisson_factorial_integrable r 2
  have h1 := (poisson_factorial_integrable r 1).const_mul (1-2*(r : ℝ))
  have h0 := integrable_const ((r : ℝ)^2) (μ := poissonMeasure r)
  have h21 := h2.add h1
  dsimp only [Pi.add_def] at h21
  simp_rw [centered_square_factorials]
  rw [integral_add h21 h0, integral_add h2 h1, integral_const_mul,
    poisson_factorial_integral, poisson_factorial_integral]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, pow_one]
  ring

theorem poisson_centered_fourth_integral (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ)-(r : ℝ))^4 ∂poissonMeasure r) = (r : ℝ)+3*(r : ℝ)^2 := by
  have h4 := poisson_factorial_integrable r 4
  have h3 := (poisson_factorial_integrable r 3).const_mul (6-4*(r : ℝ))
  have h2 := (poisson_factorial_integrable r 2).const_mul (7-12*(r : ℝ)+6*(r : ℝ)^2)
  have h1 := (poisson_factorial_integrable r 1).const_mul (1-4*(r : ℝ)+6*(r : ℝ)^2-4*(r : ℝ)^3)
  have h0 := integrable_const ((r : ℝ)^4) (μ := poissonMeasure r)
  have h43 := h4.add h3
  have h432 := h43.add h2
  have h4321 := h432.add h1
  dsimp only [Pi.add_def] at h43 h432 h4321
  simp_rw [centered_fourth_factorials]
  rw [integral_add h4321 h0, integral_add h432 h1, integral_add h43 h2, integral_add h4 h3]
  simp only [integral_const_mul, poisson_factorial_integral,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, pow_one]
  ring

#print axioms cast_descFactorial_succ_real
#print axioms centered_square_factorials
#print axioms centered_fourth_factorials
#print axioms poisson_centered_square_integrable
#print axioms poisson_centered_fourth_integrable
#print axioms poisson_centered_square_integral
#print axioms poisson_centered_fourth_integral

end ConditionalSpectralExtremes.BlockCounts
