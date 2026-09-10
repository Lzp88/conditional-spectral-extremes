import FiniteMultinomial

/-! Actual first and second moments of a multinomial coordinate, derived by
differentiating its proved finite generating sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts

variable {ι : Type*} [Fintype ι]

theorem multinomial_mgf_derivative (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) (t : ℝ) :
    (∑ c : countFiber ι k k, multinomialMass p k c * ((c.val j).val : ℝ) *
      Real.exp (t*((c.val j).val : ℝ))) =
      (k : ℝ)*p j*(1-p j+p j*Real.exp t)^(k-1)*Real.exp t := by
  have hleft := HasDerivAt.fun_sum (u := Finset.univ) (fun (c : countFiber ι k k) _ =>
    ((Real.hasDerivAt_exp (t*((c.val j).val : ℝ))).comp t
      ((hasDerivAt_id t).mul_const ((c.val j).val : ℝ))).const_mul (multinomialMass p k c))
  have hright := (((Real.hasDerivAt_exp t).const_mul (p j)).const_add (1-p j)).pow k
  have heq : (fun s => ∑ c : countFiber ι k k,
      multinomialMass p k c*Real.exp (s*((c.val j).val : ℝ))) =
      (fun s => (1-p j+p j*Real.exp s)^k) := funext (multinomial_mgf p hpsum k j)
  dsimp only [Function.comp_apply, id_eq, Pi.pow_apply, Pi.mul_apply] at hleft hright
  rw [heq] at hleft
  have hh := hleft.unique hright
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro c _
    ring
  · ring

theorem multinomial_coordinate_mean (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) :
    (∑ c : countFiber ι k k, multinomialMass p k c*((c.val j).val : ℝ)) =
      (k : ℝ)*p j := by
  simpa only [zero_mul, Real.exp_zero, mul_one, sub_add_cancel, one_pow] using
    multinomial_mgf_derivative p hpsum k j 0

theorem multinomial_coordinate_second_moment (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) :
    (∑ c : countFiber ι k k, multinomialMass p k c*((c.val j).val : ℝ)^2) =
      (k : ℝ)*p j + (k : ℝ)*((k : ℝ)-1)*(p j)^2 := by
  have hleft := HasDerivAt.fun_sum (u := Finset.univ) (fun (c : countFiber ι k k) _ =>
    ((Real.hasDerivAt_exp ((0 : ℝ)*((c.val j).val : ℝ))).comp 0
      ((hasDerivAt_id 0).mul_const ((c.val j).val : ℝ))).const_mul
        (multinomialMass p k c*((c.val j).val : ℝ)))
  have hright := (((((Real.hasDerivAt_exp 0).const_mul (p j)).const_add (1-p j)).pow (k-1)).mul
    (Real.hasDerivAt_exp 0)).const_mul ((k : ℝ)*p j)
  have heq : (fun s => ∑ c : countFiber ι k k,
      multinomialMass p k c*((c.val j).val : ℝ)*Real.exp (s*((c.val j).val : ℝ))) =
      (fun s => (k : ℝ)*p j*((1-p j+p j*Real.exp s)^(k-1)*Real.exp s)) := by
    funext s
    rw [multinomial_mgf_derivative p hpsum k j s]
    ring
  dsimp only [Function.comp_apply, id_eq, Pi.pow_apply, Pi.mul_apply] at hleft hright
  rw [heq] at hleft
  have hh := hleft.unique hright
  simp only [zero_mul, Real.exp_zero, mul_one, one_mul, sub_add_cancel, one_pow] at hh
  have hk : (k : ℝ)*((k-1 : ℕ) : ℝ) = (k : ℝ)*((k : ℝ)-1) := by
    by_cases hk : k = 0
    · simp [hk]
    · rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  calc
    _ = ∑ c : countFiber ι k k,
        (multinomialMass p k c*((c.val j).val : ℝ))*((c.val j).val : ℝ) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [hh]
      calc
        _ = (k : ℝ)*p j + ((k : ℝ)*((k-1 : ℕ) : ℝ))*(p j)^2 := by ring
        _ = _ := by rw [hk]

theorem multinomial_coordinate_variance (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (j : ι) :
    (∑ c : countFiber ι k k,
      multinomialMass p k c*(((c.val j).val : ℝ)-(k : ℝ)*p j)^2) =
      (k : ℝ)*p j*(1-p j) := by
  calc
    _ = (∑ c : countFiber ι k k, multinomialMass p k c*((c.val j).val : ℝ)^2) -
        2*((k : ℝ)*p j)*(∑ c : countFiber ι k k, multinomialMass p k c*((c.val j).val : ℝ)) +
        ((k : ℝ)*p j)^2*(∑ c : countFiber ι k k, multinomialMass p k c) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [multinomial_coordinate_second_moment p hpsum k j,
        multinomial_coordinate_mean p hpsum k j, multinomialMass_sum_one p hpsum k]
      ring

#print axioms multinomial_mgf_derivative
#print axioms multinomial_coordinate_mean
#print axioms multinomial_coordinate_second_moment
#print axioms multinomial_coordinate_variance

end ConditionalSpectralExtremes.BlockCounts
