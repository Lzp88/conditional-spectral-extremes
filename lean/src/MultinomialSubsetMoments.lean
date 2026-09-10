import FiniteMultinomialMoments
import NaturalMultinomialLaw

/-! Actual first and second moments of the aggregate of any category subset.
The aggregate MGF is proved directly from the finite generating polynomial. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

def subsetCount (s : Finset ι) (c : ι → ℕ) : ℝ := ∑ i ∈ s, (c i : ℝ)

theorem multinomial_subset_mgf (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (s : Finset ι) (t : ℝ) :
    (∑ c : countFiber ι k k,
      multinomialMass p k c*Real.exp (t*subsetCount s (naturalCountVector c))) =
      (1-(∑ i ∈ s, p i)+(∑ i ∈ s, p i)*Real.exp t)^k := by
  classical
  have hp : (∑ i, p i*(if i ∈ s then Real.exp t else 1)) =
      1-(∑ i ∈ s, p i)+(∑ i ∈ s, p i)*Real.exp t := by
    calc
      _ = ∑ i, (p i + if i ∈ s then p i*(Real.exp t-1) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ s
        · simp only [hi, if_true]
          ring
        · simp only [hi, if_false, mul_one, add_zero]
      _ = _ := by rw [Finset.sum_add_distrib, hpsum, Finset.sum_ite_mem_eq, ← Finset.sum_mul]; ring
  have hh := multinomial_generating_function p (fun i => if i ∈ s then Real.exp t else 1) k
  rw [hp] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp only [ite_pow, one_pow, Finset.prod_ite_mem_eq]
  simp only [subsetCount, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 1
  dsimp only [naturalCountVector]
  ring

theorem multinomial_subset_mgf_derivative (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (s : Finset ι) (t : ℝ) :
    (∑ c : countFiber ι k k, multinomialMass p k c*subsetCount s (naturalCountVector c)*
      Real.exp (t*subsetCount s (naturalCountVector c))) =
      (k : ℝ)*(∑ i ∈ s, p i)*(1-(∑ i ∈ s, p i)+(∑ i ∈ s, p i)*Real.exp t)^(k-1)*Real.exp t := by
  have hleft := HasDerivAt.fun_sum (u := Finset.univ) (fun (c : countFiber ι k k) _ =>
    ((Real.hasDerivAt_exp (t*subsetCount s (naturalCountVector c))).comp t
      ((hasDerivAt_id t).mul_const (subsetCount s (naturalCountVector c)))).const_mul (multinomialMass p k c))
  have hright := (((Real.hasDerivAt_exp t).const_mul (∑ i ∈ s, p i)).const_add (1-(∑ i ∈ s, p i))).pow k
  have heq : (fun t => ∑ c : countFiber ι k k,
      multinomialMass p k c*Real.exp (t*subsetCount s (naturalCountVector c))) =
      (fun t => (1-(∑ i ∈ s, p i)+(∑ i ∈ s, p i)*Real.exp t)^k) :=
    funext (multinomial_subset_mgf p hpsum k s)
  dsimp only [Function.comp_apply, id_eq, Pi.pow_apply, Pi.mul_apply] at hleft hright
  rw [heq] at hleft
  have hh := hleft.unique hright
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro c _
    ring
  · ring

theorem multinomial_subset_mean (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (s : Finset ι) :
    (∑ c : countFiber ι k k, multinomialMass p k c*subsetCount s (naturalCountVector c)) =
      (k : ℝ)*(∑ i ∈ s, p i) := by
  simpa only [zero_mul, Real.exp_zero, mul_one, sub_add_cancel, one_pow] using
    multinomial_subset_mgf_derivative p hpsum k s 0

theorem multinomial_subset_second_moment (p : ι → ℝ) (hpsum : ∑ i, p i = 1)
    (k : ℕ) (s : Finset ι) :
    (∑ c : countFiber ι k k, multinomialMass p k c*(subsetCount s (naturalCountVector c))^2) =
      (k : ℝ)*(∑ i ∈ s, p i)+(k : ℝ)*((k : ℝ)-1)*(∑ i ∈ s, p i)^2 := by
  have hleft := HasDerivAt.fun_sum (u := Finset.univ) (fun (c : countFiber ι k k) _ =>
    ((Real.hasDerivAt_exp ((0 : ℝ)*subsetCount s (naturalCountVector c))).comp 0
      ((hasDerivAt_id 0).mul_const (subsetCount s (naturalCountVector c)))).const_mul
        (multinomialMass p k c*subsetCount s (naturalCountVector c)))
  have hright := (((((Real.hasDerivAt_exp 0).const_mul (∑ i ∈ s, p i)).const_add
    (1-(∑ i ∈ s, p i))).pow (k-1)).mul (Real.hasDerivAt_exp 0)).const_mul ((k : ℝ)*(∑ i ∈ s, p i))
  have heq : (fun t => ∑ c : countFiber ι k k,
      multinomialMass p k c*subsetCount s (naturalCountVector c)*Real.exp (t*subsetCount s (naturalCountVector c))) =
      (fun t => (k : ℝ)*(∑ i ∈ s, p i)*
        ((1-(∑ i ∈ s, p i)+(∑ i ∈ s, p i)*Real.exp t)^(k-1)*Real.exp t)) := by
    funext t
    rw [multinomial_subset_mgf_derivative p hpsum k s t]
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
        (multinomialMass p k c*subsetCount s (naturalCountVector c))*subsetCount s (naturalCountVector c) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [hh]
      calc
        _ = (k : ℝ)*(∑ i ∈ s, p i)+((k : ℝ)*((k-1 : ℕ) : ℝ))*(∑ i ∈ s, p i)^2 := by ring
        _ = _ := by rw [hk]

#print axioms multinomial_subset_mgf
#print axioms multinomial_subset_mgf_derivative
#print axioms multinomial_subset_mean
#print axioms multinomial_subset_second_moment

end ConditionalSpectralExtremes.BlockCounts
