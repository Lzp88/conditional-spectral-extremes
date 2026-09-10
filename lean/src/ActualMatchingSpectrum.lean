import TwoMatchingProductParts
import ActualTwoMatchingLaw
import PermutationPartitionDeterminant
import PolynomialCirclePowers

/-! The original two-matching model's literal determinant and maximum,
for every fixed matching a and every matching b, not only a standard a. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes.TwoMatchings

def twoMatchingDetPolynomial {n : Nat} (a b : Matching (Fin n × Bool)) : Polynomial Complex :=
  (1-(Polynomial.X : Polynomial Complex) • (a.val*b.val).permMatrix (Polynomial Complex)).det

theorem actual_two_matching_determinant_polynomial {n : Nat}
    (a b : Matching (Fin n × Bool)) :
    twoMatchingDetPolynomial a b=(characteristicPolynomial (twoMatchingConfiguration a b))^2 := by
  unfold twoMatchingDetPolynomial
  rw [permutation_determinant_partition,two_matching_product_parts,
    ← twoMatchingConfiguration_parts a b]
  simp only [Multiset.map_add,Multiset.prod_add,profileParts_polynomial,pow_two]

theorem actual_two_matching_determinant {n : Nat}
    (a b : Matching (Fin n × Bool)) (z : Complex) :
    (1-z • (a.val*b.val).permMatrix Complex).det=
      ((characteristicPolynomial (twoMatchingConfiguration a b)).eval z)^2 := by
  rw [permutation_determinant_partition,two_matching_product_parts,
    ← twoMatchingConfiguration_parts a b]
  simp only [Multiset.map_add,Multiset.prod_add,profileParts_map_prod,
    characteristicPolynomial,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,pow_two]

def twoMatchingMaximumLogModulus {n : Nat} (a b : Matching (Fin n × Bool)) : Real :=
  Real.log (circleNorm (twoMatchingDetPolynomial a b))

theorem actual_two_matching_maximum {n : Nat} (a b : Matching (Fin n × Bool)) :
    twoMatchingMaximumLogModulus a b=2*maximumLogModulus (twoMatchingConfiguration a b) := by
  rw [twoMatchingMaximumLogModulus,actual_two_matching_determinant_polynomial,log_circleNorm_pow]
  rfl

#print axioms actual_two_matching_determinant_polynomial
#print axioms actual_two_matching_determinant
#print axioms actual_two_matching_maximum
end ConditionalSpectralExtremes.TwoMatchings
