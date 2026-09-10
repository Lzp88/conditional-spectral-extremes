import PermutationOrbitProducts
import PermutationOrbitDeterminant

/-! A basis-independent version of the literal matrix/cycle identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem permutation_determinant_partition {α R : Type*} [Fintype α] [DecidableEq α]
    [CommRing R] (σ : Equiv.Perm α) (z : R) :
    (1-z • σ.permMatrix R).det=
      ((σ.partition.parts).map (fun j => 1-z^j)).prod := by
  rw [permutation_orbit_determinant,← permutationOrbitParts_eq_partition,
    permutationOrbitParts,multiset_map_prod_finset_sum]
  simp only [Multiset.map_singleton,Multiset.prod_singleton]

theorem profileParts_map_prod {n : Nat} {M : Type*} [CommMonoid M]
    (c : Configuration n) (f : Nat → M) :
    ((profileParts c).map f).prod=∏ j : Fin n, f (j.val+1)^(c j).val := by
  rw [profileParts,multiset_map_prod_finset_sum]
  simp only [Multiset.map_replicate,Multiset.prod_replicate]

theorem profileParts_polynomial {n : Nat} (c : Configuration n) :
    ((profileParts c).map (fun j => 1-(Polynomial.X : Polynomial Complex)^j)).prod=
      characteristicPolynomial c := by
  rw [profileParts_map_prod]
  rfl

#print axioms permutation_determinant_partition
#print axioms profileParts_polynomial
end ConditionalSpectralExtremes
