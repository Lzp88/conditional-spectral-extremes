import PermutationOrbitPartition

/-! Product identities for the actual orbit partition and the literal
cycle-count characteristic polynomial, with no model substitution. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes
attribute [local instance] Classical.propDecidable

theorem multiset_map_prod_finset_sum {ι α M : Type*} [CommMonoid M]
    (S : Finset ι) (q : ι → Multiset α) (f : α → M) :
    ((∑ i ∈ S, q i).map f).prod=∏ i ∈ S, ((q i).map f).prod := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi,Finset.prod_insert hi,Multiset.map_add,Multiset.prod_add,ih]

theorem permutation_orbit_cycle_product {n : Nat} {M : Type*} [CommMonoid M]
    (σ : Equiv.Perm (Fin n)) (f : Nat → M) :
    (∏ q : PermutationOrbit σ, f (Nat.card (PermutationOrbitFiber σ q)))=
      ∏ j : Fin n, f (j.val+1)^(permutationConfiguration σ j).val := by
  classical
  have hleft : ((σ.partition.parts).map f).prod=
      ∏ q : PermutationOrbit σ, f (Nat.card (PermutationOrbitFiber σ q)) := by
    rw [← permutationOrbitParts_eq_partition,permutationOrbitParts,multiset_map_prod_finset_sum]
    simp only [Multiset.map_singleton,Multiset.prod_singleton]
  rw [← hleft,← permutationConfiguration_parts,profileParts,multiset_map_prod_finset_sum]
  simp only [Multiset.map_replicate,Multiset.prod_replicate]

#print axioms permutation_orbit_cycle_product
end ConditionalSpectralExtremes
