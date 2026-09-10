import EncodedProductOrbits

/-! Exact cycle-partition duplication for the actual product of two
fixed-point-free involutions, including one-cycles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {ι : Type*} [Fintype ι]

theorem encodedProduct_parts [DecidableEq ι] (π : Perm ι) (bits : ι → Bool) :
    (encodedProduct π bits).partition.parts=π.partition.parts+π.partition.parts := by
  rw [← permutationOrbitParts_eq_partition]
  unfold permutationOrbitParts
  simp_rw [encodedProductOrbitFiber_card]
  rw [Equiv.sum_comp (encodedProductOrbitEquiv π bits)
    (fun p => ({Nat.card (PermutationOrbitFiber π p.1)} : Multiset Nat)), Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  change permutationOrbitParts π+permutationOrbitParts π=π.partition.parts+π.partition.parts
  rw [permutationOrbitParts_eq_partition]

theorem actual_matching_product_parts (b : Matching (ι × Bool)) :
    ((standardMatching ι).val*b.val).partition.parts=
      matchingComponentParts b+matchingComponentParts b := by
  let c := matchingBinaryColoring (standardMatching ι) b
  rw [← recover_encoded_matching c]
  rw [matchingComponentParts_encoded]
  exact encodedProduct_parts (recoverPermutation c) (coloringBits c)

#print axioms encodedProduct_parts
#print axioms actual_matching_product_parts
end ConditionalSpectralExtremes.TwoMatchings
