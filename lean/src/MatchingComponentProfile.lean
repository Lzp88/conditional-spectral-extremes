import EncodedMatchingComponents
import RecoverColoredMatching
import MatchingBinaryColoring
import PermutationOrbitPartition

/-! The profile is defined from the genuine graph components: each part
is half the number of graph vertices. The encoding identifies this actual
profile with the ordinary cycle partition, and proves positivity and total size. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {ι : Type*} [Fintype ι]

def matchingComponentParts (b : Matching (ι × Bool)) : Multiset Nat :=
  ∑ C : (matchingGraph (standardMatching ι) b).ConnectedComponent,
    {Nat.card (GraphComponentFiber (matchingGraph (standardMatching ι) b) C) / 2}

theorem matchingComponentParts_encoded (π : Perm ι) (bits : ι → Bool) :
    matchingComponentParts (encodedMatching π bits)=π.partition.parts := by
  let := Classical.decEq ι
  unfold matchingComponentParts
  simp_rw [encodedComponentFiber_card, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rw [Equiv.sum_comp (encodedComponentEquiv π bits)
    (fun q => ({Nat.card (PermutationOrbitFiber π q)} : Multiset Nat))]
  exact permutationOrbitParts_eq_partition π

theorem matchingComponentParts_recover (b : Matching (ι × Bool)) (c : StandardColoring b) :
    matchingComponentParts b=(recoverPermutation c).partition.parts := by
  exact (congrArg matchingComponentParts (recover_encoded_matching c)).symm.trans
    (matchingComponentParts_encoded (recoverPermutation c) (coloringBits c))

def matchingComponentPartition (b : Matching (ι × Bool)) : (Fintype.card ι).Partition where
  parts := matchingComponentParts b
  parts_pos := by
    rw [matchingComponentParts_recover b (matchingBinaryColoring (standardMatching ι) b)]
    exact (recoverPermutation (matchingBinaryColoring (standardMatching ι) b)).partition.parts_pos
  parts_sum := by
    rw [matchingComponentParts_recover b (matchingBinaryColoring (standardMatching ι) b)]
    exact (recoverPermutation (matchingBinaryColoring (standardMatching ι) b)).partition.parts_sum

theorem matchingComponentParts_card (b : Matching (ι × Bool)) :
    (matchingComponentParts b).card=componentNumber (standardMatching ι) b := by
  unfold matchingComponentParts componentNumber
  rw [Multiset.card_sum]
  simp only [Multiset.card_singleton, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

def matchingConfiguration {n : Nat} (b : Matching (Fin n × Bool)) : Configuration n :=
  partitionConfiguration ⟨matchingComponentParts b,
    (matchingComponentPartition b).parts_pos,
    by simpa only [Fintype.card_fin] using
      (show (matchingComponentParts b).sum=Fintype.card (Fin n) from
        (matchingComponentPartition b).parts_sum)⟩

theorem matchingConfiguration_parts {n : Nat} (b : Matching (Fin n × Bool)) :
    profileParts (matchingConfiguration b)=matchingComponentParts b :=
  profileParts_partitionConfiguration _

theorem matchingConfiguration_size {n : Nat} (b : Matching (Fin n × Bool)) :
    totalSize (matchingConfiguration b)=n := partitionConfiguration_size _

theorem matchingConfiguration_count {n : Nat} (b : Matching (Fin n × Bool)) :
    cycleCount (matchingConfiguration b)=componentNumber (standardMatching (Fin n)) b := by
  rw [← profileParts_card, matchingConfiguration_parts, matchingComponentParts_card]

theorem matchingConfiguration_encoded {n : Nat} (π : Perm (Fin n)) (bits : Fin n → Bool) :
    matchingConfiguration (encodedMatching π bits)=permutationConfiguration π := by
  funext j
  apply Fin.ext
  change (matchingComponentParts (encodedMatching π bits)).count (j.val+1)=
    π.partition.parts.count (j.val+1)
  rw [matchingComponentParts_encoded]
  rw [Subsingleton.elim (fun a b : Fin n => Classical.propDecidable (a=b)) (instDecidableEqFin n)]

theorem matchingConfiguration_recover {n : Nat} (b : Matching (Fin n × Bool))
    (c : StandardColoring b) : permutationConfiguration (recoverPermutation c)=matchingConfiguration b := by
  rw [← matchingConfiguration_encoded _ (coloringBits c), recover_encoded_matching]

#print axioms matchingComponentParts_recover
#print axioms matchingConfiguration_parts
#print axioms matchingConfiguration_size
#print axioms matchingConfiguration_count
#print axioms matchingConfiguration_encoded
#print axioms matchingConfiguration_recover
end ConditionalSpectralExtremes.TwoMatchings
