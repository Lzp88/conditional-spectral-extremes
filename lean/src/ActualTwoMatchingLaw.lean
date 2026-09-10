import UniformMatchingConjugation
import MatchingGraphConjugation

/-! The paper's actual model: a is any fixed-point-free involution and
b=g a g⁻¹ with g a genuinely uniform permutation. The observable is
the half-size profile of the actual union graph of a and b. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv

theorem uniformMatchingProbability_conjugation (n : Nat) (g : Perm (Fin n × Bool))
    (E : Matching (Fin n × Bool) → Prop) :
    uniformMatchingProbability n (fun b => E (conjugateMatching g b))=
      uniformMatchingProbability n E := by
  unfold uniformMatchingProbability uniformMatchingMass
  congr 1
  exact Equiv.sum_comp (conjugateMatchingEquiv g) (fun b => if E b then (1:Real) else 0)

theorem uniformMatchingProbability_actual_components (n : Nat) (a : Matching (Fin n × Bool))
    (E : Configuration n → Prop) :
    uniformMatchingProbability n (fun b => E (twoMatchingConfiguration a b))=
      ewensProbability (1/2) n E := by
  obtain ⟨g,rfl⟩ := conjugateMatching_surjective (standardMatching (Fin n)) a
  rw [← uniformMatchingProbability_conjugation n g
    (fun b => E (twoMatchingConfiguration (conjugateMatching g (standardMatching (Fin n))) b))]
  simp_rw [twoMatchingConfiguration_conjugation, twoMatchingConfiguration_standard]
  exact uniformMatchingProbability_profile n E

theorem actual_two_matching_Ewens (n : Nat) (a : Matching (Fin n × Bool))
    (E : Configuration n → Prop) :
    uniformConjugationProbability a (fun b => E (twoMatchingConfiguration a b))=
      ewensProbability (1/2) n E := by
  rw [uniformConjugationProbability_matching, uniformMatchingProbability_actual_components]

theorem twoMatchingConfiguration_count {n : Nat} (a b : Matching (Fin n × Bool)) :
    cycleCount (twoMatchingConfiguration a b)=componentNumber a b := by
  rw [← profileParts_card, twoMatchingConfiguration_parts]
  unfold twoMatchingParts componentNumber
  rw [Multiset.card_sum]
  simp only [Multiset.card_singleton, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]
  let fc : Fintype (matchingGraph a b).ConnectedComponent :=
    @SimpleGraph.instFintypeConnectedComponent (Fin n × Bool) (matchingGraph a b)
      (fun x y => Classical.propDecidable (x=y)) _
      (fun x y => Classical.propDecidable ((matchingGraph a b).Adj x y))
  exact (@Nat.card_eq_fintype_card (matchingGraph a b).ConnectedComponent fc).symm

theorem actual_two_matching_component_condition (n k : Nat) (a : Matching (Fin n × Bool))
    (E : Configuration n → Prop) :
    uniformConjugationProbability a (fun b => componentNumber a b=k ∧ E (twoMatchingConfiguration a b)) /
      uniformConjugationProbability a (fun b => componentNumber a b=k)=
        ewensConditioned (1/2) n k E := by
  simp_rw [← twoMatchingConfiguration_count]
  rw [actual_two_matching_Ewens n a (fun c => cycleCount c=k ∧ E c),
    actual_two_matching_Ewens n a (fun c => cycleCount c=k)]
  rfl

#print axioms uniformMatchingProbability_actual_components
#print axioms actual_two_matching_Ewens
#print axioms twoMatchingConfiguration_count
#print axioms actual_two_matching_component_condition
end ConditionalSpectralExtremes.TwoMatchings
