import ActualTwoMatchingLaw
import TwoMatchingProductParts

/-! Final semantic interface for the exact encoding used in the paper.
Every observable is computed from actual involutions and actual graph components. -/
noncomputable section
namespace ConditionalSpectralExtremes.TwoMatchings

theorem actual_two_matching_encoding (n : Nat) (a : Matching (Fin n × Bool)) :
    (∀ E : Configuration n → Prop,
      uniformConjugationProbability a (fun b => E (twoMatchingConfiguration a b))=
        ewensProbability (1/2) n E) ∧
    (∀ b : Matching (Fin n × Bool),
      totalSize (twoMatchingConfiguration a b)=n ∧
      cycleCount (twoMatchingConfiguration a b)=componentNumber a b ∧
      (a.val*b.val).partition.parts=
        profileParts (twoMatchingConfiguration a b)+profileParts (twoMatchingConfiguration a b)) := by
  refine ⟨actual_two_matching_Ewens n a,?_⟩
  intro b
  refine ⟨twoMatchingConfiguration_size a b,twoMatchingConfiguration_count a b,?_⟩
  rw [twoMatchingConfiguration_parts]
  exact two_matching_product_parts a b

#print axioms actual_two_matching_encoding
end ConditionalSpectralExtremes.TwoMatchings
