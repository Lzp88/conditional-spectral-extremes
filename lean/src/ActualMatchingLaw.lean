import MatchingComponentProfile
import ActualPermutationLaw

/-! Exact uniform-matching probabilities, obtained by counting actual
colored matchings through the explicit bijection, not by defining a
matching law to be an Ewens law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv

theorem matching_sum_profile (n : Nat) (f : Configuration n → Real) :
    (∑ b : Matching (Fin n × Bool), f (matchingConfiguration b))=
      (2:Real)^n * ∑ π : Perm (Fin n),
        (1/2:Real)^cycleCount (permutationConfiguration π) * f (permutationConfiguration π) := by
  let : ∀ b : Matching (Fin n × Bool), Fintype (StandardColoring b) := fun _ => Fintype.ofFinite _
  have hh := Equiv.sum_comp (coloredMatchingEquiv (Fin n))
    (fun pb => (1/2:Real)^cycleCount (permutationConfiguration pb.1) *
      f (permutationConfiguration pb.1))
  change (∑ bc : ColoredMatching (Fin n),
    (1/2:Real)^cycleCount (permutationConfiguration (recoverPermutation bc.2)) *
      f (permutationConfiguration (recoverPermutation bc.2))) = _ at hh
  rw [Fintype.sum_sigma, Fintype.sum_prod_type] at hh
  simp_rw [matchingConfiguration_recover] at hh
  have hcard (b : Matching (Fin n × Bool)) :
      (Fintype.card (StandardColoring b) : Real)=(2:Real)^cycleCount (matchingConfiguration b) := by
    rw [← Nat.card_eq_fintype_card, actual_matching_coloring_count, ← matchingConfiguration_count]
    norm_cast
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  simp_rw [hcard] at hh
  have hcancel (k : Nat) (v : Real) : (2:Real)^k*((1/2:Real)^k*v)=v := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  simp_rw [hcancel] at hh
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hh
  push_cast at hh
  rw [← Finset.mul_sum] at hh
  exact hh

def uniformMatchingMass (n : Nat) (E : Matching (Fin n × Bool) → Prop) : Real :=
  ∑ b : Matching (Fin n × Bool), if E b then 1 else 0

def uniformMatchingProbability (n : Nat) (E : Matching (Fin n × Bool) → Prop) : Real :=
  uniformMatchingMass n E / uniformMatchingMass n (fun _ => True)

theorem uniformMatchingMass_profile (n : Nat) (E : Configuration n → Prop) :
    uniformMatchingMass n (fun b => E (matchingConfiguration b))=
      (2:Real)^n * (n.factorial:Real) * ewensMass (1/2) n E := by
  unfold uniformMatchingMass
  rw [matching_sum_profile n (fun c => if E c then 1 else 0)]
  have hh := ewensPermutationMass_profile (1/2) n E
  unfold ewensPermutationMass at hh
  simp only [mul_ite, mul_one, mul_zero]
  rw [hh, mul_assoc]

theorem uniformMatchingProbability_profile (n : Nat) (E : Configuration n → Prop) :
    uniformMatchingProbability n (fun b => E (matchingConfiguration b))=ewensProbability (1/2) n E := by
  unfold uniformMatchingProbability
  rw [uniformMatchingMass_profile, uniformMatchingMass_profile n (fun _ => True)]
  exact mul_div_mul_left _ _ (by positivity : (2:Real)^n*(n.factorial:Real)≠0)

theorem uniformMatchingProbability_component_condition (n k : Nat) (E : Configuration n → Prop) :
    uniformMatchingProbability n (fun b => componentNumber (standardMatching (Fin n)) b=k ∧
        E (matchingConfiguration b)) /
      uniformMatchingProbability n (fun b => componentNumber (standardMatching (Fin n)) b=k) =
        ewensConditioned (1/2) n k E := by
  simp_rw [← matchingConfiguration_count]
  rw [uniformMatchingProbability_profile n (fun c => cycleCount c=k ∧ E c),
    uniformMatchingProbability_profile n (fun c => cycleCount c=k)]
  rfl

#print axioms matching_sum_profile
#print axioms uniformMatchingMass_profile
#print axioms uniformMatchingProbability_profile
#print axioms uniformMatchingProbability_component_condition
end ConditionalSpectralExtremes.TwoMatchings
