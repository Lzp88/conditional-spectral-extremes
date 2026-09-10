import MatchingConjugacy
import ActualMatchingLaw

/-! The matching sampled by conjugating any fixed involution with a
uniform permutation is actually uniform on all fixed-point-free matchings. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace ConditionalSpectralExtremes.TwoMatchings
open Equiv
variable {α : Type*} [Fintype α]

def conjugationFiberCard (a : Matching α) : Nat :=
  Nat.card {g : Perm α // conjugateMatching g a=a}

theorem matching_conjugation_sum (a : Matching α) (f : Matching α → Real) :
    (∑ g : Perm α, f (conjugateMatching g a))=
      (conjugationFiberCard a : Real) * ∑ b : Matching α, f b := by
  rw [← Fintype.sum_fiberwise (fun g : Perm α => conjugateMatching g a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hh (g : {g : Perm α // conjugateMatching g a=b}) : f (conjugateMatching g.val a)=f b :=
    congrArg f g.property
  simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, conjugateMatching_fibers_card a b a]
  rfl

def uniformConjugationProbability (a : Matching α) (E : Matching α → Prop) : Real :=
  (∑ g : Perm α, if E (conjugateMatching g a) then 1 else 0) / (Fintype.card (Perm α) : Real)

theorem uniformConjugationProbability_matching (n : Nat) (a : Matching (Fin n × Bool))
    (E : Matching (Fin n × Bool) → Prop) :
    uniformConjugationProbability a E=uniformMatchingProbability n E := by
  have hnum := matching_conjugation_sum a (fun b => if E b then 1 else 0)
  have hden := matching_conjugation_sum a (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hden
  unfold uniformConjugationProbability uniformMatchingProbability uniformMatchingMass
  rw [hnum,hden]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [if_pos True.intro, mul_one]
  exact mul_div_mul_left _ _ (by
    exact_mod_cast (conjugateMatching_fiber_card_pos a a).ne' :
      (conjugationFiberCard a : Real)≠0)

theorem actual_conjugation_component_profile (n : Nat) (a : Matching (Fin n × Bool))
    (E : Configuration n → Prop) :
    uniformConjugationProbability a (fun b => E (matchingConfiguration b))=
      ewensProbability (1/2) n E := by
  rw [uniformConjugationProbability_matching, uniformMatchingProbability_profile]

#print axioms matching_conjugation_sum
#print axioms uniformConjugationProbability_matching
#print axioms actual_conjugation_component_profile
end ConditionalSpectralExtremes.TwoMatchings
