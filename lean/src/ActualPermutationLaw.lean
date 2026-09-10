import PermutationProfileCardinality
import ExactConditioning

/-! The genuine Ewens law on permutations pushes forward to the exact
profile law already used throughout the analytic proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ConditionalSpectralExtremes

def ewensPermutationMass (θ : Real) (n : Nat) (E : Equiv.Perm (Fin n) → Prop) : Real :=
  ∑ σ : Equiv.Perm (Fin n), if E σ then θ^cycleCount (permutationConfiguration σ) else 0

def ewensPermutationProbability (θ : Real) (n : Nat) (E : Equiv.Perm (Fin n) → Prop) : Real :=
  ewensPermutationMass θ n E/ewensPermutationMass θ n (fun _ => True)

theorem permutation_sum_profile (n : Nat) (f : Configuration n → Real) :
    (∑ σ : Equiv.Perm (Fin n), f (permutationConfiguration σ))=
      ∑ c : Configuration n, (permutationProfileCard n c : Real)*f c := by
  rw [← Fintype.sum_fiberwise (@permutationConfiguration n)]
  apply Finset.sum_congr rfl
  intro c _
  have hf (σ : {σ : Equiv.Perm (Fin n) // permutationConfiguration σ=c}) :
      f (permutationConfiguration σ.val)=f c := congrArg f σ.property
  simp only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    permutationProfileCard,Nat.card_eq_fintype_card]

theorem ewensPermutationMass_profile (θ : Real) (n : Nat) (E : Configuration n → Prop) :
    ewensPermutationMass θ n (fun σ => E (permutationConfiguration σ))=
      (n.factorial : Real)*ewensMass θ n E := by
  unfold ewensPermutationMass
  rw [permutation_sum_profile n (fun c => if E c then θ^cycleCount c else 0)]
  unfold ewensMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hh := permutationProfileCard_probability n c
  rw [div_eq_iff (by positivity : (n.factorial : Real)≠0)] at hh
  rw [hh,ewensProfileWeight_factor]
  by_cases hc : totalSize c=n <;> by_cases he : E c <;> simp [hc,he]
  ring

theorem ewensPermutationProbability_profile (θ : Real) (n : Nat) (E : Configuration n → Prop) :
    ewensPermutationProbability θ n (fun σ => E (permutationConfiguration σ))=
      ewensProbability θ n E := by
  unfold ewensPermutationProbability
  rw [ewensPermutationMass_profile,ewensPermutationMass_profile θ n (fun _ => True)]
  exact mul_div_mul_left _ _ (by positivity : (n.factorial : Real)≠0)

theorem ewensPermutationProbability_cycle_condition (θ : Real) (n k : Nat)
    (E : Configuration n → Prop) :
    ewensPermutationProbability θ n (fun σ => cycleCount (permutationConfiguration σ)=k ∧ E (permutationConfiguration σ))/
      ewensPermutationProbability θ n (fun σ => cycleCount (permutationConfiguration σ)=k)=
      ewensConditioned θ n k E := by
  rw [ewensPermutationProbability_profile θ n (fun c => cycleCount c=k ∧ E c),
    ewensPermutationProbability_profile θ n (fun c => cycleCount c=k)]
  rfl

#print axioms ewensPermutationMass_profile
#print axioms ewensPermutationProbability_profile
end ConditionalSpectralExtremes
