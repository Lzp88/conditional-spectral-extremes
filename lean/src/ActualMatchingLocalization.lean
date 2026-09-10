import ActualMatchingSpectrum
import ActualConditioningNonvacuity

/-! The final paragraph of the manuscript on its original probability
space: a fixed matching a, uniform g, and b=g a g⁻¹, conditioned on the
number of actual alternating graph components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes.TwoMatchings

def uniformConjugationConditioned {n : Nat} (a : Matching (Fin n × Bool)) (k : Nat)
    (E : Matching (Fin n × Bool) → Prop) : Real :=
  uniformConjugationProbability a (fun b => componentNumber a b=k ∧ E b)/
    uniformConjugationProbability a (fun b => componentNumber a b=k)

theorem actual_two_matching_conditioned_profile {n : Nat}
    (a : Matching (Fin n × Bool)) (k : Nat) (E : Configuration n → Prop) :
    uniformConjugationConditioned a k (fun b => E (twoMatchingConfiguration a b))=
      conditionalProbability n k E := by
  rw [uniformConjugationConditioned,actual_two_matching_component_condition]
  have hh := actual_ewens_conditioned_profile (1/2) (by norm_num) n k E
  rw [ewensPermutationConditioned,ewensPermutationProbability_cycle_condition] at hh
  exact hh

theorem actual_two_matching_exact_component_localization :
    ∀ κlo κhi : Real, 0 < κlo → κlo < κhi →
      ∃ C : Real, 0 ≤ C ∧ ∀ ε : Real, 0 < ε →
        ∃ N : Nat, 2 ≤ N ∧ ∀ n : Nat, N ≤ n →
          ∀ a : Matching (Fin n × Bool), ∀ k : Nat,
          κlo*Real.log n ≤ (k : Real) → (k : Real) ≤ κhi*Real.log n →
          uniformConjugationConditioned a k (fun b =>
            C*Real.log (Real.log n) < |twoMatchingMaximumLogModulus a b-2*center n k|) < ε := by
  intro κlo κhi hlo hhi
  obtain ⟨C,hC,h⟩ := exact_cycle_localization κlo κhi hlo hhi
  refine ⟨2*C,by positivity,?_⟩
  intro ε hε
  obtain ⟨N,hN,hn⟩ := h ε hε
  refine ⟨N,hN,?_⟩
  intro n hnN a k hklo hkhi
  have he : (fun b : Matching (Fin n × Bool) =>
      (2*C)*Real.log (Real.log n) < |twoMatchingMaximumLogModulus a b-2*center n k|)=
      (fun b => C*Real.log (Real.log n) <
        |maximumLogModulus (twoMatchingConfiguration a b)-center n k|) := by
    funext b
    apply propext
    rw [actual_two_matching_maximum,← mul_sub,abs_mul]
    norm_num
    constructor <;> intro hb <;> nlinarith
  rw [he,actual_two_matching_conditioned_profile a k
    (fun c => C*Real.log (Real.log n) < |maximumLogModulus c-center n k|)]
  exact hn n hnN k hklo hkhi

theorem actual_two_matching_conditioning_eventually_positive {a B : Real}
    (ha : 0 < a) (haB : a ≤ B) :
    ∃ N : Nat, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : Nat,
      a*Real.log n ≤ (k : Real) → (k : Real) ≤ B*Real.log n →
      ∀ a₀ : Matching (Fin n × Bool),
      0 < uniformConjugationProbability a₀ (fun b => componentNumber a₀ b=k) := by
  obtain ⟨N,hN,h⟩ := actual_permutation_conditioning_eventually_positive ha haB
  refine ⟨N,hN,?_⟩
  intro n hn k hka hkB a₀
  simp only [← twoMatchingConfiguration_count]
  rw [actual_two_matching_Ewens n a₀ (fun c => cycleCount c=k)]
  rw [← ewensPermutationProbability_profile (1/2) n (fun c => cycleCount c=k)]
  exact h n hn k hka hkB (1/2) (by norm_num)

#print axioms actual_two_matching_conditioned_profile
#print axioms actual_two_matching_exact_component_localization
#print axioms actual_two_matching_conditioning_eventually_positive
end ConditionalSpectralExtremes.TwoMatchings
