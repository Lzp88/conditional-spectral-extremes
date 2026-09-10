import ActualPermutationSpectrum
import ActualPermutationLaw
import OrdinaryEwensCorollary

/-! The main theorem and the ordinary random-centering corollary on the
literal space of permutations with their actual matrix polynomial. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
namespace ConditionalSpectralExtremes

def ewensPermutationConditioned (θ : Real) (n k : Nat)
    (E : Equiv.Perm (Fin n) → Prop) : Real :=
  ewensPermutationProbability θ n (fun σ => cycleCount (permutationConfiguration σ)=k ∧ E σ)/
    ewensPermutationProbability θ n (fun σ => cycleCount (permutationConfiguration σ)=k)

theorem actual_ewens_conditioned_profile (θ : Real) (hθ : 0 < θ) (n k : Nat)
    (E : Configuration n → Prop) :
    ewensPermutationConditioned θ n k (fun σ => E (permutationConfiguration σ))=
      conditionalProbability n k E := by
  rw [ewensPermutationConditioned,ewensPermutationProbability_cycle_condition]
  unfold ewensConditioned ewensProbability
  rw [div_div_div_cancel_right₀ (ne_of_gt (ewensPartition_pos θ hθ n)),
    ewensMass_count_event,ewensMass_count]
  exact mul_div_mul_left _ _ (ne_of_gt (pow_pos hθ k))

theorem actual_permutation_exact_cycle_localization :
    ∀ κlo κhi : Real, 0 < κlo → κlo < κhi →
      ∃ C : Real, 0 ≤ C ∧ ∀ θ : Real, 0 < θ → ∀ ε : Real, 0 < ε →
        ∃ N : Nat, 2 ≤ N ∧ ∀ n : Nat, N ≤ n → ∀ k : Nat,
          κlo*Real.log n ≤ (k : Real) → (k : Real) ≤ κhi*Real.log n →
          ewensPermutationConditioned θ n k (fun σ =>
            C*Real.log (Real.log n) < |permutationMaximumLogModulus σ-center n k|) < ε := by
  intro κlo κhi hlo hhi
  obtain ⟨C,hC,h⟩ := exact_cycle_localization κlo κhi hlo hhi
  refine ⟨C,hC,?_⟩
  intro θ hθ ε hε
  obtain ⟨N,hN,hn⟩ := h ε hε
  refine ⟨N,hN,?_⟩
  intro n hnN k hklo hkhi
  simp only [permutationMaximumLogModulus_eq_profile]
  rw [actual_ewens_conditioned_profile θ hθ n k
    (fun c => C*Real.log (Real.log n) < |maximumLogModulus c-center n k|)]
  exact hn n hnN k hklo hkhi

theorem actual_permutation_ordinary_random_centering (θ : Real) (hθ : 0 < θ) :
    ∃ C : Real, 0 ≤ C ∧ Tendsto (fun n : Nat => ewensPermutationProbability θ n
      (fun σ => C*Real.log (Real.log n) < |permutationMaximumLogModulus σ-
        ordinaryLinearCenter θ n (cycleCount (permutationConfiguration σ))|)) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := actual_ordinary_ewens_random_centering θ hθ
  refine ⟨C,hC,?_⟩
  have he (n : Nat) : ewensPermutationProbability θ n
      (fun σ => C*Real.log (Real.log n) < |permutationMaximumLogModulus σ-
        ordinaryLinearCenter θ n (cycleCount (permutationConfiguration σ))|)=
      ewensProbability θ n (fun c => C*Real.log (Real.log n) <
        |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|) := by
    simp only [permutationMaximumLogModulus_eq_profile]
    exact ewensPermutationProbability_profile θ n (fun c =>
      C*Real.log (Real.log n) < |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|)
  simpa only [he] using h

#print axioms actual_ewens_conditioned_profile
#print axioms actual_permutation_exact_cycle_localization
#print axioms actual_permutation_ordinary_random_centering
end ConditionalSpectralExtremes
