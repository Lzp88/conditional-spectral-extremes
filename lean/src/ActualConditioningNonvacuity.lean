import ActualPermutationLocalization

/-! Positivity of every conditioning event in the uniform main-theorem
window, on the actual permutation probability space. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem actual_permutation_count_probability (θ : Real) (n k : Nat) :
    ewensPermutationProbability θ n (fun σ => cycleCount (permutationConfiguration σ)=k)=
      θ^k*coefficient n k/ewensPartition θ n := by
  rw [ewensPermutationProbability_profile θ n (fun c => cycleCount c=k),
    ewensProbability,ewensMass_count]

theorem actual_permutation_conditioning_eventually_positive {a B : Real}
    (ha : 0 < a) (haB : a ≤ B) :
    ∃ N : Nat, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : Nat,
      a*Real.log n ≤ (k : Real) → (k : Real) ≤ B*Real.log n →
      ∀ θ : Real, 0 < θ →
      0 < ewensPermutationProbability θ n
        (fun σ => cycleCount (permutationConfiguration σ)=k) := by
  obtain ⟨D,_hD,N,hN,hbound⟩ := actual_coefficient_ratio_bounded ha haB
  refine ⟨N,hN,?_⟩
  intro n hn k hka hkB θ hθ
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc := (hbound n hn n k 0 (by omega) le_rfl (by omega)
    ((le_div_iff₀ hL).mpr hka) ((div_le_iff₀ hL).mpr hkB)).1
  rw [actual_permutation_count_probability]
  exact div_pos (mul_pos (pow_pos hθ k) hc) (ewensPartition_pos θ hθ n)

#print axioms actual_permutation_count_probability
#print axioms actual_permutation_conditioning_eventually_positive
end ConditionalSpectralExtremes
