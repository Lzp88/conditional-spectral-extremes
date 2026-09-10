import CrossMassFarBound
import ActualCoefficientComparison
import ReservoirScale

/-! The actual uniform conditional cross-mass expectation, including b=0. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes

theorem actual_conditional_cross_mass_bound {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ k b : ℕ,
      a ≤ (k : ℝ)/Real.log n → (k : ℝ)/Real.log n ≤ B → 4*b ≤ n →
      conditionalExpectation n k (fun c => shortCycleMass b c * longCycleReciprocal b c) ≤ C := by
  obtain ⟨D, hD, N, hN, hr⟩ := actual_coefficient_ratio_bounded ha haB
  refine ⟨3*D, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N,
    ReservoirScale.L_tendsto_atTop.eventually_ge_atTop (2/a)] with n hn hL k b hal hlB hb
  have hn2 : 2 ≤ n := hN.trans hn
  have hn1 : 1 ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hLp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlarge : 2 ≤ a*Real.log n := by
    have := (div_le_iff₀ ha).mp hL
    simpa only [ReservoirScale.L, mul_comm] using this
  have hk2 : 2 ≤ k := by
    have he := (le_div_iff₀ hLp).mp hal
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨hc, h1⟩ := hr n hn n k 1 (by omega) le_rfl (by norm_num) hal hlB
  have h2 := (hr n hn n k 2 (by omega) le_rfl le_rfl hal hlB).2
  rw [cross_mass_expectation_exact hk2]
  by_cases hb0 : b = 0
  · subst b
    have hz : shortLengths n 0 = ∅ := by
      ext j
      simp [shortLengths]
    simp only [crossMassCoefficientSum, hz, Finset.sum_empty]
    positivity
  have hbp : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  rw [crossMassCoefficientSum_split]
  calc
    _ ≤ ∑ j ∈ shortLengths n b, (D/b+8*D/n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjb : j.val+1 ≤ b := (Finset.mem_filter.1 hj).2
      exact add_le_add (cross_mass_near_bound hb (by omega) hD.le
        (fun r hnr hrn => (hr n hn r k 2 hnr hrn le_rfl hal hlB).2) j hjb)
        (cross_mass_far_bound hn1 hk2 hD.le hc h1 h2 j)
    _ = (b : ℝ)*(D/b+8*D/n) := by
      simp only [Finset.sum_const, nsmul_eq_mul, shortLengths_card (show b ≤ n by omega)]
    _ ≤ 3*D := by
      have hbr : (4 : ℝ)*b ≤ n := by exact_mod_cast hb
      have he : (b : ℝ)*(D/b+8*D/n) = D + (8*D*b)/n := by field_simp
      rw [he]
      have hfar : (8*D*b)/n ≤ 2*D := by
        apply (div_le_iff₀ hnp).2
        nlinarith
      linarith

theorem actual_cross_mass_tail_bound {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ k b : ℕ,
      a ≤ (k : ℝ)/Real.log n → (k : ℝ)/Real.log n ≤ B → 4*b ≤ n →
      ∀ t : ℝ, 0 < t → conditionalProbability n k
        (fun c => t ≤ shortCycleMass b c * longCycleReciprocal b c) ≤ C/t := by
  obtain ⟨C, hC, he⟩ := actual_conditional_cross_mass_bound ha haB
  refine ⟨C, hC, ?_⟩
  filter_upwards [he] with n hn k b hal hlB hb t ht
  exact (conditionalExpectation_markov (fun c _ => cross_mass_observable_nonneg b c) ht).trans
    (div_le_div_of_nonneg_right (hn k b hal hlB hb) ht.le)

#print axioms actual_conditional_cross_mass_bound
#print axioms actual_cross_mass_tail_bound
end ConditionalSpectralExtremes
