import ConfigurationCycleLists
import ActualCrossMassBound
import ReservoirScaleAsymptotics

/-! Insertion stability applied to the actual short/long permutation factors. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem actual_short_long_insertion {n : ℕ} (b : ℕ) (c : Configuration n) :
    -Real.log 2 - 2*Real.exp 1*shortCycleMass b c*longCycleReciprocal b c ≤
      maximumLogModulus c - maximumLogModulus (shortConfiguration b c) ∧
    maximumLogModulus c - maximumLogModulus (shortConfiguration b c) ≤
      (cycleCount (longConfiguration b c) : ℝ)*Real.log 2 := by
  let p := characteristicPolynomial (shortConfiguration b c)
  let J := configurationCycleList (longConfiguration b c)
  have hp : p ≠ 0 := characteristicPolynomial_ne_zero _
  have hJ : ∀ j ∈ J, 0 < j := configurationCycleList_pos _
  have hprod : p*cycleProduct J = characteristicPolynomial c := by
    dsimp [p, J]
    rw [configurationCycleList_polynomial, ← characteristicPolynomial_short_long]
  have hmass : (p.natDegree : ℝ) = shortCycleMass b c := by
    dsimp [p]
    rw [characteristicPolynomial_natDegree, shortConfiguration_mass]
  have hrecip : (J.map (fun j : ℕ => (j : ℝ)⁻¹)).sum = longCycleReciprocal b c :=
    longConfiguration_reciprocal b c
  have hupper := insertion_log_upper p hp J hJ
  rw [hprod, configurationCycleList_length] at hupper
  refine ⟨?_, hupper⟩
  by_cases hd : 0 < p.natDegree
  · have hlower := insertion_log_lower p hp hd J hJ
    rw [hprod, hmass, hrecip] at hlower
    exact hlower
  · have hz : p.natDegree = 0 := by omega
    have hlower := insertion_log_lower_degree_zero p hp hz J hJ
    rw [hprod] at hlower
    have hm : shortCycleMass b c = 0 := by simpa only [hz, Nat.cast_zero] using hmass.symm
    rw [hm]
    simp only [mul_zero, zero_mul, sub_zero]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact (neg_nonpos.mpr hlog).trans hlower

theorem actual_insertion_loss_tail {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ k b : ℕ,
      a ≤ (k : ℝ)/Real.log n → (k : ℝ)/Real.log n ≤ B → 4*b ≤ n →
      ∀ t : ℝ, 0 < t → conditionalProbability n k
        (fun c => t+Real.log 2 ≤
          maximumLogModulus (shortConfiguration b c)-maximumLogModulus c) ≤ C/t := by
  obtain ⟨C, hC, he⟩ := actual_cross_mass_tail_bound ha haB
  refine ⟨(2*Real.exp 1)*C, by positivity, ?_⟩
  filter_upwards [he] with n hn k b hal hlB hb t ht
  have htail := hn k b hal hlB hb (t/(2*Real.exp 1)) (by positivity)
  have hevent : ∀ c : Configuration n,
      t+Real.log 2 ≤ maximumLogModulus (shortConfiguration b c)-maximumLogModulus c →
        t/(2*Real.exp 1) ≤ shortCycleMass b c*longCycleReciprocal b c := by
    intro c hc
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.exp 1)).2
    have hlow := (actual_short_long_insertion b c).1
    nlinarith
  have hmono : conditionalProbability n k
      (fun c => t+Real.log 2 ≤ maximumLogModulus (shortConfiguration b c)-maximumLogModulus c) ≤
      conditionalProbability n k (fun c => t/(2*Real.exp 1) ≤ shortCycleMass b c*longCycleReciprocal b c) := by
    classical
    rw [← conditionalExpectation_indicator, ← conditionalExpectation_indicator]
    apply conditionalExpectation_mono
    intro c _
    split_ifs with h1 h2 h2
    · rfl
    · exact False.elim (h2 (hevent c h1))
    · norm_num
    · rfl
  calc
    _ ≤ C/(t/(2*Real.exp 1)) := hmono.trans htail
    _ = (2*Real.exp 1)*C/t := by field_simp

#print axioms actual_short_long_insertion
#print axioms actual_insertion_loss_tail
end ConditionalSpectralExtremes
