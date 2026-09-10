import PoissonCenteredMoments
import CountCouplingKernel

/-! Actual moments of the discrepancy total |N-k| for N distributed Poisson(k). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts

theorem poisson_countGap_integrable (k : ℕ) :
    Integrable (fun N => (countGap k N : ℝ)) (poissonMeasure ⟨k, Nat.cast_nonneg k⟩) := by
  have hN : Integrable (fun N : ℕ => (N : ℝ)) (poissonMeasure ⟨k, Nat.cast_nonneg k⟩) := by
    simpa only [Nat.descFactorial_one] using poisson_factorial_integrable ⟨k, Nat.cast_nonneg k⟩ 1
  simpa only [countGap_real, Pi.sub_apply] using (hN.sub (integrable_const (k : ℝ))).abs

theorem poisson_countGap_square (k : ℕ) :
    Integrable (fun N => (countGap k N : ℝ)^2) (poissonMeasure ⟨k, Nat.cast_nonneg k⟩) ∧
    (∫ N, (countGap k N : ℝ)^2 ∂poissonMeasure ⟨k, Nat.cast_nonneg k⟩) = (k : ℝ) := by
  simp only [countGap_real, sq_abs]
  exact ⟨poisson_centered_square_integrable ⟨k, Nat.cast_nonneg k⟩,
    poisson_centered_square_integral ⟨k, Nat.cast_nonneg k⟩⟩

theorem poisson_countGap_mean_le_sqrt (k : ℕ) (hk : 0 < k) :
    (∫ N, (countGap k N : ℝ) ∂poissonMeasure ⟨k, Nat.cast_nonneg k⟩) ≤ Real.sqrt k := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkr
  have hi := (poisson_countGap_square k).1.add (integrable_const (k : ℝ))
  dsimp only [Pi.add_def] at hi
  have hp (N : ℕ) : (countGap k N : ℝ) ≤ ((countGap k N : ℝ)^2+(k : ℝ))/(2*Real.sqrt k) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt (k : ℝ))).mpr
    nlinarith [sq_nonneg ((countGap k N : ℝ)-Real.sqrt k), Real.sq_sqrt hkr.le]
  have hb := integral_mono (poisson_countGap_integrable k) (hi.div_const (2*Real.sqrt k)) hp
  rw [integral_div, integral_add (poisson_countGap_square k).1 (integrable_const _),
    (poisson_countGap_square k).2, integral_const] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hb
  have he : ((k : ℝ)+(k : ℝ))/(2*Real.sqrt k) = Real.sqrt k := by
    apply (div_eq_iff (by positivity : 2*Real.sqrt (k : ℝ) ≠ 0)).mpr
    nlinarith [Real.sq_sqrt hkr.le]
  simpa only [he] using hb

#print axioms poisson_countGap_integrable
#print axioms poisson_countGap_square
#print axioms poisson_countGap_mean_le_sqrt

end ConditionalSpectralExtremes.BlockCounts
