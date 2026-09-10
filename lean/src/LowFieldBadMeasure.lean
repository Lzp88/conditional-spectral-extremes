import LowLogSineField
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Deterministic low-field exclusion: its bad angular set is bounded by
the actual number of low cycles, uniformly in all their positive lengths. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Real BigOperators ENNReal
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.ArithmeticArcs

theorem lowLogSineField_measurable {q : Nat} (j : Fin q → Nat) : Measurable (lowLogSineField j) := by
  unfold lowLogSineField logSine
  fun_prop

theorem low_negative_sum_integrable {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v) :
    Integrable (fun t : Torus => ∑ v, negativeLogSine (j v • t)) haar :=
  integrable_finsetSum Finset.univ (fun v _ => logSine_nsmul_integrable (j v) (hj v))

theorem low_negative_sum_integral {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v) :
    (∫ t : Torus, ∑ v, negativeLogSine (j v • t) ∂haar) = (q : Real)*negativeLogSineMass := by
  rw [integral_finsetSum Finset.univ (fun v _ => logSine_nsmul_integrable (j v) (hj v))]
  simp only [negativeLogSine_nsmul_integral _ (hj _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem actual_low_field_bad_measure {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v)
    (u : Real) (hu : 0 < u) :
    haar {t | lowLogSineField j t < -u} ≤ ENNReal.ofReal ((q : Real)*negativeLogSineMass/u) := by
  let g : Torus → ENNReal := fun t => ENNReal.ofReal (∑ v, negativeLogSine (j v • t))
  have hm : Measurable g := by unfold g negativeLogSine logSine; fun_prop
  have hinc : {t | lowLogSineField j t < -u} ⊆ {t | ENNReal.ofReal u ≤ g t} := by
    intro t ht
    change lowLogSineField j t < -u at ht
    apply ENNReal.ofReal_le_ofReal
    exact (show u ≤ max (-lowLogSineField j t) 0 from
      (by linarith : u ≤ -lowLogSineField j t).trans (le_max_left _ _)).trans
      (lowLogSineField_negative_bound j t)
  have hi : (∫⁻ t, g t ∂haar) = ENNReal.ofReal ((q : Real)*negativeLogSineMass) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (low_negative_sum_integrable j hj)
      (Filter.Eventually.of_forall (fun t => Finset.sum_nonneg (fun _ _ => negativeLogSine_nonneg _))),
      low_negative_sum_integral j hj]
  calc
    _ ≤ haar {t | ENNReal.ofReal u ≤ g t} := measure_mono hinc
    _ ≤ (∫⁻ t, g t ∂haar)/ENNReal.ofReal u :=
      meas_ge_le_lintegral_div hm.aemeasurable (ENNReal.ofReal_ne_zero_iff.mpr hu) ENNReal.ofReal_ne_top
    _ = _ := by rw [hi, ← ENNReal.ofReal_div_of_pos hu]

theorem logSine_le_log_two (t : Torus) : logSine t ≤ Real.log 2 := by
  by_cases hz : ‖(1 : Complex)-fourier 1 t‖=0
  · simp only [logSine, hz, Real.log_zero]
    exact Real.log_nonneg (by norm_num)
  · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))
      (ConditionalSpectralAudit.FourierHarmonic.logSine_norm_le_two t)

theorem lowLogSineField_upper {q : Nat} (j : Fin q → Nat) (t : Torus) :
    lowLogSineField j t ≤ (q : Real)*Real.log 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (v : Fin q) _ => logSine_le_log_two (j v • t))
  simpa only [lowLogSineField, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

#print axioms actual_low_field_bad_measure
#print axioms lowLogSineField_upper
end ConditionalSpectralExtremes
