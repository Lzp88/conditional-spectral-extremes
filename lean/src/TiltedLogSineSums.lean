import TiltedLogSine

/-!
Actual finite iid tilted log-sine product spaces and their sum moment
generating functions. Every factor is the normalized tilted Haar
pushforward law from TiltedLogSine. No independence or mgf identity is
postulated. The tail bounds below are direct exponential Markov bounds.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ConditionalSpectralExtremes

def tiltedLogSineProduct (β : ℝ) (q : ℕ) : Measure (Fin q → ℝ) :=
  Measure.pi (fun _ => tiltedLogSineLaw β)

theorem tiltedLogSineProduct_isProbabilityMeasure (β : ℝ) (q : ℕ) (hβ : -1 < β) :
    IsProbabilityMeasure (tiltedLogSineProduct β q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  unfold tiltedLogSineProduct
  infer_instance

theorem tiltedLogSineProduct_independent (β : ℝ) (q : ℕ) (hβ : -1 < β) :
    iIndepFun (fun i (ω : Fin q → ℝ) => ω i) (tiltedLogSineProduct β q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

theorem tiltedLogSineProduct_marginal (β : ℝ) (q : ℕ) (hβ : -1 < β) (i : Fin q) :
    (tiltedLogSineProduct β q).map (fun ω => ω i) = tiltedLogSineLaw β := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  exact (measurePreserving_eval (fun _ : Fin q => tiltedLogSineLaw β) i).map_eq

def logSineSum {q : ℕ} (ω : Fin q → ℝ) : ℝ := ∑ i, ω i

def centeredLogSineSum (β : ℝ) {q : ℕ} (ω : Fin q → ℝ) : ℝ :=
  ∑ i, centeredLogSine β (ω i)

theorem centeredLogSineSum_eq (β : ℝ) (q : ℕ) (ω : Fin q → ℝ) :
    centeredLogSineSum β ω = logSineSum ω - (q : ℝ) * deriv lambda β := by
  simp [centeredLogSineSum, centeredLogSine, logSineSum, Finset.sum_sub_distrib]

theorem logSineSum_exp_integrable (β t : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) :
    Integrable (fun ω => Real.exp (t * logSineSum ω)) (tiltedLogSineProduct β q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  simpa only [logSineSum, tiltedLogSineProduct, Finset.mul_sum, Real.exp_sum] using
    Integrable.fintype_prod (fun _ : Fin q => tiltedLogSineLaw_exp_integrable β t hβ ht)

theorem logSineSum_mgf (β t : ℝ) (q : ℕ) (hβ : -1 < β) (ht : -1 < β + t) :
    mgf logSineSum (tiltedLogSineProduct β q) t =
      Real.exp ((q : ℝ) * (lambda (β + t) - lambda β)) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  simp only [mgf, logSineSum, tiltedLogSineProduct, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (ι := Fin q) (μ := tiltedLogSineLaw β)
    (fun x : ℝ => Real.exp (t * x))]
  simp only [Fintype.card_fin]
  change (mgf id (tiltedLogSineLaw β) t) ^ q = _
  rw [tiltedLogSineLaw_mgf_lambda β t hβ ht, ← Real.exp_nat_mul]

theorem centeredLogSineSum_exp_integrable (β t : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) :
    Integrable (fun ω => Real.exp (t * centeredLogSineSum β ω))
      (tiltedLogSineProduct β q) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  simpa only [centeredLogSineSum, tiltedLogSineProduct, Finset.mul_sum, Real.exp_sum] using
    Integrable.fintype_prod (fun _ : Fin q => centeredLogSine_exp_integrable β t hβ ht)

theorem centeredLogSineSum_mgf (β t : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) :
    mgf (centeredLogSineSum β) (tiltedLogSineProduct β q) t =
      Real.exp ((q : ℝ) * (lambda (β + t) - lambda β - t * deriv lambda β)) := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  simp only [mgf, centeredLogSineSum, tiltedLogSineProduct, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (ι := Fin q) (μ := tiltedLogSineLaw β)
    (fun x : ℝ => Real.exp (t * centeredLogSine β x))]
  simp only [Fintype.card_fin]
  change (mgf (centeredLogSine β) (tiltedLogSineLaw β) t) ^ q = _
  rw [centeredLogSine_mgf β t hβ ht, ← Real.exp_nat_mul]

theorem logSineSum_chernoff_upper (β t a : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) (ht0 : 0 ≤ t) :
    (tiltedLogSineProduct β q).real {ω | a ≤ logSineSum ω} ≤
      Real.exp (-t * a + (q : ℝ) * (lambda (β + t) - lambda β)) := by
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hβ
  have hh := measure_ge_le_exp_mul_mgf a ht0 (logSineSum_exp_integrable β t q hβ ht)
  rwa [logSineSum_mgf β t q hβ ht, ← Real.exp_add] at hh

theorem logSineSum_chernoff_lower (β t a : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) (ht0 : t ≤ 0) :
    (tiltedLogSineProduct β q).real {ω | logSineSum ω ≤ a} ≤
      Real.exp (-t * a + (q : ℝ) * (lambda (β + t) - lambda β)) := by
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hβ
  have hh := measure_le_le_exp_mul_mgf a ht0 (logSineSum_exp_integrable β t q hβ ht)
  rwa [logSineSum_mgf β t q hβ ht, ← Real.exp_add] at hh

theorem centeredLogSineSum_chernoff_upper (β t a : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) (ht0 : 0 ≤ t) :
    (tiltedLogSineProduct β q).real {ω | a ≤ centeredLogSineSum β ω} ≤
      Real.exp (-t * a + (q : ℝ) *
        (lambda (β + t) - lambda β - t * deriv lambda β)) := by
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hβ
  have hh := measure_ge_le_exp_mul_mgf a ht0
    (centeredLogSineSum_exp_integrable β t q hβ ht)
  rwa [centeredLogSineSum_mgf β t q hβ ht, ← Real.exp_add] at hh

theorem centeredLogSineSum_chernoff_lower (β t a : ℝ) (q : ℕ)
    (hβ : -1 < β) (ht : -1 < β + t) (ht0 : t ≤ 0) :
    (tiltedLogSineProduct β q).real {ω | centeredLogSineSum β ω ≤ a} ≤
      Real.exp (-t * a + (q : ℝ) *
        (lambda (β + t) - lambda β - t * deriv lambda β)) := by
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hβ
  have hh := measure_le_le_exp_mul_mgf a ht0
    (centeredLogSineSum_exp_integrable β t q hβ ht)
  rwa [centeredLogSineSum_mgf β t q hβ ht, ← Real.exp_add] at hh

#print axioms tiltedLogSineProduct_isProbabilityMeasure
#print axioms tiltedLogSineProduct_independent
#print axioms tiltedLogSineProduct_marginal
#print axioms centeredLogSineSum_eq
#print axioms logSineSum_exp_integrable
#print axioms logSineSum_mgf
#print axioms centeredLogSineSum_exp_integrable
#print axioms centeredLogSineSum_mgf
#print axioms logSineSum_chernoff_upper
#print axioms logSineSum_chernoff_lower
#print axioms centeredLogSineSum_chernoff_upper
#print axioms centeredLogSineSum_chernoff_lower

end ConditionalSpectralExtremes
