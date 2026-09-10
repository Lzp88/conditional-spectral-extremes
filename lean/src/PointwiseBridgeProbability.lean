import PointwiseBridgeSplit
import FiniteDensityProduct

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def centeredMaximumEvent (β : ℝ) (q : ℕ) (w : ℝ) : Set (Fin q → ℝ) :=
  {x | ∃ j ≤ q, w ≤ |centeredLogSinePartial β j x|}

theorem centeredMaximumEvent_measurable (β : ℝ) (q : ℕ) (w : ℝ) :
    MeasurableSet (centeredMaximumEvent β q w) := by
  simp only [centeredMaximumEvent, ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases hj : j ≤ q
  · simp only [hj, true_and]
    apply measurableSet_le measurable_const
    unfold centeredLogSinePartial FiniteWalk.partialSum centeredLogSine
    fun_prop
  · simp only [hj, false_and, ofPred_false]
    exact MeasurableSet.empty

theorem pointwiseBridge_first_probability_bound (β : ℝ) (hβ : -1 < β)
    (m n : ℕ) (d : ℝ) (E : Set (Fin m → ℝ)) (hE : MeasurableSet E)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ u : ℝ, pointwiseBridge (tiltedDensity β) n u univ ≤ C) :
    pointwiseBridge (tiltedDensity β) (m+n) d (bridgeFirstEvent m n E) ≤
      C * tiltedLogSineProduct β m E := by
  rw [tiltedLogSineProduct_event_density β m hβ E hE]
  exact pointwiseBridge_first_le_unused_sup _ (tiltedDensity_measurable β) m n d E hE C hC hbound

theorem pointwiseBridge_first_maximal_bound (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ β ∈ Icc a b, ∀ m : ℕ, 0 < m →
      ∀ w : ℝ, 1 ≤ w → w ≤ c*(m : ℝ) → ∀ n : ℕ, ∀ d : ℝ, ∀ C : ℝ≥0∞,
      C ≠ ∞ → (∀ u : ℝ, pointwiseBridge (tiltedDensity β) n u univ ≤ C) →
      pointwiseBridge (tiltedDensity β) (m+n) d
        (bridgeFirstEvent m n (centeredMaximumEvent β m w)) ≤
          C * ENNReal.ofReal (2 * Real.exp (-c*w^2/(m : ℝ))) := by
  obtain ⟨c, hc, hh⟩ := walk_maximal_deviation a b ha hab
  refine ⟨c, hc, ?_⟩
  intro β hβ m hm w hw hwrange n d C hC hbound
  have hb := lt_of_lt_of_le ha hβ.1
  let _ := tiltedLogSineProduct_isProbabilityMeasure β m hb
  apply (pointwiseBridge_first_probability_bound β hb m n d _
    (centeredMaximumEvent_measurable β m w) C hC hbound).trans
  have hprob := ENNReal.ofReal_le_ofReal (hh β hβ m hm w hw hwrange)
  rw [ofReal_measureReal] at hprob
  gcongr
  exact hprob

#print axioms centeredMaximumEvent_measurable
#print axioms pointwiseBridge_first_probability_bound
#print axioms pointwiseBridge_first_maximal_bound

end ConditionalSpectralExtremes
