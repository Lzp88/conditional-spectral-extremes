import PointwiseBridgeDefinitions
import TiltedLogSineDensity

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem tiltedLogSineProduct_eq_withDensity (β : ℝ) (q : ℕ) (hβ : -1 < β) :
    tiltedLogSineProduct β q =
      volume.withDensity (fun x : Fin q → ℝ => ∏ i, ENNReal.ofReal (tiltedDensity β (x i))) := by
  classical
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  apply Measure.pi_eq
  intro s hs
  let g : Fin q → ℝ → ℝ := fun i => (s i).indicator (tiltedDensity β)
  have hg (i : Fin q) : Integrable (g i) := (tiltedDensity_integrable β hβ).indicator (hs i)
  have hgn (i : Fin q) (x : ℝ) : 0 ≤ g i x := by
    exact Set.indicator_nonneg (fun y _ => tiltedDensity_nonneg β y) x
  have hp := Integrable.fintype_prod (μ := fun _ : Fin q => (volume : Measure ℝ)) hg
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he : (univ.pi s).indicator (fun x => ∏ i, ENNReal.ofReal (tiltedDensity β (x i))) =
      fun x => ENNReal.ofReal (∏ i, g i (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [Set.indicator_of_mem hx, ENNReal.ofReal_prod_of_nonneg (fun i _ => hgn i (x i))]
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      exact (Set.indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have hex : ∃ i, x i ∉ s i := by simpa only [mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := hex
      have hz : (∏ j, g j (x j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)
      rw [hz, ENNReal.ofReal_zero]
  rw [he]
  dsimp only
  rw [volume_pi, ← ofReal_integral_eq_lintegral_ofReal hp
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hgn i (x i)))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hgn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [tiltedLogSineLaw_eq_withDensity β hβ, withDensity_apply _ (hs i),
    ← lintegral_indicator (hs i), ofReal_integral_eq_lintegral_ofReal (hg i)
      (Filter.Eventually.of_forall (hgn i))]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s i <;> simp [g, hx]

theorem tiltedLogSineProduct_event_density (β : ℝ) (q : ℕ) (hβ : -1 < β)
    (E : Set (Fin q → ℝ)) (hE : MeasurableSet E) :
    tiltedLogSineProduct β q E =
      ∫⁻ x, E.indicator (fun x => ∏ i, ENNReal.ofReal (tiltedDensity β (x i))) x := by
  rw [tiltedLogSineProduct_eq_withDensity β q hβ, withDensity_apply _ hE,
    lintegral_indicator hE]

#print axioms tiltedLogSineProduct_eq_withDensity
#print axioms tiltedLogSineProduct_event_density

end ConditionalSpectralExtremes
