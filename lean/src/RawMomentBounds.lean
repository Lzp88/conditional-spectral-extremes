import RawMomentTonelli

/-! Real moments are measurable and integrable under any finite angle measure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem rawFirstMoment_uniform_bound (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i)) (t : AddCircle (1 : Real)) :
    rawFirstMoment p n κ G δ q lo hi t ≤ Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ) := by
  let _ := harmonicMiddleSampleLaw_probability lo hi (fun j => q (j+1)) (FineScales.count p n) hH
  have hh := lintegral_mono (μ := harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n))
    (fun x => rawPathQuality_uniform_bound p n κ G δ hκ hδ q t x)
  simp only [lintegral_const, measure_univ, mul_one] at hh
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (Real.exp_pos _).le)

theorem rawSecondMoment_uniform_bound (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i)) (t u : AddCircle (1 : Real)) :
    rawSecondMoment p n κ G δ q lo hi t u ≤ (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))^2 := by
  let _ := harmonicMiddleSampleLaw_probability lo hi (fun j => q (j+1)) (FineScales.count p n) hH
  have hh := lintegral_mono (μ := harmonicMiddleSampleLaw lo hi (fun j => q (j+1)) (FineScales.count p n))
    (fun x => mul_le_mul' (rawPathQuality_uniform_bound p n κ G δ hκ hδ q t x)
      (rawPathQuality_uniform_bound p n κ G δ hκ hδ q u x))
  simp only [lintegral_const, measure_univ, mul_one] at hh
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hh
  simpa only [rawSecondMoment, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, pow_two] using! hr

theorem rawFirstMoment_integrable (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i))
    (μ : Measure (AddCircle (1 : Real))) [IsFiniteMeasure μ] :
    Integrable (rawFirstMoment p n κ G δ q lo hi) μ := by
  apply (integrable_const (Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))).mono'
    (rawFirstMoment_measurable p n κ G δ hκ hδ q lo hi).aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ rawFirstMoment p n κ G δ q lo hi t from ENNReal.toReal_nonneg)]
  exact rawFirstMoment_uniform_bound p n κ G δ hκ hδ q lo hi hH t

theorem rawSecondMoment_integrable (p : FineScales.Parameters) (n : Nat)
    (κ G δ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q lo hi : Nat → Nat)
    (hH : ∀ i < FineScales.count p n, 0 < harmonicMass (lo i) (hi i))
    (μ : Measure (AddCircle (1 : Real) × AddCircle (1 : Real))) [IsFiniteMeasure μ] :
    Integrable (fun z => rawSecondMoment p n κ G δ q lo hi z.1 z.2) μ := by
  apply (integrable_const ((Real.exp (criticalPoint κ*(FineScales.count p n : Real)*δ))^2)).mono'
    (rawSecondMoment_measurable p n κ G δ hκ hδ q lo hi).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ rawSecondMoment p n κ G δ q lo hi z.1 z.2 from ENNReal.toReal_nonneg)]
  exact rawSecondMoment_uniform_bound p n κ G δ hκ hδ q lo hi hH z.1 z.2

#print axioms rawFirstMoment_integrable
#print axioms rawSecondMoment_integrable
end ConditionalSpectralAudit.FourierHarmonic
