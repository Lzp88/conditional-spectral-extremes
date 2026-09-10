import Mathlib

/-! A layer-cake fourth-moment bound with an explicit convergent envelope.
It will be instantiated with the actual normalized Poisson path maximum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal

namespace ConditionalSpectralExtremes.BlockCounts

def fourthMomentEnvelope (t : ℝ) : ℝ := 4*t^3*Real.exp (-t/2)

theorem fourthMomentEnvelope_integrable : IntegrableOn fourthMomentEnvelope (Ioi 0) := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 3) (p := 1) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
  have hi : Integrable (fun t : ℝ => t^3*Real.exp (-(1/2)*t)) (volume.restrict (Ioi 0)) := by
    norm_num [IntegrableOn] at hh ⊢
    exact hh
  change Integrable fourthMomentEnvelope (volume.restrict (Ioi 0))
  apply (hi.const_mul 4).congr
  apply ae_of_all
  intro t
  dsimp only [fourthMomentEnvelope]
  rw [show -(1/2 : ℝ)*t = -t/2 by ring]
  ring

theorem fourthMomentEnvelope_integral : (∫ t in Ioi 0, fourthMomentEnvelope t) = 384 := by
  have hG : Real.Gamma 4 = 6 := by norm_num
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := 1/2) (by norm_num) (by norm_num)
  norm_num [hG] at hh
  have he : fourthMomentEnvelope = fun t : ℝ => 4*(t^3*Real.exp (-(1/2*t))) := by
    funext t
    unfold fourthMomentEnvelope
    rw [show -t/2 = -((1/2 : ℝ)*t) by ring]
    ring
  rw [he, integral_const_mul, hh]
  norm_num

theorem fourth_moment_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (hfn : ∀ ω, 0 ≤ f ω) (A : ℝ) (hA : 0 ≤ A)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ f ω} ≤ A*Real.exp (-t/2)) :
    Integrable (fun ω => (f ω)^4) μ ∧ (∫ ω, (f ω)^4 ∂μ) ≤ 384*A := by
  have hG (x : ℝ) : (∫ t in 0..x, 4*t^3) = x^4 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hgn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ 4*t^3 :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by have ht0 : 0 < t := ht; positivity)
  have henvn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ A*fourthMomentEnvelope t :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := ht
      dsimp [fourthMomentEnvelope]
      positivity)
  have hpow : 0 ≤ᵐ[μ] fun ω => (f ω)^4 := ae_of_all _ (fun ω => by positivity)
  have hlayer := lintegral_comp_eq_lintegral_meas_le_mul (f := f) (g := fun t : ℝ => 4*t^3)
    μ (ae_of_all _ hfn) hf.aemeasurable
    (fun t _ => (show Continuous (fun t : ℝ => 4*t^3) by fun_prop).intervalIntegrable 0 t) hgn
  simp_rw [hG] at hlayer
  have hbound : (∫⁻ ω, ENNReal.ofReal ((f ω)^4) ∂μ) ≤ ENNReal.ofReal (384*A) := by
    calc
      _ = ∫⁻ t in Ioi 0, μ {ω | t ≤ f ω}*ENNReal.ofReal (4*t^3) := hlayer
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (A*fourthMomentEnvelope t) := by
        apply lintegral_mono_ae
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := ht
        rw [show μ {ω | t ≤ f ω} = ENNReal.ofReal (μ.real {ω | t ≤ f ω}) from
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
          ← ENNReal.ofReal_mul (measureReal_nonneg)]
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_right (htail t ht) (show 0 ≤ 4*t^3 by positivity)
        dsimp only [fourthMomentEnvelope]
        nlinarith
      _ = ENNReal.ofReal (∫ t in Ioi 0, A*fourthMomentEnvelope t) :=
        (ofReal_integral_eq_lintegral_ofReal (fourthMomentEnvelope_integrable.const_mul A) henvn).symm
      _ = _ := by rw [integral_const_mul, fourthMomentEnvelope_integral, mul_comm A]
  have hi : Integrable (fun ω => (f ω)^4) μ :=
    ⟨(hf.pow_const 4).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hpow).mpr (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [← integral_eq_lintegral_of_nonneg_ae hpow hi.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 384*A)] at hh
  exact hh

#print axioms fourthMomentEnvelope_integrable
#print axioms fourthMomentEnvelope_integral
#print axioms fourth_moment_of_exponential_tail

end ConditionalSpectralExtremes.BlockCounts
