import UniformSmoothingNoise

/-! Exact support and exponential-moment bounds of the actual smoothing noise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic

theorem symmetricUniform_support (h : Real) :
    ∀ᵐ x ∂symmetricUniform h, |x| ≤ h := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioc (-h) h), |x| ≤ h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact abs_le.mpr ⟨hx.1.le, hx.2⟩
  exact Measure.ae_smul_measure hh _

theorem tenUniformNoise_support (δ : Real) (hδ : 0 < δ) :
    ∀ᵐ x ∂tenUniformNoise δ, |x| ≤ δ := by
  let _ := symmetricUniform_probability (δ/10) (by positivity)
  have hi (i : Fin 10) :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin 10 => symmetricUniform (δ/10)), |x i| ≤ δ/10 :=
    (measurePreserving_eval (fun _ : Fin 10 => symmetricUniform (δ/10)) i).quasiMeasurePreserving.tendsto_ae.eventually
      (symmetricUniform_support (δ/10))
  have hh := ae_all_iff.mpr hi
  rw [tenUniformNoise, ae_map_iff (by fun_prop) (measurableSet_le measurable_abs measurable_const)]
  filter_upwards [hh] with x hx
  calc
    |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 10, δ/10 := Finset.sum_le_sum (fun i _ => hx i)
    _ = δ := by simp; ring

theorem tenUniformNoise_exp_integrable (δ r : Real) (hδ : 0 < δ) :
    Integrable (fun x => Real.exp (r*x)) (tenUniformNoise δ) := by
  let _ := tenUniformNoise_probability δ hδ
  apply (integrable_const (Real.exp (|r| * δ))).mono' (by fun_prop)
  filter_upwards [tenUniformNoise_support δ hδ] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r*x ≤ |r*x| := le_abs_self _
    _ = |r| * |x| := abs_mul _ _
    _ ≤ |r| * δ := mul_le_mul_of_nonneg_left hx (abs_nonneg _)

theorem tenUniformNoise_mgf_bound (δ r : Real) (hδ : 0 < δ) :
    mgf id (tenUniformNoise δ) r ≤ Real.exp (|r| * δ) := by
  let _ := tenUniformNoise_probability δ hδ
  unfold mgf
  calc
    _ ≤ ∫ _ : Real, Real.exp (|r| * δ) ∂tenUniformNoise δ := by
      apply integral_mono_ae (tenUniformNoise_exp_integrable δ r hδ) (integrable_const _)
      filter_upwards [tenUniformNoise_support δ hδ] with x hx
      apply Real.exp_le_exp.mpr
      calc
        r*x ≤ |r*x| := le_abs_self _
        _ = |r| * |x| := abs_mul _ _
        _ ≤ |r| * δ := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = _ := by simp

#print axioms tenUniformNoise_support
#print axioms tenUniformNoise_mgf_bound
end ConditionalSpectralAudit.FourierHarmonic
