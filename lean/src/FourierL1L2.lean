import Mathlib

/-! Bridge between the actual integrable-function Fourier integral and mathlib's
L2 Plancherel isometry. No pointwise Fourier/L2 identification is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory SchwartzMap
open scoped ENNReal FourierTransform Topology

namespace ConditionalSpectralExtremes

theorem fourier_integral_pairing {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, 𝓕 f x * g x) = ∫ x, f x * 𝓕 g x := by
  change (∫ x, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f x * g x) =
    ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x
  simpa using (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg)

theorem fourier_L1_L2_ae {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (fun x => (𝓕 (hf2.toLp f) : Lp ℂ 2 volume) x) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (𝓕 (hf2.toLp f))).locallyIntegrable (by norm_num)
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1).locallyIntegrable
  · intro g hg hgc
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hg₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM ∘ g) :=
      Complex.ofRealCLM.contDiff.comp hg
    let G : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂
    have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T G)
      (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
    simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
    calc
      (∫ x, g x • (𝓕 (hf2.toLp f) : Lp ℂ 2 volume) x) =
        ∫ x, G x * (𝓕 (hf2.toLp f) : Lp ℂ 2 volume) x := by rfl
      _ = ∫ x, (𝓕 G) x * (hf2.toLp f) x := he.symm
      _ = ∫ x, (𝓕 G) x * f x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
      _ = ∫ x, f x * 𝓕 (G : ℝ → ℂ) x := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        rw [SchwartzMap.fourier_coe]
        exact mul_comm _ _
      _ = ∫ x, 𝓕 f x * G x := (fourier_integral_pairing hf1 G.integrable).symm
      _ = ∫ x, g x • 𝓕 f x := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change 𝓕 f x * (g x : ℂ) = (g x : ℂ) * 𝓕 f x
        ring

theorem fourier_memLp_two {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume :=
  MemLp.ae_eq (fourier_L1_L2_ae hf1 hf2)
    (Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))

theorem integral_norm_sq_eq_norm_toLp_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  calc
    (∫ x, ‖f x‖ ^ 2) = ∫ x, inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (L2.inner_def _ _).symm
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem fourier_integral_norm_sq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (∫ x, ‖𝓕 f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  have hF := fourier_memLp_two hf1 hf2
  have heq : hF.toLp (𝓕 f) = 𝓕 (hf2.toLp f) := by
    apply Lp.ext
    exact hF.coeFn_toLp.trans (fourier_L1_L2_ae hf1 hf2).symm
  rw [integral_norm_sq_eq_norm_toLp_sq hF, heq, Lp.norm_fourier_eq,
    integral_norm_sq_eq_norm_toLp_sq hf2]

#print axioms fourier_integral_pairing
#print axioms fourier_L1_L2_ae
#print axioms fourier_memLp_two
#print axioms integral_norm_sq_eq_norm_toLp_sq
#print axioms fourier_integral_norm_sq

end ConditionalSpectralExtremes
