import TiltedDensityPowerRegularity
import TiltedCharacteristicFarGap

/-! Exact Fourier transforms and Fourier inversion for the actual finite
convolution densities. All identities below hold pointwise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal Convolution FourierTransform Topology

namespace ConditionalSpectralExtremes

theorem complexify_convolution (f g : ℝ → ℝ) :
    (fun x => ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x : ℂ)) =
      (fun x => (f x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => (g x : ℂ)) := by
  ext x
  change ((∫ y, f y*g (x-y) : ℝ) : ℂ) = ∫ y, (f y : ℂ)*(g (x-y) : ℂ)
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => Complex.ofReal_mul _ _)

theorem tiltedDensity_fourier {β : ℝ} (hβ : -1 < β) (ξ : ℝ) :
    𝓕 (fun x => (tiltedDensity β x : ℂ)) ξ = charFun (tiltedLogSineLaw β) (-2*Real.pi*ξ) := by
  rw [tiltedLogSineLaw_eq_withDensity β hβ,
    charFun_real_density_fourier _ (tiltedDensity_measurable β) (tiltedDensity_nonneg β)]
  field_simp

theorem tiltedDensityPower_fourier {β : ℝ} (hβ : -1 < β) (q : ℕ) (hq : 1 ≤ q) (ξ : ℝ) :
    𝓕 (fun x => (tiltedDensityPower β q x : ℂ)) ξ =
      charFun (tiltedLogSineLaw β) (-2*Real.pi*ξ)^q := by
  induction q, hq using Nat.le_induction with
  | base => simpa only [tiltedDensityPower_one, pow_one] using tiltedDensity_fourier hβ ξ
  | succ q hq ih =>
    rw [tiltedDensityPower_succ β q hq, complexify_convolution,
      Real.fourier_mul_convolution_eq (f₁ := fun x => (tiltedDensityPower β q x : ℂ))
        (f₂ := fun x => (tiltedDensity β x : ℂ)) (tiltedDensityPower_integrable hβ q).ofReal
        (tiltedDensity_integrable β hβ).ofReal, ih, tiltedDensity_fourier hβ, pow_succ]

theorem tiltedLogSineLaw_charFun_pow_integrable {β : ℝ} (hβ : -1 < β) (q : ℕ) (hq : 6 ≤ q) :
    Integrable (fun t => charFun (tiltedLogSineLaw β) t ^ q) := by
  let := tiltedLogSineLaw_isProbabilityMeasure β hβ
  apply (tiltedLogSineLaw_charFun_six_integrable hβ).mono'
    (continuous_charFun.pow q).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Pi.pow_apply, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (norm_charFun_le_one t) hq

theorem tiltedDensityPower_fourier_integrable {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 6 ≤ q) : Integrable (𝓕 (fun x => (tiltedDensityPower β q x : ℂ))) := by
  have hh := (tiltedLogSineLaw_charFun_pow_integrable hβ q hq).comp_mul_left'
    (show -2*Real.pi ≠ 0 by positivity)
  have he : 𝓕 (fun x => (tiltedDensityPower β q x : ℂ)) =
      (fun ξ => charFun (tiltedLogSineLaw β) (-2*Real.pi*ξ)^q) :=
    funext (tiltedDensityPower_fourier hβ q (by omega))
  rw [he]
  exact hh

theorem tiltedDensityPower_fourier_inversion {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 6 ≤ q) (x : ℝ) :
    (tiltedDensityPower β q x : ℂ) =
      𝓕⁻ (fun ξ => charFun (tiltedLogSineLaw β) (-2*Real.pi*ξ)^q) x := by
  have hh := (tiltedDensityPower_integrable hβ q).ofReal.fourierInv_fourier_eq (v := x)
    (tiltedDensityPower_fourier_integrable hβ q hq)
    ((Complex.continuous_ofReal.comp (tiltedDensityPower_continuous hβ q (by omega))).continuousAt)
  have he : 𝓕 (fun x => (tiltedDensityPower β q x : ℂ)) =
      (fun ξ => charFun (tiltedLogSineLaw β) (-2*Real.pi*ξ)^q) :=
    funext (tiltedDensityPower_fourier hβ q (by omega))
  rw [he] at hh
  exact hh.symm

#print axioms complexify_convolution
#print axioms tiltedDensity_fourier
#print axioms tiltedDensityPower_fourier
#print axioms tiltedLogSineLaw_charFun_pow_integrable
#print axioms tiltedDensityPower_fourier_integrable
#print axioms tiltedDensityPower_fourier_inversion

end ConditionalSpectralExtremes
