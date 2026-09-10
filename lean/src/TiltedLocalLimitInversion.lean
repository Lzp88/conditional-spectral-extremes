import TiltedCharacteristicL1CLT
import FourierAffineInversion

/-! Exact Fourier inverse representations for the actual normalized density
and its variance-matched Gaussian limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal FourierTransform Topology

namespace ConditionalSpectralExtremes

def scaledTiltedDensity (β : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt q * tiltedDensityPower β q ((q : ℝ)*deriv lambda β + Real.sqrt q*x)

def gaussianLimitDensity (β : ℝ) : ℝ → ℝ :=
  gaussianPDFReal 0 (Real.toNNReal ((deriv^[2] lambda) β))

theorem centeredTiltedLogSineLaw_charFun {β : ℝ} (hβ : -1 < β) (t : ℝ) :
    charFun (centeredTiltedLogSineLaw β) t = charFun (tiltedLogSineLaw β) t *
      Complex.exp (((-(deriv lambda β*t) : ℝ) : ℂ)*Complex.I) := by
  let := tiltedLogSineLaw_isProbabilityMeasure β hβ
  change charFun ((tiltedLogSineLaw β).map (fun x => x + -deriv lambda β)) t = _
  rw [charFun_map_add_const]
  congr 2
  simp only [Real.inner_apply]
  push_cast
  ring

theorem scaledTiltedDensity_fourier_inversion {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 6 ≤ q) (x : ℝ) :
    (scaledTiltedDensity β q x : ℂ) =
      𝓕⁻ (fun ξ => scaledCenteredCharFun β q (-2*Real.pi*ξ)) x := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  let f : ℝ → ℂ := fun ξ => charFun (tiltedLogSineLaw β) (-2*Real.pi*ξ)^q
  have hh := fourierInv_affine f ((q : ℝ)*deriv lambda β) (Real.sqrt q) x hs
  have he : (fun ξ => Complex.exp
      (((2*Real.pi*((q : ℝ)*deriv lambda β)*ξ/Real.sqrt q : ℝ) : ℂ)*Complex.I)*f (ξ/Real.sqrt q)) =
      (fun ξ => scaledCenteredCharFun β q (-2*Real.pi*ξ)) := by
    ext ξ
    rw [scaledCenteredCharFun, centeredTiltedLogSineLaw_charFun hβ, mul_pow, ← Complex.exp_nat_mul]
    dsimp only [f]
    have ht : (-2*Real.pi*ξ)/Real.sqrt q = -2*Real.pi*(ξ/Real.sqrt q) := by ring
    rw [ht, mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  rw [he] at hh
  dsimp only [f] at hh
  rw [← tiltedDensityPower_fourier_inversion hβ q hq] at hh
  simpa only [scaledTiltedDensity, Complex.ofReal_mul] using hh.symm

theorem gaussianLimitDensity_continuous (β : ℝ) : Continuous (gaussianLimitDensity β) := by
  unfold gaussianLimitDensity gaussianPDFReal
  fun_prop

theorem gaussianLimitDensity_integrable (β : ℝ) : Integrable (gaussianLimitDensity β) :=
  integrable_gaussianPDFReal _ _

theorem gaussianLimitDensity_fourier {β : ℝ} (hβ : -1 < β) (ξ : ℝ) :
    𝓕 (fun x => (gaussianLimitDensity β x : ℂ)) ξ = gaussianCharFun β (-2*Real.pi*ξ) := by
  have hv := lambda_deriv2_pos hβ
  have hv0 : Real.toNNReal ((deriv^[2] lambda) β) ≠ 0 := (Real.toNNReal_pos.mpr hv).ne'
  have hh := charFun_real_density_fourier (gaussianLimitDensity β)
    (gaussianLimitDensity_continuous β).measurable (gaussianPDFReal_nonneg _ _) (-2*Real.pi*ξ)
  change charFun (volume.withDensity (gaussianPDF 0 (Real.toNNReal ((deriv^[2] lambda) β))))
    (-2*Real.pi*ξ) = _ at hh
  rw [← gaussianReal_of_var_ne_zero 0 hv0, charFun_gaussianReal] at hh
  have ht : -(-2*Real.pi*ξ)/(2*Real.pi) = ξ := by field_simp
  rw [ht] at hh
  rw [← hh, gaussianCharFun]
  rw [Real.coe_toNNReal _ hv.le]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem gaussianLimitDensity_fourier_inversion {β : ℝ} (hβ : -1 < β) (x : ℝ) :
    (gaussianLimitDensity β x : ℂ) =
      𝓕⁻ (fun ξ => gaussianCharFun β (-2*Real.pi*ξ)) x := by
  have he : 𝓕 (fun x => (gaussianLimitDensity β x : ℂ)) =
      (fun ξ => gaussianCharFun β (-2*Real.pi*ξ)) := funext (gaussianLimitDensity_fourier hβ)
  have hi : Integrable (𝓕 (fun x => (gaussianLimitDensity β x : ℂ))) := by
    rw [he]
    exact (gaussianCharFun_integrable hβ).comp_mul_left' (by positivity : -2*Real.pi ≠ 0)
  have hh := (gaussianLimitDensity_integrable β).ofReal.fourierInv_fourier_eq (v := x) hi
    ((Complex.continuous_ofReal.comp (gaussianLimitDensity_continuous β)).continuousAt)
  rw [he] at hh
  exact hh.symm

#print axioms centeredTiltedLogSineLaw_charFun
#print axioms scaledTiltedDensity_fourier_inversion
#print axioms gaussianLimitDensity_continuous
#print axioms gaussianLimitDensity_integrable
#print axioms gaussianLimitDensity_fourier
#print axioms gaussianLimitDensity_fourier_inversion

end ConditionalSpectralExtremes
