import TiltedLocalLimitInversion

/-! The uniform density local central limit theorem for the actual tilted
log-sine convolution powers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology

namespace ConditionalSpectralExtremes

theorem scaledTiltedDensity_error_bound {β : ℝ} (hβ : -1 < β)
    (q : ℕ) (hq : 6 ≤ q) (x : ℝ) :
    |scaledTiltedDensity β q x-gaussianLimitDensity β x| ≤
      |(-2*Real.pi)⁻¹| * ∫ t, ‖scaledCenteredCharFun β q t-gaussianCharFun β t‖ := by
  have hs := (scaledCenteredCharFun_integrable hβ q hq).comp_mul_left'
    (by positivity : -2*Real.pi ≠ 0)
  have hg := (gaussianCharFun_integrable hβ).comp_mul_left'
    (by positivity : -2*Real.pi ≠ 0)
  have hh := fourierInv_difference_bound hs hg x
  rw [← scaledTiltedDensity_fourier_inversion hβ q hq,
    ← gaussianLimitDensity_fourier_inversion hβ] at hh
  have he : (∫ ξ, ‖scaledCenteredCharFun β q (-2*Real.pi*ξ)-gaussianCharFun β (-2*Real.pi*ξ)‖) =
      |(-2*Real.pi)⁻¹| * ∫ t, ‖scaledCenteredCharFun β q t-gaussianCharFun β t‖ := by
    simpa only [smul_eq_mul] using Measure.integral_comp_mul_left
      (fun t => ‖scaledCenteredCharFun β q t-gaussianCharFun β t‖) (-2*Real.pi)
  rw [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hh
  exact hh

/-- The actual density local CLT is uniform in every real spatial argument
and simultaneously in every tilt in a fixed compact subset of (-1,infinity). -/
theorem tiltedDensityPower_uniform_local_CLT
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 6 ≤ N ∧ ∀ q : ℕ, N ≤ q → ∀ β ∈ Icc a b, ∀ x : ℝ,
      |Real.sqrt q * tiltedDensityPower β q
        ((q : ℝ)*deriv lambda β + Real.sqrt q*x) - gaussianLimitDensity β x| < ε := by
  have ht := (scaledCenteredCharFun_uniform_L1_CLT a b ha hab).const_mul |(-2*Real.pi)⁻¹|
  simp only [mul_zero] at ht
  have he := ht.eventually (eventually_lt_nhds hε)
  rw [eventually_prod_principal_iff] at he
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 6, le_max_right _ _, ?_⟩
  intro q hq β hβ x
  have hq6 : 6 ≤ q := (le_max_right N 6).trans hq
  have hqN : N ≤ q := (le_max_left N 6).trans hq
  exact (scaledTiltedDensity_error_bound (lt_of_lt_of_le ha hβ.1) q hq6 x).trans_lt
    (hN q hqN β hβ)

#print axioms scaledTiltedDensity_error_bound
#print axioms tiltedDensityPower_uniform_local_CLT

end ConditionalSpectralExtremes
