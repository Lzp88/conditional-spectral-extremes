import TiltedFourierNearIntegral
import TiltedFourierFarIntegral

/-! Uniform L1 Fourier convergence for the actual normalized sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem scaledCenteredCharFun_integrable {β : ℝ} (hβ : -1 < β) (q : ℕ) (hq : 6 ≤ q) :
    Integrable (scaledCenteredCharFun β q) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hqp).ne'
  apply ((tiltedLogSineLaw_charFun_norm_pow_integrable hβ q hq).comp_div hs).mono'
    (scaledCenteredCharFun_continuous hβ q).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_of_eq (by rw [scaledCenteredCharFun, norm_pow, centeredTiltedLogSineLaw_charFun_norm hβ])

theorem gaussianCharFun_integrable {β : ℝ} (hβ : -1 < β) : Integrable (gaussianCharFun β) := by
  have hv := lambda_deriv2_pos hβ
  convert (integrable_exp_neg_mul_sq (by positivity : 0 < (deriv^[2] lambda) β/2)).ofReal using 1
  ext t
  unfold gaussianCharFun
  congr 2
  ring

theorem gaussian_sqrt_tail_tendsto {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    Tendsto (fun q : ℕ => ∫ t in (Icc (-δ*Real.sqrt q) (δ*Real.sqrt q))ᶜ,
      Real.exp (-c*t^2)) atTop (𝓝 0) := by
  have hp : Tendsto (fun q : ℕ => δ*Real.sqrt q) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδ
  have hm : Tendsto (fun q : ℕ => -δ*Real.sqrt q) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp hp using 1
    ext q
    dsimp only [Function.comp_apply]
    ring
  have ht : Tendsto (fun q : ℕ => ∫ t in Icc (-δ*Real.sqrt q) (δ*Real.sqrt q), Real.exp (-c*t^2))
      atTop (𝓝 (∫ t : ℝ, Real.exp (-c*t^2))) :=
    (aecover_Icc (μ := (volume : Measure ℝ)) hm hp).integral_tendsto_of_countably_generated
      (integrable_exp_neg_mul_sq hc)
  simp_rw [setIntegral_compl measurableSet_Icc (integrable_exp_neg_mul_sq hc)]
  have hh : Tendsto
      (fun q : ℕ => (∫ t : ℝ, Real.exp (-c*t^2)) -
        ∫ t in Icc (-δ*Real.sqrt q) (δ*Real.sqrt q), Real.exp (-c*t^2))
      atTop (𝓝 ((∫ t : ℝ, Real.exp (-c*t^2)) - (∫ t : ℝ, Real.exp (-c*t^2)))) :=
    tendsto_const_nhds.sub ht
  rw [sub_self] at hh
  exact hh

/-- This is the full uniform Fourier L1 local-limit estimate; it refers to
the actual centered sum characteristic functions and the actual variance. -/
theorem scaledCenteredCharFun_uniform_L1_CLT
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    Tendsto (fun p : ℕ × ℝ =>
      ∫ t, ‖scaledCenteredCharFun p.2 p.1 t-gaussianCharFun p.2 t‖)
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
  obtain ⟨δ, hδ, hnear⟩ := scaledCenteredCharFun_near_integral_tendsto a b ha hab
  have hfar := scaledCenteredCharFun_far_integral_tendsto a b ha hab δ hδ
  obtain ⟨l, u, hl, hv⟩ := lambda_curvature_compact_bounds ha hab
  have hgfar : Tendsto (fun p : ℕ × ℝ =>
      ∫ t in (Icc (-δ*Real.sqrt p.1) (δ*Real.sqrt p.1))ᶜ, Real.exp (-(l/2)*t^2))
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) :=
    (gaussian_sqrt_tail_tendsto hδ (by positivity : 0 < l/2)).comp tendsto_fst
  have hsum := (hnear.add hfar).add hgfar
  simp only [add_zero] at hsum
  apply squeeze_zero' (Filter.Eventually.of_forall (fun p => integral_nonneg (fun t => norm_nonneg _)))
    ?_ hsum
  rw [eventually_prod_principal_iff]
  filter_upwards [eventually_ge_atTop 6] with q hq
  intro β hβ
  have hb := lt_of_lt_of_le ha hβ.1
  have hiψ := scaledCenteredCharFun_integrable hb q hq
  have hiG := gaussianCharFun_integrable hb
  have hiE := (hiψ.sub hiG).norm
  let K : Set ℝ := Icc (-δ*Real.sqrt q) (δ*Real.sqrt q)
  have hf : (∫ t in Kᶜ, ‖scaledCenteredCharFun β q t-gaussianCharFun β t‖) ≤
      (∫ t in Kᶜ, ‖scaledCenteredCharFun β q t‖) +
        ∫ t in Kᶜ, Real.exp (-(l/2)*t^2) := by
    rw [← integral_add hiψ.norm.integrableOn
      (integrable_exp_neg_mul_sq (by positivity : 0 < l/2)).integrableOn]
    apply integral_mono hiE.integrableOn
      (hiψ.norm.add (integrable_exp_neg_mul_sq (by positivity : 0 < l/2))).integrableOn
    intro t
    dsimp only
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (gaussianCharFun_norm_bound (hv β hβ).1 t))
  have he := integral_add_compl (s := K) measurableSet_Icc hiE
  simp only [Pi.sub_apply] at he
  rw [← he]
  linarith

#print axioms scaledCenteredCharFun_integrable
#print axioms gaussianCharFun_integrable
#print axioms gaussian_sqrt_tail_tendsto
#print axioms scaledCenteredCharFun_uniform_L1_CLT

end ConditionalSpectralExtremes
