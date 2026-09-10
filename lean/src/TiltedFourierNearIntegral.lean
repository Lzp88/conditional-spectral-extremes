import TiltedScaledCharacteristic

/-! Uniform dominated convergence of the actual Fourier error on the growing
central frequency region. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem scaledCenteredCharFun_continuous {β : ℝ} (hβ : -1 < β) (n : ℕ) :
    Continuous (scaledCenteredCharFun β n) := by
  let := centeredTiltedLogSineLaw_probability hβ
  exact ((continuous_charFun.comp (continuous_id.div_const (Real.sqrt n))).pow n)

theorem gaussianCharFun_continuous (β : ℝ) : Continuous (gaussianCharFun β) := by
  unfold gaussianCharFun
  fun_prop

theorem scaledCenteredCharFun_gaussian_bound {β δ c : ℝ} (hβ : -1 < β)
    (hg : ∀ t : ℝ, |t| ≤ δ → ‖charFun (tiltedLogSineLaw β) t‖ ≤ Real.exp (-c*t^2))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : |t| ≤ δ*Real.sqrt n) :
    ‖scaledCenteredCharFun β n t‖ ≤ Real.exp (-c*t^2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnp
  have hfreq : |t/Real.sqrt n| ≤ δ := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact ht
  unfold scaledCenteredCharFun
  rw [norm_pow, centeredTiltedLogSineLaw_charFun_norm hβ]
  apply (pow_le_pow_left₀ (norm_nonneg _) (hg _ hfreq) n).trans_eq
  rw [← Real.exp_nat_mul]
  congr 1
  rw [div_pow, Real.sq_sqrt hnp.le]
  field_simp

theorem gaussianCharFun_norm_bound {β l : ℝ} (hv : l ≤ (deriv^[2] lambda) β) (t : ℝ) :
    ‖gaussianCharFun β t‖ ≤ Real.exp (-(l/2)*t^2) := by
  rw [gaussianCharFun, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hv (sq_nonneg t)
  nlinarith

theorem scaledCenteredCharFun_near_integral_tendsto
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun p : ℕ × ℝ => ∫ t in Icc (-δ*Real.sqrt p.1) (δ*Real.sqrt p.1),
        ‖scaledCenteredCharFun p.2 p.1 t-gaussianCharFun p.2 t‖)
        (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
  obtain ⟨δ, c, hδ, hc, hgb⟩ := tiltedLogSineLaw_charFun_uniform_gaussian_bound a b ha hab
  obtain ⟨l, u, hl, hv⟩ := lambda_curvature_compact_bounds ha hab
  let F : (ℕ × ℝ) → ℝ → ℝ := fun p =>
    (Icc (-δ*Real.sqrt p.1) (δ*Real.sqrt p.1)).indicator
      (fun t => ‖scaledCenteredCharFun p.2 p.1 t-gaussianCharFun p.2 t‖)
  have hD := tendsto_integral_filter_of_dominated_convergence
    (F := F) (f := fun _ : ℝ => (0 : ℝ))
    (fun t => Real.exp (-c*t^2) + Real.exp (-(l/2)*t^2))
    (show ∀ᶠ p : ℕ × ℝ in atTop ×ˢ 𝓟 (Icc a b), AEStronglyMeasurable (F p) volume from by
      rw [eventually_prod_principal_iff]
      apply Filter.Eventually.of_forall
      intro n β hβ
      exact (((scaledCenteredCharFun_continuous (lt_of_lt_of_le ha hβ.1) n).sub
        (gaussianCharFun_continuous β)).norm.aestronglyMeasurable).indicator measurableSet_Icc)
    (show ∀ᶠ p : ℕ × ℝ in atTop ×ˢ 𝓟 (Icc a b), ∀ᵐ t : ℝ,
        ‖F p t‖ ≤ Real.exp (-c*t^2) + Real.exp (-(l/2)*t^2) from by
      rw [eventually_prod_principal_iff]
      filter_upwards [eventually_ge_atTop 1] with n hn
      intro β hβ
      apply Filter.Eventually.of_forall
      intro t
      dsimp only [F]
      by_cases ht : t ∈ Icc (-δ*Real.sqrt n) (δ*Real.sqrt n)
      · rw [indicator_of_mem ht, Real.norm_of_nonneg (norm_nonneg _)]
        apply (norm_sub_le _ _).trans
        apply add_le_add
        · exact scaledCenteredCharFun_gaussian_bound (lt_of_lt_of_le ha hβ.1) (hgb β hβ) n hn t
            (abs_le.mpr (by simpa only [neg_mul, mem_Icc] using ht))
        · exact gaussianCharFun_norm_bound (hv β hβ).1 t
      · rw [indicator_of_notMem ht, norm_zero]
        positivity)
    ((integrable_exp_neg_mul_sq hc).add (integrable_exp_neg_mul_sq (by positivity : 0 < l/2)))
    (show ∀ᵐ t : ℝ, Tendsto (fun p => F p t) (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) from by
      apply Filter.Eventually.of_forall
      intro t
      apply squeeze_zero' (Filter.Eventually.of_forall (fun p => ?_))
        (Filter.Eventually.of_forall (fun p => ?_))
        (scaledCenteredCharFun_uniform_pointwise a b ha hab t)
      · dsimp only [F]
        by_cases ht : t ∈ Icc (-δ*Real.sqrt p.1) (δ*Real.sqrt p.1)
        · rw [indicator_of_mem ht]; exact norm_nonneg _
        · rw [indicator_of_notMem ht]
      · dsimp only [F]
        by_cases ht : t ∈ Icc (-δ*Real.sqrt p.1) (δ*Real.sqrt p.1)
        · rw [indicator_of_mem ht]
        · rw [indicator_of_notMem ht]; exact norm_nonneg _)
  refine ⟨δ, hδ, ?_⟩
  simpa only [F, integral_indicator measurableSet_Icc, integral_zero] using hD

#print axioms scaledCenteredCharFun_continuous
#print axioms gaussianCharFun_continuous
#print axioms scaledCenteredCharFun_gaussian_bound
#print axioms gaussianCharFun_norm_bound
#print axioms scaledCenteredCharFun_near_integral_tendsto

end ConditionalSpectralExtremes
