import LambdaDefectSeries
import DigammaLaplaceKernel

/-! Faithful digamma integral identity and the strict one-half estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ConditionalSpectralExtremes

theorem lambdaSlopeDefect_integral {s : ℝ} (hs : -1 < s) :
    lambdaSlopeDefect s = ∫ x in Ioi 0, defectLaplaceKernel s x := by
  have hnorm (m : ℕ) : (∫ x in Ioi 0, ‖defectLaplaceTerm s m x‖) = lambdaDefectTerm s m := by
    unfold lambdaDefectTerm
    rw [← defectLaplaceTerm_integral hs m]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.norm_of_nonneg (defectLaplaceTerm_nonneg s m hx.le)
  have hsum : Summable (fun m => ∫ x in Ioi 0, ‖defectLaplaceTerm s m x‖) := by
    simp_rw [hnorm]
    exact (lambdaDefect_hasSum hs).summable
  have hi := hasSum_integral_of_summable_integral_norm (defectLaplaceTerm_integrable hs) hsum
  have he : (∫ x in Ioi 0, ∑' m, defectLaplaceTerm s m x) =
      ∫ x in Ioi 0, defectLaplaceKernel s x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (defectLaplaceTerm_hasSum s hx).tsum_eq
  rw [he] at hi
  have hi' : HasSum (lambdaDefectTerm s) (∫ x in Ioi 0, defectLaplaceKernel s x) := by
    convert! hi using 1
    ext m
    exact (defectLaplaceTerm_integral hs m).symm
  exact (lambdaDefect_hasSum hs).unique hi'

theorem defectLaplaceKernel_pos (s x : ℝ) : 0 < defectLaplaceKernel s x := by
  unfold defectLaplaceKernel
  positivity

theorem defectLaplaceKernel_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (defectLaplaceKernel s) (Ioi 0) := by
  have hc : Continuous (defectLaplaceKernel s) := by
    unfold defectLaplaceKernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  apply (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (defectLaplaceKernel_pos s x).le]
  exact div_le_self (Real.exp_pos _).le (by have := Real.exp_pos x; linarith)

theorem positive_integral_Ioi_of_pos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x) : 0 < ∫ x in Ioi 0, f x := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpos x hx).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnn hf).2
  have he : Function.support f ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro x hx
    exact (hpos x hx).ne'
  rw [he]
  simp

theorem lambdaSlopeDefect_strict_half_bound {s : ℝ} (hs : 0 < s) :
    0 < s*(Real.log 2-deriv lambda s) ∧ s*(Real.log 2-deriv lambda s) < 1/2 := by
  have hi := defectLaplaceKernel_integrable hs
  have hid := lambdaSlopeDefect_integral (by linarith : -1 < s)
  have hpos := positive_integral_Ioi_of_pos hi (fun x _ => defectLaplaceKernel_pos s x)
  have heint := (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul (1/2 : ℝ)
  have hgap : 0 < ∫ x in Ioi 0, (1/2 : ℝ)*Real.exp (-s*x)-defectLaplaceKernel s x := by
    apply positive_integral_Ioi_of_pos (heint.sub hi)
    intro x hx
    apply sub_pos.mpr
    unfold defectLaplaceKernel
    apply (div_lt_iff₀ (by positivity : 0 < 1+Real.exp x)).2
    have he := Real.one_lt_exp_iff.mpr hx
    have hh := Real.exp_pos (-s*x)
    nlinarith
  rw [integral_sub heint hi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -s < 0) 0, ← hid] at hgap
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] at hgap
  rw [← hid] at hpos
  change 0 < s*lambdaSlopeDefect s ∧ s*lambdaSlopeDefect s < 1/2
  refine ⟨mul_pos hs hpos, ?_⟩
  have hh := mul_pos hs hgap
  have he : s*s⁻¹=1 := mul_inv_cancel₀ hs.ne'
  nlinarith

#print axioms lambdaSlopeDefect_integral
#print axioms lambdaSlopeDefect_strict_half_bound
end ConditionalSpectralExtremes
