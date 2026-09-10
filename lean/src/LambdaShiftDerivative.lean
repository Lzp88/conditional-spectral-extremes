import LambdaEntropyGap

/-! Exact derivative recurrence and asymptotic slope for the actual lambda. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ConditionalSpectralExtremes

theorem lambda_deriv_add_two {s : ℝ} (hs : -1 < s) :
    deriv lambda (s+2) = deriv lambda s + (s+1)⁻¹-(s+2)⁻¹ := by
  have hd := ((lambda_hasDerivAt hs).differentiableAt.hasDerivAt.add_const
    (2*Real.log 2)).add
    (((hasDerivAt_id s).add_const 1).log (by linarith : s+1 ≠ 0))
  have hd' := hd.sub (((hasDerivAt_id s).add_const 2).log (by linarith : s+2 ≠ 0))
  have hl : HasDerivAt (fun x => lambda (x+2)) (deriv lambda (s+2)) s := by
    convert! ((lambda_hasDerivAt (by linarith : -1 < s+2)).differentiableAt.hasDerivAt).comp s
      ((hasDerivAt_id s).add_const 2) using 1
    simp
  have he : (fun x => lambda (x+2)) =ᶠ[𝓝 s]
      (fun x => lambda x + 2*Real.log 2 + Real.log (x+1)-Real.log (x+2)) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact lambda_add_two hx
  have hd'' := hd'.congr_of_eventuallyEq he
  simpa only [id_eq, one_div] using hl.unique hd''

theorem lambda_derivative_secant_bounds {s : ℝ} (hs : 2 < s) :
    Real.log 2 + (Real.log (s-1)-Real.log s)/2 ≤ deriv lambda s ∧
    deriv lambda s ≤ Real.log 2 + (Real.log (s+1)-Real.log (s+2))/2 := by
  have hsd : -1 < s := by linarith
  have hsm : -1 < s-2 := by linarith
  have hsp : -1 < s+2 := by linarith
  have hc := lambda_strictConvexOn.convexOn
  have hlo := hc.slope_le_deriv hsm hsd (by linarith : s-2 < s)
    (lambda_hasDerivAt hsd).differentiableAt
  have hup := hc.deriv_le_slope hsd hsp (by linarith : s < s+2)
    (lambda_hasDerivAt hsd).differentiableAt
  have he := lambda_add_two hsm
  rw [show s-2+2=s by ring, show s-2+1=s-1 by ring] at he
  rw [slope_def_field, show s-(s-2)=2 by ring] at hlo
  rw [slope_def_field, show s+2-s=2 by ring, lambda_add_two hsd] at hup
  constructor <;> linarith

theorem lambda_derivative_tendsto_log_two : Tendsto (deriv lambda) atTop (𝓝 (Real.log 2)) := by
  have hlog (a b : ℝ) :
      Tendsto (fun x : ℝ => Real.log (x+a)-Real.log (x+b)) atTop (𝓝 0) := by
    have hratio : Tendsto (fun x : ℝ => (x+a)/(x+b)) atTop (𝓝 1) := by
      have he := ((tendsto_const_nhds (x := a-b)).div_atTop
        (tendsto_atTop_add_const_right atTop b tendsto_id)).const_add 1
      simp only [add_zero] at he
      apply he.congr'
      filter_upwards [eventually_gt_atTop (-b)] with x hx
      have hb : x+b ≠ 0 := by linarith
      simp only [id_eq]
      field_simp
      ring
    have hh := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
    simp only [Real.log_one] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (-a), eventually_gt_atTop (-b)] with x ha hb
    rw [Real.log_div (by linarith : x+a ≠ 0) (by linarith : x+b ≠ 0)]
  have hl := (hlog (-1) 0).div_const 2 |>.const_add (Real.log 2)
  have hu := (hlog 1 2).div_const 2 |>.const_add (Real.log 2)
  simp only [zero_div, add_zero, ← sub_eq_add_neg] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
    exact (lambda_derivative_secant_bounds hs).1
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with s hs
    exact (lambda_derivative_secant_bounds hs).2

#print axioms lambda_deriv_add_two
#print axioms lambda_derivative_tendsto_log_two
end ConditionalSpectralExtremes
