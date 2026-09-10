import CenterMinimizer

/-! Smoothness and a strictly positive second derivative of actual lambda. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology

namespace ConditionalSpectralExtremes

theorem gamma_contDiffAt_pos {x : ℝ} (hx : 0 < x) (m : ℕ) :
    ContDiffAt ℝ m Real.Gamma x := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro n hn
    have he := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at he
    have hp : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    change 0 < z.re at hz
    linarith
  have ho : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hh : ContDiffAt ℂ m Complex.Gamma (x : ℂ) :=
    (hd.contDiffOn ho).contDiffAt (ho.mem_nhds hx)
  exact hh.real_of_complex

theorem lambda_contDiffAt {s : ℝ} (hs : -1 < s) (m : ℕ) :
    ContDiffAt ℝ m lambda s := by
  have h1 : 0 < 1 + s := by linarith
  have h2 : 0 < 1 + s / 2 := by linarith
  have g1 := (gamma_contDiffAt_pos h1 m).comp s
    (show ContDiffAt ℝ m (fun x : ℝ => 1 + x) s by fun_prop)
  have g2 := (gamma_contDiffAt_pos h2 m).comp s
    (show ContDiffAt ℝ m (fun x : ℝ => 1 + x / 2) s by fun_prop)
  exact (g1.log (Real.Gamma_pos_of_pos h1).ne').sub
    (contDiffAt_const.mul (g2.log (Real.Gamma_pos_of_pos h2).ne'))

theorem shifted_logStep_contDiffAt {s : ℝ} (hs : -1 < s) (m : ℕ) :
    ContDiffAt ℝ m (fun x => logStep 1 (1 + x)) s := by
  unfold logStep
  have h1 : 1 + s ≠ 0 := by linarith
  have h2 : 1 + s + 1 ≠ 0 := by linarith
  exact ((show ContDiffAt ℝ m (fun x : ℝ => 1 + x + 1) s by fun_prop).log h2).sub
    ((show ContDiffAt ℝ m (fun x : ℝ => 1 + x) s by fun_prop).log h1)

theorem logStep_half_rescale {s : ℝ} (hs : -1 < s) :
    logStep (1 / 2) ((1 + s) / 2) = logStep 1 (1 + s) := by
  unfold logStep
  have he : (1 + s) / 2 + 1 / 2 = (1 + s + 1) / 2 := by ring
  rw [he, Real.log_div (by linarith : (1 + s + 1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div (by linarith : (1 + s : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem lambda_sub_step_eq {s : ℝ} (hs : -1 < s) :
    lambda s - logStep 1 (1 + s) = s * Real.log 2 - (1 / 2) * Real.log Real.pi +
      (Real.log (Real.Gamma ((1 + s) / 2)) -
        Real.log (Real.Gamma (((1 + s) / 2) + 1 / 2)) -
        logStep (1 / 2) ((1 + s) / 2)) := by
  rw [lambda_duplication hs, logStep_half_rescale hs]
  have he : (1 + s) / 2 + 1 / 2 = 1 + s / 2 := by ring
  rw [he]
  ring

theorem lambda_sub_step_convexOn :
    ConvexOn ℝ (Ioi (-1)) (fun s => lambda s - logStep 1 (1 + s)) := by
  refine ⟨convex_Ioi (-1), ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : 0 < (1 + x) / 2 := by change -1 < x at hx; linarith
  have hy' : 0 < (1 + y) / 2 := by change -1 < y at hy; linarith
  have hz : -1 < a * x + b * y := (convex_Ioi (-1 : ℝ)) hx hy ha hb hab
  have h := (logGammaRatio_sub_logStep_convexOn (by norm_num : (0 : ℝ) < 1 / 2)).2
    hx' hy' ha hb hab
  simp only [smul_eq_mul] at *
  rw [lambda_sub_step_eq hx, lambda_sub_step_eq hy, lambda_sub_step_eq hz]
  have he : a * ((1 + x) / 2) + b * ((1 + y) / 2) = (1 + (a * x + b * y)) / 2 := by
    nlinarith [hab]
  rw [he] at h
  have hc := congrArg (fun r : ℝ => r * ((1 / 2) * Real.log Real.pi)) hab
  nlinarith only [h, hc]

theorem lambda_deriv2_lower {s : ℝ} (hs : -1 < s) :
    ((1 + s) ^ 2)⁻¹ - ((1 + s + 1) ^ 2)⁻¹ ≤ (deriv^[2] lambda) s := by
  let f := fun s : ℝ => lambda s - logStep 1 (1 + s)
  have hc : ConvexOn ℝ (Ioi (-1)) f := lambda_sub_step_convexOn
  have hm := hc.monotoneOn_deriv (fun x hx =>
    ((lambda_contDiffAt hx 1).sub (shifted_logStep_contDiffAt hx 1)).differentiableAt (by norm_num))
  have hn : 0 ≤ deriv (deriv f) s := by
    have hh := hm.derivWithin_nonneg (x := s)
    rwa [derivWithin_of_mem_nhds (Ioi_mem_nhds hs)] at hh
  have hd := iteratedDeriv_fun_sub (lambda_contDiffAt hs 2) (shifted_logStep_contDiffAt hs 2)
  have hstep : iteratedDeriv 2 (fun x => logStep 1 (1 + x)) s =
      ((1 + s) ^ 2)⁻¹ - ((1 + s + 1) ^ 2)⁻¹ := by
    rw [iteratedDeriv_comp_const_add, iteratedDeriv_eq_iterate]
    exact logStep_deriv2 (by norm_num) (by linarith)
  rw [hstep, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate] at hd
  change deriv (deriv f) s =
    (deriv^[2] lambda) s - (((1 + s) ^ 2)⁻¹ - ((1 + s + 1) ^ 2)⁻¹) at hd
  linarith

theorem lambda_deriv2_pos {s : ℝ} (hs : -1 < s) : 0 < (deriv^[2] lambda) s := by
  have hp : 0 < 1 + s := by linarith
  have hl : 0 < ((1 + s) ^ 2)⁻¹ - ((1 + s + 1) ^ 2)⁻¹ := by
    apply sub_pos.2
    exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (by nlinarith)
  exact lt_of_lt_of_le hl (lambda_deriv2_lower hs)

#print axioms lambda_contDiffAt
#print axioms lambda_sub_step_convexOn
#print axioms lambda_deriv2_lower
#print axioms lambda_deriv2_pos

end ConditionalSpectralExtremes
