import ManuscriptDefinitions
import GammaRatioConvexity

/-!
Analysis of the actual Gamma expression `ConditionalSpectralExtremes.lambda`.
This file proves analytic facts about the manuscript's function, without
postulating a cumulant identity, convexity, or existence of a saddle.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology

namespace ConditionalSpectralExtremes

theorem lambda_zero : lambda 0 = 0 := by
  simp [lambda, Real.Gamma_one]

theorem lambda_two : lambda 2 = Real.log 2 := by
  norm_num [lambda, Real.Gamma_nat_eq_factorial]

theorem gamma_differentiableAt_pos {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ Real.Gamma x := by
  apply Real.differentiableAt_Gamma
  intro m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem lambda_hasDerivAt {s : ℝ} (hs : -1 < s) :
    HasDerivAt lambda
      (deriv Real.Gamma (1 + s) / Real.Gamma (1 + s) -
       deriv Real.Gamma (1 + s / 2) / Real.Gamma (1 + s / 2)) s := by
  have h1 : 0 < 1 + s := by linarith
  have h2 : 0 < 1 + s / 2 := by linarith
  have a1 : HasDerivAt (fun x : ℝ => 1 + x) 1 s := (hasDerivAt_id s).const_add 1
  have a2 : HasDerivAt (fun x : ℝ => 1 + x / 2) (1 / 2) s :=
    ((hasDerivAt_id s).div_const 2).const_add 1
  have dg1 : HasDerivAt Real.Gamma (deriv Real.Gamma (1 + s)) (1 + s) :=
    (gamma_differentiableAt_pos h1).hasDerivAt
  have dg2 : HasDerivAt Real.Gamma (deriv Real.Gamma (1 + s / 2)) (1 + s / 2) :=
    (gamma_differentiableAt_pos h2).hasDerivAt
  have g1 : HasDerivAt (fun x : ℝ => Real.Gamma (1 + x))
      (deriv Real.Gamma (1 + s) * 1) s :=
    dg1.comp s a1
  have g2 : HasDerivAt (fun x : ℝ => Real.Gamma (1 + x / 2))
      (deriv Real.Gamma (1 + s / 2) * (1 / 2)) s :=
    by convert! dg2.comp s a2 using 1
  have d1 := g1.log (Real.Gamma_pos_of_pos h1).ne'
  have d2 := g2.log (Real.Gamma_pos_of_pos h2).ne'
  unfold lambda
  convert! d1.sub (d2.const_mul 2) using 1
  ring

theorem lambda_continuousOn : ContinuousOn lambda (Ioi (-1)) := by
  intro s hs
  exact (lambda_hasDerivAt hs).continuousAt.continuousWithinAt

theorem lambda_nonneg {s : ℝ} (hs : -1 < s) : 0 ≤ lambda s := by
  have h := Real.convexOn_log_Gamma.2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show 1 + s ∈ Ioi 0 by change 0 < 1 + s; linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, Function.comp_apply, Real.Gamma_one, Real.log_one,
    mul_zero, zero_add] at h
  have heq : (1 / 2 : ℝ) * 1 + 1 / 2 * (1 + s) = 1 + s / 2 := by ring
  rw [heq] at h
  dsimp [lambda]
  linarith

theorem lambda_duplication {s : ℝ} (hs : -1 < s) :
    lambda s = s * Real.log 2 - (1 / 2) * Real.log Real.pi +
      (Real.log (Real.Gamma ((1 + s) / 2)) -
       Real.log (Real.Gamma (1 + s / 2))) := by
  have h1 : 0 < (1 + s) / 2 := by linarith
  have h2 : 0 < 1 + s / 2 := by linarith
  have h3 : 0 < 1 + s := by linarith
  have hd := Real.Gamma_mul_Gamma_add_half_of_pos h1
  have e1 : (1 + s) / 2 + 1 / 2 = 1 + s / 2 := by ring
  have e2 : 2 * ((1 + s) / 2) = 1 + s := by ring
  rw [e1, e2] at hd
  have hl := congrArg Real.log hd
  rw [Real.log_mul (Real.Gamma_pos_of_pos h1).ne' (Real.Gamma_pos_of_pos h2).ne',
      Real.log_mul (mul_pos (Real.Gamma_pos_of_pos h3) (Real.rpow_pos_of_pos (by norm_num) _)).ne'
        (Real.sqrt_pos.2 Real.pi_pos).ne',
      Real.log_mul (Real.Gamma_pos_of_pos h3).ne'
        (Real.rpow_pos_of_pos (by norm_num) _).ne',
      Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_sqrt Real.pi_pos.le] at hl
  dsimp [lambda]
  linarith

theorem lambda_strictConvexOn : StrictConvexOn ℝ (Ioi (-1)) lambda := by
  refine ⟨convex_Ioi (-1), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : 0 < (1 + x) / 2 := by change -1 < x at hx; linarith
  have hy' : 0 < (1 + y) / 2 := by change -1 < y at hy; linarith
  have hxy' : (1 + x) / 2 ≠ (1 + y) / 2 := by intro h; apply hxy; linarith
  have h := (logGammaRatio_strictConvexOn (by norm_num : (0 : ℝ) < 1 / 2)).2
    hx' hy' hxy' ha hb hab
  have hz : -1 < a * x + b * y := by
    have := (convex_Ioi (-1 : ℝ)) hx hy ha.le hb.le hab
    exact this
  simp only [smul_eq_mul] at *
  rw [lambda_duplication hz, lambda_duplication hx, lambda_duplication hy]
  have he : a * ((1 + x) / 2) + b * ((1 + y) / 2) = (1 + (a * x + b * y)) / 2 := by
    nlinarith [hab]
  rw [he] at h
  have hxc : (1 + x) / 2 + 1 / 2 = 1 + x / 2 := by ring
  have hyc : (1 + y) / 2 + 1 / 2 = 1 + y / 2 := by ring
  have hzc : (1 + (a * x + b * y)) / 2 + 1 / 2 = 1 + (a * x + b * y) / 2 := by ring
  rw [hxc, hyc, hzc] at h
  have hc := congrArg (fun r : ℝ => r * ((1 / 2) * Real.log Real.pi)) hab
  nlinarith only [h, hc]

theorem logGamma_half_lower {x : ℝ} (hx : 0 < x) :
    -(1 / 2) * Real.log x ≤ Real.log (Real.Gamma x) - Real.log (Real.Gamma (x + 1 / 2)) := by
  have h := Real.convexOn_log_Gamma.2 hx (show 0 < x + 1 by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, Function.comp_apply] at h
  have he : (1 / 2 : ℝ) * x + 1 / 2 * (x + 1) = x + 1 / 2 := by ring
  rw [he, Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne'] at h
  linarith

theorem logGamma_half_upper {x : ℝ} (hx : (1 / 2 : ℝ) ≤ x) :
    Real.log (Real.Gamma x) - Real.log (Real.Gamma (x + 1 / 2)) ≤
      (1 / 2) * Real.log 2 - (1 / 2) * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hxp : 0 < x + 1 / 2 := by linarith
  have h := Real.convexOn_log_Gamma.2 hxp (show 0 < (x + 1 / 2) + 1 by linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, Function.comp_apply] at h
  have he : (1 / 2 : ℝ) * (x + 1 / 2) + 1 / 2 * ((x + 1 / 2) + 1) = x + 1 := by ring
  rw [he, Real.Gamma_add_one hx0.ne', Real.Gamma_add_one hxp.ne',
    Real.log_mul hx0.ne' (Real.Gamma_pos_of_pos hx0).ne',
    Real.log_mul hxp.ne' (Real.Gamma_pos_of_pos hxp).ne'] at h
  have hl : Real.log (x + 1 / 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    exact Real.log_le_log hxp (by linarith)
  linarith

theorem lambda_log_bounds {s : ℝ} (hs : 0 ≤ s) :
    s * Real.log 2 - (1 / 2) * Real.log (1 + s) +
      (1 / 2) * Real.log 2 - (1 / 2) * Real.log Real.pi ≤ lambda s ∧
    lambda s ≤ s * Real.log 2 - (1 / 2) * Real.log (1 + s) +
      Real.log 2 - (1 / 2) * Real.log Real.pi := by
  have hx : 0 < (1 + s) / 2 := by linarith
  have hl := logGamma_half_lower hx
  have hu := logGamma_half_upper (x := (1 + s) / 2) (by linarith)
  have he : (1 + s) / 2 + 1 / 2 = 1 + s / 2 := by ring
  rw [he] at hl hu
  rw [Real.log_div (by linarith : (1 + s : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at hl hu
  rw [lambda_duplication (by linarith)]
  constructor <;> linarith

def variationalValues (L k : ℝ) : Set ℝ :=
  {r | ∃ s : ℝ, 0 < s ∧ r = (L + k * lambda s) / s}

theorem variationalValues_nonempty (L k : ℝ) : (variationalValues L k).Nonempty :=
  ⟨(L + k * lambda 1) / 1, 1, by norm_num, rfl⟩

theorem variationalValues_bddBelow {L k : ℝ} (hL : 0 ≤ L) (hk : 0 ≤ k) :
    BddBelow (variationalValues L k) := by
  refine ⟨0, ?_⟩
  rintro r ⟨s, hs, rfl⟩
  exact div_nonneg (add_nonneg hL (mul_nonneg hk (lambda_nonneg (by linarith)))) hs.le

theorem center_nonneg {n k : ℕ} (hn : 1 ≤ n) : 0 ≤ center n k := by
  apply le_csInf (variationalValues_nonempty (Real.log n) k)
  rintro r ⟨s, hs, rfl⟩
  exact div_nonneg (add_nonneg (Real.log_nonneg (by exact_mod_cast hn))
    (mul_nonneg (Nat.cast_nonneg k) (lambda_nonneg (by linarith)))) hs.le

theorem center_le_trial {n k : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    center n k ≤ (Real.log n + k * lambda s) / s := by
  exact csInf_le (variationalValues_bddBelow (Real.log_nonneg (by exact_mod_cast hn))
    (Nat.cast_nonneg k)) ⟨s, hs, rfl⟩

#print axioms lambda_hasDerivAt
#print axioms lambda_nonneg
#print axioms lambda_duplication
#print axioms lambda_strictConvexOn
#print axioms lambda_log_bounds
#print axioms center_nonneg
#print axioms center_le_trial

end ConditionalSpectralExtremes
