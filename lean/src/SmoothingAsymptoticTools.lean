import ActualMomentUniformBounds
import IntegratedErrorScales

/-! Explicit elementary asymptotic tools for the smoothing parameters. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralAudit.FourierHarmonic

theorem eventually_const_rpow_le (a b C ε : Real) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : Real in atTop, C*x^a ≤ ε*x^b := by
  have ht : Tendsto (fun x : Real => C*x^(a-b)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_sub] using (tendsto_rpow_neg_atTop (by linarith : 0 < b-a)).const_mul C
  filter_upwards [eventually_gt_atTop (0 : Real), ht.eventually (gt_mem_nhds hε)] with x hx hh
  have he : C*x^a = (C*x^(a-b))*x^b := by
    rw [mul_assoc, ← Real.rpow_add hx]
    congr 1
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hh.le (Real.rpow_nonneg hx.le _)

theorem eventually_const_exp_le_rpow (C b ε : Real) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ x : Real in atTop, C*Real.exp (-x) ≤ ε*x^b := by
  have hh := ((isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) b).const_mul_left C).bound hε
  filter_upwards [eventually_gt_atTop (0 : Real), hh] with x hx h
  simpa only [neg_one_mul, Real.norm_of_nonneg (mul_nonneg hC (Real.exp_pos _).le),
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le b)] using h

theorem eventually_quadratic_exponent_le (p P B : Real) (hp : 0 < p) (hP : 0 ≤ P) :
    ∀ᶠ x : Real in atTop, -p/2*x^2+P/2+x*B ≤ -x := by
  filter_upwards [eventually_ge_atTop (1 : Real), eventually_ge_atTop (2*(B+P/2+1)/p)] with x hx hlarge
  have hc : B+P/2+1 ≤ p/2*x := by
    have ht := (div_le_iff₀ hp).mp hlarge
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ x),
    mul_nonneg (sub_nonneg.mpr hx) hP]

theorem momentMajorant_ge_one (P : Real) (hP : 0 ≤ P) (d : Nat) : 1 ≤ momentMajorant P d := by
  have hh : 1 ≤ ((2 : Real)^(3*P/2))^d := one_le_pow₀ (Real.one_le_rpow (by norm_num) (by positivity))
  unfold momentMajorant
  linarith

theorem smoothing_tail_eventually_exp (p P : Real) (hp : 0 < p) (hP : p ≤ P) (d : Nat) :
    ∀ᶠ x : Real in atTop, ∀ (s : Real) (q : Nat), p ≤ s → s ≤ P → (q : Real) ≤ x →
      Real.exp (-(s/2)*x^2+(s/2)*x^(-10 : Real))*momentMajorant P d^q ≤ Real.exp (-x) := by
  have hPP : 0 ≤ P := by linarith
  have hM := momentMajorant_pos P d
  have hlog : 0 ≤ Real.log (momentMajorant P d) := Real.log_nonneg (momentMajorant_ge_one P hPP d)
  filter_upwards [eventually_ge_atTop (1 : Real),
    eventually_quadratic_exponent_le p P (Real.log (momentMajorant P d)) hp hPP] with x hx he
  intro s q hsp hsP hq
  have hxp : 0 < x := by linarith
  have hδ : x^(-10 : Real) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hδn := Real.rpow_nonneg hxp.le (-10 : Real)
  have hqlog := mul_le_mul_of_nonneg_right hq hlog
  have hsδ : s/2*x^(-10 : Real) ≤ P/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hδ (by linarith : 0 ≤ s/2)]
  have hsx := mul_le_mul_of_nonneg_right hsp (sq_nonneg x)
  rw [← Real.exp_log hM, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms smoothing_tail_eventually_exp
#print axioms eventually_const_rpow_le
end ConditionalSpectralAudit.FourierHarmonic
