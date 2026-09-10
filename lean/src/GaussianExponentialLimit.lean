import Mathlib

/-! A direct third-order exponential remainder for the Poisson-type Gaussian exponent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace ConditionalSpectralExtremes

theorem gaussian_exponent_remainder (b t : Real) (hb : 0 < b) :
    ‖(b : Complex)^2*(Complex.exp (Complex.I*(t : Complex)/b)-1-Complex.I*(t : Complex)/b)+(t : Complex)^2/2‖ ≤
      |t|^3/b*Real.exp (|t|/b) := by
  let w : Complex := Complex.I*(t : Complex)/b
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp w 3
  norm_num [Finset.sum_range_succ] at h
  have hbC : (b : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have heq : (b : Complex)^2*(Complex.exp w-1-w)+(t : Complex)^2/2 =
      (b : Complex)^2*(Complex.exp w-(1+w+w^2/2)) := by
    dsimp [w]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  change ‖(b : Complex)^2*(Complex.exp w-1-w)+(t : Complex)^2/2‖ ≤ _
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
  have hw : ‖w‖=|t|/b := by
    simp only [w,norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg b)
  rw [hw] at hh
  calc
    _ ≤ b^2*((|t|/b)^3*Real.exp (|t|/b)) := hh
    _ = _ := by field_simp

theorem gaussian_exponent_tendsto (t : Real) :
    Tendsto (fun b : Real => (b : Complex)^2*
      (Complex.exp (Complex.I*(t : Complex)/b)-1-Complex.I*(t : Complex)/b))
      atTop (𝓝 (-(t : Complex)^2/2)) := by
  have he : Tendsto (fun b : Real =>
      (b : Complex)^2*(Complex.exp (Complex.I*(t : Complex)/b)-1-Complex.I*(t : Complex)/b)+(t : Complex)^2/2)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun b : Real => |t|^3/b*Real.exp (|t|/b))
    · filter_upwards [eventually_gt_atTop (0 : Real)] with b hb
      exact gaussian_exponent_remainder b t hb
    · have h1 : Tendsto (fun b : Real => |t|^3/b) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      have h2 : Tendsto (fun b : Real => |t|/b) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      simpa only [Real.exp_zero,zero_mul,Function.comp_def] using!
        h1.mul (Real.continuous_exp.continuousAt.tendsto.comp h2)
  have hh := he.sub_const ((t : Complex)^2/2)
  simpa only [add_sub_cancel_right,zero_sub,neg_div] using hh

#print axioms gaussian_exponent_remainder
#print axioms gaussian_exponent_tendsto
end ConditionalSpectralExtremes
