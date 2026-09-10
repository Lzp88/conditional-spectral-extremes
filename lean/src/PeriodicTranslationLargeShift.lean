import FourierAbsoluteContinuity

/-! Elementary large-shift supplement to the small-shift singular
translation estimate. All integrals are actual period integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace ConditionalSpectralAudit.FourierDerivative

theorem endpoint_power_integrable {α : Real} (ha : 0 < α) :
    IntervalIntegrable (fun t : Real => t^(α-1)+(1-t)^(α-1)) volume 0 1 := by
  have hp : IntervalIntegrable (fun t : Real => t^(α-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hq := hp.comp_sub_left 1
  simp only [sub_self,sub_zero] at hq
  exact hp.add hq.symm

theorem endpoint_power_integral {α : Real} (ha : 0 < α) :
    (∫ t in (0:Real)..1, t^(α-1)+(1-t)^(α-1))=2/α := by
  have hp : IntervalIntegrable (fun t : Real => t^(α-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hq := hp.comp_sub_left 1
  simp only [sub_self,sub_zero] at hq
  rw [intervalIntegral.integral_add hp hq.symm,
    intervalIntegral.integral_comp_sub_left (fun t : Real => t^(α-1)) 1]
  simp only [sub_self,sub_zero]
  rw [integral_rpow (Or.inl (show -1<α-1 by linarith))]
  simp only [sub_add_cancel,Real.one_rpow,Real.zero_rpow ha.ne',sub_zero]
  ring

theorem periodic_norm_shift_integral (g : Real → Complex) (hg : Function.Periodic g 1)
    (h : Real) :
    (∫ t in (0:Real)..1, ‖g (t+h)‖)=∫ t in (0:Real)..1, ‖g t‖ := by
  have hn : Function.Periodic (fun t => ‖g t‖) 1 := fun t => by dsimp only; rw [hg t]
  rw [intervalIntegral.integral_comp_add_right (fun t => ‖g t‖) h,zero_add,add_comm 1 h]
  simpa only [zero_add] using hn.intervalIntegral_add_eq h 0

theorem periodic_difference_integral_le_twice (g : Real → Complex)
    (hg : Function.Periodic g 1) (hgi : IntervalIntegrable g volume 0 1) (h : Real) :
    (∫ t in (0:Real)..1, ‖g (t+h)-g t‖) ≤ 2*(∫ t in (0:Real)..1, ‖g t‖) := by
  have hshift : IntervalIntegrable (fun t => g (t+h)) volume 0 1 := by
    have hi := (hg.intervalIntegrable₀ (by norm_num) hgi h (1+h)).comp_add_right h
    simpa only [sub_self,add_sub_cancel_right] using hi
  calc
    _ ≤ ∫ t in (0:Real)..1, (‖g (t+h)‖+‖g t‖) :=
      intervalIntegral.integral_mono (by norm_num) (hshift.sub hgi).norm
        (hshift.norm.add hgi.norm) (fun t => norm_sub_le _ _)
    _ = _ := by
      rw [intervalIntegral.integral_add hshift.norm hgi.norm,periodic_norm_shift_integral g hg]
      ring

theorem periodic_endpoint_norm_integral_le (g : Real → Complex) {K α : Real}
    (ha : 0 < α) (hgi : IntervalIntegrable g volume 0 1)
    (hbound : ∀ t ∈ Ioo (0:Real) 1, ‖g t‖ ≤ K*(t^(α-1)+(1-t)^(α-1))) :
    (∫ t in (0:Real)..1, ‖g t‖) ≤ 2*K/α := by
  calc
    _ ≤ ∫ t in (0:Real)..1, K*(t^(α-1)+(1-t)^(α-1)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hgi.norm
        ((endpoint_power_integrable ha).const_mul K) hbound
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,endpoint_power_integral ha]
      ring

theorem periodic_large_shift_bound (g : Real → Complex) {K α : Real}
    (hK : 0 ≤ K) (ha : 0 < α) (hg : Function.Periodic g 1)
    (hgi : IntervalIntegrable g volume 0 1)
    (hbound : ∀ t ∈ Ioo (0:Real) 1, ‖g t‖ ≤ K*(t^(α-1)+(1-t)^(α-1)))
    {h : Real} (hh : (1:Real)/4 ≤ h) :
    (∫ t in (0:Real)..1, ‖g (t+h)-g t‖) ≤ (4*4^α/α)*K*h^α := by
  have hp : (1:Real) ≤ 4^α*h^α := by
    rw [← Real.mul_rpow (by norm_num : (0:Real)≤4) (by linarith : 0≤h)]
    exact Real.one_le_rpow (by linarith) ha.le
  have hb := (periodic_difference_integral_le_twice g hg hgi h).trans
    (mul_le_mul_of_nonneg_left (periodic_endpoint_norm_integral_le g ha hgi hbound) (by norm_num))
  have hk : 0 ≤ 4*K/α := by positivity
  calc
    _ ≤ 4*K/α := hb.trans_eq (by ring)
    _ ≤ (4*K/α)*(4^α*h^α) := le_mul_of_one_le_right hk hp
    _ = _ := by ring

#print axioms endpoint_power_integral
#print axioms periodic_difference_integral_le_twice
#print axioms periodic_large_shift_bound
end ConditionalSpectralAudit.FourierDerivative
