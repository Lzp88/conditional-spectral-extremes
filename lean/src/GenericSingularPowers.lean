import Mathlib

/-! Elementary endpoint and interior power integrals used in the generic
periodic translation estimate. No translation estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralExtremes

theorem singular_endpoint_integral {α K a : Real} (hα : 0 < α) (hα1 : α < 1)
    (hK : 0 ≤ K) (ha : 0 < a) (ha2 : a ≤ 1/2) (f : Real → Real)
    (hf : IntervalIntegrable f volume 0 a)
    (hb : ∀ t ∈ Ioo 0 a, f t ≤ K*(t^(α-1)+(1-t)^(α-1))) :
    (∫ t in 0..a, f t) ≤ 2*K*a^α/α := by
  have hp : IntervalIntegrable (fun t : Real => t^(α-1)) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo ha.le hf (hp.const_mul (2*K)) (by
    intro t ht
    have ht1 : t ≤ 1-t := by linarith [ht.2]
    have hh := Real.rpow_le_rpow_of_nonpos ht.1 ht1 (by linarith : α-1 ≤ 0)
    calc
      f t ≤ K*(t^(α-1)+(1-t)^(α-1)) := hb t ht
      _ ≤ 2*K*t^(α-1) := by nlinarith)
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < α-1))] at hm
  rw [show α-1+1=α by ring, Real.zero_rpow hα.ne', sub_zero] at hm
  convert hm using 1
  ring

theorem singular_interior_integral {α a b : Real} (hα1 : α < 1) (ha : 0 < a)
    (hab : a ≤ b) :
    (∫ t in a..b, t^(α-2)) ≤ a^(α-1)/(1-α) := by
  have hz : (0:Real) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro hh
    linarith [hh.1]
  rw [integral_rpow (Or.inr ⟨by linarith, hz⟩),
    show α-2+1=α-1 by ring]
  calc
    (b^(α-1)-a^(α-1))/(α-1)=(a^(α-1)-b^(α-1))/(1-α) := by
      rw [show α-1=-(1-α) by ring, div_neg]
      ring
    _ ≤ a^(α-1)/(1-α) := div_le_div_of_nonneg_right
      (sub_le_self _ (Real.rpow_nonneg (ha.le.trans hab) _)) (by linarith)

theorem singular_shift_pointwise {α K h t : Real} (hα1 : α < 1) (hK : 0 ≤ K)
    (hh : 0 < h) (ht : 0 < t) (hth : t+h < 1)
    (g d : Real → Complex)
    (hd : ∀ u ∈ Ioo 0 1, HasDerivAt g (d u) u)
    (hb : ∀ u ∈ Ioo 0 1, ‖d u‖ ≤ K*(u^(α-2)+(1-u)^(α-2))) :
    ‖g (t+h)-g t‖ ≤ K*h*(t^(α-2)+(1-h-t)^(α-2)) := by
  have hseg (u : Real) (hu : u ∈ Icc t (t+h)) : u ∈ Ioo 0 1 := by
    constructor <;> linarith [hu.1,hu.2]
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=t) (b:=t+h) (f:=g) (f':=d)
    (C:=K*(t^(α-2)+(1-h-t)^(α-2)))
    (fun u hu => (hd u (hseg u hu)).hasDerivWithinAt) (by
      intro u hu
      have hu' : u ∈ Ioo 0 1 := hseg u ⟨hu.1,hu.2.le⟩
      have hleft := Real.rpow_le_rpow_of_nonpos ht hu.1 (by linarith : α-2 ≤ 0)
      have hright := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1-h-t)
        (by linarith [hu.2] : 1-h-t ≤ 1-u) (by linarith : α-2 ≤ 0)
      exact (hb u hu').trans (mul_le_mul_of_nonneg_left (add_le_add hleft hright) hK))
    (t+h) ⟨by linarith,le_rfl⟩
  convert hm using 1
  ring

#print axioms singular_endpoint_integral
#print axioms singular_interior_integral
#print axioms singular_shift_pointwise
end ConditionalSpectralExtremes
