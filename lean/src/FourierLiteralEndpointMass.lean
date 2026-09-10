import FourierLiteralDerivativeBounds

/-! The literal near-integer integral estimate with exponent pmin and
linear imaginary-marker factor from the Fourier proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierDerivative

theorem actual_uniform_literal_endpoint_mass (pmin P : Real) (hp : 0 < pmin) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      ∀ h : Real, 0 < h → h ≤ 1/2 →
        (∫ t in 0..h, ‖circlePhiDerivative z t‖)+
          (∫ t in 1-h..1, ‖circlePhiDerivative z t‖) ≤ C*(1+|z.im|)*h^pmin := by
  obtain ⟨C,hC,h⟩ := actual_uniform_literal_derivative_bounds_two_sides pmin P hp hpP
  refine ⟨2*C/pmin,by positivity,?_⟩
  intro z hzp hzP δ hδ hδ2
  have hz : 0 < z.re := hp.trans_le hzp
  have hi := (circlePhiDerivative_periodic z).intervalIntegrable₀
    (by norm_num : (1:Real)≠0) (circlePhiDerivative_intervalIntegrable z hz)
  have hd := h z hzp hzP
  have hpow : IntervalIntegrable (fun t : Real => t^(pmin-1)) volume 0 δ :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowr : IntervalIntegrable (fun t : Real => (1-t)^(pmin-1)) volume (1-δ) 1 := by
    simpa only [sub_zero] using (hpow.comp_sub_left 1).symm
  have hleft : (∫ t in 0..δ, ‖circlePhiDerivative z t‖) ≤ C*(1+|z.im|)*δ^pmin/pmin := by
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo hδ.le (hi 0 δ).norm
      (hpow.const_mul (C*(1+|z.im|))) (by
        intro t ht
        exact (hd.1 t ht.1 (by linarith [ht.2])).1)
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : -1 < pmin-1)),
      show pmin-1+1=pmin by ring, Real.zero_rpow hp.ne',sub_zero] at hm
    convert hm using 1
    ring
  have hright : (∫ t in 1-δ..1, ‖circlePhiDerivative z t‖) ≤ C*(1+|z.im|)*δ^pmin/pmin := by
    have hm := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : 1-δ ≤ 1)
      (hi (1-δ) 1).norm (hpowr.const_mul (C*(1+|z.im|))) (by
        intro t ht
        exact (hd.2 t (by linarith [ht.1]) ht.2).1)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun t : Real => t^(pmin-1)) 1,
      sub_self,sub_sub_cancel,integral_rpow (Or.inl (by linarith : -1 < pmin-1)),
      show pmin-1+1=pmin by ring,Real.zero_rpow hp.ne',sub_zero] at hm
    convert hm using 1
    ring
  calc
    _ ≤ C*(1+|z.im|)*δ^pmin/pmin+C*(1+|z.im|)*δ^pmin/pmin := add_le_add hleft hright
    _ = _ := by ring

#print axioms actual_uniform_literal_endpoint_mass
end ConditionalSpectralAudit.FourierDerivative
