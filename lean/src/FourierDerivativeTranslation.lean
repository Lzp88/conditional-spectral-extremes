import FourierUniformDerivativeBounds
import PeriodicTranslationLargeShift
import GenericPeriodicSingularTranslation

/-! The manuscript's actual complex-power derivative L1 translation
display, with compact-parameter constants and every real translation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierDerivative
open ConditionalSpectralExtremes

theorem periodic_translation_norm_even (g : Real → Complex)
    (hg : Function.Periodic g 1) (h : Real) :
    (∫ t in (0:Real)..1, ‖g (t-h)-g t‖)=
      ∫ t in (0:Real)..1, ‖g (t+h)-g t‖ := by
  have hp : Function.Periodic (fun t => g (t+h)-g t) 1 := by
    intro t
    dsimp only
    rw [show t+1+h=(t+h)+1 by ring,hg (t+h),hg t]
  have hs := periodic_norm_shift_integral (fun t => g (t+h)-g t) hp (-h)
  calc
    _ = ∫ t in (0:Real)..1, ‖g ((t+ -h)+h)-g (t+ -h)‖ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [show (t+ -h)+h=t by ring,show t+ -h=t-h by ring,norm_sub_rev]
    _ = _ := hs

theorem actual_derivative_translation_positive (pmin P α : Real)
    (ha : 0 < α) (hap : α < pmin) (ha1 : α < 1) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      ∀ h : Real, 0 < h →
        (∫ t in (0:Real)..1, ‖circlePhiDerivative z (t+h)-circlePhiDerivative z t‖) ≤
          C*(1+|z.im|)^2*h^α := by
  obtain ⟨K,hK,hbound⟩ := actual_uniform_derivative_endpoint_bounds pmin P α ha hap ha1 hpP
  let C0 := periodicSingularTranslationConstant α
  let C1 := 4*4^α/α
  have hC0 : 0 < C0 := periodicSingularTranslationConstant_pos ha ha1
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  refine ⟨(C0+C1)*K,by positivity,?_⟩
  intro z hzp hzP h hh
  have hz : 0 < z.re := (ha.trans hap).trans_le hzp
  have hU : 0 ≤ K*(1+|z.im|)^2 := by positivity
  have hb := hbound z hzp hzP
  by_cases hs : h ≤ 1/4
  · have hm := generic_periodic_singular_translation_bound ha ha1 hU
      (circlePhiDerivative z) (circlePhiSecondExpression z)
      (circlePhiDerivative_periodic z) (circlePhiDerivative_intervalIntegrable z hz)
      (fun _ ht => circlePhiDerivative_hasDerivAt z hz ht)
      (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).2) hh hs
    calc
      _ ≤ C0*(K*(1+|z.im|)^2)*h^α := hm
      _ ≤ ((C0+C1)*K)*(1+|z.im|)^2*h^α := by
        have hp : 0 ≤ h^α := Real.rpow_nonneg hh.le _
        nlinarith [mul_nonneg (mul_nonneg hC1.le hU) hp]
  · have hm := periodic_large_shift_bound (circlePhiDerivative z) hU ha
      (circlePhiDerivative_periodic z) (circlePhiDerivative_intervalIntegrable z hz)
      (fun t ht => (hb t ht).1) (le_of_not_ge hs)
    calc
      _ ≤ C1*(K*(1+|z.im|)^2)*h^α := hm
      _ ≤ ((C0+C1)*K)*(1+|z.im|)^2*h^α := by
        have hp : 0 ≤ h^α := Real.rpow_nonneg hh.le _
        nlinarith [mul_nonneg (mul_nonneg hC0.le hU) hp]

theorem actual_derivative_translation_display (pmin P α : Real)
    (ha : 0 < α) (hap : α < pmin) (ha1 : α < 1) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      ∀ h : Real,
        (∫ t in (0:Real)..1, ‖circlePhiDerivative z (t+h)-circlePhiDerivative z t‖) ≤
          C*(1+|z.im|)^2*|h|^α := by
  obtain ⟨C,hC,hbound⟩ := actual_derivative_translation_positive pmin P α ha hap ha1 hpP
  refine ⟨C,hC,?_⟩
  intro z hzp hzP h
  rcases lt_trichotomy h 0 with hh | hh | hh
  · rw [abs_of_neg hh]
    have hb := hbound z hzp hzP (-h) (neg_pos.mpr hh)
    have he := periodic_translation_norm_even (circlePhiDerivative z) (circlePhiDerivative_periodic z) h
    calc
      _ = ∫ t in (0:Real)..1, ‖circlePhiDerivative z (t-h)-circlePhiDerivative z t‖ := he.symm
      _ ≤ _ := by simpa only [sub_eq_add_neg] using hb
  · subst h
    simp only [add_zero,sub_self,norm_zero,intervalIntegral.integral_zero,
      abs_zero,Real.zero_rpow ha.ne',mul_zero,le_refl]
  · rw [abs_of_pos hh]
    exact hbound z hzp hzP h hh

#print axioms periodic_translation_norm_even
#print axioms actual_derivative_translation_positive
#print axioms actual_derivative_translation_display
end ConditionalSpectralAudit.FourierDerivative
