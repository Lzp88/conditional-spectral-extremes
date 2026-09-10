import FourierDerivativeCoefficient
import FourierDerivativeTranslation

/-! The manuscript's literal half-period translation argument, followed by
the actual integration-by-parts identity. No coefficient estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierDerivative
open FourierTail
local instance : Fact (0 < (1 : Real)) := ⟨by norm_num⟩

theorem periodic_fourier_half_shift_bound (g : Real → Complex)
    (hp : Function.Periodic g 1) (hg : IntervalIntegrable g volume 0 1)
    {j : Int} (hj : j ≠ 0) :
    2 * ‖∫ t in (0 : Real)..1, fourier (-j) (t : AddCircle (1 : Real)) * g t‖ ≤
      ∫ t in (0 : Real)..1, ‖g (t + (1 : Real) / 2 / (-j : Int)) - g t‖ := by
  let h : Real := 1 / 2 / (-j : Int)
  let w : Real → Complex := fun t => fourier (-j) (t : AddCircle (1 : Real))
  have hwc : Continuous w := (fourier (-j)).continuous.comp (AddCircle.continuous_mk' 1)
  have hwp : Function.Periodic w 1 := fun t => by
    dsimp only [w]
    rw [AddCircle.coe_add_period]
  have hwshift (t : Real) : w (t+h) = -w t := by
    dsimp only [w,h]
    rw [AddCircle.coe_add]
    exact fourier_add_half_inv_index (neg_ne_zero.mpr hj) (by norm_num) _
  have hgp : Function.Periodic (fun t => w t * g t) 1 := fun t => by
    dsimp only
    rw [hwp t,hp t]
  have hgi : IntervalIntegrable (fun t => g (t+h)) volume 0 1 := by
    have hi := (hp.intervalIntegrable₀ (by norm_num) hg h (1+h)).comp_add_right h
    simpa only [sub_self,add_sub_cancel_right] using hi
  have hwi := hg.continuousOn_mul hwc.continuousOn
  have hwgi := hgi.continuousOn_mul hwc.continuousOn
  have hshift : (∫ t in (0 : Real)..1, w t * g (t+h)) =
      -(∫ t in (0 : Real)..1, w t * g t) := by
    have heq : (∫ t in (0 : Real)..1, w (t+h) * g (t+h)) =
        ∫ t in (0 : Real)..1, w t * g t := by
      rw [intervalIntegral.integral_comp_add_right (fun t => w t * g t) h,
        zero_add,add_comm 1 h]
      simpa only [zero_add] using hgp.intervalIntegral_add_eq h 0
    simp only [hwshift,neg_mul,intervalIntegral.integral_neg] at heq
    exact neg_eq_iff_eq_neg.mp heq
  have hid : (∫ t in (0 : Real)..1, w t * (g (t+h)-g t)) =
      (-2 : Complex) * (∫ t in (0 : Real)..1, w t * g t) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hwgi hwi,hshift]
    ring
  have hn := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun t => w t * (g (t+h)-g t)) (by norm_num : (0 : Real) ≤ 1)
  rw [hid,norm_mul] at hn
  have hwn (t : Real) : ‖w t‖ = 1 := by
    exact Circle.norm_coe _
  simp only [norm_mul,hwn,one_mul,norm_neg,Complex.norm_ofNat] at hn
  exact hn

theorem actual_derivative_fourier_translation_bound (z : Complex) (hz : 0 < z.re)
    {j : Int} (hj : j ≠ 0) :
    2 * ‖fourierCoeff (circlePhiDerivativeOnCircle z) j‖ ≤
      ∫ t in (0 : Real)..1,
        ‖circlePhiDerivative z (t + (1 : Real) / 2 / (-j : Int)) -
          circlePhiDerivative z t‖ := by
  have h := periodic_fourier_half_shift_bound (circlePhiDerivative z)
    (circlePhiDerivative_periodic z) (circlePhiDerivative_intervalIntegrable z hz) hj
  rw [circlePhiDerivativeOnCircle,fourierCoeff_liftIoc_eq,fourierCoeffOn_eq_integral]
  simp only [zero_add,sub_zero,one_smul,smul_eq_mul,fourier_coe_apply,
    Complex.ofReal_one,div_one] at h ⊢
  exact h

theorem actual_coefficient_decay_by_translation (pmin P α : Real)
    (ha : 0 < α) (hap : α < pmin) (ha1 : α < 1) (hpP : pmin ≤ P) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex, pmin ≤ z.re → z.re ≤ P →
      ∀ j : Int, j ≠ 0 →
        ‖complexCoefficient z j‖ ≤ C*(1+|z.im|)^2*|(j : Real)|^(-1-α) := by
  obtain ⟨C,hC,hbound⟩ := actual_derivative_translation_display pmin P α ha hap ha1 hpP
  refine ⟨C,hC,?_⟩
  intro z hzp hzP j hj
  have hz : 0 < z.re := lt_of_lt_of_le (lt_trans ha hap) hzp
  have hjr : (j : Real) ≠ 0 := by exact_mod_cast hj
  have hjabs : 0 < |(j : Real)| := abs_pos.mpr hjr
  have hhabs : |(1 : Real) / 2 / (-j : Int)| ≤ |(j : Real)|⁻¹ := by
    rw [abs_div,Int.cast_neg,abs_neg,abs_div,abs_one,abs_of_pos (by norm_num : (0 : Real)<2)]
    rw [← one_div]
    exact div_le_div_of_nonneg_right (by norm_num) hjabs.le
  have hpow : |(1 : Real) / 2 / (-j : Int)|^α ≤ |(j : Real)|^(-α) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    exact Real.rpow_le_rpow (abs_nonneg _) hhabs ha.le
  have hfirst := (actual_derivative_fourier_translation_bound z hz hj).trans
    ((hbound z hzp hzP ((1 : Real)/2/(-j : Int))).trans
      (mul_le_mul_of_nonneg_left hpow (by positivity)))
  rw [circlePhiDerivative_fourierCoeff z hz,norm_mul,norm_mul,norm_mul,norm_mul,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    Complex.norm_I,mul_one,← Complex.ofReal_intCast,Complex.norm_real,
    Real.norm_eq_abs] at hfirst
  have hsmall : |(j : Real)| * ‖complexCoefficient z j‖ ≤
      C*(1+|z.im|)^2*|(j : Real)|^(-α) := by
    have hnon : 0 ≤ |(j : Real)| * ‖complexCoefficient z j‖ := by positivity
    nlinarith [Real.pi_gt_three]
  have hpower : |(j : Real)| * |(j : Real)|^(-1-α) = |(j : Real)|^(-α) := by
    calc
      _ = |(j : Real)|^1 * |(j : Real)|^(-1-α) := by rw [Real.rpow_one]
      _ = |(j : Real)|^(1+(-1-α)) := (Real.rpow_add hjabs _ _).symm
      _ = _ := by congr 1; ring
  apply (mul_le_mul_iff_right₀ hjabs).mp
  calc
    |(j : Real)| * ‖complexCoefficient z j‖ ≤
        C*(1+|z.im|)^2*|(j : Real)|^(-α) := hsmall
    _ = |(j : Real)| * (C*(1+|z.im|)^2*|(j : Real)|^(-1-α)) := by
      rw [← hpower]
      ring

#print axioms periodic_fourier_half_shift_bound
#print axioms actual_derivative_fourier_translation_bound
#print axioms actual_coefficient_decay_by_translation
end ConditionalSpectralAudit.FourierDerivative
