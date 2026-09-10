import FourierDerivativeFoundation

/-! Actual first and second derivatives with uniform endpoint bounds.
The power comparison is on the true sin kernel, not an assumed majorant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace ConditionalSpectralAudit.FourierDerivative
open FourierTail

theorem sine_ge_left_distance {t : Real} (ht : 0 < t) (ht2 : t ≤ 1/2) :
    t ≤ Real.sin (Real.pi*t) := by
  have hp : 0 < Real.pi*t := mul_pos Real.pi_pos ht
  have hb : |Real.pi*t| ≤ Real.pi/2 := by rw [abs_of_pos hp]; nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hb
  rw [abs_of_pos hp,abs_of_pos (sine_pos_interior (show t ∈ Ioo (0:Real) 1 from
    ⟨ht,by linarith⟩))] at hs
  have he : 2/Real.pi*(Real.pi*t)=2*t := by field_simp
  rw [he] at hs
  linarith

theorem sine_ge_right_distance {t : Real} (ht2 : 1/2 ≤ t) (ht1 : t < 1) :
    1-t ≤ Real.sin (Real.pi*t) := by
  have hs := sine_ge_left_distance (show 0<1-t by linarith) (show 1-t≤1/2 by linarith)
  rwa [show Real.pi*(1-t)=Real.pi-Real.pi*t by ring,Real.sin_pi_sub] at hs

theorem sine_rpow_le_endpoint_powers {t r p : Real} (ht : t ∈ Ioo (0:Real) 1)
    (hr : r ≤ 0) (hrp : r ≤ p) :
    Real.sin (Real.pi*t)^p ≤ t^r+(1-t)^r := by
  have hs := (Real.rpow_le_rpow_of_exponent_ge (sine_pos_interior ht)
    (Real.sin_le_one _) hrp)
  by_cases hh : t ≤ 1/2
  · exact hs.trans ((Real.rpow_le_rpow_of_nonpos ht.1
      (sine_ge_left_distance ht.1 hh) hr).trans (le_add_of_nonneg_right
        (Real.rpow_nonneg (by linarith [ht.2]) r)))
  · exact hs.trans ((Real.rpow_le_rpow_of_nonpos (show 0<1-t by linarith [ht.2])
      (sine_ge_right_distance (by linarith) ht.2) hr).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ht.1.le r)))

theorem hasDerivAt_complexSinePower_any (z : Complex) {t : Real}
    (ht : t ∈ Ioo (0 : Real) 1) :
    HasDerivAt (complexSinePower z)
      (z*(Real.sin (Real.pi*t) : Complex)^(z-1)*(Real.cos (Real.pi*t) : Complex)*
        (Real.pi : Complex)) t := by
  by_cases hz : z=0
  · subst z
    unfold complexSinePower
    simp only [zero_mul,Complex.cpow_zero]
    exact hasDerivAt_const t (1 : Complex)
  · have h := (hasDerivAt_ofReal_cpow_const (sine_pos_interior ht).ne' hz).scomp t
      (((hasDerivAt_id t).const_mul Real.pi).sin)
    unfold complexSinePower
    convert! h using 1
    simp only [mul_one,Complex.real_smul,Complex.ofReal_mul,id_eq]
    ring

def circlePhiSecondExpression (z : Complex) (t : Real) : Complex :=
  (2 : Complex)^z*z*(Real.pi : Complex)^2*
    ((z-1)*(Real.sin (Real.pi*t) : Complex)^(z-2)*(Real.cos (Real.pi*t) : Complex)^2-
      (Real.sin (Real.pi*t) : Complex)^z)

theorem circlePhiDerivative_hasDerivAt (z : Complex) (hz : 0 < z.re)
    {t : Real} (ht : t ∈ Ioo (0 : Real) 1) :
    HasDerivAt (circlePhiDerivative z) (circlePhiSecondExpression z t) t := by
  have hp := hasDerivAt_complexSinePower_any (z-1) ht
  have hc := (((hasDerivAt_id t).const_mul Real.pi).cos).ofReal_comp
  have hd := ((hp.const_mul ((2 : Complex)^z*z)).mul hc).mul_const (Real.pi : Complex)
  have he : circlePhiDerivative z =ᶠ[𝓝 t]
      (fun x => (2 : Complex)^z*z*complexSinePower (z-1) x*
        (Real.cos (Real.pi*x) : Complex)*(Real.pi : Complex)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact circlePhiDerivative_eq z hz hx
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert! hd using 1
  have hpow : (Real.sin (Real.pi*t) : Complex)^(z-1)*
      (Real.sin (Real.pi*t) : Complex)=(Real.sin (Real.pi*t) : Complex)^z := by
    calc
      _ = (Real.sin (Real.pi*t) : Complex)^(z-1)*
          (Real.sin (Real.pi*t) : Complex)^(1 : Complex) := by rw [Complex.cpow_one]
      _ = (Real.sin (Real.pi*t) : Complex)^((z-1)+1) :=
        (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (sine_pos_interior ht).ne')).symm
      _ = _ := by congr 1; ring
  simp only [circlePhiSecondExpression,complexSinePower,Complex.ofReal_mul,
    Complex.ofReal_neg,mul_one,id_eq]
  rw [show z-1-1=z-2 by ring]
  linear_combination ((2 : Complex)^z*z*(Real.pi : Complex)^2)*hpow

theorem circlePhiDerivative_differentiableOn (z : Complex) (hz : 0 < z.re) :
    DifferentiableOn Real (circlePhiDerivative z) (Ioo (0:Real) 1) :=
  fun _ ht => (circlePhiDerivative_hasDerivAt z hz ht).differentiableAt.differentiableWithinAt

theorem norm_two_cpow (z : Complex) : ‖(2 : Complex)^z‖=(2 : Real)^z.re := by
  simpa only [Complex.ofReal_ofNat] using
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:Real)<2) z

theorem circlePhiSecondExpression_norm_le (z : Complex) {t : Real}
    (ht : t ∈ Ioo (0 : Real) 1) :
    ‖circlePhiSecondExpression z t‖ ≤
      (2 : Real)^z.re*‖z‖*Real.pi^2*
        (‖z-1‖*Real.sin (Real.pi*t)^(z.re-2)+Real.sin (Real.pi*t)^z.re) := by
  unfold circlePhiSecondExpression
  rw [norm_mul,norm_mul,norm_mul,norm_two_cpow,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  gcongr
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,norm_pow,Complex.norm_cpow_eq_rpow_re_of_pos (sine_pos_interior ht),
    Complex.sub_re,Complex.norm_real,Real.norm_eq_abs]
  change ‖z-1‖*Real.sin (Real.pi*t)^(z.re-2)*|Real.cos (Real.pi*t)|^2+
    Real.sin (Real.pi*t)^z.re ≤ _
  have hc : |Real.cos (Real.pi*t)|^2 ≤ 1 := by
    nlinarith [Real.abs_cos_le_one (Real.pi*t),abs_nonneg (Real.cos (Real.pi*t))]
  nlinarith [mul_nonneg (norm_nonneg (z-1))
    (Real.rpow_nonneg (sine_pos_interior ht).le (z.re-2))]

#print axioms sine_rpow_le_endpoint_powers
#print axioms hasDerivAt_complexSinePower_any
#print axioms circlePhiDerivative_hasDerivAt
#print axioms circlePhiSecondExpression_norm_le
end ConditionalSpectralAudit.FourierDerivative
