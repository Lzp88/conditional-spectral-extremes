import FourierTail

/-! The actual periodic lift of the manuscript's complex power, its
interior derivative, and integrability of that genuine derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology
namespace ConditionalSpectralAudit.FourierDerivative
open FourierGeneral FourierTail

def circlePhiLift (z : Complex) (t : Real) : Complex :=
  complexPhi z (t : AddCircle (1 : Real))

def circlePhiDerivative (z : Complex) : Real → Complex := deriv (circlePhiLift z)

theorem circlePhiLift_continuous (z : Complex) (hz : 0 < z.re) :
    Continuous (circlePhiLift z) :=
  (continuous_complexPhi z hz).comp (AddCircle.continuous_mk' 1)

theorem circlePhiLift_periodic (z : Complex) : Function.Periodic (circlePhiLift z) 1 := by
  intro t
  simp only [circlePhiLift,AddCircle.coe_add_period]

theorem circlePhiDerivative_periodic (z : Complex) :
    Function.Periodic (circlePhiDerivative z) 1 := by
  intro t
  have he : (fun x => circlePhiLift z (x+1))=circlePhiLift z :=
    funext (circlePhiLift_periodic z)
  change deriv (circlePhiLift z) (t+1)=deriv (circlePhiLift z) t
  rw [← deriv_comp_add_const,he]

theorem circlePhiLift_hasDerivAt (z : Complex) (hz : 0 < z.re)
    {t : Real} (ht : t ∈ Ioo (0 : Real) 1) :
    HasDerivAt (circlePhiLift z)
      ((2 : Complex)^z*z*(Real.sin (Real.pi*t) : Complex)^(z-1)*
        (Real.cos (Real.pi*t) : Complex)*(Real.pi : Complex)) t := by
  have hn : z ≠ 0 := by intro he; simp [he] at hz
  have hd := (hasDerivAt_ofReal_cpow_const (sine_pos_interior ht).ne' hn).scomp t
    (((hasDerivAt_id t).const_mul Real.pi).sin)
  have hscaled := hd.const_mul ((2 : Complex)^z)
  have he : circlePhiLift z =ᶠ[𝓝 t]
      (fun x => (2 : Complex)^z*complexSinePower z x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact complexPhi_on_unit_interval z ⟨hx.1.le,hx.2.le⟩
  apply HasDerivAt.congr_of_eventuallyEq _ he
  unfold complexSinePower
  convert! hscaled using 1
  simp only [mul_one,Complex.real_smul,Complex.ofReal_mul,id_eq]
  ring

theorem circlePhiDerivative_eq (z : Complex) (hz : 0 < z.re)
    {t : Real} (ht : t ∈ Ioo (0 : Real) 1) :
    circlePhiDerivative z t=
      (2 : Complex)^z*z*(Real.sin (Real.pi*t) : Complex)^(z-1)*
        (Real.cos (Real.pi*t) : Complex)*(Real.pi : Complex) :=
  (circlePhiLift_hasDerivAt z hz ht).deriv

theorem circlePhiDerivative_norm (z : Complex) (hz : 0 < z.re)
    {t : Real} (ht : t ∈ Ioo (0 : Real) 1) :
    ‖circlePhiDerivative z t‖=
      (2 : Real)^z.re*‖z‖*Real.sin (Real.pi*t)^(z.re-1)*
        |Real.cos (Real.pi*t)| * Real.pi := by
  rw [circlePhiDerivative_eq z hz ht]
  have htwo : ‖(2 : Complex)^z‖=(2 : Real)^z.re := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:Real)<2) z
  simp only [norm_mul,htwo,
    Complex.norm_cpow_eq_rpow_re_of_pos (sine_pos_interior ht),Complex.sub_re,
    Complex.one_re,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]

theorem sine_rpow_intervalIntegrable (s : Real) (hs : -1 < s) :
    IntervalIntegrable (fun t => Real.sin (Real.pi*t)^s) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
  intro hzero
  have he := coefficient_zero_Gamma s hs
  rw [coefficient_zero_eq_real_sine,hzero,mul_zero] at he
  have hp : 0 < Real.Gamma (1+s)/Real.Gamma (1+s/2)^2 := by
    exact div_pos (Real.Gamma_pos_of_pos (by linarith))
      (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))
  have : (0 : Real)=Real.Gamma (1+s)/Real.Gamma (1+s/2)^2 :=
    Complex.ofReal_injective he
  linarith

theorem circlePhiDerivative_intervalIntegrable (z : Complex) (hz : 0 < z.re) :
    IntervalIntegrable (circlePhiDerivative z) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:Real)≤1)]
  have hsin := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0:Real)≤1)).mp
      (sine_rpow_intervalIntegrable (z.re-1) (by linarith))
  apply (hsin.const_mul ((2 : Real)^z.re*‖z‖*Real.pi)).mono'
    (aestronglyMeasurable_deriv (circlePhiLift z) _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change ‖circlePhiDerivative z t‖ ≤ _
  rw [circlePhiDerivative_norm z hz ht]
  have hc := Real.abs_cos_le_one (Real.pi*t)
  have hp := Real.rpow_nonneg (le_of_lt (sine_pos_interior ht)) (z.re-1)
  calc
    (2 : Real)^z.re*‖z‖*Real.sin (Real.pi*t)^(z.re-1)*
        |Real.cos (Real.pi*t)| * Real.pi ≤
      (2 : Real)^z.re*‖z‖*Real.sin (Real.pi*t)^(z.re-1)*1*Real.pi := by
        gcongr
    _ = _ := by ring

#print axioms circlePhiLift_hasDerivAt
#print axioms circlePhiDerivative_periodic
#print axioms circlePhiDerivative_norm
#print axioms sine_rpow_intervalIntegrable
#print axioms circlePhiDerivative_intervalIntegrable
end ConditionalSpectralAudit.FourierDerivative
