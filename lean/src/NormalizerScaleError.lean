import NormalizerPowerError
import SmoothingErrorAsymptotic

/-! The same explicit smoothing exponents control the full q-power normalizer. -/
noncomputable section
open Filter Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem chosen_normalizer_error_eventually_small (C J α : Real)
    (hC : 0 ≤ C) (hJ : 0 < J) (hα : 0 < α) :
    ∀ᶠ x : Real in atTop, ∀ (E : Real) (q : Nat), (q : Real) ≤ x → 0 ≤ E →
      E ≤ smoothingKernelEnvelope C x (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) α →
      (q : Real)*E*Real.exp ((q : Real)*E) ≤ x^(-J) := by
  obtain ⟨h1,h2,_,_,_,hc2,hc3,_⟩ := smoothing_exponents_valid J α hJ hα
  have ha2 : 1+4*smoothingExponentOne J-smoothingExponentTwo J α*α < -J := by linarith
  have ha3 : 1+4*smoothingExponentOne J-smoothingExponentThree J < -J := by linarith
  have hε : 0 < (2*Real.exp 1)⁻¹ := by positivity
  have hh2 := eventually_const_rpow_le _ (-J) (16*C) ((2*Real.exp 1)⁻¹) ha2 hε
  have hh3 := eventually_const_rpow_le _ (-J) (16*C) ((2*Real.exp 1)⁻¹) ha3 hε
  filter_upwards [eventually_ge_atTop (1 : Real), hh2, hh3] with x hx he2 he3
  intro E q hq hE hEB
  have hp : 0 < x := by linarith
  have he := hEB.trans (smoothing_kernel_power_bound C x _ _ _ α hC hx h1.le h2.le hα.le)
  have hqE : (q : Real)*E ≤ 16*C*(x^(1+4*smoothingExponentOne J-smoothingExponentTwo J α*α)+
      x^(1+4*smoothingExponentOne J-smoothingExponentThree J)) := by
    calc
      _ ≤ x*E := mul_le_mul_of_nonneg_right hq hE
      _ ≤ x*(16*C*(x^(4*smoothingExponentOne J-smoothingExponentTwo J α*α)+
          x^(4*smoothingExponentOne J-smoothingExponentThree J))) := mul_le_mul_of_nonneg_left he hp.le
      _ = _ := by
        rw [show 1+4*smoothingExponentOne J-smoothingExponentTwo J α*α=
            1+(4*smoothingExponentOne J-smoothingExponentTwo J α*α) by ring,
          show 1+4*smoothingExponentOne J-smoothingExponentThree J=
            1+(4*smoothingExponentOne J-smoothingExponentThree J) by ring,
          Real.rpow_add hp, Real.rpow_add hp, Real.rpow_one]
        ring
  have hsmall : (q : Real)*E ≤ (Real.exp 1)⁻¹*x^(-J) := by
    have hcoef : 2*(2*Real.exp 1)⁻¹=(Real.exp 1)⁻¹ := by field_simp
    calc
      _ ≤ 16*C*(x^(1+4*smoothingExponentOne J-smoothingExponentTwo J α*α)+
          x^(1+4*smoothingExponentOne J-smoothingExponentThree J)) := hqE
      _ = 16*C*x^(1+4*smoothingExponentOne J-smoothingExponentTwo J α*α)+
          16*C*x^(1+4*smoothingExponentOne J-smoothingExponentThree J) := by ring
      _ ≤ (2*Real.exp 1)⁻¹*x^(-J)+(2*Real.exp 1)⁻¹*x^(-J) := add_le_add he2 he3
      _ = (2*(2*Real.exp 1)⁻¹)*x^(-J) := by ring
      _ = _ := by rw [hcoef]
  have hpow : x^(-J) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hi : (Real.exp 1)⁻¹ ≤ 1 := (inv_le_one₀ (Real.exp_pos 1)).mpr (by
    exact Real.one_le_exp_iff.mpr (by norm_num))
  have hq1 : (q : Real)*E ≤ 1 := hsmall.trans
    (mul_le_one₀ hi (by positivity) hpow)
  calc
    _ ≤ ((Real.exp 1)⁻¹*x^(-J))*Real.exp 1 :=
      mul_le_mul hsmall (Real.exp_le_exp.mpr hq1) (Real.exp_pos _).le (by positivity)
    _ = _ := by field_simp

#print axioms chosen_normalizer_error_eventually_small
end ConditionalSpectralAudit.FourierHarmonic
