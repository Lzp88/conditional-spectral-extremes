import SmoothingPowerScales

/-! Uniform polynomial accuracy with the manuscript's spatial box and smoothing scale. -/
noncomputable section
open Filter Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem smoothing_errors_eventually_small (p P C J u₁ u₂ u₃ α : Real)
    (hp : 0 < p) (hP : p ≤ P) (hC : 0 ≤ C) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hα : 0 ≤ α)
    (hk₂ : 4*u₁-u₂*α < 0) (hk₃ : 4*u₁-u₃ < 0)
    (hc₂ : 5+6*u₁-u₂*α < -J) (hc₃ : 5+6*u₁-u₃ < -J)
    (hn : 114-9*u₁ < -J) :
    ∀ᶠ x : Real in atTop, ∀ (s E : Real) (q : Nat),
      p ≤ s → s ≤ P → (q : Real) ≤ x → 0 ≤ E → E ≤ smoothingKernelEnvelope C x u₁ u₂ u₃ α →
      E ≤ 1/2 ∧
      smoothingErrorOne P s (x^(-10 : Real)) (x^u₁) (x^2) E q ≤ x^(-J) ∧
      smoothingErrorTwo P s (x^(-10 : Real)) (x^u₁) (x^2) E q ≤ x^(-J) := by
  have he₂ := eventually_const_rpow_le (4*u₁-u₂*α) 0 (16*C) (1/4) hk₂ (by norm_num)
  have he₃ := eventually_const_rpow_le (4*u₁-u₃) 0 (16*C) (1/4) hk₃ (by norm_num)
  have hc2 := eventually_const_rpow_le (5+6*u₁-u₂*α) (-J) (1024*C) (1/8) hc₂ (by norm_num)
  have hc3 := eventually_const_rpow_le (5+6*u₁-u₃) (-J) (1024*C) (1/8) hc₃ (by norm_num)
  have hnoise := eventually_const_rpow_le (114-9*u₁) (-J) ((6400/81 : Real)*10^10) (1/4) hn (by norm_num)
  have htail := eventually_const_exp_le_rpow 8 (-J) (1/2) (by norm_num) (by norm_num)
  have hspace := smoothing_tail_eventually_exp p P hp hP 2
  filter_upwards [eventually_ge_atTop (1 : Real), he₂, he₃, hc2, hc3, hnoise, htail, hspace]
    with x hx he2 he3 hc2x hc3x hnX htX hsX
  intro s E q hsp hsP hq hE hEB
  have hxp : 0 < x := by linarith
  have hδp : 0 < x^(-10 : Real) := Real.rpow_pos_of_pos hxp _
  have hδ : x^(-10 : Real) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hT : 1 ≤ x^u₁ := Real.one_le_rpow hx hu₁
  have hK : 1 ≤ x^2 := one_le_pow₀ hx
  have hbound := hEB.trans (smoothing_kernel_power_bound C x u₁ u₂ u₃ α hC hx hu₁ hu₂ hα)
  have hsmall : E ≤ 1/2 := by
    simp only [Real.rpow_zero, mul_one] at he2 he3
    linarith
  have hcore := smoothing_frequency_core_power_bound C x u₁ u₂ u₃ α E q hC hx hE hq hbound
  have hnt := smoothing_frequency_tail_power x u₁ hxp
  have hst := hsX s q hsp hsP hq
  have hcommon : smoothingCrudeError P s (x^(-10 : Real)) (x^u₁) (x^2) E q ≤ x^(-J) := by
    unfold smoothingCrudeError
    have hqtail := mul_le_mul_of_nonneg_left hst (by norm_num : (0 : Real) ≤ 8)
    nlinarith
  refine ⟨hsmall, ?_, ?_⟩
  · exact (smoothingErrorOne_le_crude P s _ _ _ E q (by linarith) hδp hδ hT hK hE).trans hcommon
  · exact (smoothingErrorTwo_le_crude P s _ _ _ E q hδp (by linarith) hE).trans hcommon

def smoothingExponentOne (J : Real) : Real := J+200
def smoothingExponentTwo (J α : Real) : Real := (6*(J+200)+J+100)/α
def smoothingExponentThree (J : Real) : Real := 6*(J+200)+J+100

theorem smoothing_exponents_valid (J α : Real) (hJ : 0 < J) (hα : 0 < α) :
    0 < smoothingExponentOne J ∧ 0 < smoothingExponentTwo J α ∧ 0 < smoothingExponentThree J ∧
    4*smoothingExponentOne J-smoothingExponentTwo J α*α < 0 ∧
    4*smoothingExponentOne J-smoothingExponentThree J < 0 ∧
    5+6*smoothingExponentOne J-smoothingExponentTwo J α*α < -J ∧
    5+6*smoothingExponentOne J-smoothingExponentThree J < -J ∧
    114-9*smoothingExponentOne J < -J := by
  unfold smoothingExponentOne smoothingExponentTwo smoothingExponentThree
  rw [div_mul_cancel₀ _ hα.ne']
  refine ⟨by linarith, by positivity, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

theorem chosen_smoothing_errors_eventually_small (p P C J α : Real)
    (hp : 0 < p) (hP : p ≤ P) (hC : 0 ≤ C) (hJ : 0 < J) (hα : 0 < α) :
    ∀ᶠ x : Real in atTop, ∀ (s E : Real) (q : Nat),
      p ≤ s → s ≤ P → (q : Real) ≤ x → 0 ≤ E →
      E ≤ smoothingKernelEnvelope C x (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) α →
      E ≤ 1/2 ∧
      smoothingErrorOne P s (x^(-10 : Real)) (x^(smoothingExponentOne J)) (x^2) E q ≤ x^(-J) ∧
      smoothingErrorTwo P s (x^(-10 : Real)) (x^(smoothingExponentOne J)) (x^2) E q ≤ x^(-J) := by
  obtain ⟨h1,h2,_,he2,he3,hc2,hc3,hn⟩ := smoothing_exponents_valid J α hJ hα
  exact smoothing_errors_eventually_small p P C J _ _ _ α hp hP hC h1.le h2.le hα.le he2 he3 hc2 hc3 hn

#print axioms chosen_smoothing_errors_eventually_small
end ConditionalSpectralAudit.FourierHarmonic
