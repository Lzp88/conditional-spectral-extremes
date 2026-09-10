import ActualIntegratedMoment
import ReservoirScale

/-! Explicit power envelopes for both errors in the actual integrated
moment. Rounding the frequency cutoff upward only enlarges the finite
frequency set; all bounds retain their stated uniform constants. -/
noncomputable section
open Filter
open scoped Real Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes.ReservoirScale

def integrationFrequencyCutoff (x u : Real) : Nat := ⌈x^u⌉₊

theorem integration_cutoff_bounds (x u : Real) (hx : 1 ≤ x) (hu : 0 ≤ u) :
    0 < integrationFrequencyCutoff x u ∧ x^u ≤ (integrationFrequencyCutoff x u : Real) ∧
      (integrationFrequencyCutoff x u : Real) ≤ 2*x^u := by
  have hp : 0 < x := by linarith
  have hpow : 1 ≤ x^u := Real.one_le_rpow hx hu
  have hlow : x^u ≤ (integrationFrequencyCutoff x u : Real) := Nat.le_ceil _
  have hhi := Nat.ceil_lt_add_one (Real.rpow_nonneg hp.le u)
  change (integrationFrequencyCutoff x u : Real) < x^u+1 at hhi
  refine ⟨?_, hlow, by linarith⟩
  have hc : (0 : Real) < integrationFrequencyCutoff x u := by linarith
  exact_mod_cast hc

theorem integration_cutoff_negative_power (x u α : Real) (hx : 1 ≤ x) (hu : 0 ≤ u) (hα : 0 ≤ α) :
    (integrationFrequencyCutoff x u : Real)^(-α) ≤ x^(-u*α) := by
  obtain ⟨_, hlo, _⟩ := integration_cutoff_bounds x u hx hu
  have hp : 0 < x := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hp u) hlo (neg_nonpos.mpr hα)
  rw [← Real.rpow_mul hp.le] at hh
  convert! hh using 1
  congr 1
  ring

theorem exp_log_scale (x a : Real) (hx : 0 < x) : Real.exp (a*Real.log x)=x^a := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem integrated_normalizer_error_bound (x u₂ u₃ α C K Q : Real)
    (hx : 1 ≤ x) (hu₂ : 0 ≤ u₂) (hα : 0 ≤ α) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hQ : Q ≤ K*x) :
    Q*(C*((integrationFrequencyCutoff x u₂ : Real)^(-α)+Real.exp (-(u₃*Real.log x)))) ≤
      K*C*(x^(1-u₂*α)+x^(1-u₃)) := by
  have hp : 0 < x := by linarith
  have hR := integration_cutoff_negative_power x u₂ α hx hu₂ hα
  have hE : Real.exp (-(u₃*Real.log x))=x^(-u₃) := by
    rw [show -(u₃*Real.log x)=(-u₃)*Real.log x by ring, exp_log_scale x (-u₃) hp]
  rw [hE]
  calc
    _ ≤ (K*x)*(C*((integrationFrequencyCutoff x u₂ : Real)^(-α)+x^(-u₃))) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ ≤ (K*x)*(C*(x^(-u₂*α)+x^(-u₃))) := by gcongr
    _ = K*C*(x^(1-u₂*α)+x^(1-u₃)) := by
      rw [show 1-u₂*α=(1 : Real)+(-u₂*α) by ring,
        show 1-u₃=(1 : Real)+(-u₃) by ring, Real.rpow_add hp, Real.rpow_add hp, Real.rpow_one]
      ring

theorem integrated_bad_arc_error_bound (x u₂ u₃ rStar ρ A₀ ω : Real)
    (hx : 1 ≤ x) (hu₂ : 0 ≤ u₂) (hρ : 0 ≤ ρ) (hω : ω ≤ A₀*Real.log x) :
    12*(integrationFrequencyCutoff x u₂ : Real)*Real.exp (-rStar*Real.log x+u₃*Real.log x+ρ*ω) ≤
      24*x^(u₂+u₃-rStar+ρ*A₀) := by
  have hp : 0 < x := by linarith
  obtain ⟨_, _, hR⟩ := integration_cutoff_bounds x u₂ hx hu₂
  have he : -rStar*Real.log x+u₃*Real.log x+ρ*ω ≤ (-rStar+u₃+ρ*A₀)*Real.log x := by
    nlinarith [mul_le_mul_of_nonneg_left hω hρ]
  calc
    _ ≤ 12*(2*x^u₂)*Real.exp ((-rStar+u₃+ρ*A₀)*Real.log x) := by gcongr
    _ = 24*x^(u₂+u₃-rStar+ρ*A₀) := by
      rw [exp_log_scale x _ hp,
        show u₂+u₃-rStar+ρ*A₀=u₂+(-rStar+u₃+ρ*A₀) by ring,
        Real.rpow_add hp u₂ (-rStar+u₃+ρ*A₀)]
      ring

def integratedErrorEnvelope (x u₂ u₃ α rStar ρ A₀ C K : Real) : Real :=
  Real.exp (K*C*(x^(1-u₂*α)+x^(1-u₃)))*(1+24*x^(u₂+u₃-rStar+ρ*A₀))

theorem integrated_error_envelope_tendsto_one (u₂ u₃ α rStar ρ A₀ C K : Real)
    (h₂ : 1 < u₂*α) (h₃ : 1 < u₃) (hr : u₂+u₃+ρ*A₀ < rStar) :
    Tendsto (fun n : Nat => integratedErrorEnvelope (L n) u₂ u₃ α rStar ρ A₀ C K) atTop (𝓝 1) := by
  have hpow (a : Real) (ha : a < 0) : Tendsto (fun n : Nat => (L n)^a) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -a)).comp L_tendsto_atTop
  have hA := Real.continuous_exp.continuousAt.tendsto.comp
    (((hpow _ (by linarith : 1-u₂*α<0)).add
      (hpow _ (by linarith : 1-u₃<0))).const_mul (K*C))
  have hB := ((hpow _ (by linarith : u₂+u₃-rStar+ρ*A₀<0)).const_mul 24).const_add 1
  simpa only [Function.comp_def, integratedErrorEnvelope, add_zero, mul_zero, Real.exp_zero, one_mul] using hA.mul hB

#print axioms integrated_normalizer_error_bound
#print axioms integrated_bad_arc_error_bound
#print axioms integrated_error_envelope_tendsto_one
end ConditionalSpectralAudit.FourierHarmonic
