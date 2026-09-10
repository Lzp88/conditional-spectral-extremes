import DiophantineSmoothingL1
import NormalizerScaleError

/-! Polynomially accurate L1 comparison for actual one- and two-point sampled height laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

def PolynomialSmoothingL1One (p P J _u₁ u₂ u₃ x : Real) : Prop :=
  ∀ (s a : Real) (m n q : Nat) (t : AddCircle (1 : Real)),
    p ≤ s → s ≤ P → (q : Real) ≤ x → 0 < m → 1 ≤ harmonicMass m n → Real.exp a ≤ m →
    (∀ k : Int, |(k : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) → k ≠ 0 →
      Real.exp (-a+u₃*Real.log x) ≤ ‖k • t‖) →
    (∫ z : Real, |smoothedDensity (x^(-10 : Real))
      (coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0) z -
      smoothedDensity (x^(-10 : Real)) (coordinateLaw (referenceVectorSumLaw s 1 q) 0) z|) ≤ x^(-J) ∧
    |harmonicTiltNormalizer s (fun _ : Fin 1 => t) m n^q/logSineA s^q-1| ≤ x^(-J)

def PolynomialSmoothingL1Two (p P J _u₁ u₂ u₃ x : Real) : Prop :=
  ∀ (s a : Real) (m n q : Nat) (t₁ t₂ : AddCircle (1 : Real)),
    p ≤ s → s ≤ P → (q : Real) ≤ x → 0 < m → 1 ≤ harmonicMass m n → Real.exp a ≤ m →
    (∀ k : Int × Int,
      (|(k.1 : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real) ∧
        |(k.2 : Real)| ≤ (integrationFrequencyCutoff x u₂ : Real)) → k ≠ 0 →
      Real.exp (-a+u₃*Real.log x) ≤ ‖k.1 • t₁+k.2 • t₂‖) →
    (∫ z : PairSpace, |pairSmoothedDensity (x^(-10 : Real))
      (pairVectorLaw (harmonicTiltSumLaw s ![t₁,t₂] m n q)) z -
      pairSmoothedDensity (x^(-10 : Real)) (pairVectorLaw (referenceVectorSumLaw s 2 q)) z|) ≤ x^(-J) ∧
    |harmonicTiltNormalizer s ![t₁,t₂] m n^q/logSineA s^(2*q)-1| ≤ x^(-J)

theorem polynomial_smoothing_l1_one (p P J α : Real) (hp : 0 < p) (hP : p ≤ P)
    (hJ : 0 < J) (hα : 0 < α) (hαp : α < p) (hα1 : α ≤ 1) :
    ∀ᶠ x : Real in atTop, PolynomialSmoothingL1One p P J
      (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) x := by
  obtain ⟨C,hC,hTV⟩ := uniform_actual_l1_one p P α hP hα hαp hα1
  obtain ⟨D,hD,hB⟩ := uniform_harmonic_phi_error_one p P α hP hα hαp hα1
  obtain ⟨hu1,hu2,_,_⟩ := smoothing_exponents_valid J α hJ hα
  have hErr := chosen_smoothing_errors_eventually_small p P C J α hp hP hC.le hJ hα
  have hNorm := chosen_normalizer_error_eventually_small D J α hD.le hJ hα
  filter_upwards [eventually_ge_atTop (1 : Real), hErr, hNorm] with x hx hErrX hNormX
  intro s a m n q t hsp hsP hq hm hH ham hsep
  have hs : 0 < s := by linarith
  have hxp : 0 < x := by linarith
  have hT : 1 ≤ x^(smoothingExponentOne J) := Real.one_le_rpow hx hu1.le
  have hR : 0 < (integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real) := by
    exact_mod_cast (integration_cutoff_bounds x _ hx hu2.le).1
  let E := C*(1+x^(smoothingExponentOne J))^2*
    ((integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real)^(-α)+Real.exp (-(smoothingExponentThree J*Real.log x)))
  have hEn : 0 ≤ E := by dsimp only [E]; positivity
  have hEB : E ≤ smoothingKernelEnvelope C x (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) α := by
    unfold E smoothingKernelEnvelope
    gcongr <;> linarith
  obtain ⟨hEs,hEone,_⟩ := hErrX s E q hsp hsP hq hEn hEB
  have ht := hTV s (x^(-10 : Real)) (x^(smoothingExponentOne J)) (x^2)
    (integrationFrequencyCutoff x (smoothingExponentTwo J α)) a (smoothingExponentThree J*Real.log x)
    m n q t hsp hsP (by positivity) (by positivity) (by positivity) hR hm hH ham hsep hEs
  refine ⟨ht.trans hEone, ?_⟩
  let E₀ := D*((integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real)^(-α)+
    Real.exp (-(smoothingExponentThree J*Real.log x)))
  have hE₀n : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hz := hB (s : Complex) 0 (integrationFrequencyCutoff x (smoothingExponentTwo J α)) a
    (smoothingExponentThree J*Real.log x) m n t hsp hsP (by simp) hR hm (by linarith) ham hsep
  have h0 : ‖harmonicVectorKernel (fun _ : Fin 1 => (s : Complex)) (fun _ => t) m n-
      (logSineA s : Complex)^1‖ ≤ E₀ := by
    rw [harmonicVectorKernel_one, pow_one]
    rw [complexLogSineA_ofReal] at hz
    norm_num only [add_zero, one_pow, mul_one] at hz
    exact hz.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_self (Real.exp_pos _).le hH)) hD.le)
  have hE₀B : E₀ ≤ smoothingKernelEnvelope D x (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) α := by
    unfold E₀ smoothingKernelEnvelope
    have hpow : 1 ≤ (1+x^(smoothingExponentOne J))^4 := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD.le)
      (show 0 ≤ (integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real)^(-α)+Real.exp (-(smoothingExponentThree J*Real.log x)) by positivity)]
  have hn := actual_normalizer_power_relative_error s hs (fun _ : Fin 1 => t) m n q E₀ hE₀n h0
  simpa only [one_mul] using hn.trans (hNormX E₀ q hq hE₀n hE₀B)

theorem polynomial_smoothing_l1_two (p P J α : Real) (hp : 0 < p) (hP : p ≤ P)
    (hJ : 0 < J) (hα : 0 < α) (hαp : α < p) (hα1 : α ≤ 1) :
    ∀ᶠ x : Real in atTop, PolynomialSmoothingL1Two p P J
      (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) x := by
  obtain ⟨C,hC,hTV⟩ := uniform_actual_l1_two p P α hP hα hαp hα1
  obtain ⟨D,hD,hB⟩ := uniform_harmonic_phi_error_two p P α hP hα hαp hα1
  obtain ⟨hu1,hu2,_,_⟩ := smoothing_exponents_valid J α hJ hα
  have hErr := chosen_smoothing_errors_eventually_small p P C J α hp hP hC.le hJ hα
  have hNorm := chosen_normalizer_error_eventually_small D J α hD.le hJ hα
  filter_upwards [eventually_ge_atTop (1 : Real), hErr, hNorm] with x hx hErrX hNormX
  intro s a m n q t₁ t₂ hsp hsP hq hm hH ham hsep
  have hs : 0 < s := by linarith
  have hxp : 0 < x := by linarith
  have hT : 1 ≤ x^(smoothingExponentOne J) := Real.one_le_rpow hx hu1.le
  have hR : 0 < (integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real) := by
    exact_mod_cast (integration_cutoff_bounds x _ hx hu2.le).1
  let E := smoothingKernelEnvelope C x (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) α
  have hEn : 0 ≤ E := by unfold E smoothingKernelEnvelope; positivity
  obtain ⟨hEs,_,hEtwo⟩ := hErrX s E q hsp hsP hq hEn le_rfl
  have ht := hTV s (x^(-10 : Real)) (x^(smoothingExponentOne J)) (x^2)
    (integrationFrequencyCutoff x (smoothingExponentTwo J α)) a (smoothingExponentThree J*Real.log x)
    m n q t₁ t₂ hsp hsP (by positivity) (by positivity) (by positivity) hR hm hH ham hsep hEs
  refine ⟨ht.trans hEtwo, ?_⟩
  let E₀ := D*((integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real)^(-α)+
    Real.exp (-(smoothingExponentThree J*Real.log x)))
  have hE₀n : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have hz := hB (s : Complex) (s : Complex) 0 (integrationFrequencyCutoff x (smoothingExponentTwo J α)) a
    (smoothingExponentThree J*Real.log x) m n t₁ t₂ hsp hsP hsp hsP (by simp) (by simp) hR hm (by linarith) ham hsep
  have hconst : (fun _ : Fin 2 => (s : Complex)) = ![(s : Complex),(s : Complex)] := by ext i; fin_cases i <;> rfl
  have h0 : ‖harmonicVectorKernel (fun _ : Fin 2 => (s : Complex)) ![t₁,t₂] m n-
      (logSineA s : Complex)^2‖ ≤ E₀ := by
    rw [hconst, harmonicVectorKernel_two, pow_two]
    rw [complexLogSineA_ofReal] at hz
    norm_num only [add_zero, one_pow, mul_one] at hz
    exact hz.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_self (Real.exp_pos _).le hH)) hD.le)
  have hE₀B : E₀ ≤ smoothingKernelEnvelope D x (smoothingExponentOne J) (smoothingExponentTwo J α) (smoothingExponentThree J) α := by
    unfold E₀ smoothingKernelEnvelope
    have hpow : 1 ≤ (1+x^(smoothingExponentOne J))^4 := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD.le)
      (show 0 ≤ (integrationFrequencyCutoff x (smoothingExponentTwo J α) : Real)^(-α)+Real.exp (-(smoothingExponentThree J*Real.log x)) by positivity)]
  exact (actual_normalizer_power_relative_error s hs ![t₁,t₂] m n q E₀ hE₀n h0).trans
    (hNormX E₀ q hq hE₀n hE₀B)

theorem polynomially_accurate_smoothing_l1 (p P J : Real) (hp : 0 < p) (hP : p ≤ P) (hJ : 0 < J) :
    ∃ u₁ > 0, ∃ u₂ > 0, ∃ u₃ > 0, ∀ᶠ x : Real in atTop,
      PolynomialSmoothingL1One p P J u₁ u₂ u₃ x ∧ PolynomialSmoothingL1Two p P J u₁ u₂ u₃ x := by
  let α := min (p/4) (1/2 : Real)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαp : α < p := (min_le_left _ _).trans_lt (by linarith)
  have hα1 : α ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨h1,h2,h3,_⟩ := smoothing_exponents_valid J α hJ hα
  exact ⟨_,h1,_,h2,_,h3,
    (polynomial_smoothing_l1_one p P J α hp hP hJ hα hαp hα1).and
      (polynomial_smoothing_l1_two p P J α hp hP hJ hα hαp hα1)⟩

#print axioms polynomially_accurate_smoothing_l1
end ConditionalSpectralAudit.FourierHarmonic
