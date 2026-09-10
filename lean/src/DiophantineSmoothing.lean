import ActualKernelTotalVariation

/-! Genuine one- and two-point TV bounds from the actual Diophantine hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WithLp

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem uniform_actual_smoothing_one (pmin P alpha : Real) (hpP : pmin ≤ P)
    (ha : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ (s δ T K R a Delta : Real) (m n q : Nat) (t : AddCircle (1 : Real)),
      pmin ≤ s → s ≤ P → 0 < δ → 0 < T → 0 ≤ K → 0 < R → 0 < m →
      1 ≤ harmonicMass m n → Real.exp a ≤ m →
      (∀ k : Int, |(k : Real)| ≤ R → k ≠ 0 → Real.exp (-a+Delta) ≤ ‖k • t‖) →
      C*(1+T)^2*(R^(-alpha)+Real.exp (-Delta)) ≤ 1/2 →
      totalVariationDistance
        ((coordinateLaw (harmonicTiltSumLaw s (fun _ : Fin 1 => t) m n q) 0) ∗ tenUniformNoise δ)
        ((coordinateLaw (referenceVectorSumLaw s 1 q) 0) ∗ tenUniformNoise δ) ≤
      smoothingErrorOne P s δ T K (C*(1+T)^2*(R^(-alpha)+Real.exp (-Delta))) q := by
  obtain ⟨C,hC,hB⟩ := uniform_harmonic_phi_error_one pmin P alpha hpP ha hap ha1
  refine ⟨C,hC,?_⟩
  intro s δ T K R a Delta m n q t hsp hsP hδ hT hK hR hm hH ham hsep hsmall
  have hs : 0 < s := by linarith
  apply actual_kernel_totalVariation_one s P δ T K _ hs hsP hδ hT hK (by positivity) hsmall
    t m n q (by linarith)
  intro u hu
  have hh := hB ((s : Complex)+u*Complex.I) T R a Delta m n t
    (by simpa using hsp) (by simpa using hsP) (by simpa using hu) hR hm (by linarith) ham hsep
  rw [harmonicVectorKernel_one]
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (div_le_self (Real.exp_pos _).le hH)) (by positivity)

theorem uniform_actual_smoothing_two (pmin P alpha : Real) (hpP : pmin ≤ P)
    (ha : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ (s δ T K R a Delta : Real) (m n q : Nat) (t₁ t₂ : AddCircle (1 : Real)),
      pmin ≤ s → s ≤ P → 0 < δ → 0 < T → 0 ≤ K → 0 < R → 0 < m →
      1 ≤ harmonicMass m n → Real.exp a ≤ m →
      (∀ k : Int × Int, (|(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R) → k ≠ 0 →
        Real.exp (-a+Delta) ≤ ‖k.1 • t₁+k.2 • t₂‖) →
      C*(1+T)^4*(R^(-alpha)+Real.exp (-Delta)) ≤ 1/2 →
      pairTotalVariationDistance
        ((pairVectorLaw (harmonicTiltSumLaw s ![t₁,t₂] m n q)) ∗ pairUniformNoise δ)
        ((pairVectorLaw (referenceVectorSumLaw s 2 q)) ∗ pairUniformNoise δ) ≤
      smoothingErrorTwo P s δ T K (C*(1+T)^4*(R^(-alpha)+Real.exp (-Delta))) q := by
  obtain ⟨C,hC,hB⟩ := uniform_harmonic_phi_error_two pmin P alpha hpP ha hap ha1
  refine ⟨C,hC,?_⟩
  intro s δ T K R a Delta m n q t₁ t₂ hsp hsP hδ hT hK hR hm hH ham hsep hsmall
  have hs : 0 < s := by linarith
  apply actual_kernel_totalVariation_two s P δ T K _ hs hsP hδ hT hK (by positivity) hsmall
    ![t₁,t₂] m n q (by linarith)
  intro u hu
  have hh := hB ((s : Complex)+u 0*Complex.I) ((s : Complex)+u 1*Complex.I)
    T R a Delta m n t₁ t₂
    (by simpa using hsp) (by simpa using hsP) (by simpa using hsp) (by simpa using hsP)
    (by simpa using hu 0) (by simpa using hu 1) hR hm (by linarith) ham hsep
  have he : (fun v => (s : Complex)+u v*Complex.I) = ![(s : Complex)+u 0*Complex.I,(s : Complex)+u 1*Complex.I] := by
    ext v; fin_cases v <;> rfl
  rw [he, harmonicVectorKernel_two]
  simp only [Fin.prod_univ_two]
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (div_le_self (Real.exp_pos _).le hH)) (by positivity)

#print axioms uniform_actual_smoothing_one
#print axioms uniform_actual_smoothing_two
end ConditionalSpectralAudit.FourierHarmonic
