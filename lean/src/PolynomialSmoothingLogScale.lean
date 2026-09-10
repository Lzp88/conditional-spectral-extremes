import PolynomialSmoothing

/-! The actual manuscript scale L(n)=log n in the full smoothing theorem. -/
noncomputable section
open Filter
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes.ReservoirScale

theorem polynomially_accurate_smoothing_log_scale (p P J : Real)
    (hp : 0 < p) (hP : p ≤ P) (hJ : 0 < J) :
    ∃ u₁ > 0, ∃ u₂ > 0, ∃ u₃ > 0, ∀ᶠ n : Nat in atTop,
      PolynomialSmoothingOne p P J u₁ u₂ u₃ (L n) ∧
        PolynomialSmoothingTwo p P J u₁ u₂ u₃ (L n) := by
  obtain ⟨u₁,h1,u₂,h2,u₃,h3,hh⟩ := polynomially_accurate_smoothing p P J hp hP hJ
  exact ⟨u₁,h1,u₂,h2,u₃,h3,L_tendsto_atTop.eventually hh⟩

#print axioms polynomially_accurate_smoothing_log_scale
end ConditionalSpectralAudit.FourierHarmonic
