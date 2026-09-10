import IntegratedHighPoint
import RawPathUniformBound
import SecondMomentFailure

/-! Actual integrated path moments imply high points of the actual
polynomial, including all low factors. All L2 hypotheses are discharged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales CoarseBoxes ArithmeticArcs

theorem actual_integrated_high_point_probability (p : Parameters) (n : Nat) (κ G δ : Real)
    (q : Nat → Nat) (D : Set Torus) (hD : MeasurableSet D) (hκ : 0 < κ) (hδ : 0 < δ)
    (μ : Measure (FineRawSample p n q)) [IsProbabilityMeasure μ]
    {q₀ : Nat} (j : Fin q₀ → Nat) (hj : ∀ v, 0 < j v) (u : Real)
    (hgood : D ⊆ lowGoodSet j u) (M ε : Real) (hM : 0 < M) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hfirst : M*(1-ε) ≤ ∫ x, (rawPathIntegral p n κ G δ q D x).toReal ∂μ)
    (hsecond : (∫ x, ((rawPathIntegral p n κ G δ q D x).toReal)^2 ∂μ) ≤ M^2*(1+ε)) :
    μ {x | Real.log (circleNorm (lowCyclePolynomial j*
      harmonicSamplePolynomial (q := fun i => q (i+1)) x)) <
        terminalHeight p n κ q-(count p n : Real)*δ-u} ≤ ENNReal.ofReal (12*ε) := by
  have hX := rawPathIntegral_toReal_memLp p n κ G δ hκ hδ q D μ 2
  apply (measure_mono (show
    {x | Real.log (circleNorm (lowCyclePolynomial j*harmonicSamplePolynomial (q := fun i => q (i+1)) x)) <
      terminalHeight p n κ q-(count p n : Real)*δ-u} ⊆
    {x | (rawPathIntegral p n κ G δ q D x).toReal ≤ 0} from ?_)).trans
    (second_moment_failure_bound μ _ hX M ε hM hε hεsmall hfirst hsecond)
  intro x hx
  have hzero : rawPathIntegral p n κ G δ q D x=0 := by
    apply le_antisymm _ zero_le
    apply le_of_not_gt
    intro hpos
    have hh := rawPathIntegral_positive_low_restoration p n κ G δ q D hD x hδ j hj u hgood hpos
    exact (not_lt_of_ge hh) hx
  simp only [mem_ofPred_eq, hzero, ENNReal.toReal_zero, le_refl]

#print axioms actual_integrated_high_point_probability
end ConditionalSpectralAudit.FourierHarmonic
