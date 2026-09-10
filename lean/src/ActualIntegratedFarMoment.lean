import ActualIntegratedPathMean

/-! The actual far part of E[Z_D^2], on the same arithmetic partition as the near proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath FineScales ArithmeticArcs

theorem actual_integrated_far_moment_upper (p : Parameters) (n : Nat)
    (κ G pmin P J u₁ u₂ u₃ x ε : Real) (hκ : 0 < κ) (hp : 0 < pmin)
    (hsp : pmin ≤ criticalPoint κ) (hsP : criticalPoint κ ≤ P)
    (hx : 1 ≤ x) (heps : x^(-J) < 1)
    (hpoly : PolynomialSmoothingL1Two pmin P J u₁ u₂ u₃ x)
    (q : Nat → Nat) (hdata : FineMomentData p n q x)
    (D : Set (AddCircle (1 : Real))) (hD : MeasurableSet D)
    (herror : pathComparisonError (count p n) x J ≤ ε*
      (referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal^2) :
    (∫ z in farPathPairs p n x u₂ u₃ D,
      rawSecondMoment p n κ G (x^(-10 : Real)) q (fineBlockLo p n) (fineBlockHi p n) z.1 z.2
      ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) ≤
      (pathIntegralScale p n κ G (x^(-10 : Real)) q D)^2*(1+ε) := by
  have hδ : 0 < x^(-10 : Real) := by positivity
  have hH (i : Nat) (hi : i < count p n) : 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) :=
    lt_of_lt_of_le zero_lt_one (hdata.2 i hi).2.2.1
  have hpoint (z : AddCircle (1 : Real) × AddCircle (1 : Real)) (hz : z ∈ farPathPairs p n x u₂ u₃ D) :=
    actual_second_moment_comparison p n κ G pmin P J u₁ u₂ u₃ x hκ hp hsp hsP hx heps hpoly
      q (fineBlockLo p n) (fineBlockHi p n) (coordinate p n) z.1 z.2
      (fun i hi => (hdata.2 i hi).1) (fun i hi => (hdata.2 i hi).2.1)
      (fun i hi => (hdata.2 i hi).2.2.1) (fun i hi => (hdata.2 i hi).2.2.2)
      (fun i _ => good_pair_separated_all_fine p n _ i _ hdata.1 z.1 z.2 hz.2)
  have hu := setIntegral_upper_of_normalized_error
    (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (farPathPairs p n x u₂ u₃ D)
    (farPathPairs_measurable p n x u₂ u₃ D hD)
    (fun z => rawSecondMoment p n κ G (x^(-10 : Real)) q (fineBlockLo p n) (fineBlockHi p n) z.1 z.2)
    (rawSecondMoment_integrable p n κ G (x^(-10 : Real)) hκ hδ q (fineBlockLo p n) (fineBlockHi p n) hH _)
    ((pathMomentScale p n κ q)^2)
    ((referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal^2)
    (pathComparisonError (count p n) x J) (sq_pos_of_pos (pathMomentScale_pos p n κ hκ q)) hpoint
  have harea : (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle).real (farPathPairs p n x u₂ u₃ D) ≤
      (AddCircle.haarAddCircle.real D)^2 := by
    have hh := ENNReal.toReal_mono
      (measure_ne_top (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (D ×ˢ D))
      (measure_mono (show farPathPairs p n x u₂ u₃ D ⊆ D ×ˢ D from inter_subset_left))
    simpa only [← measureReal_def, measureReal_prod_prod, pow_two] using hh
  have hEn := pathComparisonError_nonneg (count p n) x J (by linarith)
  calc
    _ ≤ _ := hu
    _ ≤ (AddCircle.haarAddCircle.real D)^2*(pathMomentScale p n κ q)^2*
        ((referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal^2+
          pathComparisonError (count p n) x J) := by gcongr
    _ ≤ (AddCircle.haarAddCircle.real D)^2*(pathMomentScale p n κ q)^2*
        ((referencePathMass p n κ G q (fineSmoothingNoise (x^(-10 : Real)) (count p n))).toReal^2*(1+ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by unfold pathIntegralScale; ring

#print axioms actual_integrated_far_moment_upper
end ConditionalSpectralAudit.FourierHarmonic
