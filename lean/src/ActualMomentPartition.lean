import ActualIntegratedFarMoment

/-! Exact real second-moment partition, on the actual arithmetic bad-pair set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath FineScales ArithmeticArcs

theorem actual_second_moment_partition (p : Parameters) (n : Nat)
    (κ G δ x u₂ u₃ : Real) (hκ : 0 < κ) (hδ : 0 < δ) (q : Nat → Nat)
    (hH : ∀ i < count p n, 0 < harmonicMass (fineBlockLo p n i) (fineBlockHi p n i))
    (D : Set (AddCircle (1 : Real))) (hD : MeasurableSet D) :
    (∫ z, (rawPathIntegral p n κ G δ q D z).toReal^2
      ∂harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun j => q (j+1)) (count p n)) =
      (∫ z in farPathPairs p n x u₂ u₃ D,
        rawSecondMoment p n κ G δ q (fineBlockLo p n) (fineBlockHi p n) z.1 z.2
          ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) +
      ∫ z in (D ×ˢ D) ∩ badPair (integrationFrequencyCutoff x u₂) (Real.exp (-r p n+u₃*Real.log x)),
        rawSecondMoment p n κ G δ q (fineBlockLo p n) (fineBlockHi p n) z.1 z.2
          ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
  rw [rawPathIntegral_second_moment_real p n κ G δ hκ hδ]
  have hi := rawSecondMoment_integrable p n κ G δ hκ hδ q (fineBlockLo p n) (fineBlockHi p n) hH
    (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
  have hdis : Disjoint (farPathPairs p n x u₂ u₃ D)
      ((D ×ˢ D) ∩ badPair (integrationFrequencyCutoff x u₂) (Real.exp (-r p n+u₃*Real.log x))) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hz.2 hz'.2
  have hcover : farPathPairs p n x u₂ u₃ D ∪
      ((D ×ˢ D) ∩ badPair (integrationFrequencyCutoff x u₂) (Real.exp (-r p n+u₃*Real.log x))) = D ×ˢ D := by
    unfold farPathPairs
    ext z
    simp only [mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  conv_lhs => rw [← hcover]
  exact setIntegral_union hdis ((hD.prod hD).inter (badPair_measurable _ _)) hi.integrableOn hi.integrableOn

#print axioms actual_second_moment_partition
end ConditionalSpectralAudit.FourierHarmonic
