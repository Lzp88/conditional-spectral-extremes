import ActualIntegratedFarMoment
import FineSmoothingData
import InitialDiophantineSet

/-! Uniform actual first and far second moments.  The smoothing exponents and the
polynomial path-mass exponent are supplied by the same established joint choice
as the near-pair argument; this theorem makes no second choice of constants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.KernelPath FineScales ReservoirScale ArithmeticArcs

theorem eventually_actual_regular_mean_far (p : Parameters) (hA : 0 < p.A₀)
    (hr : 0 < p.rStar) (κmin κmax η K_E C_E Cstar J u₁ u₂ u₃ : Real)
    (ha : 0 < κmin) (horder : κmin ≤ κmax) (hη : 0 ≤ η)
    (hJ : 1 ≤ J) (hJC : 1+2*Cstar < J)
    (hpoly : ∀ᶠ x : Real in atTop,
      PolynomialSmoothingL1One (criticalPoint κmax) (criticalPoint κmin) J u₁ u₂ u₃ x ∧
      PolynomialSmoothingL1Two (criticalPoint κmax) (criticalPoint κmin) J u₁ u₂ u₃ x)
    (ε : Real) (hε : 0 < ε) :
    ∀ᶠ n : Nat in atTop, ∀ κ ∈ Icc κmin κmax, ∀ q : Nat → Nat,
      Regular p n κ η K_E C_E q → ∀ G : Real,
      (L n)^(-Cstar) ≤ (referencePathMass p n κ G q
        (fineSmoothingNoise ((L n)^(-10 : Real)) (count p n))).toReal →
      ∀ D : Set (AddCircle (1 : Real)), MeasurableSet D →
        D ⊆ initialDiophantineSet (L n) u₂ u₃ p.rStar →
      pathIntegralScale p n κ G ((L n)^(-10 : Real)) q D*(1-ε) ≤
        ∫ z, (rawPathIntegral p n κ G ((L n)^(-10 : Real)) q D z).toReal
          ∂harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun j => q (j+1)) (count p n) ∧
      (∫ z in farPathPairs p n (L n) u₂ u₃ D,
        rawSecondMoment p n κ G ((L n)^(-10 : Real)) q (fineBlockLo p n) (fineBlockHi p n) z.1 z.2
          ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) ≤
        (pathIntegralScale p n κ G ((L n)^(-10 : Real)) q D)^2*(1+ε) := by
  have hb : 0 < κmax := ha.trans_le horder
  have hp : 0 < criticalPoint κmax := criticalPoint_pos hb
  have hpower : ∀ᶠ n : Nat in atTop, (L n)^(-J) < 1 := by
    have ht := (tendsto_rpow_neg_atTop (by linarith : 0 < J)).comp L_tendsto_atTop
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : Real)<1))
  filter_upwards [eventually_regular_fine_smoothing_data p hA hr κmax η hb hη,
    L_tendsto_atTop.eventually hpoly, L_tendsto_atTop.eventually_ge_atTop 1, hpower,
    L_tendsto_atTop.eventually (eventually_pathComparisonError_small J Cstar ε hJ hJC hε)]
    with n hdata hpol hn hpow herr
  intro κ hκ q hreg G hmass D hD hgood
  have hk : 0 < κ := ha.trans_le hκ.1
  have hs := criticalPoint_compact_bounds ha hκ.1 hκ.2
  have hgeo := hdata κ K_E C_E q hκ.2 hreg
  have hfd : FineMomentData p n q (L n) := ⟨hgeo.2.2.1.le,hgeo.2.2.2⟩
  have hδ : 0 < (L n)^(-10 : Real) := by positivity
  let _ : IsProbabilityMeasure (fineSmoothingNoise ((L n)^(-10 : Real)) (count p n)) :=
    fineSmoothingNoise_probability _ hδ _
  have hmass1 : (referencePathMass p n κ G q
      (fineSmoothingNoise ((L n)^(-10 : Real)) (count p n))).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (referencePathMass_le_one p n κ G q hk _)
  have he2 := herr (count p n) _ hgeo.2.1 hmass
  have he1 : pathComparisonError (count p n) (L n) J ≤ ε*
      (referencePathMass p n κ G q
        (fineSmoothingNoise ((L n)^(-10 : Real)) (count p n))).toReal := by
    apply he2.trans
    apply mul_le_mul_of_nonneg_left _ hε.le
    simpa only [pow_two, mul_one] using
      mul_le_mul_of_nonneg_left hmass1 ENNReal.toReal_nonneg
  have hgood' : D ⊆ (badOne (integrationFrequencyCutoff (L n) u₂)
      (Real.exp (-r p n+u₃*Real.log (L n))))ᶜ := by
    have heq : -r p n+u₃*Real.log (L n)=(-p.rStar+u₃)*Real.log (L n) := by
      unfold r ell
      ring
    simpa only [heq, initialDiophantineSet] using hgood
  exact ⟨actual_integrated_first_moment_lower p n κ G (criticalPoint κmax) (criticalPoint κmin)
      J u₁ u₂ u₃ (L n) ε hk hp hs.2.1 hs.2.2 hn hpow hpol.1 q hfd D hD hgood' he1,
    actual_integrated_far_moment_upper p n κ G (criticalPoint κmax) (criticalPoint κmin)
      J u₁ u₂ u₃ (L n) ε hk hp hs.2.1 hs.2.2 hn hpow hpol.2 q hfd D hD he2⟩

#print axioms eventually_actual_regular_mean_far
end ConditionalSpectralAudit.FourierHarmonic
