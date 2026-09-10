import RawShortLocalization
import ConditionalSampleIntegration

/-! The low-dependent angular set is selected before integrating the
independent middle sample. Its actual Haar mass is bounded uniformly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ArithmeticArcs ReservoirScale

def lowRestorationCoefficient (K : Real) : Real := 8*K*negativeLogSineMass+1

theorem actual_fixed_low_short_probability
    (p : Parameters) (n : Nat) (κ G δ smin K Cmid : Real) (q : Nat → Nat)
    (Dbase : Set Torus) (hDbase : MeasurableSet Dbase) (hDsmall : haar.real Dbaseᶜ ≤ 1/8)
    (hκ : 0 < κ) (hδ : 0 < δ) (hsmin : 0 < smin) (hss : smin ≤ criticalPoint κ)
    (hell : 0 < ell n) (hr : 0 < p.rStar) (hK : 0 ≤ K) (hCmid : 0 ≤ Cmid)
    (hnoise : (count p n : Real)*δ ≤ ell n)
    (μ : Measure (FineRawSample p n q)) [IsProbabilityMeasure μ]
    (ε : Real) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hmom : ∀ D : Set Torus, MeasurableSet D → D ⊆ Dbase → 1/2 ≤ haar.real D →
      ∃ M : Real, 0 < M ∧
        M*(1-ε) ≤ ∫ x, (rawPathIntegral p n κ G δ q D x).toReal ∂μ ∧
        (∫ x, ((rawPathIntegral p n κ G δ q D x).toReal)^2 ∂μ) ≤ M^2*(1+ε))
    (hupper : μ {x | (aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+Cmid*ell n ≤
      Real.log (circleNorm (harmonicSamplePolynomial (q := fun i => q (i+1)) x))} ≤ ENNReal.ofReal ε)
    {q₀ : Nat} (j : Fin q₀ → Nat) (hj : ∀ v, 0 < j v)
    (hq : (q₀ : Real) ≤ K*p.rStar*ell n) :
    μ {x | shortRestorationConstant smin p.rStar K (lowRestorationCoefficient K) Cmid*ell n <
      |Real.log (circleNorm (rawShortPolynomial j x))-rawShortCenter p n κ q q₀|} ≤
      ENNReal.ofReal (13*ε) := by
  let C₂ := lowRestorationCoefficient K
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂,lowRestorationCoefficient]
    nlinarith [negativeLogSineMass_nonneg]
  let D : Set Torus := Dbase ∩ lowGoodSet j (C₂*p.rStar*ell n)
  have hD : MeasurableSet D := hDbase.inter (lowGoodSet_measurable _ _)
  have hlarge : 1/2 ≤ haar.real D := by
    have hh := actual_low_good_set_large j hj K (p.rStar*ell n) hK (mul_pos hr hell)
      (by simpa only [mul_assoc] using hq) Dbase hDbase hDsmall
    change 3/4 ≤ haar.real (Dbase ∩ lowGoodSet j ((8*K*negativeLogSineMass+1)*(p.rStar*ell n))) at hh
    have he : (8*K*negativeLogSineMass+1)*(p.rStar*ell n)=C₂*p.rStar*ell n := by
      dsimp [C₂,lowRestorationCoefficient]
      ring
    rw [he] at hh
    exact (by norm_num : (1/2 : Real)≤3/4).trans hh
  obtain ⟨M,hM,hfirst,hsecond⟩ := hmom D hD inter_subset_left hlarge
  have hh := actual_short_failure_probability_from_moments p n κ G δ smin K C₂ Cmid q D hD
    hκ hδ hsmin hss hell.le hr.le hK hC₂ hCmid j hj hq hnoise inter_subset_right
    μ M ε hM hε hεsmall hfirst hsecond
  apply hh.trans
  calc
    _ ≤ ENNReal.ofReal ε+ENNReal.ofReal (12*ε) := add_le_add hupper le_rfl
    _ = ENNReal.ofReal (13*ε) := by rw [← ENNReal.ofReal_add hε (by positivity)]; congr 1; ring

theorem actual_random_low_short_probability
    (p : Parameters) (n : Nat) (κ G δ smin K Cmid : Real) (q : Nat → Nat)
    (Dbase : Set Torus) (hDbase : MeasurableSet Dbase) (hDsmall : haar.real Dbaseᶜ ≤ 1/8)
    (hκ : 0 < κ) (hδ : 0 < δ) (hsmin : 0 < smin) (hss : smin ≤ criticalPoint κ)
    (hell : 0 < ell n) (hr : 0 < p.rStar) (hK : 0 ≤ K) (hCmid : 0 ≤ Cmid)
    (hnoise : (count p n : Real)*δ ≤ ell n)
    (μ : Measure (FineRawSample p n q)) [IsProbabilityMeasure μ]
    (ε : Real) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hmom : ∀ D : Set Torus, MeasurableSet D → D ⊆ Dbase → 1/2 ≤ haar.real D →
      ∃ M : Real, 0 < M ∧
        M*(1-ε) ≤ ∫ x, (rawPathIntegral p n κ G δ q D x).toReal ∂μ ∧
        (∫ x, ((rawPathIntegral p n κ G δ q D x).toReal)^2 ∂μ) ≤ M^2*(1+ε))
    (hupper : μ {x | (aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+Cmid*ell n ≤
      Real.log (circleNorm (harmonicSamplePolynomial (q := fun i => q (i+1)) x))} ≤ ENNReal.ofReal ε)
    {q₀ : Nat} (μ₀ : Measure (Fin q₀ → Nat)) [IsProbabilityMeasure μ₀]
    (hj : ∀ᵐ j ∂μ₀, ∀ v, 0 < j v) (hq : (q₀ : Real) ≤ K*p.rStar*ell n) :
    (μ₀.prod μ) {jx | shortRestorationConstant smin p.rStar K (lowRestorationCoefficient K) Cmid*ell n <
      |Real.log (circleNorm (rawShortPolynomial jx.1 jx.2))-rawShortCenter p n κ q q₀|} ≤
      ENNReal.ofReal (13*ε) := by
  apply independent_countable_event_bound μ₀ μ _ _
  filter_upwards [hj] with j hj
  exact actual_fixed_low_short_probability p n κ G δ smin K Cmid q Dbase hDbase hDsmall
    hκ hδ hsmin hss hell hr hK hCmid hnoise μ ε hε hεsmall hmom hupper j hj hq

#print axioms actual_fixed_low_short_probability
#print axioms actual_random_low_short_probability
end ConditionalSpectralAudit.FourierHarmonic
