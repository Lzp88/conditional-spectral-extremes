import ShortRestorationAlgebra
import IntegratedHighPointProbability

/-! Actual low/middle polynomial localization from the same integrated
path moments and middle upper tail. No replacement probability model. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales CoarseBoxes ArithmeticArcs ReservoirScale

def rawShortPolynomial {p : Parameters} {n : Nat} {q : Nat → Nat} {q₀ : Nat}
    (j : Fin q₀ → Nat) (x : FineRawSample p n q) : Polynomial Complex :=
  lowCyclePolynomial j*harmonicSamplePolynomial (q := fun i => q (i+1)) x

def rawShortCenter (p : Parameters) (n : Nat) (κ : Real) (q : Nat → Nat) (q₀ : Nat) : Real :=
  (aStar n+lambda (criticalPoint κ)*((countPrefix q (count p n) : Real)+q₀))/criticalPoint κ

def shortRestorationConstant (smin rStar K C₂ Cmid : Real) : Real :=
  Cmid+(1/smin+K*Real.log 2+C₂)*rStar+1

theorem actual_short_localization_at_sample (p : Parameters) (n : Nat) (κ G δ smin K C₂ Cmid : Real)
    (q : Nat → Nat) (D : Set Torus) (hD : MeasurableSet D) (hδ : 0 < δ)
    (hsmin : 0 < smin) (hss : smin ≤ criticalPoint κ) (hell : 0 ≤ ell n)
    (hr : 0 ≤ p.rStar) (hK : 0 ≤ K) (hC₂ : 0 ≤ C₂) (hCmid : 0 ≤ Cmid)
    {q₀ : Nat} (j : Fin q₀ → Nat) (hj : ∀ v, 0 < j v)
    (hq : (q₀ : Real) ≤ K*p.rStar*ell n) (hnoise : (count p n : Real)*δ ≤ ell n)
    (hgood : D ⊆ lowGoodSet j (C₂*p.rStar*ell n)) (x : FineRawSample p n q)
    (hZ : 0 < rawPathIntegral p n κ G δ q D x)
    (hmid : Real.log (circleNorm (harmonicSamplePolynomial (q := fun i => q (i+1)) x)) ≤
      (aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+Cmid*ell n) :
    |Real.log (circleNorm (rawShortPolynomial j x))-rawShortCenter p n κ q q₀| ≤
      shortRestorationConstant smin p.rStar K C₂ Cmid*ell n := by
  obtain ⟨t,_,_,hrf,_⟩ := rawPathIntegral_positive_high_point p n κ G δ q D hD x hδ hZ
  have hPt := rawMiddleRootFree_polynomial_eval_ne_zero p n q t x hrf
  have hP : harmonicSamplePolynomial (q := fun i => q (i+1)) x ≠ 0 := by
    intro hz
    simp [hz] at hPt
  have hu := low_polynomial_restoration_upper j hj _ hP
  have hl := rawPathIntegral_positive_low_restoration p n κ G δ q D hD x hδ j hj
    (C₂*p.rStar*ell n) hgood hZ
  change (aStar n-p.rStar*ell n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ-
    (count p n : Real)*δ-C₂*p.rStar*ell n ≤ _ at hl
  exact restored_short_height_bound smin (criticalPoint κ) (aStar n) (ell n) p.rStar K C₂ Cmid
    ((count p n : Real)*δ) (countPrefix q (count p n)) q₀ _ _ hsmin hss hell hr hK hC₂ hCmid
    (Nat.cast_nonneg _) hq hnoise hmid hu hl

theorem actual_short_failure_probability_from_moments
    (p : Parameters) (n : Nat) (κ G δ smin K C₂ Cmid : Real)
    (q : Nat → Nat) (D : Set Torus) (hD : MeasurableSet D) (hκ : 0 < κ) (hδ : 0 < δ)
    (hsmin : 0 < smin) (hss : smin ≤ criticalPoint κ) (hell : 0 ≤ ell n)
    (hr : 0 ≤ p.rStar) (hK : 0 ≤ K) (hC₂ : 0 ≤ C₂) (hCmid : 0 ≤ Cmid)
    {q₀ : Nat} (j : Fin q₀ → Nat) (hj : ∀ v, 0 < j v)
    (hq : (q₀ : Real) ≤ K*p.rStar*ell n) (hnoise : (count p n : Real)*δ ≤ ell n)
    (hgood : D ⊆ lowGoodSet j (C₂*p.rStar*ell n))
    (μ : Measure (FineRawSample p n q)) [IsProbabilityMeasure μ]
    (M ε : Real) (hM : 0 < M) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hfirst : M*(1-ε) ≤ ∫ x, (rawPathIntegral p n κ G δ q D x).toReal ∂μ)
    (hsecond : (∫ x, ((rawPathIntegral p n κ G δ q D x).toReal)^2 ∂μ) ≤ M^2*(1+ε)) :
    μ {x | shortRestorationConstant smin p.rStar K C₂ Cmid*ell n <
      |Real.log (circleNorm (rawShortPolynomial j x))-rawShortCenter p n κ q q₀|} ≤
    μ {x | (aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+Cmid*ell n ≤
      Real.log (circleNorm (harmonicSamplePolynomial (q := fun i => q (i+1)) x))}+
      ENNReal.ofReal (12*ε) := by
  let U : Set (FineRawSample p n q) := {x |
    (aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+Cmid*ell n ≤
      Real.log (circleNorm (harmonicSamplePolynomial (q := fun i => q (i+1)) x))}
  let V : Set (FineRawSample p n q) := {x | (rawPathIntegral p n κ G δ q D x).toReal ≤ 0}
  have hV : μ V ≤ ENNReal.ofReal (12*ε) := second_moment_failure_bound μ _
    (rawPathIntegral_toReal_memLp p n κ G δ hκ hδ q D μ 2) M ε hM hε hεsmall hfirst hsecond
  have hsub : {x | shortRestorationConstant smin p.rStar K C₂ Cmid*ell n <
      |Real.log (circleNorm (rawShortPolynomial j x))-rawShortCenter p n κ q q₀|} ⊆ U ∪ V := by
    intro x hx
    by_contra hn
    have hnotU : x ∉ U := fun hu => hn (Or.inl hu)
    have hnotV : x ∉ V := fun hv => hn (Or.inr hv)
    have hZ : 0 < rawPathIntegral p n κ G δ q D x := by
      apply lt_of_not_ge
      intro hz
      have he : rawPathIntegral p n κ G δ q D x=0 := le_antisymm hz zero_le
      exact hnotV (by simp [V,he])
    have hm : Real.log (circleNorm (harmonicSamplePolynomial (q := fun i => q (i+1)) x)) ≤
        (aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+Cmid*ell n := by
      exact le_of_lt (lt_of_not_ge hnotU)
    have hh := actual_short_localization_at_sample p n κ G δ smin K C₂ Cmid q D hD hδ hsmin hss
      hell hr hK hC₂ hCmid j hj hq hnoise hgood x hZ hm
    exact (not_lt_of_ge hh) hx
  exact (measure_mono hsub).trans ((measure_union_le U V).trans (add_le_add le_rfl hV))

#print axioms actual_short_localization_at_sample
#print axioms actual_short_failure_probability_from_moments
end ConditionalSpectralAudit.FourierHarmonic
