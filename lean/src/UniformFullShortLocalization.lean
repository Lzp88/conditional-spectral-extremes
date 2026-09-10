import UniformActualPathMoments
import UniformMiddleMaximum
import RandomLowShortLocalization
import FullShortSamplingProbability
import FineNoiseScales
import ParameterOrderAlgebra

/-! Complete actual harmonic short-polynomial localization. Box, smoothing,
barrier, and angular-set constants are chosen once before every epsilon. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ReservoirScale ArithmeticArcs

theorem uniform_full_short_harmonic_localization {a B : Real}
    (ha : 0 < a) (haB : a ≤ B) (K_E C_E K : Real) (hKE : 0 ≤ K_E) (hCE : 0 ≤ C_E) (hK : 0 ≤ K) :
    ∃ η D₀ : Real, 0 < η ∧ 0 < D₀ ∧ ∀ A₀ : Real, 0 < A₀ →
      ∃ rStar C : Real, 0 < rStar ∧ 0 < C ∧
        ∀ ε : Real, 0 < ε → ∀ᶠ n : Nat in atTop, ∀ κ ∈ Icc a B, ∀ q : Nat → Nat,
          Regular ⟨A₀,rStar,D₀⟩ n κ η K_E C_E q →
          (q 0 : Real) ≤ K*rStar*ell n →
          fullShortHarmonicLaw ⟨A₀,rStar,D₀⟩ n q
            {jx | C*ell n < |Real.log (circleNorm (rawShortPolynomial jx.1 jx.2))-
              rawShortCenter ⟨A₀,rStar,D₀⟩ n κ q (q 0)|} ≤ ENNReal.ofReal ε := by
  obtain ⟨η,Cmid,hη,hCmid,hupper⟩ := uniform_harmonic_middle_maximum_upper ha haB
  obtain ⟨D₀,Cstar,hD₀,hCstar,_hmass,hchoose⟩ := actual_regular_path_moments a B K_E C_E ha haB hKE hCE
  have hJ := manuscriptPrecision_bounds Cstar hCstar.le
  obtain ⟨u₁,hu₁,u₂,hu₂,u₃,hu₃,_hpoly,hmom⟩ :=
    hchoose (manuscriptPrecision Cstar) hJ.1 (by linarith [hJ.2.1])
  have hsmin : 0 < criticalPoint B := criticalPoint_pos (ha.trans_le haB)
  refine ⟨η,D₀,hη,hD₀,?_⟩
  intro A₀ hA
  obtain ⟨rmin,hrmin,hup⟩ := hupper A₀ hA
  let g := manuscriptGap (criticalPoint B) A₀ u₂ u₃ Cstar
  have hg := manuscriptGap_bounds (criticalPoint B) A₀ u₂ u₃ Cstar hsmin
  let rStar := manuscriptReservoir (criticalPoint a) g A₀ u₂ u₃ rmin
  have hr := manuscriptReservoir_bounds (criticalPoint a) g A₀ u₂ u₃ rmin
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  let C := shortRestorationConstant (criticalPoint B) rStar K (lowRestorationCoefficient K) Cmid
  have hC₂ : 0 ≤ lowRestorationCoefficient K := by
    unfold lowRestorationCoefficient
    nlinarith [negativeLogSineMass_nonneg]
  have hC : 0 < C := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [C,shortRestorationConstant]
    have hrpos : 0 < rStar := hr.1
    positivity
  refine ⟨rStar,C,hr.1,hC,?_⟩
  intro ε hε
  let e : Real := min (ε/26) (1/4)
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have heε : 13*e ≤ ε := by
    have hh : e ≤ ε/26 := min_le_left _ _
    linarith
  have hneg : 1+2*u₂+u₃+A₀+2*Cstar < criticalPoint B*g := by linarith [hg.2.1]
  have hrD : u₂+u₃ < rStar := by linarith [hr.2.2.1]
  filter_upwards [hmom A₀ g rStar η hA hg.1 hr.1 hη.le hr.2.1.le hneg e he,
    hup rStar D₀ hr.2.2.2.le e he,
    eventually_full_short_sampling_probability p hA hr.1,
    eventually_fine_noise_margins p hA hr.1 1 (by norm_num),
    initialDiophantineSet_compl_eventually_small u₂ u₃ rStar hu₂.le hrD (1/8) (by norm_num),
    ell_tendsto_atTop.eventually_gt_atTop 0]
    with n hmoment hmax hsampling hnoise hDsmall hell
  intro κ hκ q hreg hq
  let μ := harmonicMiddleSampleLaw (fineBlockLo p n) (fineBlockHi p n) (fun i => q (i+1)) (count p n)
  let μ₀ := harmonicBlockSampleLaw 1 (fineBlockLo p n 0) (q 0)
  let _ := harmonicMiddleSampleLaw_probability (fineBlockLo p n) (fineBlockHi p n)
    (fun i => q (i+1)) (count p n) hsampling.2.1
  let _ := harmonicBlockSampleLaw_probability 1 (fineBlockLo p n 0) (q 0) hsampling.1
  let Dbase := initialDiophantineSet (L n) u₂ u₃ rStar
  have hDs : haar.real Dbaseᶜ ≤ 1/8 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hDsmall
    simpa only [Dbase,measureReal_def,ENNReal.toReal_ofReal (by norm_num : (0 : Real)≤1/8)] using hh
  have hk : 0 < κ := ha.trans_le hκ.1
  have hs := criticalPoint_compact_bounds ha hκ.1 hκ.2
  have hactualmom : ∀ D : Set Torus, MeasurableSet D → D ⊆ Dbase → 1/2 ≤ haar.real D →
      ∃ M : Real, 0 < M ∧
        M*(1-e) ≤ ∫ x, (rawPathIntegral p n κ (g*ell n) ((L n)^(-10 : Real)) q D x).toReal ∂μ ∧
        (∫ x, ((rawPathIntegral p n κ (g*ell n) ((L n)^(-10 : Real)) q D x).toReal)^2 ∂μ) ≤ M^2*(1+e) := by
    intro D hD hsub hmassD
    have hh := hmoment κ hκ q hreg D hD hsub hmassD
    exact ⟨pathIntegralScale p n κ (g*ell n) ((L n)^(-10 : Real)) q D,hh.1,hh.2⟩
  have hb := actual_random_low_short_probability p n κ (g*ell n) ((L n)^(-10 : Real))
    (criticalPoint B) K Cmid q Dbase (initialDiophantineSet_measurable _ _ _ _) hDs
    hk hnoise.1 hsmin hs.2.1 hell hr.1 hK hCmid.le (by simpa only [one_mul] using hnoise.2.1)
    μ e he.le he1 hactualmom (hmax κ K_E C_E q hκ hreg) μ₀ (low_harmonic_sample_positive p n (q 0)) hq
  exact hb.trans (ENNReal.ofReal_le_ofReal heε)

#print axioms uniform_full_short_harmonic_localization
end ConditionalSpectralAudit.FourierHarmonic
