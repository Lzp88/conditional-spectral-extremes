import HarmonicSampleMaximum
import UniformIntegratedMiddleMoment
import FineSamplingBounds
import MiddleMaximumAlgebra

/-! The manuscript's uniform upper localization for the actual harmonic
middle polynomial, with the genuine regular environment and critical root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Real BigOperators ENNReal Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales ArithmeticArcs ReservoirScale

theorem uniform_harmonic_middle_maximum_upper {a B : Real} (ha : 0 < a) (haB : a ≤ B) :
    ∃ η C : Real, 0 < η ∧ 0 < C ∧ ∀ A₀ : Real, 0 < A₀ → ∃ r₀ : Real, 0 < r₀ ∧
      ∀ rStar D₀ : Real, r₀ ≤ rStar → ∀ ε : Real, 0 < ε → ∀ᶠ n : Nat in atTop,
        ∀ (κ K_E C_E : Real) (q : Nat → Nat), κ ∈ Icc a B →
        Regular ⟨A₀,rStar,D₀⟩ n κ η K_E C_E q →
        harmonicMiddleSampleLaw (fineBlockLo ⟨A₀,rStar,D₀⟩ n)
          (fineBlockHi ⟨A₀,rStar,D₀⟩ n) (fun i => q (i+1)) (count ⟨A₀,rStar,D₀⟩ n)
          {x | (aStar n+lambda (criticalPoint κ)*(countPrefix q (count ⟨A₀,rStar,D₀⟩ n)))/
              criticalPoint κ+C*ell n ≤ Real.log (circleNorm (harmonicSamplePolynomial
                (m := count ⟨A₀,rStar,D₀⟩ n) (q := fun i => q (i+1)) x))} ≤
          ENNReal.ofReal ε := by
  obtain ⟨η,hη,hint⟩ := uniform_integrated_middle_moment ha haB
  have hB : 0 < B := ha.trans_le haB
  let smin := criticalPoint B
  let S := criticalPoint a
  let C := 3/smin
  have hsmin : 0 < smin := criticalPoint_pos hB
  have hC : 0 < C := div_pos (by norm_num) hsmin
  refine ⟨η,C,hη,hC,?_⟩
  intro A₀ hA
  obtain ⟨r₀,hr₀,hrint⟩ := hint A₀ hA
  refine ⟨r₀,hr₀,?_⟩
  intro rStar D₀ hrStar ε hε
  let p : Parameters := ⟨A₀,rStar,D₀⟩
  have hr : 0 < p.rStar := hr₀.trans_le hrStar
  have hpow : Tendsto (fun n : Nat => (2*(B+η)/polynomialMomentConstant S)*(L n)^(-2 : Real))
      atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : Real)<2)).comp L_tendsto_atTop).const_mul
      (2*(B+η)/polynomialMomentConstant S)
    simpa only [Function.comp_def, mul_zero] using hh
  filter_upwards [hrint rStar D₀ hrStar 1 (by norm_num),
    eventually_harmonic_fine_geometry p hA hr, eventually_fine_scale_geometry p hA hr,
    eventually_aStar_le_L, (r_tendsto_atTop p hr).eventually_ge_atTop 0,
    cutoff_tendsto_atTop.eventually_ge_atTop 1, L_tendsto_atTop.eventually_ge_atTop 1,
    hpow.eventually (gt_mem_nhds hε)] with n hI hgeo hscales haL hrn hb hL hsmall
  intro κ K_E C_E q hκ hreg
  have hk : 0 < κ := ha.trans_le hκ.1
  have hs := criticalPoint_compact_bounds ha hκ.1 hκ.2
  have hspos : 0 < criticalPoint κ := criticalPoint_pos hk
  have hm : 0 < count p n := hscales.2.2.2.1
  have hQ := middle_count_positive p n κ η K_E C_E q hk hgeo.1 hm hreg
  have hQK := middle_count_le_scale p n κ η K_E C_E q (by positivity) hrn haL hm hreg
  have hQK' : ((countPrefix q (count p n)) : Real) ≤ (B+η)*L n :=
    hQK.trans (mul_le_mul_of_nonneg_right (by linarith [hκ.2]) (by linarith))
  have hcut : 0 < cutoff n := hb
  have ht := actual_harmonic_middle_maximum_tail (criticalPoint κ) S hspos hs.2.2
    (fineBlockLo p n) (fineBlockHi p n) (fun i => q (i+1)) (count p n) (cutoff n) hcut hQ
    (fun i _hi => (hgeo.2 i).1)
    (fun i hi => fineBlockHi_le_cutoff_add_one p n i hgeo.1.le hm hcut hi) 1
    ((aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/criticalPoint κ+C*ell n)
    (hI κ K_E C_E q hκ hreg)
  have hcancel := middle_maximum_tail_cancellation (criticalPoint κ) S (cutoff n) (L n) C 1
    (countPrefix q (count p n)) hspos (by exact_mod_cast hcut) (by linarith) hQ
  change logSineA (criticalPoint κ)^(countPrefix q (count p n))*(1+1)/
    (polynomialMomentConstant S/((cutoff n : Real)*countPrefix q (count p n))*
      Real.exp (criticalPoint κ*((aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/
        criticalPoint κ+C*ell n))) = _ at hcancel
  change _ ≤ ENNReal.ofReal (logSineA (criticalPoint κ)^(countPrefix q (count p n))*(1+1)/
    (polynomialMomentConstant S/((cutoff n : Real)*countPrefix q (count p n))*
      Real.exp (criticalPoint κ*((aStar n+lambda (criticalPoint κ)*countPrefix q (count p n))/
        criticalPoint κ+C*ell n)))) at ht
  rw [hcancel] at ht
  have hsC : 3 ≤ criticalPoint κ*C := by
    have he : smin*C=3 := by dsimp [C]; field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_right hs.2.1 hC.le
  have hbnd := middle_maximum_scale_bound (L n) (B+η) (polynomialMomentConstant S)
    (criticalPoint κ) C (countPrefix q (count p n)) hL (by positivity)
    (polynomialMomentConstant_pos S) (Nat.cast_nonneg _) hQK' hsC
  exact ht.trans (ENNReal.ofReal_le_ofReal (by simpa only [show (1+1 : Real)=2 by norm_num] using hbnd.trans hsmall.le))

#print axioms uniform_harmonic_middle_maximum_upper
end ConditionalSpectralAudit.FourierHarmonic
