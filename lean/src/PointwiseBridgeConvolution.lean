import BridgeReversal
import TiltedDensityPowerRegularity

/-! Pointwise identification of the actual hyperplane integral with the
continuous convolution version. The twofold identity is first established
almost everywhere; convolution with the third increment then gives equality
at every endpoint. This does not silently replace an a.e. density by a
pointwise chosen representative inside a null-event conditional law. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal Convolution

namespace ConditionalSpectralExtremes

theorem bridgePath_density_product (f : ℝ → ℝ) (n : ℕ) (d : ℝ) (x : Fin n → ℝ) :
    (∏ i, ENNReal.ofReal (f (bridgePath n d x i))) =
      (∏ i, ENNReal.ofReal (f (x i))) * ENNReal.ofReal (f (d-∑ i, x i)) := by
  rw [Fin.prod_univ_castSucc]
  simp only [bridgePath_castSucc, bridgePath_last]

theorem pointwiseBridge_zero (f : ℝ → ℝ) (d : ℝ) :
    pointwiseBridge f 0 d univ = ENNReal.ofReal (f d) := by
  rw [pointwiseBridge_univ]
  simp [volume_pi, Measure.pi_empty_univ]

theorem pointwiseBridge_succ (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (d : ℝ) :
    pointwiseBridge f (n+1) d univ =
      ∫⁻ a : ℝ, ENNReal.ofReal (f a) * pointwiseBridge f n (d-a) univ := by
  unfold pointwiseBridge
  rw [lintegral_fin_cons n _ (pointwiseBridge_integrand_measurable f hf (n+1) d univ .univ)]
  apply lintegral_congr
  intro a
  rw [← lintegral_const_mul _ (pointwiseBridge_integrand_measurable f hf n (d-a) univ .univ)]
  apply lintegral_congr
  intro x
  simp only [indicator_univ]
  rw [bridgePath_density_product, bridgePath_density_product,
    Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [show d-(a+∑ i, x i) = d-a-∑ i, x i by ring]
  simp only [mul_assoc]

theorem pointwiseBridge_one_eq_of_integrable (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (d : ℝ)
    (hi : Integrable (fun a => f a * f (d-a))) :
    pointwiseBridge f 1 d univ =
      ENNReal.ofReal ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] f) d) := by
  rw [pointwiseBridge_succ f hf 0 d]
  simp_rw [pointwiseBridge_zero, ← ENNReal.ofReal_mul (hfn _)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun a => mul_nonneg (hfn a) (hfn (d-a))))).symm

theorem pointwiseBridge_tilted_one_ae (β : ℝ) (hβ : -1 < β) :
    (fun d => pointwiseBridge (tiltedDensity β) 1 d univ) =ᵐ[volume]
      fun d => ENNReal.ofReal (tiltedDensityPower β 2 d) := by
  filter_upwards [(tiltedDensity_integrable β hβ).ae_convolution_exists
    (L := ContinuousLinearMap.mul ℝ ℝ) (tiltedDensity_integrable β hβ)] with d hd
  exact pointwiseBridge_one_eq_of_integrable _ (tiltedDensity_measurable β)
    (tiltedDensity_nonneg β) d hd

theorem pointwiseBridge_next_of_ae (β : ℝ) (n : ℕ) (d : ℝ)
    (he : (fun u => pointwiseBridge (tiltedDensity β) n u univ) =ᵐ[volume]
      fun u => ENNReal.ofReal (tiltedDensityPower β (n+1) u))
    (hi : ConvolutionExistsAt (tiltedDensityPower β (n+1)) (tiltedDensity β)
      d (ContinuousLinearMap.mul ℝ ℝ) volume) :
    pointwiseBridge (tiltedDensity β) (n+1) d univ =
      ENNReal.ofReal (tiltedDensityPower β (n+2) d) := by
  rw [pointwiseBridge_succ _ (tiltedDensity_measurable β) n d]
  have hs := he.comp_tendsto (Measure.measurePreserving_sub_left (volume : Measure ℝ) d).quasiMeasurePreserving.tendsto_ae
  calc
    _ = ∫⁻ a : ℝ, ENNReal.ofReal (tiltedDensityPower β (n+1) (d-a) * tiltedDensity β a) := by
      apply lintegral_congr_ae
      filter_upwards [hs] with a ha
      dsimp only [Function.comp_def] at ha
      rw [ha, ENNReal.ofReal_mul (tiltedDensityPower_nonneg β (n+1) _), mul_comm]
    _ = ENNReal.ofReal (∫ a, tiltedDensityPower β (n+1) (d-a) * tiltedDensity β a) := by
      exact (ofReal_integral_eq_lintegral_ofReal hi.integrable_swap
        (Filter.Eventually.of_forall (fun a => mul_nonneg
          (tiltedDensityPower_nonneg β (n+1) _) (tiltedDensity_nonneg β a)))).symm
    _ = _ := by
      rw [tiltedDensityPower_succ β (n+1) (by omega), convolution_eq_swap]
      rfl

theorem pointwiseBridge_tilted_eq_power (β : ℝ) (hβ : -1 < β) (n : ℕ) (hn : 2 ≤ n) (d : ℝ) :
    pointwiseBridge (tiltedDensity β) n d univ =
      ENNReal.ofReal (tiltedDensityPower β (n+1) d) := by
  induction n, hn using Nat.le_induction generalizing d with
  | base =>
    exact pointwiseBridge_next_of_ae β 1 d (pointwiseBridge_tilted_one_ae β hβ)
      (tiltedDensityPower_convolution_exists hβ 2 (by omega) d)
  | succ n hn ih =>
    exact pointwiseBridge_next_of_ae β n d (Filter.Eventually.of_forall ih)
      (tiltedDensityPower_convolution_exists hβ (n+1) (by omega) d)

#print axioms bridgePath_density_product
#print axioms pointwiseBridge_zero
#print axioms pointwiseBridge_succ
#print axioms pointwiseBridge_one_eq_of_integrable
#print axioms pointwiseBridge_tilted_one_ae
#print axioms pointwiseBridge_next_of_ae
#print axioms pointwiseBridge_tilted_eq_power

end ConditionalSpectralExtremes
