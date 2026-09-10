import TiltedDensityLp
import TiltedLogSineDensity
import ConjugateConvolution

/-! The special Young inequality and translation argument needed for a continuous
threefold convolution density. The explicit density Lp bound is proved elsewhere. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Convolution Topology

namespace ConditionalSpectralExtremes

theorem ennreal_mul_thirds (a b : ℝ≥0∞) :
    (a ^ (3 / 2 : ℝ) * b ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
      (a ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
      (b ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) = a * b := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp only [← ENNReal.rpow_mul]
  norm_num
  calc
    a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) =
      (a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ)) *
        (b ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) := by ring
    _ = a * b := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

theorem lintegral_mul_cube_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) ^ (3 : ℝ) ≤
      (∫⁻ x, f x ^ (3 / 2 : ℝ) * g x ^ (3 / 2 : ℝ) ∂μ) *
        (∫⁻ x, f x ^ (3 / 2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (3 / 2 : ℝ) ∂μ) := by
  let fs : Fin 3 → α → ℝ≥0∞ :=
    ![fun x => f x ^ (3 / 2 : ℝ) * g x ^ (3 / 2 : ℝ),
      fun x => f x ^ (3 / 2 : ℝ), fun x => g x ^ (3 / 2 : ℝ)]
  have hfs : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (fs i) μ := by
    intro i _
    fin_cases i
    · exact (hf.pow_const _).mul (hg.pow_const _)
    · exact hf.pow_const _
    · exact hg.pow_const _
  have h := ENNReal.lintegral_prod_norm_pow_le Finset.univ hfs
    (p := fun _ => (1 / 3 : ℝ)) (by norm_num) (by intro i hi; norm_num)
  simp only [Fin.prod_univ_succ, fs, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one] at h
  have hid (x : α) :
      (f x ^ (3 / 2 : ℝ) * g x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
        ((f x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) * (g x ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ)) =
          f x * g x := by simpa only [mul_assoc] using ennreal_mul_thirds (f x) (g x)
  simp_rw [hid] at h
  have hc := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3),
    ← ENNReal.rpow_mul] at hc
  norm_num at hc
  simpa only [mul_assoc, ENNReal.rpow_ofNat] using hc

theorem lintegral_convolution_product {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, f y * g (x - y)) = (∫⁻ y, f y) * ∫⁻ y, g y := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  have hi (y : ℝ) : (∫⁻ x, f y * g (x - y)) = f y * ∫⁻ x, g x := by
    rw [lintegral_const_mul (f y) (show Measurable (fun x : ℝ => g (x - y)) by fun_prop),
      lintegral_sub_right_eq_self]
  simp_rw [hi]
  exact lintegral_mul_const'' _ hf.aemeasurable

theorem convolution_memLp_three {f g : ℝ → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) (hf1 : Integrable f) (hg1 : Integrable g)
    (hf : MemLp f (3 / 2) volume) (hg : MemLp g (3 / 2) volume) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) 3 volume := by
  let F : ℝ → ℝ≥0∞ := fun y => ‖f y‖ₑ ^ (3 / 2 : ℝ)
  let G : ℝ → ℝ≥0∞ := fun y => ‖g y‖ₑ ^ (3 / 2 : ℝ)
  have hFm : Measurable F := hfm.enorm.pow_const _
  have hGm : Measurable G := hgm.enorm.pow_const _
  have hF : (∫⁻ y, F y) < ∞ := by
    simpa only [F, ENNReal.toReal_div, ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
        (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞) hf.2)
  have hG : (∫⁻ y, G y) < ∞ := by
    simpa only [G, ENNReal.toReal_div, ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
        (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ∞) hg.2)
  have hp (x : ℝ) : ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x‖ₑ ^ (3 : ℝ) ≤
      (∫⁻ y, F y * G (x - y)) * (∫⁻ y, F y) * ∫⁻ y, G y := by
    have h0 := ENNReal.rpow_le_rpow
      (enorm_integral_le_lintegral_enorm (μ := volume) (fun y => f y * g (x - y)))
      (by norm_num : (0 : ℝ) ≤ 3)
    simp only [enorm_mul] at h0
    have h1 := lintegral_mul_cube_bound (μ := volume)
      (f := fun y => ‖f y‖ₑ) (g := fun y => ‖g (x - y)‖ₑ)
      hfm.enorm.aemeasurable (by fun_prop)
    rw [lintegral_sub_left_eq_self (fun y => ‖g y‖ₑ ^ (3 / 2 : ℝ)) x] at h1
    exact h0.trans h1
  refine ⟨(hf1.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg1).1, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  apply lt_of_le_of_lt (lintegral_mono hp)
  rw [lintegral_mul_const' _ _ hG.ne, lintegral_mul_const' _ _ hF.ne,
    lintegral_convolution_product hFm hGm]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hF hG) hF) hG

#print axioms ennreal_mul_thirds
#print axioms lintegral_mul_cube_bound
#print axioms lintegral_convolution_product
#print axioms convolution_memLp_three

theorem holderConjugate_three_three_halves :
    ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := by
  apply ENNReal.holderConjugate_iff.mpr
  apply (ENNReal.toReal_eq_toReal_iff' (by
    simp only [ENNReal.add_ne_top, ENNReal.inv_ne_top]
    norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]

def tiltedDensityDouble (β : ℝ) : ℝ → ℝ :=
  tiltedDensity β ⋆[ContinuousLinearMap.mul ℝ ℝ] tiltedDensity β

def tiltedDensityTriple (β : ℝ) : ℝ → ℝ :=
  tiltedDensityDouble β ⋆[ContinuousLinearMap.mul ℝ ℝ] tiltedDensity β

theorem tiltedDensityDouble_memLp {β : ℝ} (hβ : -1 < β) :
    MemLp (tiltedDensityDouble β) 3 volume :=
  convolution_memLp_three (tiltedDensity_measurable β) (tiltedDensity_measurable β)
    (tiltedDensity_integrable β hβ) (tiltedDensity_integrable β hβ)
    (tiltedDensity_memLp_three_halves hβ) (tiltedDensity_memLp_three_halves hβ)

theorem tiltedDensityTriple_continuous {β : ℝ} (hβ : -1 < β) :
    Continuous (tiltedDensityTriple β) := by
  let : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := holderConjugate_three_three_halves
  let : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) :=
    ⟨ENNReal.HolderConjugate.one_le (3 / 2) 3⟩
  exact convolution_continuous_of_memLp (by finiteness)
    (tiltedDensityDouble_memLp hβ) (tiltedDensity_memLp_three_halves hβ)

theorem tiltedDensityTriple_exists {β : ℝ} (hβ : -1 < β) :
    ConvolutionExists (tiltedDensityDouble β) (tiltedDensity β)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  let : ENNReal.HolderConjugate (3 : ℝ≥0∞) (3 / 2) := holderConjugate_three_three_halves
  exact convolution_exists_of_memLp
    (tiltedDensityDouble_memLp hβ) (tiltedDensity_memLp_three_halves hβ)

theorem tiltedDensityDouble_integrable {β : ℝ} (hβ : -1 < β) :
    Integrable (tiltedDensityDouble β) :=
  (tiltedDensity_integrable β hβ).integrable_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) (tiltedDensity_integrable β hβ)

theorem tiltedDensityTriple_integrable {β : ℝ} (hβ : -1 < β) :
    Integrable (tiltedDensityTriple β) :=
  (tiltedDensityDouble_integrable hβ).integrable_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) (tiltedDensity_integrable β hβ)

theorem tiltedDensityDouble_nonneg (β x : ℝ) : 0 ≤ tiltedDensityDouble β x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (tiltedDensity_nonneg β y) (tiltedDensity_nonneg β (x - y))

theorem tiltedDensityTriple_nonneg (β x : ℝ) : 0 ≤ tiltedDensityTriple β x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (tiltedDensityDouble_nonneg β y) (tiltedDensity_nonneg β (x - y))

theorem tiltedDensityDouble_integral {β : ℝ} (hβ : -1 < β) :
    ∫ x, tiltedDensityDouble β x = 1 := by
  rw [tiltedDensityDouble, integral_convolution _
    (tiltedDensity_integrable β hβ) (tiltedDensity_integrable β hβ)]
  simp [tiltedDensity_integral β hβ]

theorem tiltedDensityTriple_integral {β : ℝ} (hβ : -1 < β) :
    ∫ x, tiltedDensityTriple β x = 1 := by
  rw [tiltedDensityTriple, integral_convolution _
    (tiltedDensityDouble_integrable hβ) (tiltedDensity_integrable β hβ)]
  simp [tiltedDensityDouble_integral hβ, tiltedDensity_integral β hβ]

#print axioms holderConjugate_three_three_halves
#print axioms tiltedDensityDouble_memLp
#print axioms tiltedDensityTriple_continuous
#print axioms tiltedDensityTriple_exists
#print axioms tiltedDensityDouble_integrable
#print axioms tiltedDensityTriple_integrable
#print axioms tiltedDensityDouble_nonneg
#print axioms tiltedDensityTriple_nonneg
#print axioms tiltedDensityDouble_integral
#print axioms tiltedDensityTriple_integral

end ConditionalSpectralExtremes
