import Mathlib

/-! Exact affine change of variables in the Fourier inverse, with its scale
factor and phase kept explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped FourierTransform

namespace ConditionalSpectralExtremes

theorem fourierInv_real_integral (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ f x = ∫ ξ, Complex.exp (((2*Real.pi*ξ*x : ℝ) : ℂ)*Complex.I)*f ξ := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem fourierInv_affine (f : ℝ → ℂ) (m s x : ℝ) (hs : 0 < s) :
    𝓕⁻ (fun ξ => Complex.exp (((2*Real.pi*m*ξ/s : ℝ) : ℂ)*Complex.I)*f (ξ/s)) x =
      (s : ℂ)*𝓕⁻ f (m+s*x) := by
  rw [fourierInv_real_integral, fourierInv_real_integral]
  let F : ℝ → ℂ := fun ξ => Complex.exp (((2*Real.pi*ξ*(m+s*x) : ℝ) : ℂ)*Complex.I)*f ξ
  have he (ξ : ℝ) :
      Complex.exp (((2*Real.pi*ξ*x : ℝ) : ℂ)*Complex.I)*
        (Complex.exp (((2*Real.pi*m*ξ/s : ℝ) : ℂ)*Complex.I)*f (ξ/s)) = F (ξ/s) := by
    rw [← mul_assoc, ← Complex.exp_add]
    dsimp only [F]
    congr 2
    push_cast
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp [hsc]
    ring
  simp_rw [he]
  rw [Measure.integral_comp_div F s, abs_of_pos hs, Complex.real_smul]

theorem fourierInv_difference_bound {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    ‖𝓕⁻ f x-𝓕⁻ g x‖ ≤ ∫ ξ, ‖f ξ-g ξ‖ := by
  rw [fourierInv_real_integral, fourierInv_real_integral, ← integral_sub]
  · apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp only
    rw [← mul_sub, norm_mul]
    simp [Complex.norm_exp]
  · exact (hf.bdd_mul (by fun_prop) (c := 1)
      (Filter.Eventually.of_forall (fun ξ => by simp [Complex.norm_exp])))
  · exact (hg.bdd_mul (by fun_prop) (c := 1)
      (Filter.Eventually.of_forall (fun ξ => by simp [Complex.norm_exp])))

#print axioms fourierInv_real_integral
#print axioms fourierInv_affine
#print axioms fourierInv_difference_bound

end ConditionalSpectralExtremes
