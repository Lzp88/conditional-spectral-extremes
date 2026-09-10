import Mathlib

/-! The paper's actual ten-fold uniform smoothing noise and its Fourier decay. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Real Complex

namespace ConditionalSpectralAudit.FourierHarmonic

def symmetricUniform (h : Real) : Measure Real :=
  ENNReal.ofReal ((2 * h)⁻¹) • volume.restrict (Ioc (-h) h)

theorem symmetricUniform_probability (h : Real) (hh : 0 < h) :
    IsProbabilityMeasure (symmetricUniform h) := by
  constructor
  simp only [symmetricUniform, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioc, smul_eq_mul, sub_neg_eq_add, ← two_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem symmetricUniform_charFun (h u : Real) (hh : 0 < h) (hu : u ≠ 0) :
    charFun (symmetricUniform h) u = ((2 * h : Real) : Complex)⁻¹ *
      (Complex.exp (((u * h : Real) : Complex) * Complex.I) -
        Complex.exp (((u * (-h) : Real) : Complex) * Complex.I)) / ((u : Complex) * Complex.I) := by
  rw [charFun_apply_real, symmetricUniform, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), ← intervalIntegral.integral_of_le (by linarith : -h ≤ h)]
  have he : (fun x : Real => Complex.exp ((u : Complex) * x * Complex.I)) =
      (fun x : Real => Complex.exp (((u : Complex) * Complex.I) * x)) := by
    funext x
    congr 1
    ring
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [he, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hu) Complex.I_ne_zero)]
  push_cast
  simp only [mul_assoc, mul_left_comm, mul_comm, mul_div_assoc]
  ring

theorem symmetricUniform_charFun_decay (h u : Real) (hh : 0 < h) (hu : u ≠ 0) :
    ‖charFun (symmetricUniform h) u‖ ≤ (h * |u|)⁻¹ := by
  rw [symmetricUniform_charFun h u hh hu, norm_div, norm_mul]
  have h1 : ‖Complex.exp (((u * h : Real) : Complex) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  have h2 : ‖Complex.exp (((u * (-h) : Real) : Complex) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  have hd := norm_sub_le (Complex.exp (((u * h : Real) : Complex) * Complex.I))
    (Complex.exp (((u * (-h) : Real) : Complex) * Complex.I))
  rw [h1, h2] at hd
  simp only [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_of_pos (by norm_num : (0 : Real) < 2), abs_of_pos hh]
  calc
    _ ≤ (2 * h)⁻¹ * (1 + 1) / |u| := by gcongr
    _ = _ := by field_simp; ring

def tenUniformNoise (δ : Real) : Measure Real :=
  (Measure.pi (fun _ : Fin 10 => symmetricUniform (δ / 10))).map (fun x => ∑ i, x i)

theorem tenUniformNoise_probability (δ : Real) (hδ : 0 < δ) :
    IsProbabilityMeasure (tenUniformNoise δ) := by
  let _ := symmetricUniform_probability (δ / 10) (by positivity)
  unfold tenUniformNoise
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem tenUniformNoise_charFun (δ u : Real) (hδ : 0 < δ) :
    charFun (tenUniformNoise δ) u = charFun (symmetricUniform (δ / 10)) u ^ 10 := by
  let _ := symmetricUniform_probability (δ / 10) (by positivity)
  have hh := congrFun (charFun_map_sum_pi_eq_prod (fun _ : Fin 10 => symmetricUniform (δ / 10))) u
  simpa [tenUniformNoise] using hh

theorem tenUniformNoise_charFun_decay (δ u : Real) (hδ : 0 < δ) (hu : u ≠ 0) :
    ‖charFun (tenUniformNoise δ) u‖ ≤ min 1 (((δ / 10) * |u|)⁻¹ ^ 10) := by
  let _ := tenUniformNoise_probability δ hδ
  apply le_min (norm_charFun_le_one u)
  rw [tenUniformNoise_charFun δ u hδ, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (symmetricUniform_charFun_decay (δ / 10) u (by positivity) hu) 10

#print axioms symmetricUniform_charFun_decay
#print axioms tenUniformNoise_charFun_decay
end ConditionalSpectralAudit.FourierHarmonic
