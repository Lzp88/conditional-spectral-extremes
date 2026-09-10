import TiltedCharacteristicNearZero

/-! Quantitative Gaussian approximation of powers of the actual centered
characteristic function, before passage to the local limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem complex_pow_sub_pow_le_unit {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z^n-w^n‖ ≤ (n : ℝ)*‖z-w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z^(n+1)-w^(n+1) = (z^n-w^n)*z + w^n*(z-w) := by ring
    have hwp : ‖w^n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
    rw [he]
    calc
      ‖(z^n-w^n)*z + w^n*(z-w)‖ ≤ ‖z^n-w^n‖*‖z‖ + ‖w^n‖*‖z-w‖ := by
        simpa only [norm_mul] using norm_add_le ((z^n-w^n)*z) (w^n*(z-w))
      _ ≤ (n : ℝ)*‖z-w‖ + ‖z-w‖ := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right ih (norm_nonneg _)).trans
            (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hz
              (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg (z-w)))))
        · nlinarith [norm_nonneg (z-w)]
      _ = (n+1 : ℕ)*‖z-w‖ := by push_cast; ring

theorem complex_gaussian_linear_error (v t : ℝ) (hv : 0 ≤ v) (hvt : v*t^2/2 ≤ 1) :
    ‖(1 - (v : ℂ)*(t : ℂ)^2/2) - (Real.exp (-v*t^2/2) : ℂ)‖ ≤ v^2*t^4/4 := by
  have ha : |-v*t^2/2| ≤ 1 := by
    rw [abs_of_nonpos (by nlinarith [mul_nonneg hv (sq_nonneg t)])]
    linarith
  have hh := Real.abs_exp_sub_one_sub_id_le ha
  have he : (1 - (v : ℂ)*(t : ℂ)^2/2) - (Real.exp (-v*t^2/2) : ℂ) =
      ((1-v*t^2/2-Real.exp (-v*t^2/2) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  have hneg : 1-v*t^2/2-Real.exp (-v*t^2/2) =
      -(Real.exp (-v*t^2/2)-1-(-v*t^2/2)) := by ring
  rw [hneg, abs_neg]
  convert hh using 1
  ring

theorem complex_pow_gaussian_error {z : ℂ} {v M t : ℝ} (hz : ‖z‖ ≤ 1)
    (hv : 0 ≤ v) (hvt : v*t^2/2 ≤ 1)
    (hrem : ‖z-(1-(v : ℂ)*(t : ℂ)^2/2)‖ ≤ M*|t|^3) (n : ℕ) :
    ‖z^n-(Real.exp (-(n : ℝ)*v*t^2/2) : ℂ)‖ ≤
      (n : ℝ)*(M*|t|^3 + v^2*t^4/4) := by
  have hnorm : ‖(Real.exp (-v*t^2/2) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hv (sq_nonneg t)])
  have hdiff : ‖z-(Real.exp (-v*t^2/2) : ℂ)‖ ≤ M*|t|^3 + v^2*t^4/4 := by
    have he : z-(Real.exp (-v*t^2/2) : ℂ) =
        (z-(1-(v : ℂ)*(t : ℂ)^2/2)) +
          ((1-(v : ℂ)*(t : ℂ)^2/2)-(Real.exp (-v*t^2/2) : ℂ)) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hrem (complex_gaussian_linear_error v t hv hvt))
  have hh := (complex_pow_sub_pow_le_unit hz hnorm n).trans
    (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg n))
  have he : (Real.exp (-v*t^2/2) : ℂ)^n = (Real.exp (-(n : ℝ)*v*t^2/2) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rwa [he] at hh

theorem centeredTiltedLogSineLaw_uniform_power_gaussian_error
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ∈ Icc a b, ∀ t : ℝ, (deriv^[2] lambda) β*t^2/2 ≤ 1 →
      ∀ n : ℕ,
      ‖charFun (centeredTiltedLogSineLaw β) t^n -
        (Real.exp (-(n : ℝ)*(deriv^[2] lambda) β*t^2/2) : ℂ)‖ ≤
        (n : ℝ)*(M*|t|^3 + ((deriv^[2] lambda) β)^2*t^4/4) := by
  obtain ⟨M, hM, hm⟩ := centeredTiltedLogSineLaw_uniform_quadratic_remainder a b ha hab
  refine ⟨M, hM, ?_⟩
  intro β hβ t ht n
  have hb := lt_of_lt_of_le ha hβ.1
  let := centeredTiltedLogSineLaw_probability hb
  exact complex_pow_gaussian_error (norm_charFun_le_one t) (lambda_deriv2_pos hb).le ht (hm β hβ t) n

#print axioms complex_pow_sub_pow_le_unit
#print axioms complex_gaussian_linear_error
#print axioms complex_pow_gaussian_error
#print axioms centeredTiltedLogSineLaw_uniform_power_gaussian_error

end ConditionalSpectralExtremes
