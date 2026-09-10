import ActualCoefficientApproximation
import EntireMarkerSaddle
import SaddleRescaling

/-! Uniform marker asymptotic for the actual fixed-cycle normalization coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes.ComplexCoefficientAnalysis
open ReservoirAnalysis

theorem actual_marker_normalized_error {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N, ∀ k : ℕ, 1 ≤ k →
      a ≤ (k : ℝ) / Real.log n → (k : ℝ) / Real.log n ≤ B →
      ‖((n : ℂ) * k.factorial / ((Real.log n : ℝ) : ℂ) ^ k) * (coefficient n k : ℂ) -
        (Complex.Gamma (((k : ℝ) / Real.log n : ℝ) : ℂ))⁻¹‖ ≤ C / Real.log n := by
  have hg : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma
  obtain ⟨Cg, hCg, hgBound⟩ := entire_marker_saddle hg ha haB
  obtain ⟨Ce, hCe, N, hN, heBound⟩ := actual_coefficient_cauchy_error (R := max 1 B) (le_max_left _ _)
  have hB : 0 < B := ha.trans_le haB
  refine ⟨Cg + 8 * Ce * Real.exp 1 * B, by positivity, max N 2, le_max_right _ _, ?_⟩
  intro n hn k hk hak hkB
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log n := Real.log_pos hnreal
  have hnp : 0 < (n : ℝ) := zero_lt_one.trans hnreal
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hnp.ne'
  have hLc : ((Real.log n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have hr : 0 < (k : ℝ) / Real.log n := div_pos hkp hL
  let A := analyticCoefficient (gammaMarker (Real.log n)) k
  let Q : ℂ := (n : ℂ) * k.factorial / ((Real.log n : ℝ) : ℂ) ^ k
  have hQ : ‖Q‖ = (n : ℝ) * k.factorial / (Real.log n) ^ k := by
    have he : Q = (((n : ℝ) * k.factorial / (Real.log n) ^ k : ℝ) : ℂ) := by
      simp only [Q, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have herror := heBound n hnN _ hr (hkB.trans (le_max_right 1 B)) k
  have hscale : ‖Q * (coefficient n k : ℂ) -
      ((k.factorial : ℂ) / ((Real.log n : ℝ) : ℂ) ^ k) * A‖ ≤
      (8 * Ce * Real.exp 1 * B) / Real.log n := by
    have he : Q * (coefficient n k : ℂ) -
        ((k.factorial : ℂ) / ((Real.log n : ℝ) : ℂ) ^ k) * A =
        Q * ((coefficient n k : ℂ) - (n : ℂ)⁻¹ * A) := by
      dsimp [Q]
      field_simp
    rw [he, norm_mul, hQ]
    calc
      _ ≤ ((n : ℝ) * k.factorial / (Real.log n) ^ k) *
          (Ce * (n : ℝ) ^ ((k : ℝ) / Real.log n - 2) * ((k : ℝ) / Real.log n)⁻¹ ^ k) :=
        mul_le_mul_of_nonneg_left herror (by positivity)
      _ = (Ce / n) * ((k.factorial : ℝ) * Real.exp k / (k : ℝ) ^ k) :=
        saddle_cauchy_rescaling hnreal hk Ce
      _ ≤ _ := saddle_cauchy_error_log_bound hnreal hCe.le hk hkB
  have hs : ‖((k.factorial : ℂ) / ((Real.log n : ℝ) : ℂ) ^ k) * A -
      (Complex.Gamma (((k : ℝ) / Real.log n : ℝ) : ℂ))⁻¹‖ ≤ Cg / Real.log n :=
    hgBound (Real.log n) k hL hk hak hkB
  calc
    _ ≤ ‖Q * (coefficient n k : ℂ) -
        ((k.factorial : ℂ) / ((Real.log n : ℝ) : ℂ) ^ k) * A‖ +
      ‖((k.factorial : ℂ) / ((Real.log n : ℝ) : ℂ) ^ k) * A -
        (Complex.Gamma (((k : ℝ) / Real.log n : ℝ) : ℂ))⁻¹‖ := by
      simpa only [dist_eq_norm] using dist_triangle (Q * (coefficient n k : ℂ))
        (((k.factorial : ℂ) / ((Real.log n : ℝ) : ℂ) ^ k) * A)
        ((Complex.Gamma (((k : ℝ) / Real.log n : ℝ) : ℂ))⁻¹)
    _ ≤ (8 * Ce * Real.exp 1 * B) / Real.log n + Cg / Real.log n := add_le_add hscale hs
    _ = (Cg + 8 * Ce * Real.exp 1 * B) / Real.log n := by ring

#print axioms actual_marker_normalized_error
end ConditionalSpectralExtremes.ComplexCoefficientAnalysis
