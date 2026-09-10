import MarkerStepBounds
import ProductConvergenceRate

/-! The actual uniform complex Gamma-ratio error, including all Gamma poles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ConditionalSpectralExtremes.ComplexCoefficientAnalysis

theorem normalizedMarker_error_bound {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R)
    {n : ℕ} (hn : 1 ≤ n) (hnR : 2 * (R + 1) ≤ n)
    (hnC : 16 * (R ^ 2 + R) ≤ n) :
    ‖normalizedMarker n z - (Complex.Gamma z)⁻¹‖ ≤
      (16 * (R ^ 2 + R) / n) * ‖(Complex.Gamma z)⁻¹‖ := by
  rw [show 16 * (R ^ 2 + R) = 8 * (2 * (R ^ 2 + R)) by ring]
  apply product_limit_rate (a := fun j => normalizedMarker j z)
    (r := fun j => Complex.exp (markerStepLog z j))
    (C := 2 * (R ^ 2 + R)) (by positivity) hn (by nlinarith) ?_ ?_
    (normalizedMarker_tendsto z)
  · intro j hj
    have hjp : 0 < j := lt_of_lt_of_le (by omega : 0 < n) hj
    have hjr : 2 * (R + 1) ≤ (j : ℝ) := le_trans hnR (by exact_mod_cast hj)
    have hjpR : 0 < (j : ℝ) := by exact_mod_cast hjp
    apply normalizedMarker_step (Nat.ne_of_gt hjp)
    have hnorm : ‖z / (j : ℂ)‖ ≤ (1 / 2 : ℝ) := by
      simp only [norm_div, Complex.norm_natCast]
      apply (div_le_iff₀ hjpR).2
      linarith
    intro he
    have hv : z / (j : ℂ) = -1 := eq_neg_of_add_eq_zero_right he
    rw [hv, norm_neg, norm_one] at hnorm
    norm_num at hnorm
  · intro j hj
    exact markerStepExp_bound hR hz (le_trans hnR (by exact_mod_cast hj))

theorem uniform_normalized_marker_error {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(n : ℂ) ^ (1 - z) * markerValue n z - (Complex.Gamma z)⁻¹‖ ≤ C / n := by
  have hcont : Continuous (fun z : ℂ => (Complex.Gamma z)⁻¹) := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcont.continuousOn
  have hM0 : 0 ≤ M := by
    have hh := hM 0 (by simpa using (show (0 : ℝ) ≤ R by linarith))
    simpa using hh
  let C := 16 * (R ^ 2 + R) * (M + 1)
  let N := Nat.ceil (max (2 * (R + 1)) (16 * (R ^ 2 + R))) + 1
  have hCp : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCp, N, by dsimp [N]; omega, ?_⟩
  intro n hn z hz
  have hn1 : 1 ≤ n := by dsimp [N] at hn; omega
  have hbound : max (2 * (R + 1)) (16 * (R ^ 2 + R)) ≤ (n : ℝ) := by
    have hh := Nat.le_ceil (max (2 * (R + 1)) (16 * (R ^ 2 + R)))
    have hcast : (Nat.ceil (max (2 * (R + 1)) (16 * (R ^ 2 + R))) : ℝ) ≤ n := by
      exact_mod_cast (show Nat.ceil (max (2 * (R + 1)) (16 * (R ^ 2 + R))) ≤ n by
        dsimp [N] at hn; omega)
    exact hh.trans hcast
  have he := normalizedMarker_error_bound hR hz hn1
    ((le_max_left _ _).trans hbound) ((le_max_right _ _).trans hbound)
  rw [normalizedMarker_eq (Nat.ne_of_gt (by omega)) z] at he
  have hzM : ‖(Complex.Gamma z)⁻¹‖ ≤ M + 1 :=
    (hM z (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)).trans (by linarith)
  calc
    ‖(n : ℂ) ^ (1 - z) * markerValue n z - (Complex.Gamma z)⁻¹‖ ≤
      (16 * (R ^ 2 + R) / n) * ‖(Complex.Gamma z)⁻¹‖ := he
    _ ≤ (16 * (R ^ 2 + R) / n) * (M + 1) := by gcongr
    _ = C / n := by dsimp [C]; ring

#print axioms normalizedMarker_error_bound
#print axioms uniform_normalized_marker_error
end ConditionalSpectralExtremes.ComplexCoefficientAnalysis
