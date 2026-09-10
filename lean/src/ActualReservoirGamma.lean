import ActualReservoirScalar
import ActualCoefficientApproximation

/-! Actual reservoir approximation by the inverse-Gamma marker function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ComplexCoefficientAnalysis

def reservoirTime (b N : ℕ) : ℝ := Real.log N - harmonicNumber b
def reservoirOuterError (M : ℝ) (b N : ℕ) : ℝ :=
  (2 * Real.pi * reservoirOuterConstant M) * (b : ℝ) ^ reservoirOuterPower M *
    Real.exp (-(N : ℝ) / (2 * b))

theorem reservoirOuterError_nonneg (M : ℝ) (b N : ℕ) : 0 ≤ reservoirOuterError M b N := by
  unfold reservoirOuterError
  have hC := reservoirOuterConstant_pos M
  positivity

theorem reservoir_main_function (b N : ℕ) (u : ℂ) :
    Complex.exp (-u * (harmonicNumber b : ℂ)) * approximateMarker N u =
      (N : ℂ)⁻¹ * gammaMarker (reservoirTime b N) u := by
  have he : Complex.exp (-u * (harmonicNumber b : ℂ)) * Complex.exp (((Real.log N : ℝ) : ℂ) * u) =
      Complex.exp (((reservoirTime b N : ℝ) : ℂ) * u) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [reservoirTime, Complex.ofReal_sub]
    ring
  unfold approximateMarker gammaMarker
  calc
    _ = (N : ℂ)⁻¹ * (Complex.exp (-u * (harmonicNumber b : ℂ)) *
        Complex.exp (((Real.log N : ℝ) : ℂ) * u)) * (Complex.Gamma u)⁻¹ := by ring
    _ = _ := by rw [he]; ring

theorem reservoir_error_weight (b N : ℕ) (hN : 0 < N) (a : ℝ) :
    Real.exp (-a * harmonicNumber b) * (N : ℝ) ^ (a - 2) =
      Real.exp (reservoirTime b N * a) / (N : ℝ) ^ 2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [Real.rpow_sub hNp, Real.rpow_two, Real.rpow_def_of_pos hNp, ← mul_div_assoc,
    ← Real.exp_add]
  congr 2
  unfold reservoirTime
  ring

theorem actual_reservoir_gamma_error {M : ℝ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ b : ℕ, 0 < b → 2 * b ≤ N →
      ∀ u : ℂ, ‖u‖ ≤ M →
      ‖reservoirAnalyticCoefficient b N u - (N : ℂ)⁻¹ * gammaMarker (reservoirTime b N) u‖ ≤
        (C * b / (N : ℝ) ^ 2) * Real.exp (reservoirTime b N * u.re) + reservoirOuterError M b N := by
  obtain ⟨Cg, hCg, N₀, hN₀, hg⟩ := uniform_absolute_marker_error hM
  have hCl := reservoirContourLocalConstant_nonneg M (zero_le_one.trans hM)
  refine ⟨reservoirContourLocalConstant M + Cg, by positivity, N₀, hN₀, ?_⟩
  intro N hNN b hb hNb u hu
  have hN1 : 1 ≤ N := hN₀.trans hNN
  have hNp : 0 < N := by omega
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  let Q := Complex.exp (-u * (harmonicNumber b : ℂ))
  let K := Real.exp (-u.re * harmonicNumber b) * (N : ℝ) ^ (u.re - 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : ‖Q‖ = Real.exp (-u.re * harmonicNumber b) := by
    simp [Q, Complex.norm_exp]
  have he := actual_reservoir_scalar_error b N hb hNb u M hu
  have hG := hg N hNN u hu
  rw [← approximateMarker_eq hN1] at hG
  rw [← reservoir_main_function]
  calc
    _ ≤ ‖reservoirAnalyticCoefficient b N u - Q * markerValue N u‖ +
        ‖Q * markerValue N u - Q * approximateMarker N u‖ := by
      simpa only [dist_eq_norm] using dist_triangle (reservoirAnalyticCoefficient b N u)
        (Q * markerValue N u) (Q * approximateMarker N u)
    _ ≤ (reservoirContourLocalConstant M * Real.exp (-u.re * harmonicNumber b) * b *
          (N : ℝ) ^ (u.re - 2) + reservoirOuterError M b N) +
        Real.exp (-u.re * harmonicNumber b) * (Cg * (N : ℝ) ^ (u.re - 2)) := by
      apply add_le_add he
      rw [← mul_sub, norm_mul, hQ]
      exact mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le
    _ = (reservoirContourLocalConstant M * b + Cg) * K + reservoirOuterError M b N := by dsimp [K]; ring
    _ ≤ ((reservoirContourLocalConstant M + Cg) * b) * K + reservoirOuterError M b N := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ hK
      nlinarith
    _ = _ := by
      dsimp [K]
      rw [reservoir_error_weight b N hNp u.re]
      ring

#print axioms actual_reservoir_gamma_error
end ConditionalSpectralExtremes.ReservoirAnalysis
