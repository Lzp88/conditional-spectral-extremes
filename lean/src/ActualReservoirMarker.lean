import ActualReservoirGamma
import ReservoirMarkerAnalytic
import GammaMarkerPerturbation

/-! Actual reservoir marker extraction, retaining the explicit outer-contour remainder. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open Reservoir

theorem sqrt_count_le_saddle_scale {x B : ℝ} (hx : 0 < x) (hB : 0 ≤ B)
    {l : ℕ} (hl : (l : ℝ) / x ≤ B) :
    Real.sqrt (2 * (l : ℝ)) ≤ Real.sqrt (2 * B) * Real.sqrt x := by
  calc
    _ ≤ Real.sqrt ((2 * B) * x) := Real.sqrt_le_sqrt (by have := (div_le_iff₀ hx).1 hl; linarith)
    _ = _ := Real.sqrt_mul (by positivity) _

theorem actual_reservoir_marker_complex_error {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ b : ℕ,
      0 < b → 2 * b ≤ N → 0 < reservoirTime b N → ∀ l : ℕ, 1 ≤ l →
      a ≤ (l : ℝ) / reservoirTime b N → (l : ℝ) / reservoirTime b N ≤ B →
      ‖((((N : ℝ) * l.factorial / (reservoirTime b N) ^ l : ℝ) : ℂ)) *
          (reservoirCoefficient N b N l : ℂ) -
        (Complex.Gamma (((l : ℝ) / reservoirTime b N : ℝ) : ℂ))⁻¹‖ ≤
        C / reservoirTime b N + D * Real.sqrt (reservoirTime b N) * b / N +
          (N : ℝ) * reservoirOuterError (max 1 B) b N := by
  have hB : 0 < B := ha.trans_le haB
  obtain ⟨Cp, hCp, N₀, hN₀, hpoint⟩ := actual_reservoir_gamma_error (M := max 1 B) (le_max_left _ _)
  obtain ⟨Cg, hCg, hsaddle⟩ := gamma_marker_saddle_with_circle_error ha haB
  refine ⟨Cg + 1, Cp * Real.exp 1 * Real.sqrt (2 * B), by positivity, by positivity,
    N₀, hN₀, ?_⟩
  intro N hNN b hb hNb hT l hl hal hlB
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbN : b ≤ N := by omega
  have he := hsaddle (reservoirTime b N) l hT hl hal hlB (N : ℝ)
    (Cp * b / (N : ℝ) ^ 2) (reservoirOuterError (max 1 B) b N) hNp (by positivity)
    (reservoirOuterError_nonneg _ _ _) (reservoirAnalyticCoefficient b N)
    (reservoirAnalyticCoefficient_differentiable hbN)
    (fun z hz => hpoint N hNN b hb hNb z (hz.le.trans (hlB.trans (le_max_right _ _))))
  rw [reservoir_marker_coefficient hbN] at he
  apply he.trans
  apply add_le_add _ le_rfl
  apply add_le_add
  · exact div_le_div_of_nonneg_right (by linarith : Cg ≤ Cg + 1) hT.le
  · calc
      _ ≤ (N : ℝ) * (Cp * b / (N : ℝ) ^ 2) * Real.exp 1 *
          (Real.sqrt (2 * B) * Real.sqrt (reservoirTime b N)) :=
        mul_le_mul_of_nonneg_left (sqrt_count_le_saddle_scale hT hB.le hlB) (by positivity)
      _ = _ := by field_simp

#print axioms actual_reservoir_marker_complex_error
end ConditionalSpectralExtremes.ReservoirAnalysis
