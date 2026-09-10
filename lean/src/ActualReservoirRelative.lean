import ActualReservoirMarker
import ActualNormalizationAsymptotic

/-! Real relative reservoir marker error, before specializing the cutoff. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open Reservoir

def reservoirLeading (b N l : ℕ) : ℝ :=
  (reservoirTime b N) ^ l /
    ((N : ℝ) * l.factorial * Real.Gamma ((l : ℝ) / reservoirTime b N))

theorem reservoirLeading_pos {b N l : ℕ} (hN : 0 < N) (hT : 0 < reservoirTime b N) (hl : 0 < l) :
    0 < reservoirLeading b N l := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlp : 0 < (l : ℝ) := by exact_mod_cast hl
  have hG := Real.Gamma_pos_of_pos (div_pos hlp hT)
  unfold reservoirLeading
  positivity

theorem actual_reservoir_marker_relative_error {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ C D E : ℝ, 0 < C ∧ 0 < D ∧ 0 < E ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ b : ℕ, 0 < b → 2 * b ≤ N → 0 < reservoirTime b N →
      ∀ l : ℕ, 1 ≤ l → a ≤ (l : ℝ) / reservoirTime b N → (l : ℝ) / reservoirTime b N ≤ B →
      |reservoirCoefficient N b N l / reservoirLeading b N l - 1| ≤
        C / reservoirTime b N + D * Real.sqrt (reservoirTime b N) * b / N +
          E * N * reservoirOuterError (max 1 B) b N := by
  obtain ⟨C, D, hC, hD, N₀, hN₀, hbound⟩ := actual_reservoir_marker_complex_error ha haB
  obtain ⟨G, hG, hGbound⟩ := gamma_bounded_on_positive_interval ha haB
  refine ⟨C * G, D * G, G, by positivity, by positivity, hG, N₀, hN₀, ?_⟩
  intro N hNN b hb hNb hT l hl hal hlB
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hΓ := Real.Gamma_pos_of_pos (ha.trans_le hal)
  have hΓG := hGbound _ ⟨hal, hlB⟩
  have he := hbound N hNN b hb hNb hT l hl hal hlB
  have heR : |((N : ℝ) * l.factorial / (reservoirTime b N) ^ l) * reservoirCoefficient N b N l -
      (Real.Gamma ((l : ℝ) / reservoirTime b N))⁻¹| ≤
      C / reservoirTime b N + D * Real.sqrt (reservoirTime b N) * b / N +
        (N : ℝ) * reservoirOuterError (max 1 B) b N := by
    simpa only [Complex.Gamma_ofReal, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using! he
  have hf : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
  have heq : reservoirCoefficient N b N l / reservoirLeading b N l - 1 =
      (((N : ℝ) * l.factorial / (reservoirTime b N) ^ l) * reservoirCoefficient N b N l -
        (Real.Gamma ((l : ℝ) / reservoirTime b N))⁻¹) * Real.Gamma ((l : ℝ) / reservoirTime b N) := by
    unfold reservoirLeading
    field_simp
  rw [heq, abs_mul, abs_of_pos hΓ]
  calc
    _ ≤ (C / reservoirTime b N + D * Real.sqrt (reservoirTime b N) * b / N +
        (N : ℝ) * reservoirOuterError (max 1 B) b N) * G :=
      mul_le_mul heR hΓG hΓ.le (by have := reservoirOuterError_nonneg (max 1 B) b N; positivity)
    _ = _ := by ring

#print axioms actual_reservoir_marker_relative_error
end ConditionalSpectralExtremes.ReservoirAnalysis
