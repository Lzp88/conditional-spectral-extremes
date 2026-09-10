import ActualReservoirRelative
import ReservoirOuterUniform

/-! Equation (reservoir-marker) at the actual floor cutoff, with the outer
contour term absorbed by a proved uniform bound. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ReservoirScale Reservoir

theorem actual_reservoir_marker_at_cutoff {a B C₀ : ℝ}
    (ha : 0 < a) (haB : a ≤ B) (hC₀ : 0 ≤ C₀) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ C₀ * L n * cutoff n →
        ∀ l : ℕ, a ≤ (l : ℝ) / reservoirTime (cutoff n) (n - d) →
          (l : ℝ) / reservoirTime (cutoff n) (n - d) ≤ B →
        |reservoirCoefficient (n - d) (cutoff n) (n - d) l /
            reservoirLeading (cutoff n) (n - d) l - 1| ≤
          C / reservoirTime (cutoff n) (n - d) +
            D * Real.sqrt (reservoirTime (cutoff n) (n - d)) * cutoff n / (n - d : ℕ) := by
  obtain ⟨C, D, E, hC, hD, hE, N₀, hN₀, he⟩ := actual_reservoir_marker_relative_error ha haB
  let K := 2 * Real.pi * reservoirOuterConstant (max 1 B)
  have hK : 0 < K := by
    have := reservoirOuterConstant_pos (max 1 B)
    dsimp [K]
    positivity
  refine ⟨C + E * K, D, by positivity, hD, ?_⟩
  filter_upwards [eventually_reservoir_shift_scales hC₀, eventually_shift_ge hC₀ N₀,
    eventually_outer_error_over_time (by positivity : 0 ≤ max (1 : ℝ) B) hC₀]
      with n hs hN ho d hd l hal hlB
  obtain ⟨hb, hNb, hT, _, _, _, _⟩ := hs d hd
  have hl : 1 ≤ l := by
    have hlp : 0 < (l : ℝ) := (div_pos_iff_of_pos_right hT).mp (ha.trans_le hal)
    have : 0 < l := by exact_mod_cast hlp
    omega
  have hh := he (n - d) (hN d hd) (cutoff n) hb hNb hT l hl hal hlB
  have hoo := mul_le_mul_of_nonneg_left (ho d hd) hE.le
  calc
    _ ≤ C / reservoirTime (cutoff n) (n - d) +
        D * Real.sqrt (reservoirTime (cutoff n) (n - d)) * cutoff n / (n - d : ℕ) +
        E * (n - d : ℕ) * reservoirOuterError (max 1 B) (cutoff n) (n - d) := hh
    _ ≤ C / reservoirTime (cutoff n) (n - d) +
        D * Real.sqrt (reservoirTime (cutoff n) (n - d)) * cutoff n / (n - d : ℕ) +
        E * (K / reservoirTime (cutoff n) (n - d)) := by dsimp [K] at *; nlinarith
    _ = _ := by ring

#print axioms actual_reservoir_marker_at_cutoff
end ConditionalSpectralExtremes.ReservoirAnalysis
