import UniformBridgeFromLocalBounds
import BridgeTiltExistence

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem tubeBridge_change_tilt_real (s β : ℝ) (n : ℕ) (d R : ℝ) :
    (tubeBridge s n d R).toReal =
      Real.exp ((n+1 : ℕ)*(lambda β-lambda s)-(β-s)*d) * (tubeBridge β n d R).toReal := by
  rw [tubeBridge_change_tilt, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

theorem uniform_saddle_bridge_from_local_bounds (a b c₀ C : ℝ) (ha : -1 < a) (hab : a ≤ b)
    (hc₀ : 0 < c₀) (hC : 0 ≤ C) (N : ℕ)
    (hlocal : ∀ β ∈ Icc a b, ∀ q : ℕ, N ≤ q →
      (∀ u : ℝ, tiltedDensityPower β q u ≤ C/Real.sqrt (q : ℝ)) ∧
      c₀/Real.sqrt (q : ℝ) ≤ tiltedDensityPower β q ((q : ℝ)*deriv lambda β)) :
    ∃ W c : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ ∀ β ∈ Icc a b, ∀ s : ℝ,
      ∀ n : ℕ, N₀ ≤ n → ∀ d : ℝ, d = (n+1 : ℕ)*deriv lambda β →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp ((n+1 : ℕ)*(lambda β-lambda s)-(β-s)*d) ≤
        (tubeBridge s n d (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨W, c, N₀, hW, hc, hh⟩ := uniform_bridge_from_local_bounds a b c₀ C ha hab hc₀ hC N hlocal
  refine ⟨W, c, N₀, hW, hc, ?_⟩
  intro β hβ s n hn d hd
  rw [tubeBridge_change_tilt_real s β]
  have hlower := hh β hβ n hn
  rw [← hd] at hlower
  have hm := mul_le_mul_of_nonneg_left hlower
    (Real.exp_nonneg ((n+1 : ℕ)*(lambda β-lambda s)-(β-s)*d))
  simpa only [mul_comm] using hm

theorem uniform_gaussian_saddle_bridge_from_local_bounds (a b c₀ C : ℝ)
    (ha : -1 < a) (hab : a ≤ b) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (N : ℕ)
    (hlocal : ∀ β ∈ Icc a b, ∀ q : ℕ, N ≤ q →
      (∀ u : ℝ, tiltedDensityPower β q u ≤ C/Real.sqrt (q : ℝ)) ∧
      c₀/Real.sqrt (q : ℝ) ≤ tiltedDensityPower β q ((q : ℝ)*deriv lambda β)) :
    ∃ W c K : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ 0 < K ∧
      ∀ s ∈ Icc a b, ∀ β ∈ Icc a b, ∀ n : ℕ, N₀ ≤ n →
      ∀ d : ℝ, d = (n+1 : ℕ)*deriv lambda β →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp (-K*(d-(n+1 : ℕ)*deriv lambda s)^2/((n+1 : ℕ) : ℝ)) ≤
        (tubeBridge s n d (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨W, c, N₀, hW, hc, hh⟩ := uniform_saddle_bridge_from_local_bounds a b c₀ C ha hab hc₀ hC N hlocal
  obtain ⟨K, hK, hk⟩ := bridge_saddle_factor_gaussian_lower a b ha hab
  refine ⟨W, c, K, N₀, hW, hc, hK, ?_⟩
  intro s hs β hβ n hn d hd
  apply le_trans _ (hh β hβ s n hn d hd)
  exact mul_le_mul_of_nonneg_left (hk s hs β hβ (n+1) (by omega) d hd) (by positivity)

theorem uniform_near_mean_bridge_from_local_bounds (a b ε c₀ C : ℝ) (hε : 0 < ε)
    (ha : -1 < a-ε) (hab : a ≤ b) (hc₀ : 0 < c₀) (hC : 0 ≤ C) (N : ℕ)
    (hlocal : ∀ β ∈ Icc (a-ε) (b+ε), ∀ q : ℕ, N ≤ q →
      (∀ u : ℝ, tiltedDensityPower β q u ≤ C/Real.sqrt (q : ℝ)) ∧
      c₀/Real.sqrt (q : ℝ) ≤ tiltedDensityPower β q ((q : ℝ)*deriv lambda β)) :
    ∃ W c K δ : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ 0 < K ∧ 0 < δ ∧
      ∀ s ∈ Icc a b, ∀ n : ℕ, N₀ ≤ n → ∀ d : ℝ,
      |d/((n+1 : ℕ) : ℝ)-deriv lambda s| ≤ δ →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp (-K*(d-(n+1 : ℕ)*deriv lambda s)^2/((n+1 : ℕ) : ℝ)) ≤
        (tubeBridge s n d (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨δ, L, hδ, hL, hinv⟩ := lambda_mean_inverse_uniform a b ε hε ha hab
  obtain ⟨W, c, K, N₀, hW, hc, hK, hh⟩ := uniform_gaussian_saddle_bridge_from_local_bounds
    (a-ε) (b+ε) c₀ C ha (by linarith) hc₀ hC N hlocal
  refine ⟨W, c, K, δ, N₀, hW, hc, hK, hδ, ?_⟩
  intro s hs n hn d hd
  obtain ⟨β, hβ, he, hsep⟩ := hinv s hs (d/((n+1 : ℕ) : ℝ)) hd
  have hq0 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd' : d = (n+1 : ℕ)*deriv lambda β := by
    rw [he]
    field_simp
  exact hh s ⟨by linarith [hs.1], by linarith [hs.2]⟩ β hβ n hn d hd'

#print axioms tubeBridge_change_tilt_real
#print axioms uniform_saddle_bridge_from_local_bounds
#print axioms uniform_gaussian_saddle_bridge_from_local_bounds
#print axioms uniform_near_mean_bridge_from_local_bounds

end ConditionalSpectralExtremes
