import TiltedLocalBounds
import BridgeTiltedLowerFromLocalBounds
import CenteredBridge

/-! The manuscript's pointwise bridge lemma on the actual tilted log-sine
law. All unrestricted density estimates are instantiated by the proved
uniform local central limit theorem; no local-bound assumption remains.
The path has q=n+1 increments and its bridge integral has exactly n free
Lebesgue coordinates. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem actual_bridge_kernel (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ W c : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ ∀ β ∈ Icc a b, ∀ n : ℕ, N₀ ≤ n →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) ≤
        (tubeBridge β n ((n+1 : ℕ)*deriv lambda β)
          (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨c₀, C, hc₀, hC, N, hN, hlocal⟩ := tiltedDensityPower_uniform_local_bounds a b ha hab
  exact uniform_bridge_from_local_bounds a b c₀ C ha hab hc₀ hC.le N hlocal

theorem actual_centered_bridge_kernel (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ W c : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ ∀ β ∈ Icc a b, ∀ n : ℕ, N₀ ≤ n →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) ≤
        (centeredTubeBridge β n (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨W, c, N₀, hW, hc, hh⟩ := actual_bridge_kernel a b ha hab
  refine ⟨W, c, N₀, hW, hc, ?_⟩
  intro β hβ n hn
  rw [centeredTubeBridge_eq_tubeBridge]
  exact hh β hβ n hn

theorem actual_bridge_saddle (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ W c : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ ∀ β ∈ Icc a b, ∀ s ∈ Icc a b,
      ∀ n : ℕ, N₀ ≤ n → ∀ d : ℝ, d = (n+1 : ℕ)*deriv lambda β →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp ((n+1 : ℕ)*(lambda β-lambda s)-(β-s)*d) ≤
        (tubeBridge s n d (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  obtain ⟨c₀, C, hc₀, hC, N, hN, hlocal⟩ := tiltedDensityPower_uniform_local_bounds a b ha hab
  obtain ⟨W, c, N₀, hW, hc, hh⟩ := uniform_saddle_bridge_from_local_bounds a b c₀ C ha hab hc₀ hC.le N hlocal
  exact ⟨W, c, N₀, hW, hc, fun β hβ s _ n hn d hd => hh β hβ s n hn d hd⟩

theorem actual_near_mean_bridge_kernel (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ W c K δ : ℝ, ∃ N₀ : ℕ, 0 < W ∧ 0 < c ∧ 0 < K ∧ 0 < δ ∧
      ∀ s ∈ Icc a b, ∀ n : ℕ, N₀ ≤ n → ∀ d : ℝ,
      |d/((n+1 : ℕ) : ℝ)-deriv lambda s| ≤ δ →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp (-K*(d-(n+1 : ℕ)*deriv lambda s)^2/((n+1 : ℕ) : ℝ)) ≤
        (tubeBridge s n d (W*Real.sqrt ((n+1 : ℕ) : ℝ))).toReal := by
  let ε := (a+1)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha' : -1 < a-ε := by dsimp [ε]; linarith
  have hab' : a-ε ≤ b+ε := by linarith
  obtain ⟨c₀, C, hc₀, hC, N, hN, hlocal⟩ := tiltedDensityPower_uniform_local_bounds (a-ε) (b+ε) ha' hab'
  exact uniform_near_mean_bridge_from_local_bounds a b ε c₀ C hε ha' hab hc₀ hC.le N hlocal

#print axioms actual_bridge_kernel
#print axioms actual_centered_bridge_kernel
#print axioms actual_bridge_saddle
#print axioms actual_near_mean_bridge_kernel

end ConditionalSpectralExtremes
