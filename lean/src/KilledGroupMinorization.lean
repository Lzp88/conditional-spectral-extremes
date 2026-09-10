import ActualBridge
import KilledGroupDefinitions
import GroupKernelScaling

/-! Actual pointwise killed-kernel estimates. The probability and density
inputs are all supplied by the proved tilted log-sine bridge theorem.
Only deterministic count, drift, and chord inequalities are hypotheses. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem actual_killed_group_kernel (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ W c K δ : ℝ, ∃ N : ℕ, 0 < W ∧ 0 < c ∧ 0 < K ∧ 0 < δ ∧
      ∀ s ∈ Icc a b, ∀ n : ℕ, N ≤ n →
      ∀ (ι : Type) (times : ι → ℕ), (∀ i, times i ≤ n+1) →
      ∀ (barrier : ι → ℝ) (x x' : ℝ),
      |(x'-x)/((n+1 : ℕ) : ℝ)-deriv lambda s| ≤ δ →
      (∀ i, x+(times i : ℝ)/((n+1 : ℕ) : ℝ)*(x'-x) +
        W*Real.sqrt ((n+1 : ℕ) : ℝ) ≤ barrier i) →
      c/Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp (-K*((x'-x)-(n+1 : ℕ)*deriv lambda s)^2/((n+1 : ℕ) : ℝ)) ≤
          killedGroupKernel s n times barrier x x' := by
  obtain ⟨W, c, K, δ, N, hW, hc, hK, hδ, hh⟩ := actual_near_mean_bridge_kernel a b ha hab
  refine ⟨W, c, K, δ, max N 2, hW, hc, hK, hδ, ?_⟩
  intro s hs n hn ι times htimes barrier x x' hmean hgap
  exact (hh s hs n (le_trans (le_max_left _ _) hn) (x'-x) hmean).trans
    (tubeBridge_le_killedGroupKernel s (lt_of_lt_of_le ha hs.1) n
      (le_trans (le_max_right _ _) hn) times htimes barrier x x' _ hgap)

theorem actual_killed_group_minorization (a b α A D : ℝ)
    (ha : -1 < a) (hab : a ≤ b) (hα : 0 < α) (hA : 0 < A) (hD : 0 < D) :
    ∃ W c C δ : ℝ, ∃ N : ℕ, 0 < W ∧ 0 < c ∧ 0 < C ∧ 0 < δ ∧
      ∀ s ∈ Icc a b, ∀ n : ℕ, N ≤ n →
      ∀ (ι : Type) (times : ι → ℕ), (∀ i, times i ≤ n+1) →
      ∀ (barrier : ι → ℝ) (x x' H U : ℝ), 0 < H → 0 ≤ U →
      α*H ≤ (n+1 : ℕ) → ((n+1 : ℕ) : ℝ) ≤ A*H →
      |(x'-x)-(n+1 : ℕ)*deriv lambda s| ≤ D*Real.sqrt H*U →
      D*U ≤ δ*α*Real.sqrt H →
      (∀ i, x+(times i : ℝ)/((n+1 : ℕ) : ℝ)*(x'-x) +
        W*Real.sqrt ((n+1 : ℕ) : ℝ) ≤ barrier i) →
      c/Real.sqrt H * Real.exp (-C*U^2) ≤ killedGroupKernel s n times barrier x x' := by
  obtain ⟨W, c, K, δ, N, hW, hc, hK, hδ, hh⟩ := actual_killed_group_kernel a b ha hab
  refine ⟨W, c/Real.sqrt A, K*D^2/α, δ, N, hW, by positivity, by positivity, hδ, ?_⟩
  intro s hs n hn ι times htimes barrier x x' H U hH hU hcount₁ hcount₂ hdrift hsmall hgap
  have hq : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hmean := group_mean_deviation_small ((n+1 : ℕ) : ℝ) H α D U δ (x'-x)
    (deriv lambda s) hq hH hα hδ.le hcount₁ hdrift hsmall
  exact (group_gaussian_kernel_scaling ((n+1 : ℕ) : ℝ) H α A D U c K (x'-x)
    (deriv lambda s) hq hH hα hA hD.le hU hc.le hK.le hcount₁ hcount₂ hdrift).trans
    (hh s hs n hn ι times htimes barrier x x' hmean hgap)

#print axioms actual_killed_group_kernel
#print axioms actual_killed_group_minorization

end ConditionalSpectralExtremes
