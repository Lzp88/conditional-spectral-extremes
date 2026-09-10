import BoxChainSubprobability
import KilledEndpointLaw

/-! Initial-height measurability and the actual fresh-increment
interpretation of a killed transition against any measurable test. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes

theorem boxChainIntegral_measurable_initial (n : ℕ) (K : Fin n → ℝ → ℝ → ℝ≥0∞)
    (hK : ∀ i, Measurable (fun p : ℝ × ℝ => K i p.1 p.2))
    (lo hi : Fin n → ℝ) : Measurable (boxChainIntegral n K lo hi) := by
  have hm : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (Icc lo hi).indicator
        (fun y => ∏ i, K i (endpointPath n p.1 y i.castSucc) (y i)) p.2) := by
    have hprod : Measurable (fun p : ℝ × (Fin n → ℝ) =>
        ∏ i, K i (endpointPath n p.1 p.2 i.castSucc) (p.2 i)) := by
      apply Finset.measurable_prod
      intro i _
      have hp : Measurable (fun p : ℝ × (Fin n → ℝ) =>
          (endpointPath n p.1 p.2 i.castSucc, p.2 i)) := by
        unfold endpointPath
        fun_prop
      exact (hK i).comp hp
    convert! hprod.indicator (measurableSet_Icc.preimage measurable_snd) using 1
  exact hm.lintegral_prod_right'

theorem killedGroupKernelENN_test_integral {ι : Type*} [Countable ι]
    (s : ℝ) (hs : -1 < s) (n : ℕ) (times : ι → ℕ) (barrier : ι → ℝ) (x : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x' : ℝ, killedGroupKernelENN s n times barrier x x' * F x') =
      ∫⁻ y in killedGroupEvent (n+1) times barrier x,
        F ((∑ i, y i)+x) ∂tiltedLogSineProduct s (n+1) := by
  have hK : Measurable (fun x' => killedGroupKernelENN s n times barrier x x') := by
    exact (killedGroupKernelENN_measurable s n times barrier).comp
      (measurable_const.prodMk measurable_id)
  have he : (∫⁻ x', F x' ∂volume.withDensity
      (fun x' => killedGroupKernelENN s n times barrier x x')) =
      ∫⁻ x', killedGroupKernelENN s n times barrier x x' * F x' := by
    simpa only [Pi.mul_apply] using! lintegral_withDensity_eq_lintegral_mul volume hK hF
  rw [← he, ← killedEndpointLaw_eq_withDensity s hs n times barrier x,
    killedEndpointLaw, lintegral_map hF (by fun_prop)]

#print axioms boxChainIntegral_measurable_initial
#print axioms killedGroupKernelENN_test_integral

end ConditionalSpectralExtremes
