import UniformGammaCoefficient

/-! Uniform Gamma-coefficient asymptotics apply to actual moving complex arguments. -/
noncomputable section
open Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes.ComplexCoefficientAnalysis

theorem normalized_marker_moving_tendsto (z : Nat → Complex) (z₀ : Complex)
    (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n : Nat => (n : Complex)^(1-z n)*markerValue n (z n))
      atTop (𝓝 (Complex.Gamma z₀)⁻¹) := by
  let R : Real := ‖z₀‖+2
  obtain ⟨C,hC,N,_hN,hbound⟩ := uniform_normalized_marker_error
    (show 1 ≤ R by dsimp [R]; linarith [norm_nonneg z₀])
  have hnorm : ∀ᶠ n : Nat in atTop, ‖z n‖ ≤ R :=
    (hz.norm.eventually (gt_mem_nhds (show ‖z₀‖ < R by dsimp [R]; linarith))).mono (fun _ h => h.le)
  have he : Tendsto (fun n : Nat => (n : Complex)^(1-z n)*markerValue n (z n)-(Complex.Gamma (z n))⁻¹)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n : Nat => C/(n : Real))
    · filter_upwards [eventually_ge_atTop N,hnorm] with n hn hz
      exact hbound n hn (z n) hz
    · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun n => (Complex.Gamma (z n))⁻¹) atTop (𝓝 (Complex.Gamma z₀)⁻¹) :=
    (show Continuous (fun w : Complex => (Complex.Gamma w)⁻¹) by
      simpa only [one_div] using Complex.differentiable_one_div_Gamma.continuous).continuousAt.tendsto.comp hz
  simpa only [sub_add_cancel,zero_add] using he.add hg

#print axioms normalized_marker_moving_tendsto
end ConditionalSpectralExtremes.ComplexCoefficientAnalysis
