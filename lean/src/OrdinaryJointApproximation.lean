import OrdinaryJointDefinitions

/-! The two actual ordinary-Ewens observables differ by o_P(1). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

theorem ordinary_loglog_scale_tendsto_zero (θ : Real) (hθ : 0 < θ) (C : Real) :
    Tendsto (fun n : Nat => C*Real.log (Real.log n)/
      (ordinarySlope θ*Real.sqrt (θ*Real.log n))) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : Nat => Real.log (Real.log n)/Real.sqrt (Real.log n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 : Real)/2) (by norm_num)).tendsto_div_nhds_zero.comp hL
  have hh := ht.const_mul (C/(ordinarySlope θ*Real.sqrt θ))
  simp only [mul_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [Real.sqrt_mul hθ.le]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem ordinary_joint_approximation (hmain : ExactCycleLocalization) (θ : Real) (hθ : 0 < θ)
    (ε : Real) (hε : 0 < ε) :
    Tendsto (fun n : Nat => (ewensProfileLaw θ n).real
      {c | ε≤‖ordinaryJoint θ n c-ordinaryDiagonal θ n c‖}) atTop (𝓝 0) := by
  obtain ⟨C,hC,hcenter⟩ := ordinary_ewens_random_centering hmain θ hθ
  have ha := ordinarySlope_pos θ hθ
  have hscale := ordinary_loglog_scale_tendsto_zero θ hθ C
  have hupper : ∀ᶠ n : Nat in atTop,
      (ewensProfileLaw θ n).real {c | ε≤‖ordinaryJoint θ n c-ordinaryDiagonal θ n c‖} ≤
        ewensProbability θ n (fun c => C*Real.log (Real.log n)<
          |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)|) := by
    filter_upwards [eventually_ge_atTop (2 : Nat),hscale.eventually (gt_mem_nhds hε)] with n hn hsc
    rw [ewensProfileLaw_real θ hθ n]
    apply ewensProbability_mono θ hθ n _ _
    intro c _ hc
    have hnR : 1 < (n : Real) := by exact_mod_cast (show 1<n by omega)
    have hden : 0 < ordinarySlope θ*Real.sqrt (θ*Real.log n) :=
      mul_pos ha (Real.sqrt_pos.2 (mul_pos hθ (Real.log_pos hnR)))
    change ε≤‖ordinaryJoint θ n c-ordinaryDiagonal θ n c‖ at hc
    rw [ordinary_joint_difference θ hθ n c] at hc
    exact (div_lt_div_iff_of_pos_right hden).mp (hsc.trans_le hc)
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) hupper hcenter

#print axioms ordinary_joint_approximation
end ConditionalSpectralExtremes
