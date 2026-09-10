import TripleDensityLaw

/-! Exact exponential-tilt identities give joint parameter/spatial continuity
and global compact-parameter bounds for the actual triple density. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Convolution Topology

namespace ConditionalSpectralExtremes

theorem convolution_exp_tilt (f g : ℝ → ℝ) (β c d x : ℝ) :
    ((fun y => Real.exp (β * y - c) * f y) ⋆[ContinuousLinearMap.mul ℝ ℝ]
      (fun y => Real.exp (β * y - d) * g y)) x =
        Real.exp (β * x - (c + d)) * (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  calc
    (Real.exp (β * y - c) * f y) * (Real.exp (β * (x - y) - d) * g (x - y)) =
      (Real.exp (β * y - c) * Real.exp (β * (x - y) - d)) * (f y * g (x - y)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem tiltedDensity_zero : tiltedDensity 0 = logSineDensity := by
  funext x
  simp [tiltedDensity_eq_weight, lambda_zero]

theorem tiltedDensityDouble_exp_tilt (β x : ℝ) :
    tiltedDensityDouble β x =
      Real.exp (β * x - 2 * lambda β) * tiltedDensityDouble 0 x := by
  unfold tiltedDensityDouble
  rw [tiltedDensity_zero]
  have hfun : tiltedDensity β = fun y => Real.exp (β * y - lambda β) * logSineDensity y :=
    funext (tiltedDensity_eq_weight β)
  rw [hfun, convolution_exp_tilt]
  congr 2
  ring

theorem tiltedDensityTriple_exp_tilt (β x : ℝ) :
    tiltedDensityTriple β x =
      Real.exp (β * x - 3 * lambda β) * tiltedDensityTriple 0 x := by
  unfold tiltedDensityTriple
  rw [tiltedDensity_zero]
  have hd : tiltedDensityDouble β = fun y =>
      Real.exp (β * y - 2 * lambda β) * tiltedDensityDouble 0 y :=
    funext (tiltedDensityDouble_exp_tilt β)
  have hf : tiltedDensity β = fun y => Real.exp (β * y - lambda β) * logSineDensity y :=
    funext (tiltedDensity_eq_weight β)
  rw [hd, hf, convolution_exp_tilt]
  congr 2
  ring

theorem tiltedDensityTriple_joint_continuous :
    Continuous (fun p : Ioi (-1 : ℝ) × ℝ => tiltedDensityTriple p.1.val p.2) := by
  have hl : Continuous (fun β : Ioi (-1 : ℝ) => lambda β.val) := by
    apply continuous_iff_continuousAt.mpr
    intro β
    exact (lambda_contDiffAt β.property 0).continuousAt.comp continuous_subtype_val.continuousAt
  have hh : Continuous (fun p : Ioi (-1 : ℝ) × ℝ =>
      Real.exp (p.1.val * p.2 - 3 * lambda p.1.val) * tiltedDensityTriple 0 p.2) :=
    (((continuous_subtype_val.comp continuous_fst).mul continuous_snd).sub
    (continuous_const.mul (hl.comp continuous_fst))).rexp.mul
      ((tiltedDensityTriple_continuous (by norm_num : (-1 : ℝ) < 0)).comp continuous_snd)
  exact hh.congr (fun p => (tiltedDensityTriple_exp_tilt p.1.val p.2).symm)

theorem tiltedDensityTriple_unnormalized (β x : ℝ) :
    Real.exp (3 * lambda β) * tiltedDensityTriple β x =
      Real.exp (β * x) * tiltedDensityTriple 0 x := by
  rw [tiltedDensityTriple_exp_tilt, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tiltedDensityTriple_endpoint_domination {a b β : ℝ} (hβ : β ∈ Icc a b) (x : ℝ) :
    tiltedDensityTriple β x ≤ Real.exp (-3 * lambda β) *
      (Real.exp (3 * lambda a) * tiltedDensityTriple a x +
        Real.exp (3 * lambda b) * tiltedDensityTriple b x) := by
  rw [tiltedDensityTriple_unnormalized, tiltedDensityTriple_unnormalized,
    tiltedDensityTriple_exp_tilt]
  have he : Real.exp (β * x) ≤ Real.exp (a * x) + Real.exp (b * x) := by
    by_cases hx : 0 ≤ x
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ.2 hx)).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hβ.1 (le_of_not_ge hx))).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
  rw [show β * x - 3 * lambda β = -3 * lambda β + β * x by ring, Real.exp_add]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.exp_pos (-3 * lambda β)).le)
      (tiltedDensityTriple_nonneg 0 x)
  simpa only [mul_add, add_mul, mul_assoc] using hh

theorem tiltedDensityTriple_compact_uniform_bound (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ β ∈ Icc a b, ∀ x, ‖tiltedDensityTriple β x‖ ≤ C := by
  have hc : ContinuousOn (fun β : ℝ => Real.exp (-3 * lambda β)) (Icc a b) := by
    intro β hβ
    exact ((continuousAt_const.mul
      (lambda_contDiffAt (lt_of_lt_of_le ha hβ.1) 0).continuousAt).rexp).continuousWithinAt
  obtain ⟨β₀, hβ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  obtain ⟨Ca, hCa⟩ := tiltedDensityTriple_bounded ha
  obtain ⟨Cb, hCb⟩ := tiltedDensityTriple_bounded (lt_of_lt_of_le ha hab)
  refine ⟨Real.exp (-3 * lambda β₀) *
    (Real.exp (3 * lambda a) * Ca + Real.exp (3 * lambda b) * Cb), ?_⟩
  intro β hβ x
  rw [Real.norm_of_nonneg (tiltedDensityTriple_nonneg β x)]
  apply (tiltedDensityTriple_endpoint_domination hβ x).trans
  apply mul_le_mul
  · exact hmax hβ
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [Real.norm_of_nonneg (tiltedDensityTriple_nonneg a x)] using hCa x
    · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [Real.norm_of_nonneg (tiltedDensityTriple_nonneg b x)] using hCb x
  · exact add_nonneg
      (mul_nonneg (Real.exp_pos _).le (tiltedDensityTriple_nonneg a x))
      (mul_nonneg (Real.exp_pos _).le (tiltedDensityTriple_nonneg b x))
  · exact (Real.exp_pos _).le

#print axioms convolution_exp_tilt
#print axioms tiltedDensity_zero
#print axioms tiltedDensityDouble_exp_tilt
#print axioms tiltedDensityTriple_exp_tilt
#print axioms tiltedDensityTriple_joint_continuous
#print axioms tiltedDensityTriple_unnormalized
#print axioms tiltedDensityTriple_endpoint_domination
#print axioms tiltedDensityTriple_compact_uniform_bound

end ConditionalSpectralExtremes
