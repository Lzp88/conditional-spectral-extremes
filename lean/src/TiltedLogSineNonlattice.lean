import TiltedLogSineDensity

/-! Strict nonlattice characteristic-function bounds for the actual tilted
log-sine law. Countability of complex-exponential fibers and the proved
absence of atoms exclude the equality case of the strict Jensen theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology

namespace ConditionalSpectralExtremes

theorem real_exponential_fiber_countable (t : ℝ) (ht : t ≠ 0) (z : ℂ) :
    {x : ℝ | Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) = z}.Countable := by
  have hinj : Injective (fun x : ℝ => ((t * x : ℝ) : ℂ) * Complex.I) := by
    intro x y he
    have hh := congrArg Complex.im he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hh
    exact mul_left_cancel₀ ht hh
  exact (Set.countable_singleton z).preimage_cexp.preimage hinj

/-- A nonatomic real probability measure has strictly subunit characteristic
function at every nonzero frequency. The hypothesis is verified below for
the actual log-sine law using its exact Jacobian density. -/
theorem nonatomic_charFun_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (t : ℝ) (ht : t ≠ 0) : ‖charFun μ t‖ < 1 := by
  let f : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  have hf : ∀ x, ‖f x‖ = 1 := by intro x; simp [f, Complex.norm_exp]
  have hh := ae_eq_const_or_norm_integral_lt_of_norm_le_const
    (μ := μ) (f := f) (C := 1) (ae_of_all _ (fun x => (hf x).le))
  rcases hh with hconst | hlt
  · have hn := (real_exponential_fiber_countable t ht (⨍ x, f x ∂μ)).ae_notMem μ
    obtain ⟨x, hx, hx'⟩ := (hconst.and hn).exists
    exact False.elim (hx' hx)
  · rw [charFun_apply_real]
    simpa [measureReal_def, f, Complex.ofReal_mul] using hlt

theorem tiltedLogSineLaw_charFun_lt_one (β t : ℝ) (hβ : -1 < β) (ht : t ≠ 0) :
    ‖charFun (tiltedLogSineLaw β) t‖ < 1 := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  let _ : NullSingletonClass (tiltedLogSineLaw β) :=
    ⟨fun x => tiltedLogSineLaw_singleton_zero β x hβ⟩
  exact nonatomic_charFun_lt_one _ t ht

/-- For each fixed actual tilt, the strict nonlattice bound is uniform on
any compact set of frequencies that excludes zero. -/
theorem tiltedLogSineLaw_charFun_compact_gap (β : ℝ) (hβ : -1 < β)
    (K : Set ℝ) (hK : IsCompact K) (hzero : 0 ∉ K) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ t ∈ K, ‖charFun (tiltedLogSineLaw β) t‖ ≤ ρ := by
  let _ := tiltedLogSineLaw_isProbabilityMeasure β hβ
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    simp [he]
  · obtain ⟨t, ht, hmax⟩ := hK.exists_isMaxOn hne
      ((continuous_charFun (μ := tiltedLogSineLaw β)).norm.continuousOn)
    refine ⟨‖charFun (tiltedLogSineLaw β) t‖, norm_nonneg _,
      tiltedLogSineLaw_charFun_lt_one β t hβ (by intro he; exact hzero (he ▸ ht)), ?_⟩
    exact hmax

def logSineFourierLaplaceIntegrand (p : ℝ × ℝ) (x : ℝ) : ℂ :=
  (Real.exp (p.1 * x) : ℂ) * Complex.exp (((p.2 * x : ℝ) : ℂ) * Complex.I)

def logSineFourierLaplace (p : ℝ × ℝ) : ℂ :=
  ∫ x, logSineFourierLaplaceIntegrand p x ∂logSineLaw

theorem logSineFourierLaplaceIntegrand_norm (p : ℝ × ℝ) (x : ℝ) :
    ‖logSineFourierLaplaceIntegrand p x‖ = Real.exp (p.1 * x) := by
  simp [logSineFourierLaplaceIntegrand, Complex.norm_exp]

theorem logSineFourierLaplace_continuousOn (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ContinuousOn logSineFourierLaplace ((Icc a b) ×ˢ (univ : Set ℝ)) := by
  apply continuousOn_of_dominated
    (bound := fun x => Real.exp (a * x) + Real.exp (b * x))
  · intro p hp
    exact (show Continuous (logSineFourierLaplaceIntegrand p) by
      unfold logSineFourierLaplaceIntegrand; fun_prop).aestronglyMeasurable
  · intro p hp
    apply ae_of_all
    intro x
    rw [logSineFourierLaplaceIntegrand_norm]
    by_cases hx : 0 ≤ x
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hp.1.2 hx)).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hp.1.1 (le_of_not_ge hx))).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact (logSineLaw_exp_integrable a ha).add
      (logSineLaw_exp_integrable b (lt_of_lt_of_le ha hab))
  · apply ae_of_all
    intro x
    exact (show Continuous (fun p : ℝ × ℝ => logSineFourierLaplaceIntegrand p x) by
      unfold logSineFourierLaplaceIntegrand; fun_prop).continuousOn

theorem tiltedLogSineLaw_charFun_eq_fourierLaplace (β t : ℝ) (hβ : -1 < β) :
    charFun (tiltedLogSineLaw β) t = Real.exp (-lambda β) • logSineFourierLaplace (β, t) := by
  rw [charFun_apply_real]
  unfold tiltedLogSineLaw
  rw [integral_tilted, logSineLaw_integral_exp β hβ, logSineA_eq_exp_lambda β hβ]
  unfold logSineFourierLaplace
  rw [← integral_smul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [logSineFourierLaplaceIntegrand, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_mul, Real.exp_neg, Complex.ofReal_inv]
  ring

/-- Joint continuity in the tilt and frequency on every admissible closed strip. -/
theorem tiltedLogSineLaw_charFun_continuousOn_strip (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ContinuousOn (fun p : ℝ × ℝ => charFun (tiltedLogSineLaw p.1) p.2)
      ((Icc a b) ×ˢ (univ : Set ℝ)) := by
  have hl : ContinuousOn (fun p : ℝ × ℝ => lambda p.1) ((Icc a b) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    exact (((lambda_contDiffAt (lt_of_lt_of_le ha hp.1.1) 0).continuousAt).comp
      continuous_fst.continuousAt).continuousWithinAt
  have hh := hl.neg.rexp.smul (logSineFourierLaplace_continuousOn a b ha hab)
  apply hh.congr
  intro p hp
  exact tiltedLogSineLaw_charFun_eq_fourierLaplace p.1 p.2 (lt_of_lt_of_le ha hp.1.1)

/-- The actual strict nonlattice bound, uniform simultaneously over a compact
tilt interval and a compact frequency set away from zero. -/
theorem tiltedLogSineLaw_charFun_uniform_gap (a b : ℝ) (ha : -1 < a) (hab : a ≤ b)
    (K : Set ℝ) (hK : IsCompact K) (hzero : 0 ∉ K) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ β ∈ Icc a b, ∀ t ∈ K,
      ‖charFun (tiltedLogSineLaw β) t‖ ≤ ρ := by
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    simp [he]
  · have hcomp : IsCompact ((Icc a b) ×ˢ K) := isCompact_Icc.prod hK
    have hcont := (tiltedLogSineLaw_charFun_continuousOn_strip a b ha hab).norm.mono
      (Set.prod_mono (Subset.refl _) (subset_univ K))
    obtain ⟨p, hp, hmax⟩ := hcomp.exists_isMaxOn ((nonempty_Icc.mpr hab).prod hne) hcont
    refine ⟨‖charFun (tiltedLogSineLaw p.1) p.2‖, norm_nonneg _,
      tiltedLogSineLaw_charFun_lt_one p.1 p.2 (lt_of_lt_of_le ha hp.1.1)
        (by intro he; exact hzero (he ▸ hp.2)), ?_⟩
    intro β hβ t ht
    exact hmax (a := (β, t)) ⟨hβ, ht⟩

#print axioms real_exponential_fiber_countable
#print axioms nonatomic_charFun_lt_one
#print axioms tiltedLogSineLaw_charFun_lt_one
#print axioms tiltedLogSineLaw_charFun_compact_gap
#print axioms logSineFourierLaplaceIntegrand_norm
#print axioms logSineFourierLaplace_continuousOn
#print axioms tiltedLogSineLaw_charFun_eq_fourierLaplace
#print axioms tiltedLogSineLaw_charFun_continuousOn_strip
#print axioms tiltedLogSineLaw_charFun_uniform_gap

end ConditionalSpectralExtremes
