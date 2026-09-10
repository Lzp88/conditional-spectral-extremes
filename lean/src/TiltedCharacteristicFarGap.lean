import TiltedCharacteristicNearZero
import TiltedCharacteristicUniformTail

/-! Uniform strict nonlattice control on the entire complement of a
neighborhood of zero, derived from actual moment and frequency-tail bounds. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem tiltedLogSineLaw_norm_charFun_uniform_lipschitz
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ β ∈ Icc a b, ∀ s t : ℝ,
      |‖charFun (tiltedLogSineLaw β) s‖ - ‖charFun (tiltedLogSineLaw β) t‖| ≤ L*|s-t| := by
  obtain ⟨L, hL, hm⟩ := tiltedLogSineLaw_centered_moment_uniform_bound a b ha hab 1
  refine ⟨L, hL, ?_⟩
  intro β hβ s t
  have hb := lt_of_lt_of_le ha hβ.1
  let := centeredTiltedLogSineLaw_probability hb
  have hmem := centeredTiltedLogSineLaw_moments hb 1
  have hc : ContDiff ℝ 1 (charFun (centeredTiltedLogSineLaw β)) := contDiff_charFun hmem
  have hd (x : ℝ) : ‖deriv (charFun (centeredTiltedLogSineLaw β)) x‖ ≤ L := by
    have hh := charFun_iteratedDeriv_norm_le hmem x
    rw [centeredTiltedLogSineLaw_norm_moment] at hh
    have hh' : ‖deriv (charFun (centeredTiltedLogSineLaw β)) x‖ ≤
        ∫ y, ‖centeredLogSine β y‖^1 ∂tiltedLogSineLaw β := by
      simpa only [iteratedDeriv_one] using hh
    exact hh'.trans (hm β hβ)
  rw [← centeredTiltedLogSineLaw_charFun_norm hb s, ← centeredTiltedLogSineLaw_charFun_norm hb t]
  apply (abs_norm_sub_norm_le _ _).trans
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s := (univ : Set ℝ))
    (fun x _ => hc.differentiable (by norm_num) x) (fun x _ => hd x)
    convex_univ (mem_univ t) (mem_univ s)
  simpa only [Real.norm_eq_abs] using hh

theorem tiltedLogSineLaw_charFun_uniform_half_at_infinity
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ R : ℝ, 0 < R ∧ ∀ β ∈ Icc a b, ∀ t : ℝ, R ≤ |t| →
      ‖charFun (tiltedLogSineLaw β) t‖ ≤ 1/2 := by
  obtain ⟨L, hL, hlip⟩ := tiltedLogSineLaw_norm_charFun_uniform_lipschitz a b ha hab
  let r : ℝ := 1/(4*(L+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hLr : L*r ≤ 1/4 := by
    have hh : (4*(L+1))*r = 1 := by dsimp [r]; field_simp
    nlinarith
  obtain ⟨R, hR, htail⟩ := tiltedLogSineLaw_charFun_six_uniform_tail a b ha hab
    (r*(1/4)^6) (by positivity)
  refine ⟨R+r+1, by positivity, ?_⟩
  intro β hβ t ht
  by_contra hbad
  have hlarge : 1/2 < ‖charFun (tiltedLogSineLaw β) t‖ := lt_of_not_ge hbad
  have hdist (s : ℝ) (hs : s ∈ Icc (t-r) (t+r)) : |s-t| ≤ r := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hspike (s : ℝ) (hs : s ∈ Icc (t-r) (t+r)) :
      (1/4 : ℝ)^6 ≤ ‖charFun (tiltedLogSineLaw β) s‖^6 := by
    have hds := (hlip β hβ s t).trans (mul_le_mul_of_nonneg_left (hdist s hs) hL)
    have hd := (abs_le.mp hds).1
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 6
  have hsub : Icc (t-r) (t+r) ⊆ (Icc (-R) R)ᶜ := by
    intro s hs hin
    rcases le_total 0 t with ht0 | ht0
    · rw [abs_of_nonneg ht0] at ht
      linarith [hs.1, hin.2]
    · rw [abs_of_nonpos ht0] at ht
      linarith [hs.2, hin.1]
  have hi := tiltedLogSineLaw_charFun_six_integrable (lt_of_lt_of_le ha hβ.1)
  have hlow : 2*r*(1/4)^6 ≤ ∫ s in Icc (t-r) (t+r), ‖charFun (tiltedLogSineLaw β) s‖^6 := by
    calc
      2*r*(1/4)^6 = ∫ _s in Icc (t-r) (t+r), (1/4 : ℝ)^6 := by
        rw [integral_const, Measure.real, Measure.restrict_apply_univ]
        rw [← Measure.real, Real.volume_real_Icc_of_le (by linarith)]
        simp only [smul_eq_mul]
        ring
      _ ≤ _ := integral_mono_ae (integrable_const _) hi.integrableOn
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs; exact hspike s hs)
  have hmono : (∫ s in Icc (t-r) (t+r), ‖charFun (tiltedLogSineLaw β) s‖^6) ≤
      ∫ s in (Icc (-R) R)ᶜ, ‖charFun (tiltedLogSineLaw β) s‖^6 :=
    setIntegral_mono_set hi.integrableOn
      (Filter.Eventually.of_forall (fun s => pow_nonneg (norm_nonneg _) _))
      (Filter.Eventually.of_forall (fun s hs => hsub hs))
  have hsmall := htail β hβ
  nlinarith

/-- A single strict gap controls all frequencies bounded away from zero. -/
theorem tiltedLogSineLaw_charFun_uniform_far_gap
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ β ∈ Icc a b, ∀ t : ℝ, δ ≤ |t| →
      ‖charFun (tiltedLogSineLaw β) t‖ ≤ ρ := by
  obtain ⟨R, hR, hhalf⟩ := tiltedLogSineLaw_charFun_uniform_half_at_infinity a b ha hab
  let K : Set ℝ := Icc (-R) R \ Ioo (-δ) δ
  have hK : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  have hzero : 0 ∉ K := by intro h; exact h.2 ⟨by linarith, hδ⟩
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ := tiltedLogSineLaw_charFun_uniform_gap a b ha hab K hK hzero
  refine ⟨max ρ (1/2), le_max_of_le_left hρ0, max_lt hρ1 (by norm_num), ?_⟩
  intro β hβ t ht
  by_cases hfar : R ≤ |t|
  · exact (hhalf β hβ t hfar).trans (le_max_right _ _)
  · apply (hgap β hβ t ?_).trans (le_max_left _ _)
    refine ⟨abs_le.mp (le_of_lt (lt_of_not_ge hfar)), ?_⟩
    intro hin
    exact (not_lt_of_ge ht) (abs_lt.mpr hin)

#print axioms tiltedLogSineLaw_norm_charFun_uniform_lipschitz
#print axioms tiltedLogSineLaw_charFun_uniform_half_at_infinity
#print axioms tiltedLogSineLaw_charFun_uniform_far_gap

end ConditionalSpectralExtremes
