import TiltedLogSine
import FourierTail

/-! Identification of the actual complex Laplace transform by holomorphic continuation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Real Complex Topology

namespace ConditionalSpectralExtremes

def complexLogSineA (z : Complex) : Complex :=
  Complex.Gamma (1 + z) * (Complex.Gamma (1 + z / 2))⁻¹ ^ 2

theorem complexLogSineA_ofReal (s : Real) : complexLogSineA s = (logSineA s : Complex) := by
  unfold complexLogSineA logSineA
  rw [show (1 : Complex) + (s : Complex) = ((1 + s : Real) : Complex) by push_cast; rfl,
    show (1 : Complex) + (s : Complex) / 2 = ((1 + s / 2 : Real) : Complex) by push_cast; rfl]
  simp only [Complex.Gamma_ofReal]
  push_cast
  ring

theorem complexLogSineA_analyticOnNhd :
    AnalyticOnNhd Complex complexLogSineA {z : Complex | -1 < z.re} := by
  have ho : IsOpen {z : Complex | -1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ ho
  intro z hz
  have hg : DifferentiableAt Complex Complex.Gamma (1 + z) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
    have hnn : (0 : Real) ≤ n := Nat.cast_nonneg n
    change -1 < z.re at hz
    linarith
  have hc : DifferentiableAt Complex (fun w : Complex => 1 + w) z := by fun_prop
  have hi : Differentiable Complex (fun w : Complex => (Complex.Gamma (1 + w / 2))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  exact ((hg.comp z hc).mul ((hi z).pow 2)).differentiableWithinAt

theorem logSineLaw_complexMGF_analyticOnNhd :
    AnalyticOnNhd Complex (complexMGF id logSineLaw) {z : Complex | -1 < z.re} := by
  apply analyticOnNhd_complexMGF.mono
  intro z hz
  exact logSineLaw_interior_exp_domain z.re hz

theorem logSineLaw_complexMGF_eq_Gamma :
    EqOn (complexMGF id logSineLaw) complexLogSineA {z : Complex | -1 < z.re} := by
  have hpre : IsPreconnected {z : Complex | -1 < z.re} :=
    ((convex_Ioi (-1 : Real)).linear_preimage Complex.reLm).isPreconnected
  apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    logSineLaw_complexMGF_analyticOnNhd complexLogSineA_analyticOnNhd hpre
    (z₀ := (0 : Complex)) (by norm_num)
  have hr : ∃ᶠ (x : Real) in 𝓝[≠] (0 : Real),
      complexMGF id logSineLaw (x : Complex) = complexLogSineA (x : Complex) := by
    apply (eventually_gt_nhds (by norm_num : (-1 : Real) < 0)).filter_mono nhdsWithin_le_nhds |>.frequently.mono
    intro x hx
    rw [complexMGF_ofReal, logSineLaw_mgf x hx, complexLogSineA_ofReal]
  rw [frequently_iff_seq_forall] at hr ⊢
  obtain ⟨xs, hxs, heq⟩ := hr
  refine ⟨fun n => (xs n : Complex), ?_, heq⟩
  rw [tendsto_nhdsWithin_iff] at hxs ⊢
  constructor
  · simpa only [Function.comp_apply, Complex.ofReal_zero] using! Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1
  · simpa using hxs.2

theorem complexPhi_eq_exp_logSine_ae (z : Complex) :
    ConditionalSpectralAudit.FourierTail.complexPhi z =ᵐ[AddCircle.haarAddCircle]
      (fun t => Complex.exp (z * (logSine t : Complex))) := by
  filter_upwards [logSine_root_null] with t ht
  have hp := logSine_norm_pos ht
  unfold ConditionalSpectralAudit.FourierTail.complexPhi logSine
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le]
  congr 1
  ring

theorem actual_complex_mellin_eq_complexMGF (z : Complex) :
    (∫ t : AddCircle (1 : Real), ConditionalSpectralAudit.FourierTail.complexPhi z t ∂AddCircle.haarAddCircle) =
      complexMGF id logSineLaw z := by
  rw [integral_congr_ae (complexPhi_eq_exp_logSine_ae z)]
  unfold logSineLaw
  rw [complexMGF_id_map logSine_measurable.aemeasurable]
  rfl

theorem actual_complex_mellin_Gamma (z : Complex) (hz : -1 < z.re) :
    (∫ t : AddCircle (1 : Real), ConditionalSpectralAudit.FourierTail.complexPhi z t ∂AddCircle.haarAddCircle) =
      complexLogSineA z := by
  rw [actual_complex_mellin_eq_complexMGF]
  exact logSineLaw_complexMGF_eq_Gamma hz

theorem actual_zero_complex_fourier_Gamma (z : Complex) (hz : -1 < z.re) :
    ConditionalSpectralAudit.FourierTail.complexCoefficient z 0 = complexLogSineA z := by
  simpa only [ConditionalSpectralAudit.FourierTail.complexCoefficient, fourierCoeff,
    neg_zero, fourier_zero, one_smul] using actual_complex_mellin_Gamma z hz

#print axioms logSineLaw_complexMGF_eq_Gamma
#print axioms actual_complex_mellin_Gamma
#print axioms actual_zero_complex_fourier_Gamma
end ConditionalSpectralExtremes
