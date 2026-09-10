import LambdaCurvature

/-! Literal analytic identities displayed in the paper.
The lambda identity uses the actual log-Gamma lambda, with its smoothness
proved in the original corpus. No differentiability assumption is added. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped Topology

namespace ConditionalSpectralExtremes.ExpandedProof

theorem reservoir_log_main_derivative (H l N : ℝ) (hl : 0 < l)
    (hN : 0 < N) (hT : 0 < Real.log N-H) :
    HasDerivAt
      (fun x : ℝ => l*Real.log (Real.log x-H)-Real.log x-
        Real.log (Real.Gamma (l/(Real.log x-H))))
      (1/N*(-1+l/(Real.log N-H)+l/(Real.log N-H)^2*
        (deriv Real.Gamma (l/(Real.log N-H))/Real.Gamma (l/(Real.log N-H))))) N := by
  have hlog := Real.hasDerivAt_log hN.ne'
  have ht := hlog.sub_const H
  have harg : 0 < l/(Real.log N-H) := div_pos hl hT
  have hratio := (hasDerivAt_const N l).div ht hT.ne'
  have hgamma := (gamma_differentiableAt_pos harg).hasDerivAt.comp N hratio
  have hg : Real.Gamma (l/(Real.log N-H)) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg).ne'
  have hd := (((ht.log hT.ne').const_mul l).sub hlog).sub (hgamma.log hg)
  apply hd.congr_deriv
  simp only [Function.comp_apply, Pi.div_apply]
  field_simp [hN.ne', hT.ne', hg]
  ring

theorem reservoir_log_main_identity (H N : ℝ) (l : ℕ)
    (hl : 0 < l) (hN : 0 < N) (hT : 0 < Real.log N-H) :
    Real.log ((Real.log N-H)^l/(N*Real.Gamma ((l : ℝ)/(Real.log N-H)))) =
      (l : ℝ)*Real.log (Real.log N-H)-Real.log N-
        Real.log (Real.Gamma ((l : ℝ)/(Real.log N-H))) := by
  have harg : 0 < (l : ℝ)/(Real.log N-H) := div_pos (Nat.cast_pos.mpr hl) hT
  have hg : Real.Gamma ((l : ℝ)/(Real.log N-H)) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg).ne'
  rw [Real.log_div (pow_ne_zero _ hT.ne') (mul_ne_zero hN.ne' hg),
    Real.log_mul hN.ne' hg, Real.log_pow]
  ring

theorem actual_reservoir_log_main_derivative (H N : ℝ) (l : ℕ)
    (hl : 0 < l) (hN : 0 < N) (hT : 0 < Real.log N-H) :
    HasDerivAt
      (fun x : ℝ => Real.log ((Real.log x-H)^l/
        (x*Real.Gamma ((l : ℝ)/(Real.log x-H)))))
      (1/N*(-1+(l : ℝ)/(Real.log N-H)+(l : ℝ)/(Real.log N-H)^2*
        (deriv Real.Gamma ((l : ℝ)/(Real.log N-H))/
          Real.Gamma ((l : ℝ)/(Real.log N-H))))) N := by
  have hd := reservoir_log_main_derivative H (l : ℝ) N (Nat.cast_pos.mpr hl) hN hT
  apply hd.congr_of_eventuallyEq
  have hpos : ∀ᶠ x : ℝ in 𝓝 N, 0 < x := lt_mem_nhds hN
  have htpos := ((Real.hasDerivAt_log hN.ne').sub_const H).continuousAt.eventually
    (lt_mem_nhds hT)
  filter_upwards [hpos, htpos] with x hx htx
  exact reservoir_log_main_identity H x l hl hx htx

theorem actual_lambda_saddle_integral (s β : ℝ) (hs : -1 < s) (hβ : -1 < β) :
    lambda β-lambda s-(β-s)*deriv lambda β =
      -(∫ t in s..β, (t-s)*deriv (deriv lambda) t) := by
  have hdom (x : ℝ) (hx : x ∈ uIcc s β) : -1 < x :=
    lt_of_lt_of_le (lt_min hs hβ) hx.1
  have hderiv (x : ℝ) (hx : x ∈ uIcc s β) :
      HasDerivAt (fun t : ℝ => lambda t-(t-s)*deriv lambda t)
        (-((x-s)*deriv (deriv lambda) x)) x := by
    have h1 : HasDerivAt lambda (deriv lambda x) x :=
      ((lambda_contDiffAt (hdom x hx) 1).differentiableAt
      (by norm_num)).hasDerivAt
    have h2 : HasDerivAt (deriv lambda) (deriv (deriv lambda) x) x :=
      (((lambda_contDiffAt (hdom x hx) 2).derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
    apply (h1.sub (((hasDerivAt_id x).sub_const s).mul h2)).congr_deriv
    simp only [id_eq, one_mul]
    ring
  have hcont : ContinuousOn (fun t : ℝ => -((t-s)*deriv (deriv lambda) t))
      (uIcc s β) := by
    intro x hx
    have hc := (((lambda_contDiffAt (hdom x hx) 3).derivWithin
      (m := 2) (by norm_num)).derivWithin (m := 1) (by norm_num)).continuousAt
    exact (((continuousAt_id.sub continuousAt_const).mul hc).neg).continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg] at hi
  simp only [sub_self, zero_mul, sub_zero] at hi
  linarith

theorem actual_lambda_saddle_quadratic (s β M : ℝ) (hs : -1 < s) (hβ : -1 < β)
    (hM : ∀ t ∈ uIcc s β, deriv (deriv lambda) t ≤ M) :
    -(M/2)*(β-s)^2 ≤ lambda β-lambda s-(β-s)*deriv lambda β := by
  have hdom (x : ℝ) (hx : x ∈ uIcc s β) : -1 < x :=
    lt_of_lt_of_le (lt_min hs hβ) hx.1
  have hc : ContinuousOn (deriv (deriv lambda)) (uIcc s β) := by
    intro x hx
    exact (((lambda_contDiffAt (hdom x hx) 3).derivWithin
      (m := 2) (by norm_num)).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hf : IntervalIntegrable (fun t : ℝ => (t-s)*deriv (deriv lambda) t) volume s β :=
    ((continuous_id.sub continuous_const).continuousOn.mul hc).intervalIntegrable
  have hp : IntervalIntegrable (fun t : ℝ => (t-s)*M) volume s β :=
    ((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _
  have hlinear : (∫ t in s..β, (t-s)*M) = (M/2)*(β-s)^2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub
      (f := fun t : ℝ => t) (g := fun _ : ℝ => s)
      (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hbound : (∫ t in s..β, (t-s)*deriv (deriv lambda) t) ≤ (M/2)*(β-s)^2 := by
    rcases le_total s β with hle | hle
    · have hi := intervalIntegral.integral_mono_on hle hf hp (fun t ht =>
        mul_le_mul_of_nonneg_left (hM t (by simpa only [uIcc_of_le hle] using ht))
          (sub_nonneg.mpr ht.1))
      rwa [hlinear] at hi
    · have hi := intervalIntegral.integral_mono_on hle hp.symm hf.symm (fun t ht =>
        mul_le_mul_of_nonpos_left (hM t (by simpa only [uIcc_of_ge hle] using ht))
          (sub_nonpos.mpr ht.2))
      simp only [intervalIntegral.integral_symm s β] at hi
      rw [hlinear] at hi
      linarith
  rw [actual_lambda_saddle_integral s β hs hβ]
  linarith

end ConditionalSpectralExtremes.ExpandedProof
