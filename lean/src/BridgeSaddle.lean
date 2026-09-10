import PointwiseBridgeDefinitions
import TiltedConcentration

/-! The actual saddle factor in Lemma bridge, bounded using the proved
curvature of the manuscript lambda function. No inverse-tilt Lipschitz
estimate or Taylor bound is assumed as an axiom. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem lambda_deriv_separation (a b v s β : ℝ) (ha : -1 < a)
    (hs : s ∈ Icc a b) (hβ : β ∈ Icc a b)
    (hcurv : ∀ x ∈ Icc a b, v ≤ (deriv^[2] lambda) x) :
    v*|β-s| ≤ |deriv lambda β-deriv lambda s| := by
  have hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ (deriv lambda) x := by
    intro x hx
    exact ((lambda_contDiffAt (lt_of_lt_of_le ha hx.1) 2).derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcont : ContinuousOn (deriv lambda) (Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (deriv lambda) (interior (Icc a b)) :=
    fun x hx => (hd x (interior_subset hx)).differentiableWithinAt
  have hg := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun x hx => hcurv x (interior_subset hx))
  rcases le_total s β with hsβ | hβs
  · rw [abs_of_nonneg (sub_nonneg.mpr hsβ)]
    exact (hg s hs β hβ hsβ).trans (le_abs_self _)
  · rw [abs_sub_comm β s, abs_of_nonneg (sub_nonneg.mpr hβs),
      abs_sub_comm (deriv lambda β) (deriv lambda s)]
    exact (hg β hβ s hs hβs).trans (le_abs_self _)

theorem bridge_saddle_exponent_lower (a b v M s β : ℝ) (ha : -1 < a)
    (hv : 0 < v) (hM : 0 ≤ M) (hs : s ∈ Icc a b) (hβ : β ∈ Icc a b)
    (hcurv : ∀ x ∈ Icc a b, v ≤ (deriv^[2] lambda) x ∧ (deriv^[2] lambda) x ≤ M)
    (q : ℕ) (hq : 0 < q) :
    -(M/v^2) * ((q : ℝ)*deriv lambda β-(q : ℝ)*deriv lambda s)^2/(q : ℝ) ≤
      (q : ℝ)*(lambda β-lambda s) - (β-s)*((q : ℝ)*deriv lambda β) := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hrem := lambda_linear_remainder_bound a b β (s-β) M ha hM hβ
    (by simpa using hs) (fun x hx => (hcurv x hx).2)
  rw [show β+(s-β)=s by ring] at hrem
  have hsep := lambda_deriv_separation a b v s β ha hs hβ (fun x hx => (hcurv x hx).1)
  have hsq : (v*|β-s|)^2 ≤ |deriv lambda β-deriv lambda s|^2 :=
    (sq_le_sq₀ (by positivity) (abs_nonneg _)).mpr hsep
  simp only [mul_pow, sq_abs] at hsq
  have hdist : (s-β)^2 ≤ (deriv lambda β-deriv lambda s)^2/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
    nlinarith only [hsq]
  have hrem' := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hrem) hq'.le
  have hd' := mul_le_mul_of_nonneg_left hdist (mul_nonneg hq'.le hM)
  have he : -(M/v^2) * ((q : ℝ)*deriv lambda β-(q : ℝ)*deriv lambda s)^2/(q : ℝ) =
      -((q : ℝ)*M)*((deriv lambda β-deriv lambda s)^2/v^2) := by
    field_simp
  rw [he]
  nlinarith only [hrem', hd']

theorem bridge_saddle_factor_gaussian_lower (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ∈ Icc a b, ∀ β ∈ Icc a b, ∀ q : ℕ, 0 < q →
      ∀ d : ℝ, d = (q : ℝ)*deriv lambda β →
      Real.exp (-K*(d-(q : ℝ)*deriv lambda s)^2/(q : ℝ)) ≤
        Real.exp ((q : ℝ)*(lambda β-lambda s)-(β-s)*d) := by
  obtain ⟨v, M, hv, hcurv⟩ := lambda_curvature_compact_bounds ha hab
  have hM : 0 < M := lt_of_lt_of_le hv
    ((hcurv a ⟨le_rfl, hab⟩).1.trans (hcurv a ⟨le_rfl, hab⟩).2)
  refine ⟨M/v^2, by positivity, ?_⟩
  intro s hs β hβ q hq d hd
  subst d
  apply Real.exp_le_exp.mpr
  exact bridge_saddle_exponent_lower a b v M s β ha hv hM.le hs hβ hcurv q hq

#print axioms lambda_deriv_separation
#print axioms bridge_saddle_exponent_lower
#print axioms bridge_saddle_factor_gaussian_lower

end ConditionalSpectralExtremes
