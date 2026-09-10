import TiltedLogSineSums
import UniformCriticalParameters

/-! Actual compact-uniform small-parameter quadratic cumulant bounds and
their consequences for finite sums of tilted log-sine increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace ConditionalSpectralExtremes

theorem lambda_linear_remainder_bound (a b β t M : ℝ) (ha : -1 < a)
    (hM : 0 ≤ M) (hb : β ∈ Icc a b) (hbt : β + t ∈ Icc a b)
    (hcurv : ∀ x ∈ Icc a b, (deriv^[2] lambda) x ≤ M) :
    |lambda (β + t) - lambda β - t * deriv lambda β| ≤ M * t ^ 2 := by
  have hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ (deriv lambda) x := by
    intro x hx
    exact ((lambda_contDiffAt (lt_of_lt_of_le ha hx.1) 2).derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hn : ∀ x ∈ Icc a b, ‖deriv (deriv lambda) x‖ ≤ M := by
    intro x hx
    rw [Real.norm_eq_abs]
    change |(deriv^[2] lambda) x| ≤ M
    rw [abs_of_pos (lambda_deriv2_pos (lt_of_lt_of_le ha hx.1))]
    exact hcurv x hx
  have hlip : ∀ u ∈ Icc a b, ‖deriv lambda u - deriv lambda β‖ ≤ M * ‖u - β‖ := by
    intro u hu
    exact Convex.norm_image_sub_le_of_norm_deriv_le hd hn (convex_Icc a b) hb hu
  let g : ℝ → ℝ := fun u => lambda u - u * deriv lambda β
  have hsub : uIcc β (β + t) ⊆ Icc a b := uIcc_subset_Icc hb hbt
  have hg : ∀ u ∈ uIcc β (β + t),
      HasDerivWithinAt g (deriv lambda u - deriv lambda β) (uIcc β (β + t)) u := by
    intro u hu
    have hu' := hsub hu
    have hh := ((lambda_contDiffAt (lt_of_lt_of_le ha hu'.1) 1).differentiableAt
      (by norm_num)).hasDerivAt.sub ((hasDerivAt_id u).mul_const (deriv lambda β))
    simpa only [one_mul] using! hh.hasDerivWithinAt
  have hg_bound : ∀ u ∈ uIcc β (β + t),
      ‖deriv lambda u - deriv lambda β‖ ≤ M * |t| := by
    intro u hu
    have hh := abs_sub_left_of_mem_uIcc hu
    simp only [add_sub_cancel_left] at hh
    exact (hlip u (hsub hu)).trans (mul_le_mul_of_nonneg_left hh hM)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hg_bound
    (convex_uIcc β (β + t)) (left_mem_uIcc) (right_mem_uIcc)
  have he : g (β + t) - g β = lambda (β + t) - lambda β - t * deriv lambda β := by
    dsimp [g]
    ring
  rw [he, add_sub_cancel_left, Real.norm_eq_abs, Real.norm_eq_abs] at hh
  calc
    _ ≤ (M * |t|) * |t| := hh
    _ = M * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem lambda_uniform_quadratic_cumulant (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ β ∈ Icc a b, ∀ t : ℝ, |t| ≤ δ →
      -1 < β + t ∧ |lambda (β + t) - lambda β - t * deriv lambda β| ≤ M * t ^ 2 := by
  let δ := (a + 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlo : -1 < a - δ := by dsimp [δ]; linarith
  have hord : a - δ ≤ b + δ := by linarith
  obtain ⟨vlo, M, hvlo, hcurv⟩ := lambda_curvature_compact_bounds hlo hord
  have hM : 0 < M := lt_of_lt_of_le hvlo ((hcurv (a - δ) ⟨le_rfl, hord⟩).1.trans
    (hcurv (a - δ) ⟨le_rfl, hord⟩).2)
  refine ⟨δ, M, hδ, hM, ?_⟩
  intro β hβ t ht
  have ht' := abs_le.mp ht
  have hb' : β ∈ Icc (a - δ) (b + δ) := ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  have hbt' : β + t ∈ Icc (a - δ) (b + δ) :=
    ⟨by linarith [hβ.1, ht'.1], by linarith [hβ.2, ht'.2]⟩
  exact ⟨lt_of_lt_of_le hlo hbt'.1,
    lambda_linear_remainder_bound _ _ β t M hlo hM.le hb' hbt' (fun x hx => (hcurv x hx).2)⟩

theorem centeredLogSineSum_uniform_mgf_bound (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ β ∈ Icc a b, ∀ q : ℕ, ∀ t : ℝ, |t| ≤ δ →
      Integrable (fun ω => Real.exp (t * centeredLogSineSum β ω)) (tiltedLogSineProduct β q) ∧
      mgf (centeredLogSineSum β) (tiltedLogSineProduct β q) t ≤
        Real.exp ((q : ℝ) * M * t ^ 2) := by
  obtain ⟨δ, M, hδ, hM, hh⟩ := lambda_uniform_quadratic_cumulant a b ha hab
  refine ⟨δ, M, hδ, hM, ?_⟩
  intro β hβ q t ht
  have hb := lt_of_lt_of_le ha hβ.1
  obtain ⟨hbt, hquad⟩ := hh β hβ t ht
  refine ⟨centeredLogSineSum_exp_integrable β t q hb hbt, ?_⟩
  rw [centeredLogSineSum_mgf β t q hb hbt]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (q : ℝ) * (M * t ^ 2) := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans hquad) (Nat.cast_nonneg q)
    _ = _ := by ring

/-- Uniform Gaussian moderate-deviation tails for the actual centered sums.
This is a terminal-sum theorem; it makes no unproved maximal-process claim. -/
theorem centeredLogSineSum_uniform_moderate_deviation (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ β ∈ Icc a b, ∀ q : ℕ, 0 < q →
      ∀ w : ℝ, 0 ≤ w → w ≤ 2 * M * δ * (q : ℝ) →
        (tiltedLogSineProduct β q).real {ω | w ≤ |centeredLogSineSum β ω|} ≤
          2 * Real.exp (-(w ^ 2) / (4 * M * (q : ℝ))) := by
  obtain ⟨δ, M, hδ, hM, hh⟩ := lambda_uniform_quadratic_cumulant a b ha hab
  refine ⟨δ, M, hδ, hM, ?_⟩
  intro β hβ q hq w hw hwrange
  have hb := lt_of_lt_of_le ha hβ.1
  let _ := tiltedLogSineProduct_isProbabilityMeasure β q hb
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  let r := w / (2 * M * (q : ℝ))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrδ : |r| ≤ δ := by
    rw [abs_of_nonneg hr0]
    apply (div_le_iff₀ (by positivity : 0 < 2 * M * (q : ℝ))).mpr
    nlinarith only [hwrange]
  obtain ⟨hbr, hqr⟩ := hh β hβ r hrδ
  obtain ⟨hbn, hqn⟩ := hh β hβ (-r) (by simpa only [abs_neg] using hrδ)
  have hupper : (tiltedLogSineProduct β q).real {ω | w ≤ centeredLogSineSum β ω} ≤
      Real.exp (-(w ^ 2) / (4 * M * (q : ℝ))) := by
    calc
      _ ≤ Real.exp (-r * w + (q : ℝ) *
          (lambda (β + r) - lambda β - r * deriv lambda β)) :=
        centeredLogSineSum_chernoff_upper β r w q hb hbr hr0
      _ ≤ Real.exp (-r * w + (q : ℝ) * (M * r ^ 2)) := by
        apply Real.exp_le_exp.mpr
        linarith only [mul_le_mul_of_nonneg_left ((le_abs_self _).trans hqr) hq'.le]
      _ = _ := by
        congr 1
        dsimp [r]
        field_simp
        ring
  have hlower : (tiltedLogSineProduct β q).real {ω | centeredLogSineSum β ω ≤ -w} ≤
      Real.exp (-(w ^ 2) / (4 * M * (q : ℝ))) := by
    calc
      _ ≤ Real.exp (-(-r) * (-w) + (q : ℝ) *
          (lambda (β + -r) - lambda β - (-r) * deriv lambda β)) :=
        centeredLogSineSum_chernoff_lower β (-r) (-w) q hb hbn (by linarith)
      _ ≤ Real.exp (-(-r) * (-w) + (q : ℝ) * (M * (-r) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        linarith only [mul_le_mul_of_nonneg_left ((le_abs_self _).trans hqn) hq'.le]
      _ = _ := by
        congr 1
        dsimp [r]
        field_simp
        ring
  have he : {ω : Fin q → ℝ | w ≤ |centeredLogSineSum β ω|} =
      {ω | w ≤ centeredLogSineSum β ω} ∪ {ω | centeredLogSineSum β ω ≤ -w} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, le_abs, le_neg]
  rw [he]
  exact (measureReal_union_le _ _).trans ((add_le_add hupper hlower).trans_eq (by ring))

#print axioms lambda_linear_remainder_bound
#print axioms lambda_uniform_quadratic_cumulant
#print axioms centeredLogSineSum_uniform_mgf_bound
#print axioms centeredLogSineSum_uniform_moderate_deviation

end ConditionalSpectralExtremes
