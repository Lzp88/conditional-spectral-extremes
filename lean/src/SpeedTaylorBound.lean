import UniformCriticalParameters

/-! Actual speed, positive first derivative, and a local quadratic Taylor bound.
No smoothness or Taylor remainder is supplied as a hypothesis. -/
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ConditionalSpectralExtremes

theorem lambda_pos {s : ℝ} (hs : 0 < s) : 0 < lambda s := by
  have hc := lambda_strictConvexOn.2
    (show (0 : ℝ) ∈ Ioi (-1) by norm_num)
    (show s ∈ Ioi (-1) by change -1 < s; linarith)
    (ne_of_lt hs)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, lambda_zero] at hc
  have hn := lambda_nonneg (s := 1 / 2 * s) (by linarith)
  linarith

theorem speed_coefficient_pos (θ : ℝ) (hθ : 0 < θ) :
    0 < lambda (criticalPoint θ) / criticalPoint θ :=
  div_pos (lambda_pos (criticalPoint_pos hθ)) (criticalPoint_pos hθ)

theorem speed_deriv_compact_lipschitz {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |deriv speed y - deriv speed x| ≤ C * |y - x| := by
  obtain ⟨vlo, vhi, hvlo, hcurv⟩ := critical_curvature_uniform ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hs : 0 < criticalPoint b := criticalPoint_pos hb
  let C : ℝ := 1 / (a ^ 3 * criticalPoint b ^ 3 * vlo)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hbound : ∀ u ∈ Icc a b,
      ‖-1 / (u ^ 3 * criticalPoint u ^ 3 * (deriv^[2] lambda) (criticalPoint u))‖ ≤ C := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
    have hsu := criticalPoint_pos hu0
    have hcu := lambda_deriv2_pos (by linarith : -1 < criticalPoint u)
    have hlower : a ^ 3 * criticalPoint b ^ 3 * vlo ≤
        u ^ 3 * criticalPoint u ^ 3 * (deriv^[2] lambda) (criticalPoint u) := by
      gcongr
      · exact hu.1
      · exact (criticalPoint_compact_bounds ha hu.1 hu.2).2.1
      · exact (hcurv u hu).1
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_one,
      abs_of_pos (show 0 < u ^ 3 * criticalPoint u ^ 3 *
        (deriv^[2] lambda) (criticalPoint u) by positivity)]
    exact one_div_le_one_div_of_le (by positivity) hlower
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (speed_deriv_hasDerivAt (lt_of_lt_of_le ha hu.1)).hasDerivWithinAt)
      hbound hx hy

theorem speed_local_quadratic_remainder (θ : ℝ) (hθ : 0 < θ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ < θ ∧
      ∀ κ : ℝ, |κ - θ| ≤ δ →
        |speed κ - speed θ -
            (lambda (criticalPoint θ) / criticalPoint θ) * (κ - θ)|
          ≤ C * (κ - θ) ^ 2 := by
  obtain ⟨C, hC, hLip⟩ := speed_deriv_compact_lipschitz
    (a := θ / 2) (b := 3 * θ / 2) (by linarith) (by linarith)
  refine ⟨θ / 2, C, by linarith, hC, by linarith, ?_⟩
  intro κ hκ
  let d : ℝ := |κ - θ|
  let S : Set ℝ := Icc (θ - d) (θ + d)
  have hd : 0 ≤ d := abs_nonneg _
  have hsub : S ⊆ Icc (θ / 2) (3 * θ / 2) := by
    intro u hu
    change θ - d ≤ u ∧ u ≤ θ + d at hu
    change d ≤ θ / 2 at hκ
    constructor <;> linarith [hu.1, hu.2]
  have hθS : θ ∈ S := by constructor <;> linarith
  have hκS : κ ∈ S := by
    have hh := abs_le.mp (le_refl d : |κ - θ| ≤ d)
    constructor <;> linarith [hh.1, hh.2]
  let F : ℝ → ℝ := fun u => speed u - speed θ - deriv speed θ * (u - θ)
  have hF : ∀ u ∈ S, HasDerivWithinAt F (deriv speed u - deriv speed θ) S u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le (by linarith : 0 < θ / 2) (hsub hu).1
    have hv := (speed_hasDerivAt hu0).differentiableAt.hasDerivAt
    convert! ((hv.sub_const (speed θ)).sub
      (((hasDerivAt_id u).sub_const θ).const_mul (deriv speed θ))).hasDerivWithinAt using 1
    simp
  have hFb : ∀ u ∈ S, ‖deriv speed u - deriv speed θ‖ ≤ C * d := by
    intro u hu
    have hud : |u - θ| ≤ d := by
      apply abs_le.mpr
      constructor <;> linarith [hu.1, hu.2]
    rw [Real.norm_eq_abs]
    exact (hLip θ (hsub hθS) u (hsub hu)).trans (mul_le_mul_of_nonneg_left hud hC.le)
  have hm := (convex_Icc (θ - d) (θ + d)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hF hFb hθS hκS
  simp only [F, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at hm
  rw [(speed_hasDerivAt hθ).deriv] at hm
  calc
    _ ≤ (C * d) * |κ - θ| := hm
    _ = C * (κ - θ) ^ 2 := by dsimp [d]; rw [mul_assoc, ← sq, sq_abs]

#print axioms lambda_pos
#print axioms speed_coefficient_pos
#print axioms speed_deriv_compact_lipschitz
#print axioms speed_local_quadratic_remainder

end ConditionalSpectralExtremes
