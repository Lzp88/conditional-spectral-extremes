import LambdaCurvature

/-! Actual implicit-parameter and speed derivatives, using the inverse theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology

namespace ConditionalSpectralExtremes

def entropy (s : ℝ) : ℝ := s * deriv lambda s - lambda s

theorem entropy_hasDerivAt {s : ℝ} (hs : -1 < s) :
    HasDerivAt entropy (s * (deriv^[2] lambda) s) s := by
  have hd : HasDerivAt lambda (deriv lambda s) s :=
    (lambda_hasDerivAt hs).differentiableAt.hasDerivAt
  have hdd : HasDerivAt (deriv lambda) ((deriv^[2] lambda) s) s :=
    ((lambda_contDiffAt hs 2).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasDerivAt
  convert! ((hasDerivAt_id s).mul hdd).sub hd using 1
  simp only [id_eq, one_mul]
  ring

theorem entropy_contDiffAt {s : ℝ} (hs : -1 < s) : ContDiffAt ℝ 1 entropy s :=
  (contDiffAt_id.mul ((lambda_contDiffAt hs 2).derivWithin (m := 1) (by norm_num))).sub
    (lambda_contDiffAt hs 1)

theorem entropy_at_criticalPoint {κ : ℝ} (hκ : 0 < κ) :
    entropy (criticalPoint κ) = κ⁻¹ := by
  have h := criticalPoint_equation hκ
  change κ * entropy (criticalPoint κ) = 1 at h
  apply (mul_left_cancel₀ hκ.ne')
  rw [h, mul_inv_cancel₀ hκ.ne']

theorem criticalPoint_hasDerivAt {κ : ℝ} (hκ : 0 < κ) :
    HasDerivAt criticalPoint
      (-1 / (κ ^ 2 * criticalPoint κ * (deriv^[2] lambda) (criticalPoint κ))) κ := by
  let s := criticalPoint κ
  have hs : 0 < s := criticalPoint_pos hκ
  have hsd : -1 < s := by linarith
  have he : entropy s = κ⁻¹ := entropy_at_criticalPoint hκ
  have hepos : 0 < entropy s := by rw [he]; positivity
  let f := fun t : ℝ => (entropy t)⁻¹
  have hfcont : ContDiffAt ℝ 1 f s := (entropy_contDiffAt hsd).inv hepos.ne'
  have hfd : HasDerivAt f (-(κ ^ 2 * s * (deriv^[2] lambda) s)) s := by
    have h := (entropy_hasDerivAt hsd).inv hepos.ne'
    convert! h using 1
    rw [he]
    field_simp
  have hf : HasStrictDerivAt f (-(κ ^ 2 * s * (deriv^[2] lambda) s)) s :=
    hfcont.hasStrictDerivAt' hfd (by norm_num)
  have hfne : -(κ ^ 2 * s * (deriv^[2] lambda) s) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hκ.ne') hs.ne')
      (lambda_deriv2_pos hsd).ne')
  have hleft : ∀ᶠ t : ℝ in 𝓝 s, criticalPoint (f t) = t := by
    filter_upwards [Ioi_mem_nhds hs,
      (entropy_contDiffAt hsd).continuousAt.eventually (lt_mem_nhds hepos)] with t ht het
    have hft : 0 < f t := inv_pos.2 het
    exact (criticalPoint_unique hft ht (by
      change (entropy t)⁻¹ * entropy t = 1
      exact inv_mul_cancel₀ het.ne')).symm
  have hi := (hf.to_local_left_inverse hfne hleft).hasDerivAt
  have hfs : f s = κ := by dsimp [f]; rw [he, inv_inv]
  rw [hfs] at hi
  convert! hi using 1
  simp only [neg_inv, one_div, neg_div, s]

theorem speed_hasDerivAt {κ : ℝ} (hκ : 0 < κ) :
    HasDerivAt speed (lambda (criticalPoint κ) / criticalPoint κ) κ := by
  let s := criticalPoint κ
  have hs : 0 < s := criticalPoint_pos hκ
  have hsd : -1 < s := by linarith
  have hdd : HasDerivAt (deriv lambda) ((deriv^[2] lambda) s) s :=
    ((lambda_contDiffAt hsd 2).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasDerivAt
  have hd := (hasDerivAt_id κ).mul (hdd.comp κ (criticalPoint_hasDerivAt hκ))
  have he := criticalPoint_equation hκ
  have hc : (deriv^[2] lambda) s ≠ 0 := (lambda_deriv2_pos hsd).ne'
  convert! hd using 1
  dsimp [s, Function.comp_apply, id_eq] at hc ⊢
  have hsne : criticalPoint κ ≠ 0 := (criticalPoint_pos hκ).ne'
  field_simp [hκ.ne', hsne, hc]
  nlinarith [congrArg (fun r : ℝ => r * (deriv^[2] lambda) (criticalPoint κ)) he]

theorem speed_deriv_hasDerivAt {κ : ℝ} (hκ : 0 < κ) :
    HasDerivAt (deriv speed)
      (-1 / (κ ^ 3 * criticalPoint κ ^ 3 * (deriv^[2] lambda) (criticalPoint κ))) κ := by
  let s := criticalPoint κ
  have hs : 0 < s := criticalPoint_pos hκ
  have hsd : -1 < s := by linarith
  have hl : HasDerivAt lambda (deriv lambda s) s :=
    (lambda_hasDerivAt hsd).differentiableAt.hasDerivAt
  have hg := criticalPoint_hasDerivAt hκ
  have hd := (hl.comp κ hg).div hg hs.ne'
  have he := criticalPoint_equation hκ
  have hc : (deriv^[2] lambda) s ≠ 0 := (lambda_deriv2_pos hsd).ne'
  have hval : HasDerivAt (fun x => lambda (criticalPoint x) / criticalPoint x)
      (-1 / (κ ^ 3 * criticalPoint κ ^ 3 * (deriv^[2] lambda) (criticalPoint κ))) κ := by
    convert! hd using 1
    dsimp [s, Function.comp_apply] at hc ⊢
    have hsne : criticalPoint κ ≠ 0 := (criticalPoint_pos hκ).ne'
    field_simp [hκ.ne', hsne, hc]
    nlinarith [he]
  have hev : deriv speed =ᶠ[𝓝 κ] (fun x => lambda (criticalPoint x) / criticalPoint x) := by
    filter_upwards [Ioi_mem_nhds hκ] with x hx
    exact (speed_hasDerivAt hx).deriv
  exact hval.congr_of_eventuallyEq hev

#print axioms criticalPoint_hasDerivAt
#print axioms speed_hasDerivAt
#print axioms speed_deriv_hasDerivAt

end ConditionalSpectralExtremes
