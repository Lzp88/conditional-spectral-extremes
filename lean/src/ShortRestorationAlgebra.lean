import LambdaMomentUpper

/-! Exact low/middle center bookkeeping, with a fixed logarithmic error constant. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem restored_short_height_bound (smin s a ell₀ rStar K C₂ Cmid noise Q q₀ Mmid Mfull : Real)
    (hsmin : 0 < smin) (hss : smin ≤ s) (hell : 0 ≤ ell₀) (hr : 0 ≤ rStar)
    (_hK : 0 ≤ K) (hC₂ : 0 ≤ C₂) (hCmid : 0 ≤ Cmid) (hq₀ : 0 ≤ q₀)
    (hq : q₀ ≤ K*rStar*ell₀) (hnoise : noise ≤ ell₀)
    (hmid : Mmid ≤ (a+lambda s*Q)/s+Cmid*ell₀)
    (hupper : Mfull ≤ Mmid+q₀*Real.log 2)
    (hlower : (a-rStar*ell₀+lambda s*Q)/s-noise-C₂*rStar*ell₀ ≤ Mfull) :
    |Mfull-(a+lambda s*(Q+q₀))/s| ≤
      (Cmid+(1/smin+K*Real.log 2+C₂)*rStar+1)*ell₀ := by
  have hs : 0 < s := hsmin.trans_le hss
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlam : 0 ≤ lambda s := lambda_nonneg (by linarith)
  have hlams : 0 ≤ lambda s/s := div_nonneg hlam hs.le
  have hlamupper : lambda s/s ≤ Real.log 2 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [lambda_le_s_log_two s hs.le]
  have hqlog : q₀*Real.log 2 ≤ K*rStar*ell₀*Real.log 2 :=
    mul_le_mul_of_nonneg_right hq hlog
  have hqlam : q₀*(lambda s/s) ≤ K*rStar*ell₀*Real.log 2 :=
    (mul_le_mul_of_nonneg_left hlamupper hq₀).trans hqlog
  have hrdiv : rStar*ell₀/s ≤ rStar*ell₀/smin :=
    div_le_div_of_nonneg_left (mul_nonneg hr hell) hsmin hss
  rw [show rStar*ell₀/smin=(1/smin)*rStar*ell₀ by ring] at hrdiv
  have hcenter : (a+lambda s*(Q+q₀))/s = (a+lambda s*Q)/s+q₀*(lambda s/s) := by
    field_simp
    ring
  have hlowercenter : (a+lambda s*(Q+q₀))/s =
      (a-rStar*ell₀+lambda s*Q)/s+rStar*ell₀/s+q₀*(lambda s/s) := by
    field_simp
    ring
  have hnonneg1 : 0 ≤ Cmid*ell₀ := mul_nonneg hCmid hell
  have hnonneg2 : 0 ≤ (1/smin+C₂)*rStar*ell₀ := by positivity
  apply abs_le.mpr
  constructor
  · rw [hlowercenter]
    nlinarith
  · rw [hcenter]
    have hqlam0 := mul_nonneg hq₀ hlams
    nlinarith

#print axioms restored_short_height_bound
end ConditionalSpectralExtremes
