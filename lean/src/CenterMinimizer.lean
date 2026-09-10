import LambdaAnalysis

/-! Existence and uniqueness for the manuscript's actual variational centre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology

namespace ConditionalSpectralExtremes

def variationalCost (L k s : ℝ) : ℝ := (L + k * lambda s) / s

theorem lambda_ratio_tendsto :
    Tendsto (fun s : ℝ => lambda s / s) atTop (𝓝 (Real.log 2)) := by
  have hl : Tendsto (fun s : ℝ => Real.log (1 + s) / s) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right, add_comm, id_eq] using! h
  have hc (c : ℝ) : Tendsto (fun s : ℝ => Real.log 2 - (1 / 2) *
      (Real.log (1 + s) / s) + c / s) atTop (𝓝 (Real.log 2)) := by
    have hconst : Tendsto (fun s : ℝ => c / s) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa only [mul_zero, sub_zero, add_zero] using!
      (tendsto_const_nhds.sub (hl.const_mul (1 / 2))).add hconst
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hc ((1 / 2) * Real.log 2 - (1 / 2) * Real.log Real.pi))
    (hc (Real.log 2 - (1 / 2) * Real.log Real.pi)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have h := (div_le_div_iff_of_pos_right hs).2 (lambda_log_bounds hs.le).1
    convert h using 1
    field_simp
    ring
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have h := (div_le_div_iff_of_pos_right hs).2 (lambda_log_bounds hs.le).2
    convert h using 1
    field_simp
    ring

theorem variationalCost_tendsto (L k : ℝ) :
    Tendsto (variationalCost L k) atTop (𝓝 (k * Real.log 2)) := by
  have hconst : Tendsto (fun s : ℝ => L / s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := hconst.add (lambda_ratio_tendsto.const_mul k)
  convert h using 1
  · ext s
    simp [variationalCost, add_div, mul_div_assoc]
  · simp

theorem variationalCost_nonneg {L k s : ℝ} (hL : 0 ≤ L) (hk : 0 ≤ k) (hs : 0 < s) :
    0 ≤ variationalCost L k s :=
  div_nonneg (add_nonneg hL (mul_nonneg hk (lambda_nonneg (by linarith)))) hs.le

theorem variationalCost_ge {L k s : ℝ} (hk : 0 ≤ k) (hs : 0 < s) :
    L / s ≤ variationalCost L k s := by
  apply (div_le_div_iff_of_pos_right hs).2
  linarith [mul_nonneg hk (lambda_nonneg (by linarith : -1 < s))]

theorem variationalCost_continuousOn (L k : ℝ) :
    ContinuousOn (variationalCost L k) (Ioi 0) := by
  intro s hs
  change 0 < s at hs
  have hl := (lambda_hasDerivAt (by linarith : -1 < s)).continuousAt
  exact ((continuousAt_const.add (continuousAt_const.mul hl)).div continuousAt_id
    (ne_of_gt hs)).continuousWithinAt

theorem variationalCost_exists_below_limit (L : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ t : ℝ, 0 < t ∧ variationalCost L k t < k * Real.log 2 := by
  have hlog : Tendsto (fun s : ℝ => Real.log (1 + s)) atTop atTop := by
    simpa only [Function.comp_def, add_comm, id_eq] using! Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  obtain ⟨t, ht, htl⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlog.eventually_gt_atTop (2 * (L / k + Real.log 2 - (1 / 2) * Real.log Real.pi)))).exists
  refine ⟨t, ht, ?_⟩
  unfold variationalCost
  apply (div_lt_iff₀ ht).2
  have hu := (lambda_log_bounds ht.le).2
  have hmul := mul_lt_mul_of_pos_left htl hk
  have hcancel : k * (L / k) = L := mul_div_cancel₀ L hk.ne'
  nlinarith [mul_le_mul_of_nonneg_left hu hk.le]

theorem variationalCost_exists_min {L k : ℝ} (hL : 0 < L) (hk : 0 < k) :
    ∃ s : ℝ, 0 < s ∧ IsMinOn (variationalCost L k) (Ioi 0) s := by
  let f := variationalCost L k
  obtain ⟨t, ht, htl⟩ := variationalCost_exists_below_limit L hk
  have hft : 0 ≤ f t := variationalCost_nonneg hL.le hk.le ht
  have hev : ∀ᶠ s : ℝ in atTop, f t < f s :=
    (variationalCost_tendsto L k).eventually (lt_mem_nhds htl)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  let δ := L / (f t + 1)
  have hden : 0 < f t + 1 := by linarith
  have hd : 0 < δ := div_pos hL hden
  have hdt : δ < t := by
    apply (div_lt_iff₀ hden).2
    have hh := (div_le_iff₀ ht).1 (variationalCost_ge (L := L) hk.le ht)
    change L ≤ f t * t at hh
    nlinarith
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc δ (max R t)).Nonempty from ⟨t, hdt.le, le_max_right R t⟩)
    ((variationalCost_continuousOn L k).mono (by intro x hx; exact lt_of_lt_of_le hd hx.1))
  refine ⟨s, lt_of_lt_of_le hd hs.1, ?_⟩
  intro x hx
  have hst : f s ≤ f t := hmin ⟨hdt.le, le_max_right R t⟩
  by_cases hxd : δ ≤ x
  · by_cases hxR : x ≤ max R t
    · exact hmin ⟨hxd, hxR⟩
    · exact hst.trans (hR x (le_trans (le_max_left R t) (le_of_not_ge hxR))).le
  · have hsmall : f t < L / x := by
      apply (lt_div_iff₀ hx).2
      have hh := (lt_div_iff₀ hden).1 (lt_of_not_ge hxd)
      change x * (f t + 1) < L at hh
      nlinarith
    exact hst.trans (hsmall.trans_le (variationalCost_ge hk.le hx)).le

theorem variationalCost_min_unique {L k s t : ℝ} (hk : 0 < k)
    (hs : 0 < s) (ht : 0 < t)
    (hsm : IsMinOn (variationalCost L k) (Ioi 0) s)
    (htm : IsMinOn (variationalCost L k) (Ioi 0) t) : s = t := by
  by_contra hne
  have he : variationalCost L k s = variationalCost L k t :=
    le_antisymm (hsm ht) (htm hs)
  have hm : 0 < (s + t) / 2 := by linarith
  have hmid := hsm hm
  have hcv := lambda_strictConvexOn.2 (show -1 < s by linarith)
    (show -1 < t by linarith) hne
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hcv
  have hmidpoint : (1 / 2 : ℝ) * s + 1 / 2 * t = (s + t) / 2 := by ring
  rw [hmidpoint] at hcv
  have es : variationalCost L k s * s = L + k * lambda s := div_mul_cancel₀ _ hs.ne'
  have et : variationalCost L k t * t = L + k * lambda t := div_mul_cancel₀ _ ht.ne'
  have em := (le_div_iff₀ hm).1 hmid
  rw [← he] at et
  have hstrict := mul_lt_mul_of_pos_left hcv hk
  nlinarith

theorem variationalCost_hasDerivAt (L k : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (variationalCost L k)
      ((k * deriv lambda s * s - (L + k * lambda s)) / s ^ 2) s := by
  have hd : HasDerivAt lambda (deriv lambda s) s :=
    (lambda_hasDerivAt (by linarith : -1 < s)).differentiableAt.hasDerivAt
  convert! ((hd.const_mul k).const_add L).div (hasDerivAt_id s) hs.ne' using 1
  simp

theorem variationalCost_min_critical {L k s : ℝ} (hs : 0 < s)
    (hmin : IsMinOn (variationalCost L k) (Ioi 0) s) :
    k * (s * deriv lambda s - lambda s) = L := by
  have hz := (hmin.isLocalMin (Ioi_mem_nhds hs)).hasDerivAt_eq_zero
    (variationalCost_hasDerivAt L k hs)
  have hnum : k * deriv lambda s * s - (L + k * lambda s) = 0 :=
    (div_eq_zero_iff).1 hz |>.resolve_right (pow_ne_zero 2 hs.ne')
  nlinarith

theorem lambda_tangent_lower {s t : ℝ} (hs : -1 < s) (ht : -1 < t) :
    lambda s + (t - s) * deriv lambda s ≤ lambda t := by
  have hd : HasDerivAt lambda (deriv lambda s) s :=
    (lambda_hasDerivAt hs).differentiableAt.hasDerivAt
  rcases lt_trichotomy s t with hlt | rfl | hgt
  · have h := lambda_strictConvexOn.convexOn.le_slope_of_hasDerivAt hs ht hlt hd
    rw [slope_def_field] at h
    have := (le_div_iff₀ (sub_pos.2 hlt)).1 h
    nlinarith
  · simp
  · have h := lambda_strictConvexOn.convexOn.slope_le_of_hasDerivAt ht hs hgt hd
    rw [slope_def_field] at h
    have := (div_le_iff₀ (sub_pos.2 hgt)).1 h
    nlinarith

theorem variationalCost_min_of_critical {L k s : ℝ} (hk : 0 ≤ k) (hs : 0 < s)
    (hcrit : k * (s * deriv lambda s - lambda s) = L) :
    IsMinOn (variationalCost L k) (Ioi 0) s := by
  intro t ht
  change 0 < t at ht
  have h := mul_le_mul_of_nonneg_left
    (lambda_tangent_lower (by linarith : -1 < s) (by linarith : -1 < t)) hk
  have he : variationalCost L k s = k * deriv lambda s := by
    apply (div_eq_iff hs.ne').2
    nlinarith
  rw [he]
  apply (le_div_iff₀ ht).2
  nlinarith

def criticalPoint (κ : ℝ) : ℝ :=
  if h : 0 < κ then (variationalCost_exists_min (by norm_num : (0 : ℝ) < 1) h).choose else 1

theorem criticalPoint_pos {κ : ℝ} (hκ : 0 < κ) : 0 < criticalPoint κ := by
  simp only [criticalPoint, dif_pos hκ]
  exact (variationalCost_exists_min (by norm_num : (0 : ℝ) < 1) hκ).choose_spec.1

theorem criticalPoint_isMin {κ : ℝ} (hκ : 0 < κ) :
    IsMinOn (variationalCost 1 κ) (Ioi 0) (criticalPoint κ) := by
  simp only [criticalPoint, dif_pos hκ]
  exact (variationalCost_exists_min (by norm_num : (0 : ℝ) < 1) hκ).choose_spec.2

theorem criticalPoint_equation {κ : ℝ} (hκ : 0 < κ) :
    κ * (criticalPoint κ * deriv lambda (criticalPoint κ) - lambda (criticalPoint κ)) = 1 :=
  variationalCost_min_critical (criticalPoint_pos hκ) (criticalPoint_isMin hκ)

theorem criticalPoint_unique {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s)
    (he : κ * (s * deriv lambda s - lambda s) = 1) : s = criticalPoint κ :=
  variationalCost_min_unique hκ hs (criticalPoint_pos hκ)
    (variationalCost_min_of_critical hκ.le hs he) (criticalPoint_isMin hκ)

def speed (κ : ℝ) : ℝ := κ * deriv lambda (criticalPoint κ)

theorem speed_eq_min_cost {κ : ℝ} (hκ : 0 < κ) :
    speed κ = variationalCost 1 κ (criticalPoint κ) := by
  have he := criticalPoint_equation hκ
  symm
  apply (div_eq_iff (criticalPoint_pos hκ).ne').2
  unfold speed
  nlinarith

theorem center_eq_speed {n k : ℕ} (hn : 1 < n) (hk : 0 < k) :
    center n k = Real.log n * speed ((k : ℝ) / Real.log n) := by
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hκ : 0 < (k : ℝ) / Real.log n := div_pos (by exact_mod_cast hk) hL
  let s := criticalPoint ((k : ℝ) / Real.log n)
  have hs : 0 < s := criticalPoint_pos hκ
  have hscale (t : ℝ) : variationalCost (Real.log n) k t =
      Real.log n * variationalCost 1 ((k : ℝ) / Real.log n) t := by
    unfold variationalCost
    field_simp
  have hmin : IsMinOn (variationalCost (Real.log n) k) (Ioi 0) s := by
    intro t ht
    change variationalCost (Real.log n) k s ≤ variationalCost (Real.log n) k t
    rw [hscale s, hscale t]
    exact mul_le_mul_of_nonneg_left (criticalPoint_isMin hκ ht) hL.le
  have he : center n k = variationalCost (Real.log n) k s := by
    apply IsLeast.csInf_eq
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    rintro r ⟨t, ht, rfl⟩
    exact hmin ht
  rw [he, hscale s, ← speed_eq_min_cost hκ]

#print axioms lambda_ratio_tendsto
#print axioms variationalCost_exists_min
#print axioms variationalCost_min_unique
#print axioms criticalPoint_equation
#print axioms criticalPoint_unique
#print axioms center_eq_speed

end ConditionalSpectralExtremes
