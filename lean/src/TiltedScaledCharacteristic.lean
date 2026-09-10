import CharacteristicPowerApproximation

/-! The actual centered, square-root-scaled characteristic functions converge
to their variance-matched Gaussian functions uniformly in the tilt. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

def scaledCenteredCharFun (β : ℝ) (q : ℕ) (t : ℝ) : ℂ :=
  charFun (centeredTiltedLogSineLaw β) (t / Real.sqrt q)^q

def gaussianCharFun (β t : ℝ) : ℂ :=
  Real.exp (-(deriv^[2] lambda) β*t^2/2)

theorem complex_pow_gaussian_error_scaled {z : ℂ} {v M t : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hz : ‖z‖ ≤ 1) (hv : 0 ≤ v) (hvt : v*t^2 ≤ 2*n)
    (hrem : ‖z-(1-(v : ℂ)*((t / Real.sqrt n : ℝ) : ℂ)^2/2)‖ ≤
      M*|t / Real.sqrt n|^3) :
    ‖z^n-(Real.exp (-v*t^2/2) : ℂ)‖ ≤
      M*|t|^3/Real.sqrt n + v^2*t^4/(4*n) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnp
  have hsq : (n : ℝ) = (Real.sqrt n)^2 := (Real.sq_sqrt hnp.le).symm
  have hquot : v*(t/Real.sqrt n)^2/2 = v*t^2/(2*n) := by
    rw [div_pow, ← hsq]
    ring
  have hb : v*(t/Real.sqrt n)^2/2 ≤ 1 := by
    rw [hquot, div_le_one (by positivity)]
    exact hvt
  have hh := complex_pow_gaussian_error hz hv hb hrem n
  have hexp : -(n : ℝ)*v*(t/Real.sqrt n)^2/2 = -v*t^2/2 := by
    rw [div_pow, ← hsq]
    field_simp
  rw [hexp] at hh
  convert hh using 1
  rw [abs_div, abs_of_pos hs, hsq]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hs]
  field_simp

theorem scaledCenteredCharFun_uniform_bound
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ M u : ℝ, 0 ≤ M ∧ 0 < u ∧ ∀ β ∈ Icc a b, ∀ n : ℕ, 1 ≤ n →
      ∀ t : ℝ, u*t^2 ≤ 2*n →
      ‖scaledCenteredCharFun β n t-gaussianCharFun β t‖ ≤
        M*|t|^3/Real.sqrt n + u^2*t^4/(4*n) := by
  obtain ⟨M, hM, hm⟩ := centeredTiltedLogSineLaw_uniform_quadratic_remainder a b ha hab
  obtain ⟨l, u, hl, hv⟩ := lambda_curvature_compact_bounds ha hab
  have hu : 0 < u := hl.trans_le ((hv a ⟨le_rfl, hab⟩).1.trans (hv a ⟨le_rfl, hab⟩).2)
  refine ⟨M, u, hM, hu, ?_⟩
  intro β hβ n hn t ht
  have hb := lt_of_lt_of_le ha hβ.1
  let := centeredTiltedLogSineLaw_probability hb
  have hh := complex_pow_gaussian_error_scaled hn
    (norm_charFun_le_one (t/Real.sqrt n)) (lambda_deriv2_pos hb).le
    ((mul_le_mul_of_nonneg_right (hv β hβ).2 (sq_nonneg t)).trans ht)
    (hm β hβ (t/Real.sqrt n))
  apply hh.trans
  gcongr
  · exact (lambda_deriv2_pos hb).le
  exact (hv β hβ).2

/-- Product-filter formulation of uniformity in beta: every fixed Fourier
argument has an error tending to zero simultaneously for all admissible tilts. -/
theorem scaledCenteredCharFun_uniform_pointwise
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) (t : ℝ) :
    Tendsto (fun p : ℕ × ℝ => ‖scaledCenteredCharFun p.2 p.1 t-gaussianCharFun p.2 t‖)
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
  obtain ⟨M, u, hM, hu, hb⟩ := scaledCenteredCharFun_uniform_bound a b ha hab
  have htend : Tendsto (fun n : ℕ => M*|t|^3/Real.sqrt n + u^2*t^4/(4*n)) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop (M*|t|^3)
    have h2 := tendsto_const_div_atTop_nhds_zero_nat (u^2*t^4/4)
    convert h1.add h2 using 1
    · ext n
      dsimp only [Function.comp_apply]
      ring
    · simp
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Filter.Eventually.of_forall (fun p => hε.trans_le (norm_nonneg _))
  · intro ε hε
    rw [eventually_prod_principal_iff]
    have hn : ∀ᶠ n : ℕ in atTop, (u*t^2 : ℝ) ≤ n :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (u*t^2))
    filter_upwards [hn, eventually_ge_atTop 1, htend.eventually (eventually_lt_nhds hε)] with n hn hn1 he
    intro β hβ
    exact (hb β hβ n hn1 t (by nlinarith [Nat.cast_nonneg (α := ℝ) n])).trans_lt he

#print axioms complex_pow_gaussian_error_scaled
#print axioms scaledCenteredCharFun_uniform_bound
#print axioms scaledCenteredCharFun_uniform_pointwise

end ConditionalSpectralExtremes
