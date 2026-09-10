import TiltedLocalCLT

/-! Uniform pointwise density upper bounds and center lower bounds for the
actual tilted sums, deduced from the proved local CLT. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace ConditionalSpectralExtremes

theorem gaussianLimitDensity_eq {β : ℝ} (hβ : -1 < β) (x : ℝ) :
    gaussianLimitDensity β x = (Real.sqrt (2*Real.pi*(deriv^[2] lambda) β))⁻¹ *
      Real.exp (-x^2/(2*(deriv^[2] lambda) β)) := by
  rw [gaussianLimitDensity, gaussianPDFReal, sub_zero, Real.coe_toNNReal _ (lambda_deriv2_pos hβ).le]

theorem gaussianLimitDensity_compact_bounds
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β ∈ Icc a b,
      c ≤ gaussianLimitDensity β 0 ∧ ∀ x, gaussianLimitDensity β x ≤ C := by
  obtain ⟨l, u, hl, hv⟩ := lambda_curvature_compact_bounds ha hab
  have hu : 0 < u := hl.trans_le ((hv a ⟨le_rfl, hab⟩).1.trans (hv a ⟨le_rfl, hab⟩).2)
  refine ⟨(Real.sqrt (2*Real.pi*u))⁻¹, (Real.sqrt (2*Real.pi*l))⁻¹, by positivity, by positivity, ?_⟩
  intro β hβ
  have hb := lt_of_lt_of_le ha hβ.1
  have hvp := lambda_deriv2_pos hb
  have hs : 0 < Real.sqrt (2*Real.pi*(deriv^[2] lambda) β) := by positivity
  constructor
  · rw [gaussianLimitDensity_eq hb]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div, Real.exp_zero, mul_one]
    simp only [← one_div]
    apply one_div_le_one_div_of_le hs
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (hv β hβ).2 (by positivity)
  · intro x
    rw [gaussianLimitDensity_eq hb]
    have he : Real.exp (-x^2/(2*(deriv^[2] lambda) β)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity))
    calc
      _ ≤ (Real.sqrt (2*Real.pi*(deriv^[2] lambda) β))⁻¹ :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hs.le)
      _ ≤ _ := by
        simp only [← one_div]
        apply one_div_le_one_div_of_le (by positivity)
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left (hv β hβ).1 (by positivity)

/-- The exact interface used by the pointwise bridge proof: a global density
upper bound and a center lower bound, with uniform constants and threshold. -/
theorem tiltedDensityPower_uniform_local_bounds
    (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ c0 C : ℝ, 0 < c0 ∧ 0 < C ∧ ∃ N : ℕ, 6 ≤ N ∧
      ∀ β ∈ Icc a b, ∀ q : ℕ, N ≤ q →
        (∀ x : ℝ, tiltedDensityPower β q x ≤ C/Real.sqrt q) ∧
          c0/Real.sqrt q ≤ tiltedDensityPower β q ((q : ℝ)*deriv lambda β) := by
  obtain ⟨c, B, hc, hB, hG⟩ := gaussianLimitDensity_compact_bounds a b ha hab
  obtain ⟨N, hN6, hN⟩ := tiltedDensityPower_uniform_local_CLT a b ha hab (c/2) (by positivity)
  refine ⟨c/2, B+c/2, by positivity, by positivity, N, hN6, ?_⟩
  intro β hβ q hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  constructor
  · intro x
    have hx := hN q hq β hβ ((x-(q : ℝ)*deriv lambda β)/Real.sqrt q)
    have he : (q : ℝ)*deriv lambda β + Real.sqrt q*((x-(q : ℝ)*deriv lambda β)/Real.sqrt q) = x := by
      field_simp
      ring
    rw [he] at hx
    have hb := (hG β hβ).2 ((x-(q : ℝ)*deriv lambda β)/Real.sqrt q)
    apply (le_div_iff₀ hs).mpr
    have hh := (abs_lt.mp hx).2
    nlinarith
  · have hx := hN q hq β hβ 0
    simp only [mul_zero, add_zero] at hx
    apply (div_le_iff₀ hs).mpr
    have hh := (abs_lt.mp hx).1
    have hb := (hG β hβ).1
    nlinarith

#print axioms gaussianLimitDensity_eq
#print axioms gaussianLimitDensity_compact_bounds
#print axioms tiltedDensityPower_uniform_local_bounds

end ConditionalSpectralExtremes
