import ActualCoefficientApproximation
import EntireMarkerSaddle
import PerturbedMarkerSaddle

/-! The reservoir's marker extraction step, conditional only on the separate circle estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes
open ReservoirAnalysis ComplexCoefficientAnalysis

theorem gamma_marker_saddle_with_circle_error {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (x : ℝ) (j : ℕ), 0 < x → 1 ≤ j →
      a ≤ (j : ℝ) / x → (j : ℝ) / x ≤ B →
      ∀ (N E F : ℝ), 0 < N → 0 ≤ E → 0 ≤ F →
      ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∀ z : ℂ, ‖z‖ = (j : ℝ) / x →
        ‖f z - (N : ℂ)⁻¹ * gammaMarker x z‖ ≤ E * Real.exp (x * z.re) + F) →
      ‖(((N * j.factorial / x ^ j : ℝ) : ℂ)) * analyticCoefficient f j -
        (Complex.Gamma (((j : ℝ) / x : ℝ) : ℂ))⁻¹‖ ≤
        Cg / x + N * E * Real.exp 1 * Real.sqrt (2 * j) + N * F := by
  have hg : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma
  obtain ⟨Cg, hCg, hgBound⟩ := entire_marker_saddle hg ha haB
  refine ⟨Cg, hCg, ?_⟩
  intro x j hx hj haj hjB N E F hN hE hF f hf herr
  have hjp : 0 < (j : ℝ) := by exact_mod_cast hj
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  let h : ℂ → ℂ := fun z => (N : ℂ)⁻¹ * gammaMarker x z
  have hh : Differentiable ℂ h := (gammaMarker_differentiable x).const_mul _
  have hcircle (θ : ℝ) :
      ‖f (circleMap 0 ((j : ℝ) / x) θ) - h (circleMap 0 ((j : ℝ) / x) θ)‖ ≤
        E * Real.exp j + F := by
    have hnorm : ‖circleMap 0 ((j : ℝ) / x) θ‖ = (j : ℝ) / x := by
      simp [norm_circleMap_zero, (div_pos hjp hx).le]
    apply (herr _ hnorm).trans
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ hE
    apply Real.exp_le_exp.mpr
    have hre := mul_le_mul_of_nonneg_left (Complex.re_le_norm (circleMap 0 ((j : ℝ) / x) θ)) hx.le
    rw [hnorm] at hre
    have hxe : x * ((j : ℝ) / x) = j := by field_simp
    rwa [hxe] at hre
  let Q : ℂ := ((N * j.factorial / x ^ j : ℝ) : ℂ)
  let A := ((j.factorial : ℂ) / (x : ℂ) ^ j) * analyticCoefficient (gammaMarker x) j
  have hcoeff : Q * analyticCoefficient h j = A := by
    rw [analyticCoefficient_const_mul ((gammaMarker_differentiable x).analyticAt 0)]
    simp only [Q, A, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow]
    field_simp
  have hp := normalized_marker_perturbation hf hh hN hx hE hF hj hcircle
  have hp' : ‖Q * analyticCoefficient f j - A‖ ≤
      N * E * Real.exp 1 * Real.sqrt (2 * j) + N * F := by
    change ‖Q * (analyticCoefficient f j - analyticCoefficient h j)‖ ≤ _ at hp
    rw [mul_sub, hcoeff] at hp
    exact hp
  have hs : ‖A - (Complex.Gamma (((j : ℝ) / x : ℝ) : ℂ))⁻¹‖ ≤ Cg / x :=
    hgBound x j hx hj haj hjB
  calc
    _ ≤ ‖Q * analyticCoefficient f j - A‖ +
        ‖A - (Complex.Gamma (((j : ℝ) / x : ℝ) : ℂ))⁻¹‖ := by
      simpa only [dist_eq_norm] using dist_triangle (Q * analyticCoefficient f j) A
        ((Complex.Gamma (((j : ℝ) / x : ℝ) : ℂ))⁻¹)
    _ ≤ (N * E * Real.exp 1 * Real.sqrt (2 * j) + N * F) + Cg / x := add_le_add hp' hs
    _ = _ := by ring

#print axioms gamma_marker_saddle_with_circle_error
end ConditionalSpectralExtremes
