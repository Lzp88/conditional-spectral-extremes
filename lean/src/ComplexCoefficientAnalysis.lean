import ProfileNormalization

/-!
Actual marker polynomial, its complex Gamma representation and pointwise Euler
asymptotic. Uniform compact-set error bounds are NOT supplied by pointwise convergence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Polynomial
open scoped Topology BigOperators

namespace ConditionalSpectralExtremes
namespace ComplexCoefficientAnalysis
open ConditionalSpectralAudit.CoefficientAlgebra

def markerPolynomial (n : ℕ) : Polynomial ℂ := (h n).map (algebraMap ℚ ℂ)
def markerValue (n : ℕ) (z : ℂ) : ℂ := (markerPolynomial n).eval z

theorem markerPolynomial_coefficient (n k : ℕ) :
    (markerPolynomial n).coeff k = (coefficient n k : ℂ) := by
  rw [ProfileNormalization.coefficient_eq_pochhammer]
  simp [markerPolynomial, a]

theorem markerPolynomial_eq_actual (n : ℕ) :
    markerPolynomial n = (ProfileNormalization.profilePolynomial n).map (algebraMap ℝ ℂ) := by
  rw [ProfileNormalization.profilePolynomial_eq_hReal]
  simp [markerPolynomial, ProfileNormalization.hReal, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq ℚ ℝ ℂ]

theorem markerValue_eq_asc (n : ℕ) (z : ℂ) :
    markerValue n z = (n.factorial : ℂ)⁻¹ * (ascPochhammer ℂ n).eval z := by
  simp [markerValue, markerPolynomial, h]

theorem asc_eval_prod (n : ℕ) (z : ℂ) :
    (ascPochhammer ℂ n).eval z = ∏ j ∈ Finset.range n, (z + j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_right, ih, Finset.prod_range_succ]

theorem markerValue_eq_prod (n : ℕ) (z : ℂ) :
    markerValue n z = (n.factorial : ℂ)⁻¹ * ∏ j ∈ Finset.range n, (z + j) := by
  rw [markerValue_eq_asc, asc_eval_prod]

theorem markerValue_Gamma (n : ℕ) {z : ℂ} (hz : ∀ j : ℕ, z ≠ -j) :
    markerValue n z = Complex.Gamma (z + n) / (Complex.Gamma z * (n.factorial : ℂ)) := by
  rw [markerValue_eq_asc, ← Complex.Gamma_add_nat_div_Gamma_eq z hz]
  ring

theorem markerValue_GammaSeq {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : ∀ j : ℕ, z ≠ -j) :
    (n : ℂ) ^ (1 - z) * markerValue n z =
      ((n : ℂ) / (n + z)) * (Complex.GammaSeq z n)⁻¹ := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hpow : (n : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn0)
  have hsum (j : ℕ) : z + j ≠ 0 := by
    intro h
    exact hz j (eq_neg_of_add_eq_zero_left h)
  have hp : (∏ j ∈ Finset.range n, (z + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun j _ => hsum j)
  have hlast : (n : ℂ) + z ≠ 0 := by simpa only [add_comm] using hsum n
  rw [Complex.cpow_sub 1 z hn0, Complex.cpow_one, markerValue_eq_prod,
    Complex.GammaSeq, Finset.prod_range_succ]
  field_simp
  ring

theorem markerValue_pointwise_asymptotic {z : ℂ} (hz : ∀ j : ℕ, z ≠ -j) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ (1 - z) * markerValue n z)
      atTop (𝓝 ((Complex.Gamma z)⁻¹)) := by
  have hh := (tendsto_natCast_div_add_atTop z).mul
    ((Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hz))
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (markerValue_GammaSeq hn hz).symm

#print axioms markerPolynomial_coefficient
#print axioms markerPolynomial_eq_actual
#print axioms markerValue_Gamma
#print axioms markerValue_pointwise_asymptotic

end ComplexCoefficientAnalysis
end ConditionalSpectralExtremes
