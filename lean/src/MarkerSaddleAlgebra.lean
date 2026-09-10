import AnalyticJet
import FallingFactorialSaddle

/-! Exact derivative identity for the marker saddle, before any asymptotic estimate. -/
noncomputable section
open scoped BigOperators
namespace ConditionalSpectralExtremes
open ReservoirAnalysis

theorem normalized_exp_marker_coefficient {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x) :
    ((j.factorial : ℂ) / (x : ℂ) ^ j) *
        analyticCoefficient (fun z => Complex.exp ((x : ℂ) * z) * g z) j =
      ∑ m ∈ Finset.range (j + 1),
        (analyticCoefficient g m * ((j : ℂ) / x) ^ m) * (fallingRatio j m : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hf0 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hgc : ContDiffAt ℂ j g 0 := (hg.analyticAt 0).contDiffAt
  have hec : ContDiffAt ℂ j (fun z : ℂ => Complex.exp ((x : ℂ) * z)) 0 := by fun_prop
  unfold analyticCoefficient
  rw [show (fun z : ℂ => Complex.exp ((x : ℂ) * z) * g z) =
      (fun z => g z * Complex.exp ((x : ℂ) * z)) by funext z; ring,
    iteratedDeriv_fun_mul hgc hec]
  simp only [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one]
  rw [show ∀ S : ℂ, (j.factorial : ℂ) / (x : ℂ) ^ j * (S / j.factorial) =
      S / (x : ℂ) ^ j by intro S; field_simp]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hmj : m ≤ j := by simp only [Finset.mem_range] at hm; omega
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  simp only [fallingRatio, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_pow,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, div_pow]
  rw [pow_sub₀ (x : ℂ) hx0 hmj]
  field_simp
  push_cast
  ring

#print axioms normalized_exp_marker_coefficient
end ConditionalSpectralExtremes
