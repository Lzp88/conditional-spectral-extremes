import ReservoirLocalRadius

/-! Actual, uniformly bounded bank integrals, with the required power of N. -/
noncomputable section
open MeasureTheory
open scoped Real Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis

def laplaceMajorant (M : Real) : Real :=
  ∫ x : Real in Set.Ioi 1, x ^ (1 + M) * Real.exp (-x)

theorem laplace_majorant_integrable (M : Real) (hM : 0 ≤ M) :
    IntegrableOn (fun x : Real => x ^ (1 + M) * Real.exp (-x)) (Set.Ioi 1) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 1 + M) (p := 1) (b := 1) (by linarith) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, neg_mul, one_mul] at hi
  exact hi.mono_set (Set.Ioi_subset_Ioi (by norm_num))

theorem laplaceMajorant_nonneg (M : Real) : 0 ≤ laplaceMajorant M := by
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx] : 0 ≤ x) _) (Real.exp_pos _).le

theorem power_exponential_intervalIntegrable (a L : Real) (hL : 1 ≤ L) :
    IntervalIntegrable (fun x : Real => x ^ (1 - a) * Real.exp (-x)) volume 1 L := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hL] at hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  exact ((Real.differentiableAt_rpow_const_of_ne (1 - a) hx0).continuousAt.mul
    (by fun_prop)).continuousWithinAt

theorem uniform_laplace_integral (M a L : Real) (hM : 0 ≤ M) (ha : -M ≤ a) (hL : 1 ≤ L) :
    (∫ x : Real in 1..L, x ^ (1 - a) * Real.exp (-x)) ≤ laplaceMajorant M := by
  have hf := power_exponential_intervalIntegrable a L hL
  have hg := power_exponential_intervalIntegrable (-M) L hL
  have hh : (∫ x : Real in 1..L, x ^ (1 - a) * Real.exp (-x)) ≤
      ∫ x : Real in 1..L, x ^ (1 + M) * Real.exp (-x) := by
    apply intervalIntegral.integral_mono_on hL hf (by simpa using hg)
    intro x hx
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx.1 (by linarith)) (Real.exp_pos _).le
  refine hh.trans ?_
  rw [intervalIntegral.integral_of_le hL]
  exact MeasureTheory.setIntegral_mono_set (laplace_majorant_integrable M hM)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (by
      intro x hx
      exact mul_nonneg (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hx] : 0 ≤ x) _) (Real.exp_pos _).le))
    (Filter.Eventually.of_forall (by intro x hx; exact hx.1))

theorem scaled_laplace_integral (N a c : Real) (hN : 0 < N) (hc : N⁻¹ ≤ c) :
    (∫ x : Real in N⁻¹..c, x ^ (1 - a) * Real.exp (-N * x)) =
      N ^ (a - 2) * (∫ v : Real in 1..N * c, v ^ (1 - a) * Real.exp (-v)) := by
  have hp : N ^ (a - 1) * N ^ (1 - a) = 1 := by
    rw [← Real.rpow_add hN]
    simp
  have he : (∫ x : Real in N⁻¹..c, x ^ (1 - a) * Real.exp (-N * x)) =
      N ^ (a - 1) * (∫ x : Real in N⁻¹..c, (N * x) ^ (1 - a) * Real.exp (-(N * x))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    have hx0 : 0 ≤ x := (inv_pos.mpr hN).le.trans hx.1
    dsimp only
    rw [Real.mul_rpow hN.le hx0]
    calc
      _ = (N ^ (a - 1) * N ^ (1 - a)) * (x ^ (1 - a) * Real.exp (-(N * x))) := by rw [hp]; simp [neg_mul]
      _ = _ := by ring
  rw [he, intervalIntegral.integral_comp_mul_left (fun v : Real => v ^ (1 - a) * Real.exp (-v)) hN.ne', mul_inv_cancel₀ hN.ne']
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hN]
  congr 1
  ring

theorem uniform_scaled_laplace_integral (M N a c : Real) (hM : 0 ≤ M) (hN : 0 < N)
    (ha : -M ≤ a) (hc : N⁻¹ ≤ c) :
    (∫ x : Real in N⁻¹..c, x ^ (1 - a) * Real.exp (-N * x)) ≤
      N ^ (a - 2) * laplaceMajorant M := by
  rw [scaled_laplace_integral N a c hN hc]
  apply mul_le_mul_of_nonneg_left (uniform_laplace_integral M a (N * c) hM ha ?_)
    (Real.rpow_pos_of_pos hN _).le
  have hh := mul_le_mul_of_nonneg_left hc hN.le
  simpa only [mul_inv_cancel₀ hN.ne'] using hh

#print axioms uniform_scaled_laplace_integral
end ConditionalSpectralExtremes.ReservoirAnalysis
