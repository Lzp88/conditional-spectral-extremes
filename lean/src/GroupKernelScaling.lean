import Mathlib

/-! Quantitative conversion of the actual q-step bridge estimate to the
coarse spatial scale H. Constants are explicit, including the required
small drift per increment. -/

noncomputable section
namespace ConditionalSpectralExtremes

theorem group_mean_deviation_small (q H α D U δ d μ : ℝ)
    (hq : 0 < q) (hH : 0 < H) (_hα : 0 < α) (hδ : 0 ≤ δ)
    (hcount : α*H ≤ q) (hdrift : |d-q*μ| ≤ D*Real.sqrt H*U)
    (hsmall : D*U ≤ δ*α*Real.sqrt H) :
    |d/q-μ| ≤ δ := by
  have hsq : (Real.sqrt H)^2 = H := Real.sq_sqrt hH.le
  have hdis : |d-q*μ| ≤ δ*q := by
    have hh := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg H)
    have hhq := mul_le_mul_of_nonneg_left hcount hδ
    have heq : δ*α*Real.sqrt H*Real.sqrt H = δ*(α*H) := by
      calc
        _ = δ*α*(Real.sqrt H)^2 := by ring
        _ = _ := by rw [hsq]; ring
    rw [heq] at hh
    calc
      _ ≤ D*Real.sqrt H*U := hdrift
      _ = D*U*Real.sqrt H := by ring
      _ ≤ δ*(α*H) := hh
      _ ≤ δ*q := hhq
  have hid : d/q-μ = (d-q*μ)/q := by field_simp
  rw [hid, abs_div, abs_of_pos hq]
  exact (div_le_iff₀ hq).2 hdis

theorem group_deviation_energy_bound (q H α D U d μ : ℝ)
    (hq : 0 < q) (hH : 0 < H) (hα : 0 < α) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hcount : α*H ≤ q) (hdrift : |d-q*μ| ≤ D*Real.sqrt H*U) :
    (d-q*μ)^2/q ≤ (D^2/α)*U^2 := by
  have hs : 0 ≤ D*Real.sqrt H*U := by positivity
  have hsq := (sq_le_sq₀ (abs_nonneg (d-q*μ)) hs).2 hdrift
  rw [sq_abs] at hsq
  have heq : (D*Real.sqrt H*U)^2 = D^2*H*U^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hH.le]
  rw [heq] at hsq
  apply (div_le_iff₀ hq).2
  have hc := mul_le_mul_of_nonneg_right hcount (div_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg U)) hα.le)
  have heq₁ : α*H*(D^2*U^2/α) = D^2*H*U^2 := by field_simp
  have heq₂ : q*(D^2*U^2/α) = (D^2/α)*U^2*q := by ring
  rw [heq₁, heq₂] at hc
  exact hsq.trans hc

theorem group_density_prefactor (q H A c : ℝ)
    (hq : 0 < q) (_hH : 0 < H) (hA : 0 < A) (hc : 0 ≤ c)
    (hcount : q ≤ A*H) :
    (c/Real.sqrt A)/Real.sqrt H ≤ c/Real.sqrt q := by
  rw [div_div]
  apply div_le_div_of_nonneg_left hc (Real.sqrt_pos.mpr hq)
  rw [← Real.sqrt_mul hA.le]
  exact Real.sqrt_le_sqrt hcount

theorem group_gaussian_kernel_scaling (q H α A D U c K d μ : ℝ)
    (hq : 0 < q) (hH : 0 < H) (hα : 0 < α) (hA : 0 < A)
    (hD : 0 ≤ D) (hU : 0 ≤ U) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hcount₁ : α*H ≤ q) (hcount₂ : q ≤ A*H)
    (hdrift : |d-q*μ| ≤ D*Real.sqrt H*U) :
    (c/Real.sqrt A)/Real.sqrt H * Real.exp (-(K*D^2/α)*U^2) ≤
      c/Real.sqrt q * Real.exp (-K*(d-q*μ)^2/q) := by
  have hpref := group_density_prefactor q H A c hq hH hA hc hcount₂
  have henergy := group_deviation_energy_bound q H α D U d μ hq hH hα hD hU hcount₁ hdrift
  have hexp : Real.exp (-(K*D^2/α)*U^2) ≤ Real.exp (-K*(d-q*μ)^2/q) := by
    apply Real.exp_le_exp.mpr
    have hh := neg_le_neg (mul_le_mul_of_nonneg_left henergy hK)
    have heq₁ : -(K*((D^2/α)*U^2)) = -(K*D^2/α)*U^2 := by ring
    have heq₂ : -(K*((d-q*μ)^2/q)) = -K*(d-q*μ)^2/q := by ring
    rw [heq₁, heq₂] at hh
    exact hh
  exact mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity)

#print axioms group_mean_deviation_small
#print axioms group_deviation_energy_bound
#print axioms group_density_prefactor
#print axioms group_gaussian_kernel_scaling

end ConditionalSpectralExtremes
