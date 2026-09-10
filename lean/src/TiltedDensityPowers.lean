import TripleDensityParameter

/-! Actual positive-order convolution densities. Order zero is assigned the
zero function solely for a total definition; it is not the density of a point mass. -/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution

namespace ConditionalSpectralExtremes

def tiltedDensityPower (β : ℝ) : ℕ → ℝ → ℝ
  | 0 => 0
  | 1 => tiltedDensity β
  | n + 2 => tiltedDensityPower β (n + 1) ⋆[ContinuousLinearMap.mul ℝ ℝ] tiltedDensity β

@[simp] theorem tiltedDensityPower_zero (β : ℝ) : tiltedDensityPower β 0 = 0 := rfl
@[simp] theorem tiltedDensityPower_one (β : ℝ) : tiltedDensityPower β 1 = tiltedDensity β := rfl
@[simp] theorem tiltedDensityPower_two (β : ℝ) : tiltedDensityPower β 2 = tiltedDensityDouble β := rfl
@[simp] theorem tiltedDensityPower_three (β : ℝ) : tiltedDensityPower β 3 = tiltedDensityTriple β := rfl

theorem tiltedDensityPower_succ (β : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    tiltedDensityPower β (q + 1) =
      tiltedDensityPower β q ⋆[ContinuousLinearMap.mul ℝ ℝ] tiltedDensity β := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  rfl

theorem tiltedDensityPower_nonneg (β : ℝ) (q : ℕ) (x : ℝ) :
    0 ≤ tiltedDensityPower β q x := by
  induction q using Nat.twoStepInduction generalizing x with
  | zero => exact le_rfl
  | one => exact tiltedDensity_nonneg β x
  | more n _ ih =>
    change 0 ≤ ∫ y, tiltedDensityPower β (n + 1) y * tiltedDensity β (x - y)
    exact integral_nonneg (fun y => mul_nonneg (ih y)
      (tiltedDensity_nonneg β (x - y)))

theorem tiltedDensityPower_integrable {β : ℝ} (hβ : -1 < β) (q : ℕ) :
    Integrable (tiltedDensityPower β q) := by
  induction q using Nat.twoStepInduction with
  | zero => exact integrable_zero _ _ _
  | one => exact tiltedDensity_integrable β hβ
  | more n _ ih =>
    exact ih.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ)
      (tiltedDensity_integrable β hβ)

theorem tiltedDensityPower_integral {β : ℝ} (hβ : -1 < β) (q : ℕ) (hq : 1 ≤ q) :
    ∫ x, tiltedDensityPower β q x = 1 := by
  induction q using Nat.twoStepInduction with
  | zero => omega
  | one => exact tiltedDensity_integral β hβ
  | more n _ ih =>
    rw [tiltedDensityPower_succ β (n + 1) (by omega), integral_convolution _
      (tiltedDensityPower_integrable hβ (n + 1)) (tiltedDensity_integrable β hβ)]
    simp [ih (by omega), tiltedDensity_integral β hβ]

#print axioms tiltedDensityPower_zero
#print axioms tiltedDensityPower_one
#print axioms tiltedDensityPower_two
#print axioms tiltedDensityPower_three
#print axioms tiltedDensityPower_succ
#print axioms tiltedDensityPower_nonneg
#print axioms tiltedDensityPower_integrable
#print axioms tiltedDensityPower_integral

end ConditionalSpectralExtremes
