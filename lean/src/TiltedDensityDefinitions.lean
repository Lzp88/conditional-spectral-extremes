import TiltedLogSine

/-! Shared exact real-valued density representatives from manuscript (3.1).
Their identification with the actual Haar-pushforward probability measure
is proved separately in TiltedLogSineDensity. The value at log 2 is zero.
-/

noncomputable section
open MeasureTheory Set

namespace ConditionalSpectralExtremes

def logSineDensity (x : ℝ) : ℝ :=
  if x < Real.log 2 then
    Real.exp x / (Real.pi * Real.sqrt (1 - Real.exp (2 * x) / 4)) else 0

def tiltedDensity (β x : ℝ) : ℝ :=
  if x < Real.log 2 then
    Real.exp ((β + 1) * x - lambda β) /
      (Real.pi * Real.sqrt (1 - Real.exp (2 * x) / 4)) else 0

theorem logSineDensity_measurable : Measurable logSineDensity := by
  unfold logSineDensity
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem tiltedDensity_measurable (β : ℝ) : Measurable (tiltedDensity β) := by
  unfold tiltedDensity
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem logSineDensity_nonneg (x : ℝ) : 0 ≤ logSineDensity x := by
  unfold logSineDensity
  split_ifs <;> positivity

theorem tiltedDensity_nonneg (β x : ℝ) : 0 ≤ tiltedDensity β x := by
  unfold tiltedDensity
  split_ifs <;> positivity

theorem logSineDensity_sqrt_pos {x : ℝ} (hx : x < Real.log 2) :
    0 < Real.sqrt (1 - Real.exp (2 * x) / 4) := by
  apply Real.sqrt_pos.2
  have he : Real.exp x < 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_lt_exp.mpr hx
  have hpos := Real.exp_pos x
  rw [two_mul, Real.exp_add]
  nlinarith

theorem logSineDensity_pos {x : ℝ} (hx : x < Real.log 2) :
    0 < logSineDensity x := by
  simp only [logSineDensity, if_pos hx]
  exact div_pos (Real.exp_pos _) (mul_pos Real.pi_pos (logSineDensity_sqrt_pos hx))

theorem tiltedDensity_pos (β : ℝ) {x : ℝ} (hx : x < Real.log 2) :
    0 < tiltedDensity β x := by
  simp only [tiltedDensity, if_pos hx]
  exact div_pos (Real.exp_pos _) (mul_pos Real.pi_pos (logSineDensity_sqrt_pos hx))

theorem tiltedDensity_eq_weight (β x : ℝ) :
    tiltedDensity β x = Real.exp (β * x - lambda β) * logSineDensity x := by
  unfold tiltedDensity logSineDensity
  split_ifs with hx
  · rw [show (β + 1) * x - lambda β = (β * x - lambda β) + x by ring,
      Real.exp_add]
    ring
  · simp

#print axioms logSineDensity_measurable
#print axioms tiltedDensity_measurable
#print axioms logSineDensity_nonneg
#print axioms tiltedDensity_nonneg
#print axioms logSineDensity_sqrt_pos
#print axioms logSineDensity_pos
#print axioms tiltedDensity_pos
#print axioms tiltedDensity_eq_weight

end ConditionalSpectralExtremes
