import FineScaleAsymptotics

/-! Identification of the exponential cost with the manuscript's exact
power of the actual logarithmic scale L. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open ReservoirScale

theorem exp_neg_ell_eq_L_rpow (n : ℕ) (C : ℝ) (hL : 0 < L n) :
    Real.exp (-C*ell n) = (L n)^(-C) := by
  rw [Real.rpow_def_of_pos hL]
  congr 1
  unfold ell
  ring

#print axioms exp_neg_ell_eq_L_rpow

end ConditionalSpectralExtremes.CoarseBoxes
