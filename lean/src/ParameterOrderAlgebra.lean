import Mathlib

/-! Explicit acyclic late choices in the manuscript. The accuracy J
depends only on Cstar. After A0 and the smoothing exponents are fixed,
the gap is chosen; the reservoir constant is chosen last and can exceed
any independently proved additional lower threshold. -/
noncomputable section
namespace ConditionalSpectralAudit.FourierHarmonic

def manuscriptPrecision (Cstar : ℝ) : ℝ := 2*Cstar+13

def manuscriptGap (smin A₀ u₂ u₃ Cstar : ℝ) : ℝ :=
  (|2*u₂+u₃+A₀+2*Cstar+12| + 1)/smin

def manuscriptReservoir (smax g A₀ u₂ u₃ rmin : ℝ) : ℝ :=
  |64*smax*g+1| + |2*u₂+u₃+A₀+12| + |rmin| + 1

theorem manuscriptPrecision_bounds (Cstar : ℝ) (hC : 0 ≤ Cstar) :
    1 ≤ manuscriptPrecision Cstar ∧ 2*Cstar+12 < manuscriptPrecision Cstar ∧
      1+2*Cstar-manuscriptPrecision Cstar = -12 := by
  unfold manuscriptPrecision
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem manuscriptGap_bounds (smin A₀ u₂ u₃ Cstar : ℝ) (hsmin : 0 < smin) :
    0 < manuscriptGap smin A₀ u₂ u₃ Cstar ∧
      2*u₂+u₃+A₀+2*Cstar+12 < smin*manuscriptGap smin A₀ u₂ u₃ Cstar ∧
      1+2*u₂+u₃+A₀-smin*manuscriptGap smin A₀ u₂ u₃ Cstar+2*Cstar < -11 := by
  unfold manuscriptGap
  have he : smin*((|2*u₂+u₃+A₀+2*Cstar+12| + 1)/smin) =
      |2*u₂+u₃+A₀+2*Cstar+12| + 1 := by field_simp
  rw [he]
  have hh := le_abs_self (2*u₂+u₃+A₀+2*Cstar+12)
  refine ⟨div_pos (by positivity) hsmin, ?_, ?_⟩ <;> linarith

theorem manuscriptReservoir_bounds (smax g A₀ u₂ u₃ rmin : ℝ) :
    0 < manuscriptReservoir smax g A₀ u₂ u₃ rmin ∧
      64*smax*g+1 < manuscriptReservoir smax g A₀ u₂ u₃ rmin ∧
      2*u₂+u₃+A₀+12 < manuscriptReservoir smax g A₀ u₂ u₃ rmin ∧
      rmin < manuscriptReservoir smax g A₀ u₂ u₃ rmin := by
  unfold manuscriptReservoir
  have h1 := le_abs_self (64*smax*g+1)
  have h2 := le_abs_self (2*u₂+u₃+A₀+12)
  have h3 := le_abs_self rmin
  have hn1 := abs_nonneg (64*smax*g+1)
  have hn2 := abs_nonneg (2*u₂+u₃+A₀+12)
  have hn3 := abs_nonneg rmin
  constructor
  · positivity
  exact ⟨by linarith, by linarith, by linarith⟩

#print axioms manuscriptPrecision_bounds
#print axioms manuscriptGap_bounds
#print axioms manuscriptReservoir_bounds
end ConditionalSpectralAudit.FourierHarmonic
