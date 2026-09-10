import PolynomialInsertion

/-! Exact power identities for the actual unit-circle supremum norm. -/
noncomputable section
namespace ConditionalSpectralExtremes

theorem circleNorm_pow (p : Polynomial Complex) (q : Nat) :
    circleNorm (p^q)=(circleNorm p)^q := by
  apply le_antisymm
  · apply circleNorm_le
    intro z hz
    rw [Polynomial.eval_pow,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_le_circleNorm p z hz) q
  · obtain ⟨z,hz,he⟩ := circleNorm_attained p
    have hh := norm_eval_le_circleNorm (p^q) z hz
    simpa only [Polynomial.eval_pow,norm_pow,he] using hh

theorem log_circleNorm_pow (p : Polynomial Complex) (q : Nat) :
    Real.log (circleNorm (p^q))=(q : Real)*Real.log (circleNorm p) := by
  rw [circleNorm_pow,Real.log_pow]

#print axioms circleNorm_pow
#print axioms log_circleNorm_pow
end ConditionalSpectralExtremes
