import FiniteArcIntegration

noncomputable section
open scoped BigOperators
namespace ConditionalSpectralAudit

theorem geometric_sum_le_two (x : Real) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) (m : Nat) :
    (∑ i ∈ Finset.range m, x^i) ≤ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    have hh := mul_le_mul_of_nonneg_left ih hx
    nlinarith

theorem arithmetic_weighted_sum (R r Δ ρ ω : Real) (m : Nat)
    (hR : 0 ≤ R) (hgeom : Real.exp (-(1-ρ)*ω) ≤ 1/2) :
    (∑ i ∈ Finset.range m, Real.exp (((i+1 : Nat) : Real)*(ρ*ω))*
      (6*R*Real.exp (-(r+(i : Real)*ω)+Δ))) ≤
      12*R*Real.exp (-r+Δ+ρ*ω) := by
  have he (i : Nat) : Real.exp (((i+1 : Nat) : Real)*(ρ*ω))*
      (6*R*Real.exp (-(r+(i : Real)*ω)+Δ)) =
      (6*R*Real.exp (-r+Δ+ρ*ω))*Real.exp (-(1-ρ)*ω)^i := by
    rw [← Real.exp_nat_mul]
    have hargs : (((i+1 : Nat) : Real)*(ρ*ω))+(-(r+(i : Real)*ω)+Δ) =
        (-r+Δ+ρ*ω)+(i : Real)*(-(1-ρ)*ω) := by
      push_cast
      ring
    calc
      _ = (6*R)*(Real.exp (((i+1 : Nat) : Real)*(ρ*ω))*
          Real.exp (-(r+(i : Real)*ω)+Δ)) := by ring
      _ = (6*R)*Real.exp ((((i+1 : Nat) : Real)*(ρ*ω))+(-(r+(i : Real)*ω)+Δ)) := by
        rw [← Real.exp_add]
      _ = (6*R)*Real.exp ((-r+Δ+ρ*ω)+(i : Real)*(-(1-ρ)*ω)) := by rw [hargs]
      _ = _ := by
        rw [Real.exp_add (-r+Δ+ρ*ω) ((i : Real)*(-(1-ρ)*ω))]
        ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (geometric_sum_le_two (Real.exp (-(1-ρ)*ω)) (Real.exp_pos _).le hgeom m)
    (by positivity : 0 ≤ 6*R*Real.exp (-r+Δ+ρ*ω))
  nlinarith

#print axioms arithmetic_weighted_sum
end ConditionalSpectralAudit
