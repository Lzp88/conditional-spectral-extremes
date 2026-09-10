import ReservoirTaylor

/-! Bridge between actual analytic Taylor coefficients and finite long-cycle profiles. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology

namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ConditionalSpectralExtremes.Reservoir

theorem analyticCoefficient_polynomial_eval (p : Polynomial Complex) (N : Nat) :
    analyticCoefficient (fun z => p.eval z) N = p.coeff N := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
      unfold analyticCoefficient at *
      simp only [Polynomial.eval_add, Polynomial.coeff_add]
      have hp : ContDiffAt Complex N (fun z => p.eval z) 0 := by
        simpa [Polynomial.aeval_def] using! (p.contDiff_aeval N).contDiffAt
      have hq : ContDiffAt Complex N (fun z => q.eval z) 0 := by
        simpa [Polynomial.aeval_def] using! (q.contDiff_aeval N).contDiffAt
      rw [iteratedDeriv_fun_add hp hq, add_div, ihp, ihq]
  | monomial n a =>
      unfold analyticCoefficient
      simp only [Polynomial.eval_monomial]
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      by_cases h : N = n
      · subst N
        simp [Nat.factorial_ne_zero]
      · simp [Polynomial.coeff_monomial, h, Ne.symm h]

def reservoirScalarPolynomial (n b : Nat) (u : Complex) : Polynomial Complex :=
  (reservoirPolynomial n b).map (Polynomial.eval₂RingHom Complex.ofRealHom u)

theorem longCount_le_longMass {n b : Nat} (c : LongConfiguration n b) :
    longCount c ≤ longMass c := by
  unfold longCount longMass
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

theorem reservoirCoefficient_eq_zero_of_count_gt_size (n b N l : Nat) (hNl : N < l) :
    reservoirCoefficient n b N l = 0 := by
  unfold reservoirCoefficient
  apply Finset.sum_eq_zero
  intro c hc
  have hh := longCount_le_longMass c
  split_ifs with h
  · omega
  · rfl

theorem reservoirPolynomial_inner_natDegree_le (n b N : Nat) (hN : N ≤ n) :
    ((reservoirPolynomial n b).coeff N).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.2
  intro l hl
  rw [reservoirPolynomial_coeff]
  exact reservoirCoefficient_eq_zero_of_count_gt_size n b N l (by omega)

theorem reservoirScalarPolynomial_coeff (n b N : Nat) (hN : N ≤ n) (u : Complex) :
    (reservoirScalarPolynomial n b u).coeff N = finiteReservoirMarker n b N u := by
  unfold reservoirScalarPolynomial
  rw [Polynomial.coeff_map]
  change Polynomial.eval₂ Complex.ofRealHom u ((reservoirPolynomial n b).coeff N) = _
  rw [Polynomial.eval₂_eq_sum_range' Complex.ofRealHom
    (Nat.lt_succ_of_le (reservoirPolynomial_inner_natDegree_le n b N hN)) u]
  simp only [reservoirPolynomial_coeff, finiteReservoirMarker]
  rfl

theorem reservoirScalarPolynomial_eval (n b : Nat) (z u : Complex) :
    (reservoirScalarPolynomial n b u).eval z =
      ∏ j : LongIndex n b, ∑ k ∈ Finset.range (n + 1),
        (u * z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex)) ^ k /
          (k.factorial : Complex) := by
  unfold reservoirScalarPolynomial
  rw [reservoirPolynomial_product, Polynomial.map_prod, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
  simp only [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_monomial, Complex.ofRealHom_eq_coe]
  rw [← Fin.sum_univ_eq_sum_range (fun k : Nat =>
    (u * z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex)) ^ k /
      (k.factorial : Complex)) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  simp only [mul_pow, div_pow, pow_mul]
  ring

theorem reservoirKernel_sameJet_reservoirScalarPolynomial (n b : Nat) (hb : b ≤ n) (u : Complex) :
    SameJet (n + 1) (fun z => reservoirKernel b z u)
      (fun z => (reservoirScalarPolynomial n b u).eval z) := by
  have he : (fun z => (reservoirScalarPolynomial n b u).eval z) =
      (fun z => ∏ j : LongIndex n b, ∑ k ∈ Finset.range (n + 1),
        (u * z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex)) ^ k /
          (k.factorial : Complex)) := funext fun z => reservoirScalarPolynomial_eval n b z u
  rw [he]
  exact reservoirKernel_sameJet_cycle_product n b hb u

theorem reservoirAnalyticCoefficient_eq_finite (n b N : Nat) (hb : b ≤ n) (hN : N ≤ n)
    (u : Complex) : reservoirAnalyticCoefficient b N u = finiteReservoirMarker n b N u := by
  unfold reservoirAnalyticCoefficient
  rw [(reservoirKernel_sameJet_reservoirScalarPolynomial n b hb u).analyticCoefficient_eq N
    (Nat.lt_succ_of_le hN), analyticCoefficient_polynomial_eval,
    reservoirScalarPolynomial_coeff n b N hN u]

theorem reservoirAnalyticCoefficient_eq_inner_eval (n b N : Nat) (hb : b ≤ n) (hN : N ≤ n)
    (u : Complex) : reservoirAnalyticCoefficient b N u =
      (((reservoirPolynomial n b).coeff N).map Complex.ofRealHom).eval u := by
  rw [reservoirAnalyticCoefficient_eq_finite n b N hb hN u,
    ← reservoirScalarPolynomial_coeff n b N hN u]
  simp only [reservoirScalarPolynomial, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom,
    Polynomial.eval_map]

/-- The actual two-variable analytic coefficient equals the exact long-cycle profile sum. -/
theorem actual_bivariate_reservoir_coefficient (n b N l : Nat) (hb : b ≤ n) (hN : N ≤ n) :
    analyticCoefficient (fun u => reservoirAnalyticCoefficient b N u) l =
      (reservoirCoefficient n b N l : Complex) := by
  have he : (fun u => reservoirAnalyticCoefficient b N u) =
      (fun u => (((reservoirPolynomial n b).coeff N).map Complex.ofRealHom).eval u) :=
    funext fun u => reservoirAnalyticCoefficient_eq_inner_eval n b N hb hN u
  rw [he, analyticCoefficient_polynomial_eval]
  simp only [Polynomial.coeff_map, reservoirPolynomial_coeff, Complex.ofRealHom_eq_coe]

theorem reservoirCoefficient_ambient_invariant (n₁ n₂ b N l : Nat)
    (hb₁ : b ≤ n₁) (hN₁ : N ≤ n₁) (hb₂ : b ≤ n₂) (hN₂ : N ≤ n₂) :
    reservoirCoefficient n₁ b N l = reservoirCoefficient n₂ b N l := by
  apply Complex.ofReal_injective
  rw [← actual_bivariate_reservoir_coefficient n₁ b N l hb₁ hN₁,
    ← actual_bivariate_reservoir_coefficient n₂ b N l hb₂ hN₂]

#print axioms analyticCoefficient_polynomial_eval
#print axioms reservoirScalarPolynomial_coeff
#print axioms reservoirScalarPolynomial_eval
#print axioms reservoirAnalyticCoefficient_eq_finite
#print axioms actual_bivariate_reservoir_coefficient
#print axioms reservoirCoefficient_ambient_invariant

end ConditionalSpectralExtremes.ReservoirAnalysis
