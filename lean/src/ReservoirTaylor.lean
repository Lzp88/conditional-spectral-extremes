import ReservoirAnalytic
import AnalyticJet

/-! Actual Taylor truncations for the analytic reservoir, before the finite-profile bridge. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Topology
open Filter

namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ConditionalSpectralExtremes.Reservoir

def negativeLog (z : Complex) : Complex := -Complex.log (1 - z)

theorem negativeLog_analyticAt_zero : AnalyticAt Complex negativeLog 0 := by
  unfold negativeLog
  exact ((analyticAt_const.sub analyticAt_id).clog (by simp)).neg

theorem iteratedDeriv_negativeLog_succ (n : Nat) :
    iteratedDeriv (n + 1) negativeLog 0 = (n.factorial : Complex) := by
  unfold negativeLog
  rw [iteratedDeriv_fun_neg, iteratedDeriv_comp_const_sub]
  simp only [sub_zero, iteratedDeriv_succ_log Complex.one_mem_slitPlane, one_zpow,
    mul_one, smul_eq_mul]
  have hp : (-1 : Complex) ^ n * (-1 : Complex) ^ n = 1 := by rw [← mul_pow]; simp
  rw [pow_succ]
  linear_combination (n.factorial : Complex) * hp

theorem analyticCoefficient_negativeLog_zero : analyticCoefficient negativeLog 0 = 0 := by
  simp [analyticCoefficient, negativeLog]

theorem analyticCoefficient_negativeLog_succ (n : Nat) :
    analyticCoefficient negativeLog (n + 1) = 1 / ((n + 1 : Nat) : Complex) := by
  unfold analyticCoefficient
  rw [iteratedDeriv_negativeLog_succ, Nat.factorial_succ, Nat.cast_mul]
  field_simp [Nat.factorial_ne_zero]

theorem negativeLog_sameJet (n : Nat) : SameJet (n + 1) negativeLog (harmonicPolynomial n) := by
  have h := SameJet.taylor (n + 1) negativeLog_analyticAt_zero
  have heq : (fun z : Complex => ∑ i ∈ Finset.range (n + 1), analyticCoefficient negativeLog i * z ^ i) =
      harmonicPolynomial n := by
    funext z
    rw [Finset.sum_range_succ']
    simp only [analyticCoefficient_negativeLog_zero, zero_mul, add_zero]
    unfold harmonicPolynomial
    apply Finset.sum_congr rfl
    intro i hi
    rw [analyticCoefficient_negativeLog_succ]
    ring
  rw [heq] at h
  exact h

theorem reservoirKernel_sameJet_finite_exponential (n b : Nat) (u : Complex) :
    SameJet (n + 1) (fun z => reservoirKernel b z u)
      (fun z => Complex.exp (u * (harmonicPolynomial n z - harmonicPolynomial b z))) := by
  have hh := (negativeLog_sameJet n).add
    (SameJet.refl (n + 1) (harmonicPolynomial_analyticAt b 0).neg)
  have he := (hh.const_mul u).cexp
  convert! he using 1
  funext z
  simp only [reservoirKernel, negativeLog, Pi.neg_apply]
  congr 1
  ring

theorem exponential_sameJet_truncation (n : Nat) :
    SameJet (n + 1) Complex.exp
      (fun z => ∑ k ∈ Finset.range (n + 1), z ^ k / (k.factorial : Complex)) := by
  have hh := SameJet.taylor (n + 1) (show AnalyticAt Complex Complex.exp 0 by fun_prop)
  convert! hh using 1
  funext z
  apply Finset.sum_congr rfl
  intro k hk
  rw [analyticCoefficient_cexp]
  ring

theorem exponential_cycle_sameJet_truncation (n j : Nat) (hj : 0 < j) (u : Complex) :
    SameJet (n + 1) (fun z => Complex.exp (u * z ^ j / (j : Complex)))
      (fun z => ∑ k ∈ Finset.range (n + 1), (u * z ^ j / (j : Complex)) ^ k /
        (k.factorial : Complex)) := by
  exact (exponential_sameJet_truncation n).comp_of_zero (by fun_prop) (by simp [Nat.ne_of_gt hj])

def shortIndexEquivFin (n b : Nat) (hb : b ≤ n) : ShortIndex n b ≃ Fin b where
  toFun j := ⟨j.val.val, by have h := j.property; dsimp [IsShort] at h; omega⟩
  invFun j := ⟨⟨j.val, lt_of_lt_of_le j.isLt hb⟩, by dsimp [IsShort]; omega⟩
  left_inv j := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl

theorem harmonicPolynomial_eq_sum_fin (n : Nat) (z : Complex) :
    harmonicPolynomial n z = ∑ j : Fin n, z ^ (j.val + 1) / ((j.val + 1 : Nat) : Complex) := by
  exact (Fin.sum_univ_eq_sum_range (fun j : Nat => z ^ (j + 1) / ((j + 1 : Nat) : Complex)) n).symm

theorem harmonicPolynomial_sub_eq_long_sum (n b : Nat) (hb : b ≤ n) (z : Complex) :
    harmonicPolynomial n z - harmonicPolynomial b z =
      ∑ j : LongIndex n b, z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex) := by
  have hshort : (∑ j : ShortIndex n b, z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex)) =
      harmonicPolynomial b z := by
    rw [harmonicPolynomial_eq_sum_fin]
    exact Fintype.sum_equiv (shortIndexEquivFin n b hb) _ _ (fun j => rfl)
  have hsplit := Fintype.sum_subtype_add_sum_subtype (IsShort (n := n) b)
    (fun j : Fin n => z ^ (j.val + 1) / ((j.val + 1 : Nat) : Complex))
  rw [hshort, ← harmonicPolynomial_eq_sum_fin] at hsplit
  linear_combination -hsplit

theorem reservoirKernel_sameJet_cycle_product (n b : Nat) (hb : b ≤ n) (u : Complex) :
    SameJet (n + 1) (fun z => reservoirKernel b z u)
      (fun z => ∏ j : LongIndex n b,
        ∑ k ∈ Finset.range (n + 1),
          (u * z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex)) ^ k /
            (k.factorial : Complex)) := by
  have hprod := SameJet.prod (Finset.univ : Finset (LongIndex n b))
    (fun j _ => exponential_cycle_sameJet_truncation n (j.val.val + 1) (by omega) u)
  have heq : (fun z : Complex => Complex.exp (u * (harmonicPolynomial n z - harmonicPolynomial b z))) =
      (fun z => ∏ j : LongIndex n b, Complex.exp
        (u * z ^ (j.val.val + 1) / ((j.val.val + 1 : Nat) : Complex))) := by
    funext z
    rw [harmonicPolynomial_sub_eq_long_sum n b hb z, Finset.mul_sum, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    ring
  have hr := reservoirKernel_sameJet_finite_exponential n b u
  rw [heq] at hr
  exact hr.trans hprod

#print axioms negativeLog_sameJet
#print axioms reservoirKernel_sameJet_finite_exponential
#print axioms exponential_cycle_sameJet_truncation
#print axioms reservoirKernel_sameJet_cycle_product

end ConditionalSpectralExtremes.ReservoirAnalysis
