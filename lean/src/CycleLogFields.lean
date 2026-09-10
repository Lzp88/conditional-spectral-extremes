import LowLogSineField
import HarmonicSamplePolynomial

/-! Exact log-field identities off the explicitly removed, Haar-null set
of roots of unity. All integer lengths are covered by one common null set. -/
noncomputable section
open MeasureTheory Set Filter Polynomial
open scoped Real BigOperators
namespace ConditionalSpectralExtremes
open ConditionalSpectralAudit.ArithmeticArcs ConditionalSpectralAudit.FourierHarmonic

theorem positive_length_root_null (j : Nat) (hj : 0 < j) :
    ∀ᵐ t : Torus ∂haar, j • t ≠ 0 := by
  have hp := Measure.measurePreserving_zsmul haar (by exact_mod_cast Nat.ne_of_gt hj : (j : Int) ≠ 0)
  simpa only [natCast_zsmul] using hp.quasiMeasurePreserving.ae logSine_root_null

theorem all_positive_length_roots_null :
    ∀ᵐ t : Torus ∂haar, ∀ j : Nat, 0 < j → j • t ≠ 0 := by
  apply ae_all_iff.mpr
  intro j
  by_cases hj : 0 < j
  · filter_upwards [positive_length_root_null j hj] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall (fun _t h => False.elim (hj h))

def lowCyclePolynomial {q : Nat} (j : Fin q → Nat) : Polynomial Complex :=
  ∏ v, (1-(X : Polynomial Complex)^(j v))

theorem lowCyclePolynomial_eval_zero {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v) :
    (lowCyclePolynomial j).eval 0=1 := by
  unfold lowCyclePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp [Nat.ne_of_gt (hj _)]

theorem lowCyclePolynomial_ne_zero {q : Nat} (j : Fin q → Nat) (hj : ∀ v, 0 < j v) :
    lowCyclePolynomial j ≠ 0 := by
  intro he
  have hh := lowCyclePolynomial_eval_zero j hj
  rw [he] at hh
  simp at hh

theorem lowCyclePolynomial_eval_nonzero {q : Nat} (j : Fin q → Nat) (t : Torus)
    (ht : ∀ v, j v • t ≠ 0) : (lowCyclePolynomial j).eval (fourier 1 t) ≠ 0 := by
  unfold lowCyclePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, ← fourier_one_nsmul_eq_pow]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => norm_pos_iff.mp (logSine_norm_pos (ht v)))

theorem lowCyclePolynomial_log_eval {q : Nat} (j : Fin q → Nat) (t : Torus)
    (ht : ∀ v, j v • t ≠ 0) :
    Real.log ‖(lowCyclePolynomial j).eval (fourier 1 t)‖ = lowLogSineField j t := by
  unfold lowCyclePolynomial lowLogSineField
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, ← fourier_one_nsmul_eq_pow, norm_prod]
  rw [Real.log_prod (fun v _ => (logSine_norm_pos (ht v)).ne')]
  rfl

theorem harmonicSamplePolynomial_log_eval {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) (t : Torus) (ht : ∀ i v, x i v • t ≠ 0) :
    Real.log ‖(harmonicSamplePolynomial x).eval (fourier 1 t)‖ =
      ∑ i, ∑ v, logSine (x i v • t) := by
  unfold harmonicSamplePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, ← fourier_one_nsmul_eq_pow, norm_prod]
  rw [Real.log_prod (fun i _ => Finset.prod_ne_zero_iff.mpr (fun v _ => (logSine_norm_pos (ht i v)).ne'))]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.log_prod (fun v _ => (logSine_norm_pos (ht i v)).ne')

#print axioms all_positive_length_roots_null
#print axioms lowCyclePolynomial_log_eval
#print axioms harmonicSamplePolynomial_log_eval
end ConditionalSpectralExtremes
