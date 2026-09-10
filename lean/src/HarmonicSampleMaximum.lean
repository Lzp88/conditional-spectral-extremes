import HarmonicSamplePolynomial
import HarmonicSamplingSupport
import HarmonicSamplingTonelli
import PolynomialRandomMaximum

/-! The actual finite harmonic sample polynomial: an integrated moment
implies a tail estimate for its logarithmic circle maximum. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Real ENNReal BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

theorem harmonicSamplePolynomial_degree_ge_count {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) (hx : ∀ i v, 0 < x i v) :
    (∑ i ∈ Finset.range m, q i) ≤ (harmonicSamplePolynomial x).natDegree := by
  rw [harmonicSamplePolynomial_natDegree x hx]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin m) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (v : Fin (q i)) _ => (show (1 : Nat) ≤ x i v from hx i v)))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, Fin.sum_univ_eq_sum_range] using hh

theorem actual_harmonic_middle_maximum_tail (s S : Real) (hs : 0 < s) (hsS : s ≤ S)
    (lo hi q : Nat → Nat) (m b : Nat) (hb : 0 < b)
    (hQ : 0 < ∑ i ∈ Finset.range m, q i)
    (hlo : ∀ i < m, 0 < lo i) (hhi : ∀ i < m, hi i ≤ b+1) (ε h : Real)
    (hI : (∫⁻ t, ENNReal.ofReal (harmonicMiddleRatio s lo hi q m t) ∂haar) ≤ ENNReal.ofReal (1+ε)) :
    harmonicMiddleSampleLaw lo hi q m {x | h ≤ Real.log (circleNorm (harmonicSamplePolynomial x))} ≤
      ENNReal.ofReal (logSineA s^(∑ i ∈ Finset.range m, q i)*(1+ε)/
        (polynomialMomentConstant S/((b : Real)*(∑ i ∈ Finset.range m, q i))*Real.exp (s*h))) := by
  have hmoment := actual_harmonic_sampling_moment_bound s hs lo hi q m ε hI
  simp_rw [harmonicSamplePolynomial_eval_power] at hmoment
  apply random_polynomial_log_maximum_tail _ harmonicSamplePolynomial s S _ _ h hs hsS
    (mul_pos (by exact_mod_cast hb) (by exact_mod_cast hQ)) _ hmoment
  filter_upwards [harmonicMiddleSampleLaw_positive_bounded lo hi q m b hlo hhi] with x hx
  have hp : ∀ i v, 0 < x i v := fun i v => (hx i v).1
  refine ⟨harmonicSamplePolynomial_ne_zero x hp,
    hQ.trans_le (harmonicSamplePolynomial_degree_ge_count x hp), ?_⟩
  exact_mod_cast harmonicSamplePolynomial_degree_le x hp b (fun i v => (hx i v).2)

#print axioms harmonicSamplePolynomial_degree_ge_count
#print axioms actual_harmonic_middle_maximum_tail
end ConditionalSpectralAudit.FourierHarmonic
