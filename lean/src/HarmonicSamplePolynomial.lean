import RawHarmonicSampling
import HaarPolynomialMoment

/-! The actual polynomial of the sampled middle cycles and its degree. -/
noncomputable section
open Polynomial
open scoped Real Complex BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ArithmeticArcs

def harmonicSamplePolynomial {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) : Polynomial Complex :=
  ∏ i, ∏ v, (1-(Polynomial.X : Polynomial Complex)^(x i v))

theorem fourier_one_nsmul_eq_pow (j : Nat) (t : Torus) :
    fourier 1 (j • t) = fourier 1 t^j := by
  rw [fourier_nsmul_comm]
  simp only [one_smul, fourier_nat_eq_pow]

theorem harmonicSamplePolynomial_eval_power (s : Real) (t : Torus) {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) :
    rawHarmonicMiddleFactor s t x = ‖(harmonicSamplePolynomial x).eval (fourier 1 t)‖^s := by
  unfold rawHarmonicMiddleFactor rawHarmonicBlockFactor rawHarmonicFactor harmonicSamplePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X, fourier_one_nsmul_eq_pow, norm_prod]
  simp_rw [Real.finsetProd_rpow Finset.univ _ (fun _ _ => norm_nonneg _) s]
  exact Real.finsetProd_rpow Finset.univ _ (fun _ _ => Finset.prod_nonneg (fun _ _ => norm_nonneg _)) s

theorem harmonicSamplePolynomial_eval_zero {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) (hx : ∀ i v, 0 < x i v) :
    (harmonicSamplePolynomial x).eval 0=1 := by
  unfold harmonicSamplePolynomial
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp [Nat.ne_of_gt (hx _ _)]

theorem harmonicSamplePolynomial_ne_zero {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) (hx : ∀ i v, 0 < x i v) : harmonicSamplePolynomial x ≠ 0 := by
  intro he
  have hh := harmonicSamplePolynomial_eval_zero x hx
  rw [he] at hh
  simp at hh

theorem harmonicSamplePolynomial_natDegree {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) (hx : ∀ i v, 0 < x i v) :
    (harmonicSamplePolynomial x).natDegree = ∑ i, ∑ v, x i v := by
  have hf (i : Fin m) (v : Fin (q i)) : (1-(Polynomial.X : Polynomial Complex)^(x i v)) ≠ 0 := by
    intro he
    have hh := congrArg (fun p : Polynomial Complex => p.eval 0) he
    simp [Nat.ne_of_gt (hx i v)] at hh
  unfold harmonicSamplePolynomial
  rw [Polynomial.natDegree_prod Finset.univ _ (fun i _ => Finset.prod_ne_zero_iff.mpr (fun v _ => hf i v))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.natDegree_prod Finset.univ _ (fun v _ => hf i v)]
  apply Finset.sum_congr rfl
  intro v _
  exact cycle_factor_natDegree _ (hx i v)

theorem harmonicSamplePolynomial_degree_le {m : Nat} {q : Nat → Nat}
    (x : (i : Fin m) → Fin (q i) → Nat) (hx : ∀ i v, 0 < x i v)
    (b : Nat) (hxb : ∀ i v, x i v ≤ b) :
    (harmonicSamplePolynomial x).natDegree ≤ b*(∑ i ∈ Finset.range m, q i) := by
  rw [harmonicSamplePolynomial_natDegree x hx]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin m) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (v : Fin (q i)) _ => hxb i v))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  calc
    _ ≤ ∑ i : Fin m, q i*b := hh
    _ = b*(∑ i ∈ Finset.range m, q i) := by
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range]
      exact Nat.mul_comm _ _

#print axioms harmonicSamplePolynomial_eval_power
#print axioms harmonicSamplePolynomial_natDegree
#print axioms harmonicSamplePolynomial_degree_le
end ConditionalSpectralAudit.FourierHarmonic
