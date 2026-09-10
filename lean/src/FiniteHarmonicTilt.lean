import FiniteWeightedLaw
import HarmonicTiltKernel

/-! The actual finite tilted vector law and the transform of its independent sums. -/
noncomputable section
open MeasureTheory Set
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic
open FiniteWeighted

def harmonicTiltLaw {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real))
    (m n : Nat) : Measure (Fin d → Real) :=
  normalizedLaw (Finset.Ico m n) (harmonicTiltWeight s t) (harmonicHeight t)

theorem harmonicTiltLaw_probability {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real))
    (m n : Nat) (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    IsProbabilityMeasure (harmonicTiltLaw s t m n) :=
  normalizedLaw_isProbabilityMeasure _ _ _ (fun j _ => harmonicTiltWeight_nonneg s t j) hW

theorem harmonicTiltLaw_transform {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (u : Fin d → Real) (m n : Nat)
    (hH : 0 < harmonicMass m n) :
    (∫ x, vectorPhase u x ∂harmonicTiltLaw s t m n) =
      harmonicVectorKernel (fun v => (s : Complex) + u v * Complex.I) t m n /
        harmonicVectorKernel (fun _ => (s : Complex)) t m n := by
  rw [harmonicTiltLaw, normalizedLaw_integral _ _ _
    (fun j _ => harmonicTiltWeight_nonneg s t j)]
  simp_rw [harmonic_tilted_integrand s hs t u]
  rw [harmonicVectorKernel_real]
  unfold harmonicVectorKernel
  have hHc : (harmonicMass m n : Complex) ≠ 0 := by exact_mod_cast hH.ne'
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp
  simp only [mul_comm Complex.I]

theorem harmonicTiltLaw_transform_norm_le_one {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (u : Fin d → Real) (m n : Nat)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    ‖∫ x, vectorPhase u x ∂harmonicTiltLaw s t m n‖ ≤ 1 := by
  let _ := harmonicTiltLaw_probability s t m n hW
  simpa using norm_integral_le_of_norm_le_const (μ := harmonicTiltLaw s t m n)
    (f := vectorPhase u) (C := 1) (ae_of_all _ (fun x => (norm_vectorPhase u x).le))

def vectorSum {d q : Nat} (x : Fin q → Fin d → Real) (v : Fin d) : Real :=
  ∑ i, x i v

def harmonicTiltSumLaw {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real))
    (m n q : Nat) : Measure (Fin d → Real) :=
  (Measure.pi (fun _ : Fin q => harmonicTiltLaw s t m n)).map vectorSum

theorem vectorPhase_sum {d q : Nat} (u : Fin d → Real) (x : Fin q → Fin d → Real) :
    vectorPhase u (vectorSum x) = ∏ i, vectorPhase u (x i) := by
  unfold vectorPhase vectorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  push_cast
  rw [Finset.sum_mul, Complex.exp_sum]

theorem harmonicTiltSumLaw_transform {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (u : Fin d → Real) (m n q : Nat)
    (hH : 0 < harmonicMass m n)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    (∫ x, vectorPhase u x ∂harmonicTiltSumLaw s t m n q) =
      (harmonicVectorKernel (fun v => (s : Complex) + u v * Complex.I) t m n /
        harmonicVectorKernel (fun _ => (s : Complex)) t m n) ^ q := by
  let _ := harmonicTiltLaw_probability s t m n hW
  have hm : Measurable (@vectorSum d q) := by unfold vectorSum; fun_prop
  have hp : StronglyMeasurable (vectorPhase u) := by
    apply Continuous.stronglyMeasurable
    unfold vectorPhase
    fun_prop
  rw [harmonicTiltSumLaw, integral_map_of_stronglyMeasurable hm hp]
  simp_rw [vectorPhase_sum]
  rw [integral_fintype_prod_eq_pow, Fintype.card_fin,
    harmonicTiltLaw_transform s hs t u m n hH]

#print axioms harmonicTiltLaw_transform
#print axioms harmonicTiltSumLaw_transform
end ConditionalSpectralAudit.FourierHarmonic
