import ReferenceTiltedMoments
import VectorCoordinateLaws

/-! Exact coordinate MGFs of the actual finite and reference q-sample height laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem vectorExp_single_fun {d : Nat} (v : Fin d) (r : Real) :
    vectorExp (Pi.single v r) = fun x => Real.exp (r*x v) := funext (vectorExp_single v r)

theorem positive_single_shift {d : Nat} (s r : Real) (hs : 0 < s) (hr : 0 < s+r) (v i : Fin d) :
    0 < s+(Pi.single v r : Fin d → Real) i := by
  by_cases h : i=v
  · subst i; simpa using hr
  · simpa [Pi.single_apply, h, Ne.symm h] using hs

theorem harmonic_coordinate_exp_integrable {d : Nat} (s r : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (v : Fin d)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    Integrable (fun x => Real.exp (r*x)) (coordinateLaw (harmonicTiltSumLaw s t m n q) v) := by
  apply coordinateLaw_exp_integrable
  simpa only [vectorExp_single_fun] using harmonicTiltSumLaw_moment_integrable s (Pi.single v r) t m n q hW

theorem harmonic_coordinate_mgf {d : Nat} (s r : Real) (hs : 0 < s) (hr : 0 < s+r)
    (t : Fin d → AddCircle (1 : Real)) (m n q : Nat) (v : Fin d)
    (hH : 0 < harmonicMass m n) (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    mgf id (coordinateLaw (harmonicTiltSumLaw s t m n q) v) r =
      (realHarmonicVectorKernel (fun i => s+(Pi.single v r : Fin d → Real) i) t m n / harmonicTiltNormalizer s t m n)^q := by
  rw [coordinateLaw_mgf]
  simpa only [vectorExp_single_fun] using harmonicTiltSumLaw_moment s hs (Pi.single v r)
    (positive_single_shift s r hs hr v) t m n q hH hW

theorem reference_coordinate_exp_integrable {d : Nat} (s r : Real) (hs : 0 < s) (hr : 0 < s+r)
    (q : Nat) (v : Fin d) :
    Integrable (fun x => Real.exp (r*x)) (coordinateLaw (referenceVectorSumLaw s d q) v) := by
  apply coordinateLaw_exp_integrable
  simpa only [vectorExp_single_fun] using referenceVectorSumLaw_moment_integrable s (by linarith) d q
    (Pi.single v r) (fun i => by linarith [positive_single_shift s r hs hr v i])

theorem reference_coordinate_mgf {d : Nat} (s r : Real) (hs : 0 < s) (hr : 0 < s+r)
    (q : Nat) (v : Fin d) :
    mgf id (coordinateLaw (referenceVectorSumLaw s d q) v) r =
      ((∏ i, logSineA (s+(Pi.single v r : Fin d → Real) i)) / logSineA s ^ d)^q := by
  rw [coordinateLaw_mgf]
  simpa only [vectorExp_single_fun] using referenceVectorSumLaw_moment s (by linarith) d q
    (Pi.single v r) (fun i => by linarith [positive_single_shift s r hs hr v i])

theorem pair_harmonic_coordinate_exp_integrable (s r : Real)
    (t : Fin 2 → AddCircle (1 : Real)) (m n q : Nat) (v : Fin 2)
    (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    Integrable (fun x => Real.exp (r*pairCoordinate v x)) (pairVectorLaw (harmonicTiltSumLaw s t m n q)) := by
  apply pairVectorLaw_exp_integrable
  simpa only [vectorExp_single_fun] using harmonicTiltSumLaw_moment_integrable s (Pi.single v r) t m n q hW

theorem pair_harmonic_coordinate_mgf (s r : Real) (hs : 0 < s) (hr : 0 < s+r)
    (t : Fin 2 → AddCircle (1 : Real)) (m n q : Nat) (v : Fin 2)
    (hH : 0 < harmonicMass m n) (hW : 0 < ∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j) :
    mgf (pairCoordinate v) (pairVectorLaw (harmonicTiltSumLaw s t m n q)) r =
      (realHarmonicVectorKernel (fun i => s+(Pi.single v r : Fin 2 → Real) i) t m n / harmonicTiltNormalizer s t m n)^q := by
  rw [pairVectorLaw_mgf]
  simpa only [vectorExp_single_fun] using harmonicTiltSumLaw_moment s hs (Pi.single v r)
    (positive_single_shift s r hs hr v) t m n q hH hW

theorem pair_reference_coordinate_exp_integrable (s r : Real) (hs : 0 < s) (hr : 0 < s+r)
    (q : Nat) (v : Fin 2) :
    Integrable (fun x => Real.exp (r*pairCoordinate v x)) (pairVectorLaw (referenceVectorSumLaw s 2 q)) := by
  apply pairVectorLaw_exp_integrable
  simpa only [vectorExp_single_fun] using referenceVectorSumLaw_moment_integrable s (by linarith) 2 q
    (Pi.single v r) (fun i => by linarith [positive_single_shift s r hs hr v i])

theorem pair_reference_coordinate_mgf (s r : Real) (hs : 0 < s) (hr : 0 < s+r)
    (q : Nat) (v : Fin 2) :
    mgf (pairCoordinate v) (pairVectorLaw (referenceVectorSumLaw s 2 q)) r =
      ((∏ i, logSineA (s+(Pi.single v r : Fin 2 → Real) i)) / logSineA s ^ 2)^q := by
  rw [pairVectorLaw_mgf]
  simpa only [vectorExp_single_fun] using referenceVectorSumLaw_moment s (by linarith) 2 q
    (Pi.single v r) (fun i => by linarith [positive_single_shift s r hs hr v i])

#print axioms harmonic_coordinate_mgf
#print axioms pair_reference_coordinate_mgf
end ConditionalSpectralAudit.FourierHarmonic
