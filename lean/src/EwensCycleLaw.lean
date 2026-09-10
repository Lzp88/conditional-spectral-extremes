import ComplexCoefficientAnalysis
import FiniteWeightedLaw

/-! The ordinary Ewens measure on the exact pre-existing finite profiles,
and its genuine cycle-count probability generating function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis ProfileNormalization ConditionalSpectralAudit.FiniteWeighted

def sizeProfiles (n : Nat) : Finset (Configuration n) :=
  Finset.univ.filter (fun c => totalSize c=n)

theorem ewensPartition_eq_sum (θ : Real) (n : Nat) :
    ewensPartition θ n=∑ c ∈ sizeProfiles n, ewensProfileWeight θ c := by
  simp only [ewensPartition,ewensMass,sizeProfiles,Finset.sum_filter,and_true]

theorem markerValue_profile_sum (n : Nat) (z : Complex) :
    markerValue n z=∑ c ∈ sizeProfiles n, (profileWeight c : Complex)*z^cycleCount c := by
  rw [markerValue,markerPolynomial_eq_actual]
  simp [profilePolynomial,sizeProfiles,Polynomial.eval_map,Polynomial.eval₂_finsetSum]

theorem ewensPartition_complex (θ : Real) (n : Nat) :
    (ewensPartition θ n : Complex)=markerValue n (θ : Complex) := by
  rw [ewensPartition_eq_sum,markerValue_profile_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  rw [ewensProfileWeight_factor]
  push_cast
  ring

theorem ewensPartition_pos (θ : Real) (hθ : 0 < θ) (n : Nat) : 0 < ewensPartition θ n := by
  have he := ewensPartition_complex θ n
  rw [markerValue_eq_prod] at he
  have heR : ewensPartition θ n=(n.factorial : Real)⁻¹*∏ j ∈ Finset.range n, (θ+(j : Real)) := by
    apply Complex.ofReal_injective
    push_cast
    exact he
  rw [heR]
  apply mul_pos (by positivity)
  exact Finset.prod_pos (fun j _ => by positivity)

def ewensProfileLaw (θ : Real) (n : Nat) : Measure (Configuration n) :=
  normalizedLaw (sizeProfiles n) (ewensProfileWeight θ) id

theorem ewensProfileLaw_probability (θ : Real) (hθ : 0 < θ) (n : Nat) :
    IsProbabilityMeasure (ewensProfileLaw θ n) := by
  apply normalizedLaw_isProbabilityMeasure
  · exact fun c _ => (ewensProfileWeight_pos hθ c).le
  · rw [← ewensPartition_eq_sum]
    exact ewensPartition_pos θ hθ n

theorem ewensProfileLaw_PGF (θ : Real) (hθ : 0 < θ) (n : Nat) (u : Complex) :
    (∫ c, u^cycleCount c ∂ewensProfileLaw θ n) =
      markerValue n ((θ : Complex)*u)/markerValue n (θ : Complex) := by
  rw [ewensProfileLaw,normalizedLaw_integral _ _ _ (fun c _ => (ewensProfileWeight_pos hθ c).le),
    ← ewensPartition_eq_sum,ewensPartition_complex,markerValue_profile_sum n ((θ : Complex)*u)]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [ewensProfileWeight_factor]
  push_cast
  simp only [id_eq,mul_pow]
  ring

#print axioms ewensPartition_pos
#print axioms ewensProfileLaw_probability
#print axioms ewensProfileLaw_PGF
end ConditionalSpectralExtremes
