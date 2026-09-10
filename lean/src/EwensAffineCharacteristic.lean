import EwensCycleLaw

/-! Characteristic functions of the actual affine cycle count under ordinary Ewens. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis

def ewensAffineMeasure (θ : Real) (n : Nat) (a b : Real) : Measure Real :=
  (ewensProfileLaw θ n).map (fun c => ((cycleCount c : Real)-a)/b)

theorem ewensAffineMeasure_probability (θ : Real) (hθ : 0 < θ) (n : Nat) (a b : Real) :
    IsProbabilityMeasure (ewensAffineMeasure θ n a b) := by
  let _ : IsProbabilityMeasure (ewensProfileLaw θ n) := ewensProfileLaw_probability θ hθ n
  exact MeasureTheory.Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem ewensAffineMeasure_charFun (θ : Real) (hθ : 0 < θ) (n : Nat) (a b t : Real) :
    charFun (ewensAffineMeasure θ n a b) t =
      Complex.exp (-((t*a/b : Real) : Complex)*Complex.I)*
        markerValue n ((θ : Complex)*Complex.exp (((t/b : Real) : Complex)*Complex.I)) /
          markerValue n (θ : Complex) := by
  rw [charFun_apply_real,ewensAffineMeasure,
    integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  have he (c : Configuration n) :
      Complex.exp ((t : Complex)*((((cycleCount c : Real)-a)/b : Real) : Complex)*Complex.I) =
        Complex.exp (-((t*a/b : Real) : Complex)*Complex.I)*
          Complex.exp (((t/b : Real) : Complex)*Complex.I)^cycleCount c := by
    rw [← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul,ewensProfileLaw_PGF θ hθ n]
  ring

def ewensCLTMeasure (θ : Real) (n : Nat) : Measure Real :=
  ewensAffineMeasure θ n (θ*Real.log n) (Real.sqrt (θ*Real.log n))

def ewensCLTLaw (θ : Real) (hθ : 0 < θ) (n : Nat) : ProbabilityMeasure Real :=
  ⟨ewensCLTMeasure θ n,ewensAffineMeasure_probability θ hθ n _ _⟩

#print axioms ewensAffineMeasure_probability
#print axioms ewensAffineMeasure_charFun
end ConditionalSpectralExtremes
