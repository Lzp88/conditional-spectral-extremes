import OrdinaryEwensRandomCentering

/-! The actual two observables in the ordinary Ewens joint corollary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionalSpectralExtremes

def ordinaryStandardCount (θ : Real) (n : Nat) (c : Configuration n) : Real :=
  ((cycleCount c : Real)-θ*Real.log n)/Real.sqrt (θ*Real.log n)

def ordinaryStandardMaximum (θ : Real) (n : Nat) (c : Configuration n) : Real :=
  (maximumLogModulus c-speed θ*Real.log n)/(ordinarySlope θ*Real.sqrt (θ*Real.log n))

def ordinaryDiagonal (θ : Real) (n : Nat) (c : Configuration n) : Real × Real :=
  (ordinaryStandardCount θ n c,ordinaryStandardCount θ n c)

def ordinaryJoint (θ : Real) (n : Nat) (c : Configuration n) : Real × Real :=
  (ordinaryStandardCount θ n c,ordinaryStandardMaximum θ n c)

def ewensJointLaw (θ : Real) (hθ : 0 < θ) (n : Nat) : ProbabilityMeasure (Real × Real) := by
  let _ : IsProbabilityMeasure (ewensProfileLaw θ n) := ewensProfileLaw_probability θ hθ n
  exact ⟨(ewensProfileLaw θ n).map (ordinaryJoint θ n),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

def standardGaussianLaw : ProbabilityMeasure Real :=
  ⟨ProbabilityTheory.gaussianReal 0 1,inferInstance⟩

def diagonalGaussianLaw : ProbabilityMeasure (Real × Real) :=
  standardGaussianLaw.map (show Continuous (fun x : Real => (x,x)) by fun_prop).measurable.aemeasurable

theorem ordinarySlope_pos (θ : Real) (hθ : 0 < θ) : 0 < ordinarySlope θ :=
  speed_coefficient_pos θ hθ

theorem ordinary_joint_difference (θ : Real) (hθ : 0 < θ) (n : Nat) (c : Configuration n) :
    ‖ordinaryJoint θ n c-ordinaryDiagonal θ n c‖ =
      |maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c)| /
        (ordinarySlope θ*Real.sqrt (θ*Real.log n)) := by
  have ha := ordinarySlope_pos θ hθ
  have he : ordinaryStandardMaximum θ n c-ordinaryStandardCount θ n c =
      (maximumLogModulus c-ordinaryLinearCenter θ n (cycleCount c))/
        (ordinarySlope θ*Real.sqrt (θ*Real.log n)) := by
    unfold ordinaryStandardMaximum ordinaryStandardCount ordinaryLinearCenter
    rw [div_mul_eq_div_div]
    rw [div_mul_eq_div_div,← sub_div]
    congr 1
    field_simp
    ring
  simp only [ordinaryJoint,ordinaryDiagonal,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
    Real.norm_eq_abs]
  rw [he,abs_div,abs_of_nonneg (mul_nonneg ha.le (Real.sqrt_nonneg _))]
  exact max_eq_right (div_nonneg (abs_nonneg _) (mul_nonneg ha.le (Real.sqrt_nonneg _)))

#print axioms ordinary_joint_difference
end ConditionalSpectralExtremes
