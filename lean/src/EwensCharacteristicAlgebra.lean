import EwensAffineCharacteristic
import MovingGammaCoefficient

/-! Exact cancellation of the growing Gamma-ratio power and affine centering. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralExtremes
open ComplexCoefficientAnalysis

theorem marker_quotient_normalized (n : Nat) (hn : n ≠ 0) (z v : Complex) :
    markerValue n z/markerValue n v =
      Complex.exp ((z-v)*(Real.log (n : Real) : Complex))*
        (((n : Complex)^(1-z)*markerValue n z)/((n : Complex)^(1-v)*markerValue n v)) := by
  have hnC : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [← div_mul_div_comm,Complex.cpow_def_of_ne_zero hnC,Complex.cpow_def_of_ne_zero hnC,
    ← Complex.exp_sub,← mul_assoc,← Complex.exp_add,← Complex.natCast_log]
  have he : (z-v)*(Real.log (n : Real) : Complex)+
      ((Real.log (n : Real) : Complex)*(1-z)-(Real.log (n : Real) : Complex)*(1-v))=0 := by ring
  rw [he,Complex.exp_zero,one_mul]

theorem ewens_affine_characteristic_normalized (θ : Real) (hθ : 0 < θ) (n : Nat)
    (hn : n ≠ 0) (b t : Real) :
    MeasureTheory.charFun (ewensAffineMeasure θ n (θ*Real.log n) b) t =
      Complex.exp (((θ*Real.log n : Real) : Complex)*
        (Complex.exp (((t/b : Real) : Complex)*Complex.I)-1-((t/b : Real) : Complex)*Complex.I))*
        (((n : Complex)^(1-(θ : Complex)*Complex.exp (((t/b : Real) : Complex)*Complex.I))*
          markerValue n ((θ : Complex)*Complex.exp (((t/b : Real) : Complex)*Complex.I)))/
          ((n : Complex)^(1-(θ : Complex))*markerValue n (θ : Complex))) := by
  rw [ewensAffineMeasure_charFun θ hθ n, mul_div_assoc,
    marker_quotient_normalized n hn,← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

#print axioms marker_quotient_normalized
#print axioms ewens_affine_characteristic_normalized
end ConditionalSpectralExtremes
