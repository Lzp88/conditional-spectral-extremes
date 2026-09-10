import ReservoirMarginal
import AnalyticJet

/-!
Actual complex analytic reservoir kernel and its coefficient interface.
The ambient `n` in `reservoirCoefficient n b N l` is a finite truncation;
the analytic kernel itself has no ambient truncation.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ConditionalSpectralExtremes.ReservoirAnalysis
open ConditionalSpectralExtremes.Reservoir

def harmonicPolynomial (b : Nat) (z : Complex) : Complex :=
  ∑ j ∈ Finset.range b, z ^ (j + 1) / ((j + 1 : Nat) : Complex)

def harmonicNumber (b : Nat) : Real := ∑ j ∈ Finset.range b, 1 / ((j + 1 : Nat) : Real)

/-- Principal-log continuation on `{z | 1-z ∈ Complex.slitPlane}`. -/
def reservoirKernel (b : Nat) (z u : Complex) : Complex :=
  Complex.exp (-u * (Complex.log (1 - z) + harmonicPolynomial b z))

def reservoirAnalyticCoefficient (b N : Nat) (u : Complex) : Complex :=
  analyticCoefficient (fun z : Complex => reservoirKernel b z u) N

def finiteReservoirMarker (n b N : Nat) (u : Complex) : Complex :=
  ∑ l ∈ Finset.range (n + 1), (reservoirCoefficient n b N l : Complex) * u ^ l

theorem harmonicPolynomial_one (b : Nat) :
    harmonicPolynomial b 1 = (harmonicNumber b : Complex) := by
  simp [harmonicPolynomial, harmonicNumber]

theorem harmonicPolynomial_zero (b : Nat) : harmonicPolynomial b 0 = 0 := by
  simp [harmonicPolynomial]

theorem reservoirKernel_zero (b : Nat) (u : Complex) : reservoirKernel b 0 u = 1 := by
  simp [reservoirKernel, harmonicPolynomial_zero]

theorem reservoirKernel_marker_zero (b : Nat) (z : Complex) : reservoirKernel b z 0 = 1 := by
  simp [reservoirKernel]

theorem harmonicPolynomial_analyticAt (b : Nat) (z : Complex) :
    AnalyticAt Complex (harmonicPolynomial b) z := by
  unfold harmonicPolynomial
  apply Finset.analyticAt_fun_sum
  intro j hj
  fun_prop

theorem reservoirKernel_analyticAt (b : Nat) (z u : Complex) (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt Complex (fun w => reservoirKernel b w u) z := by
  have hh := harmonicPolynomial_analyticAt b z
  have hl : AnalyticAt Complex (fun w : Complex => Complex.log (1 - w)) z :=
    ((analyticAt_const.sub analyticAt_id).clog hz)
  exact ((analyticAt_const.mul (hl.add hh))).cexp

theorem reservoirKernel_entire_marker (b : Nat) (z : Complex) :
    AnalyticOnNhd Complex (reservoirKernel b z) Set.univ := by
  intro u hu
  unfold reservoirKernel
  fun_prop

theorem hasSum_long_log (b : Nat) (z : Complex) (hz : ‖z‖ < 1) :
    HasSum (fun j : Nat => z ^ (j + b + 1) / ((j + b + 1 : Nat) : Complex))
      (-(Complex.log (1 - z) + harmonicPolynomial b z)) := by
  have hh := (hasSum_nat_add_iff' b).2 (Complex.hasSum_taylorSeries_neg_log' hz)
  simpa only [harmonicPolynomial, neg_add_rev, neg_sub, sub_eq_add_neg, add_comm,
    Nat.cast_add, Nat.cast_one] using hh

theorem reservoirKernel_eq_exp_tsum (b : Nat) (z u : Complex) (hz : ‖z‖ < 1) :
    reservoirKernel b z u = Complex.exp
      (u * ∑' j : Nat, z ^ (j + b + 1) / ((j + b + 1 : Nat) : Complex)) := by
  rw [(hasSum_long_log b z hz).tsum_eq]
  unfold reservoirKernel
  congr 1
  ring

theorem hasDerivAt_harmonicPolynomial (b : Nat) (z : Complex) :
    HasDerivAt (harmonicPolynomial b) (∑ j ∈ Finset.range b, z ^ j) z := by
  unfold harmonicPolynomial
  apply HasDerivAt.fun_sum
  intro j hj
  convert! ((hasDerivAt_id z).pow (j + 1)).div_const (((j + 1 : Nat) : Complex)) using 1
  field_simp
  simp

theorem hasDerivAt_log_plus_harmonicPolynomial (b : Nat) (z : Complex)
    (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : Complex => Complex.log (1 - w) + harmonicPolynomial b w)
      (-z ^ b / (1 - z)) z := by
  have hlog := (Complex.hasDerivAt_log hz).comp z
    ((hasDerivAt_const z (1 : Complex)).sub (hasDerivAt_id z))
  have h := hlog.add (hasDerivAt_harmonicPolynomial b z)
  have hne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero hz
  convert! h using 1
  have hgeom := geom_sum_mul_neg z b
  simp only [zero_sub, mul_neg_one]
  field_simp
  linear_combination -hgeom

theorem hasDerivAt_reservoirKernel (b : Nat) (z u : Complex)
    (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : Complex => reservoirKernel b w u)
      ((u * z ^ b / (1 - z)) * reservoirKernel b z u) z := by
  have h := ((hasDerivAt_log_plus_harmonicPolynomial b z hz).const_mul (-u)).cexp
  convert! h using 1
  unfold reservoirKernel
  ring

theorem reservoir_differential_equation (b : Nat) (z u : Complex)
    (hz : 1 - z ∈ Complex.slitPlane) :
    (1 - z) * deriv (fun w : Complex => reservoirKernel b w u) z =
      u * z ^ b * reservoirKernel b z u := by
  rw [(hasDerivAt_reservoirKernel b z u hz).deriv]
  field_simp [Complex.slitPlane_ne_zero hz]

#print axioms reservoirKernel_analyticAt
#print axioms reservoirKernel_eq_exp_tsum
#print axioms hasDerivAt_harmonicPolynomial

end ConditionalSpectralExtremes.ReservoirAnalysis
