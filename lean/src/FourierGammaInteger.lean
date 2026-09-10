import FourierRealSigns

/-! The manuscript's displayed Gamma formula at every integer frequency,
with reciprocal Gamma values retained at their zeros. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ConditionalSpectralAudit.FourierGeneral

def integerGammaCoefficient (s : Complex) (j : Int) : Complex :=
  (-1)^j * Complex.Gamma (1+s) *
    (Complex.Gamma (1+s/2-(j : Complex)))⁻¹ *
    (Complex.Gamma (1+s/2+(j : Complex)))⁻¹

theorem integerGammaCoefficient_nat (s : Complex) (n : Nat) :
    integerGammaCoefficient s (n : Int) = gammaCoefficient s n := by
  simp only [integerGammaCoefficient, gammaCoefficient, zpow_natCast, Int.cast_natCast]

theorem integerGammaCoefficient_even (s : Complex) : Function.Even (integerGammaCoefficient s) := by
  intro j
  unfold integerGammaCoefficient
  rw [zpow_neg]
  have he : ((-1 : Complex)^j)⁻¹ = (-1 : Complex)^j := by
    rw [← inv_zpow, inv_neg, inv_one]
  rw [he]
  push_cast
  simp only [sub_eq_add_neg, neg_neg]
  ring

theorem coefficient_Gamma_int (s : Real) (hs : 0 < s) (j : Int) :
    coefficient s j = integerGammaCoefficient (s : Complex) j := by
  cases j with
  | ofNat n =>
    change coefficient s (n : Int) = integerGammaCoefficient (s : Complex) (n : Int)
    rw [integerGammaCoefficient_nat]
    exact coefficient_Gamma_nat s hs n
  | negSucc n =>
    change coefficient s (-((n+1 : Nat) : Int)) =
      integerGammaCoefficient (s : Complex) (-((n+1 : Nat) : Int))
    rw [coefficient_even s hs, integerGammaCoefficient_even, integerGammaCoefficient_nat]
    exact coefficient_Gamma_nat s hs (n+1)

theorem coefficient_Gamma_closed_form (s : Real) (hs : 0 < s) (j : Int) :
    coefficient s j = (-1 : Complex)^j * Complex.Gamma (1+(s : Complex)) /
      (Complex.Gamma (1+(s : Complex)/2-(j : Complex)) *
        Complex.Gamma (1+(s : Complex)/2+(j : Complex))) := by
  rw [coefficient_Gamma_int s hs]
  simp only [integerGammaCoefficient, div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms integerGammaCoefficient_even
#print axioms coefficient_Gamma_int
#print axioms coefficient_Gamma_closed_form
end ConditionalSpectralAudit.FourierGeneral
