import ExtendedLogMaximum

/-! The literal torus-indexed extended height: the finite cycle sum has
value minus infinity at roots, and its supremum is the proved maximum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem exists_fourier_unit_parameter {z : Complex} (hz : ‖z‖=1) :
    ∃ t : AddCircle (1 : Real), fourier 1 t=z := by
  obtain ⟨θ,hθ⟩ := (Complex.norm_eq_one_iff z).mp hz
  refine ⟨((θ/(2*Real.pi) : Real) : AddCircle (1 : Real)),?_⟩
  rw [← hθ]
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,
    Int.cast_one,Complex.ofReal_one,mul_one,div_one]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem fourier_nat_as_power (n : Nat) (t : AddCircle (1 : Real)) :
    fourier (n : Int) t=(fourier 1 t)^n := by
  induction n with
  | zero => simp only [Nat.cast_zero,fourier_zero,pow_zero]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,pow_succ]

def extendedTorusHeight {n : Nat} (c : Configuration n) (t : AddCircle (1 : Real)) : EReal :=
  extendedPolynomialHeight (characteristicPolynomial c) (fourier 1 t)

theorem extendedTorusHeight_cycle_sum {n : Nat} (c : Configuration n)
    (t : AddCircle (1 : Real)) :
    extendedTorusHeight c t=∑ j : Fin n, ((c j).val : EReal)*
      ENNReal.log (ENNReal.ofReal ‖1-fourier ((j.val+1 : Nat) : Int) t‖) := by
  rw [extendedTorusHeight,extended_profile_height_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_nat_as_power]

theorem torus_sup_extendedPolynomialHeight (p : Polynomial Complex) :
    (⨆ t : AddCircle (1 : Real), extendedPolynomialHeight p (fourier 1 t))=
      extendedCircleMaximum p := by
  apply le_antisymm
  · apply iSup_le
    intro t
    exact le_iSup_of_le ⟨fourier 1 t,Circle.norm_coe _⟩ le_rfl
  · apply iSup_le
    intro z
    obtain ⟨t,ht⟩ := exists_fourier_unit_parameter z.property
    exact le_iSup_of_le t (by rw [ht])

theorem extendedTorusHeight_sup_eq_maximum {n : Nat} (c : Configuration n) :
    (⨆ t : AddCircle (1 : Real), extendedTorusHeight c t)=(maximumLogModulus c : EReal) := by
  change (⨆ t : AddCircle (1 : Real),
    extendedPolynomialHeight (characteristicPolynomial c) (fourier 1 t))=_
  rw [torus_sup_extendedPolynomialHeight,extended_profile_maximum]

#print axioms exists_fourier_unit_parameter
#print axioms extendedTorusHeight_cycle_sum
#print axioms extendedTorusHeight_sup_eq_maximum
end ConditionalSpectralExtremes
