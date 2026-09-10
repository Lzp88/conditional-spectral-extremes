import HarmonicCircle
import FourierTail

noncomputable section
open MeasureTheory
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic

def harmonicMass (m n : Nat) : Real := ∑ j ∈ Finset.Ico m n, (j : Real)⁻¹

def harmonicCharacter (m n : Nat) (t : AddCircle (1 : Real)) : Complex :=
  (harmonicMass m n : Complex)⁻¹ * ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * fourier (j : Int) t

def harmonicAverage (f : AddCircle (1 : Real) → Complex) (m n : Nat) (t : AddCircle (1 : Real)) : Complex :=
  (harmonicMass m n : Complex)⁻¹ * ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * f (j • t)

theorem harmonicMass_nonneg (m n : Nat) : 0 ≤ harmonicMass m n := by
  exact Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem harmonicMass_pos (m n : Nat) (hm : 0 < m) (hmn : m < n) : 0 < harmonicMass m n := by
  apply Finset.sum_pos'
  · intro j _
    positivity
  · exact ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩, inv_pos.mpr (by exact_mod_cast hm)⟩

theorem harmonicMass_complex (m n : Nat) :
    (harmonicMass m n : Complex) = ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ := by
  unfold harmonicMass
  push_cast
  rfl

theorem harmonicCharacter_zero (m n : Nat) (hH : 0 < harmonicMass m n) :
    harmonicCharacter m n 0 = 1 := by
  unfold harmonicCharacter
  simp only [fourier_eval_zero, mul_one]
  rw [← harmonicMass_complex, inv_mul_cancel₀ (by exact_mod_cast hH.ne')]

theorem norm_harmonicCharacter_le_one (m n : Nat) (hH : 0 < harmonicMass m n)
    (t : AddCircle (1 : Real)) : ‖harmonicCharacter m n t‖ ≤ 1 := by
  have hs : ‖∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * fourier (j : Int) t‖ ≤ harmonicMass m n := by
    apply (norm_sum_le _ _).trans
    unfold harmonicMass
    apply Finset.sum_le_sum
    intro j _
    have hj : ‖fourier (j : Int) t‖ = 1 := Circle.norm_coe _
    simp only [norm_mul, hj, mul_one, norm_inv, Complex.norm_natCast, le_refl]
  unfold harmonicCharacter
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  calc
    _ ≤ (harmonicMass m n)⁻¹ * harmonicMass m n := mul_le_mul_of_nonneg_left hs (inv_pos.mpr hH).le
    _ = 1 := inv_mul_cancel₀ hH.ne'

theorem harmonicCharacter_separation_bound (m n : Nat) (hm : 0 < m) (hH : 0 < harmonicMass m n)
    (a Delta : Real) (ha : Real.exp a ≤ m) (t : AddCircle (1 : Real))
    (ht : Real.exp (-a + Delta) ≤ ‖t‖) :
    ‖harmonicCharacter m n t‖ ≤ Real.exp (-Delta) / harmonicMass m n := by
  have ht0 : t ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le ht)
  have he := harmonic_circle_exponential_bound t ht0 m n hm a ha
  have htR : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hb : Real.exp (-a) / ‖t‖ ≤ Real.exp (-Delta) := by
    apply (div_le_iff₀ htR).mpr
    have hh := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-Delta)).le
    rw [← Real.exp_add] at hh
    simpa only [show -Delta + (-a + Delta) = -a by ring] using hh
  unfold harmonicCharacter
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  calc
    _ ≤ (harmonicMass m n)⁻¹ * Real.exp (-Delta) := mul_le_mul_of_nonneg_left (he.trans hb) (inv_pos.mpr hH).le
    _ = _ := by ring

theorem fourier_nsmul_comm (k : Int) (j : Nat) (t : AddCircle (1 : Real)) :
    fourier k (j • t) = fourier (j : Int) (k • t) := by
  simp only [fourier_apply, natCast_zsmul]
  rw [smul_comm]

theorem harmonicAverage_fourier (k : Int) (m n : Nat) (t : AddCircle (1 : Real)) :
    harmonicAverage (fourier k) m n t = harmonicCharacter m n (k • t) := by
  unfold harmonicAverage harmonicCharacter
  simp_rw [fourier_nsmul_comm]

#print axioms harmonicCharacter_separation_bound
end ConditionalSpectralAudit.FourierHarmonic
