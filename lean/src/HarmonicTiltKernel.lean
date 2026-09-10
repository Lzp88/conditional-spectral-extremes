import HarmonicUniformError

/-! Root-correct actual finite tilted height kernels in arbitrary finite dimension. -/
noncomputable section
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FourierTail

theorem complexPhi_ofReal (s : Real) (t : AddCircle (1 : Real)) :
    complexPhi (s : Complex) t = (‖(1 : Complex) - fourier 1 t‖ ^ s : Real) := by
  exact (Complex.ofReal_cpow (norm_nonneg _) s).symm

/-- Pointwise, including the zero of the log-sine kernel: the positive tilt kills it. -/
theorem tilted_phase_eq_complexPhi (s u : Real) (hs : 0 < s) (t : AddCircle (1 : Real)) :
    (‖(1 : Complex) - fourier 1 t‖ ^ s : Real) *
        Complex.exp (((u * logSine t : Real) : Complex) * Complex.I) =
      complexPhi ((s : Complex) + u * Complex.I) t := by
  by_cases hx : ‖(1 : Complex) - fourier 1 t‖ = 0
  · have hz : (s : Complex) + u * Complex.I ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.zero_re] at hh
      exact hs.ne' hh
    simp only [complexPhi, hx, Real.zero_rpow hs.ne', Complex.ofReal_zero,
      zero_mul, Complex.zero_cpow hz]
  · have hp : 0 < ‖(1 : Complex) - fourier 1 t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    rw [complexPhi, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx),
      ← Complex.ofReal_log hp.le, Real.rpow_def_of_pos hp, Complex.ofReal_exp,
      ← Complex.exp_add]
    unfold logSine
    push_cast
    congr 1
    ring

def harmonicVectorKernel {d : Nat} (z : Fin d → Complex)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) : Complex :=
  (harmonicMass m n : Complex)⁻¹ *
    ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * ∏ v, complexPhi (z v) (j • t v)

def harmonicTiltWeight {d : Nat} (s : Real) (t : Fin d → AddCircle (1 : Real)) (j : Nat) : Real :=
  (j : Real)⁻¹ * ∏ v, ‖(1 : Complex) - fourier 1 (j • t v)‖ ^ s

def harmonicHeight {d : Nat} (t : Fin d → AddCircle (1 : Real)) (j : Nat) (v : Fin d) : Real :=
  logSine (j • t v)

def vectorPhase {d : Nat} (u x : Fin d → Real) : Complex :=
  Complex.exp (((∑ v, u v * x v : Real) : Complex) * Complex.I)

theorem norm_vectorPhase {d : Nat} (u x : Fin d → Real) : ‖vectorPhase u x‖ = 1 := by
  simp [vectorPhase, Complex.norm_exp]

theorem harmonicTiltWeight_nonneg {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (j : Nat) : 0 ≤ harmonicTiltWeight s t j := by
  unfold harmonicTiltWeight
  positivity

theorem harmonic_tilted_integrand {d : Nat} (s : Real) (hs : 0 < s)
    (t : Fin d → AddCircle (1 : Real)) (u : Fin d → Real) (j : Nat) :
    (harmonicTiltWeight s t j : Complex) * vectorPhase u (harmonicHeight t j) =
      (j : Complex)⁻¹ * ∏ v, complexPhi ((s : Complex) + u v * Complex.I) (j • t v) := by
  have he : vectorPhase u (harmonicHeight t j) =
      ∏ v, Complex.exp (((u v * logSine (j • t v) : Real) : Complex) * Complex.I) := by
    unfold vectorPhase harmonicHeight
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  rw [he]
  simp only [harmonicTiltWeight, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_prod, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  simpa only [Complex.ofReal_mul, mul_assoc] using
    tilted_phase_eq_complexPhi s (u v) hs (j • t v)

theorem harmonicVectorKernel_real {d : Nat} (s : Real)
    (t : Fin d → AddCircle (1 : Real)) (m n : Nat) :
    harmonicVectorKernel (fun _ => (s : Complex)) t m n =
      ((∑ j ∈ Finset.Ico m n, harmonicTiltWeight s t j : Real) : Complex) /
        (harmonicMass m n : Complex) := by
  unfold harmonicVectorKernel harmonicTiltWeight
  simp only [complexPhi_ofReal]
  push_cast
  ring

theorem harmonicVectorKernel_one (z : Complex) (t : AddCircle (1 : Real)) (m n : Nat) :
    harmonicVectorKernel (fun _ : Fin 1 => z) (fun _ => t) m n =
      harmonicAverage (complexPhi z) m n t := by
  simp [harmonicVectorKernel, harmonicAverage]

theorem harmonicVectorKernel_two (z w : Complex) (t u : AddCircle (1 : Real)) (m n : Nat) :
    harmonicVectorKernel ![z, w] ![t, u] m n =
      harmonicAverageTwo (complexPhi z) (complexPhi w) m n t u := by
  simp [harmonicVectorKernel, harmonicAverageTwo, Fin.prod_univ_two]

#print axioms tilted_phase_eq_complexPhi
#print axioms harmonic_tilted_integrand
end ConditionalSpectralAudit.FourierHarmonic
