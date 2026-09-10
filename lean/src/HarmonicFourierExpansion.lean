import HarmonicAverage

noncomputable section
open MeasureTheory
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic

theorem hasSum_harmonic_expansion {ι : Type*} (a : ι → Complex) (phase : ι → AddCircle (1 : Real))
    (values : Nat → Complex) (hs : ∀ j : Nat, HasSum (fun k => a k * fourier (j : Int) (phase k)) (values j))
    (m n : Nat) :
    HasSum (fun k => a k * harmonicCharacter m n (phase k))
      ((harmonicMass m n : Complex)⁻¹ * ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * values j) := by
  have hh := hasSum_sum (s := Finset.Ico m n) (fun j _ => (hs j).mul_left (j : Complex)⁻¹)
  have ht := hh.mul_left (harmonicMass m n : Complex)⁻¹
  apply ht.congr_fun
  intro k
  unfold harmonicCharacter
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hasSum_harmonicAverage (f : C(AddCircle (1 : Real), Complex))
    (hf : Summable (fourierCoeff f)) (m n : Nat) (t : AddCircle (1 : Real)) :
    HasSum (fun k : Int => fourierCoeff f k * harmonicCharacter m n (k • t))
      (harmonicAverage f m n t) := by
  refine hasSum_harmonic_expansion (fourierCoeff f) (fun k => k • t) (fun j => f (j • t)) ?_ m n
  intro j
  simpa only [smul_eq_mul, fourier_nsmul_comm] using
    has_pointwise_sum_fourier_series_of_summable (f := f) hf (j • t)

theorem fourier_add_argument (k : Int) (t u : AddCircle (1 : Real)) :
    fourier k (t + u) = fourier k t * fourier k u := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

def harmonicAverageTwo (f g : AddCircle (1 : Real) → Complex) (m n : Nat)
    (t u : AddCircle (1 : Real)) : Complex :=
  (harmonicMass m n : Complex)⁻¹ * ∑ j ∈ Finset.Ico m n, (j : Complex)⁻¹ * (f (j • t) * g (j • u))

theorem hasSum_harmonicAverageTwo (f g : C(AddCircle (1 : Real), Complex))
    (hf : Summable (fun k : Int => ‖fourierCoeff f k‖))
    (hg : Summable (fun k : Int => ‖fourierCoeff g k‖))
    (m n : Nat) (t u : AddCircle (1 : Real)) :
    HasSum (fun k : Int × Int => (fourierCoeff f k.1 * fourierCoeff g k.2) *
      harmonicCharacter m n (k.1 • t + k.2 • u)) (harmonicAverageTwo f g m n t u) := by
  refine hasSum_harmonic_expansion (fun k : Int × Int => fourierCoeff f k.1 * fourierCoeff g k.2)
    (fun k => k.1 • t + k.2 • u) (fun j => f (j • t) * g (j • u)) ?_ m n
  intro j
  have hfj : HasSum (fun k : Int => fourierCoeff f k * fourier k (j • t)) (f (j • t)) := by
    simpa only [smul_eq_mul] using has_pointwise_sum_fourier_series_of_summable (f := f) hf.of_norm (j • t)
  have hgj : HasSum (fun k : Int => fourierCoeff g k * fourier k (j • u)) (g (j • u)) := by
    simpa only [smul_eq_mul] using has_pointwise_sum_fourier_series_of_summable (f := g) hg.of_norm (j • u)
  have hfn : Summable (fun k : Int => ‖fourierCoeff f k * fourier k (j • t)‖) := by
    have he : (fun k : Int => ‖fourierCoeff f k * fourier k (j • t)‖) = (fun k : Int => ‖fourierCoeff f k‖) := by
      funext k
      rw [norm_mul, show ‖fourier k (j • t)‖ = 1 from Circle.norm_coe _, mul_one]
    rw [he]
    exact hf
  have hgn : Summable (fun k : Int => ‖fourierCoeff g k * fourier k (j • u)‖) := by
    have he : (fun k : Int => ‖fourierCoeff g k * fourier k (j • u)‖) = (fun k : Int => ‖fourierCoeff g k‖) := by
      funext k
      rw [norm_mul, show ‖fourier k (j • u)‖ = 1 from Circle.norm_coe _, mul_one]
    rw [he]
    exact hg
  have hpn : Summable (fun k : Int × Int => (fourierCoeff f k.1 * fourier k.1 (j • t)) *
      (fourierCoeff g k.2 * fourier k.2 (j • u))) :=
    summable_mul_of_summable_norm (f := fun k : Int => fourierCoeff f k * fourier k (j • t))
      (g := fun k : Int => fourierCoeff g k * fourier k (j • u)) hfn hgn
  have hp : HasSum (fun k : Int × Int => (fourierCoeff f k.1 * fourier k.1 (j • t)) *
      (fourierCoeff g k.2 * fourier k.2 (j • u))) (f (j • t) * g (j • u)) :=
    HasSum.mul (α := Complex)
      (f := fun k : Int => fourierCoeff f k * fourier k (j • t))
      (g := fun k : Int => fourierCoeff g k * fourier k (j • u)) hfj hgj hpn
  apply hp.congr_fun
  intro k
  rw [fourier_add_argument]
  simp only [fourier_nsmul_comm]
  ring

theorem complexCoefficient_norm_summable (z : Complex) (hz : 0 < z.re) :
    Summable (fun k : Int => ‖FourierTail.complexCoefficient z k‖) := by
  let alpha : Real := min (z.re / 4) (1 / 2)
  have ha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have hap : alpha < z.re / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ha1 : alpha ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨C, _, hh⟩ := FourierTail.uniform_fourier_l1_and_tail (z.re / 2) z.re alpha
    (by linarith) ha hap ha1
  exact (hh z (by linarith) le_rfl).1

def complexPhiContinuous (z : Complex) (hz : 0 < z.re) : C(AddCircle (1 : Real), Complex) :=
  ⟨FourierTail.complexPhi z, FourierTail.continuous_complexPhi z hz⟩

theorem actual_phi_harmonic_expansion (z : Complex) (hz : 0 < z.re) (m n : Nat)
    (t : AddCircle (1 : Real)) :
    HasSum (fun k : Int => FourierTail.complexCoefficient z k * harmonicCharacter m n (k • t))
      (harmonicAverage (FourierTail.complexPhi z) m n t) :=
  hasSum_harmonicAverage (complexPhiContinuous z hz) (complexCoefficient_norm_summable z hz).of_norm m n t

theorem actual_phi_harmonic_expansion_two (z w : Complex) (hz : 0 < z.re) (hw : 0 < w.re)
    (m n : Nat) (t u : AddCircle (1 : Real)) :
    HasSum (fun k : Int × Int => (FourierTail.complexCoefficient z k.1 * FourierTail.complexCoefficient w k.2) *
      harmonicCharacter m n (k.1 • t + k.2 • u))
      (harmonicAverageTwo (FourierTail.complexPhi z) (FourierTail.complexPhi w) m n t u) :=
  hasSum_harmonicAverageTwo (complexPhiContinuous z hz) (complexPhiContinuous w hw)
    (complexCoefficient_norm_summable z hz) (complexCoefficient_norm_summable w hw) m n t u

#print axioms actual_phi_harmonic_expansion
#print axioms actual_phi_harmonic_expansion_two
end ConditionalSpectralAudit.FourierHarmonic
