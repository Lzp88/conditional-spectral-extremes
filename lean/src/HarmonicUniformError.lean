import HarmonicSeparation
import ComplexLogSineMellin

noncomputable section
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes

theorem uniform_harmonic_phi_error_one (pmin P alpha : Real) (hinterval : pmin ≤ P)
    (ha0 : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ (z : Complex) (T R a Delta : Real) (m n : Nat) (t : AddCircle (1 : Real)),
      pmin ≤ z.re → z.re ≤ P → |z.im| ≤ T → 0 < R → 0 < m → 0 < harmonicMass m n →
      Real.exp a ≤ m →
      (∀ k : Int, |(k : Real)| ≤ R → k ≠ 0 → Real.exp (-a + Delta) ≤ ‖k • t‖) →
      ‖harmonicAverage (FourierTail.complexPhi z) m n t - complexLogSineA z‖ ≤
        C * (1 + T) ^ 2 * (R ^ (-alpha) + Real.exp (-Delta) / harmonicMass m n) := by
  obtain ⟨C, hC, hcf⟩ := FourierTail.uniform_fourier_l1_and_tail pmin P alpha hinterval ha0 hap ha1
  refine ⟨C, hC, ?_⟩
  intro z T R a Delta m n t hzp hzP hzT hR hm hH ham hsep
  have hz : 0 < z.re := by linarith
  obtain ⟨_, hL, htail⟩ := hcf z hzp hzP
  have hQ : C * (1 + |z.im|) ^ 2 ≤ C * (1 + T) ^ 2 := by gcongr
  have hL' := hL.trans hQ
  have htail' := (htail R hR).trans (mul_le_mul_of_nonneg_right hQ (Real.rpow_pos_of_pos hR _).le)
  have hh := actual_phi_separation_bound z hz m n hm hH a Delta R ham t hsep
  rw [actual_zero_complex_fourier_Gamma z (by linarith)] at hh
  calc
    _ ≤ Real.exp (-Delta) / harmonicMass m n * (∑' k : Int, ‖FourierTail.complexCoefficient z k‖) +
        ∑' k : Int, if R < |(k : Real)| then ‖FourierTail.complexCoefficient z k‖ else 0 := hh
    _ ≤ Real.exp (-Delta) / harmonicMass m n * (C * (1 + T) ^ 2) +
        C * (1 + T) ^ 2 * R ^ (-alpha) :=
      add_le_add (mul_le_mul_of_nonneg_left hL' (div_nonneg (Real.exp_pos _).le hH.le)) htail'
    _ = _ := by ring

theorem uniform_harmonic_phi_error_two (pmin P alpha : Real) (hinterval : pmin ≤ P)
    (ha0 : 0 < alpha) (hap : alpha < pmin) (ha1 : alpha ≤ 1) :
    ∃ C : Real, 0 < C ∧ ∀ (z w : Complex) (T R a Delta : Real) (m n : Nat) (t u : AddCircle (1 : Real)),
      pmin ≤ z.re → z.re ≤ P → pmin ≤ w.re → w.re ≤ P → |z.im| ≤ T → |w.im| ≤ T →
      0 < R → 0 < m → 0 < harmonicMass m n → Real.exp a ≤ m →
      (∀ k : Int × Int, (|(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R) → k ≠ 0 →
        Real.exp (-a + Delta) ≤ ‖k.1 • t + k.2 • u‖) →
      ‖harmonicAverageTwo (FourierTail.complexPhi z) (FourierTail.complexPhi w) m n t u -
          complexLogSineA z * complexLogSineA w‖ ≤
        C * (1 + T) ^ 4 * (R ^ (-alpha) + Real.exp (-Delta) / harmonicMass m n) := by
  obtain ⟨C, hC, hcf⟩ := FourierTail.uniform_fourier_l1_and_tail pmin P alpha hinterval ha0 hap ha1
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro z w T R a Delta m n t u hzp hzP hwp hwP hzT hwT hR hm hH ham hsep
  have hz : 0 < z.re := by linarith
  have hw : 0 < w.re := by linarith
  obtain ⟨_, hLz, htailz⟩ := hcf z hzp hzP
  obtain ⟨_, hLw, htailw⟩ := hcf w hwp hwP
  have hQz : C * (1 + |z.im|) ^ 2 ≤ C * (1 + T) ^ 2 := by gcongr
  have hQw : C * (1 + |w.im|) ^ 2 ≤ C * (1 + T) ^ 2 := by gcongr
  have hLz' := hLz.trans hQz
  have hLw' := hLw.trans hQw
  have htz := (htailz R hR).trans (mul_le_mul_of_nonneg_right hQz (Real.rpow_pos_of_pos hR _).le)
  have htw := (htailw R hR).trans (mul_le_mul_of_nonneg_right hQw (Real.rpow_pos_of_pos hR _).le)
  have hz0 : 0 ≤ ∑' k : Int, ‖FourierTail.complexCoefficient z k‖ := by positivity
  have hw0 : 0 ≤ ∑' k : Int, ‖FourierTail.complexCoefficient w k‖ := by positivity
  have he0 : 0 ≤ Real.exp (-Delta) / harmonicMass m n := div_nonneg (Real.exp_pos _).le hH.le
  have hrt : 0 ≤ R ^ (-alpha) := (Real.rpow_pos_of_pos hR _).le
  have hCQ : 0 ≤ C * (1 + T) ^ 2 := by positivity
  have hCQtail : 0 ≤ C * (1 + T) ^ 2 * R ^ (-alpha) := mul_nonneg hCQ hrt
  have hh := actual_phi_separation_bound_two z w hz hw m n hm hH a Delta R ham t u hsep
  rw [actual_zero_complex_fourier_Gamma z (by linarith), actual_zero_complex_fourier_Gamma w (by linarith)] at hh
  calc
    _ ≤ Real.exp (-Delta) / harmonicMass m n *
        ((∑' k : Int, ‖FourierTail.complexCoefficient z k‖) * (∑' k : Int, ‖FourierTail.complexCoefficient w k‖)) +
      (∑' k : Int, if R < |(k : Real)| then ‖FourierTail.complexCoefficient z k‖ else 0) *
        (∑' k : Int, ‖FourierTail.complexCoefficient w k‖) +
      (∑' k : Int, ‖FourierTail.complexCoefficient z k‖) *
        (∑' k : Int, if R < |(k : Real)| then ‖FourierTail.complexCoefficient w k‖ else 0) := hh
    _ ≤ Real.exp (-Delta) / harmonicMass m n * ((C * (1 + T) ^ 2) * (C * (1 + T) ^ 2)) +
        (C * (1 + T) ^ 2 * R ^ (-alpha)) * (C * (1 + T) ^ 2) +
        (C * (1 + T) ^ 2) * (C * (1 + T) ^ 2 * R ^ (-alpha)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left (mul_le_mul hLz' hLw' hw0 hCQ) he0
        · exact mul_le_mul htz hLw' hw0 hCQtail
      · exact mul_le_mul hLz' htw (by positivity) hCQ
    _ ≤ (2 * C ^ 2) * (1 + T) ^ 4 * (R ^ (-alpha) + Real.exp (-Delta) / harmonicMass m n) := by
      nlinarith [mul_nonneg he0 (sq_nonneg (C * (1 + T) ^ 2))]

#print axioms uniform_harmonic_phi_error_one
#print axioms uniform_harmonic_phi_error_two
end ConditionalSpectralAudit.FourierHarmonic
