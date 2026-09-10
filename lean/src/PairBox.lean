import PairUniformNoise

noncomputable section
open MeasureTheory Set WithLp

namespace ConditionalSpectralAudit.FourierHarmonic

def pairBox (T : Real) : Set PairSpace := ofLp ⁻¹' (Icc (-T) T ×ˢ Icc (-T) T)

theorem measurableSet_pairBox (T : Real) : MeasurableSet (pairBox T) :=
  (measurableSet_Icc.prod measurableSet_Icc).preimage
    (MeasurableEquiv.toLp 2 (Real × Real)).symm.measurable

theorem mem_pairBox (T : Real) (x : PairSpace) :
    x ∈ pairBox T ↔ (ofLp x).1 ∈ Icc (-T) T ∧ (ofLp x).2 ∈ Icc (-T) T := Iff.rfl

theorem pairBox_volume (T : Real) :
    volume (pairBox T) = ENNReal.ofReal (2*T) * ENNReal.ofReal (2*T) := by
  rw [pairBox, (WithLp.volume_preserving_ofLp Real Real).measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet]
  change (volume : Measure Real).prod volume (Icc (-T) T ×ˢ Icc (-T) T) = _
  rw [Measure.prod_prod, Real.volume_Icc]
  congr 2 <;> ring

theorem pairBox_volume_real (T : Real) (hT : 0 ≤ T) :
    volume.real (pairBox T) = 4*T^2 := by
  rw [measureReal_def, pairBox_volume, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  ring

#print axioms pairBox_volume_real
end ConditionalSpectralAudit.FourierHarmonic
