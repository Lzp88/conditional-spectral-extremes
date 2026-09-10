import BridgeLowerBound

/-! Exact Lebesgue translation between the centered bridge at total zero
and the original tilted increments at total q*lambda'(beta). -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def shiftPath (q : ℕ) (a : ℝ) (x : Fin q → ℝ) : Fin q → ℝ := fun i => x i+a

theorem shiftPath_measurable (q : ℕ) (a : ℝ) : Measurable (shiftPath q a) := by
  unfold shiftPath
  fun_prop

theorem shiftPath_neg_shift (q : ℕ) (a : ℝ) (x : Fin q → ℝ) :
    shiftPath q (-a) (shiftPath q a x) = x := by
  funext i
  simp [shiftPath]

theorem bridgePath_shift (n : ℕ) (d a : ℝ) (x : Fin n → ℝ) :
    bridgePath n (d+(n+1 : ℕ)*a) (shiftPath n a x) =
      shiftPath (n+1) a (bridgePath n d x) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [bridgePath_last]
    simp only [shiftPath, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, bridgePath_last]
    push_cast
    ring
  · simp only [bridgePath_castSucc, shiftPath]

theorem shiftPath_measurePreserving (n : ℕ) (a : ℝ) :
    MeasurePreserving (shiftPath n a) := by
  exact measurePreserving_add_right (volume : Measure (Fin n → ℝ)) (fun _ => a)

theorem pointwiseBridge_translate (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (d a : ℝ)
    (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) :
    pointwiseBridge (fun u => f (u+a)) n d E =
      pointwiseBridge f n (d+(n+1 : ℕ)*a) (shiftPath (n+1) (-a) ⁻¹' E) := by
  classical
  have hF := pointwiseBridge_integrand_measurable f hf n (d+(n+1 : ℕ)*a)
    (shiftPath (n+1) (-a) ⁻¹' E) (hE.preimage (shiftPath_measurable (n+1) (-a)))
  unfold pointwiseBridge
  rw [← (shiftPath_measurePreserving n a).lintegral_comp hF]
  apply lintegral_congr
  intro x
  rw [bridgePath_shift]
  have hm : shiftPath (n+1) a (bridgePath n d x) ∈ shiftPath (n+1) (-a) ⁻¹' E ↔
      bridgePath n d x ∈ E := by
    simp only [mem_preimage, shiftPath_neg_shift]
  by_cases hx : bridgePath n d x ∈ E
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.mpr hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (hm.not.mpr hx)]

theorem bridgeTube_centering (β : ℝ) (q : ℕ) (hq : 0 < q) (R : ℝ) :
    shiftPath q (-deriv lambda β) ⁻¹' bridgeTube q 0 R =
      bridgeTube q ((q : ℝ)*deriv lambda β) R := by
  ext x
  rw [mem_bridgeTube_mean β q hq]
  simp only [mem_preimage, bridgeTube, mem_ofPred_eq, mul_zero,
    FiniteWalk.partialSum, shiftPath, centeredLogSinePartial, centeredLogSine,
    sub_eq_add_neg, neg_zero, add_zero]

def centeredTiltedDensity (β x : ℝ) : ℝ := tiltedDensity β (x+deriv lambda β)

def centeredTubeBridge (β : ℝ) (n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  pointwiseBridge (centeredTiltedDensity β) n 0 (bridgeTube (n+1) 0 R)

theorem centeredTubeBridge_eq_tubeBridge (β : ℝ) (n : ℕ) (R : ℝ) :
    centeredTubeBridge β n R = tubeBridge β n ((n+1 : ℕ)*deriv lambda β) R := by
  unfold centeredTubeBridge centeredTiltedDensity
  rw [pointwiseBridge_translate _ (tiltedDensity_measurable β) n 0 (deriv lambda β)
    _ (bridgeTube_measurable _ _ _), zero_add, bridgeTube_centering β (n+1) (by omega)]
  rfl

#print axioms shiftPath_measurable
#print axioms shiftPath_neg_shift
#print axioms bridgePath_shift
#print axioms shiftPath_measurePreserving
#print axioms pointwiseBridge_translate
#print axioms bridgeTube_centering
#print axioms centeredTubeBridge_eq_tubeBridge

end ConditionalSpectralExtremes
