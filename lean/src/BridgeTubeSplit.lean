import BridgeReversal
import PointwiseBridgeProbability
import BridgePathAlgebra

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def firstPath (q m : ℕ) (hm : m ≤ q) (x : Fin q → ℝ) : Fin m → ℝ :=
  fun i => x (Fin.castLE hm i)

def firstMaximumEvent (β : ℝ) (q m : ℕ) (hm : m ≤ q) (w : ℝ) : Set (Fin q → ℝ) :=
  firstPath q m hm ⁻¹' centeredMaximumEvent β m w

theorem firstPath_measurable (q m : ℕ) (hm : m ≤ q) : Measurable (firstPath q m hm) := by
  unfold firstPath
  fun_prop

theorem firstMaximumEvent_measurable (β : ℝ) (q m : ℕ) (hm : m ≤ q) (w : ℝ) :
    MeasurableSet (firstMaximumEvent β q m hm w) :=
  (centeredMaximumEvent_measurable β m w).preimage (firstPath_measurable q m hm)

theorem bridgeFirstEvent_eq_firstMaximum (β : ℝ) (m n : ℕ) (w : ℝ) :
    bridgeFirstEvent m n (centeredMaximumEvent β m w) =
      firstMaximumEvent β (m+n+1) m (by omega) w := by
  ext x
  change ((fun i : Fin m => x ((i.castAdd n).castSucc)) ∈ centeredMaximumEvent β m w) ↔ _
  have he : (fun i : Fin m => x ((i.castAdd n).castSucc)) = firstPath (m+n+1) m (by omega) x := by
    funext i
    rfl
  rw [he]
  rfl

theorem centered_reverse_partial_of_total (β : ℝ) (q j : ℕ) (hj : j ≤ q)
    (x : Fin q → ℝ) (hx : (∑ i, x i) = (q : ℝ)*deriv lambda β) :
    centeredLogSinePartial β j x = -centeredLogSinePartial β (q-j) (reversePath q x) := by
  have hzero : (∑ i, centeredLogSine β (x i)) = 0 := by
    simp only [centeredLogSine, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hx, sub_self]
  exact zero_total_reverse_partial q j hj (fun i => centeredLogSine β (x i)) hzero

theorem bridgeTube_complement_halves (β : ℝ) (q m : ℕ) (hq : 0 < q) (hm : m ≤ q)
    (R : ℝ) (x : Fin q → ℝ) (hx : (∑ i, x i) = (q : ℝ)*deriv lambda β)
    (hbad : x ∉ bridgeTube q ((q : ℝ)*deriv lambda β) R) :
    x ∈ firstMaximumEvent β q m hm R ∨
      reversePath q x ∈ firstMaximumEvent β q (q-m) (Nat.sub_le q m) R := by
  rw [mem_bridgeTube_mean β q hq R x] at hbad
  push Not at hbad
  obtain ⟨j, hj, hdev⟩ := hbad
  by_cases hjm : j ≤ m
  · left
    refine ⟨j, hjm, ?_⟩
    have hh := centeredLogSinePartial_restrict_first β q m j hm hjm x
    change R ≤ |centeredLogSinePartial β j (firstPath q m hm x)|
    have he : centeredLogSinePartial β j (firstPath q m hm x) = centeredLogSinePartial β j x := by
      simpa only [firstPath] using! hh.symm
    rw [he]
    exact hdev.le
  · right
    have hjm' : q-j ≤ q-m := by omega
    refine ⟨q-j, hjm', ?_⟩
    have hh := centeredLogSinePartial_restrict_first β q (q-m) (q-j) (Nat.sub_le q m) hjm' (reversePath q x)
    change R ≤ |centeredLogSinePartial β (q-j) (firstPath q (q-m) (Nat.sub_le q m) (reversePath q x))|
    have he : centeredLogSinePartial β (q-j) (firstPath q (q-m) (Nat.sub_le q m) (reversePath q x)) =
        centeredLogSinePartial β (q-j) (reversePath q x) := by
      simpa only [firstPath] using! hh.symm
    rw [he]
    rw [centered_reverse_partial_of_total β q j hj x hx, abs_neg] at hdev
    exact hdev.le

#print axioms firstPath_measurable
#print axioms firstMaximumEvent_measurable
#print axioms bridgeFirstEvent_eq_firstMaximum
#print axioms centered_reverse_partial_of_total
#print axioms bridgeTube_complement_halves

end ConditionalSpectralExtremes
