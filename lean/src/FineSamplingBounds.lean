import HarmonicFineGeometry

/-! Literal support and total count bounds of the manuscript's middle
blocks, including the floor defining the reservoir cutoff. -/
noncomputable section
open Filter Set
open scoped Real BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales

theorem fineBlockHi_le_cutoff_add_one (p : Parameters) (n i : Nat)
    (hω : 0 ≤ omega p n) (hm : 0 < count p n)
    (hb : 0 < ReservoirScale.cutoff n) (hi : i < count p n) :
    fineBlockHi p n i ≤ ReservoirScale.cutoff n+1 := by
  have hco : coordinate p n (i+1) ≤ aStar n := by
    rw [← coordinate_last p n hm]
    unfold coordinate
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hi) hω)
  have he : Real.exp (coordinate p n (i+1)) ≤ (ReservoirScale.cutoff n : Real) := by
    calc
      _ ≤ Real.exp (aStar n) := Real.exp_le_exp.mpr hco
      _ = _ := Real.exp_log (by exact_mod_cast hb)
  unfold fineBlockHi exponentialEndpoint
  exact Nat.add_le_add_right (Nat.floor_le_of_le he) 1

theorem middle_count_positive (p : Parameters) (n : Nat) (κ η K_E C_E : Real)
    (q : Nat → Nat) (hκ : 0 < κ) (hω : 0 < omega p n) (hm : 0 < count p n)
    (hreg : Regular p n κ η K_E C_E q) :
    0 < ∑ i ∈ Finset.range (count p n), q (i+1) := by
  have h0 := (hreg.1 0 (Finset.mem_range.mpr hm)).1
  have hq : 0 < q 1 := by
    have hp := (mul_pos (div_pos hκ (by norm_num : (0 : Real)<2)) hω).trans_le h0
    exact_mod_cast hp
  exact hq.trans_le (Finset.single_le_sum (f := fun i => q (i+1))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hm))

theorem middle_count_le_scale (p : Parameters) (n : Nat) (κ η K_E C_E : Real)
    (q : Nat → Nat) (hK : 0 ≤ κ+η) (hr : 0 ≤ r p n) (ha : aStar n ≤ ReservoirScale.L n)
    (hm : 0 < count p n) (hreg : Regular p n κ η K_E C_E q) :
    ((∑ i ∈ Finset.range (count p n), q (i+1) : Nat) : Real) ≤ (κ+η)*ReservoirScale.L n := by
  rw [Nat.cast_sum]
  have hh := Finset.sum_le_sum (s := Finset.range (count p n)) (fun i hi => (hreg.1 i hi).2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  have he : (count p n : Real)*omega p n = aStar n-r p n := by
    unfold omega
    field_simp
  calc
    _ ≤ (count p n : Real)*((κ+η)*omega p n) := hh
    _ = (κ+η)*(aStar n-r p n) := by rw [← he]; ring
    _ ≤ (κ+η)*ReservoirScale.L n := mul_le_mul_of_nonneg_left (by linarith) hK

#print axioms fineBlockHi_le_cutoff_add_one
#print axioms middle_count_positive
#print axioms middle_count_le_scale
end ConditionalSpectralAudit.FourierHarmonic
