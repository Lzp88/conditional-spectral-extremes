import HarmonicAverage

noncomputable section
open scoped Real Complex BigOperators

namespace ConditionalSpectralAudit.FourierHarmonic

theorem pair_norm_sum_eq (a b : Int → Complex)
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖)) :
    (∑' k : Int × Int, ‖a k.1 * b k.2‖) = (∑' k, ‖a k‖) * (∑' k, ‖b k‖) := by
  simp only [norm_mul]
  exact (ha.tsum_mul_tsum hb (ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))).symm

theorem pair_norm_tail_bound (a b : Int → Complex) (R : Real)
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖)) :
    (∑' k : Int × Int, if |(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R then 0 else ‖a k.1 * b k.2‖) ≤
      (∑' k : Int, if R < |(k : Real)| then ‖a k‖ else 0) * (∑' k, ‖b k‖) +
      (∑' k, ‖a k‖) * (∑' k : Int, if R < |(k : Real)| then ‖b k‖ else 0) := by
  let A : Int → Real := fun k => if R < |(k : Real)| then ‖a k‖ else 0
  let B : Int → Real := fun k => if R < |(k : Real)| then ‖b k‖ else 0
  have hA0 (k : Int) : 0 ≤ A k := by dsimp [A]; split_ifs <;> positivity
  have hB0 (k : Int) : 0 ≤ B k := by dsimp [B]; split_ifs <;> positivity
  have hA : Summable A := Summable.of_nonneg_of_le hA0 (fun k => by dsimp [A]; split_ifs <;> simp) ha
  have hB : Summable B := Summable.of_nonneg_of_le hB0 (fun k => by dsimp [B]; split_ifs <;> simp) hb
  have hleft := hA.mul_of_nonneg hb hA0 (fun _ => norm_nonneg _)
  have hright := ha.mul_of_nonneg hB (fun _ => norm_nonneg _) hB0
  have hprod := ha.mul_norm hb
  have htail : Summable (fun k : Int × Int => if |(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R then 0 else ‖a k.1 * b k.2‖) := by
    apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ hprod
    intro k
    split_ifs <;> simp; positivity
  have hpoint (k : Int × Int) :
      (if |(k.1 : Real)| ≤ R ∧ |(k.2 : Real)| ≤ R then 0 else ‖a k.1 * b k.2‖) ≤
        A k.1 * ‖b k.2‖ + ‖a k.1‖ * B k.2 := by
    dsimp [A, B]
    rw [norm_mul]
    split_ifs <;> simp_all <;>
      nlinarith [mul_nonneg (norm_nonneg (a k.1)) (norm_nonneg (b k.2))]
  calc
    _ ≤ ∑' k : Int × Int, (A k.1 * ‖b k.2‖ + ‖a k.1‖ * B k.2) := htail.tsum_le_tsum hpoint (hleft.add hright)
    _ = (∑' k : Int × Int, A k.1 * ‖b k.2‖) + (∑' k : Int × Int, ‖a k.1‖ * B k.2) := hleft.tsum_add hright
    _ = _ := by rw [← hA.tsum_mul_tsum hb hleft, ← ha.tsum_mul_tsum hB hright]

#print axioms pair_norm_tail_bound
end ConditionalSpectralAudit.FourierHarmonic
