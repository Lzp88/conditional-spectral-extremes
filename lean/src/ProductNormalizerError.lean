import NormalizerPowerError

/-! Full product normalizers: every fine-block relative error is accumulated. -/
noncomputable section
namespace ConditionalSpectralAudit.FourierHarmonic

theorem finite_product_error_power {ι : Type*} (S : Finset ι) (b : ι → Real)
    (ε : Real) (hε : 0 ≤ ε) (he : ∀ i ∈ S, |b i-1| ≤ ε) :
    |(∏ i ∈ S, b i)-1| ≤ (1+ε)^S.card-1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hp := ih (fun j hj => he j (Finset.mem_insert_of_mem hj))
      have hb := he i (Finset.mem_insert_self _ _)
      have hp0 : |∏ j ∈ S, b j| ≤ (1+ε)^S.card := by
        calc
          _ = |((∏ j ∈ S, b j)-1)+1| := by congr 1; ring
          _ ≤ |(∏ j ∈ S, b j)-1|+|1| := abs_add_le _ _
          _ ≤ _ := by norm_num at *; linarith
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      calc
        _ = |(b i-1)*(∏ j ∈ S, b j)+((∏ j ∈ S, b j)-1)| := by congr 1; ring
        _ ≤ |(b i-1)*(∏ j ∈ S, b j)|+|(∏ j ∈ S, b j)-1| := abs_add_le _ _
        _ = |b i-1| * |∏ j ∈ S, b j|+|(∏ j ∈ S, b j)-1| := by rw [abs_mul]
        _ ≤ ε*(1+ε)^S.card+((1+ε)^S.card-1) :=
          add_le_add (mul_le_mul hb hp0 (abs_nonneg _) hε) hp
        _ = _ := by rw [pow_succ]; ring

theorem finite_product_relative_error {m : Nat} (b : Fin m → Real)
    (ε : Real) (hε : 0 ≤ ε) (he : ∀ i, |b i-1| ≤ ε) :
    |(∏ i, b i)-1| ≤ (m : Real)*ε*Real.exp ((m : Real)*ε) := by
  have hh := finite_product_error_power Finset.univ b ε hε (fun i _ => he i)
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  apply hh.trans
  calc
    _ ≤ |(1+ε)^m-1| := le_abs_self _
    _ ≤ _ := positive_power_relative_error (1+ε) ε (by linarith) hε
      (by simpa only [add_sub_cancel_left, abs_of_nonneg hε] using (le_refl ε)) m

#print axioms finite_product_relative_error
end ConditionalSpectralAudit.FourierHarmonic
