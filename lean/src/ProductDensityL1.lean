import FiniteMeasureDensityProduct

/-! Actual tensorization in L1, with linear accumulation over all blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
namespace ConditionalSpectralAudit.FourierHarmonic

theorem product_density_l1_step {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (f g : α → Real) (F G : β → Real)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hF : Integrable F ν) (hG : Integrable G ν)
    (hg0 : ∀ x, 0 ≤ g x) (hF0 : ∀ x, 0 ≤ F x) :
    (∫ x, |f x.1*F x.2-g x.1*G x.2| ∂μ.prod ν) ≤
      (∫ x, |f x-g x| ∂μ) * (∫ x, F x ∂ν)+
      (∫ x, g x ∂μ) * (∫ x, |F x-G x| ∂ν) := by
  have hleft : Integrable (fun x : α × β => |f x.1*F x.2-g x.1*G x.2|) (μ.prod ν) := by
    simpa only [Pi.sub_apply] using! ((hf.mul_prod hF).sub (hg.mul_prod hG)).abs
  have ha : Integrable (fun x : α × β => |f x.1-g x.1| * F x.2) (μ.prod ν) := by
    simpa only [Pi.sub_apply] using! (hf.sub hg).abs.mul_prod hF
  have hb : Integrable (fun x : α × β => g x.1*|F x.2-G x.2|) (μ.prod ν) := by
    simpa only [Pi.sub_apply] using! hg.mul_prod (hF.sub hG).abs
  calc
    _ ≤ ∫ x, |f x.1-g x.1| * F x.2+g x.1*|F x.2-G x.2| ∂μ.prod ν := by
      apply integral_mono hleft (ha.add hb)
      intro x
      simp only [Pi.add_apply]
      calc
        _ = |(f x.1-g x.1)*F x.2+g x.1*(F x.2-G x.2)| := by congr 1; ring
        _ ≤ |(f x.1-g x.1)*F x.2|+|g x.1*(F x.2-G x.2)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hF0 _), abs_of_nonneg (hg0 _)]
    _ = _ := by
      rw [integral_add ha hb]
      congr 1
      · convert! integral_prod_mul (μ := μ) (ν := ν) (fun x => |f x-g x|) F using 1
      · convert! integral_prod_mul (μ := μ) (ν := ν) g (fun x => |F x-G x|) using 1

theorem finite_product_density_l1 {n : Nat} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : Fin n) → Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f g : (i : Fin n) → α i → Real)
    (hf : ∀ i, Integrable (f i) (μ i)) (hg : ∀ i, Integrable (g i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hf1 : ∀ i, ∫ x, f i x ∂μ i = 1) (hg1 : ∀ i, ∫ x, g i x ∂μ i = 1) :
    (∫ x, |(∏ i, f i (x i))-(∏ i, g i (x i))| ∂Measure.pi μ) ≤
      ∑ i, ∫ x, |f i x-g i x| ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hF : Integrable (fun x : (i : Fin n) → α i.succ => ∏ i, f i.succ (x i))
          (Measure.pi (fun i => μ i.succ)) := Integrable.fintype_prod_dep (fun i => hf i.succ)
      have hG : Integrable (fun x : (i : Fin n) → α i.succ => ∏ i, g i.succ (x i))
          (Measure.pi (fun i => μ i.succ)) := Integrable.fintype_prod_dep (fun i => hg i.succ)
      have hstep := product_density_l1_step (μ 0) (Measure.pi (fun i : Fin n => μ i.succ))
        (f 0) (g 0) (fun x => ∏ i : Fin n, f i.succ (x i)) (fun x => ∏ i : Fin n, g i.succ (x i))
        (hf 0) (hg 0) hF hG (hg0 0) (fun x => Finset.prod_nonneg (fun i _ => hf0 i.succ (x i)))
      have htail := ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => g i.succ)
        (fun i => hf i.succ) (fun i => hg i.succ) (fun i => hf0 i.succ) (fun i => hg0 i.succ)
        (fun i => hf1 i.succ) (fun i => hg1 i.succ)
      rw [integral_fintype_prod_eq_prod, hg1 0] at hstep
      simp only [hf1, Finset.prod_const_one, mul_one, one_mul] at hstep
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      rw [Fin.sum_univ_succ]
      linarith

#print axioms finite_product_density_l1
end ConditionalSpectralAudit.FourierHarmonic
