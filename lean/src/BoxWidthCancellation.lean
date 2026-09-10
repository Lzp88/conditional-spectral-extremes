import BoxChainIntegral

/-! Exact width cancellation in the Fin-indexed endpoint chain. There are
n+1 actual group kernels, n wide intermediate boxes, and one final interval
of fixed full width delta. -/

noncomputable section
open scoped BigOperators

namespace ConditionalSpectralExtremes

def endpointBoxRadius (n : ℕ) (w : Fin (n+1) → ℝ) (δ : ℝ) (i : Fin (n+1)) : ℝ :=
  if i=Fin.last n then δ/2 else w i

theorem endpointBoxRadius_nonneg (n : ℕ) (w : Fin (n+1) → ℝ) (δ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hδ : 0 ≤ δ) (i : Fin (n+1)) :
    0 ≤ endpointBoxRadius n w δ i := by
  unfold endpointBoxRadius
  split_ifs
  · positivity
  · exact hw i

theorem endpoint_box_width (n : ℕ) (z w : Fin (n+1) → ℝ) (δ : ℝ) (i : Fin (n+1)) :
    (z i+endpointBoxRadius n w δ i)-(z i-endpointBoxRadius n w δ i) =
      if i=Fin.last n then δ else 2*w i := by
  unfold endpointBoxRadius
  split_ifs <;> ring

theorem finite_endpoint_width_cancellation (n : ℕ) (w : Fin (n+1) → ℝ)
    (hw : ∀ i, w i ≠ 0) (δ : ℝ) :
    (∏ i, (w i)⁻¹)*(∏ i, if i=Fin.last n then δ else 2*w i) =
      2^n*δ/w (Fin.last n) := by
  rw [← Finset.prod_mul_distrib, Fin.prod_univ_castSucc]
  have hi (i : Fin n) : (w i.castSucc)⁻¹*(2*w i.castSucc) = 2 := by field_simp [hw i.castSucc]
  simp only [Fin.castSucc_ne_last, if_false, if_true, hi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

theorem gaussian_box_width_cancellation (n : ℕ) (c C δ : ℝ)
    (w U : Fin (n+1) → ℝ) (hw : ∀ i, w i ≠ 0) :
    (∏ i, c/w i*Real.exp (-C*(U i)^2)) *
        (∏ i, if i=Fin.last n then δ else 2*w i) =
      c^(n+1)*(2^n*δ/w (Fin.last n))*Real.exp (-C*(∑ i, (U i)^2)) := by
  rw [product_gaussian_kernel_factors]
  have hh := finite_endpoint_width_cancellation n w hw δ
  calc
    _ = c^(n+1)*((∏ i, (w i)⁻¹)*(∏ i, if i=Fin.last n then δ else 2*w i))*
        Real.exp (-C*(∑ i, (U i)^2)) := by ring
    _ = _ := by rw [hh]

theorem gaussian_endpoint_box_cancellation (n : ℕ) (c C δ : ℝ)
    (z w U : Fin (n+1) → ℝ) (hw : ∀ i, w i ≠ 0) :
    (∏ i, c/w i*Real.exp (-C*(U i)^2)) *
        (∏ i : Fin (n+1), ((z i+endpointBoxRadius n w δ i)-(z i-endpointBoxRadius n w δ i))) =
      c^(n+1)*(2^n*δ/w (Fin.last n))*Real.exp (-C*(∑ i, (U i)^2)) := by
  simp_rw [endpoint_box_width]
  exact gaussian_box_width_cancellation n c C δ w U hw

#print axioms endpointBoxRadius_nonneg
#print axioms endpoint_box_width
#print axioms finite_endpoint_width_cancellation
#print axioms gaussian_box_width_cancellation
#print axioms gaussian_endpoint_box_cancellation

end ConditionalSpectralExtremes
