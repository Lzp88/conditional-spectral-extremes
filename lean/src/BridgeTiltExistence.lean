import BridgeSaddle

noncomputable section
open Set

namespace ConditionalSpectralExtremes

theorem lambda_deriv_growth (a b v : ℝ) (ha : -1 < a)
    (hcurv : ∀ x ∈ Icc a b, v ≤ (deriv^[2] lambda) x) :
    ∀ s ∈ Icc a b, ∀ β ∈ Icc a b, s ≤ β →
      v*(β-s) ≤ deriv lambda β-deriv lambda s := by
  have hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ (deriv lambda) x := by
    intro x hx
    exact ((lambda_contDiffAt (lt_of_lt_of_le ha hx.1) 2).derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableWithinAt)
    (fun x hx => hcurv x (interior_subset hx))

theorem lambda_mean_inverse_uniform (a b ε : ℝ) (hε : 0 < ε)
    (ha : -1 < a-ε) (hab : a ≤ b) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ s ∈ Icc a b, ∀ z : ℝ,
      |z-deriv lambda s| ≤ δ →
      ∃ β ∈ Icc (a-ε) (b+ε), deriv lambda β = z ∧
        |β-s| ≤ L*|z-deriv lambda s| := by
  have hord : a-ε ≤ b+ε := by linarith
  obtain ⟨v, M, hv, hcurv⟩ := lambda_curvature_compact_bounds ha hord
  have hg := lambda_deriv_growth (a-ε) (b+ε) v ha (fun x hx => (hcurv x hx).1)
  refine ⟨v*ε/2, 1/v, by positivity, by positivity, ?_⟩
  intro s hs z hz
  have hs' : s ∈ Icc (a-ε) (b+ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hleft : s-ε ∈ Icc (a-ε) (b+ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hright : s+ε ∈ Icc (a-ε) (b+ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlo := hg (s-ε) hleft s hs' (by linarith)
  have hhi := hg s hs' (s+ε) hright (by linarith)
  have hz' := abs_le.mp hz
  have htarget : z ∈ Icc (deriv lambda (s-ε)) (deriv lambda (s+ε)) := by
    constructor <;> nlinarith [mul_pos hv hε]
  have hcont : ContinuousOn (deriv lambda) (Icc (s-ε) (s+ε)) := by
    intro x hx
    have hx' : -1 < x := by linarith [hleft.1, hx.1]
    exact (((lambda_contDiffAt hx' 2).derivWithin
      (m := 1) (by norm_num)).differentiableAt (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨β, hβ, he⟩ := intermediate_value_Icc (by linarith : s-ε ≤ s+ε) hcont htarget
  have hβ' : β ∈ Icc (a-ε) (b+ε) := ⟨hleft.1.trans hβ.1, hβ.2.trans hright.2⟩
  refine ⟨β, hβ', he, ?_⟩
  have hsep := lambda_deriv_separation (a-ε) (b+ε) v s β ha hs' hβ'
    (fun x hx => (hcurv x hx).1)
  rw [he] at hsep
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ hv).mpr (by nlinarith only [hsep])

theorem lambda_mean_inverse_unique (a b s β : ℝ) (ha : -1 < a) (hab : a ≤ b)
    (hs : s ∈ Icc a b) (hβ : β ∈ Icc a b) (he : deriv lambda s = deriv lambda β) : s = β := by
  obtain ⟨v, M, hv, hcurv⟩ := lambda_curvature_compact_bounds ha hab
  have hh := lambda_deriv_separation a b v s β ha hs hβ (fun x hx => (hcurv x hx).1)
  rw [he, sub_self, abs_zero] at hh
  have hz : |β-s| = 0 := by nlinarith [abs_nonneg (β-s)]
  exact (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm

#print axioms lambda_deriv_growth
#print axioms lambda_mean_inverse_uniform
#print axioms lambda_mean_inverse_unique

end ConditionalSpectralExtremes
