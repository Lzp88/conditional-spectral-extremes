import ActualEndpointChainDefinitions
import BoxWidthCancellation

/-! Actual endpoint-box volume cancellation and integration of the
proved pointwise killed-kernel bounds. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

theorem endpointLower_zero (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) :
    endpointLower p n κ G B₀ q 0=0 := by simp [endpointLower, endpointRadius, boxCenter_zero]

theorem endpointUpper_zero (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) :
    endpointUpper p n κ G B₀ q 0=0 := by simp [endpointUpper, endpointRadius, boxCenter_zero]

theorem endpointPath_lower (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (i : Fin (groupNumber p n+1)) :
    endpointPath (groupNumber p n) 0 (fun j => endpointLower p n κ G B₀ q (j.val+1)) i =
      endpointLower p n κ G B₀ q i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [endpointPath, endpointLower_zero]
  · rfl

theorem endpointPath_upper (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (i : Fin (groupNumber p n+1)) :
    endpointPath (groupNumber p n) 0 (fun j => endpointUpper p n κ G B₀ q (j.val+1)) i =
      endpointUpper p n κ G B₀ q i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [endpointPath, endpointUpper_zero]
  · rfl

theorem actualEndpointChain_product_lower (p : Parameters) (n : ℕ) (κ G B₀ c C : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hc : 0 ≤ c) (hq : ∀ j < groupNumber p n, 3 ≤ groupSamples p n q j)
    (hminor : ∀ j < groupNumber p n, ∀ x ∈ Icc (endpointLower p n κ G B₀ q j) (endpointUpper p n κ G B₀ q j),
      ∀ x' ∈ Icc (endpointLower p n κ G B₀ q (j+1)) (endpointUpper p n κ G B₀ q (j+1)),
        c/Real.sqrt (groupWidth p n j)*Real.exp (-C*(groupU p n κ q j)^2) ≤ actualCoarseKernel p n κ G q j x x') :
    (∏ j : Fin (groupNumber p n), c/Real.sqrt (groupWidth p n j.val)*Real.exp (-C*(groupU p n κ q j.val)^2)) *
      (∏ j : Fin (groupNumber p n), (endpointUpper p n κ G B₀ q (j.val+1)-endpointLower p n κ G B₀ q (j.val+1))) ≤
        (actualEndpointChain p n κ G B₀ q).toReal := by
  apply actualKilledBoxChain_lower (criticalPoint κ) (by linarith [criticalPoint_pos hκ])
    (groupNumber p n) _ _ (fun j => by have hh := hq j.val j.isLt; omega) _ _ _ _
    (fun j => endpointLower_le_upper p n κ G B₀ q (j.val+1)) 0 _ (fun _ => by positivity)
  intro j x hx x' hx'
  rw [endpointPath_lower, endpointPath_upper] at hx
  exact hminor j.val j.isLt x hx x' hx'

theorem actual_endpoint_width_cancellation (p : Parameters) (n : ℕ) (κ G B₀ c C : ℝ) (q : ℕ → ℕ)
    (hB : 0 < groupNumber p n) (hH : ∀ j < groupNumber p n, 0 < groupWidth p n j) :
    (∏ j : Fin (groupNumber p n), c/Real.sqrt (groupWidth p n j.val)*Real.exp (-C*(groupU p n κ q j.val)^2)) *
      (∏ j : Fin (groupNumber p n), (endpointUpper p n κ G B₀ q (j.val+1)-endpointLower p n κ G B₀ q (j.val+1))) =
      c^(groupNumber p n)*(2^(groupNumber p n-1)*(1/5)/Real.sqrt (groupWidth p n (groupNumber p n-1)))*
        Real.exp (-C*(∑ j ∈ Finset.range (groupNumber p n), (groupU p n κ q j)^2)) := by
  obtain ⟨B, hBeq⟩ := Nat.exists_eq_succ_of_ne_zero hB.ne'
  have hwidth (i : Fin (B+1)) :
      endpointUpper p n κ G B₀ q (i.val+1)-endpointLower p n κ G B₀ q (i.val+1) =
        if i=Fin.last B then (1/5 : ℝ) else 2*Real.sqrt (groupWidth p n i.val) := by
    unfold endpointUpper endpointLower endpointRadius
    rw [if_neg (by omega), hBeq]
    by_cases hi : i=Fin.last B
    · subst i
      simp only [Fin.val_last, ite_true]
      ring
    · have hne : i.val+1 ≠ B+1 := by
        intro hh
        apply hi
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [if_neg hne, if_neg hi, Nat.add_sub_cancel]
      ring
  rw [hBeq]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  simp_rw [hwidth]
  have hw : ∀ i : Fin (B+1), Real.sqrt (groupWidth p n i.val) ≠ 0 := by
    intro i
    exact (Real.sqrt_pos.mpr (hH i.val (by simpa only [hBeq] using i.isLt))).ne'
  have hsum : (∑ i : Fin (B+1), (groupU p n κ q i.val)^2) =
      ∑ j ∈ Finset.range (B+1), (groupU p n κ q j)^2 :=
    Fin.sum_univ_eq_sum_range (fun j => (groupU p n κ q j)^2) (B+1)
  have hh := gaussian_box_width_cancellation B c C (1/5) (fun i => Real.sqrt (groupWidth p n i.val))
    (fun i => groupU p n κ q i.val) hw
  rw [hsum] at hh
  simpa only [Fin.val_last] using hh

theorem actualEndpointChain_le_one (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hq : ∀ j < groupNumber p n, 3 ≤ groupSamples p n q j) :
    actualEndpointChain p n κ G B₀ q ≤ 1 :=
  actualKilledBoxChain_le_one (criticalPoint κ) (by linarith [criticalPoint_pos hκ])
    (groupNumber p n) _ _ (fun j => by have hh := hq j.val j.isLt; omega) _ _ _ _ 0

theorem actualEndpointChain_ne_top (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hκ : 0 < κ) (hq : ∀ j < groupNumber p n, 3 ≤ groupSamples p n q j) :
    actualEndpointChain p n κ G B₀ q ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (actualEndpointChain_le_one p n κ G B₀ q hκ hq)

#print axioms endpointLower_zero
#print axioms endpointUpper_zero
#print axioms endpointPath_lower
#print axioms endpointPath_upper
#print axioms actualEndpointChain_product_lower
#print axioms actual_endpoint_width_cancellation
#print axioms actualEndpointChain_le_one
#print axioms actualEndpointChain_ne_top

end ConditionalSpectralExtremes.CoarseBoxes
