import CoarseBoxDefinitions
import FineGroupWidthGeometry

/-! The manuscript's actual endpoint boxes, including the singleton
initial box and terminal radius 1/10. All offsets used in the analytic
kernel inequalities are consequences of membership in these boxes. -/

noncomputable section
open Set
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

def endpointRadius (p : Parameters) (n j : ℕ) : ℝ :=
  if j=0 then 0 else if j=groupNumber p n then 1/10 else Real.sqrt (groupWidth p n (j-1))

def endpointLower (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  boxCenter p n κ G B₀ q j-endpointRadius p n j

def endpointUpper (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  boxCenter p n κ G B₀ q j+endpointRadius p n j

theorem endpointRadius_nonneg (p : Parameters) (n j : ℕ) : 0 ≤ endpointRadius p n j := by
  unfold endpointRadius
  split
  · exact le_rfl
  · split
    · norm_num
    · exact Real.sqrt_nonneg _

theorem endpointLower_le_upper (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ) (j : ℕ) :
    endpointLower p n κ G B₀ q j ≤ endpointUpper p n κ G B₀ q j := by
  unfold endpointLower endpointUpper
  linarith [endpointRadius_nonneg p n j]

theorem endpoint_box_offset (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (j : ℕ) (x : ℝ) (hx : x ∈ Icc (endpointLower p n κ G B₀ q j) (endpointUpper p n κ G B₀ q j)) :
    |x-boxCenter p n κ G B₀ q j| ≤ endpointRadius p n j := by
  apply abs_le.mpr
  unfold endpointLower endpointUpper at hx
  constructor <;> linarith [hx.1, hx.2]

theorem right_endpointRadius_le_sqrt (p : Parameters) (n j : ℕ) (_hj : j < groupNumber p n)
    (hH : 1 ≤ groupWidth p n j) : endpointRadius p n (j+1) ≤ Real.sqrt (groupWidth p n j) := by
  have hsqrt : 1 ≤ Real.sqrt (groupWidth p n j) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hH
  unfold endpointRadius
  rw [if_neg (by omega)]
  split
  · linarith
  · simp only [Nat.add_sub_cancel]
    exact le_rfl

theorem left_endpointRadius_le_two_sqrt (p : Parameters) (n j : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (hj : j < groupNumber p n) :
    endpointRadius p n j ≤ 2*Real.sqrt (groupWidth p n j) := by
  by_cases hj0 : j=0
  · simp only [endpointRadius, hj0, ite_true]
    positivity
  · have hs := (sqrt_groupWidth_adjacent p n (j-1) hv hm hω (by omega)).1
    rw [show j-1+1=j by omega] at hs
    simpa only [endpointRadius, if_neg hj0, if_neg (show j ≠ groupNumber p n by omega)] using hs

theorem actual_endpoint_offsets (p : Parameters) (n : ℕ) (κ G B₀ : ℝ) (q : ℕ → ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (hω : 0 ≤ omega p n) (j : ℕ) (hj : j < groupNumber p n)
    (hH : 1 ≤ groupWidth p n j) (x x' : ℝ)
    (hx : x ∈ Icc (endpointLower p n κ G B₀ q j) (endpointUpper p n κ G B₀ q j))
    (hx' : x' ∈ Icc (endpointLower p n κ G B₀ q (j+1)) (endpointUpper p n κ G B₀ q (j+1))) :
    |x-boxCenter p n κ G B₀ q j| ≤ 2*Real.sqrt (groupWidth p n j) ∧
    |x'-boxCenter p n κ G B₀ q (j+1)| ≤ Real.sqrt (groupWidth p n j) ∧
    (j=0 → x-boxCenter p n κ G B₀ q j=0) ∧
    (j+1=groupNumber p n → |x'-boxCenter p n κ G B₀ q (j+1)| ≤ 1/10) := by
  have he := endpoint_box_offset p n κ G B₀ q j x hx
  have he' := endpoint_box_offset p n κ G B₀ q (j+1) x' hx'
  refine ⟨he.trans (left_endpointRadius_le_two_sqrt p n j hv hm hω hj),
    he'.trans (right_endpointRadius_le_sqrt p n j hj hH), ?_, ?_⟩
  · intro hj0
    have hrad : endpointRadius p n j=0 := by simp [endpointRadius, hj0]
    rw [hrad] at he
    exact abs_nonpos_iff.mp he
  · intro hjlast
    have hrad : endpointRadius p n (j+1)=1/10 := by
      unfold endpointRadius
      rw [if_neg (by omega), if_pos hjlast]
    rwa [hrad] at he'

#print axioms endpointRadius_nonneg
#print axioms endpointLower_le_upper
#print axioms endpoint_box_offset
#print axioms right_endpointRadius_le_sqrt
#print axioms left_endpointRadius_le_two_sqrt
#print axioms actual_endpoint_offsets

end ConditionalSpectralExtremes.CoarseBoxes
