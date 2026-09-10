import CoarseBoxCountBounds
import KilledGroupDefinitions

/-! The fine endpoint times and barriers of an actual coarse group.
The chord comparison uses the actual prefix discrepancies and frontier. -/

noncomputable section
namespace ConditionalSpectralExtremes.CoarseBoxes
open FineScales

def groupTime (p : Parameters) (n : ℕ) (q : ℕ → ℕ) (j i : ℕ) : ℕ :=
  countPrefix q (groupStart p n j+i)-countPrefix q (groupStart p n j)

def groupBarrier (p : Parameters) (n : ℕ) (κ G : ℝ) (q : ℕ → ℕ) (j i : ℕ) : ℝ :=
  fineFrontier p n κ q (groupStart p n j+i)-2*G

theorem groupTime_cast (p : Parameters) (n : ℕ) (q : ℕ → ℕ) (j i : ℕ) :
    (groupTime p n q j i : ℝ) = (countPrefix q (groupStart p n j+i) : ℝ)-
      countPrefix q (groupStart p n j) := by
  unfold groupTime
  exact Nat.cast_sub (countPrefix_mono q (by omega))

theorem groupTime_le_samples (p : Parameters) (n : ℕ) (q : ℕ → ℕ) (j i : ℕ)
    (hj : j < groupNumber p n) (hi : i ≤ groupBlocks p n j) :
    groupTime p n q j i ≤ groupSamples p n q j := by
  unfold groupTime groupSamples
  rw [group_start_step p n j hj]
  exact Nat.sub_le_sub_right (countPrefix_mono q (by omega)) _

theorem groupTime_discrepancy (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ)
    (j i : ℕ) (hH : 0 < groupWidth p n j) (hi : i ≤ groupBlocks p n j) :
    |(groupTime p n q j i : ℝ)-κ*((i : ℝ)*omega p n)| ≤
      environmentE p n κ q j*Real.sqrt (groupWidth p n j) := by
  rw [groupTime_cast]
  simpa only [localDiscrepancy, environmentE, groupWidth, mul_assoc] using!
    localDiscrepancy_bound (omega p n) κ q (groupStart p n j) (groupBlocks p n j) i hH hi

theorem actual_group_chord_bound (p : Parameters) (n : ℕ) (κ G B₀ α R : ℝ)
    (q : ℕ → ℕ) (hκ : 0 < κ) (hα : 0 < α) (hω : 0 ≤ omega p n)
    (j : ℕ) (hj : j < groupNumber p n) (hH : 0 < groupWidth p n j)
    (hq : α*groupWidth p n j ≤ (groupSamples p n q j : ℝ))
    (e e' : ℝ)
    (hleft : 2*G+R+(2/α)*environmentE p n κ q j*Real.sqrt (groupWidth p n j)/criticalPoint κ ≤
      gap p n κ G B₀ q j-e)
    (hright : 2*G+R+(2/α)*environmentE p n κ q j*Real.sqrt (groupWidth p n j)/criticalPoint κ ≤
      gap p n κ G B₀ q (j+1)-e')
    (i : ℕ) (hi : i ≤ groupBlocks p n j) :
    (boxCenter p n κ G B₀ q j+e)+
      (groupTime p n q j i : ℝ)/(groupSamples p n q j : ℝ)*
        ((boxCenter p n κ G B₀ q (j+1)+e')-(boxCenter p n κ G B₀ q j+e))+R ≤
      groupBarrier p n κ G q j i := by
  have ha : 0 ≤ (i : ℝ)*omega p n := mul_nonneg (Nat.cast_nonneg _) hω
  have haH : (i : ℝ)*omega p n ≤ groupWidth p n j :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hω
  have htq : (groupTime p n q j i : ℝ) ≤ (groupSamples p n q j : ℝ) := by
    exact_mod_cast groupTime_le_samples p n q j i hj hi
  have hE : 0 ≤ environmentE p n κ q j := le_trans (by norm_num) (localE_ge_one _ _ _ _ _)
  have hh := frontier_chord_gap_lower
    (coordinate p n (groupStart p n j)) (countPrefix q (groupStart p n j))
    ((i : ℝ)*omega p n) (groupWidth p n j) (groupTime p n q j i) (groupSamples p n q j)
    (lambda (criticalPoint κ)) (criticalPoint κ) (gap p n κ G B₀ q j)
    (gap p n κ G B₀ q (j+1)) e e' κ (environmentE p n κ q j) α G R
    (criticalPoint_pos hκ) hH hα ha haH (Nat.cast_nonneg _) htq hq hE
    (groupTime_discrepancy p n κ q j i hH hi)
    (groupSamples_discrepancy p n κ q j hj hH) hleft hright
  have haend : coordinate p n (groupStart p n j)+groupWidth p n j =
      coordinate p n (groupStart p n (j+1)) := by
    have h := group_spatial_width p n j hj
    linarith
  have hSend : (countPrefix q (groupStart p n j) : ℝ)+(groupSamples p n q j : ℝ) =
      countPrefix q (groupStart p n (j+1)) := by
    rw [groupSamples_cast p n q j hj]
    ring
  have hai : coordinate p n (groupStart p n j)+(i : ℝ)*omega p n =
      coordinate p n (groupStart p n j+i) := by
    have h := coordinate_difference p n (groupStart p n j) i
    linarith
  have hSi : (countPrefix q (groupStart p n j) : ℝ)+(groupTime p n q j i : ℝ) =
      countPrefix q (groupStart p n j+i) := by
    rw [groupTime_cast]
    ring
  rw [haend, hSend, hai, hSi] at hh
  convert! hh using 1
  · unfold boxCenter fineFrontier ConditionalSpectralAudit.BoxAlgebra.boxPoint
    ring

#print axioms groupTime_cast
#print axioms groupTime_le_samples
#print axioms groupTime_discrepancy
#print axioms actual_group_chord_bound

end ConditionalSpectralExtremes.CoarseBoxes
