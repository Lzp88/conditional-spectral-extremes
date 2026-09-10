import ReservoirScale
import DyadicGeometry

/-! Literal fine-scale and regular-environment definitions of Section 3.
Coarse group indices are zero based here; the list itself is produced by
the corrected two-ended dyadic algorithm. The formulas are defined even
for small n; meaningful geometric statements explicitly require their
positive-scale hypotheses until the large-n bounds are proved. -/

noncomputable section
open scoped BigOperators
open Set

namespace ConditionalSpectralExtremes.FineScales

structure Parameters where
  A₀ : ℝ
  rStar : ℝ
  D₀ : ℝ

def h (p : Parameters) (n : ℕ) : ℝ := p.A₀*ReservoirScale.ell n
def r (p : Parameters) (n : ℕ) : ℝ := p.rStar*ReservoirScale.ell n
def aStar (n : ℕ) : ℝ := Real.log (ReservoirScale.cutoff n)
def count (p : Parameters) (n : ℕ) : ℕ := ⌈(aStar n-r p n)/h p n⌉₊
def omega (p : Parameters) (n : ℕ) : ℝ := (aStar n-r p n)/count p n
def coordinate (p : Parameters) (n i : ℕ) : ℝ := r p n+(i : ℝ)*omega p n
def baseWidth (p : Parameters) (n : ℕ) : ℝ := (r p n)^2/(p.D₀*Real.log (ReservoirScale.ell n))
def baseBlocks (p : Parameters) (n : ℕ) : ℕ := ⌈baseWidth p n/omega p n⌉₊
def groups (p : Parameters) (n : ℕ) : List ℕ :=
  ConditionalSpectralAudit.DyadicGrouping.dyadicGroups (count p n) (baseBlocks p n)
def groupNumber (p : Parameters) (n : ℕ) : ℕ := (groups p n).length
def groupStart (p : Parameters) (n j : ℕ) : ℕ := ((groups p n).take j).sum
def groupBlocks (p : Parameters) (n j : ℕ) : ℕ := ((groups p n)[j]?).getD 0
def groupWidth (p : Parameters) (n j : ℕ) : ℝ := (groupBlocks p n j : ℝ)*omega p n

/-- q(i) is the count in fine block i, so q(0) is the separately omitted
initial block and contributes nothing to the middle-field prefixes. -/
def countPrefix (q : ℕ → ℕ) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, q (j+1)

def localDiscrepancy (ω κ : ℝ) (q : ℕ → ℕ) (start offset : ℕ) : ℝ :=
  (countPrefix q (start+offset) : ℝ)-countPrefix q start-κ*(offset : ℝ)*ω

def localMaximum (ω κ : ℝ) (q : ℕ → ℕ) (start width : ℕ) : ℝ :=
  (Finset.range (width+1)).sup' (by exact ⟨0, Finset.mem_range.mpr (by omega)⟩)
    (fun i => |localDiscrepancy ω κ q start i|)

def localE (ω κ : ℝ) (q : ℕ → ℕ) (start width : ℕ) : ℝ :=
  1+localMaximum ω κ q start width/Real.sqrt ((width : ℝ)*ω)

def environmentE (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  localE (omega p n) κ q (groupStart p n j) (groupBlocks p n j)

def paddedE (p : Parameters) (n : ℕ) (κ : ℝ) (q : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j=0 ∨ groupNumber p n<j then 1 else environmentE p n κ q (j-1)

def Regular (p : Parameters) (n : ℕ) (κ η K_E C_E : ℝ) (q : ℕ → ℕ) : Prop :=
  (∀ i ∈ Finset.range (count p n), κ/2*omega p n ≤ (q (i+1) : ℝ) ∧
    (q (i+1) : ℝ) ≤ (κ+η)*omega p n) ∧
  (∀ j ∈ Finset.range (groupNumber p n),
    environmentE p n κ q j ≤ K_E*Real.sqrt (Real.log (ReservoirScale.ell n))) ∧
  (∑ j ∈ Finset.range (groupNumber p n), (environmentE p n κ q j)^2) ≤ C_E*groupNumber p n

/-- The category label for a cycle length. For positive fine scales this
is exactly the block specified by the manuscript's exponential endpoints.
The cap gives a total finite-valued definition before those bounds. -/
def category (p : Parameters) (n length : ℕ) : Fin (count p n+1) :=
  ⟨min (count p n) ⌈(Real.log length-r p n)/omega p n⌉₊,
    Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

theorem coordinate_zero (p : Parameters) (n : ℕ) : coordinate p n 0 = r p n := by
  simp [coordinate]

theorem coordinate_last (p : Parameters) (n : ℕ) (hc : 0 < count p n) :
    coordinate p n (count p n) = aStar n := by
  have hc' : (count p n : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold coordinate omega
  field_simp
  ring

theorem coordinate_difference (p : Parameters) (n start offset : ℕ) :
    coordinate p n (start+offset)-coordinate p n start = (offset : ℝ)*omega p n := by
  simp only [coordinate, Nat.cast_add]
  ring

theorem group_start_zero (p : Parameters) (n : ℕ) : groupStart p n 0 = 0 := by
  simp [groupStart]

theorem group_start_step (p : Parameters) (n j : ℕ) (hj : j < groupNumber p n) :
    groupStart p n (j+1) = groupStart p n j+groupBlocks p n j := by
  have hj' : j < (groups p n).length := hj
  simp only [groupStart, groupBlocks, List.take_succ_eq_append_getElem hj',
    List.sum_append, List.sum_cons, List.sum_nil, add_zero, List.getElem?_eq_getElem hj', Option.getD_some]

theorem group_spatial_width (p : Parameters) (n j : ℕ) (hj : j < groupNumber p n) :
    coordinate p n (groupStart p n (j+1))-coordinate p n (groupStart p n j) =
      groupWidth p n j := by
  rw [group_start_step p n j hj, coordinate_difference]
  rfl

theorem countPrefix_zero (q : ℕ → ℕ) : countPrefix q 0 = 0 := by simp [countPrefix]

theorem countPrefix_step (q : ℕ → ℕ) (i : ℕ) :
    countPrefix q (i+1) = countPrefix q i+q (i+1) := by
  exact Finset.sum_range_succ (fun j => q (j+1)) i

theorem countPrefix_mono (q : ℕ → ℕ) : Monotone (countPrefix q) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [countPrefix_step]
  omega

theorem localMaximum_nonneg (ω κ : ℝ) (q : ℕ → ℕ) (start width : ℕ) :
    0 ≤ localMaximum ω κ q start width := by
  exact (abs_nonneg (localDiscrepancy ω κ q start 0)).trans
    (Finset.le_sup' (fun i => |localDiscrepancy ω κ q start i|)
      (Finset.mem_range.mpr (show 0<width+1 by omega)))

theorem localE_ge_one (ω κ : ℝ) (q : ℕ → ℕ) (start width : ℕ) :
    1 ≤ localE ω κ q start width := by
  unfold localE
  have hh := div_nonneg (localMaximum_nonneg ω κ q start width)
    (Real.sqrt_nonneg ((width : ℝ)*ω))
  linarith

theorem localDiscrepancy_bound (ω κ : ℝ) (q : ℕ → ℕ) (start width i : ℕ)
    (hwidth : 0 < (width : ℝ)*ω) (hi : i ≤ width) :
    |localDiscrepancy ω κ q start i| ≤ localE ω κ q start width*Real.sqrt ((width : ℝ)*ω) := by
  have hsup : |localDiscrepancy ω κ q start i| ≤ localMaximum ω κ q start width :=
    Finset.le_sup' (fun j => |localDiscrepancy ω κ q start j|)
      (Finset.mem_range.mpr (show i<width+1 by omega))
  have hs : 0 < Real.sqrt ((width : ℝ)*ω) := Real.sqrt_pos.mpr hwidth
  have heq : localE ω κ q start width*Real.sqrt ((width : ℝ)*ω) =
      Real.sqrt ((width : ℝ)*ω)+localMaximum ω κ q start width := by
    unfold localE
    field_simp
  rw [heq]
  linarith

#print axioms coordinate_zero
#print axioms coordinate_last
#print axioms coordinate_difference
#print axioms group_start_zero
#print axioms group_start_step
#print axioms group_spatial_width
#print axioms countPrefix_zero
#print axioms countPrefix_step
#print axioms countPrefix_mono
#print axioms localMaximum_nonneg
#print axioms localE_ge_one
#print axioms localDiscrepancy_bound

end ConditionalSpectralExtremes.FineScales
