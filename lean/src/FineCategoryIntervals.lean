import FullShortHarmonicLaw
import FineBlockHarmonicMass

/-! Exact bijections between actual short-length category fibers and the
literal integer harmonic intervals, including the initial low category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Set
open scoped BigOperators
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes FineScales Reservoir ReservoirScale BlockCounts

theorem fullBlockHi_eq_endpoint (p : Parameters) (n i : Nat) :
    fullBlockHi p n i=exponentialEndpoint (coordinate p n i) := by
  cases i <;> rfl

theorem fullBlockLo_positive (p : Parameters) (n i : Nat) : 0 < fullBlockLo p n i := by
  cases i with
  | zero => exact Nat.zero_lt_one
  | succ i => exact exponentialEndpoint_pos _

theorem fullBlockHi_le_cutoff (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 ≤ omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) :
    fullBlockHi p n i ≤ cutoff n+1 := by
  rw [fullBlockHi_eq_endpoint]
  unfold exponentialEndpoint
  exact Nat.succ_le_succ (Nat.floor_le_of_le (exp_coordinate_le_cutoff p n i hω hm hb (by omega)))

theorem actual_category_iff_interval (p : Parameters) (n length : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hl : 0 < length) (hb : length ≤ cutoff n) :
    category p n length=i ↔ length ∈ Finset.Ico (fullBlockLo p n i) (fullBlockHi p n i) := by
  rw [Fin.ext_iff]
  rcases i with ⟨i,hi⟩
  cases i with
  | zero =>
    rw [category_zero_iff p n length hω hm hl hb]
    simp only [fullBlockLo,fullBlockHi,fineBlockLo,coordinate_zero,exponentialEndpoint,Finset.mem_Ico]
    have hf : length ≤ ⌊Real.exp (r p n)⌋₊ ↔ (length : Real) ≤ Real.exp (r p n) :=
      Nat.le_floor_iff' hl.ne'
    rw [← hf]
    omega
  | succ i =>
    rw [category_positive_iff p n length (i+1) hω hm hl hb (by omega)]
    simp only [Nat.add_sub_cancel,fullBlockLo,fullBlockHi,fineBlockLo,fineBlockHi,exponentialEndpoint,
      Finset.mem_Ico]
    have h1 : ⌊Real.exp (coordinate p n i)⌋₊ < length ↔ Real.exp (coordinate p n i) < (length : Real) :=
      Nat.floor_lt' hl.ne'
    have h2 : length ≤ ⌊Real.exp (coordinate p n (i+1))⌋₊ ↔
        (length : Real) ≤ Real.exp (coordinate p n (i+1)) := Nat.le_floor_iff' hl.ne'
    rw [← h1,← h2]
    omega

abbrev FineCategoryFiber (p : Parameters) (n : Nat) (i : Fin (count p n+1)) :=
  {j : ShortIndex n (cutoff n) // fineCategoryBlock p n j=i}

def fineFiberLength {p : Parameters} {n : Nat} {i : Fin (count p n+1)} (j : FineCategoryFiber p n i) : Nat :=
  j.val.val.val+1

def fineCategoryIntervalEquiv (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n) :
    FineCategoryFiber p n i ≃ {length // length ∈ Finset.Ico (fullBlockLo p n i) (fullBlockHi p n i)} := by
  let f : FineCategoryFiber p n i → {length // length ∈ Finset.Ico (fullBlockLo p n i) (fullBlockHi p n i)} :=
    fun j => ⟨fineFiberLength j,(actual_category_iff_interval p n _ i hω hm (by omega)
      j.val.property).mp j.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro j l he
    have hh := congrArg Subtype.val he
    change fineFiberLength j=fineFiberLength l at hh
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    unfold fineFiberLength at hh
    omega
  · intro t
    have hlo := fullBlockLo_positive p n i
    have hhi := fullBlockHi_le_cutoff p n i hω.le hm hb
    have ht := Finset.mem_Ico.mp t.property
    have hpos : 0 < t.val := by omega
    have hcut : t.val ≤ cutoff n := by omega
    let j : ShortIndex n (cutoff n) := ⟨⟨t.val-1,by omega⟩,by change t.val-1+1 ≤ cutoff n; omega⟩
    have hjlen : j.val.val+1=t.val := by dsimp [j]; omega
    have hj : fineCategoryBlock p n j=i := by
      unfold fineCategoryBlock
      rw [hjlen]
      exact (actual_category_iff_interval p n t.val i hω hm hpos hcut).mpr t.property
    refine ⟨⟨j,hj⟩,?_⟩
    apply Subtype.ext
    exact hjlen

theorem fineFiber_sum {M : Type*} [AddCommMonoid M]
    (p : Parameters) (n : Nat) (i : Fin (count p n+1))
    (hω : 0 < omega p n) (hm : 0 < count p n) (hb : 0 < cutoff n) (hbn : cutoff n ≤ n)
    (f : Nat → M) :
    (∑ j : FineCategoryFiber p n i, f (fineFiberLength j)) =
      ∑ length ∈ Finset.Ico (fullBlockLo p n i) (fullBlockHi p n i), f length := by
  classical
  calc
    _ = ∑ t : {length // length ∈ Finset.Ico (fullBlockLo p n i) (fullBlockHi p n i)}, f t.val := by
      apply Fintype.sum_equiv (fineCategoryIntervalEquiv p n i hω hm hb hbn)
      intro j
      rfl
    _ = _ := (Finset.sum_subtype _ (by simp) f).symm

#print axioms actual_category_iff_interval
#print axioms fineCategoryIntervalEquiv
#print axioms fineFiber_sum
end ConditionalSpectralAudit.FourierHarmonic
