import PermutationProfileWeights
import ProfileNormalization

/-! Exact cardinalities of the fibers of the actual permutation profile.
The extension from realized fibers uses the already proved total profile
normalization and positivity, so no cycle-type existence is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace ConditionalSpectralExtremes

theorem profileParts_injective (n : Nat) : Function.Injective (@profileParts n) := by
  intro c d h
  funext j
  apply Fin.ext
  have hh := congrArg (fun m : Multiset Nat => m.count (j.val+1)) h
  simpa only [profileParts_count] using hh

theorem permutationConfiguration_eq_iff_partition {n : Nat} (σ τ : Equiv.Perm (Fin n)) :
    permutationConfiguration σ=permutationConfiguration τ ↔ σ.partition=τ.partition := by
  constructor
  · intro h
    apply Nat.Partition.ext
    simpa only [permutationConfiguration_parts] using congrArg profileParts h
  · intro h
    apply profileParts_injective n
    rw [permutationConfiguration_parts,permutationConfiguration_parts,h]

def permutationProfileCard (n : Nat) (c : Configuration n) : Nat :=
  Nat.card {σ : Equiv.Perm (Fin n) // permutationConfiguration σ=c}

theorem permutationProfileCard_actual_mul {n : Nat} (σ : Equiv.Perm (Fin n)) :
    permutationProfileCard n (permutationConfiguration σ)*
      profileDenominator (permutationConfiguration σ)=n.factorial := by
  have hset : {τ : Equiv.Perm (Fin n) | IsConj σ τ}=
      {τ | permutationConfiguration τ=permutationConfiguration σ} := by
    ext τ
    rw [Set.mem_ofPred_eq,Set.mem_ofPred_eq,permutationConfiguration_eq_iff_partition,
      Equiv.Perm.partition_eq_of_isConj]
    exact eq_comm
  have hh := Equiv.Perm.card_isConj_mul_eq σ
  rw [hset,Fintype.card_fin,← permutation_profile_denominator σ] at hh
  exact hh

theorem permutationProfileCard_actual_probability {n : Nat} (σ : Equiv.Perm (Fin n)) :
    (permutationProfileCard n (permutationConfiguration σ) : Real)/(n.factorial : Real)=
      profileWeight (permutationConfiguration σ) := by
  have hh : (permutationProfileCard n (permutationConfiguration σ) : Real)*
      (profileDenominator (permutationConfiguration σ) : Real)=(n.factorial : Real) := by
    exact_mod_cast permutationProfileCard_actual_mul σ
  have hn : (n.factorial : Real)≠0 := by positivity
  have hD : (profileDenominator (permutationConfiguration σ) : Real)≠0 := by
    intro h
    rw [h,mul_zero] at hh
    exact hn hh.symm
  rw [profileWeight_eq_inv_denominator]
  apply (div_eq_iff hn).mpr
  rw [← hh]
  field_simp

theorem permutationProfileCard_sum (n : Nat) : (∑ c : Configuration n, permutationProfileCard n c)=n.factorial := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (f := @permutationConfiguration n) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  simpa only [permutationProfileCard,Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.card_univ,Fintype.card_perm,Fintype.card_fin] using hh.symm

theorem hReal_eval_one (n : Nat) : (ProfileNormalization.hReal n).eval 1=1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [ProfileNormalization.hReal,ConditionalSpectralAudit.CoefficientAlgebra.h]
    | succ m =>
      have hh := ProfileNormalization.hReal_eval_recurrence 1 m
      have hs : (∑ q ∈ Finset.range (m+1), (ProfileNormalization.hReal q).eval 1)=(m+1 : Nat) := by
        simp only [Finset.sum_congr rfl (fun q hq => ih q (Finset.mem_range.mp hq)),
          Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
      rw [hs,one_mul] at hh
      have hn : (0 : Real)<(m+1 : Nat) := by positivity
      nlinarith

theorem profileWeight_sum_size (n : Nat) :
    (∑ c : Configuration n, if totalSize c=n then profileWeight c else 0)=1 := by
  have hh := ProfileNormalization.ewensPartition_eq_hReal_eval 1 n
  rw [hReal_eval_one] at hh
  simpa only [ewensPartition,ewensMass,and_true,ewensProfileWeight_factor,one_pow,one_mul] using hh

theorem permutationProfileCard_probability (n : Nat) (c : Configuration n) :
    (permutationProfileCard n c : Real)/(n.factorial : Real)=
      if totalSize c=n then profileWeight c else 0 := by
  classical
  let Q : Configuration n → Real := fun c => (permutationProfileCard n c : Real)/(n.factorial : Real)
  let W : Configuration n → Real := fun c => if totalSize c=n then profileWeight c else 0
  have hle (c : Configuration n) : Q c ≤ W c := by
    by_cases hc : ∃ σ : Equiv.Perm (Fin n), permutationConfiguration σ=c
    · obtain ⟨σ,rfl⟩ := hc
      dsimp [Q,W]
      rw [permutationProfileCard_actual_probability,if_pos (permutationConfiguration_size σ)]
    · have hz : permutationProfileCard n c=0 := by
        apply Nat.card_eq_zero.mpr
        left
        exact ⟨fun σ => hc ⟨σ.val,σ.property⟩⟩
      dsimp [Q,W]
      rw [hz,Nat.cast_zero,zero_div]
      split_ifs
      · exact (profileWeight_pos _).le
      · exact le_rfl
  have hQ : (∑ c, Q c)=1 := by
    simp only [Q,← Finset.sum_div,← Nat.cast_sum,permutationProfileCard_sum,
      div_self (by positivity : (n.factorial : Real)≠0)]
  have hW : (∑ c, W c)=1 := profileWeight_sum_size n
  exact (Finset.sum_eq_sum_iff_of_le (fun c _ => hle c)).mp (hQ.trans hW.symm) c (Finset.mem_univ c)

theorem permutationProfileCard_eq (n : Nat) (c : Configuration n) (hc : totalSize c=n) :
    (permutationProfileCard n c : Real)=(n.factorial : Real)*profileWeight c := by
  have hh := permutationProfileCard_probability n c
  rw [if_pos hc,div_eq_iff (by positivity : (n.factorial : Real)≠0)] at hh
  simpa only [mul_comm] using hh

#print axioms permutationProfileCard_actual_probability
#print axioms permutationProfileCard_probability
#print axioms permutationProfileCard_eq
end ConditionalSpectralExtremes
