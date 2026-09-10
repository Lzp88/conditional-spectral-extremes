import PermutationProfile

/-! Genuine SameCycle quotient classes are in bijection with nontrivial
cycle factors together with individual fixed points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Equiv Set
namespace ConditionalSpectralExtremes
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev PermutationOrbit (σ : Perm α) := Quotient (Perm.SameCycle.setoid σ)

def permutationOrbitClass (σ : Perm α) (x : α) : PermutationOrbit σ :=
  Quotient.mk (Perm.SameCycle.setoid σ) x

abbrev PermutationOrbitFiber (σ : Perm α) (q : PermutationOrbit σ) :=
  {x : α // permutationOrbitClass σ x=q}

abbrev PermutationCycleLabels (σ : Perm α) :=
  (↑σ.cycleFactorsFinset) ⊕ (Function.fixedPoints σ)

def permutationCycleLabel (σ : Perm α) (x : α) : PermutationCycleLabels σ :=
  if hx : σ x=x then Sum.inr ⟨x,hx⟩ else
    Sum.inl ⟨σ.cycleOf x,Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hx)⟩

omit [Fintype α] [DecidableEq α] in
theorem permutationOrbitClass_eq_iff (σ : Perm α) (x y : α) :
    permutationOrbitClass σ x=permutationOrbitClass σ y ↔ σ.SameCycle x y := Quotient.eq

theorem permutationCycleLabel_eq_iff (σ : Perm α) (x y : α) :
    permutationCycleLabel σ x=permutationCycleLabel σ y ↔ σ.SameCycle x y := by
  by_cases hx : σ x=x <;> by_cases hy : σ y=y
  · simp only [permutationCycleLabel,dif_pos hx,dif_pos hy,Sum.inr.injEq,Subtype.mk.injEq]
    exact ⟨fun h => h.sameCycle σ,fun h => h.eq_of_left hx⟩
  · simp only [permutationCycleLabel,dif_pos hx,dif_neg hy,Sum.inr_ne_inl,false_iff]
    exact fun h => hy (h.apply_eq_self_iff.mp hx)
  · simp only [permutationCycleLabel,dif_neg hx,dif_pos hy,Sum.inl_ne_inr,false_iff]
    exact fun h => hx (h.apply_eq_self_iff.mpr hy)
  · simp only [permutationCycleLabel,dif_neg hx,dif_neg hy,Sum.inl.injEq,Subtype.mk.injEq]
    exact (Perm.sameCycle_iff_cycleOf_eq_of_mem_support (Perm.mem_support.mpr hx)
      (Perm.mem_support.mpr hy)).symm

theorem permutationCycleLabel_surjective (σ : Perm α) : Function.Surjective (permutationCycleLabel σ) := by
  intro l
  cases l with
  | inr x => exact ⟨x.val,by simp only [permutationCycleLabel,dif_pos (show σ x.val=x.val from x.property)]⟩
  | inl c =>
    obtain ⟨x,hx⟩ := (Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
    have hσx : σ x≠x := Perm.mem_support.mp (Perm.mem_cycleFactorsFinset_support_le c.property hx)
    refine ⟨x,?_⟩
    simp only [permutationCycleLabel,dif_neg hσx,Sum.inl.injEq]
    exact Subtype.ext (Perm.cycle_is_cycleOf hx c.property).symm

def permutationOrbitLabel (σ : Perm α) : PermutationOrbit σ → PermutationCycleLabels σ :=
  Quotient.lift (permutationCycleLabel σ) (fun x y h => (permutationCycleLabel_eq_iff σ x y).mpr h)

theorem permutationOrbitLabel_class (σ : Perm α) (x : α) :
    permutationOrbitLabel σ (permutationOrbitClass σ x)=permutationCycleLabel σ x := rfl

theorem permutationOrbitLabel_bijective (σ : Perm α) : Function.Bijective (permutationOrbitLabel σ) := by
  constructor
  · intro q r
    induction q using Quotient.inductionOn with | h x =>
      induction r using Quotient.inductionOn with | h y =>
        intro hh
        apply Quotient.sound
        exact (permutationCycleLabel_eq_iff σ x y).mp hh
  · intro l
    obtain ⟨x,hx⟩ := permutationCycleLabel_surjective σ l
    exact ⟨permutationOrbitClass σ x,hx⟩

def permutationOrbitLabelEquiv (σ : Perm α) : PermutationOrbit σ ≃ PermutationCycleLabels σ :=
  Equiv.ofBijective (permutationOrbitLabel σ) (permutationOrbitLabel_bijective σ)

theorem permutationOrbitLabelEquiv_class (σ : Perm α) (x : α) :
    permutationOrbitLabelEquiv σ (permutationOrbitClass σ x)=permutationCycleLabel σ x := rfl

theorem permutationCycleLabel_inl_iff (σ : Perm α) (x : α) (c : ↑σ.cycleFactorsFinset) :
    permutationCycleLabel σ x=Sum.inl c ↔ x ∈ c.val.support := by
  by_cases hx : σ x=x
  · simp only [permutationCycleLabel,dif_pos hx,Sum.inr_ne_inl,false_iff]
    intro hh
    exact (Perm.mem_support.mp (Perm.mem_cycleFactorsFinset_support_le c.property hh)) hx
  · simp only [permutationCycleLabel,dif_neg hx,Sum.inl.injEq,Subtype.ext_iff]
    exact eq_comm.trans (Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c.val c.property x)

theorem permutationCycleLabel_inr_iff (σ : Perm α) (x : α) (y : Function.fixedPoints σ) :
    permutationCycleLabel σ x=Sum.inr y ↔ x=y.val := by
  by_cases hx : σ x=x
  · simp only [permutationCycleLabel,dif_pos hx,Sum.inr.injEq,Subtype.ext_iff]
  · simp only [permutationCycleLabel,dif_neg hx,Sum.inl_ne_inr,false_iff]
    intro hh
    exact hx (hh ▸ y.property)

#print axioms permutationOrbitLabelEquiv
#print axioms permutationCycleLabel_inl_iff
end ConditionalSpectralExtremes
