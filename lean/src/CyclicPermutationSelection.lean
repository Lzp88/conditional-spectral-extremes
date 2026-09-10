import Mathlib

/-! In a single actual permutation orbit, a permutation selecting only
the diagonal or the cycle edge must select the whole cycle or no edge. -/
noncomputable section
namespace ConditionalSpectralExtremes
open Equiv

theorem permutation_cycle_selection {α : Type*} [Fintype α]
    (σ ρ : Perm α) (hcycle : ∀ x y, σ.SameCycle x y)
    (hselect : ∀ x, ρ x=x ∨ ρ x=σ x) : ρ=1 ∨ ρ=σ := by
  classical
  by_cases hρ : ρ=1
  · exact Or.inl hρ
  right
  obtain ⟨x,hx⟩ : ∃ x, ρ x≠x := by
    by_contra hh
    apply hρ
    ext x
    exact not_not.mp ((not_exists.mp hh) x)
  have hρx : ρ x=σ x := (hselect x).resolve_left hx
  have hσx : σ x≠x := by rwa [← hρx]
  have hσ (y : α) : σ y≠y := by
    intro hy
    exact hσx ((hcycle x y).apply_eq_self_iff.mpr hy)
  have hstep (y : α) (hy : ρ y=σ y) : ρ (σ y)=σ (σ y) := by
    rcases hselect (σ y) with h | h
    · have hh : ρ (σ y)=ρ y := h.trans hy.symm
      exact False.elim (hσ y (ρ.injective hh))
    · exact h
  have hpow (k : Nat) : ρ ((σ^k) x)=σ ((σ^k) x) := by
    induction k with
    | zero => simpa only [pow_zero,Perm.one_apply] using hρx
    | succ k ih =>
      simpa only [pow_succ',Perm.mul_apply] using hstep ((σ^k) x) ih
  ext y
  obtain ⟨k,hk⟩ := (hcycle x y).exists_nat_pow_eq
  rw [← hk]
  exact hpow k

#print axioms permutation_cycle_selection
end ConditionalSpectralExtremes
