import CoarsePoissonEnvironment

/-! Actual single-group and simultaneous coarse-environment tails under
the Poisson product law, with the literal coarse count coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales

theorem coarsePoisson_environment_tail (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ C : ℝ) (hC : 1 ≤ C) (α : Option (Fin (count p n+1)) → ℝ≥0)
    (j : Fin (groupNumber p n)) (hH : 0 < groupWidth p n j)
    (hα : 0 < ∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ))
    (hαH : (∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ)) ≤ C*groupWidth p n j)
    (hδ : (∑ i, |(α (coarseCountIndex p n hv hm j i) : ℝ)-κ*omega p n|) ≤ Real.sqrt (groupWidth p n j))
    (x : ℝ) (hx : 2 ≤ x) (hxH : x-2 ≤ Real.sqrt (groupWidth p n j)) :
    (Measure.pi (fun i => poissonMeasure (α i))).real {X | x ≤ coarseCountEnvironment p n κ j X} ≤
      2*Real.exp (-(x-2)^2/(4*C)) := by
  let e := coarseCountIndex p n hv hm j
  have hm' : Measurable (fun X : Option (Fin (count p n+1)) → ℕ =>
      fun i : Fin (groupBlocks p n j) => X (e i)) := .of_discrete
  have hs' : MeasurableSet {X : Fin (groupBlocks p n j) → ℕ |
      x ≤ countPathEnvironment (groupWidth p n j) (κ*omega p n) X} := .of_discrete
  have hprob : (Measure.pi (fun i => poissonMeasure (α i))).real {X | x ≤ coarseCountEnvironment p n κ j X} =
      (poissonProductLaw (fun i => α (e i))).real
        {X | x ≤ countPathEnvironment (groupWidth p n j) (κ*omega p n) X} := by
    rw [← poisson_subvector_map α e]
    simp only [measureReal_def]
    rw [Measure.map_apply hm' hs']
    congr 2
    ext X
    change (x ≤ coarseCountEnvironment p n κ j X) ↔
      (x ≤ countPathEnvironment (groupWidth p n j) (κ*omega p n) (fun i => X (e i)))
    rw [coarseCountEnvironment_eq p n hv hm κ j]
  rw [hprob]
  exact poisson_countPathEnvironment_tail _ _ _ C hH hC hα hαH hδ x hx hxH

theorem coarsePoisson_environment_max_tail (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ C : ℝ) (hC : 1 ≤ C) (α : Option (Fin (count p n+1)) → ℝ≥0)
    (hH : ∀ j : Fin (groupNumber p n), 0 < groupWidth p n j)
    (hα : ∀ j : Fin (groupNumber p n), 0 < ∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ))
    (hαH : ∀ j : Fin (groupNumber p n),
      (∑ i, (α (coarseCountIndex p n hv hm j i) : ℝ)) ≤ C*groupWidth p n j)
    (hδ : ∀ j : Fin (groupNumber p n),
      (∑ i, |(α (coarseCountIndex p n hv hm j i) : ℝ)-κ*omega p n|) ≤ Real.sqrt (groupWidth p n j))
    (x : ℝ) (hx : 2 ≤ x) (hxH : ∀ j : Fin (groupNumber p n), x-2 ≤ Real.sqrt (groupWidth p n j)) :
    (Measure.pi (fun i => poissonMeasure (α i))).real
      {X | ∃ j : Fin (groupNumber p n), x ≤ coarseCountEnvironment p n κ j X} ≤
        2*(groupNumber p n : ℝ)*Real.exp (-(x-2)^2/(4*C)) := by
  have he : {X | ∃ j : Fin (groupNumber p n), x ≤ coarseCountEnvironment p n κ j X} =
      ⋃ j : Fin (groupNumber p n), {X | x ≤ coarseCountEnvironment p n κ j X} := by ext X; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    coarsePoisson_environment_tail p n hv hm κ C hC α j (hH j) (hα j) (hαH j) (hδ j) x hx (hxH j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  calc
    _ ≤ (groupNumber p n : ℝ)*(2*Real.exp (-(x-2)^2/(4*C))) := hh
    _ = _ := by ring

#print axioms coarsePoisson_environment_tail
#print axioms coarsePoisson_environment_max_tail

end ConditionalSpectralExtremes.BlockCounts
