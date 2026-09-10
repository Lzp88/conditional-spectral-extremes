import PointwiseBridgeSplit

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def reversePath (q : ℕ) (x : Fin q → ℝ) : Fin q → ℝ := fun i => x i.rev

theorem reversePath_involutive (q : ℕ) : Function.Involutive (reversePath q) := by
  intro x
  funext i
  simp [reversePath]

theorem reversePath_sum (q : ℕ) (x : Fin q → ℝ) :
    (∑ i, reversePath q x i) = ∑ i, x i := by
  exact Equiv.sum_comp Fin.revPerm x

theorem partialSum_reverse_complement (q j : ℕ) (hj : j ≤ q) (x : Fin q → ℝ) :
    FiniteWalk.partialSum j x + FiniteWalk.partialSum (q-j) (reversePath q x) = ∑ i, x i := by
  have he : (∑ i ∈ FiniteWalk.prefixIndices q (q-j), x i.rev) =
      ∑ i ∈ (FiniteWalk.prefixIndices q j)ᶜ, x i := by
    apply Finset.sum_bij (fun i _ => i.rev)
    · intro i hi
      simp only [FiniteWalk.prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_compl, FiniteWalk.prefixIndices, Finset.mem_filter,
        Finset.mem_univ, true_and, not_lt, Fin.val_rev]
      omega
    · intro i hi k hk hik
      exact Fin.rev_injective hik
    · intro i hi
      refine ⟨i.rev, ?_, by simp⟩
      simp only [Finset.mem_compl, FiniteWalk.prefixIndices, Finset.mem_filter,
        Finset.mem_univ, true_and, not_lt] at hi
      simp only [FiniteWalk.prefixIndices, Finset.mem_filter, Finset.mem_univ,
        true_and, Fin.val_rev]
      omega
    · intro i hi
      rfl
  unfold FiniteWalk.partialSum
  dsimp only [reversePath]
  rw [he]
  exact Finset.sum_add_sum_compl _ _

theorem zero_total_reverse_partial (q j : ℕ) (hj : j ≤ q) (x : Fin q → ℝ)
    (hx : (∑ i, x i) = 0) :
    FiniteWalk.partialSum j x = -FiniteWalk.partialSum (q-j) (reversePath q x) := by
  have hh := partialSum_reverse_complement q j hj x
  rw [hx] at hh
  linarith

theorem bridgePath_reverse_partial (n j : ℕ) (hj : j ≤ n+1) (x : Fin n → ℝ) :
    FiniteWalk.partialSum j (bridgePath n 0 x) =
      -FiniteWalk.partialSum (n+1-j) (reversePath (n+1) (bridgePath n 0 x)) :=
  zero_total_reverse_partial (n+1) j hj _ (bridgePath_sum n 0 x)

theorem reversePath_measurable (q : ℕ) : Measurable (reversePath q) := by
  unfold reversePath
  fun_prop

theorem lintegral_reversePath (q : ℕ) (F : (Fin q → ℝ) → ℝ≥0∞) :
    (∫⁻ x, F (reversePath q x)) = ∫⁻ x, F x := by
  have hh := (volume_measurePreserving_piCongrLeft (fun _ : Fin q => ℝ) Fin.revPerm).lintegral_map_equiv F
  convert! hh.symm using 1
  apply lintegral_congr
  intro x
  congr 1
  funext i
  simpa only [Fin.revPerm_apply, Fin.rev_rev, reversePath] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin q => ℝ) Fin.revPerm x i.rev).symm

def bridgeReverseFree (n : ℕ) (d : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => reversePath (n+1) (bridgePath n d x) i.castSucc

theorem bridgeReverseFree_measurable (n : ℕ) (d : ℝ) : Measurable (bridgeReverseFree n d) := by
  have h := (reversePath_measurable (n+1)).comp (bridgePath_measurable n d)
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.castSucc).comp h

theorem bridgeReverseFree_path (n : ℕ) (d : ℝ) (x : Fin n → ℝ) :
    bridgePath n d (bridgeReverseFree n d x) = reversePath (n+1) (bridgePath n d x) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hs := reversePath_sum (n+1) (bridgePath n d x)
    rw [bridgePath_sum, Fin.sum_univ_castSucc] at hs
    rw [bridgePath_last]
    change d - (∑ i : Fin n, reversePath (n+1) (bridgePath n d x) i.castSucc) = _
    linarith
  · exact bridgePath_castSucc n d (bridgeReverseFree n d x) i

theorem bridgeReverseFree_involutive (n : ℕ) (d : ℝ) : Function.Involutive (bridgeReverseFree n d) := by
  intro x
  funext i
  change reversePath (n+1) (bridgePath n d (bridgeReverseFree n d x)) i.castSucc = x i
  rw [bridgeReverseFree_path, reversePath_involutive]
  exact bridgePath_castSucc n d x i

theorem bridgeReverseFree_cons (n : ℕ) (d a : ℝ) (x : Fin n → ℝ) :
    bridgeReverseFree (n+1) d (Fin.cons a x) =
      Fin.cons (d-a-∑ i, x i) (reversePath n x) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [bridgeReverseFree, reversePath, bridgePath, Fin.sum_univ_succ]
    ring
  · change bridgePath (n+1) d (Fin.cons a x) i.succ.castSucc.rev = x i.rev
    have he : i.succ.castSucc.rev = i.rev.succ.castSucc := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [he, bridgePath_castSucc, Fin.cons_succ]

def consMeasurableEquiv (n : ℕ) : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm

theorem consMeasurableEquiv_apply (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    consMeasurableEquiv n (a,x) = Fin.cons a x := by
  simp [consMeasurableEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]

theorem consMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (consMeasurableEquiv n) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm _

theorem lintegral_fin_cons (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ a : ℝ, ∫⁻ x : Fin n → ℝ, F (Fin.cons a x) := by
  rw [(consMeasurableEquiv_measurePreserving n).lintegral_map_equiv F]
  rw [Measure.volume_eq_prod]
  have hh := lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
    (fun p : ℝ × (Fin n → ℝ) => F (consMeasurableEquiv n p))
    (hF.comp (consMeasurableEquiv n).measurable).aemeasurable
  simpa only [consMeasurableEquiv_apply] using! hh

set_option maxHeartbeats 1000000 in
theorem lintegral_bridgeReverseFree (n : ℕ) (d : ℝ)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F (bridgeReverseFree n d x)) = ∫⁻ x, F x := by
  cases n with
  | zero =>
    apply lintegral_congr
    intro x
    congr 1
    exact Subsingleton.elim _ _
  | succ n =>
    rw [lintegral_fin_cons n (fun x => F (bridgeReverseFree (n+1) d x))
      (hF.comp (bridgeReverseFree_measurable _ d)), lintegral_fin_cons n F hF]
    simp only [bridgeReverseFree_cons]
    have hc : Measurable (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
      simpa only [← consMeasurableEquiv_apply] using (consMeasurableEquiv n).measurable
    have hleft : Measurable (fun p : ℝ × (Fin n → ℝ) =>
        F (Fin.cons (d-p.1-∑ i, p.2 i) (reversePath n p.2))) := by
      have hp : Measurable (fun p : ℝ × (Fin n → ℝ) =>
          (d-p.1-∑ i, p.2 i, reversePath n p.2)) :=
        Measurable.prodMk (by fun_prop) ((reversePath_measurable n).comp measurable_snd)
      convert! hF.comp (hc.comp hp)
    have hright : Measurable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2)) := by
      simpa only [Function.comp_def] using! hF.comp hc
    rw [lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
      (f := fun (a : ℝ) (x : Fin n → ℝ) => F (Fin.cons (d-a-∑ i, x i) (reversePath n x)))
      hleft.aemeasurable,
      lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
        (f := fun (a : ℝ) (x : Fin n → ℝ) => F (Fin.cons a x)) hright.aemeasurable]
    calc
      _ = ∫⁻ x : Fin n → ℝ, ∫⁻ a : ℝ, F (Fin.cons a (reversePath n x)) := by
        apply lintegral_congr
        intro x
        have hg : Measurable (fun a : ℝ => F (Fin.cons a (reversePath n x))) :=
          hF.comp (hc.comp (measurable_id.prodMk measurable_const))
        have hh := (Measure.measurePreserving_sub_left (volume : Measure ℝ) (d-∑ i, x i)).lintegral_comp hg
        convert! hh using 1
        apply lintegral_congr
        intro a
        congr 2
        ring
      _ = _ := by
        simpa only using! lintegral_reversePath n (fun x => ∫⁻ a : ℝ, F (Fin.cons a x))

theorem pointwiseBridge_reverse (f : ℝ → ℝ) (hf : Measurable f)
    (n : ℕ) (d : ℝ) (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) :
    pointwiseBridge f n d (reversePath (n+1) ⁻¹' E) = pointwiseBridge f n d E := by
  classical
  unfold pointwiseBridge
  rw [← lintegral_bridgeReverseFree n d _ (pointwiseBridge_integrand_measurable f hf n d E hE)]
  apply lintegral_congr
  intro x
  rw [bridgeReverseFree_path]
  by_cases hx : reversePath (n+1) (bridgePath n d x) ∈ E
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show bridgePath n d x ∈ reversePath (n+1) ⁻¹' E from hx)]
    exact (Equiv.prod_comp Fin.revPerm (fun i => ENNReal.ofReal (f (bridgePath n d x i)))).symm
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show bridgePath n d x ∉ reversePath (n+1) ⁻¹' E from hx)]

#print axioms reversePath_involutive
#print axioms reversePath_sum
#print axioms partialSum_reverse_complement
#print axioms zero_total_reverse_partial
#print axioms bridgePath_reverse_partial
#print axioms reversePath_measurable
#print axioms lintegral_reversePath
#print axioms bridgeReverseFree_measurable
#print axioms bridgeReverseFree_path
#print axioms bridgeReverseFree_involutive
#print axioms bridgeReverseFree_cons
#print axioms consMeasurableEquiv_apply
#print axioms consMeasurableEquiv_measurePreserving
#print axioms lintegral_fin_cons
#print axioms lintegral_bridgeReverseFree
#print axioms pointwiseBridge_reverse

end ConditionalSpectralExtremes
