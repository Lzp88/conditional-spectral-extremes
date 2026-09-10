import PointwiseBridgeDefinitions
import TiltedDensityPowers

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

def splitFinMeasurableEquiv (m n : ℕ) :
    (Fin (m+n) → ℝ) ≃ᵐ (Fin m → ℝ) × (Fin n → ℝ) where
  toFun x := (fun i => x (i.castAdd n), fun i => x (i.natAdd m))
  invFun y := Fin.append y.1 y.2
  left_inv x := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  right_inv y := by simp
  measurable_toFun := by
    change Measurable (fun x : Fin (m+n) → ℝ =>
      (fun i : Fin m => x (i.castAdd n), fun i : Fin n => x (i.natAdd m)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun y : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append y.1 y.2)
    apply measurable_pi_lambda
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right] <;> fun_prop

theorem splitFinMeasurableEquiv_symm_apply (m n : ℕ)
    (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    (splitFinMeasurableEquiv m n).symm x = Fin.append x.1 x.2 := rfl

theorem finAppend_measurePreserving (m n : ℕ) :
    MeasurePreserving (splitFinMeasurableEquiv m n).symm := by
  refine ⟨(splitFinMeasurableEquiv m n).symm.measurable, ?_⟩
  apply (Measure.pi_eq (μ := fun _ : Fin (m+n) => (volume : Measure ℝ)) ?_).symm
  intro s hs
  rw [Measure.map_apply (splitFinMeasurableEquiv m n).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have he : (splitFinMeasurableEquiv m n).symm ⁻¹' univ.pi s =
      (univ.pi (fun i : Fin m => s (i.castAdd n))) ×ˢ
        (univ.pi (fun i : Fin n => s (i.natAdd m))) := by
    ext x
    simp only [mem_preimage, mem_univ_pi, splitFinMeasurableEquiv_symm_apply,
      mem_prod, Fin.forall_fin_add, Fin.append_left, Fin.append_right]
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi, Fin.prod_univ_add]

theorem lintegral_fin_append (m n : ℕ) (F : (Fin (m+n) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ x : Fin m → ℝ, ∫⁻ y : Fin n → ℝ, F (Fin.append x y) := by
  rw [(finAppend_measurePreserving m n).lintegral_map_equiv F]
  exact lintegral_prod _ (hF.comp (splitFinMeasurableEquiv m n).symm.measurable).aemeasurable

theorem bridgePath_measurable (n : ℕ) (d : ℝ) : Measurable (bridgePath n d) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [bridgePath_last]; fun_prop
  · simp only [bridgePath_castSucc]; fun_prop

theorem pointwiseBridge_integrand_measurable (f : ℝ → ℝ) (hf : Measurable f)
    (n : ℕ) (d : ℝ) (E : Set (Fin (n+1) → ℝ)) (hE : MeasurableSet E) :
    Measurable (fun x => E.indicator
      (fun y => ∏ i, ENNReal.ofReal (f (y i))) (bridgePath n d x)) := by
  have hprod : Measurable (fun y : Fin (n+1) → ℝ => ∏ i, ENNReal.ofReal (f (y i))) := by
    fun_prop
  convert! (hprod.indicator hE).comp (bridgePath_measurable n d)

def bridgeFirstEvent (m n : ℕ) (E : Set (Fin m → ℝ)) : Set (Fin (m+n+1) → ℝ) :=
  {y | (fun i : Fin m => y ((i.castAdd n).castSucc)) ∈ E}

theorem bridgeFirstEvent_measurable (m n : ℕ) (E : Set (Fin m → ℝ))
    (hE : MeasurableSet E) : MeasurableSet (bridgeFirstEvent m n E) := by
  exact hE.preimage (by fun_prop)

theorem pointwiseBridge_split_first (f : ℝ → ℝ) (hf : Measurable f)
    (m n : ℕ) (d : ℝ) (E : Set (Fin m → ℝ)) (hE : MeasurableSet E) :
    pointwiseBridge f (m+n) d (bridgeFirstEvent m n E) =
      ∫⁻ x : Fin m → ℝ, E.indicator (fun x =>
        (∏ i, ENNReal.ofReal (f (x i))) * pointwiseBridge f n (d-∑ i, x i) univ) x := by
  classical
  unfold pointwiseBridge
  rw [lintegral_fin_append m n _
    (pointwiseBridge_integrand_measurable f hf _ d _ (bridgeFirstEvent_measurable m n E hE))]
  apply lintegral_congr
  intro x
  have he (y : Fin n → ℝ) :
      bridgePath (m+n) d (Fin.append x y) ∈ bridgeFirstEvent m n E ↔ x ∈ E := by
    simp only [bridgeFirstEvent, mem_ofPred_eq, bridgePath_castSucc, Fin.append_left]
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    rw [← lintegral_const_mul _ (pointwiseBridge_integrand_measurable f hf n _ univ .univ)]
    apply lintegral_congr
    intro y
    simp only [Set.indicator_of_mem ((he y).mpr hx), indicator_univ]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [bridgePath_castSucc, bridgePath_last]
    rw [Fin.prod_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [show d - ((∑ i, x i) + ∑ i, y i) = (d-∑ i, x i)-∑ i, y i by ring]
    exact mul_assoc _ _ _
  · simp only [Set.indicator_of_notMem hx]
    calc
      _ = ∫⁻ _ : Fin n → ℝ, (0 : ℝ≥0∞) :=
        lintegral_congr (fun y => Set.indicator_of_notMem (by simpa only [he y] using hx) _)
      _ = 0 := lintegral_zero

theorem pointwiseBridge_first_le_unused_sup (f : ℝ → ℝ) (hf : Measurable f)
    (m n : ℕ) (d : ℝ) (E : Set (Fin m → ℝ)) (hE : MeasurableSet E)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ u : ℝ, pointwiseBridge f n u univ ≤ C) :
    pointwiseBridge f (m+n) d (bridgeFirstEvent m n E) ≤
      C * ∫⁻ x : Fin m → ℝ, E.indicator (fun x => ∏ i, ENNReal.ofReal (f (x i))) x := by
  classical
  rw [pointwiseBridge_split_first f hf m n d E hE, ← lintegral_const_mul' _ _ hC]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    calc
      _ ≤ (∏ i, ENNReal.ofReal (f (x i))) * C := by gcongr; exact hbound _
      _ = _ := mul_comm _ _
  · simp only [Set.indicator_of_notMem hx, mul_zero, le_refl]

#print axioms splitFinMeasurableEquiv_symm_apply
#print axioms finAppend_measurePreserving
#print axioms lintegral_fin_append
#print axioms bridgePath_measurable
#print axioms pointwiseBridge_integrand_measurable
#print axioms bridgeFirstEvent_measurable
#print axioms pointwiseBridge_split_first
#print axioms pointwiseBridge_first_le_unused_sup

end ConditionalSpectralExtremes
