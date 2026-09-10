import BridgeDensityMeasure
import BridgeTubeSplit

/-! The actual bridge lower estimate obtained by subtracting both half-path
violation densities. Analytic bounds on unrestricted convolution densities
are explicit inputs; the bridge conclusion and density/probability factorization
are proved from the original finite-dimensional integrals. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ConditionalSpectralExtremes

theorem bridgeTube_measurable (q : ℕ) (d R : ℝ) : MeasurableSet (bridgeTube q d R) := by
  simp only [bridgeTube, ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  apply measurableSet_le _ measurable_const
  unfold FiniteWalk.partialSum
  fun_prop

theorem bridgeEndpointMeasure_real_univ (β : ℝ) (hβ : -1 < β) (n : ℕ) (hn : 2 ≤ n) (d : ℝ) :
    (bridgeEndpointMeasure (tiltedDensity β) n d).real univ = tiltedDensityPower β (n+1) d := by
  rw [measureReal_def, bridgeEndpointMeasure_univ, pointwiseBridge_tilted_eq_power β hβ n hn d,
    ENNReal.toReal_ofReal (tiltedDensityPower_nonneg β (n+1) d)]

theorem bridgeEndpointMeasure_first_real_bound (β : ℝ) (hβ : -1 < β)
    (n m : ℕ) (hm : m ≤ n) (hrest : 2 ≤ n-m) (d R C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : ℝ, tiltedDensityPower β (n-m+1) u ≤ C) :
    (bridgeEndpointMeasure (tiltedDensity β) n d).real
      (firstMaximumEvent β (n+1) m (by omega) R) ≤
        C * (tiltedLogSineProduct β m).real (centeredMaximumEvent β m R) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  let _ := tiltedLogSineProduct_isProbabilityMeasure β m hβ
  have hsup (u : ℝ) : pointwiseBridge (tiltedDensity β) k u univ ≤ ENNReal.ofReal C := by
    rw [pointwiseBridge_tilted_eq_power β hβ k (by omega) u]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.add_sub_cancel_left] using hbound u
  have hh := pointwiseBridge_first_probability_bound β hβ m k d
    (centeredMaximumEvent β m R) (centeredMaximumEvent_measurable β m R)
    (ENNReal.ofReal C) ENNReal.ofReal_ne_top hsup
  rw [bridgeFirstEvent_eq_firstMaximum] at hh
  rw [pointwiseBridge_eq_measure _ _ _ _ (firstMaximumEvent_measurable β (m+k+1) m (by omega) R)] at hh
  have ht := ENNReal.toReal_mono (by finiteness) hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, measureReal_def] using ht

theorem bridgeTube_total_le_good_add_halves (β : ℝ) (hβ : -1 < β)
    (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n+1) (R : ℝ) :
    (bridgeEndpointMeasure (tiltedDensity β) n ((n+1 : ℕ)*deriv lambda β)).real univ ≤
      (bridgeEndpointMeasure (tiltedDensity β) n ((n+1 : ℕ)*deriv lambda β)).real
        (bridgeTube (n+1) ((n+1 : ℕ)*deriv lambda β) R) +
      (bridgeEndpointMeasure (tiltedDensity β) n ((n+1 : ℕ)*deriv lambda β)).real
        (firstMaximumEvent β (n+1) m hm R) +
      (bridgeEndpointMeasure (tiltedDensity β) n ((n+1 : ℕ)*deriv lambda β)).real
        (firstMaximumEvent β (n+1) (n+1-m) (Nat.sub_le _ _) R) := by
  let d : ℝ := (n+1 : ℕ)*deriv lambda β
  let μ := bridgeEndpointMeasure (tiltedDensity β) n d
  let _ := tiltedBridgeEndpointMeasure_finite β hβ n hn d
  let T : Set (Fin (n+1) → ℝ) := bridgeTube (n+1) d R
  let A : Set (Fin (n+1) → ℝ) := firstMaximumEvent β (n+1) m hm R
  let B : Set (Fin (n+1) → ℝ) := firstMaximumEvent β (n+1) (n+1-m) (Nat.sub_le _ _) R
  have hB : MeasurableSet B := firstMaximumEvent_measurable β (n+1) _ _ R
  have hcover : ∀ᵐ x ∂μ, x ∈ (univ : Set (Fin (n+1) → ℝ)) →
      x ∈ ((T ∪ A) ∪ (reversePath (n+1) ⁻¹' B)) := by
    filter_upwards [bridgeEndpointMeasure_total_ae (tiltedDensity β) n d] with x hx
    intro _
    by_cases hT : x ∈ T
    · exact Or.inl (Or.inl hT)
    · rcases bridgeTube_complement_halves β (n+1) m (by omega) hm R x hx hT with hA | hB
      · exact Or.inl (Or.inr hA)
      · exact Or.inr hB
  have hrev : μ (reversePath (n+1) ⁻¹' B) = μ B := by
    rw [← Measure.map_apply (reversePath_measurable (n+1)) hB]
    exact congrArg (fun ν : Measure (Fin (n+1) → ℝ) => ν B)
      (bridgeEndpointMeasure_reverse (tiltedDensity β) (tiltedDensity_measurable β) n d)
  change μ.real univ ≤ μ.real T + μ.real A + μ.real B
  calc
    _ ≤ μ.real ((T ∪ A) ∪ reversePath (n+1) ⁻¹' B) :=
      ENNReal.toReal_mono (by finiteness) (measure_mono_ae hcover)
    _ ≤ μ.real (T ∪ A) + μ.real (reversePath (n+1) ⁻¹' B) := measureReal_union_le _ _
    _ ≤ (μ.real T + μ.real A) + μ.real (reversePath (n+1) ⁻¹' B) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ = _ := by simp only [measureReal_def, hrev]

theorem bridgeTube_lower_of_convolution_bounds (β : ℝ) (hβ : -1 < β)
    (n m : ℕ) (hm : 3 ≤ m) (hrest : 2 ≤ n-m) (R U₁ U₂ : ℝ)
    (hU₁ : 0 ≤ U₁) (hU₂ : 0 ≤ U₂)
    (hbound₁ : ∀ u : ℝ, tiltedDensityPower β m u ≤ U₁)
    (hbound₂ : ∀ u : ℝ, tiltedDensityPower β (n+1-m) u ≤ U₂) :
    tiltedDensityPower β (n+1) ((n+1 : ℕ)*deriv lambda β) -
      U₂ * (tiltedLogSineProduct β m).real (centeredMaximumEvent β m R) -
      U₁ * (tiltedLogSineProduct β (n+1-m)).real (centeredMaximumEvent β (n+1-m) R) ≤
        (tubeBridge β n ((n+1 : ℕ)*deriv lambda β) R).toReal := by
  have hmn : m ≤ n := by omega
  have hn : 2 ≤ n := by omega
  have hh := bridgeTube_total_le_good_add_halves β hβ n m hn (by omega) R
  have hfirst := bridgeEndpointMeasure_first_real_bound β hβ n m hmn hrest
    ((n+1 : ℕ)*deriv lambda β) R U₂ hU₂ (by
      have he : n-m+1=n+1-m := by omega
      simpa only [he] using hbound₂)
  have hsecond := bridgeEndpointMeasure_first_real_bound β hβ n (n+1-m) (by omega) (by omega)
    ((n+1 : ℕ)*deriv lambda β) R U₁ hU₁ (by
      have he : n-(n+1-m)+1=m := by omega
      simpa only [he] using hbound₁)
  rw [bridgeEndpointMeasure_real_univ β hβ n hn] at hh
  have hgood : (bridgeEndpointMeasure (tiltedDensity β) n ((n+1 : ℕ)*deriv lambda β)).real
      (bridgeTube (n+1) ((n+1 : ℕ)*deriv lambda β) R) =
        (tubeBridge β n ((n+1 : ℕ)*deriv lambda β) R).toReal := by
    rw [measureReal_def, ← pointwiseBridge_eq_measure _ _ _ _ (bridgeTube_measurable _ _ _)]
    rfl
  rw [hgood] at hh
  linarith only [hh, hfirst, hsecond]

theorem bridgeTube_lower_with_exponential_errors (a b : ℝ) (ha : -1 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ β ∈ Icc a b, ∀ n m : ℕ, 3 ≤ m → 2 ≤ n-m →
      ∀ R U₁ U₂ : ℝ, 1 ≤ R → R ≤ c*(m : ℝ) → R ≤ c*((n+1-m : ℕ) : ℝ) →
      0 ≤ U₁ → 0 ≤ U₂ →
      (∀ u : ℝ, tiltedDensityPower β m u ≤ U₁) →
      (∀ u : ℝ, tiltedDensityPower β (n+1-m) u ≤ U₂) →
      tiltedDensityPower β (n+1) ((n+1 : ℕ)*deriv lambda β) -
        2*U₂*Real.exp (-c*R^2/(m : ℝ)) -
        2*U₁*Real.exp (-c*R^2/((n+1-m : ℕ) : ℝ)) ≤
          (tubeBridge β n ((n+1 : ℕ)*deriv lambda β) R).toReal := by
  obtain ⟨c, hc, hh⟩ := walk_maximal_deviation a b ha hab
  refine ⟨c, hc, ?_⟩
  intro β hβ n m hm hrest R U₁ U₂ hR hRm hRrest hU₁ hU₂ hbound₁ hbound₂
  have hb := lt_of_lt_of_le ha hβ.1
  have hbase := bridgeTube_lower_of_convolution_bounds β hb n m hm hrest R U₁ U₂ hU₁ hU₂ hbound₁ hbound₂
  have hfirst := mul_le_mul_of_nonneg_left (hh β hβ m (by omega) R hR hRm) hU₂
  have hsecond := mul_le_mul_of_nonneg_left (hh β hβ (n+1-m) (by omega) R hR hRrest) hU₁
  change U₂ * (tiltedLogSineProduct β m).real (centeredMaximumEvent β m R) ≤ _ at hfirst
  change U₁ * (tiltedLogSineProduct β (n+1-m)).real (centeredMaximumEvent β (n+1-m) R) ≤ _ at hsecond
  nlinarith only [hbase, hfirst, hsecond]

#print axioms bridgeTube_measurable
#print axioms bridgeEndpointMeasure_real_univ
#print axioms bridgeEndpointMeasure_first_real_bound
#print axioms bridgeTube_total_le_good_add_halves
#print axioms bridgeTube_lower_of_convolution_bounds
#print axioms bridgeTube_lower_with_exponential_errors

end ConditionalSpectralExtremes
