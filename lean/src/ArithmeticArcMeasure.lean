import ActualBlockEnvelope
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Prod

/-! Actual one- and two-point arithmetic arc measures. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped Real BigOperators ENNReal
namespace ConditionalSpectralAudit.ArithmeticArcs

abbrev Torus := AddCircle (1 : Real)
abbrev haar : Measure Torus := AddCircle.haarAddCircle

theorem haar_eq_volume : haar = (volume : Measure Torus) := by
  symm
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real)))

theorem haar_small_norm_le (ε : Real) :
    haar {t : Torus | ‖t‖ < ε} ≤ ENNReal.ofReal (2*ε) := by
  rw [haar_eq_volume]
  have hsub : {t : Torus | ‖t‖ < ε} ⊆ Metric.closedBall (0 : Torus) ε := by
    intro t ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt ht
  exact (measure_mono hsub).trans (by
    rw [AddCircle.volume_closedBall]
    exact ENNReal.ofReal_le_ofReal (min_le_right _ _))

theorem haar_linear_arc_le (j : Int) (hj : j ≠ 0) (ε : Real) :
    haar {t : Torus | ‖j • t‖ < ε} ≤ ENNReal.ofReal (2*ε) := by
  have hp := measurePreserving_zsmul haar hj
  have hm : MeasurableSet {t : Torus | ‖t‖ < ε} := measurableSet_lt continuous_norm.measurable measurable_const
  have he := hp.measure_preimage hm.nullMeasurableSet
  change haar {t : Torus | ‖j • t‖ < ε} = haar {t : Torus | ‖t‖ < ε} at he
  rw [he]
  exact haar_small_norm_le ε

theorem circle_zsmul_surjective (j : Int) (hj : j ≠ 0) :
    Function.Surjective (fun t : Torus => j • t) := by
  intro t
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective t
  refine ⟨((u/(j : Real) : Real) : Torus), ?_⟩
  change j • (((u/(j : Real)) : Real) : Torus) = (u : Torus)
  rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul, mul_div_cancel₀ u (by exact_mod_cast hj)]

def pairLinearHom (j l : Int) : Torus × Torus →+ Torus where
  toFun p := j • p.1+l • p.2
  map_zero' := by simp
  map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add, zsmul_add]; abel

theorem pairLinear_measurePreserving (j l : Int) (hjl : j ≠ 0 ∨ l ≠ 0) :
    MeasurePreserving (fun p : Torus × Torus => j • p.1+l • p.2) (haar.prod haar) haar := by
  have hc : Continuous (pairLinearHom j l) :=
    (continuous_fst.zsmul j).add (continuous_snd.zsmul l)
  have hs : Function.Surjective (pairLinearHom j l) := by
    intro t
    rcases hjl with hj | hl
    · obtain ⟨u, hu⟩ := circle_zsmul_surjective j hj t
      exact ⟨(u,0), by simpa [pairLinearHom] using hu⟩
    · obtain ⟨u, hu⟩ := circle_zsmul_surjective l hl t
      exact ⟨(0,u), by simpa [pairLinearHom] using hu⟩
  exact AddMonoidHom.measurePreserving hc hs (by simp)

theorem haar_pair_arc_le (j l : Int) (hjl : j ≠ 0 ∨ l ≠ 0) (ε : Real) :
    (haar.prod haar) {p : Torus × Torus | ‖j • p.1+l • p.2‖ < ε} ≤ ENNReal.ofReal (2*ε) := by
  have hp := pairLinear_measurePreserving j l hjl
  have hm : MeasurableSet {t : Torus | ‖t‖ < ε} := measurableSet_lt continuous_norm.measurable measurable_const
  have he := hp.measure_preimage hm.nullMeasurableSet
  change (haar.prod haar) {p : Torus × Torus | ‖j • p.1+l • p.2‖ < ε} =
    haar {t : Torus | ‖t‖ < ε} at he
  rw [he]
  exact haar_small_norm_le ε

theorem one_point_bad_arcs (S : Finset Int) (hS : ∀ j ∈ S, j ≠ 0) (ε : Real) :
    haar {t : Torus | ∃ j ∈ S, ‖j • t‖ < ε} ≤ ENNReal.ofReal ((S.card : Real)*2*ε) := by
  classical
  have hh := measure_biUnion_finset_le (μ := haar) S (fun j : Int => {t : Torus | ‖j • t‖ < ε})
  have he : {t : Torus | ∃ j ∈ S, ‖j • t‖ < ε} = ⋃ j ∈ S, {t : Torus | ‖j • t‖ < ε} := by
    ext t; simp
  rw [he]
  calc
    _ ≤ ∑ j ∈ S, haar {t : Torus | ‖j • t‖ < ε} := hh
    _ ≤ ∑ _j ∈ S, ENNReal.ofReal (2*ε) :=
      Finset.sum_le_sum (fun j hj => haar_linear_arc_le j (hS j hj) ε)
    _ = ENNReal.ofReal ((S.card : Real)*2*ε) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

theorem two_point_bad_arcs (S : Finset (Int × Int))
    (hS : ∀ jl ∈ S, jl.1 ≠ 0 ∨ jl.2 ≠ 0) (ε : Real) :
    (haar.prod haar) {p : Torus × Torus | ∃ jl ∈ S, ‖jl.1 • p.1+jl.2 • p.2‖ < ε} ≤
      ENNReal.ofReal ((S.card : Real)*2*ε) := by
  classical
  have hh := measure_biUnion_finset_le (μ := haar.prod haar) S
    (fun jl : Int × Int => {p : Torus × Torus | ‖jl.1 • p.1+jl.2 • p.2‖ < ε})
  have he : {p : Torus × Torus | ∃ jl ∈ S, ‖jl.1 • p.1+jl.2 • p.2‖ < ε} =
      ⋃ jl ∈ S, {p : Torus × Torus | ‖jl.1 • p.1+jl.2 • p.2‖ < ε} := by
    ext p; simp
  rw [he]
  calc
    _ ≤ ∑ jl ∈ S, (haar.prod haar) {p : Torus × Torus | ‖jl.1 • p.1+jl.2 • p.2‖ < ε} := hh
    _ ≤ ∑ _jl ∈ S, ENNReal.ofReal (2*ε) :=
      Finset.sum_le_sum (fun jl hjl => haar_pair_arc_le jl.1 jl.2 (hS jl hjl) ε)
    _ = ENNReal.ofReal ((S.card : Real)*2*ε) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

#print axioms one_point_bad_arcs
#print axioms two_point_bad_arcs
end ConditionalSpectralAudit.ArithmeticArcs
