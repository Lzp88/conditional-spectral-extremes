import KilledGroupMinorization
import UniformCriticalParameters

/-! Scalar constants for the box proof. Their choice is made before the
fixed low-scale constants gStar,rStar and is independent of them. -/

noncomputable section
open Filter
open scoped Topology
namespace ConditionalSpectralExtremes.CoarseBoxes

theorem exists_boundary_scale (M smax : ℝ) (hsmax : 0 < smax) :
    ∃ D : ℝ, 0 < D ∧ M*Real.sqrt (2/D) ≤ 1/(8*smax) := by
  have hh : Tendsto (fun D : ℝ => M*Real.sqrt (2/D)) atTop (𝓝 0) := by
    have he := (((tendsto_const_nhds (x := (2 : ℝ))).div_atTop
      (tendsto_id : Tendsto (fun D : ℝ => D) atTop atTop)).sqrt).const_mul M
    simpa only [id_eq, Real.sqrt_zero, mul_zero] using! he
  have hp : (0 : ℝ)<1/(8*smax) := by positivity
  have he := hh.eventually (gt_mem_nhds hp)
  obtain ⟨D, hD, hbound⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  exact ⟨D, hD, hbound.le⟩

#print axioms exists_boundary_scale

end ConditionalSpectralExtremes.CoarseBoxes
