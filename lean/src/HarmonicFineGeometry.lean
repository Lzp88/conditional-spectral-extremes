import ActualBlockMomentBounds
import HarmonicEndpointBounds
import FineScaleAsymptotics

/-! Exact integer endpoints of the manuscript's harmonic blocks, connected
to its literal floor/ceiling fine scales. -/
noncomputable section
open Filter Set
open scoped Real BigOperators Topology
namespace ConditionalSpectralAudit.FourierHarmonic
open ConditionalSpectralExtremes ConditionalSpectralExtremes.ReservoirAnalysis
open ConditionalSpectralExtremes.FineScales ConditionalSpectralExtremes.ReservoirScale

def exponentialEndpoint (u : Real) : Nat := ⌊Real.exp u⌋₊+1

theorem harmonicNumber_eq_sum_range_succ (N : Nat) :
    harmonicNumber N = ∑ j ∈ Finset.range (N+1), (j : Real)⁻¹ := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, inv_zero, add_zero]
  simp only [harmonicNumber, one_div]

theorem harmonicMass_eq_harmonic_difference (a b : Nat) (hab : a ≤ b) :
    harmonicMass (a+1) (b+1) = harmonicNumber b-harmonicNumber a := by
  rw [harmonicNumber_eq_sum_range_succ, harmonicNumber_eq_sum_range_succ]
  exact Finset.sum_Ico_eq_sub (fun j : Nat => (j : Real)⁻¹) (by omega)

theorem exponential_harmonic_error (u v : Real) (hu : Real.log 2 ≤ u) (huv : u ≤ v) :
    |harmonicMass (exponentialEndpoint u) (exponentialEndpoint v)-(v-u)| ≤ 4*Real.exp (-u) := by
  unfold exponentialEndpoint
  rw [harmonicMass_eq_harmonic_difference _ _ (Nat.floor_mono (Real.exp_le_exp.mpr huv))]
  exact BlockCounts.harmonic_exponential_interval_error u v hu huv

theorem exponentialEndpoint_pos (u : Real) : 0 < exponentialEndpoint u := by
  unfold exponentialEndpoint
  omega

theorem exp_le_exponentialEndpoint (u : Real) : Real.exp u ≤ (exponentialEndpoint u : Real) := by
  have hh := (Nat.lt_floor_add_one (Real.exp u)).le
  simpa only [exponentialEndpoint, Nat.cast_add, Nat.cast_one] using hh

theorem omega_tendsto_atTop (p : Parameters) (hA : 0 < p.A₀) :
    Tendsto (omega p) atTop atTop := by
  have ht := (ell_tendsto_atTop.const_mul_atTop hA).atTop_div_const (by norm_num : (0 : Real)<2)
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [eventually_omega_bounds p hA] with n hn
  exact hn.1

def fineBlockLo (p : Parameters) (n i : Nat) : Nat := exponentialEndpoint (coordinate p n i)
def fineBlockHi (p : Parameters) (n i : Nat) : Nat := exponentialEndpoint (coordinate p n (i+1))

theorem eventually_harmonic_fine_geometry (p : Parameters) (hA : 0 < p.A₀) (hr : 0 < p.rStar) :
    ∀ᶠ n : Nat in atTop, 0 < omega p n ∧ ∀ i : Nat,
      0 < fineBlockLo p n i ∧ 1 ≤ harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) ∧
      omega p n/2 ≤ harmonicMass (fineBlockLo p n i) (fineBlockHi p n i) ∧
      Real.exp (r p n+(i : Real)*omega p n) ≤ fineBlockLo p n i := by
  filter_upwards [(omega_tendsto_atTop p hA).eventually_ge_atTop 8,
    (r_tendsto_atTop p hr).eventually_ge_atTop (Real.log 2)] with n hω hrn
  refine ⟨by linarith, ?_⟩
  intro i
  have hi : (0 : Real) ≤ i := Nat.cast_nonneg _
  have hu : Real.log 2 ≤ coordinate p n i := by dsimp [coordinate]; nlinarith
  have huv : coordinate p n i ≤ coordinate p n (i+1) := by
    simp only [coordinate, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hh := exponential_harmonic_error _ _ hu huv
  have hdiff : coordinate p n (i+1)-coordinate p n i=omega p n := by
    simp only [coordinate, Nat.cast_add, Nat.cast_one]
    ring
  rw [hdiff] at hh
  have hu0 : 0 ≤ coordinate p n i := (Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)).trans hu
  have he : Real.exp (-coordinate p n i) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hl := (abs_le.mp hh).1
  refine ⟨exponentialEndpoint_pos _, by dsimp [fineBlockLo, fineBlockHi]; linarith,
    by dsimp [fineBlockLo, fineBlockHi]; linarith, exp_le_exponentialEndpoint _⟩

#print axioms harmonicMass_eq_harmonic_difference
#print axioms eventually_harmonic_fine_geometry
end ConditionalSpectralAudit.FourierHarmonic
