import CoarsePoissonEnvironment
import CountPathCoupling
import CouplingWeightedEnergy

/-! The literal manuscript coarse environments are controlled jointly by
one discrepancy energy in the actual count coupling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
open FineScales

def coarseCouplingEnergy (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (z : CoupledCounts (Option (Fin (count p n+1)))) : ℝ :=
  couplingWeightedDiscrepancy (coarseCountSet p n hv hm) (fun j => groupWidth p n j) z

theorem coarse_coupled_environment_square (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ : ℝ) (j : Fin (groupNumber p n)) (hH : 0 < groupWidth p n j)
    (z : CoupledCounts (Option (Fin (count p n+1)))) (hz : CountsCoupled z) :
    (coarseCountEnvironment p n κ j z.1-coarseCountEnvironment p n κ j z.2.1)^2 ≤
      (subsetCount (coarseCountSet p n hv hm j) z.2.2)^2/groupWidth p n j := by
  rw [coarseCountEnvironment_eq p n hv hm κ j]
  exact countPathEnvironment_coupled_square (coarseCountIndex p n hv hm j) _ _ hH z hz

theorem coarse_coupled_environment_energy (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ : ℝ) (hH : ∀ j : Fin (groupNumber p n), 0 < groupWidth p n j)
    (z : CoupledCounts (Option (Fin (count p n+1)))) (hz : CountsCoupled z) :
    (∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n κ j z.2.1)^2) ≤
      2*(∑ j : Fin (groupNumber p n), (coarseCountEnvironment p n κ j z.1)^2)+
        2*coarseCouplingEnergy p n hv hm z := by
  have hp (j : Fin (groupNumber p n)) : (coarseCountEnvironment p n κ j z.2.1)^2 ≤
      2*(coarseCountEnvironment p n κ j z.1)^2+
        2*((subsetCount (coarseCountSet p n hv hm j) z.2.2)^2/groupWidth p n j) := by
    have hh := coarse_coupled_environment_square p n hv hm κ j (hH j) z hz
    nlinarith [sq_nonneg (2*coarseCountEnvironment p n κ j z.1-coarseCountEnvironment p n κ j z.2.1)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  simpa only [coarseCouplingEnergy, couplingWeightedDiscrepancy,
    Finset.sum_add_distrib, Finset.mul_sum] using hh

theorem coarse_coupled_environment_max (p : Parameters) (n : ℕ)
    (hv : 0 < baseBlocks p n) (hm : 2*baseBlocks p n ≤ count p n)
    (κ : ℝ) (hH : ∀ j : Fin (groupNumber p n), 0 < groupWidth p n j)
    (z : CoupledCounts (Option (Fin (count p n+1)))) (hz : CountsCoupled z)
    (R : ℝ) (hR : 0 ≤ R) (hE : coarseCouplingEnergy p n hv hm z ≤ R)
    (j : Fin (groupNumber p n)) :
    coarseCountEnvironment p n κ j z.2.1 ≤ coarseCountEnvironment p n κ j z.1+Real.sqrt R := by
  have hs : (subsetCount (coarseCountSet p n hv hm j) z.2.2)^2/groupWidth p n j ≤
      coarseCouplingEnergy p n hv hm z :=
    Finset.single_le_sum (fun i _ => div_nonneg
      (sq_nonneg (subsetCount (coarseCountSet p n hv hm i) z.2.2)) (hH i).le) (Finset.mem_univ j)
  have hh := (coarse_coupled_environment_square p n hv hm κ j (hH j) z hz).trans (hs.trans hE)
  have hsq : |coarseCountEnvironment p n κ j z.1-coarseCountEnvironment p n κ j z.2.1|^2 ≤
      (Real.sqrt R)^2 := by rw [sq_abs, Real.sq_sqrt hR]; exact hh
  have habs := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg R)).mp hsq
  have hlo := (abs_le.mp habs).1
  linarith

#print axioms coarse_coupled_environment_square
#print axioms coarse_coupled_environment_energy
#print axioms coarse_coupled_environment_max

end ConditionalSpectralExtremes.BlockCounts
