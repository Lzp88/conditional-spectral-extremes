import ActualKernelTotalVariation

/-! A common explicit envelope for both actual one- and two-dimensional TV errors. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace ConditionalSpectralAudit.FourierHarmonic

def smoothingCrudeError (P s δ T K E : Real) (q : Nat) : Real :=
  4*K^2*(4*T^2*(4*q*E)+4*(2*(δ/10)⁻¹^10*T^(-9 : Real)/9)*((200/9 : Real)/δ))+
    8*Real.exp (-(s/2)*K+(s/2)*δ)*momentMajorant P 2^q

theorem smoothingErrorTwo_le_crude (P s δ T K E : Real) (q : Nat)
    (hδ : 0 < δ) (hT : 0 < T) (hE : 0 ≤ E) :
    smoothingErrorTwo P s δ T K E q ≤ smoothingCrudeError P s δ T K E q := by
  unfold smoothingErrorTwo smoothingCrudeError
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpi : 1 ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  have hinv : ((2*Real.pi)^2)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hpi
  exact mul_le_of_le_one_left (by positivity) hinv

theorem smoothingErrorOne_le_crude (P s δ T K E : Real) (q : Nat)
    (hP : 0 ≤ P) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 1 ≤ T) (hK : 1 ≤ K) (hE : 0 ≤ E) :
    smoothingErrorOne P s δ T K E q ≤ smoothingCrudeError P s δ T K E q := by
  have hπ : (2*Real.pi)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith [Real.pi_gt_three])
  have hTpos : 0 < T := by linarith
  have hbase : 1 ≤ (2 : Real)^(3*P/2) := Real.one_le_rpow (by norm_num) (by positivity)
  have hM : momentMajorant P 1 ≤ momentMajorant P 2 := by
    unfold momentMajorant
    simp only [pow_one, pow_two]
    nlinarith
  have hMq := pow_le_pow_left₀ (momentMajorant_pos P 1).le hM q
  have hconst : 1 ≤ (200/9 : Real)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hn : 0 ≤ (δ/10)⁻¹^10*T^(-9 : Real)/9 := by positivity
  have hnoise : 4*(δ/10)⁻¹^10*T^(-9 : Real)/9 ≤
      4*(2*(δ/10)⁻¹^10*T^(-9 : Real)/9)*((200/9 : Real)/δ) := by
    nlinarith [mul_le_mul_of_nonneg_left hconst hn]
  have hqE : 0 ≤ 4*(q : Real)*E := by positivity
  have hcore : 2*T*(4*q*E)+4*(δ/10)⁻¹^10*T^(-9 : Real)/9 ≤
      4*T^2*(4*q*E)+4*(2*(δ/10)⁻¹^10*T^(-9 : Real)/9)*((200/9 : Real)/δ) := by
    nlinarith [mul_le_mul_of_nonneg_right (show 2*T ≤ 4*T^2 by nlinarith) hqE]
  have hvol : 2*K ≤ 4*K^2 := by nlinarith
  unfold smoothingErrorOne smoothingCrudeError
  apply add_le_add
  · apply mul_le_mul hvol _ (by positivity) (by positivity)
    exact (mul_le_of_le_one_left (by positivity) hπ).trans hcore
  · nlinarith [mul_le_mul_of_nonneg_left hMq (show 0 ≤ 4*Real.exp (-(s/2)*K+(s/2)*δ) by positivity),
      mul_nonneg (Real.exp_pos (-(s/2)*K+(s/2)*δ)).le
        (pow_nonneg (momentMajorant_pos P 2).le q)]

#print axioms smoothingErrorOne_le_crude
#print axioms smoothingErrorTwo_le_crude
end ConditionalSpectralAudit.FourierHarmonic
