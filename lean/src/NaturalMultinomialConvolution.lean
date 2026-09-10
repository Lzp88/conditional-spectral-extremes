import NaturalMultinomialLaw
import MultinomialPMFConvolution

/-! The actual convolution identity on the common natural count-vector space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators

namespace ConditionalSpectralExtremes.BlockCounts
variable {ι : Type*} [Fintype ι]

theorem naturalCountVector_add {m n : ℕ} (u : countFiber ι m m) (v : countFiber ι n n) :
    naturalCountVector (addCountState u v) = naturalCountVector u+naturalCountVector v := rfl

theorem naturalMultinomial_convolution (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (m n : ℕ) :
    ((naturalMultinomialPMF p hp hpsum m).bind (fun u =>
      (naturalMultinomialPMF p hp hpsum n).map (fun v => u+v))) =
      naturalMultinomialPMF p hp hpsum (m+n) := by
  have hh := congrArg (fun q : PMF (countFiber ι (m+n) (m+n)) => q.map naturalCountVector)
    (multinomialPMF_convolution p hp hpsum m n)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, naturalCountVector_add] at hh
  simpa only [naturalMultinomialPMF, PMF.bind_map, PMF.map_comp, Function.comp_def] using hh

#print axioms naturalCountVector_add
#print axioms naturalMultinomial_convolution

end ConditionalSpectralExtremes.BlockCounts
