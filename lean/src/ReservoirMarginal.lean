import ProfileNormalization

/-!
Exact reservoir elimination for the manuscript's actual finite profile law.
The short/long configuration split is an equivalence, not an independence
assumption. Residual size and cycle count are both retained. Natural-number
residuals are guarded by feasibility inequalities to prevent truncating an
impossible negative residual to zero.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ConditionalSpectralExtremes.Reservoir

def IsShort {n : ℕ} (b : ℕ) (j : Fin n) : Prop := j.val + 1 ≤ b
abbrev ShortIndex (n b : ℕ) := {j : Fin n // IsShort b j}
abbrev LongIndex (n b : ℕ) := {j : Fin n // ¬ IsShort b j}
abbrev ShortConfiguration (n b : ℕ) := ShortIndex n b → Fin (n+1)
abbrev LongConfiguration (n b : ℕ) := LongIndex n b → Fin (n+1)

def splitEquiv (n b : ℕ) :
    Configuration n ≃ ShortConfiguration n b × LongConfiguration n b :=
  Equiv.piEquivPiSubtypeProd (IsShort b) (fun _ : Fin n => Fin (n+1))

def shortPart {n : ℕ} (b : ℕ) (c : Configuration n) : ShortConfiguration n b :=
  (splitEquiv n b c).1
def longPart {n : ℕ} (b : ℕ) (c : Configuration n) : LongConfiguration n b :=
  (splitEquiv n b c).2

def shortMass {n b : ℕ} (c : ShortConfiguration n b) : ℕ :=
  ∑ j : ShortIndex n b, (j.val.val+1) * (c j).val
def longMass {n b : ℕ} (c : LongConfiguration n b) : ℕ :=
  ∑ j : LongIndex n b, (j.val.val+1) * (c j).val
def shortCount {n b : ℕ} (c : ShortConfiguration n b) : ℕ :=
  ∑ j : ShortIndex n b, (c j).val
def longCount {n b : ℕ} (c : LongConfiguration n b) : ℕ :=
  ∑ j : LongIndex n b, (c j).val
def shortWeight {n b : ℕ} (c : ShortConfiguration n b) : ℝ :=
  ∏ j : ShortIndex n b,
    ((j.val.val+1 : ℕ) : ℝ)⁻¹ ^ (c j).val / ((c j).val.factorial : ℝ)
def longWeight {n b : ℕ} (c : LongConfiguration n b) : ℝ :=
  ∏ j : LongIndex n b,
    ((j.val.val+1 : ℕ) : ℝ)⁻¹ ^ (c j).val / ((c j).val.factorial : ℝ)

theorem totalSize_split {n : ℕ} (b : ℕ) (c : Configuration n) :
    totalSize c = shortMass (shortPart b c) + longMass (longPart b c) := by
  exact (Fintype.sum_subtype_add_sum_subtype (IsShort b)
    (fun j : Fin n => (j.val+1) * (c j).val)).symm

theorem cycleCount_split {n : ℕ} (b : ℕ) (c : Configuration n) :
    cycleCount c = shortCount (shortPart b c) + longCount (longPart b c) := by
  exact (Fintype.sum_subtype_add_sum_subtype (IsShort b)
    (fun j : Fin n => (c j).val)).symm

theorem profileWeight_split {n : ℕ} (b : ℕ) (c : Configuration n) :
    profileWeight c = shortWeight (shortPart b c) * longWeight (longPart b c) := by
  exact (Fintype.prod_subtype_mul_prod_subtype (IsShort b)
    (fun j : Fin n => ((j.val+1 : ℕ) : ℝ)⁻¹ ^ (c j).val /
      ((c j).val.factorial : ℝ))).symm

/-- The actual long-cycle reservoir weight at specified residual size and count. -/
def reservoirCoefficient (n b N l : ℕ) : ℝ :=
  ∑ c : LongConfiguration n b,
    if longMass c = N ∧ longCount c = l then longWeight c else 0

/-- Literal two-variable finite reservoir polynomial: outer X marks size,
    inner X marks the number of long cycles. -/
def reservoirPolynomial (n b : ℕ) : Polynomial (Polynomial ℝ) :=
  ∑ c : LongConfiguration n b,
    Polynomial.monomial (longMass c)
      (Polynomial.monomial (longCount c) (longWeight c))

theorem reservoirPolynomial_coeff (n b N l : ℕ) :
    ((reservoirPolynomial n b).coeff N).coeff l = reservoirCoefficient n b N l := by
  classical
  unfold reservoirPolynomial reservoirCoefficient
  simp only [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hm : N = longMass c
  · by_cases hk : l = longCount c
    · simp [hm, hk]
    · have hk' : longCount c ≠ l := Ne.symm hk
      simp [Polynomial.coeff_monomial, hm, hk']
  · have hm' : longMass c ≠ N := Ne.symm hm
    simp [Polynomial.coeff_monomial, hm']

theorem finite_product_monomials {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → ℕ) (v : ι → R) :
    (∏ i ∈ s, Polynomial.monomial (a i) (v i)) =
      Polynomial.monomial (∑ i ∈ s, a i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp [hi, ih, Polynomial.monomial_mul_monomial]

/-- The reservoir is the literal product of the truncated long-cycle
    exponential factors, with size and count kept as separate variables. -/
theorem reservoirPolynomial_product (n b : ℕ) :
    reservoirPolynomial n b =
      ∏ j : LongIndex n b, ∑ c : Fin (n+1),
        Polynomial.monomial ((j.val.val+1) * c.val)
          (Polynomial.monomial c.val
            (((j.val.val+1 : ℕ) : ℝ)⁻¹ ^ c.val / (c.val.factorial : ℝ))) := by
  classical
  unfold reservoirPolynomial
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [finite_product_monomials, finite_product_monomials]
  rfl

/-- The exact unnormalized marginal contribution of a fixed short profile. -/
theorem residual_sum (n b k : ℕ) (s : ShortConfiguration n b)
    (event : ShortConfiguration n b → Prop) :
    (∑ t : LongConfiguration n b,
      if (shortMass s + longMass t = n ∧ shortCount s + longCount t = k) ∧ event s
      then shortWeight s * longWeight t else 0) =
    if shortMass s ≤ n ∧ shortCount s ≤ k ∧ event s
    then shortWeight s * reservoirCoefficient n b (n-shortMass s) (k-shortCount s)
    else 0 := by
  classical
  by_cases hs : shortMass s ≤ n
  · by_cases hk : shortCount s ≤ k
    · by_cases he : event s
      · simp only [hs, hk, he, and_self, if_true, and_true]
        unfold reservoirCoefficient
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        have hi :
            (shortMass s + longMass t = n ∧ shortCount s + longCount t = k) ↔
            (longMass t = n-shortMass s ∧ longCount t = k-shortCount s) := by omega
        simp only [hi, mul_ite, mul_zero]
      · simp [he]
    · simp only [hk, and_false, false_and, if_false]
      apply Finset.sum_eq_zero
      intro t _
      have hi : ¬ ((shortMass s + longMass t = n ∧
          shortCount s + longCount t = k) ∧ event s) := by omega
      simp [hi]
  · simp only [hs, false_and, if_false]
    apply Finset.sum_eq_zero
    intro t _
    have hi : ¬ ((shortMass s + longMass t = n ∧
        shortCount s + longCount t = k) ∧ event s) := by omega
    simp [hi]

/-- Entire event-restricted finite marginal, before normalization. -/
theorem short_event_numerator (n b k : ℕ) (event : ShortConfiguration n b → Prop) :
    (∑ c : Configuration n,
      if Valid k c ∧ event (shortPart b c) then profileWeight c else 0) =
    ∑ s : ShortConfiguration n b,
      if shortMass s ≤ n ∧ shortCount s ≤ k ∧ event s
      then shortWeight s * reservoirCoefficient n b (n-shortMass s) (k-shortCount s)
      else 0 := by
  classical
  calc
    (∑ c : Configuration n,
        if Valid k c ∧ event (shortPart b c) then profileWeight c else 0) =
      ∑ p : ShortConfiguration n b × LongConfiguration n b,
        if (shortMass p.1 + longMass p.2 = n ∧
            shortCount p.1 + longCount p.2 = k) ∧ event p.1
        then shortWeight p.1 * longWeight p.2 else 0 := by
      apply Fintype.sum_equiv (splitEquiv n b)
      intro c
      simp only [Valid, totalSize_split b c, cycleCount_split b c,
        profileWeight_split b c]
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      exact residual_sum n b k s event

/-- The exact reservoir marginal formula under the manuscript's actual law.
    Every short event is allowed; no independence approximation is used. -/
theorem conditionalProbability_short_event (n b k : ℕ)
    (event : ShortConfiguration n b → Prop) :
    conditionalProbability n k (fun c => event (shortPart b c)) =
      (∑ s : ShortConfiguration n b,
        if shortMass s ≤ n ∧ shortCount s ≤ k ∧ event s
        then shortWeight s * reservoirCoefficient n b (n-shortMass s) (k-shortCount s)
        else 0) / coefficient n k := by
  unfold conditionalProbability
  rw [short_event_numerator]

theorem shortWeight_pos {n b : ℕ} (s : ShortConfiguration n b) :
    0 < shortWeight s := by
  unfold shortWeight
  apply Finset.prod_pos
  intro j _
  positivity

theorem longWeight_pos {n b : ℕ} (t : LongConfiguration n b) :
    0 < longWeight t := by
  unfold longWeight
  apply Finset.prod_pos
  intro j _
  positivity

theorem reservoirCoefficient_nonneg (n b N l : ℕ) :
    0 ≤ reservoirCoefficient n b N l := by
  unfold reservoirCoefficient
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact (longWeight_pos t).le
  · exact le_rfl

#print axioms totalSize_split
#print axioms cycleCount_split
#print axioms profileWeight_split
#print axioms reservoirPolynomial_coeff
#print axioms reservoirPolynomial_product
#print axioms residual_sum
#print axioms short_event_numerator
#print axioms conditionalProbability_short_event
#print axioms shortWeight_pos
#print axioms longWeight_pos
#print axioms reservoirCoefficient_nonneg

end ConditionalSpectralExtremes.Reservoir
