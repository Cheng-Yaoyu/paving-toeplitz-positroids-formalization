import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Positive finite expansions and support

These lemmas isolate the no-cancellation step used in Corollary 4. They are
independent of matrices: once Theorem 3 supplies a positive anchor expansion,
nonnegativity and exact vanishing support follow formally.
-/

namespace PavingToeplitzPositroids

open scoped BigOperators

/-- A scalar expressed as a strictly positive linear combination of the
entries indexed by `anchors`. -/
structure PositiveAnchorExpansion {ι : Type*} [Fintype ι]
    (value : ℝ) (anchorValue : ι → ℝ) (anchors : Finset ι) where
  coefficient : ι → ℝ
  coefficient_pos : ∀ i ∈ anchors, 0 < coefficient i
  value_eq_sum : value = ∑ i ∈ anchors, coefficient i * anchorValue i

namespace PositiveAnchorExpansion

variable {ι : Type*} [Fintype ι]
  {value : ℝ} {anchorValue : ι → ℝ} {anchors : Finset ι}

/-- Nonnegative anchors make the expanded scalar nonnegative. -/
theorem value_nonneg (E : PositiveAnchorExpansion value anchorValue anchors)
    (hanchor : ∀ i ∈ anchors, 0 ≤ anchorValue i) :
    0 ≤ value := by
  rw [E.value_eq_sum]
  exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (E.coefficient_pos i hi).le (hanchor i hi)

/-- **Corollary 4, abstract form.** A positive combination of nonnegative
anchors vanishes exactly when every anchor vanishes. -/
theorem value_eq_zero_iff (E : PositiveAnchorExpansion value anchorValue anchors)
    (hanchor : ∀ i ∈ anchors, 0 ≤ anchorValue i) :
    value = 0 ↔ ∀ i ∈ anchors, anchorValue i = 0 := by
  constructor
  · intro hvalue i hi
    have hterm_nonneg : ∀ j ∈ anchors, 0 ≤ E.coefficient j * anchorValue j :=
      fun j hj ↦ mul_nonneg (E.coefficient_pos j hj).le (hanchor j hj)
    have hterm_le : E.coefficient i * anchorValue i ≤ value := by
      calc
        E.coefficient i * anchorValue i ≤
            ∑ j ∈ anchors, E.coefficient j * anchorValue j :=
          Finset.single_le_sum hterm_nonneg hi
        _ = value := E.value_eq_sum.symm
    have hterm_zero : E.coefficient i * anchorValue i = 0 := by
      apply le_antisymm
      · simpa [hvalue] using hterm_le
      · exact hterm_nonneg i hi
    exact (mul_eq_zero.mp hterm_zero).resolve_left (E.coefficient_pos i hi).ne'
  · intro hzero
    rw [E.value_eq_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i hi, mul_zero]

end PositiveAnchorExpansion

/-- Equality of all scalar pairings determines a finite real vector. This is
the extensional step in Corollary 5. -/
theorem pi_eq_of_dotProduct_eq {n : ℕ} {x y : Fin n → ℝ}
    (h : ∀ f : Fin n → ℝ, (∑ i, x i * f i) = ∑ i, y i * f i) :
    x = y := by
  funext j
  let f : Fin n → ℝ := fun i ↦ if i = j then 1 else 0
  have hj := h f
  simpa [f, Fintype.sum_ite_eq'] using hj

end PavingToeplitzPositroids
