import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Abstract positive interpolation by refinement

This module formalizes the induction pattern of Theorem 3. A non-atomic node
splits into two smaller-span nodes with positive coefficients, and the two
anchor sets cover the original anchor set. The conclusion constructs a
strictly positive coefficient at every anchor and zero coefficient elsewhere.
-/

namespace PavingToeplitzPositroids

open scoped BigOperators

/-- A positive expansion over a full finite anchor type. -/
structure FullPositiveAnchorExpansion {ι : Type*} [Fintype ι]
    (value : ℝ) (anchorValue : ι → ℝ) (anchors : Finset ι) where
  coefficient : ι → ℝ
  coefficient_nonneg : ∀ i, 0 ≤ coefficient i
  coefficient_pos_iff : ∀ i, 0 < coefficient i ↔ i ∈ anchors
  value_eq_sum : value = ∑ i, coefficient i * anchorValue i

namespace FullPositiveAnchorExpansion

variable {ι : Type*} [Fintype ι]
  {value : ℝ} {anchorValue : ι → ℝ} {anchors : Finset ι}

/-- Nonnegative anchors make the expanded value nonnegative. -/
theorem value_nonneg
    (E : FullPositiveAnchorExpansion value anchorValue anchors)
    (hanchor : ∀ i, 0 ≤ anchorValue i) :
    0 ≤ value := by
  rw [E.value_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (E.coefficient_nonneg i) (hanchor i)

/-- The full-support no-cancellation criterion. -/
theorem value_eq_zero_iff
    (E : FullPositiveAnchorExpansion value anchorValue anchors)
    (hanchor : ∀ i, 0 ≤ anchorValue i) :
    value = 0 ↔ ∀ i ∈ anchors, anchorValue i = 0 := by
  constructor
  · intro hvalue i hi
    have hterm_nonneg : ∀ j : ι, 0 ≤ E.coefficient j * anchorValue j :=
      fun j ↦ mul_nonneg (E.coefficient_nonneg j) (hanchor j)
    have hterm_le : E.coefficient i * anchorValue i ≤ value := by
      calc
        E.coefficient i * anchorValue i ≤
            ∑ j, E.coefficient j * anchorValue j :=
          Finset.single_le_sum (fun j _ ↦ hterm_nonneg j) (Finset.mem_univ i)
        _ = value := E.value_eq_sum.symm
    have hterm_zero : E.coefficient i * anchorValue i = 0 := by
      apply le_antisymm
      · simpa [hvalue] using hterm_le
      · exact hterm_nonneg i
    exact (mul_eq_zero.mp hterm_zero).resolve_left
      ((E.coefficient_pos_iff i).2 hi).ne'
  · intro hzero
    rw [E.value_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ anchors
    · rw [hzero i hi, mul_zero]
    · have hnotpos : ¬0 < E.coefficient i :=
        (E.coefficient_pos_iff i).not.mpr hi
      have hcoeff : E.coefficient i = 0 :=
        le_antisymm (not_lt.mp hnotpos) (E.coefficient_nonneg i)
      rw [hcoeff, zero_mul]

end FullPositiveAnchorExpansion

/-- The data needed by the span induction in Theorem 3. -/
structure PositiveRefinementSystem (node anchor : Type*) [Fintype anchor]
    [DecidableEq anchor] where
  measure : node → ℕ
  anchors : node → Finset anchor
  value : node → ℝ
  anchorValue : anchor → ℝ
  atomic : node → Prop
  atomic_spec : ∀ J, atomic J →
    ∃ t, anchors J = {t} ∧ value J = anchorValue t
  refine : ∀ J, ¬atomic J →
    ∃ L R alpha beta,
      0 < alpha ∧ 0 < beta ∧
      measure L < measure J ∧ measure R < measure J ∧
      anchors J = anchors L ∪ anchors R ∧
      value J = alpha * value L + beta * value R

namespace PositiveRefinementSystem

variable {node anchor : Type*} [Fintype anchor] [DecidableEq anchor]

/-- Combine two positive expansions along one refinement step. -/
noncomputable def combine (S : PositiveRefinementSystem node anchor)
    {J L R : node} {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta)
    (hanchors : S.anchors J = S.anchors L ∪ S.anchors R)
    (hvalue : S.value J = alpha * S.value L + beta * S.value R)
    (EL : FullPositiveAnchorExpansion (S.value L) S.anchorValue (S.anchors L))
    (ER : FullPositiveAnchorExpansion (S.value R) S.anchorValue (S.anchors R)) :
    FullPositiveAnchorExpansion (S.value J) S.anchorValue (S.anchors J) where
  coefficient i := alpha * EL.coefficient i + beta * ER.coefficient i
  coefficient_nonneg i := add_nonneg
    (mul_nonneg ha.le (EL.coefficient_nonneg i))
    (mul_nonneg hb.le (ER.coefficient_nonneg i))
  coefficient_pos_iff i := by
    rw [hanchors, Finset.mem_union]
    constructor
    · intro hpos
      by_contra hnot
      push Not at hnot
      have hLnot : ¬0 < EL.coefficient i :=
        (EL.coefficient_pos_iff i).not.mpr hnot.1
      have hRnot : ¬0 < ER.coefficient i :=
        (ER.coefficient_pos_iff i).not.mpr hnot.2
      have hLzero : EL.coefficient i = 0 :=
        le_antisymm (not_lt.mp hLnot) (EL.coefficient_nonneg i)
      have hRzero : ER.coefficient i = 0 :=
        le_antisymm (not_lt.mp hRnot) (ER.coefficient_nonneg i)
      simp [hLzero, hRzero] at hpos
    · rintro (hiL | hiR)
      · have hLpos := (EL.coefficient_pos_iff i).2 hiL
        exact add_pos_of_pos_of_nonneg (mul_pos ha hLpos)
          (mul_nonneg hb.le (ER.coefficient_nonneg i))
      · have hRpos := (ER.coefficient_pos_iff i).2 hiR
        exact add_pos_of_nonneg_of_pos
          (mul_nonneg ha.le (EL.coefficient_nonneg i)) (mul_pos hb hRpos)
  value_eq_sum := by
    calc
      S.value J = alpha * S.value L + beta * S.value R := hvalue
      _ = alpha * (∑ i, EL.coefficient i * S.anchorValue i) +
          beta * (∑ i, ER.coefficient i * S.anchorValue i) := by
            rw [← EL.value_eq_sum, ← ER.value_eq_sum]
      _ = ∑ i, (alpha * EL.coefficient i + beta * ER.coefficient i) *
          S.anchorValue i := by
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- **Theorem 3, abstract induction form.** Every node admits a positive
expansion over all and only its consecutive anchors. -/
theorem exists_positiveExpansion (S : PositiveRefinementSystem node anchor) (J : node) :
    Nonempty (FullPositiveAnchorExpansion (S.value J) S.anchorValue (S.anchors J)) := by
  classical
  have hmain : ∀ n : ℕ, ∀ J : node, S.measure J = n →
      Nonempty (FullPositiveAnchorExpansion (S.value J) S.anchorValue (S.anchors J)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro J hmeasure
        by_cases hJ : S.atomic J
        · obtain ⟨t, hanchors, hvalue⟩ := S.atomic_spec J hJ
          let coefficient : anchor → ℝ := fun i ↦ if i = t then 1 else 0
          refine ⟨{
            coefficient := coefficient
            coefficient_nonneg := fun i ↦ by
              by_cases hi : i = t <;> simp [coefficient, hi]
            coefficient_pos_iff := fun i ↦ by
              rw [hanchors]
              by_cases hi : i = t <;> simp [coefficient, hi]
            value_eq_sum := ?_ }⟩
          rw [hvalue]
          classical
          simp [coefficient]
        · obtain ⟨L, R, alpha, beta, ha, hb, hL, hR, hanchors, hvalue⟩ :=
            S.refine J hJ
          obtain ⟨EL⟩ := ih (S.measure L) (by omega) L rfl
          obtain ⟨ER⟩ := ih (S.measure R) (by omega) R rfl
          exact ⟨S.combine ha hb hanchors hvalue EL ER⟩
  exact hmain (S.measure J) J rfl

end PositiveRefinementSystem

end PavingToeplitzPositroids
