import PavingToeplitzPositroids.InterpolationAbstract
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Positive refinement with module-valued anchors

Corollary 5 uses the same positive coefficients as Theorem 3, but its values
are vectors. This file lifts the abstract strong induction to an arbitrary
real module while retaining the scalar positivity data.
-/

namespace PavingToeplitzPositroids

open scoped BigOperators

noncomputable section

/-- A module-valued expansion with nonnegative coefficients supported exactly
on a prescribed finite anchor set. -/
structure FullPositiveModuleAnchorExpansion
    {V ι : Type*} [AddCommMonoid V] [Module ℝ V] [Fintype ι]
    (value : V) (anchorValue : ι → V) (anchors : Finset ι) where
  coefficient : ι → ℝ
  coefficient_nonneg : ∀ i, 0 ≤ coefficient i
  coefficient_pos_iff : ∀ i, 0 < coefficient i ↔ i ∈ anchors
  value_eq_sum : value = ∑ i, coefficient i • anchorValue i

/-- Module-valued data governed by a positive scalar refinement relation. -/
structure ModulePositiveRefinementSystem
    (node anchor V : Type*) [Fintype anchor] [DecidableEq anchor]
    [AddCommMonoid V] [Module ℝ V] where
  measure : node → ℕ
  anchors : node → Finset anchor
  value : node → V
  anchorValue : anchor → V
  atomic : node → Prop
  atomic_spec : ∀ J, atomic J →
    ∃ t, anchors J = {t} ∧ value J = anchorValue t
  refine : ∀ J, ¬atomic J →
    ∃ L R, ∃ alpha beta : ℝ,
      0 < alpha ∧ 0 < beta ∧
      measure L < measure J ∧ measure R < measure J ∧
      anchors J = anchors L ∪ anchors R ∧
      value J = alpha • value L + beta • value R

namespace ModulePositiveRefinementSystem

variable {node anchor V : Type*} [Fintype anchor] [DecidableEq anchor]
  [AddCommMonoid V] [Module ℝ V]

/-- Combine two module-valued expansions along one positive refinement. -/
def combine (S : ModulePositiveRefinementSystem node anchor V)
    {J L R : node} {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta)
    (hanchors : S.anchors J = S.anchors L ∪ S.anchors R)
    (hvalue : S.value J = alpha • S.value L + beta • S.value R)
    (EL : FullPositiveModuleAnchorExpansion
      (S.value L) S.anchorValue (S.anchors L))
    (ER : FullPositiveModuleAnchorExpansion
      (S.value R) S.anchorValue (S.anchors R)) :
    FullPositiveModuleAnchorExpansion
      (S.value J) S.anchorValue (S.anchors J) where
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
      · exact add_pos_of_pos_of_nonneg
          (mul_pos ha ((EL.coefficient_pos_iff i).2 hiL))
          (mul_nonneg hb.le (ER.coefficient_nonneg i))
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg ha.le (EL.coefficient_nonneg i))
          (mul_pos hb ((ER.coefficient_pos_iff i).2 hiR))
  value_eq_sum := by
    calc
      S.value J = alpha • S.value L + beta • S.value R := hvalue
      _ = alpha • (∑ i, EL.coefficient i • S.anchorValue i) +
          beta • (∑ i, ER.coefficient i • S.anchorValue i) := by
        rw [← EL.value_eq_sum, ← ER.value_eq_sum]
      _ = ∑ i, (alpha * EL.coefficient i + beta * ER.coefficient i) •
          S.anchorValue i := by
        rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp [add_smul, mul_smul]

/-- The module-valued analogue of the positive refinement induction. -/
theorem exists_positiveExpansion
    (S : ModulePositiveRefinementSystem node anchor V) (J : node) :
    Nonempty (FullPositiveModuleAnchorExpansion
      (S.value J) S.anchorValue (S.anchors J)) := by
  classical
  have hmain : ∀ n : ℕ, ∀ J : node, S.measure J = n →
      Nonempty (FullPositiveModuleAnchorExpansion
        (S.value J) S.anchorValue (S.anchors J)) := by
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
          simp [coefficient]
        · obtain ⟨L, R, alpha, beta, ha, hb, hL, hR, hanchors, hvalue⟩ :=
            S.refine J hJ
          obtain ⟨EL⟩ := ih (S.measure L) (by omega) L rfl
          obtain ⟨ER⟩ := ih (S.measure R) (by omega) R rfl
          exact ⟨S.combine (alpha := alpha) (beta := beta)
            ha hb hanchors hvalue EL ER⟩
  exact hmain (S.measure J) J rfl

end ModulePositiveRefinementSystem

end

end PavingToeplitzPositroids
