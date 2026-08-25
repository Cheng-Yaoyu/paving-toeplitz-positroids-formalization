import PavingToeplitzPositroids.Basic
import PavingToeplitzPositroids.Projection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The exact 4 x 6 example

This file verifies Section 10 over the rationals. All finite universal claims
are decided by evaluating Lean's determinant definition; no external
computation is trusted.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

/-- The Toeplitz coefficients of the paper's example, stored in the order
`a_{-3}, ..., a_5`. -/
def exactExampleCoefficients : Fin 9 → ℚ :=
  ![3, 6, 10, 15, 21, 28, 36, 2249 / 50, 27443 / 500]

/-- The exact rational `4 x 6` Toeplitz matrix from Section 10. -/
def exactExampleMatrix : Matrix (Fin 4) (Fin 6) ℚ :=
  finiteToeplitz exactExampleCoefficients

/-- The Toeplitz constructor gives the displayed matrix. -/
theorem exactExampleMatrix_eq :
    exactExampleMatrix =
      !![15, 21, 28, 36, 2249 / 50, 27443 / 500;
         10, 15, 21, 28, 36, 2249 / 50;
         6, 10, 15, 21, 28, 36;
         3, 6, 10, 15, 21, 28] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exactExampleMatrix, exactExampleCoefficients, finiteToeplitz,
      finiteToeplitzIndex]

/-- The increasing block of four columns starting at `t`. -/
def exactConsecutiveColumns (t : Fin 3) : Fin 4 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (⟨t.val + i.val, by omega⟩ : Fin 6))
    (by intro i j hij; simp only [Fin.mk_lt_mk] at hij ⊢; omega)

/-- Equation (10.2) at `epsilon = 1/50`. -/
theorem exactExample_consecutiveMinors :
    (fun t : Fin 3 ↦
      orderedMinor exactExampleMatrix (allRows 4) (exactConsecutiveColumns t)) =
      ![0, 1 / 50, 0] := by
  funext t
  fin_cases t <;>
    rw [orderedMinor, Matrix.det_succ_row_zero, Fin.sum_univ_four] <;>
    simp_rw [Matrix.det_fin_three] <;>
    simp [Fin.succAbove, Fin.castSucc, Fin.succ] <;>
    norm_num [exactConsecutiveColumns, exactExampleMatrix, exactExampleCoefficients,
      finiteToeplitz, finiteToeplitzIndex, allRows]

/-- Every entry is strictly positive. -/
theorem exactExample_orderOne_pos :
    ∀ (rows : Fin 1 ↪o Fin 4) (cols : Fin 1 ↪o Fin 6),
      0 < orderedMinor exactExampleMatrix rows cols := by
  intro rows cols
  rw [orderedMinor_one]
  generalize hrow : rows 0 = row
  generalize hcol : cols 0 = col
  fin_cases row <;> fin_cases col <;>
    norm_num [exactExampleMatrix, exactExampleCoefficients, finiteToeplitz,
      finiteToeplitzIndex]

/-- Row pair `3,4` in one-based notation. -/
def exactRows23 : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono ![2, 3] (by decide)

/-- The first two columns. -/
def exactCols01 : Fin 2 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono ![0, 1] (by decide)

/-- The lower bound six for `2 x 2` minors is attained. -/
theorem exactExample_orderTwo_eq_six :
    ∃ (rows : Fin 2 ↪o Fin 4) (cols : Fin 2 ↪o Fin 6),
      orderedMinor exactExampleMatrix rows cols = 6 := by
  refine ⟨exactRows23, exactCols01, ?_⟩
  norm_num [orderedMinor_two, exactRows23, exactCols01, exactExampleMatrix,
    exactExampleCoefficients, finiteToeplitz, finiteToeplitzIndex, Matrix.cons_val_two]

/-- Every `2 x 2` minor is at least six, so the displayed witness is the
global minimum claimed in Section 10. -/
theorem exactExample_orderTwo_ge_six :
    ∀ (rows : Fin 2 ↪o Fin 4) (cols : Fin 2 ↪o Fin 6),
      6 ≤ orderedMinor exactExampleMatrix rows cols := by
  intro rows cols
  have hrows : rows 0 < rows 1 := rows.strictMono (by decide)
  have hcols : cols 0 < cols 1 := cols.strictMono (by decide)
  generalize hrow0 : rows 0 = row0 at hrows ⊢
  generalize hrow1 : rows 1 = row1 at hrows ⊢
  generalize hcol0 : cols 0 = col0 at hcols ⊢
  generalize hcol1 : cols 1 = col1 at hcols ⊢
  rw [orderedMinor_two, hrow0, hrow1, hcol0, hcol1]
  fin_cases row0 <;> fin_cases row1 <;> fin_cases col0 <;> fin_cases col1
  all_goals try norm_num at hrows
  all_goals try norm_num at hcols
  all_goals norm_num [exactExampleMatrix, exactExampleCoefficients, finiteToeplitz,
    finiteToeplitzIndex]

/-- The first three rows. -/
def exactRows012 : Fin 3 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2] (by decide)

/-- The last three columns. -/
def exactCols345 : Fin 3 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono ![3, 4, 5] (by decide)

/-- The lower bound `841/2500` for `3 x 3` minors is attained. -/
theorem exactExample_orderThree_eq :
    ∃ (rows : Fin 3 ↪o Fin 4) (cols : Fin 3 ↪o Fin 6),
      orderedMinor exactExampleMatrix rows cols = 841 / 2500 := by
  refine ⟨exactRows012, exactCols345, ?_⟩
  norm_num [orderedMinor_three, exactRows012, exactCols345, exactExampleMatrix,
    exactExampleCoefficients, finiteToeplitz, finiteToeplitzIndex, Matrix.cons_val_two]

set_option maxHeartbeats 800000 in
-- The transparent finite case split normalizes all eighty `3 x 3` minors.
/-- Every `3 x 3` minor is at least `841/2500`, completing the exhaustive
lower-minor verification in Section 10. -/
theorem exactExample_orderThree_ge :
    ∀ (rows : Fin 3 ↪o Fin 4) (cols : Fin 3 ↪o Fin 6),
      841 / 2500 ≤ orderedMinor exactExampleMatrix rows cols := by
  intro rows cols
  obtain ⟨missingRow, rfl⟩ := exists_eq_succAboveOrderEmb rows
  have hcols01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have hcols12 : cols 1 < cols 2 := cols.strictMono (by decide)
  generalize hcol0 : cols 0 = col0 at hcols01 ⊢
  generalize hcol1 : cols 1 = col1 at hcols01 hcols12 ⊢
  generalize hcol2 : cols 2 = col2 at hcols12 ⊢
  rw [orderedMinor_three, hcol0, hcol1, hcol2]
  fin_cases missingRow <;> fin_cases col0 <;> fin_cases col1 <;> fin_cases col2
  all_goals try norm_num at hcols01
  all_goals try norm_num at hcols12
  all_goals simp [Fin.succAbove, Fin.castSucc, Fin.succ]
  all_goals norm_num [exactExampleMatrix, exactExampleCoefficients, finiteToeplitz,
    finiteToeplitzIndex, Fin.succAboveOrderEmb_apply, Matrix.cons_val_two]

/-- The fifteen increasing four-column vectors in lexicographic order. -/
def exactMaximalColumnVector : Fin 15 → Fin 4 → Fin 6 :=
  ![![0, 1, 2, 3], ![0, 1, 2, 4], ![0, 1, 2, 5],
    ![0, 1, 3, 4], ![0, 1, 3, 5], ![0, 1, 4, 5],
    ![0, 2, 3, 4], ![0, 2, 3, 5], ![0, 2, 4, 5], ![0, 3, 4, 5],
    ![1, 2, 3, 4], ![1, 2, 3, 5], ![1, 2, 4, 5], ![1, 3, 4, 5],
    ![2, 3, 4, 5]]

theorem exactMaximalColumnVector_strictMono (t : Fin 15) :
    StrictMono (exactMaximalColumnVector t) := by
  fin_cases t <;> decide

/-- Increasing enumerations of the fifteen maximal column sets. -/
def exactMaximalColumns (t : Fin 15) : Fin 4 ↪o Fin 6 :=
  OrderEmbedding.ofStrictMono (exactMaximalColumnVector t)
    (exactMaximalColumnVector_strictMono t)

/-- Increasing `q`-column selections are equivalent to `q`-element
finsets.  This is used to certify that the displayed list is exhaustive. -/
def orderEmbeddingEquivFinset (q n : ℕ) :
    (Fin q ↪o Fin n) ≃ {s : Finset (Fin n) // s.card = q} where
  toFun f := ⟨Finset.univ.map f.toEmbedding, by simp⟩
  invFun s := s.1.orderEmbOfFin s.2
  left_inv f := by
    apply OrderEmbedding.range_inj.mp
    rw [Finset.range_orderEmbOfFin]
    simp
  right_inv s := by
    apply Subtype.ext
    change Finset.univ.map (s.1.orderEmbOfFin s.2).toEmbedding = s.1
    apply Finset.coe_injective
    simpa only [Finset.coe_map, Finset.coe_univ, Set.image_univ] using
      Finset.range_orderEmbOfFin s.1 s.2

/-- There are exactly fifteen increasing selections of four columns from six. -/
theorem card_orderEmbedding_fin_four_six :
    Fintype.card (Fin 4 ↪o Fin 6) = 15 := by
  rw [Fintype.card_congr (orderEmbeddingEquivFinset 4 6),
    Fintype.card_finset_len]
  norm_num [Nat.choose]

set_option maxHeartbeats 2000000 in
-- The finite injectivity check normalizes all 225 pairs in the displayed list.
/-- The hard-coded list contains no repeated four-column selection. -/
theorem exactMaximalColumns_injective :
    Function.Injective exactMaximalColumns := by
  intro t s h
  have hv : exactMaximalColumnVector t = exactMaximalColumnVector s := by
    funext i
    exact congrArg (fun J : Fin 4 ↪o Fin 6 ↦ J i) h
  fin_cases t <;> fin_cases s <;>
    simp_all [exactMaximalColumnVector]

/-- The fifteen listed selections exhaust all increasing four-column
selections from six columns. -/
theorem exactMaximalColumns_surjective :
    Function.Surjective exactMaximalColumns :=
  ((Fintype.bijective_iff_injective_and_card exactMaximalColumns).2
    ⟨exactMaximalColumns_injective, by
      rw [Fintype.card_fin, card_orderEmbedding_fin_four_six]⟩).2

/-- The displayed list is an exact enumeration, with neither repetitions nor
omissions. -/
theorem exactMaximalColumns_bijective :
    Function.Bijective exactMaximalColumns :=
  ⟨exactMaximalColumns_injective, exactMaximalColumns_surjective⟩

/-- The maximal-minor values displayed in Section 10. -/
def exactMaximalMinorTable : Fin 15 → ℚ :=
  ![0, 1 / 50, 27 / 500,
    3 / 50, 81 / 500, 79 / 625,
    3 / 50, 81 / 500, 69 / 500, 87 / 2500,
    1 / 50, 27 / 500, 23 / 500, 29 / 2500, 0]

/-- Exact verification of all fifteen maximal minors in the paper's table. -/
theorem exactExample_maximalMinor_table :
    (fun t : Fin 15 ↦ orderedMinor exactExampleMatrix (allRows 4)
      (exactMaximalColumns t)) = exactMaximalMinorTable := by
  funext t
  fin_cases t
  all_goals simp only [exactMaximalColumns, exactMaximalColumnVector,
    exactMaximalMinorTable]
  all_goals rw [orderedMinor, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  all_goals simp_rw [Matrix.det_fin_three]
  all_goals simp [Fin.succAbove, Fin.castSucc, Fin.succ]
  all_goals norm_num [exactExampleMatrix, exactExampleCoefficients, finiteToeplitz,
      finiteToeplitzIndex, allRows, Matrix.cons_val_two]

/-- Exhaustive form of the maximal-minor table: every increasing maximal
column selection occurs at a unique row of the displayed table. -/
theorem exactExample_every_maximalMinor_in_table
    (J : Fin 4 ↪o Fin 6) :
    ∃! t : Fin 15, exactMaximalColumns t = J ∧
      orderedMinor exactExampleMatrix (allRows 4) J = exactMaximalMinorTable t := by
  obtain ⟨t, ht⟩ := exactMaximalColumns_surjective J
  refine ⟨t, ⟨ht, ?_⟩, ?_⟩
  · rw [← ht]
    exact congrFun exactExample_maximalMinor_table t
  · intro s hs
    exact exactMaximalColumns_injective (hs.1.trans ht.symm)

end PavingToeplitzPositroids
