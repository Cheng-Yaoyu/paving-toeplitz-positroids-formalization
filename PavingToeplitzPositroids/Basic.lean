import ToeplitzPositroids.Matrix.Basic
import ToeplitzPositroids.Matrix.CauchyBinet
import ToeplitzPositroids.Matrix.ColumnMatroid
import ToeplitzPositroids.Matrix.Positroid
import ToeplitzPositroids.Matrix.Toeplitz
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Basic definitions for paving Toeplitz positroids

This file fixes the common finite-index conventions used throughout the
formalization. Matrix rows and columns are zero-indexed in Lean. Thus the
paper's ordinary interval `[a, b]` is represented by the set of finite indices
whose values lie between `a - 1` and `b - 1`.
-/

namespace PavingToeplitzPositroids

open Set ToeplitzPositroids

@[simp]
theorem allRows_apply_eq_self {m : ℕ} (i : Fin m) : allRows m i = i :=
  rfl

/-- The order of a nonzero square subminor is bounded by the matrix rank. -/
theorem orderedMinor_order_le_rank
    {q m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (rows : Fin q ↪o Fin m) (cols : Fin q ↪o Fin n)
    (hminor : orderedMinor A rows cols ≠ 0) :
    q ≤ A.rank := by
  let Ar : Matrix (Fin q) (Fin n) ℝ :=
    A.submatrix rows (Equiv.refl (Fin n))
  let B : Matrix (Fin q) (Fin q) ℝ := A.submatrix rows cols
  have hBdet : B.det ≠ 0 := by
    simpa only [B, orderedMinor] using hminor
  have hBrank : B.rank = q := by
    simpa using Matrix.rank_of_isUnit B
      ((Matrix.isUnit_iff_isUnit_det B).2 (isUnit_iff_ne_zero.mpr hBdet))
  have hcols : B.rank ≤ Ar.rank := by
    have hBT : Ar.transpose.submatrix cols (Equiv.refl (Fin q)) = B.transpose := by
      ext i j
      rfl
    have h := Matrix.rank_submatrix_le cols (Equiv.refl (Fin q)) Ar.transpose
    rw [hBT, Matrix.rank_transpose, Matrix.rank_transpose] at h
    exact h
  have hrows : Ar.rank ≤ A.rank := by
    exact Matrix.rank_submatrix_le rows (Equiv.refl (Fin n)) A
  rw [hBrank] at hcols
  exact hcols.trans hrows

/-- If every ordered maximal minor of a `(p+1)`-row matrix vanishes, its rank
is at most `p`. -/
theorem matrixRank_le_of_all_orderedMaximalMinors_zero
    {p n : ℕ} {A : Matrix (Fin (p + 1)) (Fin n) ℝ}
    (hzero : ∀ cols : Fin (p + 1) ↪o Fin n,
      orderedMinor A (allRows (p + 1)) cols = 0) :
    A.rank ≤ p := by
  by_contra hrank
  have hrankLe : A.rank ≤ p + 1 := by
    simpa using A.rank_le_card_height
  have hrankEq : A.rank = p + 1 := by omega
  obtain ⟨b, hbuniv, _, hspan, hlin⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ A.col)
      (Set.empty_subset (Set.univ : Set (Fin n)))
  have hspan' : Set.range A.col ⊆ Submodule.span ℝ (A.col '' b) := by
    simpa only [Set.image_univ] using hspan
  have hspanEq : Submodule.span ℝ (A.col '' b) =
      Submodule.span ℝ (Set.range A.col) :=
    le_antisymm (Submodule.span_mono (Set.image_subset_range A.col b))
      (Submodule.span_le.mpr hspan')
  let hbfin : b.Finite := Set.toFinite b
  letI := hbfin.fintype
  have hrankb : Module.finrank ℝ (Submodule.span ℝ (A.col '' b)) = b.ncard := by
    have hrange : Set.range (fun x : b ↦ A.col x) = A.col '' b := by
      ext x
      simp
    rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hlin
  have hbcard : b.ncard = p + 1 := by
    rw [hspanEq, ← A.rank_eq_finrank_span_cols, hrankEq] at hrankb
    exact hrankb.symm
  let s : Finset (Fin n) := hbfin.toFinset
  have hscard : s.card = p + 1 := by
    rw [← Set.ncard_eq_toFinset_card b hbfin]
    exact hbcard
  let cols : Fin (p + 1) ↪o Fin n := s.orderEmbOfFin hscard
  have hcolsRange : Set.range cols = b := by
    dsimp only [cols]
    rw [Finset.range_orderEmbOfFin]
    dsimp only [s]
    exact hbfin.coe_toFinset
  have hind : (columnMatroid A).Indep (Set.range cols) := by
    rw [hcolsRange, columnMatroid_indep_iff]
    exact hlin
  have hdet : orderedMinor A (allRows (p + 1)) cols ≠ 0 :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns A cols).2
      ((columnMatroid_indep_range_iff A cols).1 hind)
  exact hdet (hzero cols)

end PavingToeplitzPositroids
