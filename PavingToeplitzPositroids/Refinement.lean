import PavingToeplitzPositroids.ConcreteExchange
import PavingToeplitzPositroids.Projection

/-!
# Refinement for totally nonnegative paving matrices

This file assembles Theorem 8 from the fixed positive projection, the exact
independence-to-row-minor bridge, and the concrete interpolation theorem.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- The determinant-one row transformation used in Theorem 8. -/
def projectionTransform {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ) :
    Matrix (Fin (k + 1)) (Fin n) ℝ :=
  projectionP k * A

/-- The first rows of the transformed matrix are the fixed positive
projection of the original matrix. -/
theorem firstRows_projectionTransform
    {r n : ℕ} (A : Matrix (Fin (r + 2)) (Fin n) ℝ) :
    firstRows (projectionTransform A) = projectedMatrix A := by
  ext i j
  rfl

/-- Since the row transformation has determinant one, it preserves every
maximal minor. -/
@[simp]
theorem projectionTransform_matrixMaximalMinor
    {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) :
    matrixMaximalMinor (projectionTransform A) J = matrixMaximalMinor A J := by
  unfold matrixMaximalMinor orderedMinor projectionTransform
  have hsub :
      (projectionP k * A).submatrix (allRows (k + 1)) J =
        projectionP k * A.submatrix id J := by
    ext i j
    simp [Matrix.mul_apply, allRows]
  rw [hsub, Matrix.det_mul, projectionP_det, one_mul]
  congr 1

/-- Consecutive maximal minors are also preserved. -/
@[simp]
theorem projectionTransform_matrixConsecutiveMinor
    {k n : ℕ} (hk : k < n) (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (t : Fin (n - k)) :
    matrixConsecutiveMinor hk (projectionTransform A) t =
      matrixConsecutiveMinor hk A t := by
  unfold matrixConsecutiveMinor
  exact projectionTransform_matrixMaximalMinor A _

/-- The projected first-row block has strictly positive maximal minors under
the manuscript's independence hypothesis. -/
theorem firstRows_projectionTransform_maximalMinor_pos
    {r n : ℕ} {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (cols : Fin (r + 1) ↪o Fin n) :
    0 < orderedMinor (firstRows (projectionTransform A))
      (allRows (r + 1)) cols := by
  rw [firstRows_projectionTransform]
  exact projectedMatrix_orderedMinor_pos_of_linearIndependent hA cols (hind cols)

/-- **Theorem 8, positive interpolation form.** Every maximal minor is a
strictly positive combination of all its consecutive anchors. -/
theorem exists_refinement_interpolation
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (J : Fin (r + 2) ↪o Fin n) :
    Nonempty (FullPositiveAnchorExpansion (matrixMaximalMinor A J)
      (matrixConsecutiveMinor hrn A) (anchorFinset J)) := by
  let E : MatrixLocalPositiveExchange hrn (projectionTransform A) :=
    matrixLocalPositiveExchange_of_firstRows_pos hrn (projectionTransform A)
      (firstRows_projectionTransform_maximalMinor_pos hA hind)
  obtain ⟨F⟩ := E.exists_interpolation J
  rw [projectionTransform_matrixMaximalMinor A J] at F
  have hD : matrixConsecutiveMinor hrn (projectionTransform A) =
      matrixConsecutiveMinor hrn A := by
    funext t
    exact projectionTransform_matrixConsecutiveMinor hrn A t
  rw [hD] at F
  exact ⟨F⟩

/-- **Theorem 8, support form.** A maximal minor vanishes exactly when all
consecutive anchors in its endpoint interval vanish. -/
theorem refinement_maximalMinor_eq_zero_iff
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)))
    (J : Fin (r + 2) ↪o Fin n) :
    matrixMaximalMinor A J = 0 ↔
      ∀ t ∈ anchorFinset J, matrixConsecutiveMinor hrn A t = 0 := by
  obtain ⟨F⟩ := exists_refinement_interpolation hrn hA hind J
  apply F.value_eq_zero_iff
  intro t
  change 0 ≤ orderedMinor A (allRows (r + 2)) (consecutiveColumns hrn t)
  exact hA.orderedMinor_nonneg _ _

end

end PavingToeplitzPositroids
