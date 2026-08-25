import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Invertibility of finite triangular continuous linear maps

This supplies the linear-algebra conclusion of Lemma 14 independently of the
coordinate derivative calculation.
-/

namespace PavingToeplitzPositroids

noncomputable section

/-- The standard-basis matrix of a continuous linear endomorphism of a finite
real coordinate space. -/
def continuousLinearMapMatrix {N : ℕ}
    (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' L.toLinearMap

/-- A triangular continuous linear endomorphism with nonzero diagonal is
injective. -/
theorem continuousLinearMap_injective_of_lowerTriangular
    {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (htri : (continuousLinearMapMatrix L).BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, continuousLinearMapMatrix L i i ≠ 0) :
    Function.Injective L := by
  have hdetMatrix : (continuousLinearMapMatrix L).det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ htri]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hdiag i
  have hdet : L.toLinearMap.det ≠ 0 := by
    rw [← LinearMap.det_toMatrix']
    exact hdetMatrix
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

/-- Bundle a triangular continuous linear endomorphism as an equivalence. -/
def continuousLinearEquivOfLowerTriangular
    {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (htri : (continuousLinearMapMatrix L).BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, continuousLinearMapMatrix L i i ≠ 0) :
    (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := by
  have hinj := continuousLinearMap_injective_of_lowerTriangular L htri hdiag
  exact ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj))

/-- The bundled equivalence has the original continuous linear map. -/
@[simp]
theorem continuousLinearEquivOfLowerTriangular_toContinuousLinearMap
    {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (htri : (continuousLinearMapMatrix L).BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, continuousLinearMapMatrix L i i ≠ 0) :
    (continuousLinearEquivOfLowerTriangular L htri hdiag).toContinuousLinearMap = L := by
  ext x
  rfl

end

end PavingToeplitzPositroids
