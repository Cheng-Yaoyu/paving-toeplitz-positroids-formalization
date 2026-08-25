import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Directional derivative of a finite determinant

This file proves the finite-dimensional determinant derivative directly from
the Leibniz formula. The derivative in direction `H` is the sum of the
determinants obtained by replacing one column of the base matrix by the
corresponding column of `H`.
-/

namespace PavingToeplitzPositroids

open Matrix

noncomputable section

/-- Directional derivative of the determinant along an affine matrix line. -/
theorem hasDerivAt_det_add_smul {m : ℕ}
    (B H : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun r : ℝ ↦ (B + r • H).det)
      (∑ j : Fin m, (B.updateCol j (fun i ↦ H i j)).det) 0 := by
  have hperm : ∀ σ : Equiv.Perm (Fin m),
      HasDerivAt
        (fun r : ℝ ↦ (Equiv.Perm.sign σ : ℝ) *
          ∏ j : Fin m, (B + r • H) (σ j) j)
        ((Equiv.Perm.sign σ : ℝ) *
          ∑ j : Fin m, (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j,
            B (σ k) k) * H (σ j) j) 0 := by
    intro σ
    have hf : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        HasDerivAt (fun r : ℝ ↦ (B + r • H) (σ j) j) (H (σ j) j) 0 := by
      intro j hj
      change HasDerivAt (fun r : ℝ ↦ B (σ j) j + r * H (σ j) j)
        (H (σ j) j) 0
      simpa only [id_eq, one_mul] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (H (σ j) j)).const_add
          (B (σ j) j)
    have hp := HasDerivAt.fun_finset_prod hf
    have hc := hp.const_mul (Equiv.Perm.sign σ : ℝ)
    simpa [smul_eq_mul] using hc
  have hsum := HasDerivAt.fun_sum fun σ (_ : σ ∈ (Finset.univ : Finset
      (Equiv.Perm (Fin m)))) ↦ hperm σ
  have hfun : (fun r : ℝ ↦ (B + r • H).det) =
      fun r : ℝ ↦ ∑ σ : Equiv.Perm (Fin m),
        (Equiv.Perm.sign σ : ℝ) * ∏ j : Fin m, (B + r • H) (σ j) j := by
    funext r
    rw [Matrix.det_apply']
  rw [← hfun] at hsum
  convert hsum using 1
  simp_rw [Matrix.det_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.updateCol_apply]
  rw [show (∏ i : Fin m, if i = j then H (σ i) j else B (σ i) i) =
      (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, B (σ k) k) *
        H (σ j) j by
    rw [Finset.prod_ite]
    have hfilter : (Finset.univ.filter fun x : Fin m ↦ x = j) = {j} := by
      ext x
      simp
    have hfirst : (∏ x ∈ (Finset.univ : Finset (Fin m)) with x = j,
        H (σ x) j) = H (σ j) j := by
      rw [hfilter]
      simp
    have hsecond : (Finset.univ.filter fun x : Fin m ↦ ¬x = j) =
        (Finset.univ : Finset (Fin m)).erase j := by
      ext x
      simp [eq_comm]
    rw [hfirst, hsecond]
    ring]

/-- Cofactor form of the determinant directional derivative. -/
theorem hasDerivAt_det_add_smul_adjugate {p : ℕ}
    (B H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) :
    HasDerivAt (fun r : ℝ ↦ (B + r • H).det)
      (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
        H i j * B.adjugate j i) 0 := by
  have h := hasDerivAt_det_add_smul B H
  have hderiv :
      (∑ j : Fin (p + 1), (B.updateCol j (fun i ↦ H i j)).det) =
        ∑ i : Fin (p + 1), ∑ j : Fin (p + 1), H i j * B.adjugate j i := by
    have hcol : ∀ j : Fin (p + 1),
        (B.updateCol j (fun i ↦ H i j)).det =
          ∑ i : Fin (p + 1), H i j * B.adjugate j i := by
      intro j
      conv_lhs => rw [Matrix.det_succ_column _ j]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Matrix.updateCol_self, Matrix.submatrix_updateCol_succAbove]
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      ring
    calc
      _ = ∑ j : Fin (p + 1), ∑ i : Fin (p + 1),
          H i j * B.adjugate j i := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hcol j
      _ = _ := Finset.sum_comm
  rw [hderiv] at h
  exact h

end

end PavingToeplitzPositroids
