import PavingToeplitzPositroids.TriangularChart
import PavingToeplitzPositroids.ConcreteExchange
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega

/-!
# Coordinate structure of the triangular Jacobian

This file proves the zero-above-diagonal part of Lemma 14 by restricting the
consecutive-minor map to coordinate lines. Later coordinates do not occur in
an earlier consecutive block, so the restricted determinant is constant.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- Changing the first row in only its last entry changes the determinant by
the corresponding signed maximal cofactor. -/
theorem det_updateRow_zero_add_last_single {p : ℕ}
    (B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (r : ℝ) :
    (B.updateRow 0
        (B 0 + r • (Pi.single (Fin.last p) (1 : ℝ) : Fin (p + 1) → ℝ))).det =
      B.det + r *
        ((-1 : ℝ) ^ p *
          (B.submatrix (Fin.succOrderEmb p) Fin.castSuccOrderEmb).det) := by
  rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul]
  rw [← Matrix.adjugate_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub :
      B.submatrix (0 : Fin (p + 1)).succAbove (Fin.last p).succAbove =
        B.submatrix (Fin.succOrderEmb p) Fin.castSuccOrderEmb := by
    ext i j
    simp [Matrix.submatrix_apply, Fin.succOrderEmb, Fin.castSuccOrderEmb]
  rw [hsub]
  simp

/-- The lower-order minor that occurs as the diagonal cofactor in Lemma 14. -/
def homogeneousDiagonalCofactor {p n : ℕ} (hp : p < n) (L : ℕ)
    (t : Fin (n - p)) : ℝ :=
  orderedMinor (homogeneousBaseMatrix p n L) (Fin.succOrderEmb p)
    (Fin.castSuccOrderEmb.trans (consecutiveColumns hp t))

/-- The diagonal cofactor is strictly positive at the complete-homogeneous
base point. -/
theorem homogeneousDiagonalCofactor_pos
    {p n : ℕ} (hp : p < n) {L : ℕ} (hL : p ≤ L)
    (t : Fin (n - p)) :
    0 < homogeneousDiagonalCofactor hp L t := by
  exact homogeneousBase_lowerMinor_pos le_rfl hL (Fin.succOrderEmb p)
    (Fin.castSuccOrderEmb.trans (consecutiveColumns hp t))

/-- The coordinate line through the complete-homogeneous base point. -/
def homogeneousCoordinateLine {p n : ℕ} (hp : p < n) (L : ℕ)
    (s : Fin (n - p)) (r : ℝ) : Fin (n - p) → ℝ :=
  homogeneousBaseCoordinates hp L +
    r • (Pi.single s (1 : ℝ) : Fin (n - p) → ℝ)

/-- The derivative of the coordinate line at zero is the corresponding
standard basis vector. -/
theorem homogeneousCoordinateLine_hasDerivAt
    {p n : ℕ} (hp : p < n) (L : ℕ) (s : Fin (n - p)) :
    HasDerivAt (homogeneousCoordinateLine hp L s) (Pi.single s 1) 0 := by
  change HasDerivAt
    ((fun _ : ℝ ↦ homogeneousBaseCoordinates hp L) +
      fun r : ℝ ↦ r • (Pi.single s (1 : ℝ) : Fin (n - p) → ℝ))
    (Pi.single s 1) 0
  simpa using
    (hasDerivAt_const (x := (0 : ℝ)) (homogeneousBaseCoordinates hp L)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single s (1 : ℝ) : Fin (n - p) → ℝ))

/-- The stored coefficient index of an entry in a consecutive block. -/
@[simp]
theorem finiteToeplitzIndex_consecutiveColumns_val
    {p n : ℕ} (hp : p < n) (t : Fin (n - p))
    (i j : Fin (p + 1)) :
    (finiteToeplitzIndex i (consecutiveColumns hp t j)).val =
      t.val + j.val + (p - i.val) := by
  simp only [finiteToeplitzIndex_val, consecutiveColumns_apply_val]
  have hi := i.isLt
  omega

/-- On its matching coordinate line, a consecutive block changes only in
the top-right entry. -/
theorem homogeneousSlice_consecutiveBlock_diagonalLine_eq
    {p n : ℕ} (hp : p < n) (L : ℕ) (t : Fin (n - p)) (r : ℝ) :
    (homogeneousSliceMatrix hp L (homogeneousCoordinateLine hp L t r)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t) =
      ((homogeneousSliceMatrix hp L
          (homogeneousBaseCoordinates hp L)).submatrix
          (allRows (p + 1)) (consecutiveColumns hp t)).updateRow 0
        (((homogeneousSliceMatrix hp L
            (homogeneousBaseCoordinates hp L)).submatrix
            (allRows (p + 1)) (consecutiveColumns hp t)) 0 +
          r • (Pi.single (Fin.last p) (1 : ℝ) : Fin (p + 1) → ℝ)) := by
  ext i j
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = Fin.last p
    · subst j
      simp only [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one, Matrix.submatrix_apply,
        allRows_apply_eq_self]
      simp only [homogeneousSliceMatrix, finiteToeplitz_apply,
        homogeneousSliceCoefficient]
      split_ifs with hvar
      · let q : Fin (n - p) :=
          ⟨(finiteToeplitzIndex (0 : Fin (p + 1))
            (consecutiveColumns hp t (Fin.last p))).val - 2 * p, by
              have hz := (finiteToeplitzIndex (0 : Fin (p + 1))
                (consecutiveColumns hp t (Fin.last p))).isLt
              omega⟩
        have hq : q = t := by
          apply Fin.ext
          dsimp only [q]
          rw [finiteToeplitzIndex_consecutiveColumns_val]
          simp
          omega
        change homogeneousCoordinateLine hp L t r q =
          homogeneousBaseCoordinates hp L q + r
        rw [hq]
        simp [homogeneousCoordinateLine]
      · simp only [finiteToeplitzIndex_consecutiveColumns_val,
          Fin.val_zero, Fin.val_last, Nat.sub_zero] at hvar
        omega
    · rw [Matrix.updateRow_self]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj,
        smul_eq_mul, mul_zero, add_zero, Matrix.submatrix_apply,
        allRows_apply_eq_self, homogeneousSliceMatrix,
        finiteToeplitz_apply, homogeneousSliceCoefficient]
      split_ifs with hvar
      · let q : Fin (n - p) :=
          ⟨(finiteToeplitzIndex (0 : Fin (p + 1))
            (consecutiveColumns hp t j)).val - 2 * p, by
            have hz := (finiteToeplitzIndex (0 : Fin (p + 1))
              (consecutiveColumns hp t j)).isLt
            omega⟩
        simp only [finiteToeplitzIndex_consecutiveColumns_val,
          Fin.val_zero, Nat.sub_zero] at hvar
        have hqne : q ≠ t := by
          intro h
          have hval := congrArg Fin.val h
          dsimp only [q] at hval
          simp only [finiteToeplitzIndex_consecutiveColumns_val,
            Fin.val_zero, Nat.sub_zero] at hval
          have hjlt := j.isLt
          have hjne := Fin.val_ne_of_ne hj
          simp only [Fin.val_last] at hjne
          omega
        change homogeneousCoordinateLine hp L t r q =
          homogeneousBaseCoordinates hp L q
        simp [homogeneousCoordinateLine, hqne]
      · rfl
  · rw [Matrix.updateRow_ne hi]
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
      homogeneousSliceMatrix, finiteToeplitz_apply, homogeneousSliceCoefficient]
    split_ifs with hvar
    · let q : Fin (n - p) :=
        ⟨(finiteToeplitzIndex i (consecutiveColumns hp t j)).val - 2 * p, by
          have hz := (finiteToeplitzIndex i (consecutiveColumns hp t j)).isLt
          omega⟩
      simp only [finiteToeplitzIndex_consecutiveColumns_val] at hvar
      have hqne : q ≠ t := by
        intro h
        have hval := congrArg Fin.val h
        dsimp only [q] at hval
        simp only [finiteToeplitzIndex_consecutiveColumns_val] at hval
        have hjlt := j.isLt
        have hilt := i.isLt
        have hine := Fin.val_ne_of_ne hi
        simp only [Fin.val_zero] at hine
        omega
      change homogeneousCoordinateLine hp L t r q =
        homogeneousBaseCoordinates hp L q
      simp [homogeneousCoordinateLine, hqne]
    · rfl

/-- The determinant of the subblock obtained by deleting the first row and
last column is exactly the positive cofactor defined above. -/
theorem homogeneousSlice_consecutiveBlock_cofactor_eq
    {p n : ℕ} (hp : p < n) (L : ℕ) (t : Fin (n - p)) :
    ((((homogeneousSliceMatrix hp L (homogeneousBaseCoordinates hp L)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t)).submatrix
        (Fin.succOrderEmb p) Fin.castSuccOrderEmb).det) =
      homogeneousDiagonalCofactor hp L t := by
  rw [homogeneousSliceMatrix_base]
  unfold homogeneousDiagonalCofactor orderedMinor
  congr 1

/-- Along its matching coordinate line, the consecutive determinant is
affine with slope equal to the signed diagonal cofactor. -/
theorem homogeneousConsecutiveMap_diagonalLine_eq
    {p n : ℕ} (hp : p < n) (L : ℕ) (t : Fin (n - p)) (r : ℝ) :
    homogeneousConsecutiveMap hp L (homogeneousCoordinateLine hp L t r) t =
      homogeneousConsecutiveMap hp L (homogeneousBaseCoordinates hp L) t +
        r * ((-1 : ℝ) ^ p * homogeneousDiagonalCofactor hp L t) := by
  unfold homogeneousConsecutiveMap matrixConsecutiveMinor matrixMaximalMinor
    orderedMinor
  rw [homogeneousSlice_consecutiveBlock_diagonalLine_eq]
  rw [det_updateRow_zero_add_last_single]
  rw [homogeneousSlice_consecutiveBlock_cofactor_eq]

/-- At the rank-deficient base point, the matching coordinate restriction is
the linear function with the signed cofactor as slope. -/
theorem homogeneousConsecutiveMap_diagonalLine_eq_smul
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (t : Fin (n - p)) (r : ℝ) :
    homogeneousConsecutiveMap hpn L (homogeneousCoordinateLine hpn L t r) t =
      r * ((-1 : ℝ) ^ p * homogeneousDiagonalCofactor hpn L t) := by
  rw [homogeneousConsecutiveMap_diagonalLine_eq]
  have hbase := congrFun (homogeneousConsecutiveMap_base hp hpn hL) t
  rw [hbase, Pi.zero_apply, zero_add]

/-- A later coefficient coordinate does not occur in an earlier consecutive
block. -/
theorem homogeneousSlice_consecutiveBlock_coordinateLine_eq
    {p n : ℕ} (hp : p < n) (L : ℕ) {t s : Fin (n - p)} (hts : t < s)
    (r : ℝ) :
    (homogeneousSliceMatrix hp L (homogeneousCoordinateLine hp L s r)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t) =
      (homogeneousSliceMatrix hp L (homogeneousBaseCoordinates hp L)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t) := by
  ext i j
  simp only [Matrix.submatrix_apply, allRows,
    homogeneousSliceMatrix, finiteToeplitz_apply, homogeneousSliceCoefficient]
  split_ifs with hvar
  · let q : Fin (n - p) :=
      ⟨(finiteToeplitzIndex i (consecutiveColumns hp t j)).val - 2 * p, by
        have hz := (finiteToeplitzIndex i (consecutiveColumns hp t j)).isLt
        omega⟩
    have hqle : q.val ≤ t.val := by
      dsimp only [q]
      simp only [finiteToeplitzIndex_val, consecutiveColumns_apply_val]
      have hj := j.isLt
      omega
    have hqne : q ≠ s := by
      intro h
      have hval := congrArg Fin.val h
      omega
    change homogeneousCoordinateLine hp L s r q = homogeneousBaseCoordinates hp L q
    simp [homogeneousCoordinateLine, hqne]
  · rfl

/-- Consequently, the corresponding consecutive-minor coordinate is constant
on that line. -/
theorem homogeneousConsecutiveMap_coordinateLine_eq
    {p n : ℕ} (hp : p < n) (L : ℕ) {t s : Fin (n - p)} (hts : t < s)
    (r : ℝ) :
    homogeneousConsecutiveMap hp L (homogeneousCoordinateLine hp L s r) t =
      homogeneousConsecutiveMap hp L (homogeneousBaseCoordinates hp L) t := by
  unfold homogeneousConsecutiveMap matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  rw [homogeneousSlice_consecutiveBlock_coordinateLine_eq hp L hts r]

/-- The Jacobian entry in row `t`, column `s` is zero whenever `t < s`. -/
theorem homogeneousConsecutiveFDeriv_apply_eq_zero_of_lt
    {p n : ℕ} (hp : p < n) (L : ℕ) {t s : Fin (n - p)} (hts : t < s) :
    homogeneousConsecutiveFDeriv hp L (Pi.single s 1) t = 0 := by
  have hphi := (homogeneousConsecutiveMap_hasStrictFDerivAt hp L).hasFDerivAt
  have hline := homogeneousCoordinateLine_hasDerivAt hp L s
  have hcomp := hphi.comp_hasDerivAt_of_eq 0 hline (by
    simp [homogeneousCoordinateLine])
  let proj : (Fin (n - p) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj t
  have hcoord := proj.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have hconst : HasDerivAt
      (fun r : ℝ ↦ homogeneousConsecutiveMap hp L
        (homogeneousCoordinateLine hp L s r) t) 0 0 := by
    convert hasDerivAt_const (x := (0 : ℝ))
      (homogeneousConsecutiveMap hp L (homogeneousBaseCoordinates hp L) t) using 1
    funext r
    exact homogeneousConsecutiveMap_coordinateLine_eq hp L hts r
  have heq := hcoord.unique hconst
  simpa [proj, Function.comp_def] using heq

/-- The diagonal Jacobian entry is the signed positive cofactor from the
matching consecutive block. -/
theorem homogeneousConsecutiveFDeriv_apply_self
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (t : Fin (n - p)) :
    homogeneousConsecutiveFDeriv hpn L (Pi.single t 1) t =
      (-1 : ℝ) ^ p * homogeneousDiagonalCofactor hpn L t := by
  have hphi := (homogeneousConsecutiveMap_hasStrictFDerivAt hpn L).hasFDerivAt
  have hline := homogeneousCoordinateLine_hasDerivAt hpn L t
  have hcomp := hphi.comp_hasDerivAt_of_eq 0 hline (by
    simp [homogeneousCoordinateLine])
  let proj : (Fin (n - p) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj t
  have hcoord := proj.hasFDerivAt.comp_hasDerivAt 0 hcomp
  let c : ℝ := (-1 : ℝ) ^ p * homogeneousDiagonalCofactor hpn L t
  have hlinear : HasDerivAt (fun r : ℝ ↦ r * c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
  have hrestricted : HasDerivAt
      (fun r : ℝ ↦ homogeneousConsecutiveMap hpn L
        (homogeneousCoordinateLine hpn L t r) t) c 0 := by
    convert hlinear using 1
    funext r
    exact homogeneousConsecutiveMap_diagonalLine_eq_smul hp hpn hL t r
  have heq := hcoord.unique hrestricted
  simpa [proj, c, Function.comp_def] using heq

/-- Matrix form of the diagonal formula in Lemma 14. -/
theorem homogeneousConsecutiveFDeriv_diagonal
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (t : Fin (n - p)) :
    continuousLinearMapMatrix (homogeneousConsecutiveFDeriv hpn L) t t =
      (-1 : ℝ) ^ p * homogeneousDiagonalCofactor hpn L t := by
  simp only [continuousLinearMapMatrix, LinearMap.toMatrix'_apply]
  exact homogeneousConsecutiveFDeriv_apply_self hp hpn hL t

/-- Every diagonal entry of the triangular Jacobian is nonzero. -/
theorem homogeneousConsecutiveFDeriv_diagonal_ne_zero
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L) :
    ∀ t, continuousLinearMapMatrix (homogeneousConsecutiveFDeriv hpn L) t t ≠ 0 := by
  intro t
  rw [homogeneousConsecutiveFDeriv_diagonal hp hpn hL]
  exact mul_ne_zero (pow_ne_zero p (by norm_num))
    (ne_of_gt (homogeneousDiagonalCofactor_pos hpn hL t))

/-- The actual Jacobian matrix is lower triangular. -/
theorem homogeneousConsecutiveFDeriv_lowerTriangular
    {p n : ℕ} (hp : p < n) (L : ℕ) :
    (continuousLinearMapMatrix (homogeneousConsecutiveFDeriv hp L)).BlockTriangular
      OrderDual.toDual := by
  intro t s hst
  have hts : t < s := hst
  simp only [continuousLinearMapMatrix, LinearMap.toMatrix'_apply]
  exact homogeneousConsecutiveFDeriv_apply_eq_zero_of_lt hp L hts

/-- The actual derivative of the complete-homogeneous chart, bundled as a
continuous linear equivalence. -/
def homogeneousConsecutiveDerivativeEquiv
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L) :
    (Fin (n - p) → ℝ) ≃L[ℝ] (Fin (n - p) → ℝ) :=
  continuousLinearEquivOfLowerTriangular
    (homogeneousConsecutiveFDeriv hpn L)
    (homogeneousConsecutiveFDeriv_lowerTriangular hpn L)
    (homogeneousConsecutiveFDeriv_diagonal_ne_zero hp hpn hL)

/-- Lemma 14 supplies all analytic data needed for the local chart; only the
concrete sorted Plucker exchange remains as an input. -/
def homogeneousLocalConsecutiveChartFromExchange
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (hexchange : ∀ x, x ∈ strictLowerMinorSet p (p + 1) n
        (homogeneousSliceMatrix hpn L) →
      MatrixLocalPositiveExchange hpn (homogeneousSliceMatrix hpn L x)) :
    LocalConsecutiveChart p n hpn :=
  homogeneousLocalConsecutiveChart hp hpn hL
    (homogeneousConsecutiveDerivativeEquiv hp hpn hL)
    (by simpa using homogeneousConsecutiveMap_hasStrictFDerivAt hpn L)
    hexchange

/-- The complete-homogeneous slice is an unconditional local consecutive
chart: strict lower-minor positivity supplies its sorted mixed-Plucker
exchange. -/
def homogeneousConcreteLocalConsecutiveChart
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L) :
    LocalConsecutiveChart p n hpn := by
  cases p with
  | zero => omega
  | succ r =>
      apply homogeneousLocalConsecutiveChartFromExchange (by omega) hpn hL
      intro x hx
      apply matrixLocalPositiveExchange_of_strictLowerMinorSet hpn
      intro q I J
      exact hx q I J

@[simp]
theorem homogeneousConcreteLocalConsecutiveChart_matrix
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (x : Fin (n - p) → ℝ) :
    (homogeneousConcreteLocalConsecutiveChart hp hpn hL).matrix x =
      homogeneousSliceMatrix hpn L x := by
  cases p with
  | zero => omega
  | succ r => rfl

/-- **Theorem 15 for the triangular Toeplitz chart.** Every sufficiently small
nonnegative consecutive-minor vector has a totally nonnegative Toeplitz
realization with all lower minors positive. -/
theorem homogeneousConcrete_exists_realization_box
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin (n - p) → ℝ,
        (∀ t, 0 ≤ delta t ∧ delta t < eta) →
          Nonempty (LocalTargetRealization
            (homogeneousConcreteLocalConsecutiveChart hp hpn hL) delta) :=
  (homogeneousConcreteLocalConsecutiveChart hp hpn hL).exists_realization_box

/-- **Corollary 16 for the triangular Toeplitz chart.** Every proper zero set
of consecutive maximal minors is realized. -/
theorem homogeneousConcrete_exists_zeroPatternRealization
    {p n L : ℕ} (hp : 0 < p) (hpn : p < n) (hL : p ≤ L)
    (Z : Finset (Fin (n - p))) (hZ : Z ≠ Finset.univ) :
    Nonempty (ZeroPatternRealization
      (homogeneousConcreteLocalConsecutiveChart hp hpn hL) Z) :=
  LocalConsecutiveChart.exists_zeroPatternRealization
    (homogeneousConcreteLocalConsecutiveChart hp hpn hL) Z hZ

end

end PavingToeplitzPositroids
