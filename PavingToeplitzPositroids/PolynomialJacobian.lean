import PavingToeplitzPositroids.PolynomialBase
import PavingToeplitzPositroids.PascalKernel
import PavingToeplitzPositroids.DeterminantDerivative
import PavingToeplitzPositroids.TriangularLinear

/-!
# Polynomial block kernels and Jacobian cofactors

This file develops the algebraic part of Theorem 18. The alternating binomial
vector is shown to be both a left and right kernel vector of every consecutive
polynomial base block.
-/

namespace PavingToeplitzPositroids

open Matrix Polynomial ToeplitzPositroids

noncomputable section

/-- A consecutive square block of the polynomial base matrix. -/
def polynomialBaseBlock {p n : ℕ} (hp : p < n) (M : ℕ)
    (t : Fin (n - p)) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  (finiteToeplitz (polynomialStoredCoefficient (n := n) p M)).submatrix
    (allRows (p + 1)) (consecutiveColumns hp t)

/-- The consecutive block inherits the global monomial factorization. -/
theorem polynomialBaseBlock_factor
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t : Fin (n - p)) :
    polynomialBaseBlock hp M t =
      polynomialLeftFeature p M *
        (polynomialRightFeature p n).submatrix id (consecutiveColumns hp t) := by
  unfold polynomialBaseBlock
  rw [finiteToeplitz_polynomialStoredCoefficient_factor hp0 hM]
  ext i j
  simp [Matrix.mul_apply, allRows]

/-- The selected right feature matrix kills the alternating binomial vector. -/
theorem polynomialRightFeature_consecutive_mulVec_eq_zero
    {p n : ℕ} (hp : p < n) (t : Fin (n - p)) :
    (polynomialRightFeature p n).submatrix id (consecutiveColumns hp t) *ᵥ
        alternatingBinomialVector p = 0 := by
  funext l
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.id_def,
    polynomialRightFeature, consecutiveColumns_apply_val, Pi.zero_apply]
  let e := p - 1 - l.val
  let P : ℝ[X] := (Polynomial.X + Polynomial.C (t.val : ℝ)) ^ e
  have he : e < p := by
    have hl := l.isLt
    dsimp only [e]
    omega
  have hPdeg : P.natDegree < p := by
    have hdeg : P.natDegree ≤ e := by
      dsimp only [P]
      calc
        ((Polynomial.X + Polynomial.C (t.val : ℝ)) ^ e).natDegree ≤
            e * (Polynomial.X + Polynomial.C (t.val : ℝ)).natDegree :=
          Polynomial.natDegree_pow_le
        _ ≤ e := by rw [Polynomial.natDegree_X_add_C, mul_one]
    omega
  have hzero := alternatingBinomialEval_eq_zero_of_natDegree_lt P hPdeg
  unfold alternatingBinomialEval at hzero
  simpa [P, e, Polynomial.eval_add, add_comm, add_left_comm, add_assoc, mul_comm] using hzero

/-- The alternating binomial vector also kills the left feature matrix from
the left. -/
theorem alternatingBinomialVector_vecMul_polynomialLeftFeature_eq_zero
    {p M : ℕ} (hM : p ≤ M) :
    alternatingBinomialVector p ᵥ* polynomialLeftFeature p M = 0 := by
  funext l
  simp only [Matrix.vecMul, dotProduct, polynomialLeftFeature, Pi.zero_apply]
  let P : ℝ[X] := (Polynomial.C (M : ℝ) - Polynomial.X) ^ l.val
  have hPdeg : P.natDegree < p := by
    have hdeg : P.natDegree ≤ l.val := by
      dsimp only [P]
      calc
        ((Polynomial.C (M : ℝ) - Polynomial.X) ^ l.val).natDegree ≤
            l.val * (Polynomial.C (M : ℝ) - Polynomial.X).natDegree :=
          Polynomial.natDegree_pow_le
        _ ≤ l.val := by
          rw [show Polynomial.C (M : ℝ) - Polynomial.X =
            -(Polynomial.X - Polynomial.C (M : ℝ)) by ring,
            Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C, mul_one]
    exact hdeg.trans_lt l.isLt
  have hzero := alternatingBinomialEval_eq_zero_of_natDegree_lt P hPdeg
  unfold alternatingBinomialEval at hzero
  have heval :
      (∑ i : Fin (p + 1), alternatingBinomialVector p i *
        (((M - i.val : ℕ) : ℝ) ^ l.val)) = 0 := by
    rw [← hzero]
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i.val ≤ M := by
      have hi' := i.isLt
      omega
    simp only [P, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X]
    rw [Nat.cast_sub hiM]
  calc
    (∑ i : Fin (p + 1), alternatingBinomialVector p i *
      (((M - i.val : ℕ) : ℝ) ^ l.val * Nat.choose (p - 1) l.val)) =
        (Nat.choose (p - 1) l.val : ℝ) *
          ∑ i : Fin (p + 1), alternatingBinomialVector p i *
            (((M - i.val : ℕ) : ℝ) ^ l.val) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
    _ = 0 := by rw [heval, mul_zero]

/-- Every polynomial base block has the alternating binomial right kernel. -/
theorem polynomialBaseBlock_mulVec_eq_zero
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t : Fin (n - p)) :
    polynomialBaseBlock hp M t *ᵥ alternatingBinomialVector p = 0 := by
  rw [polynomialBaseBlock_factor hp0 hp hM, ← Matrix.mulVec_mulVec,
    polynomialRightFeature_consecutive_mulVec_eq_zero hp t,
    Matrix.mulVec_zero]

/-- Every polynomial base block has the same alternating binomial left
kernel. -/
theorem alternatingBinomialVector_vecMul_polynomialBaseBlock_eq_zero
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t : Fin (n - p)) :
    alternatingBinomialVector p ᵥ* polynomialBaseBlock hp M t = 0 := by
  rw [polynomialBaseBlock_factor hp0 hp hM, ← Matrix.vecMul_vecMul,
    alternatingBinomialVector_vecMul_polynomialLeftFeature_eq_zero hM,
    Matrix.zero_vecMul]

/-- A vector in the kernel is determined by its first coordinate when the
minor obtained by deleting the first row and column is nonsingular. -/
theorem eq_smul_kernelVector_of_mulVec_eq_zero
    {p : ℕ} (B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (b z : Fin (p + 1) → ℝ) (hb0 : b 0 = 1)
    (hb : B *ᵥ b = 0)
    (hminor : (B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p)).det ≠ 0)
    (hz : B *ᵥ z = 0) :
    z = z 0 • b := by
  let w : Fin (p + 1) → ℝ := z - z 0 • b
  have hw0 : w 0 = 0 := by simp [w, hb0]
  have hBw : B *ᵥ w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hz, hb, smul_zero, sub_zero]
  let wt : Fin p → ℝ := fun i ↦ w i.succ
  let Q := B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p)
  have hQw : Q *ᵥ wt = 0 := by
    funext i
    have hrow := congrFun hBw i.succ
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hrow ⊢
    rw [Fin.sum_univ_succ] at hrow
    simpa [Q, wt, Matrix.submatrix_apply, hw0] using hrow
  have hwt : wt = 0 := Matrix.eq_zero_of_mulVec_eq_zero hminor hQw
  apply sub_eq_zero.mp
  change w = 0
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using hw0
  · exact congrFun hwt j

/-- The analogous uniqueness statement for the left kernel. -/
theorem eq_smul_kernelVector_of_vecMul_eq_zero
    {p : ℕ} (B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (b z : Fin (p + 1) → ℝ) (hb0 : b 0 = 1)
    (hb : b ᵥ* B = 0)
    (hminor : (B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p)).det ≠ 0)
    (hz : z ᵥ* B = 0) :
    z = z 0 • b := by
  apply eq_smul_kernelVector_of_mulVec_eq_zero Bᵀ b z hb0
  · simpa only [Matrix.mulVec_transpose] using hb
  · have hsub : Bᵀ.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p) =
        (B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p))ᵀ := by
      ext i j
      rfl
    rw [hsub, Matrix.det_transpose]
    exact hminor
  · simpa only [Matrix.mulVec_transpose] using hz

/-- The positive cofactor obtained by deleting the first row and first column
of a polynomial base block. -/
def polynomialBlockKappa {p n : ℕ} (hp : p < n) (M : ℕ)
    (t : Fin (n - p)) : ℝ :=
  ((polynomialBaseBlock hp M t).submatrix
    (Fin.succOrderEmb p) (Fin.succOrderEmb p)).det

/-- The closed scalar multiplying the finite-difference kernel in the
polynomial chart.  With `p = m - 1`, this is
`(∏ l, choose (m-2) l) * (∏ j=1..m-2 j!)^2`. -/
def polynomialJacobianKappa (p : ℕ) : ℝ :=
  (∏ l : Fin p, (Nat.choose (p - 1) l.val : ℝ)) *
    (Nat.superFactorial (p - 1) : ℝ) ^ 2

/-- The block cofactor `kappa_t` is strictly positive. -/
theorem polynomialBlockKappa_pos
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t : Fin (n - p)) :
    0 < polynomialBlockKappa hp M t := by
  unfold polynomialBlockKappa polynomialBaseBlock
  have heq :
      ((finiteToeplitz (polynomialStoredCoefficient (n := n) p M)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t)).submatrix
          (Fin.succOrderEmb p) (Fin.succOrderEmb p) =
      (finiteToeplitz (polynomialStoredCoefficient (n := n) p M)).submatrix
        (Fin.succOrderEmb p)
        ((Fin.succOrderEmb p).trans (consecutiveColumns hp t)) := by
    ext i j
    simp [Matrix.submatrix_apply]
  rw [heq]
  exact polynomialBase_orderP_minor_pos hp0 hM (Fin.succOrderEmb p)
    ((Fin.succOrderEmb p).trans (consecutiveColumns hp t))

/-- The block cofactor is independent of the consecutive-block position and
has the explicit closed value from the strengthened form of Theorem 18. -/
theorem polynomialBlockKappa_eq_polynomialJacobianKappa
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t : Fin (n - p)) :
    polynomialBlockKappa hp M t = polynomialJacobianKappa p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0.ne'
  let rows : Fin (d + 1) ↪o Fin (d + 2) := Fin.succOrderEmb (d + 1)
  let cols : Fin (d + 1) ↪o Fin n :=
    (Fin.succOrderEmb (d + 1)).trans (consecutiveColumns hp t)
  let Lm : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    (polynomialLeftFeature (d + 1) M).submatrix rows id
  let Rm : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    (polynomialRightFeature (d + 1) n).submatrix id cols
  let Lrev : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Lm.submatrix Fin.rev id
  let Rrev : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Rm.submatrix Fin.rev id
  let x : Fin (d + 1) → ℝ := fun i ↦
    ((M - (rows (Fin.rev i)).val : ℕ) : ℝ)
  let y : Fin (d + 1) → ℝ := fun j ↦ (cols j).val
  have hcofactor :
      (polynomialBaseBlock hp M t).submatrix
          (Fin.succOrderEmb (d + 1)) (Fin.succOrderEmb (d + 1)) =
        Lm * Rm := by
    rw [polynomialBaseBlock_factor (by omega) hp hM]
    ext i j
    simp [Lm, Rm, rows, cols, Matrix.mul_apply]
  have hx : x = fun i : Fin (d + 1) ↦
      (i.val : ℝ) + ((M - (d + 1) : ℕ) : ℝ) := by
    funext i
    dsimp only [x, rows]
    push_cast
    simp only [Fin.val_succ, Fin.val_rev]
    rw [← Nat.cast_add]
    norm_cast
    omega
  have hy : y = fun j : Fin (d + 1) ↦
      (j.val : ℝ) + ((t.val + 1 : ℕ) : ℝ) := by
    funext j
    dsimp only [y, cols]
    simp only [RelEmbedding.coe_trans, Function.comp_apply,
      Fin.coe_succOrderEmb, consecutiveColumns_apply_val]
    rw [← Nat.cast_add]
    norm_cast
    simp only [Fin.val_succ]
    omega
  have hLrev : Lrev = Matrix.vandermonde x *
      Matrix.diagonal (fun l : Fin (d + 1) ↦ (Nat.choose d l.val : ℝ)) := by
    ext i l
    simp [Lrev, Lm, x, polynomialLeftFeature, Matrix.mul_diagonal]
  have hRrev : Rrev = (Matrix.vandermonde y)ᵀ := by
    ext i j
    simp only [Rrev, Rm, Matrix.submatrix_apply, Function.id_def,
      polynomialRightFeature, Matrix.transpose_apply, Matrix.vandermonde_apply, y]
    congr 1
    simp only [Fin.val_rev]
    omega
  have hLrevDet : Lrev.det =
      (Nat.superFactorial d : ℝ) *
        ∏ l : Fin (d + 1), (Nat.choose d l.val : ℝ) := by
    rw [hLrev, Matrix.det_mul, Matrix.det_diagonal, hx,
      Matrix.det_vandermonde_add,
      Matrix.det_vandermonde_id_eq_superFactorial]
  have hRrevDet : Rrev.det = Nat.superFactorial d := by
    rw [hRrev, Matrix.det_transpose, hy, Matrix.det_vandermonde_add,
      Matrix.det_vandermonde_id_eq_superFactorial]
  have hLsign := Matrix.det_permute Fin.revPerm Lm
  have hRsign := Matrix.det_permute Fin.revPerm Rm
  change Lrev.det = _ at hLsign
  change Rrev.det = _ at hRsign
  have hdetProduct : Lm.det * Rm.det = Lrev.det * Rrev.det := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (@Fin.revPerm (d + 1))) with hs | hs
    · simp only [hs, Units.val_one, Int.cast_one, one_mul] at hLsign hRsign
      rw [hLsign, hRsign]
    · simp only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
        neg_mul] at hLsign hRsign
      rw [hLsign, hRsign]
      ring
  unfold polynomialBlockKappa
  rw [hcofactor, Matrix.det_mul, hdetProduct, hLrevDet, hRrevDet]
  simp only [polynomialJacobianKappa, Nat.succ_sub_one]
  ring

/-- The common polynomial-chart cofactor is strictly positive. -/
theorem polynomialJacobianKappa_pos {p : ℕ} (hp0 : 0 < p) :
    0 < polynomialJacobianKappa p := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0.ne'
  unfold polynomialJacobianKappa
  apply mul_pos
  · apply Finset.prod_pos
    intro l hl
    exact_mod_cast Nat.choose_pos (by omega : l.val ≤ n)
  · have hsf : 0 < Nat.superFactorial n := by
      rw [← Nat.prod_range_succ_factorial]
      exact Finset.prod_pos fun i hi ↦ Nat.factorial_pos i
    exact pow_pos (by exact_mod_cast hsf) 2

/-- **Equation (8.7).** The adjugate of each polynomial base block is the
positive scalar `kappa_t` times the outer product of alternating binomial
kernel vectors. -/
theorem polynomialBaseBlock_adjugate_eq
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t : Fin (n - p)) :
    (polynomialBaseBlock hp M t).adjugate =
      polynomialBlockKappa hp M t •
        Matrix.vecMulVec (alternatingBinomialVector p)
          (alternatingBinomialVector p) := by
  let B := polynomialBaseBlock hp M t
  let b := alternatingBinomialVector p
  have hb0 : b 0 = 1 := by simp [b, alternatingBinomialVector]
  have hbR : B *ᵥ b = 0 :=
    polynomialBaseBlock_mulVec_eq_zero hp0 hp hM t
  have hbL : b ᵥ* B = 0 :=
    alternatingBinomialVector_vecMul_polynomialBaseBlock_eq_zero hp0 hp hM t
  have hminor : (B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p)).det ≠ 0 :=
    (polynomialBlockKappa_pos hp0 hp hM t).ne'
  have hdet : B.det = 0 := by
    unfold B polynomialBaseBlock
    exact polynomialBase_maximalMinor_eq_zero hp0 hM (consecutiveColumns hp t)
  have hBA : B * B.adjugate = 0 := by
    rw [Matrix.mul_adjugate, hdet, zero_smul]
  have hAB : B.adjugate * B = 0 := by
    rw [Matrix.adjugate_mul, hdet, zero_smul]
  have hkappa : B.adjugate 0 0 = polynomialBlockKappa hp M t := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hsub : B.submatrix (0 : Fin (p + 1)).succAbove
        (0 : Fin (p + 1)).succAbove =
        B.submatrix (Fin.succOrderEmb p) (Fin.succOrderEmb p) := by
      ext i j
      rfl
    rw [hsub]
    simp [polynomialBlockKappa, B]
  ext i j
  have hcolZero : B *ᵥ (fun q ↦ B.adjugate q j) = 0 := by
    funext q
    simpa [Matrix.mulVec, Matrix.mul_apply] using congrArg (fun X ↦ X q j) hBA
  have hcol := eq_smul_kernelVector_of_mulVec_eq_zero B b
    (fun q ↦ B.adjugate q j) hb0 hbR hminor hcolZero
  have hrowZero : (fun q ↦ B.adjugate 0 q) ᵥ* B = 0 := by
    funext q
    simpa [Matrix.vecMul, Matrix.mul_apply] using congrArg (fun X ↦ X 0 q) hAB
  have hrow := eq_smul_kernelVector_of_vecMul_eq_zero B b
    (fun q ↦ B.adjugate 0 q) hb0 hbL hminor hrowZero
  have hcolij := congrFun hcol i
  have hrowj := congrFun hrow j
  simp only [Pi.smul_apply, smul_eq_mul] at hcolij hrowj
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [hcolij, hrowj, hkappa]
  ring

/-- A coordinate line through the polynomial base point. -/
def polynomialCoordinateLine {p n : ℕ} (hp : p < n) (M : ℕ)
    (s : Fin (n - p)) (r : ℝ) : Fin (n - p) → ℝ :=
  polynomialBaseCoordinates hp M +
    r • (Pi.single s (1 : ℝ) : Fin (n - p) → ℝ)

/-- The derivative of a polynomial coordinate line is its standard basis
vector. -/
theorem polynomialCoordinateLine_hasDerivAt
    {p n : ℕ} (hp : p < n) (M : ℕ) (s : Fin (n - p)) :
    HasDerivAt (polynomialCoordinateLine hp M s) (Pi.single s 1) 0 := by
  change HasDerivAt
    ((fun _ : ℝ ↦ polynomialBaseCoordinates hp M) +
      fun r : ℝ ↦ r • (Pi.single s (1 : ℝ) : Fin (n - p) → ℝ))
    (Pi.single s 1) 0
  simpa using
    (hasDerivAt_const (x := (0 : ℝ)) (polynomialBaseCoordinates hp M)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single s (1 : ℝ) : Fin (n - p) → ℝ))

/-- The block direction selected by coefficient coordinate `s`. -/
def polynomialBlockDirection {p n : ℕ} (_hp : p < n)
    (t s : Fin (n - p)) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun i j ↦ if t.val + j.val = s.val + i.val then 1 else 0

@[simp]
theorem polynomial_finiteToeplitzIndex_consecutiveColumns_val
    {p n : ℕ} (hp : p < n) (t : Fin (n - p))
    (i j : Fin (p + 1)) :
    (finiteToeplitzIndex i (consecutiveColumns hp t j)).val =
      t.val + j.val + (p - i.val) := by
  simp only [finiteToeplitzIndex_val, consecutiveColumns_apply_val]
  have hi := i.isLt
  omega

/-- Along a coordinate line, a consecutive block is its base block plus the
corresponding diagonal direction. -/
theorem polynomialSlice_consecutiveBlock_coordinateLine_eq
    {p n : ℕ} (hp : p < n) (M : ℕ)
    (t s : Fin (n - p)) (r : ℝ) :
    (polynomialSliceMatrix hp M (polynomialCoordinateLine hp M s r)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t) =
      polynomialBaseBlock hp M t + r • polynomialBlockDirection hp t s := by
  ext i j
  simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
    polynomialSliceMatrix, finiteToeplitz_apply, polynomialSliceCoefficient,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, polynomialBlockDirection]
  split_ifs with hvar hdiag
  · simp only [polynomial_finiteToeplitzIndex_consecutiveColumns_val] at hvar
    let q : Fin (n - p) :=
      ⟨(finiteToeplitzIndex i (consecutiveColumns hp t j)).val - p, by
        have hz := (finiteToeplitzIndex i (consecutiveColumns hp t j)).isLt
        omega⟩
    have hq : q = s := by
      apply Fin.ext
      dsimp only [q]
      rw [polynomial_finiteToeplitzIndex_consecutiveColumns_val]
      omega
    change polynomialCoordinateLine hp M s r q =
      polynomialBaseBlock hp M t i j + r * 1
    rw [hq]
    simp only [polynomialCoordinateLine, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    unfold polynomialBaseCoordinates polynomialBaseBlock
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self, finiteToeplitz_apply]
    apply congrArg (fun x : ℝ ↦ x + r)
    apply congrArg (polynomialStoredCoefficient (n := n) p M)
    apply Fin.ext
    change p + s.val = (finiteToeplitzIndex i (consecutiveColumns hp t j)).val
    rw [polynomial_finiteToeplitzIndex_consecutiveColumns_val]
    have hi := i.isLt
    omega
  · simp only [polynomial_finiteToeplitzIndex_consecutiveColumns_val] at hvar
    let q : Fin (n - p) :=
      ⟨(finiteToeplitzIndex i (consecutiveColumns hp t j)).val - p, by
        have hz := (finiteToeplitzIndex i (consecutiveColumns hp t j)).isLt
        omega⟩
    have hqne : q ≠ s := by
      intro hq
      apply hdiag
      have hval := congrArg Fin.val hq
      dsimp only [q] at hval
      rw [polynomial_finiteToeplitzIndex_consecutiveColumns_val] at hval
      omega
    change polynomialCoordinateLine hp M s r q =
      polynomialBaseBlock hp M t i j + r * 0
    simp only [polynomialCoordinateLine, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hqne, smul_eq_mul, mul_zero, add_zero]
    unfold polynomialBaseCoordinates polynomialBaseBlock
    simp only [Matrix.submatrix_apply, allRows_apply_eq_self, finiteToeplitz_apply]
    apply congrArg (polynomialStoredCoefficient (n := n) p M)
    apply Fin.ext
    dsimp only [q]
    omega
  · exfalso
    apply hvar
    constructor
    · rw [polynomial_finiteToeplitzIndex_consecutiveColumns_val]
      have hi := i.isLt
      omega
    · rw [polynomial_finiteToeplitzIndex_consecutiveColumns_val]
      have ht := t.isLt
      have hj := j.isLt
      omega
  · simp [polynomialBaseBlock, Matrix.submatrix_apply]

/-- The scalar restriction of a consecutive minor has the adjugate-weighted
directional derivative. -/
theorem polynomialConsecutiveMap_coordinateLine_hasDerivAt
    {p n M : ℕ} (hp : p < n)
    (t s : Fin (n - p)) :
    HasDerivAt
      (fun r : ℝ ↦ polynomialConsecutiveMap hp M
        (polynomialCoordinateLine hp M s r) t)
      (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
        polynomialBlockDirection hp t s i j *
          (polynomialBaseBlock hp M t).adjugate j i) 0 := by
  unfold polynomialConsecutiveMap matrixConsecutiveMinor matrixMaximalMinor orderedMinor
  rw [show (fun r : ℝ ↦
      ((polynomialSliceMatrix hp M (polynomialCoordinateLine hp M s r)).submatrix
        (allRows (p + 1)) (consecutiveColumns hp t)).det) =
      (fun r : ℝ ↦ (polynomialBaseBlock hp M t +
        r • polynomialBlockDirection hp t s).det) by
    funext r
    rw [polynomialSlice_consecutiveBlock_coordinateLine_eq]]
  exact hasDerivAt_det_add_smul_adjugate _ _

/-- Actual Jacobian entry as the adjugate-weighted block-diagonal sum. -/
theorem polynomialConsecutiveFDeriv_apply_single
    {p n M : ℕ} (hp : p < n)
    (t s : Fin (n - p)) :
    polynomialConsecutiveFDeriv hp M (Pi.single s 1) t =
      ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
        polynomialBlockDirection hp t s i j *
          (polynomialBaseBlock hp M t).adjugate j i := by
  have hphi := (polynomialConsecutiveMap_hasStrictFDerivAt hp M).hasFDerivAt
  have hline := polynomialCoordinateLine_hasDerivAt hp M s
  have hcomp := hphi.comp_hasDerivAt_of_eq 0 hline (by
    simp [polynomialCoordinateLine])
  let proj : (Fin (n - p) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj t
  have hcoord := proj.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have hdirect := polynomialConsecutiveMap_coordinateLine_hasDerivAt
    (M := M) hp t s
  have heq := hcoord.unique hdirect
  simpa [proj, Function.comp_def] using heq

/-- The binomial block-direction sum is symmetric in the source and target
coordinates. -/
theorem polynomialBlockDirection_binomial_sum_comm
    {p n : ℕ} (hp : p < n) (t s : Fin (n - p)) :
    (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      polynomialBlockDirection hp t s i j *
        alternatingBinomialVector p j * alternatingBinomialVector p i) =
    ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      polynomialBlockDirection hp s t i j *
        alternatingBinomialVector p j * alternatingBinomialVector p i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold polynomialBlockDirection
  split_ifs with h₁ h₂
  · ring
  · exfalso
    exact h₂ (by omega)
  · exfalso
    exact h₁ (by omega)
  · ring

/-- The block-direction binomial sum is the explicit finite-difference kernel
entry. -/
theorem polynomialBlockDirection_binomial_sum_eq_explicit
    {p n : ℕ} (hp : p < n) (t s : Fin (n - p)) :
    (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      polynomialBlockDirection hp t s i j *
        alternatingBinomialVector p j * alternatingBinomialVector p i) =
      explicitDifferenceKernel p (n - p) t s := by
  wlog hts : t ≤ s generalizing t s
  · have hst : s ≤ t := le_of_not_ge hts
    rw [polynomialBlockDirection_binomial_sum_comm hp t s]
    calc
      _ = explicitDifferenceKernel p (n - p) s t := this s t hst
      _ = explicitDifferenceKernel p (n - p) t s := by
        simp [explicitDifferenceKernel, Nat.dist_comm]
  let d := s.val - t.val
  have hinner : ∀ i : Fin (p + 1),
      (∑ j : Fin (p + 1), polynomialBlockDirection hp t s i j *
        alternatingBinomialVector p j * alternatingBinomialVector p i) =
      if h : d + i.val ≤ p then
        alternatingBinomialVector p ⟨d + i.val, by omega⟩ *
          alternatingBinomialVector p i else 0 := by
    intro i
    by_cases hi : d + i.val ≤ p
    · let j₀ : Fin (p + 1) := ⟨d + i.val, by omega⟩
      rw [Finset.sum_eq_single j₀]
      · rw [dif_pos hi]
        simp only [polynomialBlockDirection, j₀]
        have htsVal := Fin.le_iff_val_le_val.mp hts
        rw [if_pos (by dsimp only [d]; omega)]
        ring
      · intro j hj hne
        have hbad : ¬(t.val + j.val = s.val + i.val) := by
          intro heq
          apply hne
          apply Fin.ext
          dsimp only [j₀, d]
          have htsVal := Fin.le_iff_val_le_val.mp hts
          omega
        simp [polynomialBlockDirection, hbad]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero
      intro j hj
      have hbad : ¬(t.val + j.val = s.val + i.val) := by
        intro heq
        apply hi
        have htsVal := Fin.le_iff_val_le_val.mp hts
        have hjlt := j.isLt
        dsimp only [d]
        omega
      simp [polynomialBlockDirection, hbad]
  rw [show (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      polynomialBlockDirection hp t s i j * alternatingBinomialVector p j *
        alternatingBinomialVector p i) =
      ∑ i : Fin (p + 1), if h : d + i.val ≤ p then
        alternatingBinomialVector p ⟨d + i.val, by omega⟩ *
          alternatingBinomialVector p i else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner i]
  rw [Finset.sum_fin_eq_sum_range]
  have hnat :
      (∑ i ∈ Finset.range (p + 1), if d + i ≤ p then
        ((-1 : ℝ) ^ (d + i) * Nat.choose p (d + i)) *
          ((-1 : ℝ) ^ i * Nat.choose p i) else 0) =
      (-1 : ℝ) ^ d * Nat.choose (2 * p) (p + d) := by
    calc
      _ = ∑ i ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ (d + i) * Nat.choose p (d + i)) *
            ((-1 : ℝ) ^ i * Nat.choose p i) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hdi : d + i ≤ p
              · simp [hdi]
              · rw [if_neg hdi, Nat.choose_eq_zero_of_lt (lt_of_not_ge hdi)]
                simp
      _ = (-1 : ℝ) ^ d *
          ∑ i ∈ Finset.range (p + 1),
            (Nat.choose p (d + i) * Nat.choose p i : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [pow_add]
              ring_nf
              simp
      _ = (-1 : ℝ) ^ d * Nat.choose (2 * p) (p + d) := by
              congr 1
              exact_mod_cast sum_range_choose_shifted_mul_choose_all p d
  unfold explicitDifferenceKernel
  rw [Nat.dist_eq_sub_of_le (Fin.le_iff_val_le_val.mp hts)]
  rw [← hnat]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp [alternatingBinomialVector, hi]

/-- **Theorem 18, Jacobian entry formula.** -/
theorem polynomialConsecutiveFDeriv_apply_single_eq
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M)
    (t s : Fin (n - p)) :
    polynomialConsecutiveFDeriv hp M (Pi.single s 1) t =
      polynomialBlockKappa hp M t * explicitDifferenceKernel p (n - p) t s := by
  rw [polynomialConsecutiveFDeriv_apply_single hp t s]
  rw [polynomialBaseBlock_adjugate_eq hp0 hp hM t]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  calc
    (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
      polynomialBlockDirection hp t s i j *
        (polynomialBlockKappa hp M t *
          (alternatingBinomialVector p j * alternatingBinomialVector p i))) =
      polynomialBlockKappa hp M t *
        (∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
          polynomialBlockDirection hp t s i j *
            alternatingBinomialVector p j * alternatingBinomialVector p i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
    _ = polynomialBlockKappa hp M t * explicitDifferenceKernel p (n - p) t s := by
      rw [polynomialBlockDirection_binomial_sum_eq_explicit hp t s]

/-- **Equation (8.4).** The actual Jacobian matrix is a positive diagonal
matrix times the explicit finite-difference kernel. -/
theorem polynomialConsecutiveFDeriv_matrix_eq
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    continuousLinearMapMatrix (polynomialConsecutiveFDeriv hp M) =
      Matrix.diagonal (polynomialBlockKappa hp M) *
        explicitDifferenceKernel p (n - p) := by
  ext t s
  simp only [continuousLinearMapMatrix, LinearMap.toMatrix'_apply,
    Matrix.diagonal_mul]
  exact polynomialConsecutiveFDeriv_apply_single_eq hp0 hp hM t s

/-- **Strengthened Theorem 18.** The positive diagonal factor is constant,
so the polynomial-chart Jacobian is a positive scalar multiple of the
explicit symmetric finite-difference kernel. -/
theorem polynomialConsecutiveFDeriv_matrix_eq_kappa_smul
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    continuousLinearMapMatrix (polynomialConsecutiveFDeriv hp M) =
      polynomialJacobianKappa p • explicitDifferenceKernel p (n - p) := by
  rw [polynomialConsecutiveFDeriv_matrix_eq hp0 hp hM]
  ext t s
  simp [Matrix.diagonal_mul,
    polynomialBlockKappa_eq_polynomialJacobianKappa hp0 hp hM]

/-- The actual polynomial-chart Jacobian is symmetric positive definite. -/
theorem polynomialConsecutiveFDeriv_matrix_posDef
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    (continuousLinearMapMatrix (polynomialConsecutiveFDeriv hp M)).PosDef := by
  rw [polynomialConsecutiveFDeriv_matrix_eq_kappa_smul hp0 hp hM]
  have hK : (explicitDifferenceKernel p (n - p)).PosDef := by
    rw [← finiteDifferenceKernel_eq_explicit]
    exact finiteDifferenceKernel_posDef p (n - p)
  exact hK.smul (polynomialJacobianKappa_pos hp0)

/-- The polynomial Jacobian determinant is nonzero. -/
theorem polynomialConsecutiveFDeriv_matrix_det_ne_zero
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    (continuousLinearMapMatrix (polynomialConsecutiveFDeriv hp M)).det ≠ 0 := by
  rw [polynomialConsecutiveFDeriv_matrix_eq hp0 hp hM, Matrix.det_mul,
    Matrix.det_diagonal, ← finiteDifferenceKernel_eq_explicit]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun t ht ↦
      (polynomialBlockKappa_pos hp0 hp hM t).ne'
  · exact finiteDifferenceKernel_det_ne_zero p (n - p)

/-- The actual Frechet derivative of the polynomial chart is injective. -/
theorem polynomialConsecutiveFDeriv_injective
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    Function.Injective (polynomialConsecutiveFDeriv hp M) := by
  have hdet : (polynomialConsecutiveFDeriv hp M).toLinearMap.det ≠ 0 := by
    rw [← LinearMap.det_toMatrix']
    exact polynomialConsecutiveFDeriv_matrix_det_ne_zero hp0 hp hM
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

/-- The polynomial chart derivative bundled as a continuous linear
equivalence. -/
def polynomialConsecutiveDerivativeEquiv
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p ≤ M) :
    (Fin (n - p) → ℝ) ≃L[ℝ] (Fin (n - p) → ℝ) := by
  have hinj := polynomialConsecutiveFDeriv_injective hp0 hp hM
  exact ContinuousLinearEquiv.ofBijective (polynomialConsecutiveFDeriv hp M)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj))

/-- The symmetric polynomial slice as a local chart. Lemma 17 supplies its
strict lower-minor positivity, while Theorem 18 supplies the derivative
equivalence. -/
def polynomialLocalConsecutiveChart
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p + 2 ≤ M) :
    LocalConsecutiveChart p n hp where
  matrix := polynomialSliceMatrix hp M
  phi := polynomialConsecutiveMap hp M
  base := polynomialBaseCoordinates hp M
  derivativeEquiv := polynomialConsecutiveDerivativeEquiv (M := M) hp0 hp (by omega)
  hasStrictFDerivAt := by
    simpa using polynomialConsecutiveMap_hasStrictFDerivAt hp M
  phi_base := polynomialConsecutiveMap_base (M := M) hp0 hp (by omega)
  phi_eq_consecutive := fun _ _ ↦ rfl
  lowerMinor_continuous := fun r I J ↦
    continuous_polynomialSlice_orderedMinor hp M r.val I J
  base_lowerMinor_pos :=
    polynomialBaseCoordinates_mem_strictLowerMinorSet hp0 hp hM
  localExchange := by
    cases p with
    | zero => omega
    | succ r =>
        intro x hx
        apply matrixLocalPositiveExchange_of_strictLowerMinorSet hp
        intro q I J
        exact hx q I J

/-- **Corollary 19 (polynomial-chart realization).** Every sufficiently small
nonnegative target is realized by the symmetric polynomial Toeplitz chart,
with strict lower-minor positivity and full row rank exactly off the zero
target. -/
theorem polynomialLocalConsecutiveChart_exists_realization_box
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : p + 2 ≤ M) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin (n - p) → ℝ,
        (∀ t, 0 ≤ delta t ∧ delta t < eta) →
          Nonempty (LocalTargetRealization
            (polynomialLocalConsecutiveChart hp0 hp hM) delta) :=
  (polynomialLocalConsecutiveChart hp0 hp hM).exists_realization_box

/-- Corollary 19 under the manuscript's stated bound `M > n + m`, written
with `p = m - 1`. -/
theorem polynomialLocalConsecutiveChart_exists_realization_box_of_paper_bound
    {p n M : ℕ} (hp0 : 0 < p) (hp : p < n) (hM : n + (p + 1) < M) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin (n - p) → ℝ,
        (∀ t, 0 ≤ delta t ∧ delta t < eta) →
          Nonempty (LocalTargetRealization
            (polynomialLocalConsecutiveChart (M := M) hp0 hp (by omega)) delta) :=
  polynomialLocalConsecutiveChart_exists_realization_box (M := M) hp0 hp (by omega)

end

end PavingToeplitzPositroids
