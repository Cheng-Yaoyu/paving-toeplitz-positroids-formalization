import PavingToeplitzPositroids.Refinement
import PavingToeplitzPositroids.ModuleInterpolation
import PavingToeplitzPositroids.PositiveExpansion
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FinCases

/-!
# Alternating circuit vectors

This file formalizes the alternating cofactor vector in Corollary 5, its
Laplace pairing with an arbitrary appended row, and its kernel property.
-/

namespace PavingToeplitzPositroids

open Matrix ToeplitzPositroids
open scoped BigOperators

noncomputable section

/-- Append one last row to a matrix. -/
def appendLastRow {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (f : Fin n → ℝ) : Matrix (Fin (k + 1)) (Fin n) ℝ :=
  fun i j ↦ Fin.lastCases (f j) (fun q ↦ U q j) i

@[simp]
theorem appendLastRow_castSucc
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (f : Fin n → ℝ) (i : Fin k) (j : Fin n) :
    appendLastRow U f i.castSucc j = U i j := by
  simp [appendLastRow]

@[simp]
theorem appendLastRow_last
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (f : Fin n → ℝ) (j : Fin n) :
    appendLastRow U f (Fin.last k) j = f j := by
  simp [appendLastRow]

/-- Delete position `i` from an increasing column selection. -/
def eraseColumn {k n : ℕ} (J : Fin (k + 1) ↪o Fin n) (i : Fin (k + 1)) :
    Fin k ↪o Fin n :=
  (Fin.succAboveOrderEmb i).trans J

/-- The alternating circuit vector from equation (3.6), with Lean's
zero-based exponent convention. -/
def alternatingCircuit {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) : Fin n → ℝ :=
  ∑ i : Fin (k + 1),
    ((-1 : ℝ) ^ i.val *
      orderedMinor U (allRows k) (eraseColumn J i)) •
        (Pi.single (J i) (1 : ℝ) : Fin n → ℝ)

/-- Pairing the alternating circuit with a row gives the cofactor sum. -/
theorem alternatingCircuit_pairing
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) (f : Fin n → ℝ) :
    (∑ j, alternatingCircuit U J j * f j) =
      ∑ i : Fin (k + 1),
        (-1 : ℝ) ^ i.val * orderedMinor U (allRows k) (eraseColumn J i) *
          f (J i) := by
  classical
  unfold alternatingCircuit
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp [Pi.single_apply]

/-- The submatrix in a last-row cofactor is the lower ordered minor obtained
by deleting the corresponding selected column. -/
theorem appendLastRow_cofactor_eq_orderedMinor
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ) (f : Fin n → ℝ)
    (J : Fin (k + 1) ↪o Fin n) (i : Fin (k + 1)) :
    (((appendLastRow U f).submatrix (allRows (k + 1)) J).submatrix
        (Fin.last k).succAbove i.succAbove).det =
      orderedMinor U (allRows k) (eraseColumn J i) := by
  unfold orderedMinor eraseColumn
  congr 1
  ext p q
  simp [Matrix.submatrix_apply, Fin.succAboveOrderEmb_apply]

/-- Laplace expansion along the appended row is the pairing with the
alternating circuit, up to the common sign `(-1)^k`. -/
theorem appendLastRow_maximalMinor_eq_circuit_pairing
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) (f : Fin n → ℝ) :
    matrixMaximalMinor (appendLastRow U f) J =
      (-1 : ℝ) ^ k * (∑ j, alternatingCircuit U J j * f j) := by
  unfold matrixMaximalMinor orderedMinor
  rw [Matrix.det_succ_row _ (Fin.last k)]
  rw [alternatingCircuit_pairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [appendLastRow_cofactor_eq_orderedMinor]
  simp only [Matrix.submatrix_apply, allRows_apply_eq_self,
    appendLastRow_last, Fin.val_last]
  rw [pow_add]
  ring

/-- Appending an existing row produces a square selected matrix with a
repeated row. -/
theorem appendLastRow_existingRow_maximalMinor_eq_zero
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) (i : Fin k) :
    matrixMaximalMinor (appendLastRow U (U i)) J = 0 := by
  unfold matrixMaximalMinor orderedMinor
  apply Matrix.det_zero_of_row_eq (i.castSucc_ne_last)
  funext j
  simp [Matrix.submatrix_apply]

/-- The alternating circuit lies in the kernel of the lower matrix. -/
theorem mulVec_alternatingCircuit_eq_zero
    {k n : ℕ} (U : Matrix (Fin k) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) :
    U *ᵥ alternatingCircuit U J = 0 := by
  funext i
  have hdet := appendLastRow_existingRow_maximalMinor_eq_zero U J i
  rw [appendLastRow_maximalMinor_eq_circuit_pairing] at hdet
  have hsign : (-1 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpair : (∑ j, alternatingCircuit U J j * U i j) = 0 := by
    exact (mul_eq_zero.mp hdet).resolve_left hsign
  simpa [Matrix.mulVec, dotProduct, mul_comm] using hpair

/-- The first row block of an appended-row matrix is the original matrix. -/
@[simp]
theorem firstRows_appendLastRow
    {r n : ℕ} (U : Matrix (Fin (r + 1)) (Fin n) ℝ) (f : Fin n → ℝ) :
    firstRows (appendLastRow U f) = U := by
  ext i j
  exact appendLastRow_castSucc U f i j

/-- One local Plucker split whose positive coefficients work simultaneously
for every possible appended last row. -/
theorem exists_universal_appendedRow_exchange
    {r n : ℕ}
    (U : Matrix (Fin (r + 1)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor U (allRows (r + 1)) J)
    (J : Fin (r + 2) ↪o Fin n) (hspan : columnSpan J ≠ r + 1) :
    ∃ L R, ∃ alpha beta : ℝ,
      0 < alpha ∧ 0 < beta ∧
      L 0 = J 0 ∧ L (Fin.last (r + 1)) < J (Fin.last (r + 1)) ∧
      J 0 < R 0 ∧ R (Fin.last (r + 1)) = J (Fin.last (r + 1)) ∧
      (R 0).val + (r + 1) ≤ (L (Fin.last (r + 1))).val + 1 ∧
      ∀ f : Fin n → ℝ,
        matrixMaximalMinor (appendLastRow U f) J =
          alpha * matrixMaximalMinor (appendLastRow U f) L +
            beta * matrixMaximalMinor (appendLastRow U f) R := by
  obtain ⟨b, hab, hbc, hbJ⟩ := exists_missing_between_of_columnSpan_ne J hspan
  let S := interiorColumns J
  let a := J 0
  let c := J (Fin.last (r + 1))
  have haSlt : ∀ i, a < S i := by
    intro i
    change J (0 : Fin (r + 2)) < J i.succ.castSucc
    apply J.strictMono
    simp
  have hSltc : ∀ i, S i < c := by
    intro i
    change J i.succ.castSucc < J (Fin.last (r + 1))
    apply J.strictMono
    exact i.succ.castSucc_lt_last
  have haS : a ∉ Set.range S := by
    rintro ⟨i, hi⟩
    have hlt := haSlt i
    rw [hi] at hlt
    exact lt_irrefl a hlt
  have hcS : c ∉ Set.range S := by
    rintro ⟨i, hi⟩
    have hlt := hSltc i
    rw [hi] at hlt
    exact lt_irrefl c hlt
  have hbS : b ∉ Set.range S := by
    intro hb
    apply hbJ
    rw [range_interiorColumns_union_endpoints]
    exact Or.inl hb
  let L := sortedAppendTwo S a b haS hbS hab.ne
  let R := sortedAppendTwo S b c hbS hcS hbc.ne
  let M := sortedAppendOne S b hbS
  have hJsorted : J = sortedAppendTwo S a c haS hcS (hab.trans hbc).ne := by
    apply OrderEmbedding.range_inj.mp
    rw [range_sortedAppendTwo]
    exact range_interiorColumns_union_endpoints J
  have hLfirst : L 0 = J 0 := by
    change sortedAppendTwo S a b haS hbS hab.ne 0 = J 0
    rw [sortedAppendTwo_zero_eq_left S haS hbS hab.ne haSlt hab]
  have hRlast : R (Fin.last (r + 1)) = J (Fin.last (r + 1)) := by
    change sortedAppendTwo S b c hbS hcS hbc.ne (Fin.last (r + 1)) =
      J (Fin.last (r + 1))
    rw [sortedAppendTwo_last_eq_right S hbS hcS hbc.ne hSltc hbc]
  have hLlast_lt : L (Fin.last (r + 1)) < J (Fin.last (r + 1)) := by
    have hLrange : Set.range L = Set.range S ∪ {a, b} :=
      range_sortedAppendTwo S a b haS hbS hab.ne
    have hmem : L (Fin.last (r + 1)) ∈ Set.range S ∪ {a, b} := by
      rw [← hLrange]
      exact ⟨Fin.last (r + 1), rfl⟩
    rcases hmem with (hmem | hmem)
    · obtain ⟨i, hi⟩ := hmem
      rw [← hi]
      exact hSltc i
    · rcases hmem with (hmem | hmem)
      · rw [hmem]
        exact hab.trans hbc
      · rw [hmem]
        exact hbc
  have hRfirst_gt : J 0 < R 0 := by
    have hRrange : Set.range R = Set.range S ∪ {b, c} :=
      range_sortedAppendTwo S b c hbS hcS hbc.ne
    have hmem : R 0 ∈ Set.range S ∪ {b, c} := by
      rw [← hRrange]
      exact ⟨0, rfl⟩
    rcases hmem with (hmem | hmem)
    · obtain ⟨i, hi⟩ := hmem
      rw [← hi]
      exact haSlt i
    · rcases hmem with (hmem | hmem)
      · rw [hmem]
        exact hab
      · rw [hmem]
        exact hab.trans hbc
  have hRzeroM : R 0 = M 0 := by
    apply orderEmbedding_zero_eq_of_adjoin_greater M R c
    · have hRrange : Set.range R = Set.range S ∪ {b, c} :=
        range_sortedAppendTwo S b c hbS hcS hbc.ne
      have hMrange : Set.range M = Set.range S ∪ {b} :=
        range_sortedAppendOne S b hbS
      rw [hRrange, hMrange]
      ext z
      simp [or_assoc, or_comm]
    · intro i
      have hMrange : Set.range M = Set.range S ∪ {b} :=
        range_sortedAppendOne S b hbS
      have hmem : M i ∈ Set.range S ∪ {b} := by
        rw [← hMrange]
        exact ⟨i, rfl⟩
      rcases hmem with (hmem | hmem)
      · obtain ⟨j, hj⟩ := hmem
        rw [← hj]
        exact hSltc j
      · have hi : M i = b := by simpa using hmem
        rw [hi]
        exact hbc
  have hLlastM : L (Fin.last (r + 1)) = M (Fin.last r) := by
    apply orderEmbedding_last_eq_of_adjoin_less M L a
    · have hLrange : Set.range L = Set.range S ∪ {a, b} :=
        range_sortedAppendTwo S a b haS hbS hab.ne
      have hMrange : Set.range M = Set.range S ∪ {b} :=
        range_sortedAppendOne S b hbS
      rw [hLrange, hMrange]
      ext z
      simp [or_assoc, or_comm]
    · intro i
      have hMrange : Set.range M = Set.range S ∪ {b} :=
        range_sortedAppendOne S b hbS
      have hmem : M i ∈ Set.range S ∪ {b} := by
        rw [← hMrange]
        exact ⟨i, rfl⟩
      rcases hmem with (hmem | hmem)
      · obtain ⟨j, hj⟩ := hmem
        rw [← hj]
        exact haSlt j
      · have hi : M i = b := by simpa using hmem
        rw [hi]
        exact hab
  have hoverlap : (R 0).val + (r + 1) ≤ (L (Fin.last (r + 1))).val + 1 := by
    have hgap := orderEmbedding_endpoint_gap M
    rw [hRzeroM, hLlastM]
    omega
  let qa := orderedMinor U (allRows (r + 1)) (sortedAppendOne S a haS)
  let qb := orderedMinor U (allRows (r + 1)) (sortedAppendOne S b hbS)
  let qc := orderedMinor U (allRows (r + 1)) (sortedAppendOne S c hcS)
  have hqa : 0 < qa := hpos _
  have hqb : 0 < qb := hpos _
  have hqc : 0 < qc := hpos _
  refine ⟨L, R, qc / qb, qa / qb, div_pos hqc hqb, div_pos hqa hqb,
    hLfirst, hLlast_lt, hRfirst_gt, hRlast, hoverlap, ?_⟩
  intro f
  have hplucker := mixedPlucker_sorted (appendLastRow U f) S haS hbS hcS hab hbc
  rw [firstRows_appendLastRow] at hplucker
  rw [← hJsorted] at hplucker
  change matrixMaximalMinor (appendLastRow U f) J * qb =
    matrixMaximalMinor (appendLastRow U f) L * qc +
      matrixMaximalMinor (appendLastRow U f) R * qa at hplucker
  field_simp [hqb.ne']
  linear_combination hplucker

/-- The universal appended-row identity is equivalent to the corresponding
local vector identity for alternating circuits. -/
theorem exists_local_alternatingCircuit_exchange
    {r n : ℕ} (U : Matrix (Fin (r + 1)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor U (allRows (r + 1)) J)
    (J : Fin (r + 2) ↪o Fin n) (hspan : columnSpan J ≠ r + 1) :
    ∃ L R, ∃ alpha beta : ℝ,
      0 < alpha ∧ 0 < beta ∧
      L 0 = J 0 ∧ L (Fin.last (r + 1)) < J (Fin.last (r + 1)) ∧
      J 0 < R 0 ∧ R (Fin.last (r + 1)) = J (Fin.last (r + 1)) ∧
      (R 0).val + (r + 1) ≤ (L (Fin.last (r + 1))).val + 1 ∧
      alternatingCircuit U J =
        alpha • alternatingCircuit U L + beta • alternatingCircuit U R := by
  obtain ⟨L, R, alpha, beta, ha, hb, hfirst, hLlast, hRfirst, hlast,
    hoverlap, huniversal⟩ := exists_universal_appendedRow_exchange U hpos J hspan
  refine ⟨L, R, alpha, beta, ha, hb, hfirst, hLlast, hRfirst, hlast,
    hoverlap, ?_⟩
  apply pi_eq_of_dotProduct_eq
  intro f
  have hscalar := huniversal f
  rw [appendLastRow_maximalMinor_eq_circuit_pairing,
    appendLastRow_maximalMinor_eq_circuit_pairing,
    appendLastRow_maximalMinor_eq_circuit_pairing] at hscalar
  have hsign : (-1 : ℝ) ^ (r + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdot :
      (∑ j, alternatingCircuit U J j * f j) =
        alpha * (∑ j, alternatingCircuit U L j * f j) +
          beta * (∑ j, alternatingCircuit U R j * f j) := by
    apply mul_left_cancel₀ hsign
    calc
      (-1 : ℝ) ^ (r + 1) * (∑ j, alternatingCircuit U J j * f j) =
          alpha * ((-1 : ℝ) ^ (r + 1) *
            ∑ j, alternatingCircuit U L j * f j) +
          beta * ((-1 : ℝ) ^ (r + 1) *
            ∑ j, alternatingCircuit U R j * f j) := hscalar
      _ = (-1 : ℝ) ^ (r + 1) *
          (alpha * (∑ j, alternatingCircuit U L j * f j) +
            beta * (∑ j, alternatingCircuit U R j * f j)) := by ring
  calc
    (∑ j, alternatingCircuit U J j * f j) =
        alpha * (∑ j, alternatingCircuit U L j * f j) +
          beta * (∑ j, alternatingCircuit U R j * f j) := hdot
    _ = ∑ j,
        (alpha • alternatingCircuit U L + beta • alternatingCircuit U R) j * f j := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (fun x y : ℝ ↦ x + y)
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · apply Finset.sum_congr rfl
        intro j _
        ring

/-- The module-valued refinement system whose nodes are alternating circuits. -/
def alternatingCircuitRefinementSystem
    {r n : ℕ} (hrn : r + 1 < n)
    (U : Matrix (Fin (r + 1)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor U (allRows (r + 1)) J) :
    ModulePositiveRefinementSystem
      (Fin (r + 2) ↪o Fin n) (Fin (n - (r + 1))) (Fin n → ℝ) where
  measure := columnSpan
  anchors := anchorFinset
  value := alternatingCircuit U
  anchorValue := fun t ↦ alternatingCircuit U (consecutiveColumns hrn t)
  atomic := fun J ↦ columnSpan J = r + 1
  atomic_spec := by
    intro J hJ
    refine ⟨firstAnchor hrn J,
      anchorFinset_eq_singleton_of_span_eq hrn J hJ, ?_⟩
    exact congrArg (alternatingCircuit U)
      (eq_consecutiveColumns_of_span_eq hrn J hJ)
  refine := by
    intro J hJ
    obtain ⟨L, R, alpha, beta, ha, hb, hfirst, hLlast, hRfirst, hlast,
      hoverlap, hvalue⟩ := exists_local_alternatingCircuit_exchange U hpos J hJ
    refine ⟨L, R, alpha, beta, ha, hb, ?_, ?_, ?_, hvalue⟩
    · simp only [columnSpan]
      have hfirstVal := congrArg Fin.val hfirst
      omega
    · simp only [columnSpan]
      have hlastVal := congrArg Fin.val hlast
      omega
    · exact anchorFinset_eq_union_of_endpoint_split J L R hfirst hlast
        hLlast.le hRfirst.le hoverlap

/-- **Corollary 5.** Every alternating circuit is a positive combination of
all consecutive alternating circuits in its endpoint span. -/
theorem exists_positive_alternatingCircuit_subdivision
    {r n : ℕ} (hrn : r + 1 < n)
    (U : Matrix (Fin (r + 1)) (Fin n) ℝ)
    (hpos : ∀ J : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor U (allRows (r + 1)) J)
    (J : Fin (r + 2) ↪o Fin n) :
    Nonempty (FullPositiveModuleAnchorExpansion
      (alternatingCircuit U J)
      (fun t ↦ alternatingCircuit U (consecutiveColumns hrn t))
      (anchorFinset J)) :=
  (alternatingCircuitRefinementSystem hrn U hpos).exists_positiveExpansion J

/-- **Corollary 5 with the shared-coefficient clause.** The circuit
coefficients can be chosen once so that, for every appended last row `f`,
the very same coefficients also give the scalar consecutive-minor expansion
from Theorem 3. -/
theorem exists_joint_circuit_and_minor_interpolation
    {r n : ℕ} (hrn : r + 1 < n)
    (U : Matrix (Fin (r + 1)) (Fin n) ℝ)
    (hpos : ∀ I : Fin (r + 1) ↪o Fin n,
      0 < orderedMinor U (allRows (r + 1)) I)
    (J : Fin (r + 2) ↪o Fin n) :
    ∃ E : FullPositiveModuleAnchorExpansion
        (alternatingCircuit U J)
        (fun t ↦ alternatingCircuit U (consecutiveColumns hrn t))
        (anchorFinset J),
      ∀ f : Fin n → ℝ,
        matrixMaximalMinor (appendLastRow U f) J =
          ∑ t, E.coefficient t *
            matrixConsecutiveMinor hrn (appendLastRow U f) t := by
  obtain ⟨E⟩ := exists_positive_alternatingCircuit_subdivision hrn U hpos J
  refine ⟨E, fun f ↦ ?_⟩
  rw [appendLastRow_maximalMinor_eq_circuit_pairing]
  have hpair := congrArg (fun c : Fin n → ℝ ↦ ∑ j, c j * f j) E.value_eq_sum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hpair
  rw [hpair]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [show (∑ x, E.coefficient t *
      alternatingCircuit U (consecutiveColumns hrn t) x * f x) =
      E.coefficient t *
        ∑ x, alternatingCircuit U (consecutiveColumns hrn t) x * f x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  unfold matrixConsecutiveMinor
  rw [appendLastRow_maximalMinor_eq_circuit_pairing]
  ring

end

end PavingToeplitzPositroids
