import PavingToeplitzPositroids.Circuits
import PavingToeplitzPositroids.TriangularJacobian
import PavingToeplitzPositroids.IntervalFamily

/-!
# Matrix-support classification

This file assembles the realizability and support directions of Theorem 1.
The interval-hyperplane translation is kept in `IntervalSupport` and
`SupportTheorem`.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

noncomputable section

/-- The zero set of consecutive maximal minors of a concrete matrix. -/
def matrixConsecutiveZeroSet {k n : ℕ} (hk : k < n)
    (A : Matrix (Fin (k + 1)) (Fin n) ℝ) : Finset (Fin (n - k)) :=
  Finset.univ.filter fun t ↦ matrixConsecutiveMinor hk A t = 0

@[simp]
theorem mem_matrixConsecutiveZeroSet_iff
    {k n : ℕ} (hk : k < n) (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (t : Fin (n - k)) :
    t ∈ matrixConsecutiveZeroSet hk A ↔ matrixConsecutiveMinor hk A t = 0 := by
  simp [matrixConsecutiveZeroSet]

/-- The data realized from one proper consecutive zero pattern. -/
structure ClassifiedToeplitzRealization (p n : ℕ) (hpn : p < n)
    (Z : Finset (Fin (n - p))) where
  matrix : Matrix (Fin (p + 1)) (Fin n) ℝ
  toeplitz : HasFiniteToeplitzForm matrix
  totallyNonnegative : TotallyNonnegative matrix
  fullRowRank : HasFullRowRank matrix
  lowerMinor_pos : ∀ r : Fin (p + 1),
    ∀ (I : Fin r.val ↪o Fin (p + 1)) (J : Fin r.val ↪o Fin n),
      0 < orderedMinor matrix I J
  consecutive_eq_zero_iff : ∀ t,
    matrixConsecutiveMinor hpn matrix t = 0 ↔ t ∈ Z
  basis_rule : ∀ J : Fin (p + 1) ↪o Fin n,
    matrixMaximalMinor matrix J ≠ 0 ↔
      ∃ t ∈ anchorFinset J, t ∉ Z

/-- **Theorem 1, necessity/support direction.** A full-row-rank totally
nonnegative matrix whose codimension-one column selections are independent
has a proper consecutive zero set, and this set determines every maximal
minor support coordinate. -/
theorem tnn_refinement_classification
    {r n : ℕ} (hrn : r + 1 < n)
    {A : Matrix (Fin (r + 2)) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (hfull : HasFullRowRank A)
    (hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j))) :
    matrixConsecutiveZeroSet hrn A ≠ Finset.univ ∧
      ∀ J : Fin (r + 2) ↪o Fin n,
        matrixMaximalMinor A J ≠ 0 ↔
          ∃ t ∈ anchorFinset J, t ∉ matrixConsecutiveZeroSet hrn A := by
  have hsupport := refinement_maximalMinor_eq_zero_iff hrn hA hind
  constructor
  · obtain ⟨J, hJ⟩ := hfull
    intro hzero
    apply hJ
    change matrixMaximalMinor A J = 0
    rw [hsupport J]
    intro t _
    apply (mem_matrixConsecutiveZeroSet_iff hrn A t).1
    rw [hzero]
    simp
  · intro J
    rw [ne_eq, hsupport J]
    push Not
    simp only [mem_matrixConsecutiveZeroSet_iff]

/-- **Theorem 1, realization direction.** Every proper consecutive zero set
has a full-row-rank totally nonnegative Toeplitz realization with all lower
minors positive and with exactly the prescribed basis rule. -/
theorem exists_classifiedToeplitzRealization
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (Z : Finset (Fin (n - p))) (hZ : Z ≠ Finset.univ) :
    Nonempty (ClassifiedToeplitzRealization p n hpn Z) := by
  let C := homogeneousConcreteLocalConsecutiveChart hp hpn (le_refl p)
  obtain ⟨R⟩ := homogeneousConcrete_exists_zeroPatternRealization
    hp hpn (le_refl p) Z hZ
  let A := C.matrix R.source
  let E := (C.localExchange R.source R.lowerMinor_pos).toLocalSystem.toConsecutiveSystem
  have hEmax : ∀ J, E.maximalMinor J = matrixMaximalMinor A J := fun _ ↦ rfl
  have hED : ∀ t, E.consecutiveMinor t = matrixConsecutiveMinor hpn A t := fun _ ↦ rfl
  have hEnonneg : ∀ t, 0 ≤ E.consecutiveMinor t := by
    intro t
    rw [hED]
    change 0 ≤ orderedMinor A (allRows (p + 1)) (consecutiveColumns hpn t)
    exact R.totallyNonnegative.orderedMinor_nonneg _ _
  refine ⟨{
    matrix := A
    toeplitz := ?_
    totallyNonnegative := R.totallyNonnegative
    fullRowRank := R.fullRowRank
    lowerMinor_pos := R.lowerMinor_pos
    consecutive_eq_zero_iff := R.consecutive_eq_zero_iff
    basis_rule := fun J ↦ ?_ }⟩
  · rw [show A = homogeneousSliceMatrix hpn p R.source by
      exact homogeneousConcreteLocalConsecutiveChart_matrix hp hpn (le_refl p) R.source]
    exact homogeneousSliceMatrix_hasFiniteToeplitzForm hpn p R.source
  · have hs := (E.support_from_consecutive hEnonneg J).2
    rw [hEmax] at hs
    rw [ne_eq, hs]
    push Not
    constructor
    · rintro ⟨t, ht, hne⟩
      refine ⟨t, ?_, ?_⟩
      · simp [anchorFinset, ht]
      · intro htZ
        apply hne
        rw [hED]
        exact (R.consecutive_eq_zero_iff t).2 htZ
    · rintro ⟨t, ht, htZ⟩
      refine ⟨t, ?_, ?_⟩
      · simpa [anchorFinset] using ht
      · rw [hED]
        intro hzero
        exact htZ ((R.consecutive_eq_zero_iff t).1 hzero)

/-- **Theorem 1, interval-family realization direction.** Every interval
hyperplane family satisfying condition (iii) has a totally nonnegative
Toeplitz realization whose nonbases are exactly the maximal selections
contained in one of those intervals. -/
theorem exists_intervalFamilyToeplitzRealization
    {p n r : ℕ} (hp : 0 < p) (hpn : p < n)
    (F : IntervalHyperplaneFamily p n r) :
    ∃ R : ClassifiedToeplitzRealization p n hpn (F.zeroSet hpn),
      ∀ J : Fin (p + 1) ↪o Fin n,
        matrixMaximalMinor R.matrix J ≠ 0 ↔
          ¬∃ a, ∀ i, J i ∈ Finset.Icc (F.left a) (F.right a) := by
  obtain ⟨R⟩ := exists_classifiedToeplitzRealization hp hpn
    (F.zeroSet hpn) (F.zeroSet_ne_univ hp hpn)
  refine ⟨R, fun J ↦ ?_⟩
  rw [R.basis_rule]
  exact F.basisRule_zeroSet_iff_not_columns_mem_interval hp hpn J

/-- **Corollary 21.** A paving interval-hyperplane family in the natural
column order has a full-row-rank totally nonnegative Toeplitz realization. -/
theorem pavingIntervalFamily_has_toeplitzRealization
    {p n r : ℕ} (hp : 0 < p) (hpn : p < n)
    (F : IntervalHyperplaneFamily p n r) :
    ∃ R : ClassifiedToeplitzRealization p n hpn (F.zeroSet hpn),
      ∀ J : Fin (p + 1) ↪o Fin n,
        matrixMaximalMinor R.matrix J = 0 ↔
          ∃ a, ∀ i, J i ∈ Finset.Icc (F.left a) (F.right a) := by
  obtain ⟨R, hR⟩ := exists_intervalFamilyToeplitzRealization hp hpn F
  refine ⟨R, fun J ↦ ?_⟩
  rw [← not_iff_not]
  simpa using hR J

/-- **Corollary 22, basis generating description.** For a classified zero
set, nonbases are exactly the maximal selections lying in one enlarged run
interval. -/
theorem classified_basisGeneratingDescription
    {p n r : ℕ} (hpn : p < n) {Z : Finset (Fin (n - p))}
    (D : ZeroRunDecomposition Z r)
    (R : ClassifiedToeplitzRealization p n hpn Z)
    (J : Fin (p + 1) ↪o Fin n) :
    matrixMaximalMinor R.matrix J = 0 ↔
      ∃ a, ∀ i, J i ∈ runHyperplane hpn D a := by
  rw [← not_iff_not]
  change matrixMaximalMinor R.matrix J ≠ 0 ↔
    ¬∃ a, ∀ i, J i ∈ runHyperplane hpn D a
  rw [R.basis_rule]
  have hsupport := allAnchors_mem_iff_exists_columns_mem_runHyperplane hpn D J
  rw [← not_congr hsupport]
  push Not
  constructor
  · rintro ⟨t, ht, htz⟩
    refine ⟨t, ?_, htz⟩
    simpa [anchorFinset] using ht
  · rintro ⟨t, ht, htz⟩
    refine ⟨t, ?_, htz⟩
    simp [anchorFinset, ht]

/-- The run-indexed nonbasis families in Corollary 22 are pairwise
disjoint. -/
theorem classified_nonbasis_run_unique
    {p n r : ℕ} (hpn : p < n) {Z : Finset (Fin (n - p))}
    (D : ZeroRunDecomposition Z r) (J : Fin (p + 1) ↪o Fin n)
    {a b : Fin r}
    (ha : ∀ i, J i ∈ runHyperplane hpn D a)
    (hb : ∀ i, J i ∈ runHyperplane hpn D b) :
    a = b := by
  by_contra hab
  exact not_columns_mem_two_runHyperplanes hpn D hab J ⟨ha, hb⟩

end

end PavingToeplitzPositroids
