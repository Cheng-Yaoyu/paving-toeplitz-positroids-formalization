import PavingToeplitzPositroids.Classification
import PavingToeplitzPositroids.MatroidHyperplanes
import PavingToeplitzPositroids.IntervalFamily
import Mathlib.Combinatorics.Matroid.Rank.Cardinal

/-!
# Paper-level classification theorem

This file states Theorem 1 with an arbitrary abstract paving matroid and
proves the equivalence of the paper's three conditions.  Earlier modules
establish the matrix, zero-run, hyperplane, and realization components; the
lemmas below supply the missing abstract-matroid assembly.
-/

namespace PavingToeplitzPositroids

open Set ToeplitzPositroids

noncomputable section

/-- A rank-`p+1` paving matroid on the full ordered ground set `Fin n`.
The parameter `p` is `m-1` in the paper. -/
structure IsRankPavingMatroid (p n : ℕ) (M : Matroid (Fin n)) : Prop where
  ground_eq : M.E = Set.univ
  exists_maximalBase : ∃ J : Fin (p + 1) ↪o Fin n, M.IsBase (Set.range J)
  small_indep : ∀ X : Set (Fin n), X.ncard ≤ p → M.Indep X

namespace IsRankPavingMatroid

/-- Every base of a rank-`p+1` paving matroid has cardinality `p+1`. -/
theorem isBase_ncard_eq
    {p n : ℕ} {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M)
    {B : Set (Fin n)} (hB : M.IsBase B) :
    B.ncard = p + 1 := by
  obtain ⟨J, hJ⟩ := hM.exists_maximalBase
  rw [hB.ncard_eq_ncard_of_isBase hJ]
  simpa using Set.ncard_range_of_injective J.injective

/-- At maximal cardinality, independence is equivalent to being a base. -/
theorem indep_iff_isBase_of_ncard_eq
    {p n : ℕ} {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M)
    {X : Set (Fin n)} (hXcard : X.ncard = p + 1) :
    M.Indep X ↔ M.IsBase X := by
  constructor
  · intro hX
    obtain ⟨B, hB, hXB⟩ := hX.exists_isBase_superset
    have hcard : B.ncard ≤ X.ncard := by
      rw [hM.isBase_ncard_eq hB, hXcard]
    have hEq := Set.eq_of_subset_of_ncard_le hXB hcard
    simpa [hEq] using hB
  · exact Matroid.IsBase.indep

end IsRankPavingMatroid

/-- Increasing enumeration of a finite set with prescribed cardinality. -/
def increasingEnumeration {n q : ℕ} (X : Set (Fin n)) (hX : X.ncard = q) :
    Fin q ↪o Fin n := by
  letI : Fintype X := (Set.toFinite X).fintype
  exact X.toFinset.orderEmbOfFin (by
    rw [← Set.ncard_eq_toFinset_card' X]
    exact hX)

@[simp]
theorem range_increasingEnumeration {n q : ℕ} (X : Set (Fin n))
    (hX : X.ncard = q) :
    Set.range (increasingEnumeration X hX) = X := by
  unfold increasingEnumeration
  rw [Finset.range_orderEmbOfFin]
  simp

/-- A dependent maximal-cardinality set of a paving matroid is contained in
a dependent hyperplane. -/
theorem exists_dependentHyperplane_superset_of_dep_ncard
    {p n : ℕ} (hp : 0 < p) {M : Matroid (Fin n)}
    (hM : IsRankPavingMatroid p n M)
    {X : Set (Fin n)} (hXcard : X.ncard = p + 1) (hXdep : M.Dep X) :
    ∃ H : Set (Fin n), IsDependentMatroidHyperplane M H ∧ X ⊆ H := by
  have hXnonempty : X.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hXempty
    rw [hXempty, Set.ncard_empty] at hXcard
    omega
  obtain ⟨e, heX⟩ := hXnonempty
  let I := X \ {e}
  have heI : e ∉ I := by simp [I]
  have hIfin : X.Finite := Set.toFinite X
  have hIcard : I.ncard = p := by
    rw [Set.ncard_diff_singleton_of_mem heX, hXcard]
    omega
  have hIind : M.Indep I := hM.small_indep I hIcard.le
  have hXinsert : insert e I = X := by
    simp [I, heX]
  have hecl : e ∈ M.closure I := by
    apply (hIind.mem_closure_iff_of_notMem heI).2
    simpa [hXinsert] using hXdep
  let H := M.closure I
  have hIH : I ⊆ H := M.subset_closure I hIind.subset_ground
  have hXH : X ⊆ H := by
    rw [← hXinsert]
    exact insert_subset hecl hIH
  have hproper : H ≠ M.E := by
    intro hHE
    have hspanning : M.Spanning I := by
      rw [Matroid.spanning_iff_closure_eq hIind.subset_ground]
      exact hHE
    have hIbase : M.IsBase I := hIind.isBase_of_spanning hspanning
    have := hM.isBase_ncard_eq hIbase
    omega
  have hhyper : IsMatroidHyperplane M H := by
    refine ⟨M.isFlat_closure I, hproper, ?_⟩
    intro F hF hHF hne
    have hstrict : H ⊂ F := hHF.ssubset_of_ne hne.symm
    obtain ⟨_, x, hxF, hxH⟩ := Set.ssubset_iff_exists.mp hstrict
    have hxE : x ∈ M.E := hF.subset_ground hxF
    have hxI : x ∉ I := fun hx ↦ hxH (hIH hx)
    have hxind : M.Indep (insert x I) :=
      (hIind.notMem_closure_iff_of_notMem hxI hxE).1 hxH
    have hxcard : (insert x I).ncard = p + 1 := by
      rw [Set.ncard_insert_of_notMem hxI, hIcard]
    have hxbase : M.IsBase (insert x I) :=
      (hM.indep_iff_isBase_of_ncard_eq hxcard).1 hxind
    have hbaseF : insert x I ⊆ F :=
      insert_subset hxF (hIH.trans hHF)
    apply Set.Subset.antisymm hF.subset_ground
    rw [← hxbase.closure_eq, ← hF.closure]
    exact M.closure_mono hbaseF
  refine ⟨H, ⟨hhyper, ?_⟩, hXH⟩
  exact hXdep.superset hXH hhyper.1.subset_ground

/-- In a rank-`p+1` paving matroid, a maximal set is a base exactly when it
is contained in no dependent hyperplane. -/
theorem isBase_iff_not_subset_dependentHyperplane
    {p n : ℕ} (hp : 0 < p) {M : Matroid (Fin n)}
    (hM : IsRankPavingMatroid p n M)
    (J : Fin (p + 1) ↪o Fin n) :
    M.IsBase (Set.range J) ↔
      ¬∃ H : Set (Fin n), IsDependentMatroidHyperplane M H ∧
        Set.range J ⊆ H := by
  have hJcard : (Set.range J).ncard = p + 1 :=
    by simpa using Set.ncard_range_of_injective J.injective
  constructor
  · intro hJ
    rintro ⟨H, hH, hJH⟩
    have hgroundH : M.E ⊆ H := by
      rw [← hJ.closure_eq, ← hH.1.1.closure]
      exact M.closure_mono hJH
    exact hH.1.2.1 (Set.Subset.antisymm hH.1.1.subset_ground hgroundH)
  · intro hnone
    apply (hM.indep_iff_isBase_of_ncard_eq hJcard).1
    by_contra hnot
    have hdep : M.Dep (Set.range J) :=
      M.dep_of_not_indep hnot (by rw [hM.ground_eq]; simp)
    obtain ⟨H, hH, hJH⟩ :=
      exists_dependentHyperplane_superset_of_dep_ncard hp hM hJcard hdep
    exact hnone ⟨H, hH, hJH⟩

/-- Condition (i) of Theorem 1. -/
def PaperConditionI (p : ℕ) {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ A : Matrix (Fin (p + 1)) (Fin n) ℝ,
    HasFiniteToeplitzForm A ∧ TotallyNonnegative A ∧ HasFullRowRank A ∧
      columnMatroid A = M

/-- Condition (ii) of Theorem 1. -/
def PaperConditionII {p n : ℕ} (_hpn : p < n) (M : Matroid (Fin n)) : Prop :=
  ∃ Z : Finset (Fin (n - p)), Z ≠ Finset.univ ∧
    ∀ J : Fin (p + 1) ↪o Fin n,
      M.IsBase (Set.range J) ↔ ∃ t ∈ anchorFinset J, t ∉ Z

/-- Condition (iii) of Theorem 1.  The structure records that the dependent
hyperplanes are precisely proper ordinary intervals of size at least `p+1`,
with pairwise intersections of size at most `p-1`. -/
def PaperConditionIII (p : ℕ) {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ r, ∃ F : IntervalHyperplaneFamily p n r,
    ∀ H : Set (Fin n), IsDependentMatroidHyperplane M H ↔
      ∃ a, H = (Finset.Icc (F.left a) (F.right a) : Set (Fin n))

/-- Condition (i) implies the consecutive-zero-set basis rule (ii). -/
theorem paperConditionI_implies_II
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M) :
    PaperConditionI p M → PaperConditionII hpn M := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rintro ⟨A, htoeplitz, hTN, hfull, hAM⟩
  have hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)) := by
    intro cols
    apply (columnMatroid_indep_range_iff A cols).1
    rw [hAM]
    apply hM.small_indep
    simp [Set.ncard_range_of_injective cols.injective]
  obtain ⟨hproper, hrule⟩ := tnn_refinement_classification hpn hTN hfull hind
  refine ⟨matrixConsecutiveZeroSet hpn A, hproper, fun J ↦ ?_⟩
  rw [← hAM, columnMatroid_isBase_range_iff]
  simpa [matrixMaximalMinor] using hrule J

/-- A classified realization of a basis rule represents the originally
quantified abstract matroid, not merely an abstractly isomorphic support. -/
theorem classifiedRealization_columnMatroid_eq
    {p n : ℕ} (_hp : 0 < p) (hpn : p < n)
    {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M)
    {Z : Finset (Fin (n - p))}
    (hbasis : ∀ J : Fin (p + 1) ↪o Fin n,
      M.IsBase (Set.range J) ↔ ∃ t ∈ anchorFinset J, t ∉ Z)
    (R : ClassifiedToeplitzRealization p n hpn Z) :
    columnMatroid R.matrix = M := by
  have hcolBase : ∃ J : Fin (p + 1) ↪o Fin n,
      (columnMatroid R.matrix).IsBase (Set.range J) :=
    (hasFullRowRank_iff_exists_columnMatroid_isBase R.matrix).1 R.fullRowRank
  apply Matroid.ext_isBase
  · rw [columnMatroid_ground, hM.ground_eq]
  · intro B hBground
    constructor
    · intro hBR
      obtain ⟨J₀, hJ₀⟩ := hcolBase
      have hBcard : B.ncard = p + 1 := by
        rw [hBR.ncard_eq_ncard_of_isBase hJ₀]
        simpa using Set.ncard_range_of_injective J₀.injective
      let J := increasingEnumeration B hBcard
      have hJrange : Set.range J = B := range_increasingEnumeration B hBcard
      rw [← hJrange]
      apply (hbasis J).2
      apply (R.basis_rule J).1
      apply (columnMatroid_isBase_range_iff R.matrix J).1
      simpa [hJrange] using hBR
    · intro hBM
      have hBcard : B.ncard = p + 1 := hM.isBase_ncard_eq hBM
      let J := increasingEnumeration B hBcard
      have hJrange : Set.range J = B := range_increasingEnumeration B hBcard
      rw [← hJrange]
      apply (columnMatroid_isBase_range_iff R.matrix J).2
      change matrixMaximalMinor R.matrix J ≠ 0
      apply (R.basis_rule J).2
      apply (hbasis J).1
      simpa [hJrange] using hBM

/-- Condition (ii) has a Toeplitz realization whose represented column
matroid is the originally quantified abstract matroid. -/
theorem paperConditionII_implies_I
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M) :
    PaperConditionII hpn M → PaperConditionI p M := by
  rintro ⟨Z, hZ, hbasis⟩
  obtain ⟨R⟩ := exists_classifiedToeplitzRealization hp hpn Z hZ
  exact ⟨R.matrix, R.toeplitz, R.totallyNonnegative, R.fullRowRank,
    classifiedRealization_columnMatroid_eq hp hpn hM hbasis R⟩

/-- Condition (i) implies the exact dependent-interval-hyperplane
description (iii). -/
theorem paperConditionI_implies_III
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M) :
    PaperConditionI p M → PaperConditionIII p M := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rintro ⟨A, htoeplitz, hTN, hfull, hAM⟩
  have hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)) := by
    intro cols
    apply (columnMatroid_indep_range_iff A cols).1
    rw [hAM]
    apply hM.small_indep
    simp [Set.ncard_range_of_injective cols.injective]
  let Z := matrixConsecutiveZeroSet hpn A
  have hZ : Z ≠ Finset.univ :=
    (tnn_refinement_classification hpn hTN hfull hind).1
  obtain ⟨s, ⟨D⟩⟩ := exists_zeroRunDecomposition Z
  have hsupport : ∀ J : Fin ((r + 1) + 1) ↪o Fin n,
      matrixMaximalMinor A J = 0 ↔
        ∃ a, ∀ i, J i ∈ runHyperplane hpn D a := by
    intro J
    rw [refinement_maximalMinor_eq_zero_iff hpn hTN hind J]
    have hanchors :
        (∀ t ∈ anchorFinset J, matrixConsecutiveMinor hpn A t = 0) ↔
          ∀ t, IsAnchor J t → t ∈ Z := by
      constructor
      · intro h t ht
        apply (mem_matrixConsecutiveZeroSet_iff hpn A t).2
        exact h t (by simp [anchorFinset, ht])
      · intro h t ht
        apply (mem_matrixConsecutiveZeroSet_iff hpn A t).1
        exact h t (by simpa [anchorFinset] using ht)
    rw [hanchors]
    exact allAnchors_mem_iff_exists_columns_mem_runHyperplane hpn D J
  have hpavingA : ∀ X : Set (Fin n), X.ncard ≤ r + 1 →
      (columnMatroid A).Indep X := by
    intro X hX
    rw [hAM]
    exact hM.small_indep X hX
  let F := D.toIntervalHyperplaneFamily hp hpn hZ
  refine ⟨s, F, fun H ↦ ?_⟩
  rw [← hAM]
  have hhyper := isDependentMatroidHyperplane_iff_exists_runHyperplane
    hp hpn hZ D A hind hpavingA hsupport H
  rw [hhyper]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp [F]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp [F]⟩

/-- The interval-hyperplane condition (iii) recovers the zero-set basis rule
(ii) for the original abstract paving matroid. -/
theorem paperConditionIII_implies_II
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M) :
    PaperConditionIII p M → PaperConditionII hpn M := by
  rintro ⟨r, F, hhyper⟩
  refine ⟨F.zeroSet hpn, F.zeroSet_ne_univ hp hpn, fun J ↦ ?_⟩
  rw [F.basisRule_zeroSet_iff_not_columns_mem_interval hp hpn J]
  rw [isBase_iff_not_subset_dependentHyperplane hp hM J]
  constructor
  · intro hnone
    rintro ⟨a, ha⟩
    apply hnone
    let H : Set (Fin n) := Finset.Icc (F.left a) (F.right a)
    refine ⟨H, (hhyper H).2 ⟨a, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact ha i
  · intro hnone
    rintro ⟨H, hH, hJH⟩
    obtain ⟨a, rfl⟩ := (hhyper H).1 hH
    apply hnone
    exact ⟨a, fun i ↦ hJH ⟨i, rfl⟩⟩

/-- **Theorem 1 (paper-level statement).** For a rank-`m` paving matroid,
Toeplitz realizability, the proper consecutive-zero-set basis rule, and the
ordinary interval dependent-hyperplane description are equivalent. -/
theorem classification_of_pavingToeplitzPositroids
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (M : Matroid (Fin n)) (hM : IsRankPavingMatroid p n M) :
    (PaperConditionI p M ↔ PaperConditionII hpn M) ∧
      (PaperConditionII hpn M ↔ PaperConditionIII p M) := by
  constructor
  · exact ⟨paperConditionI_implies_II hp hpn hM,
      paperConditionII_implies_I hp hpn hM⟩
  · exact ⟨fun hII ↦ paperConditionI_implies_III hp hpn hM
        (paperConditionII_implies_I hp hpn hM hII),
      paperConditionIII_implies_II hp hpn hM⟩

/-- The strengthened realization clause in Theorem 1: condition (ii), and
hence any of the equivalent conditions, has a representation with every
minor below maximal order strictly positive. -/
theorem exists_strictLower_toeplitzRepresentation_of_conditionII
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    {M : Matroid (Fin n)} (hM : IsRankPavingMatroid p n M)
    (hII : PaperConditionII hpn M) :
    ∃ A : Matrix (Fin (p + 1)) (Fin n) ℝ,
      HasFiniteToeplitzForm A ∧ TotallyNonnegative A ∧ HasFullRowRank A ∧
      columnMatroid A = M ∧
      ∀ r : Fin (p + 1), ∀ (I : Fin r.val ↪o Fin (p + 1))
        (J : Fin r.val ↪o Fin n), 0 < orderedMinor A I J := by
  obtain ⟨Z, hZ, hbasis⟩ := hII
  obtain ⟨R⟩ := exists_classifiedToeplitzRealization hp hpn Z hZ
  have hEq : columnMatroid R.matrix = M :=
    classifiedRealization_columnMatroid_eq hp hpn hM hbasis R
  exact ⟨R.matrix, R.toeplitz, R.totallyNonnegative, R.fullRowRank,
    hEq, R.lowerMinor_pos⟩

end

end PavingToeplitzPositroids
