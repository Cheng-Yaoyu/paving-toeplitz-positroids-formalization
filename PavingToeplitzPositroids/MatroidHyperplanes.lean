import PavingToeplitzPositroids.SupportTheorem
import PavingToeplitzPositroids.Refinement
import ToeplitzPositroids.Matrix.ColumnMatroid
import Mathlib.Combinatorics.Matroid.Closure

/-!
# Matroid hyperplanes from zero-run intervals

This file supplies the matroid closure part of Theorem 10. Under the paving
independence hypothesis, the first `k` columns of an enlarged zero-run
interval form a basis of that interval. Adding any outside column produces a
matroid basis, because no second run interval can contain those `k` common
columns.
-/

namespace PavingToeplitzPositroids

open Set ToeplitzPositroids

noncomputable section

/-- A hyperplane is a proper flat maximal among proper flats. -/
def IsMatroidHyperplane {E : Type*} (M : Matroid E) (H : Set E) : Prop :=
  M.IsFlat H ∧ H ≠ M.E ∧
    ∀ F, M.IsFlat F → H ⊆ F → F ≠ H → F = M.E

/-- A dependent hyperplane additionally contains a circuit. -/
def IsDependentMatroidHyperplane {E : Type*} (M : Matroid E) (H : Set E) : Prop :=
  IsMatroidHyperplane M H ∧ M.Dep H

/-- The first `k` columns of an enlarged run interval. -/
def runCoreColumns {k n r : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z r) (a : Fin r) :
    Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨(D.left a).val + i.val, by
      have hleft := (D.left a).isLt
      have hi := i.isLt
      omega⟩)
    (by intro i j hij; simp only [Fin.mk_lt_mk] at hij ⊢; omega)

/-- The first `k+1` columns of an enlarged run interval. -/
def runFullColumns {k n r : ℕ} (hk : k < n)
    {Z : Finset (Fin (n - k))} (D : ZeroRunDecomposition Z r) (a : Fin r) :
    Fin (k + 1) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨(D.left a).val + i.val, by
      have hleft := (D.left a).isLt
      have hi := i.isLt
      omega⟩)
    (by intro i j hij; simp only [Fin.mk_lt_mk] at hij ⊢; omega)

theorem runCoreColumns_mem_runHyperplane
    {k n r : ℕ} (hk : k < n) {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition Z r) (a : Fin r) (i : Fin k) :
    runCoreColumns hk D a i ∈ runHyperplane hk D a := by
  simp only [runCoreColumns, runHyperplane, Finset.mem_Icc, runLeftColumn,
    runRightColumn, Fin.le_iff_val_le_val, OrderEmbedding.coe_ofStrictMono]
  have hi := i.isLt
  have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
  constructor <;> omega

theorem runFullColumns_mem_runHyperplane
    {k n r : ℕ} (hk : k < n) {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition Z r) (a : Fin r) (i : Fin (k + 1)) :
    runFullColumns hk D a i ∈ runHyperplane hk D a := by
  simp only [runFullColumns, runHyperplane, Finset.mem_Icc, runLeftColumn,
    runRightColumn, Fin.le_iff_val_le_val, OrderEmbedding.coe_ofStrictMono]
  have hi := i.isLt
  have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
  constructor <;> omega

/-- Dependence of a maximal selected column set is equivalent to vanishing of
its ordered maximal minor. -/
theorem columnMatroid_dep_range_iff_matrixMaximalMinor_eq_zero
    {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (J : Fin (k + 1) ↪o Fin n) :
    (columnMatroid A).Dep (Set.range J) ↔ matrixMaximalMinor A J = 0 := by
  rw [Matroid.dep_iff]
  simp only [columnMatroid_ground, Set.subset_univ]
  rw [columnMatroid_indep_range_iff,
    ← orderedMinor_ne_zero_iff_linearIndependent_columns]
  simp [matrixMaximalMinor]

/-- Every enlarged run interval is a dependent hyperplane of the represented
column matroid. -/
theorem runHyperplane_isDependentHyperplane
    {k n r : ℕ} (hk0 : 0 < k) (hk : k < n)
    {Z : Finset (Fin (n - k))} (hZ : Z ≠ Finset.univ)
    (D : ZeroRunDecomposition Z r)
    (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (hind : ∀ cols : Fin k ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin k ↦ A.col (cols j)))
    (hsupport : ∀ J : Fin (k + 1) ↪o Fin n,
      matrixMaximalMinor A J = 0 ↔
        ∃ b, ∀ i, J i ∈ runHyperplane hk D b)
    (a : Fin r) :
    IsDependentMatroidHyperplane (columnMatroid A)
      (runHyperplane hk D a : Set (Fin n)) := by
  let M := columnMatroid A
  let H : Set (Fin n) := runHyperplane hk D a
  let core := runCoreColumns hk D a
  let I : Set (Fin n) := Set.range core
  have hIind : M.Indep I := by
    apply (columnMatroid_indep_range_iff A core).2
    exact hind core
  have hIH : I ⊆ H := by
    rintro _ ⟨i, rfl⟩
    exact runCoreColumns_mem_runHyperplane hk D a i
  have hHclosure : H ⊆ M.closure I := by
    intro y hyH
    by_cases hyI : y ∈ I
    · exact M.subset_closure I hIind.subset_ground hyI
    · have hycore : y ∉ Set.range core := hyI
      let Jy := sortedAppendOne core y hycore
      have hJyRange : Set.range Jy = insert y I := by
        rw [range_sortedAppendOne]
        ext z
        simp [I]
      have hJyH : ∀ i, Jy i ∈ runHyperplane hk D a := by
        intro i
        have hi : Jy i ∈ Set.range Jy := ⟨i, rfl⟩
        rw [hJyRange] at hi
        simp only [Set.mem_insert_iff] at hi
        rcases hi with (hi | hi)
        · rw [hi]
          exact hyH
        · exact hIH hi
      have hminor : matrixMaximalMinor A Jy = 0 :=
        (hsupport Jy).2 ⟨a, hJyH⟩
      have hdep : M.Dep (insert y I) := by
        rw [← hJyRange,
          columnMatroid_dep_range_iff_matrixMaximalMinor_eq_zero]
        exact hminor
      exact (hIind.mem_closure_iff_of_notMem hyI).2 hdep
  have hIbasis : M.IsBasis I H :=
    hIind.isBasis_of_subset_of_subset_closure hIH hHclosure
  have hclosureIH : M.closure I = M.closure H := hIbasis.closure_eq_closure
  have houtside_basis : ∀ (x : Fin n) (hxH : x ∉ H),
      matrixMaximalMinor A
        (sortedAppendOne core x (fun hx ↦ hxH (hIH hx))) ≠ 0 := by
    intro x hxH
    have hxcore : x ∉ Set.range core := fun hx ↦ hxH (hIH hx)
    let Jx := sortedAppendOne core x hxcore
    intro hzero
    obtain ⟨b, hb⟩ := (hsupport Jx).1 hzero
    have hJxRange := range_sortedAppendOne core x hxcore
    have hxJ : x ∈ Set.range Jx := by
      rw [hJxRange]
      simp
    have hxb : x ∈ runHyperplane hk D b := by
      obtain ⟨i, hi⟩ := hxJ
      rw [← hi]
      exact hb i
    by_cases hba : b = a
    · subst b
      exact hxH hxb
    · let s : Finset (Fin n) := Finset.univ.map core.toEmbedding
      have hscard : s.card = k := by simp [s]
      have hsub : s ⊆ runHyperplane hk D a ∩ runHyperplane hk D b := by
        intro z hz
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hz
        change core i ∈ runHyperplane hk D a ∩ runHyperplane hk D b
        apply Finset.mem_inter.mpr
        refine ⟨runCoreColumns_mem_runHyperplane hk D a i, ?_⟩
        have hi : core i ∈ Set.range Jx := by
          rw [hJxRange]
          exact Or.inl ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := hi
        rw [← hj]
        exact hb j
      have hcard := Finset.card_le_card hsub
      have hinter := card_runHyperplane_inter_le hk D (Ne.symm hba)
      rw [hscard] at hcard
      omega
  have hclosure : M.closure H = H := by
    apply Set.Subset.antisymm
    · intro x hxcl
      by_contra hxH
      have hxI : x ∉ I := fun hx ↦ hxH (hIH hx)
      have hxclI : x ∈ M.closure I := by
        rw [hclosureIH]
        exact hxcl
      have hxcore : x ∉ Set.range core := fun hx ↦ hxH (hIH hx)
      let Jx := sortedAppendOne core x hxcore
      have hminor := houtside_basis x hxH
      have hJind : M.Indep (Set.range Jx) := by
        rw [columnMatroid_indep_range_iff,
          ← orderedMinor_ne_zero_iff_linearIndependent_columns]
        exact hminor
      have hJrange : Set.range Jx = insert x I := by
        rw [range_sortedAppendOne]
        ext z
        simp [I]
      rw [hJrange] at hJind
      exact ((hIind.notMem_closure_iff_of_notMem hxI).2 hJind) hxclI
    · exact M.subset_closure H (by simp [M])
  have hflat : M.IsFlat H := Matroid.isFlat_iff_closure_eq.2 hclosure
  have hproper : H ≠ M.E := by
    intro hHE
    apply hZ
    ext t
    simp only [Finset.mem_univ, iff_true]
    apply (D.mem_iff t).2
    let zeron : Fin n := ⟨0, by omega⟩
    let lastn : Fin n := ⟨n - 1, by omega⟩
    have hzeroH : zeron ∈ H := by
      rw [hHE]
      simp [M]
    have hlastH : lastn ∈ H := by
      rw [hHE]
      simp [M]
    change zeron ∈ runHyperplane hk D a at hzeroH
    change lastn ∈ runHyperplane hk D a at hlastH
    have hzBounds := Finset.mem_Icc.mp hzeroH
    have hlBounds := Finset.mem_Icc.mp hlastH
    simp only [runLeftColumn, runRightColumn, Fin.le_iff_val_le_val] at hzBounds hlBounds
    dsimp only [zeron] at hzBounds
    dsimp only [lastn] at hlBounds
    refine ⟨a, ?_, ?_⟩
    · omega
    · have ht := t.isLt
      omega
  have hdepH : M.Dep H := by
    let J := runFullColumns hk D a
    have hJall : ∀ i, J i ∈ runHyperplane hk D a :=
      runFullColumns_mem_runHyperplane hk D a
    have hminor : matrixMaximalMinor A J = 0 := (hsupport J).2 ⟨a, hJall⟩
    have hdepJ : M.Dep (Set.range J) :=
      (columnMatroid_dep_range_iff_matrixMaximalMinor_eq_zero A J).2 hminor
    apply hdepJ.superset
    rintro _ ⟨i, rfl⟩
    exact hJall i
  refine ⟨⟨hflat, hproper, ?_⟩, hdepH⟩
  intro F hF hHF hne
  have hstrict : ∃ x, x ∈ F ∧ x ∉ H := by
    by_contra hnone
    push Not at hnone
    exact hne (Set.Subset.antisymm (fun x hx ↦ hnone x hx) hHF)
  obtain ⟨x, hxF, hxH⟩ := hstrict
  let Jx := sortedAppendOne core x (fun hx ↦ hxH (hIH hx))
  have hminor := houtside_basis x hxH
  have hbase : M.IsBase (Set.range Jx) := by
    rw [columnMatroid_isBase_range_iff]
    exact hminor
  have hJrange : Set.range Jx = insert x I := by
    rw [range_sortedAppendOne]
    ext z
    simp [I]
  have hJsub : Set.range Jx ⊆ F := by
    rw [hJrange]
    exact insert_subset hxF (hIH.trans hHF)
  have hground : M.E ⊆ F := by
    rw [← hbase.closure_eq, ← hF.closure]
    exact M.closure_mono hJsub
  exact Set.Subset.antisymm hF.subset_ground hground

/-- Two proper matroid hyperplanes containing the same dependent maximal
column selection coincide under the paving independence hypothesis. -/
theorem matroidHyperplane_eq_of_common_dependent_maximal
    {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (hind : ∀ cols : Fin k ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin k ↦ A.col (cols j)))
    {F G : Set (Fin n)} (hF : IsMatroidHyperplane (columnMatroid A) F)
    (hG : IsMatroidHyperplane (columnMatroid A) G)
    (J : Fin (k + 1) ↪o Fin n) (hJF : Set.range J ⊆ F)
    (hJG : Set.range J ⊆ G) (hJzero : matrixMaximalMinor A J = 0) :
    F = G := by
  let M := columnMatroid A
  let K : Fin k ↪o Fin n := (Fin.succAboveOrderEmb 0).trans J
  let y : Fin n := J 0
  let I : Set (Fin n) := Set.range K
  have hyI : y ∉ I := by
    rintro ⟨i, hi⟩
    have hindex : (0 : Fin (k + 1)) = (0 : Fin (k + 1)).succAbove i :=
      J.injective hi.symm
    exact (Fin.ne_of_lt (Fin.succ_pos i)) (by simpa using hindex)
  have hJrange : Set.range J = insert y I := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ (fun q ↦ ?_) i
      · exact Set.mem_insert _ _
      · change J q.succ = y ∨ J q.succ ∈ I
        exact Or.inr ⟨q, rfl⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · exact ⟨0, rfl⟩
      · exact ⟨i.succ, rfl⟩
  have hIind : M.Indep I := by
    exact (columnMatroid_indep_range_iff A K).2 (hind K)
  have hJdep : M.Dep (insert y I) := by
    rw [← hJrange,
      columnMatroid_dep_range_iff_matrixMaximalMinor_eq_zero]
    exact hJzero
  have hclosure_eq (Q : Set (Fin n))
      (hQ : IsMatroidHyperplane M Q) (hJQ : Set.range J ⊆ Q) :
      M.closure I = Q := by
    have hIQ : I ⊆ Q := by
      intro x hx
      apply hJQ
      rw [hJrange]
      change x = y ∨ x ∈ I
      exact Or.inr hx
    apply Set.Subset.antisymm
    · rw [← hQ.1.closure]
      exact M.closure_mono hIQ
    · intro x hxQ
      by_contra hxcl
      have hxI : x ∉ I := fun hx ↦ hxcl (M.subset_closure I hIind.subset_ground hx)
      have hxind : M.Indep (insert x I) :=
        (hIind.notMem_closure_iff_of_notMem hxI).1 hxcl
      let Jx := sortedAppendOne K x hxI
      have hJxRange : Set.range Jx = insert x I := by
        rw [range_sortedAppendOne]
        ext z
        simp [I]
      have hJxind : M.Indep (Set.range Jx) := by rwa [hJxRange]
      have hminor : matrixMaximalMinor A Jx ≠ 0 := by
        rw [matrixMaximalMinor,
          orderedMinor_ne_zero_iff_linearIndependent_columns]
        exact (columnMatroid_indep_range_iff A Jx).1 hJxind
      have hbase : M.IsBase (Set.range Jx) := by
        rw [columnMatroid_isBase_range_iff]
        exact hminor
      have hJxQ : Set.range Jx ⊆ Q := by
        rw [hJxRange]
        exact insert_subset hxQ hIQ
      have hgroundQ : M.E ⊆ Q := by
        rw [← hbase.closure_eq, ← hQ.1.closure]
        exact M.closure_mono hJxQ
      exact hQ.2.1 (Set.Subset.antisymm hQ.1.subset_ground hgroundQ)
  rw [← hclosure_eq F hF hJF, ← hclosure_eq G hG hJG]

/-- In a rank-`k+1` represented paving matroid, every dependent hyperplane
contains a dependent maximal column selection. -/
theorem dependentHyperplane_contains_dependent_maximal
    {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    {F : Set (Fin n)} (hF : IsDependentMatroidHyperplane (columnMatroid A) F)
    (hpaving : ∀ X : Set (Fin n), X.ncard ≤ k → (columnMatroid A).Indep X) :
    ∃ J : Fin (k + 1) ↪o Fin n,
      Set.range J ⊆ F ∧ matrixMaximalMinor A J = 0 := by
  let M := columnMatroid A
  obtain ⟨B, hB⟩ := M.exists_isBasis F
  have hBproper : B ≠ F := by
    intro hBF
    apply hF.2.not_indep
    rw [← hBF]
    exact hB.indep
  have hnotSubset : ¬F ⊆ B := by
    intro hFB
    exact hBproper (Set.Subset.antisymm hB.subset hFB)
  obtain ⟨x, hxF, hxB⟩ := Set.not_subset.mp hnotSubset
  have hdepInsert : M.Dep (insert x B) :=
    hB.insert_dep ⟨hxF, hxB⟩
  have hkB : k ≤ B.ncard := by
    by_contra hk
    have hcard : (insert x B).ncard ≤ k := by
      rw [Set.ncard_insert_of_notMem hxB]
      omega
    exact hdepInsert.not_indep (hpaving (insert x B) hcard)
  have hBfinite : B.Finite := Set.toFinite B
  letI : Fintype B := hBfinite.fintype
  have hBlin : LinearIndependent ℝ (fun j : B ↦ A.col j) := by
    exact (columnMatroid_indep_iff A B).1 hB.indep
  have hcardle := hBlin.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hcardle
  have hBncard : B.ncard ≤ k + 1 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    simpa using hcardle
  have hBcard : B.ncard = k := by
    by_contra hne
    have heq : B.ncard = k + 1 := by omega
    let bfin : Finset (Fin n) := B.toFinset
    have hbcard : bfin.card = k + 1 := by
      change B.toFinset.card = k + 1
      rw [← Set.ncard_eq_toFinset_card' B]
      exact heq
    let J : Fin (k + 1) ↪o Fin n := bfin.orderEmbOfFin hbcard
    have hJrange : Set.range J = B := by
      change Set.range (bfin.orderEmbOfFin hbcard) = B
      rw [Finset.range_orderEmbOfFin]
      simp [bfin]
    have hJind : M.Indep (Set.range J) := by rw [hJrange]; exact hB.indep
    have hminor : matrixMaximalMinor A J ≠ 0 := by
      rw [matrixMaximalMinor,
        orderedMinor_ne_zero_iff_linearIndependent_columns]
      exact (columnMatroid_indep_range_iff A J).1 hJind
    have hbase : M.IsBase (Set.range J) := by
      rw [columnMatroid_isBase_range_iff]
      exact hminor
    have hclosureGround : M.closure B = M.E := by
      rw [← hJrange]
      exact hbase.closure_eq
    have hclosureF : M.closure F = F := hF.1.1.closure
    have hBFclosure := hB.closure_eq_closure
    apply hF.1.2.1
    rw [← hclosureF, ← hBFclosure, hclosureGround]
  have hInsertCard : (insert x B).ncard = k + 1 := by
    rw [Set.ncard_insert_of_notMem hxB, hBcard]
  have hInsertFinite : (insert x B).Finite := Set.toFinite _
  letI : Fintype {y // y ∈ insert x B} := hInsertFinite.fintype
  let cfin : Finset (Fin n) := (insert x B).toFinset
  have hcCard : cfin.card = k + 1 := by
    change (insert x B).toFinset.card = k + 1
    rw [← Set.ncard_eq_toFinset_card' (insert x B)]
    exact hInsertCard
  let J : Fin (k + 1) ↪o Fin n := cfin.orderEmbOfFin hcCard
  have hJrange : Set.range J = insert x B := by
    change Set.range (cfin.orderEmbOfFin hcCard) = insert x B
    rw [Finset.range_orderEmbOfFin]
    simp [cfin]
  refine ⟨J, ?_, ?_⟩
  · rw [hJrange]
    exact insert_subset hxF hB.subset
  · apply (columnMatroid_dep_range_iff_matrixMaximalMinor_eq_zero A J).1
    rwa [hJrange]

/-- **Theorem 10, hyperplane exhaustion.** The dependent hyperplanes are
exactly the enlarged maximal zero-run intervals. -/
theorem isDependentMatroidHyperplane_iff_exists_runHyperplane
    {k n r : ℕ} (hk0 : 0 < k) (hk : k < n)
    {Z : Finset (Fin (n - k))} (hZ : Z ≠ Finset.univ)
    (D : ZeroRunDecomposition Z r)
    (A : Matrix (Fin (k + 1)) (Fin n) ℝ)
    (hind : ∀ cols : Fin k ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin k ↦ A.col (cols j)))
    (hpaving : ∀ X : Set (Fin n), X.ncard ≤ k → (columnMatroid A).Indep X)
    (hsupport : ∀ J : Fin (k + 1) ↪o Fin n,
      matrixMaximalMinor A J = 0 ↔
        ∃ b, ∀ i, J i ∈ runHyperplane hk D b)
    (F : Set (Fin n)) :
    IsDependentMatroidHyperplane (columnMatroid A) F ↔
      ∃ a, F = (runHyperplane hk D a : Set (Fin n)) := by
  constructor
  · intro hF
    obtain ⟨J, hJF, hJzero⟩ :=
      dependentHyperplane_contains_dependent_maximal A hF hpaving
    obtain ⟨a, hJa⟩ := (hsupport J).1 hJzero
    have hHa := runHyperplane_isDependentHyperplane hk0 hk hZ D A hind hsupport a
    refine ⟨a, matroidHyperplane_eq_of_common_dependent_maximal A hind
      hF.1 hHa.1 J hJF ?_ hJzero⟩
    rintro _ ⟨i, rfl⟩
    exact hJa i
  · rintro ⟨a, rfl⟩
    exact runHyperplane_isDependentHyperplane hk0 hk hZ D A hind hsupport a

end

end PavingToeplitzPositroids
