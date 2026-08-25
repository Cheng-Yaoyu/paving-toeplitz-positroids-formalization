import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import PavingToeplitzPositroids.PaperClassification

/-!
# Counting proper consecutive-minor zero sets

Once realizability and support injectivity are established, the final count in
Theorem 1 is the elementary cardinality calculation below.
-/

namespace PavingToeplitzPositroids

open ToeplitzPositroids

/-- Proper subsets of the `N` consecutive-minor positions. -/
def ProperZeroSet (N : ℕ) :=
  {Z : Finset (Fin N) // Z ≠ Finset.univ}

/-- There are exactly `2^N - 1` proper zero sets. -/
theorem card_properZeroSet (N : ℕ) :
    Fintype.card {Z : Finset (Fin N) // Z ≠ Finset.univ} = 2 ^ N - 1 := by
  rw [show Fintype.card {Z : Finset (Fin N) // Z ≠ Finset.univ} =
      Fintype.card (Finset (Fin N)) -
        Fintype.card {Z : Finset (Fin N) // Z = Finset.univ} by
    exact Fintype.card_subtype_compl (fun Z : Finset (Fin N) ↦ Z = Finset.univ)]
  simp [Fintype.card_finset]

/-- The basis-support rule associated with a consecutive zero set. -/
def zeroSetBasisSupport {p n : ℕ} (Z : Finset (Fin (n - p)))
    (J : Fin (p + 1) ↪o Fin n) : Prop :=
  ∃ t ∈ anchorFinset J, t ∉ Z

/-- A consecutive maximal selection reads one zero-set coordinate. -/
theorem zeroSetBasisSupport_consecutive
    {p n : ℕ} (hpn : p < n) (Z : Finset (Fin (n - p)))
    (t : Fin (n - p)) :
    zeroSetBasisSupport Z (consecutiveColumns hpn t) ↔ t ∉ Z := by
  unfold zeroSetBasisSupport
  rw [anchorFinset_eq_singleton_of_span_eq hpn _
    (columnSpan_consecutiveColumns hpn t)]
  have hfirst : firstAnchor hpn (consecutiveColumns hpn t) = t := by
    apply Fin.ext
    simp
  simp [hfirst]

/-- Distinct zero sets give distinct maximal-minor supports. -/
theorem zeroSetBasisSupport_injective
    {p n : ℕ} (hpn : p < n) :
    Function.Injective
      (fun Z : Finset (Fin (n - p)) ↦ zeroSetBasisSupport (p := p) (n := n) Z) := by
  intro Z W h
  ext t
  have ht := congrFun h (consecutiveColumns hpn t)
  have ht' : zeroSetBasisSupport Z (consecutiveColumns hpn t) ↔
      zeroSetBasisSupport W (consecutiveColumns hpn t) := by
    change (fun Z ↦ zeroSetBasisSupport Z) Z (consecutiveColumns hpn t) ↔
      (fun Z ↦ zeroSetBasisSupport Z) W (consecutiveColumns hpn t)
    rw [ht]
  rw [zeroSetBasisSupport_consecutive hpn Z,
    zeroSetBasisSupport_consecutive hpn W] at ht'
  tauto

/-- Consequently, the support rules indexed by proper zero sets are counted
by `2^(n-p)-1`. -/
theorem card_zeroSetBasisSupport_range
    {p n : ℕ} (hpn : p < n) :
    Nat.card (Set.range (fun Z : ProperZeroSet (n - p) ↦
      zeroSetBasisSupport (p := p) (n := n) Z.1)) = 2 ^ (n - p) - 1 := by
  letI : Fintype (ProperZeroSet (n - p)) := by
    unfold ProperZeroSet
    infer_instance
  let f := fun Z : ProperZeroSet (n - p) ↦
    zeroSetBasisSupport (p := p) (n := n) Z.1
  have hf : Function.Injective f := fun Z W h ↦
    Subtype.ext (zeroSetBasisSupport_injective hpn h)
  calc
    Nat.card (Set.range f) = Nat.card (ProperZeroSet (n - p)) :=
      (Nat.card_congr (Equiv.ofInjective f hf)).symm
    _ = Fintype.card (ProperZeroSet (n - p)) := Nat.card_eq_fintype_card
    _ = 2 ^ (n - p) - 1 := by
      simp [ProperZeroSet]

/-- A rank-`p+1` paving matroid admitting a full-row-rank matrix
representation that is totally nonnegative in every minor order.  No
Toeplitz hypothesis is imposed. -/
def IsAllMinorTNNPavingMatroid (p n : ℕ) (M : Matroid (Fin n)) : Prop :=
  IsRankPavingMatroid p n M ∧
    ∃ A : Matrix (Fin (p + 1)) (Fin n) ℝ,
      TotallyNonnegative A ∧ HasFullRowRank A ∧ columnMatroid A = M

/-- The type of paving positroid cells covered by the first sentence of
Corollary 11. -/
def AllMinorTNNPavingMatroid (p n : ℕ) :=
  {M : Matroid (Fin n) // IsAllMinorTNNPavingMatroid p n M}

/-- The intrinsic consecutive-nonbasis set of a rank-`p+1` matroid. -/
noncomputable def matroidConsecutiveNonbasisSet
    {p n : ℕ} (hpn : p < n) (M : Matroid (Fin n)) : Finset (Fin (n - p)) := by
  classical
  exact Finset.univ.filter fun t ↦
    ¬M.IsBase (Set.range (consecutiveColumns hpn t))

@[simp]
theorem mem_matroidConsecutiveNonbasisSet_iff
    {p n : ℕ} (hpn : p < n) (M : Matroid (Fin n)) (t : Fin (n - p)) :
    t ∈ matroidConsecutiveNonbasisSet hpn M ↔
      ¬M.IsBase (Set.range (consecutiveColumns hpn t)) := by
  classical
  simp [matroidConsecutiveNonbasisSet]

/-- Theorem 8 gives the intrinsic zero-set basis rule for every all-minor
TNN paving representation, without any Toeplitz hypothesis. -/
theorem allMinorTNNPavingMatroid_classification
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (M : Matroid (Fin n)) (hM : IsAllMinorTNNPavingMatroid p n M) :
    matroidConsecutiveNonbasisSet hpn M ≠ Finset.univ ∧
      ∀ J : Fin (p + 1) ↪o Fin n,
        M.IsBase (Set.range J) ↔
          ∃ t ∈ anchorFinset J, t ∉ matroidConsecutiveNonbasisSet hpn M := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨A, hTN, hfull, hAM⟩ := hM.2
  have hind : ∀ cols : Fin (r + 1) ↪o Fin n,
      LinearIndependent ℝ (fun j : Fin (r + 1) ↦ A.col (cols j)) := by
    intro cols
    apply (columnMatroid_indep_range_iff A cols).1
    rw [hAM]
    apply hM.1.small_indep
    simp [Set.ncard_range_of_injective cols.injective]
  obtain ⟨hproper, hrule⟩ := tnn_refinement_classification hpn hTN hfull hind
  have hzero : matroidConsecutiveNonbasisSet hpn M =
      matrixConsecutiveZeroSet hpn A := by
    ext t
    rw [mem_matroidConsecutiveNonbasisSet_iff,
      mem_matrixConsecutiveZeroSet_iff, ← hAM,
      columnMatroid_isBase_range_iff]
    change (¬matrixConsecutiveMinor hpn A t ≠ 0) ↔
      matrixConsecutiveMinor hpn A t = 0
    tauto
  constructor
  · rwa [hzero]
  · intro J
    calc
      M.IsBase (Set.range J) ↔
          (columnMatroid A).IsBase (Set.range J) := by rw [hAM]
      _ ↔ matrixMaximalMinor A J ≠ 0 :=
        columnMatroid_isBase_range_iff A J
      _ ↔ ∃ t ∈ anchorFinset J, t ∉ matrixConsecutiveZeroSet hpn A := hrule J
      _ ↔ ∃ t ∈ anchorFinset J,
          t ∉ matroidConsecutiveNonbasisSet hpn M := by rw [hzero]

/-- The intrinsic consecutive-nonbasis set, bundled with its properness
proof, for an arbitrary all-minor TNN paving positroid cell. -/
noncomputable def allMinorTNNPavingMatroidZeroSet
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (M : AllMinorTNNPavingMatroid p n) : ProperZeroSet (n - p) :=
  ⟨matroidConsecutiveNonbasisSet hpn M.1,
    (allMinorTNNPavingMatroid_classification hp hpn M.1 M.2).1⟩

/-- Distinct all-minor TNN paving positroid cells have distinct intrinsic
consecutive-nonbasis sets. -/
theorem allMinorTNNPavingMatroidZeroSet_injective
    {p n : ℕ} (hp : 0 < p) (hpn : p < n) :
    Function.Injective (allMinorTNNPavingMatroidZeroSet hp hpn) := by
  intro M N hMN
  have hsets : matroidConsecutiveNonbasisSet hpn M.1 =
      matroidConsecutiveNonbasisSet hpn N.1 :=
    congrArg Subtype.val hMN
  have hMclass := allMinorTNNPavingMatroid_classification hp hpn M.1 M.2
  have hNclass := allMinorTNNPavingMatroid_classification hp hpn N.1 N.2
  apply Subtype.ext
  apply Matroid.ext_isBase
  · rw [M.2.1.ground_eq, N.2.1.ground_eq]
  · intro B _hBground
    constructor
    · intro hMB
      have hBcard : B.ncard = p + 1 := M.2.1.isBase_ncard_eq hMB
      let J := increasingEnumeration B hBcard
      have hJrange : Set.range J = B := range_increasingEnumeration B hBcard
      have hsupport : ∃ t ∈ anchorFinset J,
          t ∉ matroidConsecutiveNonbasisSet hpn M.1 :=
        (hMclass.2 J).1 (by simpa [hJrange] using hMB)
      rw [hsets] at hsupport
      have hNB := (hNclass.2 J).2 hsupport
      simpa [hJrange] using hNB
    · intro hNB
      have hBcard : B.ncard = p + 1 := N.2.1.isBase_ncard_eq hNB
      let J := increasingEnumeration B hBcard
      have hJrange : Set.range J = B := range_increasingEnumeration B hBcard
      have hsupport : ∃ t ∈ anchorFinset J,
          t ∉ matroidConsecutiveNonbasisSet hpn N.1 :=
        (hNclass.2 J).1 (by simpa [hJrange] using hNB)
      rw [← hsets] at hsupport
      have hMB := (hMclass.2 J).2 hsupport
      simpa [hJrange] using hMB

/-- **Corollary 11, general upper bound.** For fixed rank and ground-set
size, at most `2^(n-p)-1` paving positroid cells admit a full-row-rank
all-minor totally nonnegative matrix representation. -/
theorem card_allMinorTNNPavingMatroid_le
    {p n : ℕ} (hp : 0 < p) (hpn : p < n) :
    Nat.card (AllMinorTNNPavingMatroid p n) ≤ 2 ^ (n - p) - 1 := by
  letI : Fintype (ProperZeroSet (n - p)) := by
    unfold ProperZeroSet
    infer_instance
  calc
    Nat.card (AllMinorTNNPavingMatroid p n) ≤
        Nat.card (ProperZeroSet (n - p)) :=
      Nat.card_le_card_of_injective
        (allMinorTNNPavingMatroidZeroSet hp hpn)
        (allMinorTNNPavingMatroidZeroSet_injective hp hpn)
    _ = Fintype.card (ProperZeroSet (n - p)) := Nat.card_eq_fintype_card
    _ = 2 ^ (n - p) - 1 := card_properZeroSet (n - p)

/-- A canonical classified Toeplitz realization chosen for each proper zero
set.  Its mathematical properties do not depend on the choice. -/
noncomputable def canonicalClassifiedRealization
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (Z : ProperZeroSet (n - p)) :
    ClassifiedToeplitzRealization p n hpn Z.1 :=
  Classical.choice (exists_classifiedToeplitzRealization hp hpn Z.1 Z.2)

/-- The actual represented matroid associated with a proper zero set. -/
noncomputable def realizedToeplitzMatroid
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (Z : ProperZeroSet (n - p)) : Matroid (Fin n) :=
  columnMatroid (canonicalClassifiedRealization hp hpn Z).matrix

/-- Every matroid counted here genuinely has a full-row-rank all-minor TNN
Toeplitz representation. -/
theorem realizedToeplitzMatroid_conditionI
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (Z : ProperZeroSet (n - p)) :
    PaperConditionI p (realizedToeplitzMatroid hp hpn Z) := by
  let R := canonicalClassifiedRealization hp hpn Z
  exact ⟨R.matrix, R.toeplitz, R.totallyNonnegative, R.fullRowRank, rfl⟩

/-- Among rank-`p+1` paving matroids, the range above is exactly the class
described by condition (i), so the subsequent cardinality is a cell count
rather than merely a count of chosen examples. -/
theorem paperConditionI_iff_mem_realizedToeplitzMatroid_range
    {p n : ℕ} (hp : 0 < p) (hpn : p < n)
    (M : Matroid (Fin n)) (hM : IsRankPavingMatroid p n M) :
    PaperConditionI p M ↔
      M ∈ Set.range (realizedToeplitzMatroid hp hpn) := by
  constructor
  · intro hI
    obtain ⟨Z, hZ, hbasis⟩ := paperConditionI_implies_II hp hpn hM hI
    let z : ProperZeroSet (n - p) := ⟨Z, hZ⟩
    let R := canonicalClassifiedRealization hp hpn z
    refine ⟨z, ?_⟩
    change columnMatroid R.matrix = M
    exact classifiedRealization_columnMatroid_eq hp hpn hM hbasis R
  · rintro ⟨Z, rfl⟩
    exact realizedToeplitzMatroid_conditionI hp hpn Z

/-- Distinct proper zero sets give distinct represented column matroids, not
merely distinct auxiliary support predicates. -/
theorem realizedToeplitzMatroid_injective
    {p n : ℕ} (hp : 0 < p) (hpn : p < n) :
    Function.Injective (realizedToeplitzMatroid hp hpn) := by
  intro Z W hZW
  apply Subtype.ext
  ext t
  let RZ := canonicalClassifiedRealization hp hpn Z
  let RW := canonicalClassifiedRealization hp hpn W
  let J := consecutiveColumns hpn t
  have hZbase : (columnMatroid RZ.matrix).IsBase (Set.range J) ↔ t ∉ Z.1 := by
    rw [columnMatroid_isBase_range_iff]
    change matrixMaximalMinor RZ.matrix J ≠ 0 ↔ t ∉ Z.1
    rw [RZ.basis_rule]
    exact zeroSetBasisSupport_consecutive hpn Z.1 t
  have hWbase : (columnMatroid RW.matrix).IsBase (Set.range J) ↔ t ∉ W.1 := by
    rw [columnMatroid_isBase_range_iff]
    change matrixMaximalMinor RW.matrix J ≠ 0 ↔ t ∉ W.1
    rw [RW.basis_rule]
    exact zeroSetBasisSupport_consecutive hpn W.1 t
  have hbase : (columnMatroid RZ.matrix).IsBase (Set.range J) ↔
      (columnMatroid RW.matrix).IsBase (Set.range J) := by
    change (realizedToeplitzMatroid hp hpn Z).IsBase (Set.range J) ↔
      (realizedToeplitzMatroid hp hpn W).IsBase (Set.range J)
    rw [hZW]
  have hnot : t ∉ Z.1 ↔ t ∉ W.1 := hZbase.symm.trans (hbase.trans hWbase)
  tauto

/-- **Corollary 11 and the final count in Theorem 1.** The collection of
actual Toeplitz-realized paving column matroids indexed by proper zero sets
has cardinality exactly `2^(n-p)-1`. -/
theorem card_realizedToeplitzMatroid_range
    {p n : ℕ} (hp : 0 < p) (hpn : p < n) :
    Nat.card (Set.range (realizedToeplitzMatroid hp hpn)) =
      2 ^ (n - p) - 1 := by
  letI : Fintype (ProperZeroSet (n - p)) := by
    unfold ProperZeroSet
    infer_instance
  let f := realizedToeplitzMatroid hp hpn
  have hf : Function.Injective f := realizedToeplitzMatroid_injective hp hpn
  calc
    Nat.card (Set.range f) = Nat.card (ProperZeroSet (n - p)) :=
      (Nat.card_congr (Equiv.ofInjective f hf)).symm
    _ = Fintype.card (ProperZeroSet (n - p)) := Nat.card_eq_fintype_card
    _ = 2 ^ (n - p) - 1 := by simp [ProperZeroSet]

end PavingToeplitzPositroids
