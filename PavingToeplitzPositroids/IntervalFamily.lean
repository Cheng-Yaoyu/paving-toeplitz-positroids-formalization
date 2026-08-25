import PavingToeplitzPositroids.ZeroRunExistence
import PavingToeplitzPositroids.Interpolation

/-!
# Interval-hyperplane families and reduced zero runs

This file formalizes the `(iii) -> (ii)` interval calculation in Theorem 1.
An ordered family of proper intervals of length at least `k+1`, with pairwise
intersection at most `k-1`, reduces to a separated family of anchor intervals
after subtracting `k` from every right endpoint.
-/

namespace PavingToeplitzPositroids

open Set

noncomputable section

/-- The interval data in condition (iii), written with `k=m-1`. -/
structure IntervalHyperplaneFamily (k n r : ℕ) where
  left : Fin r → Fin n
  right : Fin r → Fin n
  left_le_right : ∀ a, left a ≤ right a
  long : ∀ a, (left a).val + k ≤ (right a).val
  left_strictMono : StrictMono left
  proper : ∀ a, Finset.Icc (left a) (right a) ≠ Finset.univ
  inter_card_le : ∀ {a b}, a ≠ b →
    ((Finset.Icc (left a) (right a)) ∩
      Finset.Icc (left b) (right b)).card ≤ k - 1

namespace IntervalHyperplaneFamily

variable {k n r : ℕ} (F : IntervalHyperplaneFamily k n r)

/-- The intersection bound prevents a later interval from being contained in
an earlier one, so right endpoints increase with left endpoints. -/
theorem right_strictMono : StrictMono F.right := by
  intro a b hab
  by_contra hnot
  have hright : F.right b ≤ F.right a := not_lt.mp hnot
  have hsub : Finset.Icc (F.left b) (F.right b) ⊆
      Finset.Icc (F.left a) (F.right a) ∩
        Finset.Icc (F.left b) (F.right b) := by
    intro x hx
    apply Finset.mem_inter.mpr
    refine ⟨?_, hx⟩
    have hleft := (F.left_strictMono hab).le
    exact Finset.mem_Icc.mpr
      ⟨hleft.trans (Finset.mem_Icc.mp hx).1,
        (Finset.mem_Icc.mp hx).2.trans hright⟩
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Icc] at hcard
  have hinter := F.inter_card_le hab.ne
  have hlong := F.long b
  omega

/-- Left endpoint in the reduced anchor-index space. -/
def reducedLeft (hk : k < n) (a : Fin r) : Fin (n - k) :=
  ⟨(F.left a).val, by
    have hlong := F.long a
    have hright := (F.right a).isLt
    omega⟩

/-- Right endpoint in the reduced anchor-index space. -/
def reducedRight (hk : k < n) (a : Fin r) : Fin (n - k) :=
  ⟨(F.right a).val - k, by
    have hright := (F.right a).isLt
    omega⟩

theorem reducedLeft_le_reducedRight (hk : k < n) (a : Fin r) :
    F.reducedLeft hk a ≤ F.reducedRight hk a := by
  simp only [reducedLeft, reducedRight, Fin.le_iff_val_le_val]
  have hlong := F.long a
  omega

/-- The reduced intervals are separated by at least one missing anchor. -/
theorem reduced_separated (hk0 : 0 < k) (hk : k < n) {a b : Fin r} (hab : a < b) :
    (F.reducedRight hk a).val + 1 < (F.reducedLeft hk b).val := by
  have hleft := F.left_strictMono hab
  have hright := F.right_strictMono hab
  have hlong := F.long a
  by_cases hdisjoint : F.right a < F.left b
  · simp only [reducedLeft, reducedRight]
    omega
  · have hoverlap : F.left b ≤ F.right a := not_lt.mp hdisjoint
    have hsub : Finset.Icc (F.left b) (F.right a) ⊆
        Finset.Icc (F.left a) (F.right a) ∩
          Finset.Icc (F.left b) (F.right b) := by
      intro x hx
      apply Finset.mem_inter.mpr
      constructor
      · exact Finset.mem_Icc.mpr
          ⟨(hleft.le.trans (Finset.mem_Icc.mp hx).1), (Finset.mem_Icc.mp hx).2⟩
      · exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hx).2.trans hright.le⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Icc] at hcard
    have hinter := F.inter_card_le hab.ne
    simp only [reducedLeft, reducedRight]
    omega

/-- The union of the reduced intervals in anchor-index space. -/
def zeroSet (hk : k < n) : Finset (Fin (n - k)) :=
  Finset.univ.filter fun t ↦
    ∃ a, F.reducedLeft hk a ≤ t ∧ t ≤ F.reducedRight hk a

@[simp]
theorem mem_zeroSet_iff (hk : k < n) (t : Fin (n - k)) :
    t ∈ F.zeroSet hk ↔
      ∃ a, F.reducedLeft hk a ≤ t ∧ t ≤ F.reducedRight hk a := by
  simp [zeroSet]

/-- The reduced interval data form the maximal-run decomposition of their
union. -/
def zeroRunDecomposition (hk0 : 0 < k) (hk : k < n) :
    ZeroRunDecomposition (F.zeroSet hk) r where
  left := F.reducedLeft hk
  right := F.reducedRight hk
  left_le_right := F.reducedLeft_le_reducedRight hk
  mem_iff := F.mem_zeroSet_iff hk
  separated := F.reduced_separated hk0 hk
  captures_interval := by
    intro u v huv hinterval
    have huZ := hinterval u le_rfl huv
    have hvZ := hinterval v huv le_rfl
    obtain ⟨a, haL, haR⟩ := (F.mem_zeroSet_iff hk u).1 huZ
    obtain ⟨b, hbL, hbR⟩ := (F.mem_zeroSet_iff hk v).1 hvZ
    have hab_le : a ≤ b := by
      by_contra hnot
      have hba : b < a := lt_of_not_ge hnot
      have hsep := F.reduced_separated hk0 hk hba
      have huvval := Fin.le_iff_val_le_val.mp huv
      have haLval := Fin.le_iff_val_le_val.mp haL
      have hbRval := Fin.le_iff_val_le_val.mp hbR
      omega
    rcases hab_le.eq_or_lt with rfl | hab
    · exact ⟨a, haL, hbR⟩
    · have hsep := F.reduced_separated hk0 hk hab
      let gap : Fin (n - k) := ⟨(F.reducedRight hk a).val + 1, by
        have hleftLt := (F.reducedLeft hk b).isLt
        omega⟩
      have hugap : u ≤ gap := by
        simp only [Fin.le_iff_val_le_val, gap]
        have haRval := Fin.le_iff_val_le_val.mp haR
        omega
      have hgapv : gap ≤ v := by
        simp only [Fin.le_iff_val_le_val, gap]
        have hbLval := Fin.le_iff_val_le_val.mp hbL
        omega
      have hgapZ := hinterval gap hugap hgapv
      obtain ⟨c, hcL, hcR⟩ := (F.mem_zeroSet_iff hk gap).1 hgapZ
      rcases lt_trichotomy c a with hca | rfl | hac
      · have hcsep := F.reduced_separated hk0 hk hca
        have hcRval := Fin.le_iff_val_le_val.mp hcR
        omega
      · have hcRval := Fin.le_iff_val_le_val.mp hcR
        dsimp only [gap] at hcRval
        omega
      · have hacases : c < b ∨ c = b ∨ b < c := lt_trichotomy c b
        rcases hacases with hcb | rfl | hbc
        · have hasep := F.reduced_separated hk0 hk hac
          have hcLval := Fin.le_iff_val_le_val.mp hcL
          dsimp only [gap] at hcLval
          omega
        · have hcLval := Fin.le_iff_val_le_val.mp hcL
          dsimp only [gap] at hcLval
          omega
        · have hbsep := F.reduced_separated hk0 hk hbc
          have hbRval := Fin.le_iff_val_le_val.mp hbR
          have hcLval := Fin.le_iff_val_le_val.mp hcL
          omega

/-- Enlarging a reduced run by `k` recovers the original interval. -/
theorem runHyperplane_zeroRunDecomposition (hk0 : 0 < k) (hk : k < n) (a : Fin r) :
    runHyperplane hk (F.zeroRunDecomposition hk0 hk) a =
      Finset.Icc (F.left a) (F.right a) := by
  ext x
  simp only [runHyperplane, Finset.mem_Icc, runLeftColumn, runRightColumn,
    zeroRunDecomposition, reducedLeft, reducedRight, Fin.le_iff_val_le_val]
  have hlong := F.long a
  omega

/-- The union of reduced intervals is proper whenever every original interval
is proper. -/
theorem zeroSet_ne_univ (hk0 : 0 < k) (hk : k < n) : F.zeroSet hk ≠ Finset.univ := by
  intro hzero
  let D := F.zeroRunDecomposition hk0 hk
  have hall : ∀ t : Fin (n - k), t ∈ F.zeroSet hk := by
    intro t
    rw [hzero]
    simp
  let first : Fin (n - k) := ⟨0, by omega⟩
  let last : Fin (n - k) := ⟨n - k - 1, by omega⟩
  have hfirstLast : first ≤ last := by
    simp only [Fin.le_iff_val_le_val, first, last]
    omega
  obtain ⟨a, haL, haR⟩ := D.captures_interval hfirstLast (by
    intro t _ _
    exact hall t)
  apply F.proper a
  ext x
  simp only [Finset.mem_Icc, Finset.mem_univ, iff_true]
  change F.reducedLeft hk a ≤ first at haL
  change last ≤ F.reducedRight hk a at haR
  simp only [reducedLeft, reducedRight, Fin.le_iff_val_le_val] at haL haR
  dsimp only [first] at haL
  dsimp only [last] at haR
  have hlong := F.long a
  have hx := x.isLt
  constructor <;> omega

/-- An anchor interval is contained in the reduced zero set exactly when all
selected columns lie in one original interval. -/
theorem allAnchors_mem_zeroSet_iff_exists_columns_mem_interval
    (hk0 : 0 < k) (hk : k < n) (J : Fin (k + 1) ↪o Fin n) :
    (∀ t, IsAnchor J t → t ∈ F.zeroSet hk) ↔
      ∃ a, ∀ i, J i ∈ Finset.Icc (F.left a) (F.right a) := by
  have hrun := allAnchors_mem_iff_exists_columns_mem_runHyperplane hk
    (F.zeroRunDecomposition hk0 hk) J
  rw [hrun]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun i ↦ ?_⟩
    rw [← F.runHyperplane_zeroRunDecomposition hk0 hk a]
    exact ha i
  · rintro ⟨a, ha⟩
    refine ⟨a, fun i ↦ ?_⟩
    rw [F.runHyperplane_zeroRunDecomposition hk0 hk a]
    exact ha i

/-- **Theorem 1, `(iii) -> (ii)` support rule.** A maximal selection is a
basis exactly when its anchor interval is not contained in the reduced zero
set, equivalently when it is not contained in any interval hyperplane. -/
theorem basisRule_zeroSet_iff_not_columns_mem_interval
    (hk0 : 0 < k) (hk : k < n) (J : Fin (k + 1) ↪o Fin n) :
    (∃ t ∈ anchorFinset J, t ∉ F.zeroSet hk) ↔
      ¬∃ a, ∀ i, J i ∈ Finset.Icc (F.left a) (F.right a) := by
  rw [← not_congr (F.allAnchors_mem_zeroSet_iff_exists_columns_mem_interval
    hk0 hk J)]
  push Not
  constructor
  · rintro ⟨t, ht, htz⟩
    refine ⟨t, ?_, htz⟩
    simpa [anchorFinset] using ht
  · rintro ⟨t, ht, htz⟩
    refine ⟨t, ?_, htz⟩
    simp [anchorFinset, ht]

end IntervalHyperplaneFamily

namespace ZeroRunDecomposition

/-- The enlarged intervals of a proper zero-run decomposition form exactly
an interval-hyperplane family satisfying the intersection bound in Theorem 1. -/
def toIntervalHyperplaneFamily
    {k n r : ℕ} {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition Z r) (hk0 : 0 < k) (hk : k < n)
    (hZ : Z ≠ Finset.univ) : IntervalHyperplaneFamily k n r where
  left := runLeftColumn D
  right := runRightColumn hk D
  left_le_right := by
    intro a
    simp only [runLeftColumn, runRightColumn, Fin.le_iff_val_le_val]
    have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
    omega
  long := by
    intro a
    simp only [runLeftColumn, runRightColumn]
    have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
    omega
  left_strictMono := by
    intro a b hab
    simp only [runLeftColumn, Fin.lt_def]
    have hsep := D.separated hab
    have hlr := Fin.le_iff_val_le_val.mp (D.left_le_right a)
    omega
  proper := by
    intro a ha
    apply hZ
    ext t
    simp only [Finset.mem_univ, iff_true]
    apply (D.mem_iff t).2
    let first : Fin n := ⟨0, by omega⟩
    let last : Fin n := ⟨n - 1, by omega⟩
    have hfirst : first ∈ Finset.Icc (runLeftColumn D a) (runRightColumn hk D a) := by
      rw [ha]
      simp
    have hlast : last ∈ Finset.Icc (runLeftColumn D a) (runRightColumn hk D a) := by
      rw [ha]
      simp
    simp only [Finset.mem_Icc, runLeftColumn, runRightColumn,
      Fin.le_iff_val_le_val] at hfirst hlast
    dsimp only [first] at hfirst
    dsimp only [last] at hlast
    refine ⟨a, ?_, ?_⟩
    · omega
    · have ht := t.isLt
      omega
  inter_card_le := by
    intro a b hab
    exact card_runHyperplane_inter_le hk D hab

@[simp]
theorem toIntervalHyperplaneFamily_interval
    {k n r : ℕ} {Z : Finset (Fin (n - k))}
    (D : ZeroRunDecomposition Z r) (hk0 : 0 < k) (hk : k < n)
    (hZ : Z ≠ Finset.univ) (a : Fin r) :
    Finset.Icc ((D.toIntervalHyperplaneFamily hk0 hk hZ).left a)
        ((D.toIntervalHyperplaneFamily hk0 hk hZ).right a) =
      runHyperplane hk D a := rfl

end ZeroRunDecomposition

end

end PavingToeplitzPositroids
