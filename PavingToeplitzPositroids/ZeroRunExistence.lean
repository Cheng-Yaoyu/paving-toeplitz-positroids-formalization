import PavingToeplitzPositroids.IntervalSupport
import Mathlib.Data.Finset.Max

/-!
# Existence of maximal consecutive zero-run decompositions

This file proves the elementary finite decomposition used in Section 5. The
proof removes the first maximal consecutive run and applies strong induction
to the strictly smaller remaining zero set.
-/

namespace PavingToeplitzPositroids

open Set

noncomputable section

/-- Candidate right endpoints for the initial run beginning at the least
element `u` of `Z`. -/
def initialRunEnds {N : ℕ} (Z : Finset (Fin N)) (u : Fin N) : Finset (Fin N) :=
  Z.filter fun v ↦ u ≤ v ∧ ∀ t ∈ Finset.Icc u v, t ∈ Z

/-- Every finite zero set admits a decomposition into separated maximal
consecutive runs. -/
theorem exists_zeroRunDecomposition {N : ℕ} (Z : Finset (Fin N)) :
    ∃ r, Nonempty (ZeroRunDecomposition Z r) := by
  classical
  induction hcard : Z.card using Nat.strong_induction_on generalizing Z with
  | h card ih =>
      by_cases hZ : Z.Nonempty
      · let u : Fin N := Z.min' hZ
        have huZ : u ∈ Z := Z.min'_mem hZ
        have hu_min : ∀ t ∈ Z, u ≤ t := fun t ht ↦ Z.min'_le t ht
        let E := initialRunEnds Z u
        have huE : u ∈ E := by
          simp only [E, initialRunEnds, Finset.mem_filter]
          refine ⟨huZ, le_rfl, ?_⟩
          intro t ht
          have htu := Finset.mem_Icc.mp ht
          have : t = u := le_antisymm htu.2 htu.1
          simpa [this] using huZ
        have hE : E.Nonempty := ⟨u, huE⟩
        let v : Fin N := E.max' hE
        have hvE : v ∈ E := E.max'_mem hE
        have huv : u ≤ v := (Finset.mem_filter.mp hvE).2.1
        have huvZ : ∀ t, u ≤ t → t ≤ v → t ∈ Z := by
          intro t hut htv
          exact (Finset.mem_filter.mp hvE).2.2 t (Finset.mem_Icc.mpr ⟨hut, htv⟩)
        have hgap : ∀ t ∈ Z, v < t → v.val + 1 < t.val := by
          intro t htZ hvt
          by_contra hnot
          have htval : t.val = v.val + 1 := by
            have hval := Fin.lt_def.mp hvt
            omega
          have htE : t ∈ E := by
            simp only [E, initialRunEnds, Finset.mem_filter]
            refine ⟨htZ, huv.trans hvt.le, ?_⟩
            intro x hx
            have hux := (Finset.mem_Icc.mp hx).1
            have hxt := (Finset.mem_Icc.mp hx).2
            by_cases hxv : x ≤ v
            · exact huvZ x hux hxv
            · have hxval : x.val = t.val := by
                have hvx : v < x := lt_of_not_ge hxv
                have hvxval := Fin.lt_def.mp hvx
                have hxtval := Fin.le_iff_val_le_val.mp hxt
                omega
              have hxtEq : x = t := Fin.ext hxval
              simpa [hxtEq] using htZ
          have htv : t ≤ v := E.le_max' t htE
          exact (not_le_of_gt hvt) htv
        let Z' : Finset (Fin N) := Z.filter fun t ↦ v.val + 1 < t.val
        have hZ'sub : Z' ⊆ Z := by
          exact Finset.filter_subset _ _
        have hu_not_Z' : u ∉ Z' := by
          simp only [Z', Finset.mem_filter, not_and_or]
          exact Or.inr (by
            simp only [not_lt]
            exact Nat.le_add_right_of_le (Fin.le_iff_val_le_val.mp huv))
        have hZ'proper : Z' ⊂ Z := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hZ'sub, ?_⟩
          intro heq
          apply hu_not_Z'
          rw [heq]
          exact huZ
        have hZ'card : Z'.card < card := by
          rw [← hcard]
          exact Finset.card_lt_card hZ'proper
        obtain ⟨r, ⟨D⟩⟩ := ih Z'.card hZ'card Z' rfl
        let left : Fin (r + 1) → Fin N := Fin.cases u D.left
        let right : Fin (r + 1) → Fin N := Fin.cases v D.right
        refine ⟨r + 1, ⟨{
          left := left
          right := right
          left_le_right := ?_
          mem_iff := ?_
          separated := ?_
          captures_interval := ?_ }⟩⟩
        · intro a
          refine Fin.cases huv (fun i ↦ ?_) a
          exact D.left_le_right i
        · intro t
          constructor
          · intro htZ
            by_cases htv : t ≤ v
            · exact ⟨0, hu_min t htZ, htv⟩
            · have hvt : v < t := lt_of_not_ge htv
              have htZ' : t ∈ Z' := by
                exact Finset.mem_filter.mpr ⟨htZ, hgap t htZ hvt⟩
              obtain ⟨a, ha⟩ := (D.mem_iff t).1 htZ'
              exact ⟨a.succ, ha⟩
          · rintro ⟨a, ha⟩
            revert ha
            refine Fin.cases ?_ (fun i ↦ ?_) a
            · intro ha
              change u ≤ t ∧ t ≤ v at ha
              exact huvZ t ha.1 ha.2
            · intro ha
              change D.left i ≤ t ∧ t ≤ D.right i at ha
              exact hZ'sub ((D.mem_iff t).2 ⟨i, ha⟩)
        · intro a b hab
          cases a using Fin.cases with
          | zero =>
              cases b using Fin.cases with
              | zero => exact (lt_irrefl 0 hab).elim
              | succ j =>
                  have hleftZ' : D.left j ∈ Z' :=
                    (D.mem_iff (D.left j)).2
                      ⟨j, le_rfl, D.left_le_right j⟩
                  exact (Finset.mem_filter.mp hleftZ').2
          | succ i =>
              cases b using Fin.cases with
              | zero => exact (not_lt_of_ge (Fin.zero_le _) hab).elim
              | succ j =>
                  apply D.separated
                  exact Fin.succ_lt_succ_iff.mp hab
        · intro x y hxy hinterval
          have hxZ : x ∈ Z := hinterval x le_rfl hxy
          by_cases hxv : x ≤ v
          · have huy : y ≤ v := by
              by_contra hyv
              have hvy : v < y := lt_of_not_ge hyv
              let w : Fin N := ⟨v.val + 1, by
                have hylt := y.isLt
                have hvyval := Fin.lt_def.mp hvy
                omega⟩
              have hxw : x ≤ w := by
                simp only [Fin.le_iff_val_le_val, w]
                have hxvval := Fin.le_iff_val_le_val.mp hxv
                omega
              have hwy : w ≤ y := by
                simp only [Fin.le_iff_val_le_val, w]
                have hvyval := Fin.lt_def.mp hvy
                omega
              have hwZ : w ∈ Z := hinterval w hxw hwy
              have hvw : v < w := by
                simp only [Fin.lt_def, w]
                omega
              have := hgap w hwZ hvw
              dsimp only [w] at this
              omega
            exact ⟨0, hu_min x hxZ, huy⟩
          · have hvx : v < x := lt_of_not_ge hxv
            have hxgap := hgap x hxZ hvx
            have hsubinterval : ∀ t, x ≤ t → t ≤ y → t ∈ Z' := by
              intro t hxt hty
              have htZ := hinterval t hxt hty
              apply Finset.mem_filter.mpr
              refine ⟨htZ, ?_⟩
              have hxtval := Fin.le_iff_val_le_val.mp hxt
              omega
            obtain ⟨a, ha⟩ := D.captures_interval hxy hsubinterval
            exact ⟨a.succ, ha⟩
      · have hZempty : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZ
        subst Z
        refine ⟨0, ⟨{
          left := Fin.elim0
          right := Fin.elim0
          left_le_right := fun a ↦ Fin.elim0 a
          mem_iff := fun t ↦ by simp
          separated := by intro a; exact Fin.elim0 a
          captures_interval := by
            intro u v huv hinterval
            exfalso
            simpa using hinterval u le_rfl huv }⟩⟩

/-- Two runs in one separated decomposition that overlap must be the same
run. -/
theorem ZeroRunDecomposition.eq_of_overlap
    {N r : ℕ} {Z : Finset (Fin N)} (D : ZeroRunDecomposition Z r)
    {a b : Fin r} (hab₁ : D.left a ≤ D.right b)
    (hab₂ : D.left b ≤ D.right a) :
    a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hsep := D.separated hlt
    have hle := Fin.le_iff_val_le_val.mp hab₂
    omega
  · have hsep := D.separated hgt
    have hle := Fin.le_iff_val_le_val.mp hab₁
    omega

/-- Every run in one decomposition agrees endpoint-for-endpoint with a run in
any other decomposition of the same zero set. -/
theorem ZeroRunDecomposition.exists_matching_run
    {N r s : ℕ} {Z : Finset (Fin N)}
    (D : ZeroRunDecomposition Z r) (E : ZeroRunDecomposition Z s)
    (a : Fin r) :
    ∃ b : Fin s, E.left b = D.left a ∧ E.right b = D.right a := by
  have hDZ : ∀ t, D.left a ≤ t → t ≤ D.right a → t ∈ Z := by
    intro t hlt htr
    exact (D.mem_iff t).2 ⟨a, hlt, htr⟩
  obtain ⟨b, hbL, hbR⟩ := E.captures_interval (D.left_le_right a) hDZ
  have hEZ : ∀ t, E.left b ≤ t → t ≤ E.right b → t ∈ Z := by
    intro t hlt htr
    exact (E.mem_iff t).2 ⟨b, hlt, htr⟩
  obtain ⟨c, hcL, hcR⟩ := D.captures_interval (E.left_le_right b) hEZ
  have hca : c = a := D.eq_of_overlap
    (hcL.trans (hbL.trans (D.left_le_right a)))
    ((D.left_le_right a).trans (hbR.trans hcR))
  subst c
  exact ⟨b, le_antisymm hbL hcL, le_antisymm hcR hbR⟩

/-- Maximal zero-run decompositions are unique up to the unique endpoint-
preserving equivalence of their finite index types. -/
theorem zeroRunDecomposition_unique
    {N r s : ℕ} {Z : Finset (Fin N)}
    (D : ZeroRunDecomposition Z r) (E : ZeroRunDecomposition Z s) :
    ∃ e : Fin r ≃ Fin s, ∀ a,
      E.left (e a) = D.left a ∧ E.right (e a) = D.right a := by
  let f : Fin r → Fin s := fun a ↦
    Classical.choose (D.exists_matching_run E a)
  have hf : ∀ a, E.left (f a) = D.left a ∧
      E.right (f a) = D.right a := fun a ↦
    Classical.choose_spec (D.exists_matching_run E a)
  have hinj : Function.Injective f := by
    intro a b hab
    apply D.eq_of_overlap
    · rw [← (hf a).1, ← (hf b).2, hab]
      exact E.left_le_right (f b)
    · rw [← (hf b).1, ← (hf a).2, hab]
      exact E.left_le_right (f b)
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, haL, haR⟩ := E.exists_matching_run D b
    refine ⟨a, ?_⟩
    apply E.eq_of_overlap
    · calc
        E.left (f a) = D.left a := (hf a).1
        _ ≤ D.right a := D.left_le_right a
        _ = E.right b := haR
    · calc
        E.left b = D.left a := haL.symm
        _ ≤ D.right a := D.left_le_right a
        _ = E.right (f a) := (hf a).2.symm
  let e : Fin r ≃ Fin s := Equiv.ofBijective f ⟨hinj, hsurj⟩
  exact ⟨e, fun a ↦ hf a⟩

end

end PavingToeplitzPositroids
