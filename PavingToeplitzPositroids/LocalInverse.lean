import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity
import ToeplitzPositroids.Matrix.Basic

/-!
# Uniform local targets from the inverse function theorem

This is the analytic core used in Theorems 15 and 19. It strengthens a local
inverse to a uniform nonnegative coordinate box, exactly matching the target
vectors of consecutive minors used in the paper.
-/

namespace PavingToeplitzPositroids

open Filter Set Topology
open ToeplitzPositroids

noncomputable section

/-- An invertible strict derivative makes every sufficiently small
nonnegative coordinate vector locally realizable, while keeping the preimage
inside any prescribed source neighborhood. -/
theorem exists_local_preimage_nonnegative_box
    {N : ℕ} {f : (Fin N → ℝ) → (Fin N → ℝ)}
    {f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)} {a : Fin N → ℝ}
    (hf : HasStrictFDerivAt f f'.toContinuousLinearMap a)
    {U : Set (Fin N → ℝ)} (hU : U ∈ 𝓝 a) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin N → ℝ,
        (∀ i, 0 ≤ delta i ∧ delta i < eta) →
          ∃ x ∈ U, f x = f a + delta := by
  let g : (Fin N → ℝ) → (Fin N → ℝ) := hf.localInverse f f' a
  have hsource : ∀ᶠ y in 𝓝 (f a), g y ∈ U :=
    hf.localInverse_tendsto.eventually hU
  have hright : ∀ᶠ y in 𝓝 (f a), f (g y) = y :=
    hf.eventually_right_inverse
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp (hsource.and hright)
  refine ⟨eta, heta, fun delta hdelta ↦ ?_⟩
  have hnorm : ‖delta‖ < eta := by
    apply (pi_norm_lt_iff heta).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hdelta i).1]
    exact (hdelta i).2
  have hy : f a + delta ∈ Metric.ball (f a) eta := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hnorm
  have hgood := hball hy
  exact ⟨g (f a + delta), hgood.1, hgood.2⟩

/-- The form used at a base point whose target vector is zero. -/
theorem exists_local_preimage_nonnegative_box_zero
    {N : ℕ} {f : (Fin N → ℝ) → (Fin N → ℝ)}
    {f' : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)} {a : Fin N → ℝ}
    (hf : HasStrictFDerivAt f f'.toContinuousLinearMap a)
    (hfa : f a = 0) {U : Set (Fin N → ℝ)} (hU : U ∈ 𝓝 a) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ delta : Fin N → ℝ,
        (∀ i, 0 ≤ delta i ∧ delta i < eta) →
          ∃ x ∈ U, f x = delta := by
  obtain ⟨eta, heta, hbox⟩ := exists_local_preimage_nonnegative_box hf hU
  refine ⟨eta, heta, fun delta hdelta ↦ ?_⟩
  obtain ⟨x, hx, hfx⟩ := hbox delta hdelta
  exact ⟨x, hx, by simpa [hfa] using hfx⟩

/-- The source points at which every minor through order `p` is positive. The
minor order is indexed by `Fin (p+1)`, so the definition is manifestly a
finite intersection. -/
def strictLowerMinorSet {E : Type*} (p rows cols : ℕ)
    (A : E → Matrix (Fin rows) (Fin cols) ℝ) : Set E :=
  {x | ∀ r : Fin (p + 1),
    ∀ (I : Fin r.val ↪o Fin rows) (J : Fin r.val ↪o Fin cols),
      0 < orderedMinor (A x) I J}

/-- Strict positivity of finitely many minors is an open condition. -/
theorem isOpen_strictLowerMinorSet
    {E : Type*} [TopologicalSpace E] {p rows cols : ℕ}
    {A : E → Matrix (Fin rows) (Fin cols) ℝ}
    (hcontinuous : ∀ (r : Fin (p + 1))
      (I : Fin r.val ↪o Fin rows) (J : Fin r.val ↪o Fin cols),
        Continuous (fun x ↦ orderedMinor (A x) I J)) :
    IsOpen (strictLowerMinorSet p rows cols A) := by
  rw [show strictLowerMinorSet p rows cols A =
      ⋂ r : Fin (p + 1), ⋂ I : Fin r.val ↪o Fin rows,
        ⋂ J : Fin r.val ↪o Fin cols,
          {x | 0 < orderedMinor (A x) I J} by
    ext x
    simp [strictLowerMinorSet]]
  apply isOpen_iInter_of_finite
  intro r
  apply isOpen_iInter_of_finite
  intro I
  apply isOpen_iInter_of_finite
  intro J
  exact isOpen_lt continuous_const (hcontinuous r I J)

/-- A base point with strictly positive lower minors has a neighborhood on
which all those inequalities persist. -/
theorem strictLowerMinorSet_mem_nhds
    {E : Type*} [TopologicalSpace E] {p rows cols : ℕ}
    {A : E → Matrix (Fin rows) (Fin cols) ℝ}
    (hcontinuous : ∀ (r : Fin (p + 1))
      (I : Fin r.val ↪o Fin rows) (J : Fin r.val ↪o Fin cols),
        Continuous (fun x ↦ orderedMinor (A x) I J))
    {a : E} (ha : a ∈ strictLowerMinorSet p rows cols A) :
    strictLowerMinorSet p rows cols A ∈ 𝓝 a :=
  (isOpen_strictLowerMinorSet hcontinuous).mem_nhds ha

end

end PavingToeplitzPositroids
