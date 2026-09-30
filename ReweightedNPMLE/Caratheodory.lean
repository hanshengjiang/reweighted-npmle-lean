import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Real.Basic

/-!
# Finite convex representations

The fitted-vector compactness argument and the likelihood-net moment matching
step both use the finite-dimensional Carathéodory theorem.  This file records
the cardinality form needed by the paper.
-/

open Set

namespace ReweightedNPMLE

/-- Every point in a finite-dimensional convex hull uses at most `finrank + 1` atoms. -/
theorem exists_finite_convex_representation
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (s : Set E) {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have hsub : (t : Set E) ⊆ s :=
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hmem : x ∈ convexHull ℝ (t : Set E) :=
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have hind : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hcard₁ : t.card ≤
      Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 := by
    simpa using hind.card_le_finrank_succ
  have hcard₂ : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 ≤
      Module.finrank ℝ E + 1 := Nat.add_le_add_right
        (Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))) 1
  exact ⟨t, hsub, hcard₁.trans hcard₂, hmem⟩

/-- Specialization to moment vectors indexed by `Fin k`. -/
theorem exists_finite_convex_representation_fin {k : ℕ}
    (s : Set (Fin k → ℝ)) {x : Fin k → ℝ} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset (Fin k → ℝ), (t : Set (Fin k → ℝ)) ⊆ s ∧
      t.card ≤ k + 1 ∧ x ∈ convexHull ℝ (t : Set (Fin k → ℝ)) := by
  simpa [Module.finrank_fin_fun] using exists_finite_convex_representation s hx

end ReweightedNPMLE
