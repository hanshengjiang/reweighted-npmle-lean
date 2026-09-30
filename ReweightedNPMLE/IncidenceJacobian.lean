import ReweightedNPMLE.IncidenceSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
# Full row rank of separated incidence equations

Each scalar equation depends on the common parameter and one observation row.
Nonzero selected observation derivatives give an explicit right inverse for
the full incidence derivative, without constraining the parameter derivative.
-/

open Set Filter
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def incidenceRowProjection {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ} (i : Fin n) :
    (E × (Fin n → Y)) →L[ℝ] E × Y :=
  (ContinuousLinearMap.fst ℝ E (Fin n → Y)).prod
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ E (Fin n → Y)))

noncomputable def incidenceEquations {E Y : Type*} {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y)) : Fin n → ℝ :=
  fun i ↦ H i p.1 (p.2 i)

noncomputable def incidenceDerivative {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y)) :
    (E × (Fin n → Y)) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦
    (fderiv ℝ (Function.uncurry (H i)) (p.1, p.2 i)).comp (incidenceRowProjection i))

theorem hasFDerivAt_incidenceEquations {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y))
    (hH : ∀ i, DifferentiableAt ℝ (Function.uncurry (H i)) (p.1, p.2 i)) :
    HasFDerivAt (incidenceEquations H) (incidenceDerivative H p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hH i).hasFDerivAt.comp p (incidenceRowProjection i).hasFDerivAt

theorem contDiff_incidenceEquations_of_joint {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ)
    (hH : ∀ i, ContDiff ℝ ⊤ (Function.uncurry (H i))) :
    ContDiff ℝ ⊤ (incidenceEquations H) := by
  apply contDiff_pi.mpr
  intro i
  exact (hH i).comp (incidenceRowProjection i).contDiff

theorem fderiv_uncurry_observation_apply {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (H : E → Y → ℝ) (η : E) (y u : Y)
    (hH : DifferentiableAt ℝ (Function.uncurry H) (η, y)) :
    fderiv ℝ (Function.uncurry H) (η, y) (0, u) = fderiv ℝ (H η) y u := by
  have hp := hH.hasFDerivAt.comp y
    ((hasFDerivAt_const η y).prodMk (hasFDerivAt_id y))
  have hh := congrArg (fun L : Y →L[ℝ] ℝ ↦ L u) hp.fderiv
  simpa using hh.symm

theorem incidenceDerivative_surjective_of_observation_derivatives {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y))
    (hH : ∀ i, DifferentiableAt ℝ (Function.uncurry (H i)) (p.1, p.2 i))
    (u : Fin n → Y) (hu : ∀ i, fderiv ℝ (H i p.1) (p.2 i) (u i) ≠ 0) :
    Function.Surjective (incidenceDerivative H p) := by
  let δ : Fin n → ℝ := fun i ↦ fderiv ℝ (Function.uncurry (H i)) (p.1, p.2 i) (0, u i)
  have hδ : ∀ i, δ i ≠ 0 := by
    intro i
    dsimp only [δ]
    rw [fderiv_uncurry_observation_apply (H i) p.1 (p.2 i) (u i) (hH i)]
    exact hu i
  intro z
  refine ⟨(0, fun i ↦ (z i / δ i) • u i), ?_⟩
  funext i
  change fderiv ℝ (Function.uncurry (H i)) (p.1, p.2 i)
    (0, (z i / δ i) • u i) = z i
  have heq : ((0 : E), (z i / δ i) • u i) = (z i / δ i) • ((0 : E), u i) := by simp
  rw [heq, map_smul]
  change (z i / δ i) * δ i = z i
  exact div_mul_cancel₀ _ (hδ i)

theorem fderiv_incidenceEquations_surjective {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y))
    (hH : ∀ i, DifferentiableAt ℝ (Function.uncurry (H i)) (p.1, p.2 i))
    (u : Fin n → Y) (hu : ∀ i, fderiv ℝ (H i p.1) (p.2 i) (u i) ≠ 0) :
    Function.Surjective (fderiv ℝ (incidenceEquations H) p) := by
  rw [(hasFDerivAt_incidenceEquations H p hH).fderiv]
  exact incidenceDerivative_surjective_of_observation_derivatives H p hH u hu

end ReweightedNPMLE
