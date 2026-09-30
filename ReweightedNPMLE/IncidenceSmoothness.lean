import ReweightedNPMLE.AnalyticIncidence
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

/-!
# Joint smoothness of observation derivatives

Differentiating only in the observation variable preserves joint smoothness
in parameters and observations. Evaluation of the resulting multilinear
derivative on a fixed basis word is also jointly smooth.
-/

open Set Filter
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem contDiff_iteratedFDeriv_with_parameter
    {E Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : E → Y → Z) (hf : ContDiff ℝ ⊤ (Function.uncurry F)) (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : E × Y ↦ iteratedFDeriv ℝ m (F p.1) p.2) := by
  induction m with
  | zero =>
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ Y Z).symm : Z →L[ℝ] Y [×0]→L[ℝ] Z)
  | succ m ih =>
    have hg : ContDiff ℝ ⊤ (Function.uncurry
        (fun p : E × Y ↦ fun y : Y ↦ iteratedFDeriv ℝ m (F p.1) y)) :=
      ih.comp (show ContDiff ℝ ⊤ (fun q : (E × Y) × Y ↦ (q.1.1, q.2)) by fun_prop)
    have hd : ContDiff ℝ ⊤ (fun p : E × Y ↦
        fderiv ℝ (fun y ↦ iteratedFDeriv ℝ m (F p.1) y) p.2) :=
      hg.fderiv contDiff_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ Y) Z).symm :
        (Y →L[ℝ] Y [×m]→L[ℝ] Z) →L[ℝ] Y [×(m + 1)]→L[ℝ] Z)

theorem contDiff_iteratedFDeriv_word_with_parameter
    {E Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : E → Y → Z) (hf : ContDiff ℝ ⊤ (Function.uncurry F))
    (m : ℕ) (u : Fin m → Y) :
    ContDiff ℝ ⊤ (fun p : E × Y ↦ iteratedFDeriv ℝ m (F p.1) p.2 u) :=
  (contDiff_iteratedFDeriv_with_parameter F hf m).continuousLinearMap_comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ Y) Z u)

end ReweightedNPMLE
