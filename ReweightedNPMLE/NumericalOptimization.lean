import ReweightedNPMLE.LikelihoodGap
import Mathlib.Tactic

/-!
# Transfer from numerical near-optimality to statistical accuracy

This file formalizes the deterministic final step in Corollary 5.2.  Once the
effective-dimension argument has bounded the ordinary likelihood loss of an
attainable numerical fit, ordinary optimality compares that fit with the true
mixing law.  The uniform near-MLE theorem can then be applied without making a
particular choice of ordinary maximizer.
-/

namespace ReweightedNPMLE

/-- An ordinary likelihood loss of at most `ε` implies likelihood within `ε`
of every feasible comparison point, in particular the true fitted vector. -/
theorem near_comparison_of_ordinary_gap_le {n : ℕ}
    {C : Set (Fin n → ℝ)} {v₀ vstar v : Fin n → ℝ} {ε : ℝ}
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hvstar : vstar ∈ C)
    (hgap : weightedLogLikelihood (oneWeights n) v₀ -
      weightedLogLikelihood (oneWeights n) v ≤ ε) :
    weightedLogLikelihood (oneWeights n) vstar - ε ≤
      weightedLogLikelihood (oneWeights n) v := by
  have hstar_le : weightedLogLikelihood (oneWeights n) vstar ≤
      weightedLogLikelihood (oneWeights n) v₀ := hv₀.2 vstar hvstar
  linarith

/-- Unit ordinary loss places a feasible numerical fit in the simultaneous
near-MLE class controlled by the paper's uniform testing event. -/
theorem uniform_nearMLE_transfer_of_ordinary_gap_le_one {n : ℕ}
    {C : Set (Fin n → ℝ)} {v₀ vstar v : Fin n → ℝ}
    (risk : (Fin n → ℝ) → ℝ) {riskBound : ℝ}
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hvstar : vstar ∈ C) (hv : v ∈ C)
    (hgap : weightedLogLikelihood (oneWeights n) v₀ -
      weightedLogLikelihood (oneWeights n) v ≤ 1)
    (huniform : ∀ u ∈ C,
      weightedLogLikelihood (oneWeights n) vstar - 1 ≤
        weightedLogLikelihood (oneWeights n) u → risk u ≤ riskBound) :
    risk v ≤ riskBound := by
  exact huniform v hv (near_comparison_of_ordinary_gap_le hv₀ hvstar hgap)

/--
Abstract, exact form of the numerical-optimization corollary.  The structural
event supplies both displayed deterministic bounds.  If its likelihood bound
is at most one, the same event also transfers the uniform near-MLE risk bound
to the numerical fit.  No sparsity conclusion is inferred for an approximate
optimizer.
-/
theorem numerical_optimization_corollary {n : ℕ}
    {C : Set (Fin n → ℝ)} {v₀ vstar v : Fin n → ℝ}
    (risk logRatioSq : (Fin n → ℝ) → ℝ) {B riskBound : ℝ}
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hvstar : vstar ∈ C) (hv : v ∈ C)
    (hB : B ≤ 1)
    (hlikelihood : weightedLogLikelihood (oneWeights n) v₀ -
      weightedLogLikelihood (oneWeights n) v ≤ B)
    (hlogRatio : logRatioSq v ≤ B)
    (huniform : ∀ u ∈ C,
      weightedLogLikelihood (oneWeights n) vstar - 1 ≤
        weightedLogLikelihood (oneWeights n) u → risk u ≤ riskBound) :
    0 ≤ weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v ∧
      weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v ≤ B ∧
      logRatioSq v ≤ B ∧ risk v ≤ riskBound := by
  refine ⟨ordinary_likelihood_gap_nonneg hv₀ hv, hlikelihood, hlogRatio, ?_⟩
  exact uniform_nearMLE_transfer_of_ordinary_gap_le_one risk hv₀ hvstar hv
    (hlikelihood.trans hB) huniform

end ReweightedNPMLE
