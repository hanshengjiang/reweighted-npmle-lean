import ReweightedNPMLE.GaussianMainTheorem
import Mathlib.Tactic

/-! # The displayed uniform near-MLE theorem

One positive constant controls the failure probability and the literal
logarithmic Hellinger rate, uniformly over all true and candidate laws.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

theorem gaussian_uniform_nearMLE_paper_theorem
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ E : Set (Fin n → Point d), MeasurableSet E ∧
        (compactGaussianSampleMeasure Gstar n).real Eᶜ ≤ C * (n : ℝ) ^ (-b) ∧
        ∀ x ∈ E, ∀ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) →
          hellingerSq volume (compactGaussianMixtureDensity G) (compactGaussianMixtureDensity Gstar) ≤
            C * Real.log (n : ℝ) ^ (d + 1) /
              ((n : ℝ) * Real.log (Real.log (n : ℝ)) ^ d) := by
  let R := gaussianPaperRateConstant d b
  let F := 2 * (d : ℝ) + 1
  let C := 1 + R + F
  have hR : 0 ≤ R := by dsimp [R, gaussianPaperRateConstant, gaussianPaperEntropyConstant]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hRC : R ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [compactGaussianMixture_measurable_uniform_nearMLE_event hd K hKcompact hKnonempty
      hS hb.le hKbound, eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with n hn hs hl hnOne
  intro Gstar
  obtain ⟨N, hN, hfail, hgood⟩ := hn Gstar
  refine ⟨Nᶜ, hN.compl, ?_, ?_⟩
  · rw [compl_compl]
    have hp : (n : ℝ) ^ (-(b + 2)) ≤ (n : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnOne) (by linarith)
    exact hfail.trans (mul_le_mul hFC hp (Real.rpow_nonneg (Nat.cast_nonneg _) _) hC.le)
  · intro x hx G hnear
    have hg : hellingerSq volume (compactGaussianMixtureDensity G) (compactGaussianMixtureDensity Gstar) ≤
        R * gaussianPaperRiskScale d n := by
      simpa only [R, gaussianPaperRiskScale, mul_div_assoc, mul_assoc] using hgood x hx G hnear
    have hscale : 0 ≤ gaussianPaperRiskScale d n := by
      unfold gaussianPaperRiskScale
      exact div_nonneg (mul_nonneg (pow_nonneg hs.1 d) hl) (Nat.cast_nonneg _)
    have hbound := hg.trans (mul_le_mul_of_nonneg_right hRC hscale)
    rwa [gaussianPaperRiskScale_eq, ← mul_div_assoc] at hbound

end ReweightedNPMLE
