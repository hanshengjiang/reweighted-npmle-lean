import ReweightedNPMLE.GaussianMainTheorem
import Mathlib.Tactic

/-! # Dimension refinements in the main theorem

The actual unique mixing-law support has order `log n` in dimension one
and order `(log n / log log n)^d` in every dimension at least two.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace ReweightedNPMLE

noncomputable def gaussianPaperSupportOrder (d n : ℕ) : ℝ :=
  if d = 1 then Real.log n else gaussianPaperEffectiveDimension d n

theorem eventually_gaussianPaperAugmentedDimension_le_twice_supportOrder
    {d : ℕ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      gaussianPaperAugmentedDimension d n ≤ 2 * gaussianPaperSupportOrder d n := by
  by_cases hd1 : d = 1
  · subst d
    simpa only [gaussianPaperSupportOrder, if_pos rfl] using
      eventually_gaussianPaperAugmentedDimension_one_le_twice_log
  · simpa only [gaussianPaperSupportOrder, if_neg hd1] using
      eventually_gaussianPaperAugmentedDimension_le_twice_effective (show 2 ≤ d by omega)

theorem gaussian_main_support_dimension_refinements
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, ∃ μ : ProbabilityMeasure K,
          gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
          (μ : Measure K).support.Finite ∧
          ((μ : Measure K).support.ncard : ℝ) ≤ C * gaussianPaperSupportOrder d n := by
  obtain ⟨C₀, hC₀, hmain⟩ := gaussian_exact_regularization_main hd K hKcompact hKnonempty hS hb hKbound
  refine ⟨2 * C₀, by positivity, ?_⟩
  filter_upwards [hmain, eventually_gaussianPaperAugmentedDimension_le_twice_supportOrder hd]
    with n hn horder
  intro Gstar
  obtain ⟨G, hG, hfail, hgood⟩ := hn Gstar
  refine ⟨G, hG, hfail.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ 2 * C₀)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p hp
    obtain ⟨_, _, μ, hμ, hfin, hcard, _, _⟩ := hgood p hp
    refine ⟨μ, hμ, hfin, hcard.trans ?_⟩
    convert mul_le_mul_of_nonneg_left horder hC₀.le using 1 <;> ring

end ReweightedNPMLE
