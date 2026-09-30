import ReweightedNPMLE.GaussianNearMLERate
import ReweightedNPMLE.ConditionalProductBound
import Mathlib.Tactic

/-!
# Gaussian sample laws and simultaneous genericity

The iid sample law has a density, is a probability law, and satisfies the
uniform paper-radius tail. The constants do not depend on the true compact
mixing law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ReweightedNPMLE

noncomputable def compactGaussianSampleMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : Measure (Fin n → Point d) :=
  Measure.pi (fun _ : Fin n ↦ volume.withDensity
    (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))

theorem compactGaussianMixtureLaw_eq_density {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) :
    gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d)) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)) :=
  gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture _ _ measurable_subtype_coe

instance isProbabilityMeasure_compactGaussianSampleMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) :
    IsProbabilityMeasure (compactGaussianSampleMeasure Gstar n) := by
  letI : IsProbabilityMeasure (volume.withDensity
      (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y))) := by
    rw [← compactGaussianMixtureLaw_eq_density Gstar]
    exact gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  dsimp [compactGaussianSampleMeasure]
  infer_instance

theorem compactGaussianSampleMeasure_absolutelyContinuous {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : compactGaussianSampleMeasure Gstar n ≪ volume := by
  let ν : Measure (Point d) := volume.withDensity
    (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y))
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    rw [← compactGaussianMixtureLaw_eq_density Gstar]
    exact gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  exact absolutelyContinuous_finiteProduct ν volume (withDensity_absolutelyContinuous _ _) n

theorem compactGaussianSampleMeasure_paper_radius_tail {d n : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hKbound : ∀ a ∈ K, ‖a‖ ≤ S) (hlog : 0 < Real.log (n : ℝ)) (hn : 1 ≤ n) :
    (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
  let R := gaussianPaperRadiusExponent b n
  have hR : 0 < R := by dsimp [R, gaussianPaperRadiusExponent]; positivity
  have ht : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by positivity)
  have htail := gaussianLocationMixtureSample_max_radius_tail (n := n) (Gstar : Measure K)
    (fun a : K ↦ (a : Point d)) measurable_subtype_coe
    (fun a ↦ hKbound a.val a.property) ht
  rw [compactGaussianMixtureLaw_eq_density Gstar] at htail
  have htail' : (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        2 * (n : ℝ) * d * Real.exp (-R) := by
    have hsqrt : (Real.sqrt (2 * R)) ^ 2 = 2 * R := Real.sq_sqrt (by positivity)
    change (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        2 * (n : ℝ) * d * Real.exp (-(Real.sqrt (2 * R)) ^ 2 / 2) at htail
    rwa [hsqrt, show -(2 * R) / 2 = -R by ring] at htail
  have hfail := gaussianPaper_failure_bound d n hb hn
  have hterm : 0 ≤ Real.exp (-(b + 2) * Real.log (n : ℝ) - 1) := (Real.exp_pos _).le
  exact htail'.trans (by linarith)

end ReweightedNPMLE
