/-
NEGATIVE CONTROL: intentionally changes the statistical risk definition by
a factor of two. Comparator must reject this challenge against the normal
solution, even though the theorem declaration still has identical surface syntax.
This file is not a statement of the paper and is never a production import.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Data.Set.Card

/-!
Trusted statement for the Comparator audit of paper.tex, thm:main.

This module imports only Mathlib. The 24 project definitions below are explicitly
redeclared so the challenge fixes their meanings independently of the solution's
imports. Their original qualified names and bodies are preserved for Comparator's
recursive declaration-identity check. See ../DEFINITION_MAP.md for the source map
and mathematical reading. The sole placeholder is the theorem being challenged.
Do not import this module together with the production formalization.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal RealInnerProductSpace

namespace ReweightedNPMLE

-- Source: ReweightedNPMLE/Gaussian.lean:21-21
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- Source: ReweightedNPMLE/Gaussian.lean:24-25
-- Included before gaussianConstant to preserve Lean's generated numeral proof
-- name gaussianScore._proof_1, which its Gaussian definitions reuse. This is
-- explicit algebra, not an assumed intermediate result.
noncomputable def gaussianScore {d : ℕ} (x θ : Point d) : ℝ :=
  inner ℝ x θ - ‖θ‖ ^ 2 / 2

-- Source: ReweightedNPMLE/Gaussian.lean:28-29
noncomputable def gaussianConstant (d : ℕ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2)

-- Source: ReweightedNPMLE/Gaussian.lean:36-37
noncomputable def gaussianKernel (d : ℕ) (x θ : Point d) : ℝ :=
  gaussianConstant d * Real.exp (-‖x - θ‖ ^ 2 / 2)

-- Source: ReweightedNPMLE/GaussianMixtureMeasure.lean:19-21
noncomputable def gaussianMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (θ : Θ → Point d) (x : Point d) : ℝ :=
  ∫ a, gaussianKernel d x (θ a) ∂μ

-- Source: ReweightedNPMLE/GaussianNearMLE.lean:22-24
noncomputable def compactGaussianMixtureDensity {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) : Point d → ℝ :=
  gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d))

-- Source: ReweightedNPMLE/Weights.lean:26-27
noncomputable def weightedLogLikelihood {n : ℕ} (w v : Fin n → ℝ) : ℝ :=
  ∑ i, w i * Real.log (v i)

-- Source: ReweightedNPMLE/Weights.lean:30-31
def IsMaxOn {E : Type*} (C : Set E) (f : E → ℝ) (v : E) : Prop :=
  v ∈ C ∧ ∀ u ∈ C, f u ≤ f v

-- Source: ReweightedNPMLE/Weights.lean:34-35
def positiveVectors (n : ℕ) : Set (Fin n → ℝ) :=
  {v | ∀ i, 0 < v i}

-- Source: ReweightedNPMLE/ProbabilityOptimizerFiber.lean:24-26
noncomputable def probabilityMixtureValue {Θ : Type*} [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (μ : ProbabilityMeasure Θ) : Fin n → ℝ :=
  fun i ↦ ∫ θ, A θ i ∂μ

-- Source: ReweightedNPMLE/GaussianJointEvents.lean:18-18
abbrev GaussianDataWeight (d n : ℕ) := (Fin n → Point d) × (Fin n → ℝ)

-- Source: ReweightedNPMLE/GaussianJointEvents.lean:20-23
noncomputable def gaussianProbabilityLogLikelihood {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n × ProbabilityMeasure Θ) : ℝ :=
  weightedLogLikelihood p.1.2
    (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)

-- Source: ReweightedNPMLE/GaussianJointEvents.lean:25-27
def gaussianProbabilityOptimizerSet {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n) : Set (ProbabilityMeasure Θ) :=
  {μ | IsMaxOn univ (fun ν ↦ gaussianProbabilityLogLikelihood θ (p, ν)) μ}

-- Source: ReweightedNPMLE/GaussianJointEvents.lean:82-86
noncomputable def gaussianOrdinaryLikelihoodGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.2) -
    gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.1)

-- Source: ReweightedNPMLE/GaussianJointEvents.lean:113-118
noncomputable def gaussianSquaredLogRatioGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  ∑ i, (Real.log
    (probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.1 i /
     probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.2 i)) ^ 2

-- Source: ReweightedNPMLE/GaussianNearMLERate.lean:24-25
noncomputable def gaussianPaperLogScale (n : ℕ) : ℝ :=
  Real.log n / Real.log (Real.log n)

-- Source: ReweightedNPMLE/GaussianPaperScales.lean:19-20
noncomputable def gaussianPaperEffectiveDimension (d n : ℕ) : ℝ :=
  gaussianPaperLogScale n ^ d

-- Source: ReweightedNPMLE/GaussianPaperScales.lean:22-23
noncomputable def gaussianPaperAugmentedDimension (d n : ℕ) : ℝ :=
  gaussianPaperEffectiveDimension d n + Real.log n

-- Source: ReweightedNPMLE/GaussianPaperScales.lean:25-26
noncomputable def gaussianPaperBalancedShape (d n : ℕ) : ℝ :=
  gaussianPaperAugmentedDimension d n * Real.log n

-- NEGATIVE CONTROL: differs from ReweightedNPMLE/GaussianMainTheorem.lean:15-16
noncomputable def gaussianPaperRiskScale (d n : ℕ) : ℝ :=
  gaussianPaperLogScale n ^ d * Real.log n / n * 2

-- Source: ReweightedNPMLE/GaussianSampling.lean:18-21
noncomputable def compactGaussianSampleMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : Measure (Fin n → Point d) :=
  Measure.pi (fun _ : Fin n ↦ volume.withDensity
    (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))

-- Source: ReweightedNPMLE/DirichletIndependence.lean:115-117
noncomputable def gammaProductMeasure (n : ℕ) (a r : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gammaMeasure a r)

-- Source: ReweightedNPMLE/GaussianJointTheorems.lean:19-21
noncomputable def gaussianDataWeightMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) (α : ℝ) : Measure (GaussianDataWeight d n) :=
  (compactGaussianSampleMeasure Gstar n).prod (gammaProductMeasure n α α)

-- Source: ReweightedNPMLE/Hellinger.lean:23-25
noncomputable def hellingerSq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ

end ReweightedNPMLE

open ReweightedNPMLE

namespace ComparatorAudit

theorem main
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, (∀ i, |p.2 i - 1| ≤ C / Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧
          p.2 ∈ positiveVectors n ∧ ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              C * gaussianPaperAugmentedDimension d n ∧
            (∀ μ₀ ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (p.1, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤ C / Real.log n ∧
              gaussianSquaredLogRatioGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤ C / Real.log n) ∧
            hellingerSq volume (compactGaussianMixtureDensity μ) (compactGaussianMixtureDensity Gstar) ≤
              C * gaussianPaperRiskScale d n := by
  sorry

end ComparatorAudit
