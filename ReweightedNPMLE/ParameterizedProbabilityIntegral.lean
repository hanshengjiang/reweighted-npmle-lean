import ReweightedNPMLE.ProbabilityOptimizerFiber
import ReweightedNPMLE.Gaussian
import ReweightedNPMLE.CompactOptimizerEvents
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-!
# Joint continuity of compact-parameter probability integrals

Weak convergence of the law and uniform convergence of the integrand can
vary simultaneously. The probability normalization bounds the integral of
the varying integrand difference by its supremum norm.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

theorem continuous_probabilityIntegral_with_parameter {X Θ : Type*}
    [TopologicalSpace X] [TopologicalSpace Θ] [CompactSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (F : X → C(Θ, ℝ)) (hF : Continuous F) :
    Continuous (fun p : X × ProbabilityMeasure Θ ↦ ∫ a, F p.1 a ∂p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hfixed : Tendsto (fun q : X × ProbabilityMeasure Θ ↦ ∫ a, F p.1 a ∂q.2)
      (𝓝 p) (𝓝 (∫ a, F p.1 a ∂p.2)) :=
    ((ProbabilityMeasure.continuous_integral_continuousMap (F p.1)).comp
      continuous_snd).continuousAt
  have hnorm : Tendsto (fun q : X × ProbabilityMeasure Θ ↦ ‖F q.1 - F p.1‖)
      (𝓝 p) (𝓝 0) := by
    have hh : Continuous (fun q : X × ProbabilityMeasure Θ ↦ ‖F q.1 - F p.1‖) :=
      ((hF.comp continuous_fst).sub continuous_const).norm
    have hh' : Tendsto (fun q : X × ProbabilityMeasure Θ ↦ ‖F q.1 - F p.1‖)
        (𝓝 p) (𝓝 ‖F p.1 - F p.1‖) := hh.continuousAt
    simpa only [sub_self, norm_zero] using hh'
  have herr : Tendsto (fun q : X × ProbabilityMeasure Θ ↦
      ∫ a, (F q.1 - F p.1) a ∂q.2) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero_norm _ hnorm
    intro q
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := (q.2 : Measure Θ))
        (Eventually.of_forall (fun a ↦ (F q.1 - F p.1).norm_coe_le_norm a)))
  have hidentity (q : X × ProbabilityMeasure Θ) :
      (∫ a, (F q.1 - F p.1) a ∂q.2) + (∫ a, F p.1 a ∂q.2) =
        ∫ a, F q.1 a ∂q.2 := by
    have h₁ := (F q.1).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (q.2 : Measure Θ))
    have h₂ := (F p.1).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (q.2 : Measure Θ))
    simp only [ContinuousMap.sub_apply]
    rw [integral_sub h₁ h₂]
    ring
  simpa only [hidentity, zero_add] using herr.add hfixed

theorem continuous_gaussian_probabilityMixtureValue_joint {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦
      probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1 i) (θ a)) p.2) := by
  have hk (y : Point d) : Continuous (fun a : Θ ↦ gaussianKernel d y (θ a)) := by
    have hpair : Continuous (fun a : Θ ↦ (y, θ a)) := continuous_const.prodMk hθ
    have hh : Continuous ((fun z : Point d × Point d ↦ gaussianKernel d z.1 z.2) ∘
        (fun a : Θ ↦ (y, θ a))) :=
      (continuous_gaussianKernel d).comp hpair
    simpa only [Function.comp_apply] using hh
  let F : Point d → C(Θ, ℝ) := fun y ↦ ⟨fun a ↦ gaussianKernel d y (θ a), hk y⟩
  have huncurry : Continuous (fun p : Point d × Θ ↦ F p.1 p.2) := by
    have hpair : Continuous (fun p : Point d × Θ ↦ (p.1, θ p.2)) :=
      continuous_fst.prodMk (hθ.comp continuous_snd)
    have hh : Continuous ((fun z : Point d × Point d ↦ gaussianKernel d z.1 z.2) ∘
        (fun p : Point d × Θ ↦ (p.1, θ p.2))) :=
      (continuous_gaussianKernel d).comp hpair
    exact hh
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F huncurry
  apply continuous_pi
  intro i
  have hmap : Continuous (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦ (p.1 i, p.2)) :=
    ((continuous_apply i).comp continuous_fst).prodMk continuous_snd
  have hh : Continuous ((fun p : Point d × ProbabilityMeasure Θ ↦ ∫ a, F p.1 a ∂p.2) ∘
      (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦ (p.1 i, p.2))) :=
    (continuous_probabilityIntegral_with_parameter F hF).comp hmap
  exact hh

theorem gaussian_probabilityMixtureValue_pos {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (μ : ProbabilityMeasure Θ) (i : Fin n) :
    0 < probabilityMixtureValue (fun a j ↦ gaussianKernel d (x j) (θ a)) μ i := by
  let A := fun a j ↦ gaussianKernel d (x j) (θ a)
  have hA : Continuous A := by
    apply continuous_pi
    intro j
    have hpair : Continuous (fun a : Θ ↦ (x j, θ a)) := continuous_const.prodMk hθ
    have hh : Continuous ((fun p : Point d × Point d ↦ gaussianKernel d p.1 p.2) ∘
        (fun a : Θ ↦ (x j, θ a))) := (continuous_gaussianKernel d).comp hpair
    exact hh
  have hCpos : convexHull ℝ (range A) ⊆ positiveVectors n :=
    convexHull_min (by rintro a ⟨b, rfl⟩; exact fun j ↦ gaussianKernel_pos d (x j) (θ b))
      (convex_positiveVectors n)
  exact hCpos (probabilityMixtureValue_mem_convexHull A hA μ) i

theorem continuous_gaussian_probabilityLogLikelihood_joint {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      weightedLogLikelihood p.1.2
        (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)) := by
  let M := fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
    probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2
  have hmap : Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      (p.1.1, p.2)) := (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hM : Continuous M :=
    (continuous_gaussian_probabilityMixtureValue_joint θ hθ).comp hmap
  change Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
    ∑ i, p.1.2 i * Real.log (M p i))
  apply continuous_finsetSum
  intro i _
  have hw : Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      p.1.2 i) := (continuous_apply i).comp (continuous_snd.comp continuous_fst)
  have hf : Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      M p i) := (continuous_apply i).comp hM
  exact hw.mul (hf.log (fun p ↦ (gaussian_probabilityMixtureValue_pos p.1.1 θ hθ p.2 i).ne'))

theorem isClosed_gaussian_probabilityOptimizerGraph {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    IsClosed (compactOptimizerGraph
      (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
        weightedLogLikelihood p.1.2
          (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2))) :=
  isClosed_compactOptimizerGraph _ (continuous_gaussian_probabilityLogLikelihood_joint θ hθ)

end ReweightedNPMLE
