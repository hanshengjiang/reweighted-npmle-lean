import ReweightedNPMLE.PopulationCriterion
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

/-! # Population criterion gap and unchanged Gaussian density target

The divergence is mathlib's genuine measure-theoretic KL divergence. The
true log density is integrable whenever the assumed candidate log density is;
this follows from compact Gaussian quadratic bounds, not an extra hypothesis.
-/

open Set MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ReweightedNPMLE

theorem gaussianMixture_log_quadratic_bounds {d : ℕ} {Θ : Type*}
    [MeasurableSpace Θ] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) {S : ℝ} (hS : 0 ≤ S)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) (x : Point d) :
    Real.log (gaussianConstant d) - ‖x‖ ^ 2 - S ^ 2 ≤ Real.log (gaussianMixture μ θ x) ∧
      Real.log (gaussianMixture μ θ x) ≤ Real.log (gaussianConstant d) - ‖x‖ ^ 2 / 4 + S ^ 2 / 2 := by
  have hlow (a : Θ) : gaussianConstant d * Real.exp (-‖x‖ ^ 2 - S ^ 2) ≤
      gaussianKernel d x (θ a) := by
    have htri : ‖x - θ a‖ ≤ ‖x‖ + S := (norm_sub_le x (θ a)).trans (by linarith [hθbound a])
    have hsq : ‖x - θ a‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * S ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg (x - θ a), sq_nonneg (‖x‖ - S)]
    unfold gaussianKernel
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (gaussianConstant_pos d).le
  have hupp (a : Θ) : gaussianKernel d x (θ a) ≤
      gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 4 + S ^ 2 / 2) := by
    have htri : ‖x‖ ≤ ‖x - θ a‖ + S := by
      have h := norm_add_le (x - θ a) (θ a)
      rw [sub_add_cancel] at h
      linarith [hθbound a]
    have hsq : ‖x‖ ^ 2 ≤ 2 * ‖x - θ a‖ ^ 2 + 2 * S ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg (x - θ a), sq_nonneg (‖x - θ a‖ - S)]
    unfold gaussianKernel
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (gaussianConstant_pos d).le
  have hlowInt : gaussianConstant d * Real.exp (-‖x‖ ^ 2 - S ^ 2) ≤ gaussianMixture μ θ x := by
    simpa using integral_mono (integrable_const _) (gaussianKernel_comp_integrable μ θ hθ x) hlow
  have huppInt : gaussianMixture μ θ x ≤ gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 4 + S ^ 2 / 2) := by
    simpa using integral_mono (gaussianKernel_comp_integrable μ θ hθ x) (integrable_const _) hupp
  have hl := Real.log_le_log (mul_pos (gaussianConstant_pos d) (Real.exp_pos _)) hlowInt
  have hu := Real.log_le_log (gaussianMixture_pos μ θ hθ x) huppInt
  simp only [Real.log_mul (gaussianConstant_pos d).ne' (Real.exp_pos _).ne', Real.log_exp] at hl hu
  constructor <;> linarith

theorem compactGaussianMixture_log_integrable_of_candidate {d : ℕ} {K : Set (Point d)}
    (ρ : Measure (Point d)) [IsFiniteMeasure ρ] (Gstar G : ProbabilityMeasure K)
    {S : ℝ} (hS : 0 ≤ S) (hKbound : ∀ a ∈ K, ‖a‖ ≤ S)
    (hG : Integrable (fun x ↦ Real.log (compactGaussianMixtureDensity G x)) ρ) :
    Integrable (fun x ↦ Real.log (compactGaussianMixtureDensity Gstar x)) ρ := by
  have hbound : ∀ x : Point d,
      ‖Real.log (compactGaussianMixtureDensity Gstar x)‖ ≤
        4 * ‖Real.log (compactGaussianMixtureDensity G x)‖ +
          (5 * |Real.log (gaussianConstant d)| + 3 * S ^ 2) := by
    intro x
    have hstar := gaussianMixture_log_quadratic_bounds (Gstar : Measure K)
      (fun a : K ↦ (a : Point d)) measurable_subtype_coe hS (fun a ↦ hKbound a.val a.property) x
    have hg := gaussianMixture_log_quadratic_bounds (G : Measure K)
      (fun a : K ↦ (a : Point d)) measurable_subtype_coe hS (fun a ↦ hKbound a.val a.property) x
    change Real.log (gaussianConstant d) - ‖x‖ ^ 2 - S ^ 2 ≤ Real.log (compactGaussianMixtureDensity Gstar x) ∧
      Real.log (compactGaussianMixtureDensity Gstar x) ≤ Real.log (gaussianConstant d) - ‖x‖ ^ 2 / 4 + S ^ 2 / 2 at hstar
    change Real.log (gaussianConstant d) - ‖x‖ ^ 2 - S ^ 2 ≤ Real.log (compactGaussianMixtureDensity G x) ∧
      Real.log (compactGaussianMixtureDensity G x) ≤ Real.log (gaussianConstant d) - ‖x‖ ^ 2 / 4 + S ^ 2 / 2 at hg
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith [hstar.1, hstar.2, hg.2,
      neg_abs_le (Real.log (compactGaussianMixtureDensity G x)),
      neg_abs_le (Real.log (gaussianConstant d)), le_abs_self (Real.log (gaussianConstant d)),
      abs_nonneg (Real.log (compactGaussianMixtureDensity G x)), abs_nonneg (Real.log (gaussianConstant d)),
      sq_nonneg S]
  exact ((hG.norm.const_mul 4).add (integrable_const _)).mono'
    ((compactGaussianMixtureDensity_measurable Gstar).log.aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)

/-- The density population criterion gap is precisely genuine KL divergence;
it is nonnegative and vanishes exactly at the unchanged density-law target. -/
theorem compactGaussianMixture_population_gap_eq_klDiv {d : ℕ} {K : Set (Point d)}
    (Gstar G : ProbabilityMeasure K) {S : ℝ} (hS : 0 ≤ S)
    (hKbound : ∀ a ∈ K, ‖a‖ ≤ S)
    (hG : Integrable (fun x ↦ Real.log (compactGaussianMixtureDensity G x))
      (gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d)))) :
    let ρ := gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d))
    let σ := gaussianLocationMixtureLaw (G : Measure K) (fun a : K ↦ (a : Point d))
    let gap := (∫ x, Real.log (compactGaussianMixtureDensity Gstar x) ∂ρ) -
      ∫ x, Real.log (compactGaussianMixtureDensity G x) ∂ρ
    gap = (klDiv ρ σ).toReal ∧ 0 ≤ gap ∧ (gap = 0 ↔ ρ = σ) := by
  let f := compactGaussianMixtureDensity Gstar
  let g := compactGaussianMixtureDensity G
  let ρ := gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d))
  let σ := gaussianLocationMixtureLaw (G : Measure K) (fun a : K ↦ (a : Point d))
  letI : IsProbabilityMeasure ρ := gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  letI : IsProbabilityMeasure σ := gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  have hf : Measurable f := compactGaussianMixtureDensity_measurable Gstar
  have hg : Measurable g := compactGaussianMixtureDensity_measurable G
  have hfpos : ∀ x, 0 < f x := compactGaussianMixtureDensity_pos Gstar
  have hgpos : ∀ x, 0 < g x := compactGaussianMixtureDensity_pos G
  have hρ : ρ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := compactGaussianMixtureLaw_eq_density Gstar
  have hσ : σ = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) := compactGaussianMixtureLaw_eq_density G
  have hρv : ρ ≪ volume := by rw [hρ]; exact withDensity_absolutelyContinuous _ _
  have hvσ : volume ≪ σ := by
    rw [hσ]
    exact withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hgpos x)).ne')
  have hac : ρ ≪ σ := hρv.trans hvσ
  have hrn : ρ.rnDeriv σ =ᵐ[volume] fun x ↦ (ENNReal.ofReal (g x))⁻¹ * ENNReal.ofReal (f x) := by
    have hright := Measure.rnDeriv_withDensity_right (μ := ρ) (ν := volume) hg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hgpos x)).ne')
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_ne_top)
    have hleft := Measure.rnDeriv_withDensity volume hf.ennreal_ofReal
    rw [← hσ] at hright
    rw [← hρ] at hleft
    filter_upwards [hright, hleft] with x hr hl
    rw [hr, hl]
  have hllr : llr ρ σ =ᵐ[ρ] fun x ↦ Real.log (f x) - Real.log (g x) := by
    filter_upwards [hρv.ae_le hrn] with x hx
    rw [llr, hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (hfpos x).le, ENNReal.toReal_ofReal (hgpos x).le,
      Real.log_mul (inv_ne_zero (hgpos x).ne') (hfpos x).ne', Real.log_inv]
    ring
  have hstar : Integrable (fun x ↦ Real.log (f x)) ρ :=
    compactGaussianMixture_log_integrable_of_candidate ρ Gstar G hS hKbound hG
  have hllrInt : Integrable (llr ρ σ) ρ := (hstar.sub hG).congr hllr.symm
  have hgap : (∫ x, Real.log (f x) ∂ρ) - (∫ x, Real.log (g x) ∂ρ) = (klDiv ρ σ).toReal := by
    rw [toReal_klDiv hac hllrInt, probReal_univ, probReal_univ, add_sub_cancel_right,
      ← integral_sub hstar hG]
    exact integral_congr_ae hllr.symm
  refine ⟨hgap, ?_, ?_⟩
  · rw [hgap]
    exact ENNReal.toReal_nonneg
  · rw [hgap, ENNReal.toReal_eq_zero_iff]
    simpa only [klDiv_ne_top hac hllrInt, or_false] using (klDiv_eq_zero_iff (μ := ρ) (ν := σ))

end ReweightedNPMLE
