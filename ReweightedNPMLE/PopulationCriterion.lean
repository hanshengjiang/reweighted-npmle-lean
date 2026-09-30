import ReweightedNPMLE.GaussianJointTheorems
import ReweightedNPMLE.DirichletIndependence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Joint data-and-weight population criterion

The equalities are over independent iid observations and the actual Gamma
weights, including their normalization. Integrability is proved on the product
experiment, rather than merely asserted for fixed observations.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ReweightedNPMLE

theorem iid_weighted_population_integral {X W : Type*}
    [MeasurableSpace X] [MeasurableSpace W] {n : ℕ}
    (ρ : Measure X) [IsProbabilityMeasure ρ] (Q : Measure W) [IsProbabilityMeasure Q]
    (h : X → ℝ) (hh : Integrable h ρ) (a : W → Fin n → ℝ) (c : ℝ)
    (ha : ∀ i, Integrable (fun w ↦ a w i) Q)
    (hmean : ∀ i, ∫ w, a w i ∂Q = c) :
    Integrable (fun p : (Fin n → X) × W ↦ ∑ i, a p.2 i * h (p.1 i))
      ((Measure.pi (fun _ : Fin n ↦ ρ)).prod Q) ∧
    (∫ p : (Fin n → X) × W, ∑ i, a p.2 i * h (p.1 i)
      ∂((Measure.pi (fun _ : Fin n ↦ ρ)).prod Q)) =
        (n : ℝ) * c * ∫ x, h x ∂ρ := by
  let P := Measure.pi (fun _ : Fin n ↦ ρ)
  have hcomp (i : Fin n) : Integrable (fun x : Fin n → X ↦ h (x i)) P :=
    integrable_comp_eval (μ := fun _ : Fin n ↦ ρ) hh
  have hterm (i : Fin n) : Integrable
      (fun p : (Fin n → X) × W ↦ a p.2 i * h (p.1 i)) (P.prod Q) := by
    simpa only [mul_comm] using (hcomp i).mul_prod (ha i)
  refine ⟨integrable_finsetSum Finset.univ (fun i _ ↦ hterm i), ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hterm i)]
  have hfactor (i : Fin n) :
      (∫ p : (Fin n → X) × W, a p.2 i * h (p.1 i) ∂(P.prod Q)) =
        (∫ x, h x ∂ρ) * c := by
    have hprod := integral_prod_mul (fun x : Fin n → X ↦ h (x i)) (fun w : W ↦ a w i)
      (μ := P) (ν := Q)
    rw [hmean i, integral_comp_eval (μ := fun _ : Fin n ↦ ρ) (i := i) hh.aestronglyMeasurable] at hprod
    simpa only [mul_comm] using hprod
  simp_rw [hfactor]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Both the raw Gamma-weighted empirical mean and its normalized counterpart
have the unchanged iid population mean under the actual joint experiment. -/
theorem iid_gamma_population_criterion {X : Type*} [MeasurableSpace X]
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (ρ : Measure X) [IsProbabilityMeasure ρ] (h : X → ℝ) (hh : Integrable h ρ) :
    (∫ p : (Fin n → X) × (Fin n → ℝ), (∑ i, p.2 i * h (p.1 i)) / n
      ∂((Measure.pi (fun _ : Fin n ↦ ρ)).prod (gammaWeightMeasure n α))) = ∫ x, h x ∂ρ ∧
    (∫ p : (Fin n → X) × (Fin n → ℝ), ∑ i, normalize p.2 i * h (p.1 i)
      ∂((Measure.pi (fun _ : Fin n ↦ ρ)).prod (gammaWeightMeasure n α))) = ∫ x, h x ∂ρ := by
  letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) := gammaWeightMeasure_isProbability n hα
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hraw := iid_weighted_population_integral ρ (gammaWeightMeasure n α) h hh
    (fun w ↦ w) 1
    (fun _ ↦ integrable_comp_eval (μ := fun _ : Fin n ↦ gammaMeasure α α)
      (integrable_id_gammaMeasure hα hα))
    (fun i ↦ by
      change (∫ w : Fin n → ℝ, w i ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) = 1
      rw [integral_comp_eval (μ := fun _ : Fin n ↦ gammaMeasure α α) (i := i)
        (integrable_id_gammaMeasure hα hα).aestronglyMeasurable]
      exact centered_gamma_mean hα)
  have hnormalized := iid_weighted_population_integral ρ (gammaWeightMeasure n α) h hh
    normalize (1 / n) (integrable_normalize_coord_gammaWeightMeasure hα)
    (normalized_gamma_coordinate_mean hn hα)
  constructor
  · change (∫ p : (Fin n → X) × (Fin n → ℝ),
      (∑ i, p.2 i * h (p.1 i)) * (n : ℝ)⁻¹ ∂_) = _
    rw [integral_mul_const, hraw.2]
    field_simp
  · simpa only [mul_one_div_cancel hn0, one_mul] using hnormalized.2

/-- The joint likelihood criterion in `prop:dirichlet` has exactly the
ordinary density population target, for every integrable candidate log density. -/
theorem compactGaussianMixture_unchanged_population_criterion
    {d n : ℕ} {K : Set (Point d)} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (Gstar G : ProbabilityMeasure K)
    (hlog : Integrable (fun x ↦ Real.log (compactGaussianMixtureDensity G x))
      (gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d)))) :
    (∫ p : GaussianDataWeight d n,
      (∑ i, p.2 i * Real.log (compactGaussianMixtureDensity G (p.1 i))) / n
      ∂gaussianDataWeightMeasure Gstar n α) =
        ∫ x, Real.log (compactGaussianMixtureDensity G x)
          ∂gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d)) ∧
    (∫ p : GaussianDataWeight d n,
      ∑ i, normalize p.2 i * Real.log (compactGaussianMixtureDensity G (p.1 i))
      ∂gaussianDataWeightMeasure Gstar n α) =
        ∫ x, Real.log (compactGaussianMixtureDensity G x)
          ∂gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d)) := by
  let ρ := gaussianLocationMixtureLaw (Gstar : Measure K) (fun a : K ↦ (a : Point d))
  letI : IsProbabilityMeasure ρ := gaussianLocationMixtureLaw_isProbability _ _ measurable_subtype_coe
  have h := iid_gamma_population_criterion hn hα ρ _ hlog
  simpa only [ρ, compactGaussianMixtureLaw_eq_density, gammaWeightMeasure_eq_gammaProductMeasure,
    gaussianDataWeightMeasure, compactGaussianSampleMeasure] using h

end ReweightedNPMLE
