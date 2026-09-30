import ReweightedNPMLE.GaussianMixtureHellinger

/-!
# Global Hellinger control from arbitrary mixing laws

The Gaussian overlap/Fubini identities in this file connect a general
probability mixing law to a finitely supported moment-matching law.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE

theorem gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    Integrable (fun x : Point d ↦
      gaussianMixture μ θ x * finiteGaussianMixture w z x /
        gaussianDensity d x) := by
  have hsum : Integrable (fun x : Point d ↦
      ∑ i, w i * (gaussianMixture μ θ x * gaussianKernel d x (z i) /
        gaussianDensity d x)) :=
    integrable_finsetSum Finset.univ fun i _ ↦
      (gaussianMixture_mul_kernel_div_density_integrable
        μ θ hθmeas hS hθS (z i) (hzS i)).const_mul (w i)
  apply hsum.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    unfold finiteGaussianMixture
    change (∑ i, w i * (gaussianMixture μ θ x * gaussianKernel d x (z i) /
        gaussianDensity d x)) =
      gaussianMixture μ θ x * (∑ i, w i * gaussianKernel d x (z i)) /
        gaussianDensity d x
    rw [Finset.mul_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem integral_gaussianMixture_mul_finiteGaussianMixture_div_density
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
        gaussianMixture μ θ x * finiteGaussianMixture w z x /
          gaussianDensity d x =
      ∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ := by
  have hcomponent (i : ι) := gaussianMixture_mul_kernel_div_density_integrable
    μ θ hθmeas hS hθS (z i) (hzS i)
  calc
    (∫ x : Point d,
        gaussianMixture μ θ x * finiteGaussianMixture w z x /
          gaussianDensity d x) =
        ∫ x : Point d, ∑ i, w i *
          (gaussianMixture μ θ x * gaussianKernel d x (z i) /
            gaussianDensity d x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        unfold finiteGaussianMixture
        change gaussianMixture μ θ x * (∑ i, w i * gaussianKernel d x (z i)) /
            gaussianDensity d x =
          ∑ i, w i * (gaussianMixture μ θ x * gaussianKernel d x (z i) /
            gaussianDensity d x)
        rw [Finset.mul_sum]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ∑ i, ∫ x : Point d, w i *
        (gaussianMixture μ θ x * gaussianKernel d x (z i) /
          gaussianDensity d x) := by
      rw [integral_finsetSum Finset.univ]
      intro i _
      exact (hcomponent i).const_mul (w i)
    _ = ∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul,
        integral_gaussianMixture_mul_kernel_div_density
          μ θ hθmeas hS hθS (z i) (hzS i)]

theorem gaussianMixture_sub_finite_sq_div_density_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    Integrable (fun x : Point d ↦
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x) := by
  have hp := gaussianMixture_sq_div_density_integrable μ θ hθmeas hS hθS
  have hpq := gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
    μ θ hθmeas w z hS hθS hzS
  have hq := finiteGaussianMixture_sq_div_density_integrable w z
  apply (hp.sub (hpq.const_mul 2) |>.add hq).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x -
          2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x) +
        (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x =
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x
    ring

theorem integral_gaussianMixture_sub_finite_sq_div_density
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x =
      (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
        ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) := by
  have hp := gaussianMixture_sq_div_density_integrable μ θ hθmeas hS hθS
  have hpq := gaussianMixture_mul_finiteGaussianMixture_div_density_integrable
    μ θ hθmeas w z hS hθS hzS
  have hq := finiteGaussianMixture_sq_div_density_integrable w z
  have hpq2 : Integrable (fun x : Point d ↦
      2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
        gaussianDensity d x)) := hpq.const_mul 2
  calc
    _ = ∫ x : Point d,
        (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x -
          2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x) +
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = (∫ x : Point d,
          (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x -
            2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
              gaussianDensity d x)) +
        ∫ x : Point d,
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      exact integral_add (hp.sub hpq2) hq
    _ = ((∫ x : Point d,
          (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x) -
        ∫ x : Point d,
          2 * (gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x)) +
        ∫ x : Point d,
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      rw [integral_sub hp hpq2]
    _ = (∫ x : Point d,
          (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x) -
        2 * (∫ x : Point d,
          gaussianMixture μ θ x * finiteGaussianMixture w z x /
            gaussianDensity d x) +
        ∫ x : Point d,
          (finiteGaussianMixture w z x) ^ 2 / gaussianDensity d x := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_gaussianMixture_sq_div_density μ θ hθmeas hS hθS,
        integral_gaussianMixture_mul_finiteGaussianMixture_div_density
          μ θ hθmeas w z hS hθS hzS,
        integral_finiteGaussianMixture_sq_div_density]

theorem pointTruncatedInnerExp_comp_integrable
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (θ : Θ → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (y : Point d) :
    Integrable (fun a ↦ pointTruncatedInnerExp L (θ a) y) μ := by
  have h := (coordinateTruncatedInnerExp_isMonomialCombination
    L (fun r ↦ y r)).integrable_comp_of_feature
      μ (fun a r ↦ θ a r) hint
  apply h.congr
  exact Filter.Eventually.of_forall fun a ↦ by
    simp only [pointTruncatedInnerExp, coordinateTruncatedInnerExp,
      inner_eq_coordinateDot, real_inner_comm]

theorem moment_matching_pointTruncatedInnerExp_integral
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) (θ : Θ → Point d)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    (y : Point d) :
    ∑ i, w i * pointTruncatedInnerExp L (z i) y =
      ∫ a, pointTruncatedInnerExp L (θ a) y ∂μ := by
  have h := (coordinateTruncatedInnerExp_isMonomialCombination
    L (fun r ↦ y r)).weighted_sum_eq_integral
      w (fun i r ↦ z i r) μ (fun a r ↦ θ a r) hint hmom
  simpa only [pointTruncatedInnerExp, coordinateTruncatedInnerExp,
    inner_eq_coordinateDot, real_inner_comm] using h

theorem pointTruncatedInnerExp_comm {d : ℕ} (L : ℕ) (x y : Point d) :
    pointTruncatedInnerExp L x y = pointTruncatedInnerExp L y x := by
  unfold pointTruncatedInnerExp
  rw [real_inner_comm]

/-- Exact moment matching annihilates the entire truncated part of the
general-law/finite-law Gaussian overlap quadratic form. -/
theorem moment_matching_truncated_quadratic_zero
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) (θ : Θ → Point d)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ) :
    (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointTruncatedInnerExp L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j) = 0 := by
  have hcomponent (i : ι) : Integrable (fun a ↦
      w i * pointTruncatedInnerExp L (θ a) (z i)) μ :=
    (pointTruncatedInnerExp_comp_integrable μ θ hint (z i)).const_mul (w i)
  have hA :
      (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) =
        ∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
    calc
      (∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ) =
          ∫ a, ∑ i, w i * pointTruncatedInnerExp L (z i) (θ a) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a ↦
          (moment_matching_pointTruncatedInnerExp_integral
            μ θ w z hint hmom (θ a)).symm
      _ = ∫ a, ∑ i, w i * pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a ↦ by
          apply Finset.sum_congr rfl
          intro i _
          rw [pointTruncatedInnerExp_comm]
      _ = ∑ i, ∫ a, w i * pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
        exact integral_finsetSum Finset.univ fun i _ ↦ hcomponent i
      _ = ∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
  have hB :
      (∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ) =
        ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← moment_matching_pointTruncatedInnerExp_integral μ θ w z hint hmom (z i)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pointTruncatedInnerExp_comm L (z j) (z i)]
    ring
  rw [hA, hB]
  ring

theorem continuous_pointInnerExpRemainder (d L : ℕ) :
    Continuous fun z : Point d × Point d ↦
      pointInnerExpRemainder L z.1 z.2 := by
  unfold pointInnerExpRemainder pointTruncatedInnerExp
  fun_prop

theorem pointInnerExpRemainder_comp_integrable
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (y : Point d) (hyS : ‖y‖ ≤ S) :
    Integrable (fun a ↦ pointInnerExpRemainder L (θ a) y) μ := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  apply Integrable.of_bound
    ((continuous_pointInnerExpRemainder d L).measurable.comp
      (hθmeas.prodMk measurable_const) |>.aestronglyMeasurable) R
  exact Filter.Eventually.of_forall fun a ↦ by
    rw [Real.norm_eq_abs]
    exact abs_pointInnerExpRemainder_le hS (hθS a) hyS

theorem abs_integral_pointInnerExpRemainder_comp_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (y : Point d) (hyS : ‖y‖ ≤ S) :
    |∫ a, pointInnerExpRemainder L (θ a) y ∂μ| ≤
      Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial := by
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := μ)
    (C := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial)
    (f := fun a ↦ pointInnerExpRemainder L (θ a) y)
    (Filter.Eventually.of_forall fun a ↦ by
      rw [Real.norm_eq_abs]
      exact abs_pointInnerExpRemainder_le hS (hθS a) hyS)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

theorem pointInnerExpRemainder_comp_comp_integrable
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    Integrable (fun z : Θ × Θ ↦
      pointInnerExpRemainder L (θ z.1) (θ z.2)) (μ.prod μ) := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  apply Integrable.of_bound
    ((continuous_pointInnerExpRemainder d L).measurable.comp
      ((hθmeas.comp measurable_fst).prodMk (hθmeas.comp measurable_snd))
      |>.aestronglyMeasurable) R
  exact Filter.Eventually.of_forall fun z ↦ by
    rw [Real.norm_eq_abs]
    exact abs_pointInnerExpRemainder_le hS (hθS z.1) (hθS z.2)

theorem abs_integral_integral_pointInnerExpRemainder_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    |∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ| ≤
      Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial := by
  have hrem := pointInnerExpRemainder_comp_comp_integrable
    (L := L) μ θ hθmeas hS hθS
  have hrem' : Integrable (fun z : Θ × Θ ↦
      pointInnerExpRemainder L (θ z.2) (θ z.1)) (μ.prod μ) := hrem.swap
  rw [integral_integral hrem']
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := μ.prod μ)
    (C := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial)
    (f := fun z : Θ × Θ ↦ pointInnerExpRemainder L (θ z.2) (θ z.1))
    (Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact abs_pointInnerExpRemainder_le hS (hθS z.2) (hθS z.1))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hnorm

theorem abs_general_finite_remainder_quadratic_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    |(∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)| ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  let A := ∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ
  let B := ∑ i, w i * ∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ
  let C := ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)
  have hA : |A| ≤ R := by
    simpa only [A, R] using
      abs_integral_integral_pointInnerExpRemainder_le
        (L := L) μ θ hθmeas hS hθS
  have hBi (i : ι) :
      |∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ| ≤ R := by
    simpa only [R] using
      (abs_integral_pointInnerExpRemainder_comp_le
        (d := d) (L := L) (Θ := Θ) μ θ hS hθS (z i) (hzS i))
  have hsumR : (∑ i, w i * R) = R := by
    calc
      (∑ i, w i * R) = (∑ i, w i) * R := by
        simpa using (Finset.sum_mul Finset.univ w R).symm
      _ = R := by rw [hwsum, one_mul]
  have hB : |B| ≤ R := by
    calc
      |B| ≤ ∑ i, |w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, w i * |∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]
      _ ≤ ∑ i, w i * R := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hBi i) (hw i)
      _ = R := hsumR
  have hC : |C| ≤ R := by
    calc
      |C| ≤ ∑ i, |∑ j,
          w i * w j * pointInnerExpRemainder L (z i) (z j)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j,
          |w i * w j * pointInnerExpRemainder L (z i) (z j)| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∑ j,
          w i * w j * |pointInnerExpRemainder L (z i) (z j)| := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hw i), abs_of_nonneg (hw j)]
      _ ≤ ∑ i, ∑ j, w i * w j * R := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (abs_pointInnerExpRemainder_le hS (hzS i) (hzS j))
          (mul_nonneg (hw i) (hw j))
      _ = R := by
        calc
          (∑ i, ∑ j, w i * w j * R) =
              ∑ i, w i * (∑ j, w j) * R := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum, Finset.sum_mul]
          _ = ∑ i, w i * R := by rw [hwsum]; simp
          _ = R := hsumR
  change |A - 2 * B + C| ≤ 4 * R
  calc
    |A - 2 * B + C| ≤ |A - 2 * B| + |C| := abs_add_le _ _
    _ ≤ (|A| + |2 * B|) + |C| :=
      add_le_add (abs_sub A (2 * B)) (le_refl |C|)
    _ = (|A| + 2 * |B|) + |C| := by rw [abs_mul]; norm_num
    _ ≤ (R + 2 * R) + R := by nlinarith
    _ = 4 * R := by ring

theorem exp_inner_eq_remainder_add_truncated {d : ℕ} (L : ℕ)
    (x y : Point d) :
    Real.exp (inner ℝ x y) =
      pointInnerExpRemainder L x y + pointTruncatedInnerExp L x y := by
  unfold pointInnerExpRemainder
  ring

theorem general_finite_quadratic_eq_remainder_of_moment_match
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
        ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) =
      (∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j) := by
  let Aexp := ∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ
  let Arem := ∫ a, ∫ b, pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ
  let Atrunc := ∫ a, ∫ b, pointTruncatedInnerExp L (θ b) (θ a) ∂μ ∂μ
  let Bexp := ∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ
  let Brem := ∑ i, w i * ∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ
  let Btrunc := ∑ i, w i * ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ
  let Cexp := ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j))
  let Crem := ∑ i, ∑ j, w i * w j * pointInnerExpRemainder L (z i) (z j)
  let Ctrunc := ∑ i, ∑ j, w i * w j * pointTruncatedInnerExp L (z i) (z j)
  have hExpDouble0 := exp_inner_comp_comp_integrable μ θ hθmeas hS hθS
  have hExpDouble : Integrable (fun q : Θ × Θ ↦
      Real.exp (inner ℝ (θ q.2) (θ q.1))) (μ.prod μ) := hExpDouble0.swap
  have hRemDouble0 := pointInnerExpRemainder_comp_comp_integrable
    (L := L) μ θ hθmeas hS hθS
  have hRemDouble : Integrable (fun q : Θ × Θ ↦
      pointInnerExpRemainder L (θ q.2) (θ q.1)) (μ.prod μ) := hRemDouble0.swap
  have hTruncDouble : Integrable (fun q : Θ × Θ ↦
      pointTruncatedInnerExp L (θ q.2) (θ q.1)) (μ.prod μ) := by
    apply (hExpDouble.sub hRemDouble).congr
    exact Filter.Eventually.of_forall fun q ↦ by
      change Real.exp (inner ℝ (θ q.2) (θ q.1)) -
          pointInnerExpRemainder L (θ q.2) (θ q.1) =
        pointTruncatedInnerExp L (θ q.2) (θ q.1)
      unfold pointInnerExpRemainder
      ring
  have hAeq : Aexp = Arem + Atrunc := by
    dsimp only [Aexp, Arem, Atrunc]
    rw [integral_integral hExpDouble, integral_integral hRemDouble,
      integral_integral hTruncDouble, ← integral_add hRemDouble hTruncDouble]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q ↦
      exp_inner_eq_remainder_add_truncated L (θ q.2) (θ q.1)
  have hsingle (i : ι) :
      (∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) =
        (∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ) +
          ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ := by
    have he := exp_inner_comp_integrable μ θ hθmeas hS hθS (z i) (hzS i)
    have hr := pointInnerExpRemainder_comp_integrable
      (L := L) μ θ hθmeas hS hθS (z i) (hzS i)
    have ht := pointTruncatedInnerExp_comp_integrable μ θ hint (z i)
    rw [← integral_add hr ht]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a ↦
      exp_inner_eq_remainder_add_truncated L (θ a) (z i)
  have hBeq : Bexp = Brem + Btrunc := by
    dsimp only [Bexp, Brem, Btrunc]
    calc
      (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) =
          ∑ i, w i * ((∫ a, pointInnerExpRemainder L (θ a) (z i) ∂μ) +
            ∫ a, pointTruncatedInnerExp L (θ a) (z i) ∂μ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsingle i]
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]
  have hCeq : Cexp = Crem + Ctrunc := by
    dsimp only [Cexp, Crem, Ctrunc]
    calc
      (∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j))) =
          ∑ i, ∑ j, w i * w j *
            (pointInnerExpRemainder L (z i) (z j) +
              pointTruncatedInnerExp L (z i) (z j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [exp_inner_eq_remainder_add_truncated]
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]
  have hzero : Atrunc - 2 * Btrunc + Ctrunc = 0 := by
    simpa only [Atrunc, Btrunc, Ctrunc] using
      moment_matching_truncated_quadratic_zero μ θ w z hint hmom
  change Aexp - 2 * Bexp + Cexp = Arem - 2 * Brem + Crem
  rw [hAeq, hBeq, hCeq]
  linarith

/-- Global weighted `L²` moment-tail bound between an arbitrary probability
mixing law and a moment-matching finite probability law. -/
theorem general_finite_moment_matching_weightedL2_bound
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    ∫ x : Point d,
        (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
          gaussianDensity d x ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial) := by
  calc
    (∫ x : Point d,
        (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
          gaussianDensity d x) =
        (∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ) -
          2 * (∑ i, w i * ∫ a, Real.exp (inner ℝ (θ a) (z i)) ∂μ) +
          ∑ i, ∑ j, w i * w j * Real.exp (inner ℝ (z i) (z j)) :=
      integral_gaussianMixture_sub_finite_sq_div_density
        μ θ hθmeas w z hS hθS hzS
    _ = (∫ a, ∫ b,
          pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j *
          pointInnerExpRemainder L (z i) (z j) :=
      general_finite_quadratic_eq_remainder_of_moment_match
        μ θ hθmeas w z hint hmom hS hθS hzS
    _ ≤ |(∫ a, ∫ b,
          pointInnerExpRemainder L (θ b) (θ a) ∂μ ∂μ) -
        2 * (∑ i, w i * ∫ a,
          pointInnerExpRemainder L (θ a) (z i) ∂μ) +
        ∑ i, ∑ j, w i * w j *
          pointInnerExpRemainder L (z i) (z j)| := le_abs_self _
    _ ≤ 4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial) :=
      abs_general_finite_remainder_quadratic_le
        μ θ hθmeas w z hw hwsum hS hθS hzS

/-- Squared-Hellinger consequence of moment matching for an arbitrary
probability mixing law and a finite probability law. -/
theorem hellingerSq_gaussianMixture_finite_moment_matching_le
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (w : ι → ℝ) (z : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hint : Integrable
      (fun a ↦ monomialFeature d L (fun r ↦ θ a r)) μ)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
      ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (hzS : ∀ i, ‖z i‖ ≤ S) :
    hellingerSq volume (gaussianMixture μ θ) (finiteGaussianMixture w z) ≤
      (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial)) ^ (1 / 2 : ℝ) := by
  have hpint := gaussianMixture_integrable μ θ hθmeas
  have hqint := finiteGaussianMixture_integrable w z
  have hpmeas : AEStronglyMeasurable (gaussianMixture μ θ)
      (volume : Measure (Point d)) := hpint.aestronglyMeasurable
  have hqmeas : AEStronglyMeasurable (finiteGaussianMixture w z)
      (volume : Measure (Point d)) :=
    (continuous_finiteGaussianMixture w z).aestronglyMeasurable
  have hp : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ gaussianMixture μ θ x :=
    Filter.Eventually.of_forall fun x ↦ (gaussianMixture_pos μ θ hθmeas x).le
  have hq : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture w z x :=
    Filter.Eventually.of_forall fun x ↦
      (finiteGaussianMixture_pos z hw hwsum x).le
  have hhell := hellingerIntegrand_integrable_of_integrable
    volume (gaussianMixture μ θ) (finiteGaussianMixture w z)
      hpmeas hqmeas hp hq hpint hqint
  have hl1 := abs_sub_integrable_of_integrable
    volume (gaussianMixture μ θ) (finiteGaussianMixture w z) hpint hqint
  have hweighted := gaussianMixture_sub_finite_sq_div_density_integrable
    μ θ hθmeas w z hS hθS hzS
  have hH := hellingerSq_le_sqrt_weightedL2
    volume (gaussianMixture μ θ) (finiteGaussianMixture w z)
      (gaussianDensity d) hp hq (hpmeas.sub hqmeas)
      (continuous_gaussianDensity d).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ gaussianDensity_pos d x)
      hhell hl1 hweighted (gaussianDensity_integrable d)
      (integral_gaussianDensity d)
  have hQnonneg : 0 ≤ ∫ x : Point d,
      (gaussianMixture μ θ x - finiteGaussianMixture w z x) ^ 2 /
        gaussianDensity d x := by
    apply integral_nonneg
    intro x
    exact div_nonneg (sq_nonneg _) (gaussianDensity_pos d x).le
  have hQbound := general_finite_moment_matching_weightedL2_bound
    μ θ hθmeas w z hw hwsum hint hmom hS hθS hzS
  exact hH.trans (Real.rpow_le_rpow hQnonneg hQbound (by norm_num))

/-- A compactly supported Gaussian location mixture has a finite mixture with
at most `choose (L + d) d + 1` slots and the explicit global Hellinger
moment-tail bound.  Slots of zero weight account for representations using
fewer atoms. -/
theorem exists_finite_gaussianMixture_hellinger_approximation
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    (K : Set (Point d)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ a, θ a ∈ K)
    {S : ℝ} (hS : 0 ≤ S) (hKS : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d L → ℝ) + 1) → ℝ)
      (z : Fin (Module.finrank ℝ (MonomialCoord d L → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d L → ℝ) + 1)) ∧
      (∀ i, z i ∈ K) ∧
      hellingerSq volume (gaussianMixture μ θ) (finiteGaussianMixture w z) ≤
        (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
          (L + 1).factorial)) ^ (1 / 2 : ℝ) := by
  let toCoord : Point d → (Fin d → ℝ) := fun u i ↦ u i
  let Kc : Set (Fin d → ℝ) := toCoord '' K
  have htoCoord : Continuous toCoord := by
    unfold toCoord
    fun_prop
  have hKccompact : IsCompact Kc := hKcompact.image htoCoord
  have hKcnonempty : Kc.Nonempty := hKnonempty.image toCoord
  have hθKae : ∀ᵐ a ∂μ, θ a ∈ K :=
    Filter.Eventually.of_forall hθK
  have hθKcae : ∀ᵐ a ∂μ, toCoord (θ a) ∈ Kc := by
    filter_upwards [hθKae] with a ha
    exact ⟨θ a, ha, rfl⟩
  have hint : Integrable
      (fun a ↦ monomialFeature d L (toCoord (θ a))) μ :=
    monomialFeature_integrable_of_compact_support
      μ (fun a ↦ toCoord (θ a))
        (htoCoord.measurable.comp hθmeas) Kc hKccompact hθKcae
  obtain ⟨w, zc, hw, hzcK, hmom⟩ :=
    exists_finite_monomial_moment_matching
      μ (fun a ↦ toCoord (θ a)) Kc hKccompact hKcnonempty hθKcae hint
  have hchoice : ∀ i, ∃ z, z ∈ K ∧ toCoord z = zc i := by
    intro i
    rcases hzcK i with ⟨z, hzK, hz⟩
    exact ⟨z, hzK, hz⟩
  choose z hzK hz using hchoice
  have hmomPoint :
      ∑ i, w i • monomialFeature d L (fun r ↦ z i r) =
        ∫ a, monomialFeature d L (fun r ↦ θ a r) ∂μ := by
    change ∑ i, w i • monomialFeature d L (toCoord (z i)) =
      ∫ a, monomialFeature d L (toCoord (θ a)) ∂μ
    simpa only [hz] using hmom
  refine ⟨w, z, hw, hzK, ?_⟩
  exact hellingerSq_gaussianMixture_finite_moment_matching_le
    μ θ hθmeas w z hw.1 hw.2 hint hmomPoint hS
      (fun a ↦ hKS (θ a) (hθK a)) (fun i ↦ hKS (z i) (hzK i))

end ReweightedNPMLE
