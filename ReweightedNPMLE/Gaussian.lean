import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE

/-- The ambient Euclidean parameter and observation space. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The exponent remaining after the common centered Gaussian factor is removed. -/
noncomputable def gaussianScore {d : ℕ} (x θ : Point d) : ℝ :=
  inner ℝ x θ - ‖θ‖ ^ 2 / 2

/-- The standard Gaussian normalizing constant in dimension `d`. -/
noncomputable def gaussianConstant (d : ℕ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2)

/-- The standard centered Gaussian density. -/
noncomputable def gaussianDensity (d : ℕ) (x : Point d) : ℝ :=
  gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 2)

/-- The standard Gaussian location kernel. -/
noncomputable def gaussianKernel (d : ℕ) (x θ : Point d) : ℝ :=
  gaussianConstant d * Real.exp (-‖x - θ‖ ^ 2 / 2)

/-- A finitely supported signed Gaussian mixture.  Probability mixtures are
obtained by imposing nonnegative weights with total mass one. -/
noncomputable def finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) (x : Point d) : ℝ :=
  ∑ i, w i * gaussianKernel d x (θ i)

theorem gaussianConstant_pos (d : ℕ) : 0 < gaussianConstant d := by
  unfold gaussianConstant
  positivity

theorem gaussianDensity_pos (d : ℕ) (x : Point d) : 0 < gaussianDensity d x := by
  unfold gaussianDensity
  exact mul_pos (gaussianConstant_pos d) (Real.exp_pos _)

theorem gaussianKernel_pos (d : ℕ) (x θ : Point d) : 0 < gaussianKernel d x θ := by
  unfold gaussianKernel
  exact mul_pos (gaussianConstant_pos d) (Real.exp_pos _)

theorem continuous_gaussianScore (d : ℕ) :
    Continuous fun z : Point d × Point d ↦ gaussianScore z.1 z.2 := by
  unfold gaussianScore
  fun_prop

theorem continuous_gaussianDensity (d : ℕ) : Continuous (gaussianDensity d) := by
  unfold gaussianDensity
  fun_prop

theorem continuous_gaussianKernel (d : ℕ) :
    Continuous fun z : Point d × Point d ↦ gaussianKernel d z.1 z.2 := by
  unfold gaussianKernel
  fun_prop

theorem continuous_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) : Continuous (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture gaussianKernel
  fun_prop

theorem finiteGaussianMixture_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    0 ≤ finiteGaussianMixture w θ x := by
  unfold finiteGaussianMixture
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le

theorem finiteGaussianMixture_pos {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (x : Point d) :
    0 < finiteGaussianMixture w θ x := by
  have hsumpos : 0 < ∑ i, w i := by rw [hsum]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) ↦ hw i).mp hsumpos
  unfold finiteGaussianMixture
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j) (gaussianKernel_pos d x (θ j)).le
  · exact ⟨i, Finset.mem_univ i, mul_pos hi (gaussianKernel_pos d x (θ i))⟩

/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring

/-- The centered multivariate Gaussian density is Bochner integrable. -/
theorem gaussianDensity_integrable (d : ℕ) : Integrable (gaussianDensity d) := by
  change Integrable (fun x : Point d ↦
    gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 2))
  apply Integrable.const_mul
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Point d) (b := (1 / 2 : ℂ)) (by norm_num) 0 0
  have hn := hc.norm
  have heq : (fun x : Point d ↦ Real.exp (-‖x‖ ^ 2 / 2)) =
      fun x ↦ ‖Complex.exp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 +
        0 * (inner ℝ (0 : Point d) x : ℂ))‖ := by
    funext x
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.zero_im,
      zero_mul, add_zero]
    congr 1
    norm_num
    norm_cast
    ring
  rw [heq]
  exact hn

/-- The normalization chosen in `gaussianConstant` makes the centered
Gaussian density integrate to one in every finite dimension. -/
theorem integral_gaussianDensity (d : ℕ) :
    ∫ x : Point d, gaussianDensity d x = 1 := by
  simp only [gaussianDensity]
  rw [integral_const_mul]
  have hfun : (fun x : Point d ↦ Real.exp (-‖x‖ ^ 2 / 2)) =
      fun x ↦ Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
    funext x
    congr 1
    ring
  rw [hfun,
    GaussianFourier.integral_rexp_neg_mul_sq_norm
      (show (0 : ℝ) < 1 / 2 by norm_num)]
  simp only [gaussianConstant]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]
  rw [← Real.rpow_add (by positivity : 0 < 2 * Real.pi)]
  rw [finrank_euclideanSpace_fin]
  rw [show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ

/-- Every translated Gaussian kernel integrates to one. -/
theorem integral_gaussianKernel (d : ℕ) (θ : Point d) :
    ∫ x : Point d, gaussianKernel d x θ = 1 := by
  change (∫ x : Point d, gaussianDensity d (x - θ)) = 1
  rw [integral_sub_right_eq_self, integral_gaussianDensity]

/-- Every finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_integrable {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    Integrable (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture
  exact integrable_finsetSum Finset.univ fun i _ ↦
    (gaussianKernel_integrable d (θ i)).const_mul (w i)

/-- The integral of a finite Gaussian mixture is the sum of its weights. -/
theorem integral_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    ∫ x, finiteGaussianMixture w θ x = ∑ i, w i := by
  unfold finiteGaussianMixture
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_gaussianKernel, mul_one]
  · intro i _
    exact (gaussianKernel_integrable d (θ i)).const_mul (w i)

/-- Pointwise completed-square identity behind the Gaussian-mixture
weighted `L²` calculation. -/
theorem gaussianKernel_product_div_density {d : ℕ} (x θ η : Point d) :
    gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x =
      Real.exp (inner ℝ θ η) * gaussianDensity d (x - (θ + η)) := by
  rw [gaussianKernel_eq_density_mul_exp_score,
    gaussianKernel_eq_density_mul_exp_score]
  have hd : gaussianDensity d x ≠ 0 := (gaussianDensity_pos d x).ne'
  field_simp
  unfold gaussianDensity gaussianScore
  calc
    gaussianConstant d * Real.exp (-‖x‖ ^ 2 / 2) *
          Real.exp (inner ℝ x θ - ‖θ‖ ^ 2 / 2) *
          Real.exp (inner ℝ x η - ‖η‖ ^ 2 / 2) =
        gaussianConstant d * Real.exp
          ((-‖x‖ ^ 2 / 2) + (inner ℝ x θ - ‖θ‖ ^ 2 / 2) +
            (inner ℝ x η - ‖η‖ ^ 2 / 2)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = gaussianConstant d * Real.exp
          (inner ℝ θ η + (-‖x - (θ + η)‖ ^ 2 / 2)) := by
      congr 2
      rw [norm_sub_sq_real, norm_add_sq_real, real_inner_comm η θ, inner_add_right]
      ring
    _ = Real.exp (inner ℝ θ η) *
          (gaussianConstant d * Real.exp (-‖x - (θ + η)‖ ^ 2 / 2)) := by
      rw [Real.exp_add]
      ring

/-- Exact Gaussian overlap identity used to turn moment matching into a
global weighted `L²`, hence Hellinger, approximation. -/
theorem integral_gaussianKernel_product_div_density {d : ℕ} (θ η : Point d) :
    ∫ x : Point d,
        gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x =
      Real.exp (inner ℝ θ η) := by
  calc
    (∫ x : Point d,
        gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x) =
        ∫ x : Point d,
          Real.exp (inner ℝ θ η) * gaussianDensity d (x - (θ + η)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        gaussianKernel_product_div_density x θ η
    _ = Real.exp (inner ℝ θ η) *
        ∫ x : Point d, gaussianDensity d (x - (θ + η)) := by
      rw [integral_const_mul]
    _ = Real.exp (inner ℝ θ η) := by
      rw [integral_sub_right_eq_self, integral_gaussianDensity, mul_one]

/-- The Gaussian overlap integrand is integrable. -/
theorem gaussianKernel_product_div_density_integrable
    {d : ℕ} (θ η : Point d) :
    Integrable (fun x ↦
      gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x) := by
  apply ((gaussianDensity_integrable d).comp_sub_right (θ + η)).const_mul
    (Real.exp (inner ℝ θ η)) |>.congr
  exact Filter.Eventually.of_forall fun x ↦
    (gaussianKernel_product_div_density x θ η).symm

/-- Expanding the square of a finite signed mixture gives a double sum of
Gaussian overlap terms. -/
theorem finiteGaussianMixture_sq_div_density_eq_sum_overlap
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x =
      ∑ i, ∑ j, c i * c j *
        (gaussianKernel d x (θ i) * gaussianKernel d x (θ j) /
          gaussianDensity d x) := by
  unfold finiteGaussianMixture
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Weighted square error of a finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_sq_div_density_integrable
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    Integrable (fun x ↦
      (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x) := by
  apply (integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦
      (gaussianKernel_product_div_density_integrable (θ i) (θ j)).const_mul
        (c i * c j)).congr
  exact Filter.Eventually.of_forall fun x ↦
    (finiteGaussianMixture_sq_div_density_eq_sum_overlap c θ x).symm

/-- Exact finite quadratic-form identity for a signed Gaussian mixture.  It
is the finite-support version of the manuscript's global `Q_m` identity. -/
theorem integral_finiteGaussianMixture_sq_div_density
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    ∫ x, (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x =
      ∑ i, ∑ j, c i * c j * Real.exp (inner ℝ (θ i) (θ j)) := by
  calc
    (∫ x, (finiteGaussianMixture c θ x) ^ 2 / gaussianDensity d x) =
        ∫ x, ∑ i, ∑ j, c i * c j *
          (gaussianKernel d x (θ i) * gaussianKernel d x (θ j) /
            gaussianDensity d x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        finiteGaussianMixture_sq_div_density_eq_sum_overlap c θ x
    _ = ∑ i, ∑ j, ∫ x, c i * c j *
          (gaussianKernel d x (θ i) * gaussianKernel d x (θ j) /
            gaussianDensity d x) := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ]
        intro j hj
        exact (gaussianKernel_product_div_density_integrable (θ i) (θ j)).const_mul
          (c i * c j)
      · intro i hi
        exact integrable_finsetSum Finset.univ fun j hj ↦
          (gaussianKernel_product_div_density_integrable (θ i) (θ j)).const_mul
            (c i * c j)
    _ = ∑ i, ∑ j, c i * c j * Real.exp (inner ℝ (θ i) (θ j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_gaussianKernel_product_div_density]

/-- If `x` and `θ` lie in fixed balls, their Gaussian score is uniformly bounded. -/
theorem abs_gaussianScore_le {d : ℕ} {x θ : Point d} {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) :
    |gaussianScore x θ| ≤ T * S + S ^ 2 / 2 := by
  have hinner : |inner ℝ x θ| ≤ T * S := by
    exact (abs_real_inner_le_norm x θ).trans
      (mul_le_mul hx hθ (norm_nonneg θ) hT)
  have hsq : ‖θ‖ ^ 2 / 2 ≤ S ^ 2 / 2 := by
    exact div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg θ) hS).2 hθ) (by norm_num)
  calc
    |gaussianScore x θ| = |inner ℝ x θ - ‖θ‖ ^ 2 / 2| := rfl
    _ ≤ |inner ℝ x θ| + |‖θ‖ ^ 2 / 2| := abs_sub _ _
    _ = |inner ℝ x θ| + ‖θ‖ ^ 2 / 2 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ ‖θ‖ ^ 2 / 2)]
    _ ≤ T * S + S ^ 2 / 2 := add_le_add hinner hsq

theorem exp_neg_scoreBound_le_exp_score {d : ℕ} {x θ : Point d} {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) :
    Real.exp (-(T * S + S ^ 2 / 2)) ≤ Real.exp (gaussianScore x θ) := by
  apply Real.exp_le_exp.mpr
  exact neg_le_of_abs_le (abs_gaussianScore_le hT hS hx hθ)

/-- A convex finite mixture of Gaussian exponentials is uniformly bounded away from zero. -/
theorem exp_neg_scoreBound_le_mixtureNormalizer
    {d n : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (θ : ι → Point d) (x : Fin n → Point d)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hθ : ∀ j, ‖θ j‖ ≤ S) (hx : ∀ i, ‖x i‖ ≤ T) (i : Fin n) :
    Real.exp (-(T * S + S ^ 2 / 2)) ≤
      ∑ j, p j * Real.exp (gaussianScore (x i) (θ j)) := by
  have hterm : ∀ j, p j * Real.exp (-(T * S + S ^ 2 / 2)) ≤
      p j * Real.exp (gaussianScore (x i) (θ j)) := by
    intro j
    exact mul_le_mul_of_nonneg_left
      (exp_neg_scoreBound_le_exp_score hT hS (hx i) (hθ j)) (hp j)
  calc
    Real.exp (-(T * S + S ^ 2 / 2)) =
        (∑ j, p j) * Real.exp (-(T * S + S ^ 2 / 2)) := by rw [hsum, one_mul]
    _ = ∑ j, p j * Real.exp (-(T * S + S ^ 2 / 2)) := by rw [Finset.sum_mul]
    _ ≤ ∑ j, p j * Real.exp (gaussianScore (x i) (θ j)) :=
      Finset.sum_le_sum fun j _ ↦ hterm j

end ReweightedNPMLE
