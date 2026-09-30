import ReweightedNPMLE.Gaussian
import ReweightedNPMLE.GaussianMixtureMeasure
import ReweightedNPMLE.Hellinger
import ReweightedNPMLE.PolynomialMoments

/-!
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE

/-- Coefficients of the signed mixture obtained by subtracting two finite
mixtures. -/
def signedMixtureDifferenceWeight {ι κ : Type*}
    (w : ι → ℝ) (v : κ → ℝ) : ι ⊕ κ → ℝ :=
  Sum.elim w (fun j ↦ -v j)

/-- Locations of the signed mixture obtained by concatenating two supports. -/
def signedMixtureDifferenceLocation {d : ℕ} {ι κ : Type*}
    (θ : ι → Point d) (η : κ → Point d) : ι ⊕ κ → Point d :=
  Sum.elim θ η

theorem finiteGaussianMixture_signedDifference
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d)
    (x : Point d) :
    finiteGaussianMixture (signedMixtureDifferenceWeight w v)
        (signedMixtureDifferenceLocation θ η) x =
      finiteGaussianMixture w θ x - finiteGaussianMixture v η x := by
  unfold finiteGaussianMixture signedMixtureDifferenceWeight
    signedMixtureDifferenceLocation
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
  rfl

theorem finiteGaussianMixture_difference_sq_div_density_integrable
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d) :
    Integrable (fun x ↦
      (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
        gaussianDensity d x) := by
  apply (finiteGaussianMixture_sq_div_density_integrable
    (signedMixtureDifferenceWeight w v)
    (signedMixtureDifferenceLocation θ η)).congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change finiteGaussianMixture (signedMixtureDifferenceWeight w v)
          (signedMixtureDifferenceLocation θ η) x ^ 2 / gaussianDensity d x =
        (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
          gaussianDensity d x
    rw [finiteGaussianMixture_signedDifference]

/-- Exact global weighted `L²` identity for the difference of two finite
Gaussian mixtures. -/
theorem integral_finiteGaussianMixture_difference_sq_div_density
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d) :
    ∫ x, (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
        gaussianDensity d x =
      ∑ a, ∑ b,
        signedMixtureDifferenceWeight w v a *
          signedMixtureDifferenceWeight w v b *
            Real.exp (inner ℝ
              (signedMixtureDifferenceLocation θ η a)
              (signedMixtureDifferenceLocation θ η b)) := by
  rw [← integral_finiteGaussianMixture_sq_div_density]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
          gaussianDensity d x =
        finiteGaussianMixture (signedMixtureDifferenceWeight w v)
          (signedMixtureDifferenceLocation θ η) x ^ 2 / gaussianDensity d x
    rw [finiteGaussianMixture_signedDifference]

/-- Remainder after truncating the exponential series in the inner product. -/
noncomputable def pointInnerExpRemainder {d : ℕ} (L : ℕ)
    (θ η : Point d) : ℝ :=
  Real.exp (inner ℝ θ η) - pointTruncatedInnerExp L θ η

/-- Moment matching annihilates every low-order term in the signed
exponential-kernel quadratic form. -/
theorem signedMixture_quadraticForm_eq_remainder_of_moment_match
    {d L : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ θ i r) =
      ∑ j, v j • monomialFeature d L (fun r ↦ η j r)) :
    (∑ a, ∑ b,
        signedMixtureDifferenceWeight w v a *
          signedMixtureDifferenceWeight w v b *
            Real.exp (inner ℝ
              (signedMixtureDifferenceLocation θ η a)
              (signedMixtureDifferenceLocation θ η b))) =
      ∑ a, ∑ b,
        signedMixtureDifferenceWeight w v a *
          signedMixtureDifferenceWeight w v b *
            pointInnerExpRemainder L
              (signedMixtureDifferenceLocation θ η a)
              (signedMixtureDifferenceLocation θ η b) := by
  let c := signedMixtureDifferenceWeight w v
  let z := signedMixtureDifferenceLocation θ η
  have htrunc : ∀ b, ∑ a, c a * pointTruncatedInnerExp L (z a) (z b) = 0 := by
    intro b
    have hmatch := finite_moment_matching_pointTruncatedInnerExp
      w θ v η hmom (z b)
    dsimp [c, z, signedMixtureDifferenceWeight,
      signedMixtureDifferenceLocation]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
    exact sub_eq_zero.mpr hmatch
  have hdouble :
      (∑ a, ∑ b, c a * c b * pointTruncatedInnerExp L (z a) (z b)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    calc
      (∑ a, c a * c b * pointTruncatedInnerExp L (z a) (z b)) =
          c b * ∑ a, c a * pointTruncatedInnerExp L (z a) (z b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 0 := by rw [htrunc b, mul_zero]
  change (∑ a, ∑ b, c a * c b * Real.exp (inner ℝ (z a) (z b))) =
    ∑ a, ∑ b, c a * c b * pointInnerExpRemainder L (z a) (z b)
  rw [show (∑ a, ∑ b, c a * c b * Real.exp (inner ℝ (z a) (z b))) =
      (∑ a, ∑ b, c a * c b * pointInnerExpRemainder L (z a) (z b)) +
        ∑ a, ∑ b, c a * c b * pointTruncatedInnerExp L (z a) (z b) by
    simp only [pointInnerExpRemainder, mul_sub, Finset.sum_sub_distrib]
    ring]
  rw [hdouble, add_zero]

/-- Uniform Taylor bound for the inner-product exponential remainder on a
Euclidean ball. -/
theorem abs_pointInnerExpRemainder_le
    {d L : ℕ} {θ η : Point d} {S : ℝ}
    (hS : 0 ≤ S) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S) :
    |pointInnerExpRemainder L θ η| ≤
      Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial := by
  have hinner : |inner ℝ θ η| ≤ S ^ 2 := by
    calc
      |inner ℝ θ η| ≤ ‖θ‖ * ‖η‖ := abs_real_inner_le_norm θ η
      _ ≤ S * S := mul_le_mul hθ hη (norm_nonneg η) hS
      _ = S ^ 2 := by ring
  simpa only [pointInnerExpRemainder, pointTruncatedInnerExp] using
    real_exp_taylor_remainder_bound L (sq_nonneg S) hinner

/-- Summing the uniform Taylor remainder against signed coefficients costs
the square of their total variation. -/
theorem abs_remainder_quadraticForm_le
    {d L : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (z : ι → Point d) {S : ℝ}
    (hS : 0 ≤ S) (hz : ∀ i, ‖z i‖ ≤ S) :
    |∑ i, ∑ j, c i * c j * pointInnerExpRemainder L (z i) (z j)| ≤
      (∑ i, |c i|) ^ 2 *
        (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := by
  let R := Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial
  have hterm : ∀ i j,
      |c i * c j * pointInnerExpRemainder L (z i) (z j)| ≤
        |c i| * |c j| * R := by
    intro i j
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [R] using
        abs_pointInnerExpRemainder_le (L := L) hS (hz i) (hz j))
      (mul_nonneg (abs_nonneg (c i)) (abs_nonneg (c j)))
  change |∑ i, ∑ j, c i * c j * pointInnerExpRemainder L (z i) (z j)| ≤
    (∑ i, |c i|) ^ 2 * R
  calc
    |∑ i, ∑ j, c i * c j * pointInnerExpRemainder L (z i) (z j)| ≤
        ∑ i, |∑ j, c i * c j * pointInnerExpRemainder L (z i) (z j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |c i * c j * pointInnerExpRemainder L (z i) (z j)| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |c i| * |c j| * R := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = (∑ i, |c i|) ^ 2 * R := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- Global weighted `L²` moment-tail bound for two moment-matched finite
probability mixtures supported in the radius-`S` ball. -/
theorem finite_moment_matching_weightedL2_bound
    {d L : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ j, v j = 1)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ θ i r) =
      ∑ j, v j • monomialFeature d L (fun r ↦ η j r))
    {S : ℝ} (hS : 0 ≤ S) (hθ : ∀ i, ‖θ i‖ ≤ S)
    (hη : ∀ j, ‖η j‖ ≤ S) :
    ∫ x, (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
        gaussianDensity d x ≤
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := by
  let c := signedMixtureDifferenceWeight w v
  let z := signedMixtureDifferenceLocation θ η
  have hz : ∀ a, ‖z a‖ ≤ S := by
    rintro (i | j)
    · exact hθ i
    · exact hη j
  have hcabs : ∑ a, |c a| = 2 := by
    dsimp [c, signedMixtureDifferenceWeight]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, abs_neg]
    have hwabs : (∑ i, |w i|) = 1 := by
      simpa only [abs_of_nonneg (hw _)] using hwsum
    have hvabs : (∑ j, |v j|) = 1 := by
      simpa only [abs_of_nonneg (hv _)] using hvsum
    rw [hwabs, hvabs]
    norm_num
  have hcancel := signedMixture_quadraticForm_eq_remainder_of_moment_match
    w θ v η hmom
  have hrem := abs_remainder_quadraticForm_le (L := L) c z hS hz
  have hrem' :
      |∑ a, ∑ b, c a * c b * pointInnerExpRemainder L (z a) (z b)| ≤
        4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := by
    calc
      _ ≤ (∑ a, |c a|) ^ 2 *
          (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) := hrem
      _ = _ := by simp only [hcabs]; norm_num
  calc
    (∫ x, (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
        gaussianDensity d x) =
        ∑ a, ∑ b, c a * c b * Real.exp (inner ℝ (z a) (z b)) := by
      exact integral_finiteGaussianMixture_difference_sq_div_density w θ v η
    _ = ∑ a, ∑ b, c a * c b * pointInnerExpRemainder L (z a) (z b) :=
      hcancel
    _ ≤ |∑ a, ∑ b, c a * c b * pointInnerExpRemainder L (z a) (z b)| :=
      le_abs_self _
    _ ≤ 4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) / (L + 1).factorial) :=
      hrem'

/-- Squared Hellinger distance between two finite probability mixtures is
bounded by the square root of their explicit exponential-kernel quadratic
form. -/
theorem hellingerSq_finiteGaussianMixture_le_sqrt_quadraticForm
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ j, v j = 1) :
    hellingerSq volume (finiteGaussianMixture w θ) (finiteGaussianMixture v η) ≤
      (∑ a, ∑ b,
        signedMixtureDifferenceWeight w v a *
          signedMixtureDifferenceWeight w v b *
            Real.exp (inner ℝ
              (signedMixtureDifferenceLocation θ η a)
              (signedMixtureDifferenceLocation θ η b))) ^ (1 / 2 : ℝ) := by
  have hpint := finiteGaussianMixture_integrable w θ
  have hqint := finiteGaussianMixture_integrable v η
  have hpmeas : AEStronglyMeasurable (finiteGaussianMixture w θ)
      (volume : Measure (Point d)) :=
    (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
  have hqmeas : AEStronglyMeasurable (finiteGaussianMixture v η)
      (volume : Measure (Point d)) :=
    (continuous_finiteGaussianMixture v η).aestronglyMeasurable
  have hp : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture w θ x :=
    Filter.Eventually.of_forall fun x ↦ (finiteGaussianMixture_pos θ hw hwsum x).le
  have hq : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture v η x :=
    Filter.Eventually.of_forall fun x ↦ (finiteGaussianMixture_pos η hv hvsum x).le
  have hhell := hellingerIntegrand_integrable_of_integrable
    volume (finiteGaussianMixture w θ) (finiteGaussianMixture v η)
    hpmeas hqmeas hp hq hpint hqint
  have hl1 := abs_sub_integrable_of_integrable
    volume (finiteGaussianMixture w θ) (finiteGaussianMixture v η) hpint hqint
  have hdiffmeas : AEStronglyMeasurable
      (fun x ↦ finiteGaussianMixture w θ x - finiteGaussianMixture v η x)
      (volume : Measure (Point d)) :=
    ((continuous_finiteGaussianMixture w θ).sub
      (continuous_finiteGaussianMixture v η)).aestronglyMeasurable
  have hφmeas : AEStronglyMeasurable (gaussianDensity d)
      (volume : Measure (Point d)) :=
    (continuous_gaussianDensity d).aestronglyMeasurable
  have hbound := hellingerSq_le_sqrt_weightedL2
    volume (finiteGaussianMixture w θ) (finiteGaussianMixture v η)
      (gaussianDensity d) hp hq
      hdiffmeas hφmeas
      (Filter.Eventually.of_forall fun x ↦ gaussianDensity_pos d x)
      hhell hl1
      (finiteGaussianMixture_difference_sq_div_density_integrable w θ v η)
      (gaussianDensity_integrable d) (integral_gaussianDensity d)
  rw [integral_finiteGaussianMixture_difference_sq_div_density] at hbound
  exact hbound

/-- Global squared-Hellinger consequence of finite moment matching. -/
theorem hellingerSq_finite_moment_matching_le
    {d L : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (θ : ι → Point d) (v : κ → ℝ) (η : κ → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ j, 0 ≤ v j)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ j, v j = 1)
    (hmom : ∑ i, w i • monomialFeature d L (fun r ↦ θ i r) =
      ∑ j, v j • monomialFeature d L (fun r ↦ η j r))
    {S : ℝ} (hS : 0 ≤ S) (hθ : ∀ i, ‖θ i‖ ≤ S)
    (hη : ∀ j, ‖η j‖ ≤ S) :
    hellingerSq volume (finiteGaussianMixture w θ) (finiteGaussianMixture v η) ≤
      (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (L + 1) /
        (L + 1).factorial)) ^ (1 / 2 : ℝ) := by
  have hH := hellingerSq_finiteGaussianMixture_le_sqrt_quadraticForm
    w θ v η hw hv hwsum hvsum
  rw [← integral_finiteGaussianMixture_difference_sq_div_density] at hH
  have hQnonneg : 0 ≤
      ∫ x, (finiteGaussianMixture w θ x - finiteGaussianMixture v η x) ^ 2 /
        gaussianDensity d x := by
    apply integral_nonneg
    intro x
    exact div_nonneg (sq_nonneg _) (gaussianDensity_pos d x).le
  have hQbound := finite_moment_matching_weightedL2_bound
    w θ v η hw hv hwsum hvsum hmom hS hθ hη
  exact hH.trans (Real.rpow_le_rpow hQnonneg hQbound (by norm_num))

/-- The `L¹` norm of a finite signed Gaussian mixture is bounded by the
`ℓ¹` norm of its coefficients. -/
theorem integral_abs_finiteGaussianMixture_le_sum_abs
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    ∫ x, |finiteGaussianMixture c θ x| ≤ ∑ i, |c i| := by
  have hleft : Integrable (fun x ↦ |finiteGaussianMixture c θ x|) :=
    (finiteGaussianMixture_integrable c θ).abs
  have hright : Integrable (finiteGaussianMixture (fun i ↦ |c i|) θ) :=
    finiteGaussianMixture_integrable (fun i ↦ |c i|) θ
  have hdom : ∀ x,
      |finiteGaussianMixture c θ x| ≤
        finiteGaussianMixture (fun i ↦ |c i|) θ x := by
    intro x
    unfold finiteGaussianMixture
    calc
      |∑ i, c i * gaussianKernel d x (θ i)| ≤
          ∑ i, |c i * gaussianKernel d x (θ i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |c i| * gaussianKernel d x (θ i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_pos (gaussianKernel_pos d x (θ i))]
  calc
    (∫ x, |finiteGaussianMixture c θ x|) ≤
        ∫ x, finiteGaussianMixture (fun i ↦ |c i|) θ x := by
      exact integral_mono hleft hright hdom
    _ = ∑ i, |c i| := integral_finiteGaussianMixture _ _

theorem finiteGaussianMixture_sub_same_locations
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    finiteGaussianMixture w θ x - finiteGaussianMixture v θ x =
      finiteGaussianMixture (fun i ↦ w i - v i) θ x := by
  unfold finiteGaussianMixture
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Rounding only the masses of a finite probability mixture changes squared
Hellinger distance by at most the `ℓ¹` mass error. -/
theorem hellingerSq_finiteGaussianMixture_same_locations_le_weight_l1
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1) :
    hellingerSq volume (finiteGaussianMixture w θ) (finiteGaussianMixture v θ) ≤
      ∑ i, |w i - v i| := by
  have hpint := finiteGaussianMixture_integrable w θ
  have hqint := finiteGaussianMixture_integrable v θ
  have hp : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture w θ x :=
    Filter.Eventually.of_forall fun x ↦ (finiteGaussianMixture_pos θ hw hwsum x).le
  have hq : ∀ᵐ x ∂(volume : Measure (Point d)),
      0 ≤ finiteGaussianMixture v θ x :=
    Filter.Eventually.of_forall fun x ↦ (finiteGaussianMixture_pos θ hv hvsum x).le
  have hhell := hellingerIntegrand_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v θ)
    (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
    (continuous_finiteGaussianMixture v θ).aestronglyMeasurable
    hp hq hpint hqint
  have hl1 := abs_sub_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v θ) hpint hqint
  calc
    hellingerSq volume (finiteGaussianMixture w θ) (finiteGaussianMixture v θ) ≤
        ∫ x, |finiteGaussianMixture w θ x - finiteGaussianMixture v θ x| :=
      hellingerSq_le_integral_abs_sub volume _ _ hp hq hhell hl1
    _ = ∫ x, |finiteGaussianMixture (fun i ↦ w i - v i) θ x| := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change |finiteGaussianMixture w θ x - finiteGaussianMixture v θ x| =
          |finiteGaussianMixture (fun i ↦ w i - v i) θ x|
        rw [finiteGaussianMixture_sub_same_locations]
    _ ≤ ∑ i, |w i - v i| :=
      integral_abs_finiteGaussianMixture_le_sum_abs _ _

theorem sqrt_exp (t : ℝ) :
    Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  exact (Real.exp_half t).symm

theorem sqrt_gaussianKernel {d : ℕ} (x θ : Point d) :
    Real.sqrt (gaussianKernel d x θ) =
      Real.sqrt (gaussianConstant d) * Real.exp (-‖x - θ‖ ^ 2 / 4) := by
  unfold gaussianKernel
  rw [Real.sqrt_mul (gaussianConstant_pos d).le, sqrt_exp]
  congr 2
  ring

theorem sqrt_gaussianKernel_mul {d : ℕ} (x θ η : Point d) :
    Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η) =
      Real.exp (-‖θ - η‖ ^ 2 / 8) *
        gaussianKernel d x ((1 / 2 : ℝ) • (θ + η)) := by
  rw [Real.sqrt_mul (gaussianKernel_pos d x θ).le,
    sqrt_gaussianKernel, sqrt_gaussianKernel]
  unfold gaussianKernel
  have hθ : x - θ =
      (x - (1 / 2 : ℝ) • (θ + η)) - (1 / 2 : ℝ) • (θ - η) := by module
  have hη : x - η =
      (x - (1 / 2 : ℝ) • (θ + η)) + (1 / 2 : ℝ) • (θ - η) := by module
  have hpara := parallelogram_law_with_norm ℝ
    (x - (1 / 2 : ℝ) • (θ + η)) ((1 / 2 : ℝ) • (θ - η))
  have hexp : -‖x - θ‖ ^ 2 / 4 + -‖x - η‖ ^ 2 / 4 =
      -‖θ - η‖ ^ 2 / 8 +
        -‖x - (1 / 2 : ℝ) • (θ + η)‖ ^ 2 / 2 := by
    rw [hθ, hη]
    rw [norm_smul] at hpara
    norm_num at hpara ⊢
    nlinarith
  have hc : Real.sqrt (gaussianConstant d) * Real.sqrt (gaussianConstant d) =
      gaussianConstant d := by
    rw [← pow_two, Real.sq_sqrt (gaussianConstant_pos d).le]
  calc
    (Real.sqrt (gaussianConstant d) * Real.exp (-‖x - θ‖ ^ 2 / 4)) *
        (Real.sqrt (gaussianConstant d) * Real.exp (-‖x - η‖ ^ 2 / 4)) =
        (Real.sqrt (gaussianConstant d) * Real.sqrt (gaussianConstant d)) *
          (Real.exp (-‖x - θ‖ ^ 2 / 4) * Real.exp (-‖x - η‖ ^ 2 / 4)) := by ring
    _ = gaussianConstant d * Real.exp
        (-‖θ - η‖ ^ 2 / 8 +
          -‖x - (1 / 2 : ℝ) • (θ + η)‖ ^ 2 / 2) := by
      rw [hc, ← Real.exp_add, hexp]
    _ = Real.exp (-‖θ - η‖ ^ 2 / 8) *
        (gaussianConstant d *
          Real.exp (-‖x - (1 / 2 : ℝ) • (θ + η)‖ ^ 2 / 2)) := by
      rw [Real.exp_add]
      ring

theorem gaussianKernel_sqrt_product_integrable {d : ℕ} (θ η : Point d) :
    Integrable (fun x : Point d ↦
      Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η)) := by
  apply ((gaussianKernel_integrable d ((1 / 2 : ℝ) • (θ + η))).const_mul
    (Real.exp (-‖θ - η‖ ^ 2 / 8))).congr
  exact Filter.Eventually.of_forall fun x ↦ (sqrt_gaussianKernel_mul x θ η).symm

/-- Exact Hellinger affinity of two translates of the standard Gaussian. -/
theorem hellingerAffinity_gaussianKernel {d : ℕ} (θ η : Point d) :
    hellingerAffinity volume (gaussianKernel d · θ) (gaussianKernel d · η) =
      Real.exp (-‖θ - η‖ ^ 2 / 8) := by
  unfold hellingerAffinity
  calc
    (∫ x : Point d,
        Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η)) =
        ∫ x : Point d, Real.exp (-‖θ - η‖ ^ 2 / 8) *
          gaussianKernel d x ((1 / 2 : ℝ) • (θ + η)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ sqrt_gaussianKernel_mul x θ η
    _ = Real.exp (-‖θ - η‖ ^ 2 / 8) := by
      rw [integral_const_mul, integral_gaussianKernel, mul_one]

/-- Exact squared Hellinger distance between two standard Gaussian
translates. -/
theorem hellingerSq_gaussianKernel {d : ℕ} (θ η : Point d) :
    hellingerSq volume (gaussianKernel d · θ) (gaussianKernel d · η) =
      2 * (1 - Real.exp (-‖θ - η‖ ^ 2 / 8)) := by
  rw [hellingerSq_eq_integrals volume (gaussianKernel d · θ)
    (gaussianKernel d · η)
    (fun x ↦ (gaussianKernel_pos d x θ).le)
    (fun x ↦ (gaussianKernel_pos d x η).le)
    (gaussianKernel_integrable d θ) (gaussianKernel_integrable d η)
    (gaussianKernel_sqrt_product_integrable θ η)]
  rw [integral_gaussianKernel, integral_gaussianKernel,
    hellingerAffinity_gaussianKernel]
  ring

theorem hellingerSq_gaussianKernel_le_norm_sq_div_four {d : ℕ}
    (θ η : Point d) :
    hellingerSq volume (gaussianKernel d · θ) (gaussianKernel d · η) ≤
      ‖θ - η‖ ^ 2 / 4 := by
  rw [hellingerSq_gaussianKernel]
  have hexp := Real.add_one_le_exp (-‖θ - η‖ ^ 2 / 8)
  nlinarith

theorem sqrt_weighted_kernel_product {d : ℕ}
    (a : ℝ) (ha : 0 ≤ a) (x θ η : Point d) :
    Real.sqrt (a * gaussianKernel d x θ) *
        Real.sqrt (a * gaussianKernel d x η) =
      a * Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha,
    Real.sqrt_mul (gaussianKernel_pos d x θ).le]
  have hsqa : Real.sqrt a * Real.sqrt a = a := by
    rw [← pow_two, Real.sq_sqrt ha]
  calc
    Real.sqrt a * Real.sqrt (gaussianKernel d x θ) *
        (Real.sqrt a * Real.sqrt (gaussianKernel d x η)) =
        (Real.sqrt a * Real.sqrt a) *
          (Real.sqrt (gaussianKernel d x θ) *
            Real.sqrt (gaussianKernel d x η)) := by ring
    _ = a * (Real.sqrt (gaussianKernel d x θ) *
        Real.sqrt (gaussianKernel d x η)) := by rw [hsqa]

/-- Joint convexity of the squared Hellinger integrand, specialized to
finite Gaussian mixtures with common weights. -/
theorem sqrt_sub_sq_finiteGaussianMixture_le_sum {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2 ≤
      ∑ i, w i *
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
  have hp : 0 ≤ finiteGaussianMixture w θ x :=
    finiteGaussianMixture_nonneg θ hw x
  have hq : 0 ≤ finiteGaussianMixture w η x :=
    finiteGaussianMixture_nonneg η hw x
  have hcs0 := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (f := fun i ↦ w i * gaussianKernel d x (θ i))
    (g := fun i ↦ w i * gaussianKernel d x (η i))
    (fun i ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le)
    (fun i ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (η i)).le)
  have hcs :
      ∑ i, w i * Real.sqrt
          (gaussianKernel d x (θ i) * gaussianKernel d x (η i)) ≤
        Real.sqrt (finiteGaussianMixture w θ x) *
          Real.sqrt (finiteGaussianMixture w η x) := by
    calc
      ∑ i, w i * Real.sqrt
          (gaussianKernel d x (θ i) * gaussianKernel d x (η i)) =
          ∑ i, Real.sqrt (w i * gaussianKernel d x (θ i)) *
            Real.sqrt (w i * gaussianKernel d x (η i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (sqrt_weighted_kernel_product (w i) (hw i) x (θ i) (η i)).symm
      _ ≤ Real.sqrt (∑ i, w i * gaussianKernel d x (θ i)) *
          Real.sqrt (∑ i, w i * gaussianKernel d x (η i)) := hcs0
      _ = Real.sqrt (finiteGaussianMixture w θ x) *
          Real.sqrt (finiteGaussianMixture w η x) := rfl
  rw [sqrt_sub_sq hp hq]
  simp_rw [sqrt_sub_sq (gaussianKernel_pos d x _).le
    (gaussianKernel_pos d x _).le]
  unfold finiteGaussianMixture
  unfold finiteGaussianMixture at hcs
  rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le)]
  calc
    ∑ i, w i * gaussianKernel d x (θ i) +
          ∑ i, w i * gaussianKernel d x (η i) -
        2 * (Real.sqrt (∑ i, w i * gaussianKernel d x (θ i)) *
          Real.sqrt (∑ i, w i * gaussianKernel d x (η i))) ≤
        ∑ i, w i * gaussianKernel d x (θ i) +
          ∑ i, w i * gaussianKernel d x (η i) -
        2 * ∑ i, w i * Real.sqrt
          (gaussianKernel d x (θ i) * gaussianKernel d x (η i)) := by
      nlinarith
    _ = ∑ i, w i *
        (gaussianKernel d x (θ i) + gaussianKernel d x (η i) -
          2 * Real.sqrt
            (gaussianKernel d x (θ i) * gaussianKernel d x (η i))) := by
      simp_rw [mul_sub, mul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem hellingerSq_finiteGaussianMixture_same_weights_le_sum {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
      ∑ i, w i * hellingerSq volume
        (fun x ↦ gaussianKernel d x (θ i))
        (fun x ↦ gaussianKernel d x (η i)) := by
  have hleft : Integrable (fun x : Point d ↦
      (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2) :=
    hellingerIntegrand_integrable_of_integrable volume
      (finiteGaussianMixture w θ) (finiteGaussianMixture w η)
      (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
      (continuous_finiteGaussianMixture w η).aestronglyMeasurable
      (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg θ hw))
      (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg η hw))
      (finiteGaussianMixture_integrable w θ)
      (finiteGaussianMixture_integrable w η)
  have hcomponent (i : ι) : Integrable (fun x : Point d ↦
      w i * (Real.sqrt (gaussianKernel d x (θ i)) -
        Real.sqrt (gaussianKernel d x (η i))) ^ 2) := by
    apply Integrable.const_mul
    exact hellingerIntegrand_integrable_of_integrable volume
      (fun x ↦ gaussianKernel d x (θ i)) (fun x ↦ gaussianKernel d x (η i))
      ((continuous_gaussianKernel d).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      ((continuous_gaussianKernel d).comp
        (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ (gaussianKernel_pos d x (θ i)).le)
      (Filter.Eventually.of_forall fun x ↦ (gaussianKernel_pos d x (η i)).le)
      (gaussianKernel_integrable d (θ i)) (gaussianKernel_integrable d (η i))
  have hright : Integrable (fun x : Point d ↦
      ∑ i, w i * (Real.sqrt (gaussianKernel d x (θ i)) -
        Real.sqrt (gaussianKernel d x (η i))) ^ 2) :=
    integrable_finsetSum Finset.univ fun i _ ↦ hcomponent i
  unfold hellingerSq
  calc
    (∫ x : Point d, (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2) ≤
        ∫ x : Point d, ∑ i, w i *
          (Real.sqrt (gaussianKernel d x (θ i)) -
            Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
      exact integral_mono hleft hright
        (sqrt_sub_sq_finiteGaussianMixture_le_sum w θ η hw)
    _ = ∑ i, ∫ x : Point d, w i *
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
      exact integral_finsetSum Finset.univ fun i _ ↦ hcomponent i
    _ = ∑ i, w i * ∫ x : Point d,
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]

theorem hellingerSq_finiteGaussianMixture_same_weights_le_location_sq {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
      ∑ i, w i * (‖θ i - η i‖ ^ 2 / 4) := by
  calc
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
        ∑ i, w i * hellingerSq volume
          (fun x ↦ gaussianKernel d x (θ i))
          (fun x ↦ gaussianKernel d x (η i)) :=
      hellingerSq_finiteGaussianMixture_same_weights_le_sum w θ η hw
    _ ≤ ∑ i, w i * (‖θ i - η i‖ ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (hellingerSq_gaussianKernel_le_norm_sq_div_four (θ i) (η i)) (hw i)

theorem hellingerSq_finiteGaussianMixture_location_rounding {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hloc : ∀ i, ‖θ i - η i‖ ≤ ε) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤ ε ^ 2 / 4 := by
  calc
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
        ∑ i, w i * (‖θ i - η i‖ ^ 2 / 4) :=
      hellingerSq_finiteGaussianMixture_same_weights_le_location_sq w θ η hw
    _ ≤ ∑ i, w i * (ε ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      exact div_le_div_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hε).2 (hloc i)) (by norm_num)
    _ = ε ^ 2 / 4 := by
      rw [← Finset.sum_mul, hwsum, one_mul]

theorem finiteGaussianMixture_hellingerIntegrable {d : ℕ}
    {ι : Type*} [Fintype ι] (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    Integrable (fun x : Point d ↦
      (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture v η x)) ^ 2) :=
  hellingerIntegrand_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v η)
    (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
    (continuous_finiteGaussianMixture v η).aestronglyMeasurable
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg θ hw))
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg η hv))
    (finiteGaussianMixture_integrable w θ)
    (finiteGaussianMixture_integrable v η)

/-- Simultaneously rounding every location and every mass gives the two
explicit error terms needed by the finite likelihood-net construction. -/
theorem hellingerSq_finiteGaussianMixture_rounding {d : ℕ}
    {ι : Type*} [Fintype ι] (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hloc : ∀ i, ‖θ i - η i‖ ≤ ε) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture v η) ≤
      ε ^ 2 / 2 + 2 * ∑ i, |w i - v i| := by
  have htri := hellingerSq_triangle_bound volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture w η)
    (finiteGaussianMixture v η)
    (finiteGaussianMixture_hellingerIntegrable w w θ η hw hw)
    (finiteGaussianMixture_hellingerIntegrable w v η η hw hv)
    (finiteGaussianMixture_hellingerIntegrable w v θ η hw hv)
  have hlocH := hellingerSq_finiteGaussianMixture_location_rounding
    w θ η hw hwsum hε hloc
  have hmassH := hellingerSq_finiteGaussianMixture_same_locations_le_weight_l1
    w v η hw hv hwsum hvsum
  calc
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture v η) ≤
        2 * hellingerSq volume (finiteGaussianMixture w θ)
            (finiteGaussianMixture w η) +
          2 * hellingerSq volume (finiteGaussianMixture w η)
            (finiteGaussianMixture v η) := htri
    _ ≤ 2 * (ε ^ 2 / 4) + 2 * ∑ i, |w i - v i| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlocH (by norm_num))
        (mul_le_mul_of_nonneg_left hmassH (by norm_num))
    _ = ε ^ 2 / 2 + 2 * ∑ i, |w i - v i| := by ring

end ReweightedNPMLE
