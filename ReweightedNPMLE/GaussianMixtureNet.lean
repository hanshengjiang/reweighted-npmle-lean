import ReweightedNPMLE.GaussianMixtureMeasureHellinger
import ReweightedNPMLE.Localization

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE

/-- Moving a Gaussian location by at most `ε` changes its score by at most
`(T + S) ε` on the radius-`T` observation ball when both locations lie in the
radius-`S` parameter ball. -/
theorem abs_gaussianScore_sub_le {d : ℕ} (x θ η : Point d)
    {T S ε : ℝ} (hT : 0 ≤ T) (_hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S)
    (hθη : ‖θ - η‖ ≤ ε) :
    |gaussianScore x θ - gaussianScore x η| ≤ (T + S) * ε := by
  have hinner : |inner ℝ x (θ - η)| ≤ T * ε := by
    exact (abs_real_inner_le_norm x (θ - η)).trans
      (mul_le_mul hx hθη (norm_nonneg _) hT)
  have hnormsum : ‖θ‖ + ‖η‖ ≤ 2 * S := by linarith
  have hnormdiff : |‖θ‖ ^ 2 - ‖η‖ ^ 2| ≤ 2 * S * ε := by
    calc
      |‖θ‖ ^ 2 - ‖η‖ ^ 2| = |‖θ‖ - ‖η‖| * (‖θ‖ + ‖η‖) := by
        rw [show ‖θ‖ ^ 2 - ‖η‖ ^ 2 =
          (‖θ‖ - ‖η‖) * (‖θ‖ + ‖η‖) by ring, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ ‖θ‖ + ‖η‖)]
      _ ≤ ‖θ - η‖ * (‖θ‖ + ‖η‖) :=
        mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le θ η) (by positivity)
      _ ≤ ε * (2 * S) :=
        mul_le_mul hθη hnormsum (by positivity) hε
      _ = 2 * S * ε := by ring
  have hscore : gaussianScore x θ - gaussianScore x η =
      inner ℝ x (θ - η) - (‖θ‖ ^ 2 - ‖η‖ ^ 2) / 2 := by
    simp only [gaussianScore, inner_sub_right]
    ring
  rw [hscore]
  calc
    |inner ℝ x (θ - η) - (‖θ‖ ^ 2 - ‖η‖ ^ 2) / 2| ≤
        |inner ℝ x (θ - η)| + |(‖θ‖ ^ 2 - ‖η‖ ^ 2) / 2| :=
      abs_sub _ _
    _ = |inner ℝ x (θ - η)| + |‖θ‖ ^ 2 - ‖η‖ ^ 2| / 2 := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    _ ≤ T * ε + (2 * S * ε) / 2 :=
      add_le_add hinner (div_le_div_of_nonneg_right hnormdiff (by norm_num))
    _ = (T + S) * ε := by ring

/-- A relative error at most `δ ≤ 1/2` implies the standard `2δ`
log-density error. -/
theorem abs_log_sub_log_le_two_mul_of_relative_error
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hrel : |a / b - 1| ≤ δ) :
    |Real.log a - Real.log b| ≤ 2 * δ := by
  let u := a / b - 1
  have hu : |u| ≤ δ := hrel
  have hu1 : |u| < 1 := hu.trans_lt (hδhalf.trans_lt (by norm_num))
  have hden : 0 < 1 - |u| := sub_pos.mpr hu1
  calc
    |Real.log a - Real.log b| = |Real.log (a / b)| := by
      rw [Real.log_div ha.ne' hb.ne']
    _ = |Real.log (1 + u)| := by
      congr 2
      dsimp [u]
      ring
    _ ≤ |u| / (1 - |u|) := abs_log_one_add_le hu1
    _ ≤ 2 * δ := by
      rw [div_le_iff₀ hden]
      nlinarith [abs_nonneg u]

/-- Two-sided multiplicative exponential bounds imply an additive log bound. -/
theorem abs_log_sub_log_le_of_exp_bounds {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hlower : Real.exp (-c) * b ≤ a)
    (hupper : a ≤ Real.exp c * b) :
    |Real.log a - Real.log b| ≤ c := by
  have hlowerLog : Real.log (Real.exp (-c) * b) ≤ Real.log a :=
    (Real.log_le_log_iff (mul_pos (Real.exp_pos _) hb) ha).2 hlower
  have hupperLog : Real.log a ≤ Real.log (Real.exp c * b) :=
    (Real.log_le_log_iff ha (mul_pos (Real.exp_pos _) hb)).2 hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne', Real.log_exp] at hlowerLog hupperLog
  rw [abs_le]
  constructor <;> linarith

/-- Exact factorization of a finite Gaussian mixture into the centered
Gaussian density and its exponential-score normalizer. -/
theorem finiteGaussianMixture_eq_density_mul_score_sum
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    finiteGaussianMixture w θ x = gaussianDensity d x *
      ∑ i, w i * Real.exp (gaussianScore x (θ i)) := by
  unfold finiteGaussianMixture
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianKernel_eq_density_mul_exp_score]
  ring

/-- Pointwise multiplicative comparison of two translated Gaussian kernels
whose locations are close. -/
theorem gaussianKernel_location_exp_bounds {d : ℕ} (x θ η : Point d)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S)
    (hθη : ‖θ - η‖ ≤ ε) :
    Real.exp (-((T + S) * ε)) * gaussianKernel d x θ ≤
        gaussianKernel d x η ∧
      gaussianKernel d x η ≤
        Real.exp ((T + S) * ε) * gaussianKernel d x θ := by
  let c := (T + S) * ε
  have hscore := abs_gaussianScore_sub_le x θ η hT hS hε hx hθ hη hθη
  have hdiff :
      -c ≤ gaussianScore x η - gaussianScore x θ ∧
        gaussianScore x η - gaussianScore x θ ≤ c := by
    dsimp [c]
    have habs : |gaussianScore x η - gaussianScore x θ| ≤ (T + S) * ε := by
      simpa only [abs_sub_comm] using hscore
    exact (abs_le.mp habs)
  have hkernel : gaussianKernel d x η = gaussianKernel d x θ *
      Real.exp (gaussianScore x η - gaussianScore x θ) := by
    rw [gaussianKernel_eq_density_mul_exp_score,
      gaussianKernel_eq_density_mul_exp_score, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  constructor
  · calc
      Real.exp (-c) * gaussianKernel d x θ =
          gaussianKernel d x θ * Real.exp (-c) := by ring
      _ ≤ gaussianKernel d x θ *
          Real.exp (gaussianScore x η - gaussianScore x θ) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiff.1)
          (gaussianKernel_pos d x θ).le
      _ = gaussianKernel d x η := hkernel.symm
  · rw [hkernel]
    calc
      gaussianKernel d x θ *
          Real.exp (gaussianScore x η - gaussianScore x θ) ≤
          gaussianKernel d x θ * Real.exp c :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiff.2)
          (gaussianKernel_pos d x θ).le
      _ = Real.exp c * gaussianKernel d x θ := by ring

/-- Moving all locations of a nonnegative finite mixture gives the same
two-sided exponential comparison as for each component. -/
theorem finiteGaussianMixture_location_exp_bounds
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε) :
    Real.exp (-((T + S) * ε)) * finiteGaussianMixture w θ x ≤
        finiteGaussianMixture w η x ∧
      finiteGaussianMixture w η x ≤
        Real.exp ((T + S) * ε) * finiteGaussianMixture w θ x := by
  have hcomponent (i : ι) := gaussianKernel_location_exp_bounds
    x (θ i) (η i) hT hS hε hx (hθ i) (hη i) (hθη i)
  constructor
  · unfold finiteGaussianMixture
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      Real.exp (-((T + S) * ε)) * (w i * gaussianKernel d x (θ i)) =
          w i * (Real.exp (-((T + S) * ε)) * gaussianKernel d x (θ i)) := by
        ring
      _ ≤ w i * gaussianKernel d x (η i) :=
        mul_le_mul_of_nonneg_left (hcomponent i).1 (hw i)
  · unfold finiteGaussianMixture
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      w i * gaussianKernel d x (η i) ≤
          w i * (Real.exp ((T + S) * ε) * gaussianKernel d x (θ i)) :=
        mul_le_mul_of_nonneg_left (hcomponent i).2 (hw i)
      _ = Real.exp ((T + S) * ε) *
          (w i * gaussianKernel d x (θ i)) := by ring

/-- Uniform local log-density error caused by rounding the locations of a
finite probability mixture. -/
theorem abs_log_finiteGaussianMixture_location_rounding_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε) :
    |Real.log (finiteGaussianMixture w η x) -
        Real.log (finiteGaussianMixture w θ x)| ≤ (T + S) * ε := by
  have hb := finiteGaussianMixture_location_exp_bounds
    w θ η x hw hT hS hε hx hθ hη hθη
  exact abs_log_sub_log_le_of_exp_bounds
    (finiteGaussianMixture_pos η hw hwsum x)
    (finiteGaussianMixture_pos θ hw hwsum x) hb.1 hb.2

/-- Rounding the weights of a finite mixture produces a relative density
error controlled by the `ℓ¹` weight error and the local Gaussian score
envelope. -/
theorem abs_finiteGaussianMixture_weight_relative_error_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) :
    |finiteGaussianMixture v θ x / finiteGaussianMixture w θ x - 1| ≤
      Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| := by
  let B := T * S + S ^ 2 / 2
  let A := ∑ i, w i * Real.exp (gaussianScore x (θ i))
  let C := ∑ i, v i * Real.exp (gaussianScore x (θ i))
  have hscore (i : ι) : |gaussianScore x (θ i)| ≤ B := by
    simpa only [B] using abs_gaussianScore_le hT hS hx (hθ i)
  have hA : Real.exp (-B) ≤ A := by
    calc
      Real.exp (-B) = (∑ i, w i) * Real.exp (-B) := by rw [hwsum, one_mul]
      _ = ∑ i, w i * Real.exp (-B) := by rw [Finset.sum_mul]
      _ ≤ ∑ i, w i * Real.exp (gaussianScore x (θ i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_of_abs_le (hscore i))) (hw i)
      _ = A := rfl
  have hApos : 0 < A := (Real.exp_pos (-B)).trans_le hA
  have hCA : |C - A| ≤ Real.exp B * ∑ i, |v i - w i| := by
    calc
      |C - A| = |∑ i, (v i - w i) * Real.exp (gaussianScore x (θ i))| := by
        dsimp only [C, A]
        rw [← Finset.sum_sub_distrib]
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, |(v i - w i) * Real.exp (gaussianScore x (θ i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |v i - w i| * Real.exp (gaussianScore x (θ i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ ∑ i, |v i - w i| * Real.exp B := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr ((le_abs_self _).trans (hscore i)))
          (abs_nonneg _)
      _ = Real.exp B * ∑ i, |v i - w i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hratio :
      finiteGaussianMixture v θ x / finiteGaussianMixture w θ x = C / A := by
    rw [finiteGaussianMixture_eq_density_mul_score_sum,
      finiteGaussianMixture_eq_density_mul_score_sum]
    exact mul_div_mul_left C A (gaussianDensity_pos d x).ne'
  rw [hratio, div_sub_one hApos.ne', abs_div, abs_of_pos hApos]
  calc
    |C - A| / A ≤
        (Real.exp B * ∑ i, |v i - w i|) / Real.exp (-B) := by
      exact div_le_div₀ (by positivity) hCA (Real.exp_pos _) hA
    _ = Real.exp (2 * B) * ∑ i, |v i - w i| := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      calc
        (Real.exp B * ∑ i, |v i - w i|) * Real.exp (- -B) =
            (Real.exp B * Real.exp (- -B)) * ∑ i, |v i - w i| := by ring
        _ = Real.exp (B + - -B) * ∑ i, |v i - w i| := by rw [← Real.exp_add]
        _ = Real.exp (2 * B) * ∑ i, |v i - w i| := by congr 2 <;> ring
    _ = Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| := rfl

/-- Uniform local log-density error caused by rounding only the weights. -/
theorem abs_log_finiteGaussianMixture_weight_rounding_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S)
    (hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2) :
    |Real.log (finiteGaussianMixture v θ x) -
        Real.log (finiteGaussianMixture w θ x)| ≤
      2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
        ∑ i, |v i - w i| := by
  let δ := Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i|
  have hδ : 0 ≤ δ := by positivity
  have hlog := abs_log_sub_log_le_two_mul_of_relative_error
    (finiteGaussianMixture_pos θ hv hvsum x)
    (finiteGaussianMixture_pos θ hw hwsum x) hδ
    (by simpa only [δ] using hsmall)
    (abs_finiteGaussianMixture_weight_relative_error_le
      w v θ x hw hwsum hT hS hx hθ)
  simpa only [δ, mul_assoc] using hlog

/-- Combined local log-density estimate for simultaneously rounding the
locations and the weights of a finite probability mixture. -/
theorem abs_log_finiteGaussianMixture_rounding_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2) :
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (finiteGaussianMixture w θ x)| ≤
      (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| := by
  have hloc := abs_log_finiteGaussianMixture_location_rounding_le
    w θ η x hw hwsum hT hS hε hx hθ hη hθη
  have hmass := abs_log_finiteGaussianMixture_weight_rounding_le
    w v η x hw hv hwsum hvsum hT hS hx hη hsmall
  calc
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (finiteGaussianMixture w θ x)| =
        |(Real.log (finiteGaussianMixture v η x) -
            Real.log (finiteGaussianMixture w η x)) +
          (Real.log (finiteGaussianMixture w η x) -
            Real.log (finiteGaussianMixture w θ x))| := by ring
    _ ≤ |Real.log (finiteGaussianMixture v η x) -
          Real.log (finiteGaussianMixture w η x)| +
        |Real.log (finiteGaussianMixture w η x) -
          Real.log (finiteGaussianMixture w θ x)| := abs_add_le _ _
    _ ≤ 2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| + (T + S) * ε := add_le_add hmass hloc
    _ = (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| := by ring

/-- End-to-end local log estimate: a relative moment-matching error followed
by location and weight rounding. -/
theorem abs_log_rounded_finiteGaussianMixture_sub_gaussianMixture_le
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w v : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S ε ρ : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2)
    (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hrelative :
      |finiteGaussianMixture w θ x / gaussianMixture μ ϑ x - 1| ≤ ρ) :
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (gaussianMixture μ ϑ x)| ≤
      (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| + 2 * ρ := by
  have hround := abs_log_finiteGaussianMixture_rounding_le
    w v θ η x hw hv hwsum hvsum hT hS hε hx hθ hη hθη hweightSmall
  have hmoment := abs_log_sub_log_le_two_mul_of_relative_error
    (finiteGaussianMixture_pos θ hw hwsum x)
    (gaussianMixture_pos μ ϑ hϑmeas x) hρ hρhalf hrelative
  calc
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (gaussianMixture μ ϑ x)| =
        |(Real.log (finiteGaussianMixture v η x) -
            Real.log (finiteGaussianMixture w θ x)) +
          (Real.log (finiteGaussianMixture w θ x) -
            Real.log (gaussianMixture μ ϑ x))| := by ring
    _ ≤ |Real.log (finiteGaussianMixture v η x) -
          Real.log (finiteGaussianMixture w θ x)| +
        |Real.log (finiteGaussianMixture w θ x) -
          Real.log (gaussianMixture μ ϑ x)| := abs_add_le _ _
    _ ≤ ((T + S) * ε +
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            ∑ i, |v i - w i|) + 2 * ρ := add_le_add hround hmoment
    _ = (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| + 2 * ρ := by ring

theorem gaussianMixture_finite_hellingerIntegrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w : ι → ℝ) (z : ι → Point d) (hw : ∀ i, 0 ≤ w i) :
    MeasureTheory.Integrable (fun x : Point d ↦
      (Real.sqrt (gaussianMixture μ ϑ x) -
        Real.sqrt (finiteGaussianMixture w z x)) ^ 2) := by
  exact hellingerIntegrand_integrable_of_integrable MeasureTheory.volume
    (gaussianMixture μ ϑ) (finiteGaussianMixture w z)
    (gaussianMixture_integrable μ ϑ hϑmeas).aestronglyMeasurable
    (continuous_finiteGaussianMixture w z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (gaussianMixture_pos μ ϑ hϑmeas x).le)
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg z hw))
    (gaussianMixture_integrable μ ϑ hϑmeas)
    (finiteGaussianMixture_integrable w z)

/-- Global Hellinger transfer from a moment-matched finite mixture to its
location-and-weight-rounded version. -/
theorem hellingerSq_gaussianMixture_finite_rounding_le
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {ε q : ℝ} (hε : 0 ≤ ε) (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hbase : hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
      (finiteGaussianMixture w θ) ≤ q) :
    hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture v η) ≤
      2 * q + ε ^ 2 + 4 * ∑ i, |w i - v i| := by
  have htri := hellingerSq_triangle_bound MeasureTheory.volume
    (gaussianMixture μ ϑ) (finiteGaussianMixture w θ)
    (finiteGaussianMixture v η)
    (gaussianMixture_finite_hellingerIntegrable μ ϑ hϑmeas w θ hw)
    (finiteGaussianMixture_hellingerIntegrable w v θ η hw hv)
    (gaussianMixture_finite_hellingerIntegrable μ ϑ hϑmeas v η hv)
  have hround := hellingerSq_finiteGaussianMixture_rounding
    w v θ η hw hv hwsum hvsum hε hθη
  calc
    hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture v η) ≤
        2 * hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
            (finiteGaussianMixture w θ) +
          2 * hellingerSq MeasureTheory.volume
            (finiteGaussianMixture w θ) (finiteGaussianMixture v η) := htri
    _ ≤ 2 * q + 2 * (ε ^ 2 / 2 + 2 * ∑ i, |w i - v i|) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by norm_num))
        (mul_le_mul_of_nonneg_left hround (by norm_num))
    _ = 2 * q + ε ^ 2 + 4 * ∑ i, |w i - v i| := by ring

/-- One Carathéodory mixture simultaneously supplies the global Hellinger
approximation and the uniform local relative-density approximation used in
the finite likelihood-net construction. -/
theorem exists_finite_gaussianMixture_simultaneous_approximation
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T) :
    ∃ (w : Fin (Module.finrank ℝ
          (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (z : Fin (Module.finrank ℝ
          (MonomialCoord d (2 * L) → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, z i ∈ K) ∧
      hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
          (finiteGaussianMixture w z) ≤
        (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          (2 * L + 1).factorial)) ^ (1 / 2 : ℝ) ∧
      ∀ x ∈ X,
        |finiteGaussianMixture w z x / gaussianMixture μ ϑ x - 1| ≤
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            ((T * S + S ^ 2 / 2) ^ (L + 1) / (L + 1).factorial) := by
  let B := T * S + S ^ 2 / 2
  let toCoord : Point d → (Fin d → ℝ) := fun u i ↦ u i
  let Kc : Set (Fin d → ℝ) := toCoord '' K
  have htoCoord : Continuous toCoord := by
    unfold toCoord
    fun_prop
  have hKccompact : IsCompact Kc := hKcompact.image htoCoord
  have hKcnonempty : Kc.Nonempty := hKnonempty.image toCoord
  have hϑKae : ∀ᵐ a ∂μ, ϑ a ∈ K := Filter.Eventually.of_forall hϑK
  have hϑKcae : ∀ᵐ a ∂μ, toCoord (ϑ a) ∈ Kc := by
    filter_upwards [hϑKae] with a ha
    exact ⟨ϑ a, ha, rfl⟩
  have hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (toCoord (ϑ a))) μ :=
    monomialFeature_integrable_of_compact_support
      μ (fun a ↦ toCoord (ϑ a)) (htoCoord.measurable.comp hϑmeas)
        Kc hKccompact hϑKcae
  obtain ⟨w, zc, hw, hzcK, hmom⟩ :=
    exists_finite_monomial_moment_matching
      μ (fun a ↦ toCoord (ϑ a)) Kc hKccompact hKcnonempty hϑKcae hint
  have hchoice : ∀ i, ∃ z, z ∈ K ∧ toCoord z = zc i := by
    intro i
    rcases hzcK i with ⟨z, hzK, hz⟩
    exact ⟨z, hzK, hz⟩
  choose z hzK hz using hchoice
  have hmomPoint :
      ∑ i, w i • monomialFeature d (2 * L) (fun r ↦ z i r) =
        ∫ a, monomialFeature d (2 * L) (fun r ↦ ϑ a r) ∂μ := by
    change ∑ i, w i • monomialFeature d (2 * L) (toCoord (z i)) =
      ∫ a, monomialFeature d (2 * L) (toCoord (ϑ a)) ∂μ
    simpa only [hz] using hmom
  have hH := hellingerSq_gaussianMixture_finite_moment_matching_le
    μ ϑ hϑmeas w z hw.1 hw.2 hint hmomPoint hS
      (fun a ↦ hKbound (ϑ a) (hϑK a))
      (fun i ↦ hKbound (z i) (hzK i))
  refine ⟨w, z, hw, hzK, ?_, ?_⟩
  · simpa only [Nat.mul_add, Nat.add_eq, Nat.cast_ofNat] using hH
  · intro x hxX
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    have hscorePoint (u : Point d) (hu : u ∈ K) :
        |gaussianScore x u| ≤ B := by
      simpa only [B] using
        abs_gaussianScore_le hT hS (hXbound x hxX) (hKbound u hu)
    have hexpOriginal : MeasureTheory.Integrable
        (fun a ↦ Real.exp (gaussianScore x (ϑ a))) μ := by
      apply MeasureTheory.Integrable.of_bound
        (((Real.continuous_exp.comp (continuous_gaussianScore d)).measurable.comp
          (measurable_const.prodMk hϑmeas)).aestronglyMeasurable)
        (Real.exp B)
      exact Filter.Eventually.of_forall fun a ↦ by
        change |Real.exp (gaussianScore x (ϑ a))| ≤ Real.exp B
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr
          ((le_abs_self _).trans (hscorePoint (ϑ a) (hϑK a)))
    have hscorec : ∀ u ∈ Kc,
        |coordinateGaussianScore (fun i ↦ x i) u| ≤ B := by
      rintro u ⟨y, hyK, rfl⟩
      simpa only [toCoord, gaussianScore_eq_coordinateGaussianScore] using
        hscorePoint y hyK
    have hexpc : MeasureTheory.Integrable
        (fun a ↦ Real.exp
          (coordinateGaussianScore (fun i ↦ x i) (toCoord (ϑ a)))) μ := by
      apply hexpOriginal.congr
      exact Filter.Eventually.of_forall fun a ↦ by
        simpa only [toCoord] using
          congrArg Real.exp (gaussianScore_eq_coordinateGaussianScore x (ϑ a))
    have hzB : ∀ i,
        |coordinateGaussianScore (fun j ↦ x j) (zc i)| ≤ B :=
      fun i ↦ hscorec (zc i) (hzcK i)
    have hϑB : ∀ᵐ a ∂μ,
        |coordinateGaussianScore (fun j ↦ x j) (toCoord (ϑ a))| ≤ B := by
      filter_upwards [hϑKcae] with a ha
      exact hscorec (toCoord (ϑ a)) ha
    have habs := gaussian_score_exp_average_error_of_moment_match
      μ (fun a ↦ toCoord (ϑ a)) w zc hw hint hmom
        (fun i ↦ x i) hB hzB hϑB hexpc
    have hlower := exp_neg_bound_le_gaussian_score_average
      μ (fun a ↦ toCoord (ϑ a)) (fun i ↦ x i) hϑB hexpc
    have herror :
        |(∑ i, w i * Real.exp
            (coordinateGaussianScore (fun j ↦ x j) (zc i))) -
          ∫ a, Real.exp
            (coordinateGaussianScore (fun j ↦ x j) (toCoord (ϑ a))) ∂μ| ≤
          2 * Real.exp B * (B ^ (L + 1) / (L + 1).factorial) := by
      calc
        _ ≤ 2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := habs
        _ = 2 * Real.exp B * (B ^ (L + 1) / (L + 1).factorial) := by ring
    have hrel := relative_error_of_exp_lower_bound
      (a := ∑ i, w i * Real.exp
        (coordinateGaussianScore (fun j ↦ x j) (zc i)))
      (b := ∫ a, Real.exp
        (coordinateGaussianScore (fun j ↦ x j) (toCoord (ϑ a))) ∂μ)
      (B := B) (r := B ^ (L + 1) / (L + 1).factorial) hlower herror
    have hsum :
        (∑ i, w i * Real.exp
          (coordinateGaussianScore (fun j ↦ x j) (zc i))) =
          ∑ i, w i * Real.exp (gaussianScore x (z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hz i, ← gaussianScore_eq_coordinateGaussianScore]
    have hintEq :
        (∫ a, Real.exp
          (coordinateGaussianScore (fun i ↦ x i) (toCoord (ϑ a))) ∂μ) =
          ∫ a, Real.exp (gaussianScore x (ϑ a)) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ by
        simpa only [toCoord] using
          (congrArg Real.exp
            (gaussianScore_eq_coordinateGaussianScore x (ϑ a))).symm
    rw [hsum, hintEq] at hrel
    have hden : gaussianMixture μ ϑ x = gaussianDensity d x *
        ∫ a, Real.exp (gaussianScore x (ϑ a)) ∂μ := by
      unfold gaussianMixture
      simp_rw [gaussianKernel_eq_density_mul_exp_score]
      exact MeasureTheory.integral_const_mul _ _
    rw [finiteGaussianMixture_eq_density_mul_score_sum, hden,
      mul_div_mul_left _ _ (gaussianDensity_pos d x).ne']
    simpa only [B] using hrel

end ReweightedNPMLE
