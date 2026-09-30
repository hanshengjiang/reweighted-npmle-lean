import Mathlib.Probability.Distributions.Gaussian.Multivariate
import ReweightedNPMLE.GammaDistribution
import ReweightedNPMLE.Gaussian
import ReweightedNPMLE.GaussianMixtureMeasure

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace ReweightedNPMLE

/-- The standard one-dimensional Gaussian two-sided Chernoff bound. -/
theorem gaussianReal_two_sided_tail {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real {x : ℝ | |x| > t} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hmgfPos :
      ∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 1 =
        Real.exp (t ^ 2 / 2) := by
    change mgf id (gaussianReal 0 1) t = _
    rw [mgf_id_gaussianReal]
    norm_num
  have hmgfNeg :
      ∫ x : ℝ, Real.exp (-t * x) ∂gaussianReal 0 1 =
        Real.exp (t ^ 2 / 2) := by
    change mgf id (gaussianReal 0 1) (-t) = _
    rw [mgf_id_gaussianReal]
    norm_num
  have hu := exponential_markov_upper (gaussianReal 0 1) id ht
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t) (c := t)
  have hl := exponential_markov_lower (gaussianReal 0 1) id ht
    (by simpa only [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-t))) (c := t)
  simp only [id_eq] at hu hl
  rw [hmgfPos] at hu
  rw [hmgfNeg] at hl
  have hu' : (gaussianReal 0 1).real {x : ℝ | t ≤ x} ≤
      Real.exp (-t ^ 2 / 2) := by
    calc
      _ ≤ Real.exp (-t * t) * Real.exp (t ^ 2 / 2) := hu
      _ = Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hl' : (gaussianReal 0 1).real {x : ℝ | x ≤ -t} ≤
      Real.exp (-t ^ 2 / 2) := by
    calc
      _ ≤ Real.exp (-t * t) * Real.exp (t ^ 2 / 2) := hl
      _ = Real.exp (-t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsubset : {x : ℝ | |x| > t} ⊆
      {x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t} := by
    intro x hx
    change t < |x| at hx
    change (t ≤ x) ∨ (x ≤ -t)
    by_cases hx0 : 0 ≤ x
    · left
      rw [abs_of_nonneg hx0] at hx
      exact hx.le
    · right
      have hxneg : x < 0 := lt_of_not_ge hx0
      rw [abs_of_neg hxneg] at hx
      linarith
  calc
    (gaussianReal 0 1).real {x : ℝ | |x| > t} ≤
        (gaussianReal 0 1).real
          ({x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t}) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ (gaussianReal 0 1).real {x : ℝ | t ≤ x} +
        (gaussianReal 0 1).real {x : ℝ | x ≤ -t} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / 2) + Real.exp (-t ^ 2 / 2) := add_le_add hu' hl'
    _ = 2 * Real.exp (-t ^ 2 / 2) := by ring

/-- A union bound for the largest coordinate of a standard Gaussian product. -/
theorem gaussianProduct_max_coordinate_tail (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).real
        {z : Fin d → ℝ | ∃ i, |z i| > t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by
  let μd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  have hcoord (i : Fin d) :
      μd.real {z : Fin d → ℝ | |z i| > t} ≤
        2 * Real.exp (-t ^ 2 / 2) := by
    have hmeas : MeasurableSet {x : ℝ | |x| > t} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hpre : {z : Fin d → ℝ | |z i| > t} =
        Function.eval i ⁻¹' {x : ℝ | |x| > t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin d ↦ gaussianReal 0 1) i).measure_preimage
        hmeas.nullMeasurableSet]
    exact gaussianReal_two_sided_tail ht
  have hset : {z : Fin d → ℝ | ∃ i, |z i| > t} =
      ⋃ i : Fin d, {z : Fin d → ℝ | |z i| > t} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  change μd.real {z : Fin d → ℝ | ∃ i, |z i| > t} ≤ _
  rw [hset]
  calc
    μd.real (⋃ i : Fin d, {z : Fin d → ℝ | |z i| > t}) ≤
        ∑ i : Fin d, μd.real {z : Fin d → ℝ | |z i| > t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin d, 2 * Real.exp (-t ^ 2 / 2) :=
      Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = 2 * d * Real.exp (-t ^ 2 / 2) := by simp; ring

/-- If every coordinate is at most `t` in absolute value, the Euclidean norm
is at most `sqrt d * t`. -/
theorem euclidean_norm_le_sqrt_card_mul_of_abs_coord_le
    {d : ℕ} (z : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hz : ∀ i, |z i| ≤ t) :
    ‖WithLp.toLp 2 z‖ ≤ Real.sqrt d * t := by
  have hsum : ∑ i : Fin d, (z i) ^ 2 ≤ ∑ _i : Fin d, t ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := (sq_le_sq₀ (abs_nonneg (z i)) ht).2 (hz i)
    simpa only [sq_abs] using hi
  have hnormsq : ‖WithLp.toLp 2 z‖ ^ 2 ≤ (d : ℝ) * t ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using hsum
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrtd : (Real.sqrt (d : ℝ)) ^ 2 = d :=
    Real.sq_sqrt (Nat.cast_nonneg d)
  have hrhs : 0 ≤ Real.sqrt d * t := mul_nonneg hsqrt ht
  apply (sq_le_sq₀ (norm_nonneg _) hrhs).1
  rw [mul_pow, hsqrtd]
  exact hnormsq

/-- Euclidean norm tail for a standard Gaussian product. -/
theorem gaussianProduct_euclidean_norm_tail (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).real
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by
  have hsubset :
      {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} ⊆
        {z : Fin d → ℝ | ∃ i, |z i| > t} := by
    intro z hz
    by_contra h
    simp only [Set.mem_setOf_eq, not_exists, not_lt] at h
    exact (not_le_of_gt hz)
      (euclidean_norm_le_sqrt_card_mul_of_abs_coord_le z ht.le h)
  exact (measureReal_mono hsubset (by finiteness)).trans
    (gaussianProduct_max_coordinate_tail d ht)

/-- Union bound for the maximum Euclidean norm among `n` independent
standard Gaussian product vectors. -/
theorem gaussianSample_max_euclidean_norm_tail (n d : ℕ)
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n ↦
      Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1))).real
        {z : Fin n → (Fin d → ℝ) |
          ∃ k, ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} ≤
      2 * n * d * Real.exp (-t ^ 2 / 2) := by
  let μd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  let μn : Measure (Fin n → (Fin d → ℝ)) :=
    Measure.pi (fun _ : Fin n ↦ μd)
  have hcoord (k : Fin n) :
      μn.real {z : Fin n → (Fin d → ℝ) |
          ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} ≤
        2 * d * Real.exp (-t ^ 2 / 2) := by
    have hmeas : MeasurableSet
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} := by
      exact measurableSet_lt measurable_const (by fun_prop)
    have hpre :
        {z : Fin n → (Fin d → ℝ) |
          ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} =
        Function.eval k ⁻¹'
          {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin n ↦ μd) k).measure_preimage
        hmeas.nullMeasurableSet]
    exact gaussianProduct_euclidean_norm_tail d ht
  have hset :
      {z : Fin n → (Fin d → ℝ) |
          ∃ k, ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} =
        ⋃ k : Fin n,
          {z : Fin n → (Fin d → ℝ) |
            ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  change μn.real
      {z : Fin n → (Fin d → ℝ) |
        ∃ k, ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} ≤ _
  rw [hset]
  calc
    μn.real (⋃ k : Fin n,
        {z : Fin n → (Fin d → ℝ) |
          ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t}) ≤
        ∑ k : Fin n, μn.real
          {z : Fin n → (Fin d → ℝ) |
            ‖WithLp.toLp 2 (z k)‖ > Real.sqrt d * t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin n, 2 * d * Real.exp (-t ^ 2 / 2) :=
      Finset.sum_le_sum fun k _ ↦ hcoord k
    _ = 2 * n * d * Real.exp (-t ^ 2 / 2) := by simp; ring

/-- The density used throughout the formalization induces mathlib's bundled
standard Gaussian law on Euclidean space. -/
theorem withDensity_gaussianDensity_eq_stdGaussian (d : ℕ) :
    volume.withDensity (fun x : Point d ↦ ENNReal.ofReal (gaussianDensity d x)) =
      stdGaussian (Point d) := by
  let ν : Measure (Point d) :=
    volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianDensity d x))
  letI : IsProbabilityMeasure ν := IsProbabilityMeasure.mk (by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (gaussianDensity_integrable d)
        (Filter.Eventually.of_forall fun x ↦ (gaussianDensity_pos d x).le),
      integral_gaussianDensity]
    norm_num)
  change ν = stdGaussian (Point d)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_apply]
  change (∫ x : Point d,
    Complex.exp ((inner ℝ x t : ℂ) * Complex.I) ∂ν) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((continuous_gaussianDensity d).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x ↦ by simp)]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_pos d _).le,
    Complex.real_smul]
  simp_rw [gaussianDensity, Complex.ofReal_mul, Complex.ofReal_exp]
  simp_rw [mul_assoc, ← Complex.exp_add]
  rw [integral_const_mul]
  have hfun : (fun a : Point d ↦
      Complex.exp ((- ‖a‖ ^ 2 / 2 : ℝ) +
        (inner ℝ a t : ℂ) * Complex.I)) =
      fun a : Point d ↦ Complex.exp
        (-(1 / 2 : ℂ) * (‖a‖ : ℂ) ^ 2 +
          Complex.I * (inner ℝ t a : ℂ)) := by
    funext a
    congr 1
    rw [real_inner_comm a t]
    push_cast
    ring
  rw [hfun, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := Point d) (b := (1 / 2 : ℂ)) (by norm_num) Complex.I t]
  rw [finrank_euclideanSpace_fin]
  have hbase : (↑Real.pi / (1 / 2) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbase, show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by
    push_cast
    rfl]
  rw [← Complex.ofReal_cpow (by positivity)]
  have hnorm : gaussianConstant d *
      (2 * Real.pi) ^ ((d : ℝ) / 2) = 1 := by
    unfold gaussianConstant
    rw [← Real.rpow_add (by positivity : 0 < 2 * Real.pi)]
    convert Real.rpow_zero (2 * Real.pi) using 1 <;> ring
  rw [← mul_assoc, ← Complex.ofReal_mul, hnorm, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.I_sq]
  ring

/-- Translating the standard Gaussian law produces the measure whose density
is the Gaussian location kernel. -/
theorem map_stdGaussian_add_eq_withDensity_gaussianKernel
    {d : ℕ} (θ : Point d) :
    (stdGaussian (Point d)).map (fun z ↦ θ + z) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianKernel d x θ)) := by
  rw [← withDensity_gaussianDensity_eq_stdGaussian d]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  let e : Point d ≃ᵐ Point d := MeasurableEquiv.addLeft θ
  have he : MeasurePreserving e volume volume :=
    measurePreserving_add_left volume θ
  have hmeas : Measurable (fun x : Point d ↦
      ENNReal.ofReal (gaussianKernel d x θ)) := by
    exact ((continuous_gaussianKernel d).comp
      (continuous_id.prodMk continuous_const)).measurable.ennreal_ofReal
  have hchange := he.setLIntegral_comp_preimage hs hmeas
  change (∫⁻ x in (fun z : Point d ↦ θ + z) ⁻¹' s,
      ENNReal.ofReal (gaussianDensity d x)) =
    ∫⁻ x in s, ENNReal.ofReal (gaussianKernel d x θ)
  calc
    _ = ∫⁻ x in (fun z : Point d ↦ θ + z) ⁻¹' s,
        ENNReal.ofReal (gaussianKernel d (θ + x) θ) := by
      apply setLIntegral_congr_fun (hs.preimage (by fun_prop))
      intro x _
      unfold gaussianKernel gaussianDensity
      congr 2
      simp
    _ = _ := by
      simpa only [e, MeasurableEquiv.coe_addLeft] using hchange

/-- Sampling law obtained by drawing a location from `μ`, an independent
standard Gaussian vector, and adding them. -/
noncomputable def gaussianLocationMixtureLaw
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (ϑ : Θ → Point d) : Measure (Point d) :=
  (μ.prod (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1))).map
    (fun q ↦ ϑ q.1 + WithLp.toLp 2 q.2)

theorem measurable_gaussianLocationMixtureSample
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ) :
    Measurable (fun q : Θ × (Fin d → ℝ) ↦
      ϑ q.1 + WithLp.toLp 2 q.2) := by
  fun_prop

/-- The generative Gaussian location-mixture law is exactly the measure
obtained by using `gaussianMixture` as a density with respect to volume. -/
theorem gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ) :
    gaussianLocationMixtureLaw μ ϑ =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianMixture μ ϑ x)) := by
  let γd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  let shift : Θ × (Fin d → ℝ) → Point d :=
    fun q ↦ ϑ q.1 + WithLp.toLp 2 q.2
  have hshift : Measurable shift :=
    measurable_gaussianLocationMixtureSample ϑ hϑmeas
  ext s hs
  rw [gaussianLocationMixtureLaw, Measure.map_apply hshift hs,
    Measure.prod_apply (hs.preimage hshift), withDensity_apply _ hs]
  have hslice : ∀ a : Θ,
      γd {z | ϑ a + WithLp.toLp 2 z ∈ s} =
        ∫⁻ x in s, ENNReal.ofReal (gaussianKernel d x (ϑ a)) := by
    intro a
    have hmap : γd.map (fun z ↦ ϑ a + WithLp.toLp 2 z) =
        volume.withDensity
          (fun x ↦ ENNReal.ofReal (gaussianKernel d x (ϑ a))) := by
      rw [show (fun z : Fin d → ℝ ↦ ϑ a + WithLp.toLp 2 z) =
          (fun x : Point d ↦ ϑ a + x) ∘ WithLp.toLp 2 by rfl,
        ← Measure.map_map (measurable_const_add (ϑ a)) (by fun_prop)]
      rw [show γd.map (WithLp.toLp 2) = stdGaussian (Point d) by
        simpa only [γd] using
          (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d)),
        map_stdGaussian_add_eq_withDensity_gaussianKernel]
    have hsmap := congrArg (fun m : Measure (Point d) ↦ m s) hmap
    have hza : Measurable (fun z : Fin d → ℝ ↦
        ϑ a + WithLp.toLp 2 z) :=
      (measurable_const_add (ϑ a)).comp (by fun_prop)
    change (γd.map (fun z ↦ ϑ a + WithLp.toLp 2 z)) s = _ at hsmap
    rw [Measure.map_apply hza hs] at hsmap
    change γd ((fun z ↦ ϑ a + WithLp.toLp 2 z) ⁻¹' s) =
      (volume.withDensity
        (fun x ↦ ENNReal.ofReal (gaussianKernel d x (ϑ a)))) s at hsmap
    rw [withDensity_apply _ hs] at hsmap
    exact hsmap
  change (∫⁻ a, γd {z | ϑ a + WithLp.toLp 2 z ∈ s} ∂μ) = _
  simp_rw [hslice]
  let F : Θ → Point d → ℝ≥0∞ := fun a x ↦
    s.indicator (fun y ↦ ENNReal.ofReal (gaussianKernel d y (ϑ a))) x
  have hFmeas : Measurable (Function.uncurry F) := by
    apply Measurable.indicator
    · exact ((continuous_gaussianKernel d).measurable.comp
        (measurable_snd.prodMk (hϑmeas.comp measurable_fst))).ennreal_ofReal
    · exact hs.preimage measurable_snd
  have hswap := lintegral_lintegral_swap
    (μ := μ) (ν := volume) hFmeas.aemeasurable
  have hmix (x : Point d) :
      ENNReal.ofReal (gaussianMixture μ ϑ x) =
        ∫⁻ a, ENNReal.ofReal (gaussianKernel d x (ϑ a)) ∂μ := by
    unfold gaussianMixture
    exact ofReal_integral_eq_lintegral_ofReal
      (gaussianKernel_comp_integrable μ ϑ hϑmeas x)
      (Filter.Eventually.of_forall fun a ↦
        (gaussianKernel_pos d x (ϑ a)).le)
  calc
    _ = ∫⁻ a, ∫⁻ x, F a x ∂volume ∂μ := by
      simp only [F, lintegral_indicator hs]
    _ = ∫⁻ x, ∫⁻ a, F a x ∂μ ∂volume := hswap
    _ = ∫⁻ x in s, ENNReal.ofReal (gaussianMixture μ ϑ x) := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ s
      · simp only [F, Set.indicator_of_mem hx]
        exact (hmix x).symm
      · simp only [F, Set.indicator_of_notMem hx, lintegral_zero]

theorem gaussianLocationMixtureLaw_isProbability
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ) :
    IsProbabilityMeasure (gaussianLocationMixtureLaw μ ϑ) := by
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianLocationMixtureSample ϑ hϑmeas).aemeasurable

/-- A compactly bounded random location shifts the standard Gaussian radius
threshold by at most `S`. -/
theorem gaussianLocationMixtureLaw_radius_tail
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    {S t : ℝ} (hϑS : ∀ a, ‖ϑ a‖ ≤ S) (ht : 0 < t) :
    (gaussianLocationMixtureLaw μ ϑ).real
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by
  let γd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  let shift : Θ × (Fin d → ℝ) → Point d :=
    fun q ↦ ϑ q.1 + WithLp.toLp 2 q.2
  have hshift : Measurable shift :=
    measurable_gaussianLocationMixtureSample ϑ hϑmeas
  have hbad : MeasurableSet {x : Point d | ‖x‖ > S + Real.sqrt d * t} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have htail : MeasurableSet
      {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hsubset : shift ⁻¹' {x : Point d | ‖x‖ > S + Real.sqrt d * t} ⊆
      Set.univ ×ˢ
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} := by
    intro q hq
    have hsum : ‖shift q‖ ≤ ‖ϑ q.1‖ + ‖WithLp.toLp 2 q.2‖ :=
      norm_add_le _ _
    have hnoise : Real.sqrt d * t < ‖WithLp.toLp 2 q.2‖ := by
      by_contra h
      have hle : ‖WithLp.toLp 2 q.2‖ ≤ Real.sqrt d * t := le_of_not_gt h
      have : ‖shift q‖ ≤ S + Real.sqrt d * t :=
        hsum.trans (add_le_add (hϑS q.1) hle)
      exact (not_le_of_gt hq) this
    exact ⟨Set.mem_univ _, hnoise⟩
  change ((μ.prod γd).map shift).real
      {x : Point d | ‖x‖ > S + Real.sqrt d * t} ≤ _
  rw [map_measureReal_apply hshift hbad]
  calc
    (μ.prod γd).real
        (shift ⁻¹' {x : Point d | ‖x‖ > S + Real.sqrt d * t}) ≤
        (μ.prod γd).real (Set.univ ×ˢ
          {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t}) :=
      measureReal_mono hsubset (by finiteness)
    _ = μ.real Set.univ * γd.real
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} :=
      measureReal_prod_prod _ _
    _ = γd.real
        {z : Fin d → ℝ | ‖WithLp.toLp 2 z‖ > Real.sqrt d * t} := by simp
    _ ≤ 2 * d * Real.exp (-t ^ 2 / 2) :=
      gaussianProduct_euclidean_norm_tail d ht

/-- Radius union bound for `n` independent draws from any compactly bounded
Gaussian location mixture. -/
theorem gaussianLocationMixtureSample_max_radius_tail
    {d n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    {S t : ℝ} (hϑS : ∀ a, ‖ϑ a‖ ≤ S) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n ↦ gaussianLocationMixtureLaw μ ϑ)).real
        {x : Fin n → Point d |
          ∃ k, ‖x k‖ > S + Real.sqrt d * t} ≤
      2 * n * d * Real.exp (-t ^ 2 / 2) := by
  let ν := gaussianLocationMixtureLaw μ ϑ
  letI : IsProbabilityMeasure ν :=
    gaussianLocationMixtureLaw_isProbability μ ϑ hϑmeas
  let νn : Measure (Fin n → Point d) := Measure.pi (fun _ : Fin n ↦ ν)
  have hcoord (k : Fin n) :
      νn.real {x : Fin n → Point d |
          ‖x k‖ > S + Real.sqrt d * t} ≤
        2 * d * Real.exp (-t ^ 2 / 2) := by
    have hmeas : MeasurableSet
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} :=
      measurableSet_lt measurable_const continuous_norm.measurable
    have hpre : {x : Fin n → Point d |
        ‖x k‖ > S + Real.sqrt d * t} =
      Function.eval k ⁻¹'
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin n ↦ ν) k).measure_preimage
        hmeas.nullMeasurableSet]
    exact gaussianLocationMixtureLaw_radius_tail μ ϑ hϑmeas hϑS ht
  have hset : {x : Fin n → Point d |
      ∃ k, ‖x k‖ > S + Real.sqrt d * t} =
      ⋃ k : Fin n,
        {x : Fin n → Point d | ‖x k‖ > S + Real.sqrt d * t} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  change νn.real {x : Fin n → Point d |
      ∃ k, ‖x k‖ > S + Real.sqrt d * t} ≤ _
  rw [hset]
  calc
    νn.real (⋃ k : Fin n,
        {x : Fin n → Point d | ‖x k‖ > S + Real.sqrt d * t}) ≤
        ∑ k : Fin n, νn.real
          {x : Fin n → Point d | ‖x k‖ > S + Real.sqrt d * t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _k : Fin n, 2 * d * Real.exp (-t ^ 2 / 2) :=
      Finset.sum_le_sum fun k _ ↦ hcoord k
    _ = 2 * n * d * Real.exp (-t ^ 2 / 2) := by simp; ring

end ReweightedNPMLE
