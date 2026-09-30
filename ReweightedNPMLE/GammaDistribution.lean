import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ReweightedNPMLE.GammaBounds
import Mathlib.Tactic

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

namespace ReweightedNPMLE

private theorem gammaPDF_toReal {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (gammaPDF a r x).toReal = gammaPDFReal a r x := by
  rw [gammaPDF]
  exact ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)

/-- The basic Gamma-kernel integrability lemma on the positive half-line. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ ↦ x ^ (a - 1) * Real.exp (-(r * x))) (Ioi 0) := by
  let f : ℝ → ℝ := fun y ↦ Real.exp (-y) * y ^ (a - 1)
  have hcomp : IntegrableOn (fun x ↦ f (r * x)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff f 0 hr).2
    simpa [f] using Real.GammaIntegral_convergent ha
  have hrpow : r ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hscaled := hcomp.const_mul (r ^ (a - 1))⁻¹
  apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
  intro x hx
  dsimp [f]
  rw [Real.mul_rpow hr.le hx.le]
  field_simp

/-- Exponential moments below the rate are integrable under a Gamma law. -/
theorem integrable_exp_mul_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ Real.exp (t * x)) (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x ↦ Real.exp (t * x))
    (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  have hsupport : (fun x ↦ Real.exp (t * x) * gammaPDFReal a r x) =
      Set.indicator (Ici (0 : ℝ)) (fun x ↦
        (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x)))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [gammaPDFReal, if_pos hx]
      have hxIci : x ∈ Ici (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxIci]
      have hexp : Real.exp (t * x) * Real.exp (-(r * x)) =
          Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (t * x) *
            (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
            (r ^ a / Real.Gamma a) * x ^ (a - 1) *
              (Real.exp (t * x) * Real.exp (-(r * x))) := by ring
        _ = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]; ring
    · have hxmem : x ∉ Ici (0 : ℝ) := hx
      simp [gammaPDFReal, hx, hxmem]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  rw [hsupport, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)).const_mul _

/-- The (uncentered) moment-generating integral of a shape--rate Gamma law. -/
theorem integral_exp_mul_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂gammaMeasure a r =
      r ^ a / Real.Gamma a * (1 / (r - t)) ^ a * Real.Gamma a := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x, (gammaPDF a r x).toReal * Real.exp (t * x)) = _
    simp_rw [gammaPDF_toReal ha hr]
    have hsupport : (Set.indicator (Ici (0 : ℝ)) fun x ↦
        gammaPDFReal a r x * Real.exp (t * x)) =
        (fun x ↦ gammaPDFReal a r x * Real.exp (t * x)) := by
      funext x
      by_cases hx : x ∈ Ici (0 : ℝ)
      · exact Set.indicator_of_mem hx _
      · have hxneg : x < 0 := not_le.mp hx
        simp [hx, gammaPDFReal, if_neg (not_le.mpr hxneg)]
    rw [← hsupport, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    have hfun : ∫ x in Ioi (0 : ℝ), gammaPDFReal a r x * Real.exp (t * x) =
        ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxnonneg : 0 ≤ x := hx.le
      simp only [gammaPDFReal, if_pos hxnonneg]
      have hexp : Real.exp (-(r * x)) * Real.exp (t * x) =
          Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) *
            Real.exp (t * x) =
            (r ^ a / Real.Gamma a) * x ^ (a - 1) *
              (Real.exp (-(r * x)) * Real.exp (t * x)) := by ring
        _ = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]; ring
    rw [hfun, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)]
    ring
  · exact (measurable_gammaPDFReal a r).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top

/-- Closed form of the Gamma moment-generating function. -/
theorem gamma_mgf {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂gammaMeasure a r = (r / (r - t)) ^ a := by
  rw [integral_exp_mul_gammaMeasure ha hr ht]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  calc
    r ^ a / Real.Gamma a * (1 / (r - t)) ^ a * Real.Gamma a =
        r ^ a * (1 / (r - t)) ^ a := by field_simp
    _ = (r * (1 / (r - t))) ^ a := by
      rw [Real.mul_rpow hr.le (by positivity)]
    _ = (r / (r - t)) ^ a := by simp [div_eq_mul_inv]

/-- A quadratically weighted exponential moment below the Gamma rate is
integrable.  This is the Tonelli/Fubini input for normalized-Gamma second
moments. -/
theorem integrable_sq_mul_exp_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (t * x))
      (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (t * x))
    (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  have hfun : (fun x : ℝ ↦
      (x ^ 2 * Real.exp (t * x)) * gammaPDFReal a r x) =
      Set.indicator (Ioi (0 : ℝ)) (fun x ↦
        (r ^ a / Real.Gamma a) *
          (x ^ (a + 1) * Real.exp (-((r - t) * x)))) := by
    funext x
    by_cases hx : 0 < x
    · have hxmem : x ∈ Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxmem]
      simp only [gammaPDFReal, if_pos hx.le]
      have hrpow : x ^ 2 * x ^ (a - 1) = x ^ (a + 1) := by
        calc
          x ^ 2 * x ^ (a - 1) = x ^ (2 : ℝ) * x ^ (a - 1) := by
            congr 1
            exact (Real.rpow_natCast x 2).symm
          _ = x ^ ((2 : ℝ) + (a - 1)) := (Real.rpow_add hx _ _).symm
          _ = x ^ (a + 1) := by ring_nf
      have hexp : Real.exp (t * x) * Real.exp (-(r * x)) =
          Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hrpow, ← hexp]
      ring
    · have hxmem : x ∉ Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_notMem hxmem]
      have hxle : x ≤ 0 := le_of_not_gt hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hxneg : x < 0 := lt_of_le_of_ne hxle hx0
        simp [gammaPDFReal, if_neg (not_le.mpr hxneg)]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]
  have hbase := integrableOn_rpow_mul_exp_neg_mul_Ioi
    (by linarith : 0 < a + 2) (sub_pos.mpr ht)
  have hshape : a + 2 - 1 = a + 1 := by ring
  rw [hshape] at hbase
  exact hbase.const_mul _

/-- Closed form of the quadratically weighted Gamma exponential moment. -/
theorem integral_sq_mul_exp_gammaMeasure {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x : ℝ, x ^ 2 * Real.exp (t * x) ∂gammaMeasure a r =
      a * (a + 1) * r ^ a * (1 / (r - t)) ^ (a + 2) := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x : ℝ,
        (gammaPDF a r x).toReal * (x ^ 2 * Real.exp (t * x))) = _
    simp_rw [gammaPDF_toReal ha hr]
    have hsupport : (Set.indicator (Ioi (0 : ℝ)) fun x ↦
        gammaPDFReal a r x * (x ^ 2 * Real.exp (t * x))) =
        (fun x ↦ gammaPDFReal a r x * (x ^ 2 * Real.exp (t * x))) := by
      funext x
      by_cases hx : 0 < x
      · have hxmem : x ∈ Ioi (0 : ℝ) := hx
        exact Set.indicator_of_mem hxmem _
      · have hxmem : x ∉ Ioi (0 : ℝ) := hx
        rw [Set.indicator_of_notMem hxmem]
        have hxle : x ≤ 0 := le_of_not_gt hx
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hxneg : x < 0 := lt_of_le_of_ne hxle hx0
          simp [gammaPDFReal, if_neg (not_le.mpr hxneg)]
    rw [← hsupport, integral_indicator measurableSet_Ioi]
    have hfun : ∫ x in Ioi (0 : ℝ),
        gammaPDFReal a r x * (x ^ 2 * Real.exp (t * x)) =
        ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
          (x ^ (a + 1) * Real.exp (-((r - t) * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxpos : 0 < x := hx
      simp only [gammaPDFReal, if_pos hxpos.le]
      have hrpow : x ^ (a - 1) * x ^ 2 = x ^ (a + 1) := by
        calc
          x ^ (a - 1) * x ^ 2 = x ^ (a - 1) * x ^ (2 : ℝ) := by
            congr 1
            exact (Real.rpow_natCast x 2).symm
          _ = x ^ ((a - 1) + (2 : ℝ)) :=
            (Real.rpow_add hxpos _ _).symm
          _ = x ^ (a + 1) := by ring_nf
      have hexp : Real.exp (-(r * x)) * Real.exp (t * x) =
          Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hrpow, ← hexp]
      ring
    rw [hfun, integral_const_mul]
    have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (by linarith : 0 < a + 2) (sub_pos.mpr ht)
    have hshape : a + 2 - 1 = a + 1 := by ring
    rw [hshape] at hgamma
    rw [hgamma]
    have hG2 : Real.Gamma (a + 2) =
        (a + 1) * a * Real.Gamma a := by
      rw [show a + 2 = (a + 1) + 1 by ring,
        Real.Gamma_add_one (by linarith : a + 1 ≠ 0),
        Real.Gamma_add_one ha.ne']
      ring
    rw [hG2]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    field_simp
  · exact (measurable_gammaPDFReal a r).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top

/-- The identity function is integrable under a Gamma law. -/
theorem integrable_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x) (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x : ℝ ↦ x)
    (volume.withDensity (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  have hfun : (fun x : ℝ ↦ x * gammaPDFReal a r x) =
      Set.indicator (Ioi (0 : ℝ)) (fun x ↦
        (r ^ a / Real.Gamma a) * (x ^ a * Real.exp (-(r * x)))) := by
    funext x
    by_cases hx : 0 < x
    · have hxmem : x ∈ Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxmem]
      simp only [gammaPDFReal, if_pos hx.le]
      have hrpow : x * x ^ (a - 1) = x ^ a := by
        calc
          x * x ^ (a - 1) = x ^ (1 : ℝ) * x ^ (a - 1) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + (a - 1)) := (Real.rpow_add hx _ _).symm
          _ = x ^ a := by ring_nf
      rw [← hrpow]
      ring
    · have hxmem : x ∉ Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_notMem hxmem]
      have hxle : x ≤ 0 := le_of_not_gt hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hxneg : x < 0 := lt_of_le_of_ne hxle hx0
        simp [gammaPDFReal, if_neg (not_le.mpr hxneg)]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]
  have hbase :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < a + 1) hr
  have hshape : a + 1 - 1 = a := by ring
  rw [hshape] at hbase
  exact hbase.const_mul _

/-- Mean of a shape--rate Gamma law. -/
theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x : ℝ, x ∂gammaMeasure a r = a / r := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x, (gammaPDF a r x).toReal * x) = _
    simp_rw [gammaPDF_toReal ha hr]
    have hsupport : (Set.indicator (Ioi (0 : ℝ)) fun x ↦
        gammaPDFReal a r x * x) =
        (fun x ↦ gammaPDFReal a r x * x) := by
      funext x
      by_cases hx : 0 < x
      · exact Set.indicator_of_mem hx _
      · have hxmem : x ∉ Ioi (0 : ℝ) := hx
        rw [Set.indicator_of_notMem hxmem]
        have hxle : x ≤ 0 := le_of_not_gt hx
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hxneg : x < 0 := lt_of_le_of_ne hxle hx0
          simp [gammaPDFReal, if_neg (not_le.mpr hxneg)]
    rw [← hsupport, integral_indicator measurableSet_Ioi]
    have hfun : ∫ x in Ioi (0 : ℝ), gammaPDFReal a r x * x =
        ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
          (x ^ a * Real.exp (-(r * x))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxpos : 0 < x := hx
      simp only [gammaPDFReal, if_pos hxpos.le]
      have hrpow : x ^ (a - 1) * x = x ^ a := by
        calc
          x ^ (a - 1) * x = x ^ (a - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((a - 1) + (1 : ℝ)) := (Real.rpow_add hxpos _ _).symm
          _ = x ^ a := by ring_nf
      rw [← hrpow]
      ring
    rw [hfun, integral_const_mul]
    have hgamma :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < a + 1) hr
    have hshape : a + 1 - 1 = a := by ring
    rw [hshape] at hgamma
    rw [hgamma, Real.Gamma_add_one ha.ne']
    have honeDivPos : 0 < (1 / r : ℝ) := one_div_pos.mpr hr
    rw [show a + 1 = a + (1 : ℝ) by rfl, Real.rpow_add honeDivPos,
      Real.rpow_one]
    have hprod : r ^ a * (1 / r) ^ a = 1 := by
      rw [← Real.mul_rpow hr.le honeDivPos.le]
      simp [hr.ne']
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    field_simp
    nlinarith
  · exact (measurable_gammaPDFReal a r).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top

/-- In the paper's shape-equals-rate parameterization the Gamma weights are centered at one. -/
theorem centered_gamma_mean {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, x ∂gammaMeasure a a = 1 := by
  rw [integral_id_gammaMeasure ha ha, div_self ha.ne']

/-- MGF of a centered `Gamma(a,a)` variable. -/
theorem centered_gamma_mgf {a t : ℝ} (ha : 0 < a) (ht : t < a) :
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure a a =
      Real.exp (-t) * (1 - t / a) ^ (-a) := by
  have hprob : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  calc
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure a a =
        ∫ x, Real.exp (-t) * Real.exp (t * x) ∂gammaMeasure a a := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change Real.exp (t * (x - 1)) = Real.exp (-t) * Real.exp (t * x)
            rw [← Real.exp_add]
            congr 1
            ring
    _ = Real.exp (-t) * ∫ x, Real.exp (t * x) ∂gammaMeasure a a := by
      rw [integral_const_mul]
    _ = Real.exp (-t) * (a / (a - t)) ^ a := by
      rw [gamma_mgf ha ha ht]
    _ = Real.exp (-t) * (1 - t / a) ^ (-a) := by
      congr 1
      have hbase : 0 < 1 - t / a := by
        rw [sub_pos, div_lt_one ha]
        exact ht
      have hbaseeq : a / (a - t) = (1 - t / a)⁻¹ := by
        field_simp [ha.ne']
      rw [hbaseeq, Real.inv_rpow hbase.le, Real.rpow_neg hbase.le]

/-- Integrability companion to `centered_gamma_mgf`. -/
theorem integrable_centered_gamma_exp {a t : ℝ} (ha : 0 < a) (ht : t < a) :
    Integrable (fun x ↦ Real.exp (t * (x - 1))) (gammaMeasure a a) := by
  have h := (integrable_exp_mul_gammaMeasure ha ha ht).const_mul (Real.exp (-t))
  apply h.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    change Real.exp (-t) * Real.exp (t * x) = Real.exp (t * (x - 1))
    rw [← Real.exp_add]
    congr 1
    ring

/-- Exponential Markov inequality, expressed using `Measure.real`. -/
theorem exponential_markov_upper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {s c : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω ↦ Real.exp (s * X ω)) μ) :
    μ.real {ω | c ≤ X ω} ≤
      Real.exp (-s * c) * ∫ ω, Real.exp (s * X ω) ∂μ := by
  have hset : {ω | Real.exp (s * c) ≤ Real.exp (s * X ω)} =
      {ω | c ≤ X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor <;> intro hω <;> nlinarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω ↦ Real.exp (s * X ω))
    (Filter.Eventually.of_forall fun ω ↦ (Real.exp_pos _).le) hint (Real.exp (s * c))
  rw [hset] at hmarkov
  calc
    μ.real {ω | c ≤ X ω} =
        Real.exp (-s * c) *
          (Real.exp (s * c) * μ.real {ω | c ≤ X ω}) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-s * c) * ∫ ω, Real.exp (s * X ω) ∂μ :=
      mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le

/-- Lower-tail version of exponential Markov, using a positive tilt of `-X`. -/
theorem exponential_markov_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {s c : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω ↦ Real.exp (-s * X ω)) μ) :
    μ.real {ω | X ω ≤ -c} ≤
      Real.exp (-s * c) * ∫ ω, Real.exp (-s * X ω) ∂μ := by
  have hfun : (fun ω ↦ Real.exp (s * (-X ω))) =
      (fun ω ↦ Real.exp (-s * X ω)) := by
    funext ω
    congr 1
    ring
  have hset : {ω | c ≤ -X ω} = {ω | X ω ≤ -c} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hω <;> linarith
  have hint' : Integrable (fun ω ↦ Real.exp (s * (-X ω))) μ := by
    rw [hfun]
    exact hint
  have h := exponential_markov_upper μ (fun ω ↦ -X ω) hs hint'
    (c := c)
  rw [hset, hfun] at h
  exact h

/-- Optimized upper Chernoff bound for a shape--rate `Gamma(a,a)` law. -/
theorem gamma_upper_tail_exact {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (gammaMeasure a a).real {x | 1 + t ≤ x} ≤
      Real.exp (-a * (t - Real.log (1 + t))) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  rcases ht.eq_or_lt with rfl | htpos
  · simpa using (measureReal_le_one : (gammaMeasure a a).real {x | 1 ≤ x} ≤ 1)
  · let s : ℝ := a * t / (1 + t)
    have hden : 0 < 1 + t := by linarith
    have hs : 0 < s := by dsimp [s]; positivity
    have hslt : s < a := by
      dsimp [s]
      rw [div_lt_iff₀ hden]
      nlinarith
    have hint := integrable_centered_gamma_exp ha hslt
    have hmark := exponential_markov_upper (gammaMeasure a a)
      (fun x ↦ x - 1) hs hint (c := t)
    have hset : {x : ℝ | t ≤ x - 1} = {x : ℝ | 1 + t ≤ x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hx <;> linarith
    rw [hset, centered_gamma_mgf ha hslt] at hmark
    calc
      (gammaMeasure a a).real {x | 1 + t ≤ x} ≤
          Real.exp (-s * t) * (Real.exp (-s) * (1 - s / a) ^ (-a)) := hmark
      _ = Real.exp (-a * (t - Real.log (1 + t))) := by
        have ha0 : a ≠ 0 := ha.ne'
        have hbase : 1 - s / a = (1 + t)⁻¹ := by
          dsimp [s]
          field_simp
          ring
        rw [hbase, Real.rpow_def_of_pos (inv_pos.mpr hden), Real.log_inv]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [s]
        field_simp
        ring

/-- Optimized lower Chernoff bound for a shape--rate `Gamma(a,a)` law. -/
theorem gamma_lower_tail_exact {a t : ℝ} (ha : 0 < a) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (gammaMeasure a a).real {x | x ≤ 1 - t} ≤
      Real.exp (-a * (-t - Real.log (1 - t))) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  rcases ht₀.eq_or_lt with rfl | htpos
  · simpa using (measureReal_le_one : (gammaMeasure a a).real {x | x ≤ 1} ≤ 1)
  · let s : ℝ := a * t / (1 - t)
    have hden : 0 < 1 - t := sub_pos.mpr ht₁
    have hs : 0 < s := by dsimp [s]; positivity
    have hneglt : -s < a := by linarith
    have hint := integrable_centered_gamma_exp ha hneglt
    have hmark := exponential_markov_lower (gammaMeasure a a)
      (fun x ↦ x - 1) hs hint (c := t)
    have hset : {x : ℝ | x - 1 ≤ -t} = {x : ℝ | x ≤ 1 - t} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hx <;> linarith
    rw [hset] at hmark
    have hmgf := centered_gamma_mgf ha hneglt
    have hfun : (fun x : ℝ ↦ Real.exp (-s * (x - 1))) =
        (fun x ↦ Real.exp ((-s) * (x - 1))) := by
      funext x
      congr 1
    rw [hfun, hmgf] at hmark
    calc
      (gammaMeasure a a).real {x | x ≤ 1 - t} ≤
          Real.exp (-s * t) * (Real.exp (-(-s)) * (1 - (-s) / a) ^ (-a)) := hmark
      _ = Real.exp (-a * (-t - Real.log (1 - t))) := by
        have ha0 : a ≠ 0 := ha.ne'
        have hbase : 1 - (-s) / a = (1 - t)⁻¹ := by
          dsimp [s]
          field_simp
          ring
        rw [hbase, Real.rpow_def_of_pos (inv_pos.mpr hden), Real.log_inv]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [s]
        field_simp
        ring

/-- A Gamma law assigns zero mass to the nonpositive half-line. -/
theorem gammaMeasure_Iic_zero {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    gammaMeasure a r (Iic 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
    lintegral_Iic_eq_lintegral_Iio_add_Icc (f := gammaPDF a r) le_rfl,
    lintegral_gammaPDF_of_nonpos le_rfl]
  simp

/-- The two-sided Gamma coordinate inequality away from the endpoint. -/
theorem gamma_coordinate_concentration_of_lt_one {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t < 1) :
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
      2 * Real.exp (-a * t ^ 2 / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have ht₀' : 0 ≤ t := ht₀.le
  have hu := gamma_upper_tail_exact ha ht₀'
  have hl := gamma_lower_tail_exact ha ht₀' ht₁
  have hset : {x : ℝ | |x - 1| > t} ⊆
      {x | 1 + t ≤ x} ∪ {x | x ≤ 1 - t} := by
    intro x hx
    change |x - 1| > t at hx
    change (1 + t ≤ x) ∨ (x ≤ 1 - t)
    rcases (lt_abs.mp hx) with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  calc
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
        (gammaMeasure a a).real ({x | 1 + t ≤ x} ∪ {x | x ≤ 1 - t}) :=
      measureReal_mono hset (by finiteness)
    _ ≤ (gammaMeasure a a).real {x | 1 + t ≤ x} +
        (gammaMeasure a a).real {x | x ≤ 1 - t} := measureReal_union_le _ _
    _ ≤ Real.exp (-a * (t - Real.log (1 + t))) +
        Real.exp (-a * (-t - Real.log (1 - t))) := add_le_add hu hl
    _ ≤ 2 * Real.exp (-a * t ^ 2 / 4) := by
      have huLog := sub_log_one_add_ge_sq_div_four ht₀' ht₁.le
      have hlLog : -t - Real.log (1 - t) ≥ t ^ 2 / 4 := by
        exact (neg_sub_log_one_sub_ge_sq_div_two ht₀' ht₁).trans'
          (by nlinarith [sq_nonneg t])
      have hua : -a * (t - Real.log (1 + t)) ≤ -a * t ^ 2 / 4 := by
        nlinarith
      have hla : -a * (-t - Real.log (1 - t)) ≤ -a * t ^ 2 / 4 := by
        nlinarith
      rw [two_mul]
      exact add_le_add (Real.exp_le_exp.mpr hua) (Real.exp_le_exp.mpr hla)

/-- Endpoint `t = 1`, where the lower tail is empty up to a null singleton. -/
theorem gamma_coordinate_concentration_one {a : ℝ} (ha : 0 < a) :
    (gammaMeasure a a).real {x | |x - 1| > 1} ≤
      2 * Real.exp (-a / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hu := gamma_upper_tail_exact ha (show (0 : ℝ) ≤ 1 by norm_num)
  have hzero : (gammaMeasure a a).real {x | x ≤ 0} = 0 := by
    change ENNReal.toReal (gammaMeasure a a (Iic 0)) = 0
    rw [gammaMeasure_Iic_zero ha ha]
    simp
  have hset : {x : ℝ | |x - 1| > 1} ⊆ {x | 2 ≤ x} ∪ {x | x ≤ 0} := by
    intro x hx
    change |x - 1| > 1 at hx
    change (2 ≤ x) ∨ (x ≤ 0)
    rcases (lt_abs.mp hx) with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hu' : (gammaMeasure a a).real {x | 2 ≤ x} ≤
      Real.exp (-a * (1 - Real.log 2)) := by norm_num at hu ⊢; exact hu
  have hlog := sub_log_one_add_ge_sq_div_four
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
  have hexp : Real.exp (-a * (1 - Real.log 2)) ≤ Real.exp (-a / 4) := by
    apply Real.exp_le_exp.mpr
    norm_num at hlog
    nlinarith
  calc
    (gammaMeasure a a).real {x | |x - 1| > 1} ≤
        (gammaMeasure a a).real ({x | 2 ≤ x} ∪ {x | x ≤ 0}) :=
      measureReal_mono hset (by finiteness)
    _ ≤ (gammaMeasure a a).real {x | 2 ≤ x} +
        (gammaMeasure a a).real {x | x ≤ 0} := measureReal_union_le _ _
    _ ≤ Real.exp (-a * (1 - Real.log 2)) + 0 := add_le_add hu' hzero.le
    _ ≤ 2 * Real.exp (-a / 4) := by nlinarith [Real.exp_pos (-a / 4), hexp]

/-- The manuscript's two-sided Gamma coordinate concentration inequality. -/
theorem gamma_coordinate_concentration {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    (gammaMeasure a a).real {x | |x - 1| > t} ≤
      2 * Real.exp (-a * t ^ 2 / 4) := by
  rcases ht₁.eq_or_lt with rfl | htlt
  · convert gamma_coordinate_concentration_one ha using 1 <;> ring
  · exact gamma_coordinate_concentration_of_lt_one ha ht₀ htlt

/-- A finite family of coordinate tail bounds gives a maximum-coordinate
bound, with no independence assumption needed for this union-bound step. -/
theorem finite_coordinate_union_bound_real
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (W : Fin n → Ω → ℝ) {t b : ℝ}
    (hcoord : ∀ i, μ.real {ω | |W i ω - 1| > t} ≤ b) :
    μ.real {ω | ∃ i, |W i ω - 1| > t} ≤ n * b := by
  have hset : {ω | ∃ i, |W i ω - 1| > t} =
      ⋃ i : Fin n, {ω | |W i ω - 1| > t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  calc
    μ.real (⋃ i : Fin n, {ω | |W i ω - 1| > t}) ≤
        ∑ i : Fin n, μ.real {ω | |W i ω - 1| > t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = n * b := by simp

/-- Union-bound form of Gamma concentration for an independent product draw.
This is the coordinate-maximum inequality used in both weighting regimes. -/
theorem gamma_max_coordinate_concentration {n : ℕ} {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ gammaMeasure a a)).real
        {w | ∃ i, |w i - 1| > t} ≤
      2 * n * Real.exp (-a * t ^ 2 / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  let μn : Measure (Fin n → ℝ) :=
    Measure.pi (fun _ : Fin n ↦ gammaMeasure a a)
  have hcoord (i : Fin n) :
      μn.real {w | |w i - 1| > t} ≤
        2 * Real.exp (-a * t ^ 2 / 4) := by
    have hmeas : MeasurableSet {x : ℝ | |x - 1| > t} := by
      exact measurableSet_lt measurable_const
        ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable)
    have hpre : {w : Fin n → ℝ | |w i - 1| > t} =
        Function.eval i ⁻¹' {x : ℝ | |x - 1| > t} := rfl
    rw [hpre, measureReal_def,
      (measurePreserving_eval (fun _ : Fin n ↦ gammaMeasure a a) i).measure_preimage
        hmeas.nullMeasurableSet]
    exact gamma_coordinate_concentration ha ht₀ ht₁
  have h := finite_coordinate_union_bound_real μn
    (fun i w ↦ w i) (t := t) (b := 2 * Real.exp (-a * t ^ 2 / 4)) hcoord
  change μn.real {w | ∃ i, |w i - 1| > t} ≤ _
  calc
    μn.real {w | ∃ i, |w i - 1| > t} ≤
        n * (2 * Real.exp (-a * t ^ 2 / 4)) := h
    _ = 2 * n * Real.exp (-a * t ^ 2 / 4) := by ring

end ReweightedNPMLE
