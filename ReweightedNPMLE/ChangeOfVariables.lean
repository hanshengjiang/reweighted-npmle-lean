import Mathlib.MeasureTheory.Function.Jacobian
import ReweightedNPMLE.DirichletIndependence
import ReweightedNPMLE.Localization
import ReweightedNPMLE.MatrixSensitivity

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ReweightedNPMLE

/-- The logarithm inequality converts the product of multiplicative Gamma
density factors into the exponential cost used in the determinant moment. -/
theorem gamma_product_rpow_exp_lower {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (w t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 8) :
    Real.exp (-α * (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2)) ≤
      (∏ i, (1 + t i) ^ α) * Real.exp (-α * ∑ i, w i * t i) := by
  have htpos (i : Fin n) : 0 < 1 + t i := by
    have hi := neg_le_of_abs_le (ht i)
    linarith
  have hlog : ∑ i, (t i - (t i) ^ 2) ≤ ∑ i, Real.log (1 + t i) :=
    Finset.sum_le_sum fun i _ ↦ log_one_add_ge_sub_sq (ht i)
  have hprod : (∏ i, (1 + t i) ^ α) =
      Real.exp (α * ∑ i, Real.log (1 + t i)) := by
    simp_rw [Real.rpow_def_of_pos (htpos _)]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hprod, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hscaled : α * ∑ i, (t i - (t i) ^ 2) ≤
      α * ∑ i, Real.log (1 + t i) := mul_le_mul_of_nonneg_left hlog hα
  rw [Finset.sum_sub_distrib] at hscaled
  have hcost : ∑ i, (w i - 1) * t i =
      (∑ i, w i * t i) - ∑ i, t i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcost]
  linarith

/-- Combining the product-Gamma density ratio, the logarithm lower bound,
and an assumed Jacobian lower bound gives the pointwise domination required
by the area formula. -/
theorem gamma_density_jacobian_domination_real
    {n : ℕ} {α c J : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ht : ∀ i, |t i| ≤ 1 / 8)
    (hdet : (∏ i, (1 + t i)) * c ≤ J) :
    gammaProductDensityReal n α α w *
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
      J * gammaProductDensityReal n α α
        (fun i ↦ w i * (1 + t i)) := by
  have htpos (i : Fin n) : 0 < 1 + t i := by
    have hi := neg_le_of_abs_le (ht i)
    linarith
  have hp : 0 ≤ gammaProductDensityReal n α α w := by
    unfold gammaProductDensityReal
    exact Finset.prod_nonneg fun i _ ↦ gammaPDFReal_nonneg hα hα _
  have hB : 0 ≤ ∏ i, (1 + t i) ^ (α - 1) :=
    Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (htpos i) _).le
  have hC : 0 ≤ Real.exp (-α * ∑ i, w i * t i) := (Real.exp_pos _).le
  have hAB : (∏ i, (1 + t i)) * (∏ i, (1 + t i) ^ (α - 1)) =
      ∏ i, (1 + t i) ^ α := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Real.rpow_sub_one (htpos i).ne']
    field_simp [(htpos i).ne']
  have hlower := gamma_product_rpow_exp_lower hα.le w t ht
  rw [gammaProductDensityReal_mul_one_add w t hw htpos]
  calc
    gammaProductDensityReal n α α w *
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
        gammaProductDensityReal n α α w *
          (c * ((∏ i, (1 + t i) ^ α) *
            Real.exp (-α * ∑ i, w i * t i))) := by gcongr
    _ = ((∏ i, (1 + t i)) * c) *
        (gammaProductDensityReal n α α w *
          (∏ i, (1 + t i) ^ (α - 1)) *
            Real.exp (-α * ∑ i, w i * t i)) := by rw [← hAB]; ring
    _ ≤ J * (gammaProductDensityReal n α α w *
          (∏ i, (1 + t i) ^ (α - 1)) *
            Real.exp (-α * ∑ i, w i * t i)) := by
      exact mul_le_mul_of_nonneg_right hdet (mul_nonneg (mul_nonneg hp hB) hC)

/-- `ENNReal` form of `gamma_density_jacobian_domination_real`, ready for
direct use under a Gamma product measure. -/
theorem gamma_density_jacobian_domination
    {n : ℕ} {α c J : ℝ} (hα : 0 < α) (hc : 0 ≤ c) (hJ : 0 ≤ J)
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ht : ∀ i, |t i| ≤ 1 / 8)
    (hdet : (∏ i, (1 + t i)) * c ≤ J) :
    gammaProductDensity n α α w * ENNReal.ofReal
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
      ENNReal.ofReal J * gammaProductDensity n α α
        (fun i ↦ w i * (1 + t i)) := by
  rw [gammaProductDensity_eq_ofReal n hα hα,
    gammaProductDensity_eq_ofReal n hα hα,
    ← ENNReal.ofReal_mul (by
      unfold gammaProductDensityReal
      exact Finset.prod_nonneg fun i _ ↦ gammaPDFReal_nonneg hα hα _),
    ← ENNReal.ofReal_mul hJ]
  exact ENNReal.ofReal_le_ofReal
    (gamma_density_jacobian_domination_real hα hc w t hw ht hdet)

/-- The density-weighted Jacobian of an injective differentiable map over a
measurable set has integral at most the total mass of the target density. -/
theorem lintegral_density_jacobian_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {s : Set E} (hs : MeasurableSet s) {F : E → E}
    {F' : E → E →L[ℝ] E}
    (hF' : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF : Set.InjOn F s) (p : E → ENNReal)
    (hp : ∫⁻ y, p y ∂volume ≤ 1) :
    ∫⁻ x in s, ENNReal.ofReal |(F' x).det| * p (F x) ∂volume ≤ 1 := by
  rw [← lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hF' hF]
  exact (setLIntegral_le_lintegral (F '' s) p).trans hp

/-- Abstract determinant-moment transfer.  The hypothesis `hdom` is exactly
the pointwise comparison obtained by multiplying the density ratio by the
Jacobian lower bound. -/
theorem lintegral_under_density_le_one_of_jacobian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {s : Set E} (hs : MeasurableSet s) {F : E → E}
    {F' : E → E →L[ℝ] E}
    (hF' : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF : Set.InjOn F s) {p Y : E → ENNReal}
    (hpmeas : Measurable p) (hYmeas : Measurable Y)
    (hp : ∫⁻ y, p y ∂volume ≤ 1)
    (hdom : ∀ x ∈ s,
      p x * Y x ≤ ENNReal.ofReal |(F' x).det| * p (F x)) :
    ∫⁻ x in s, Y x ∂volume.withDensity p ≤ 1 := by
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hpmeas hYmeas hs]
  exact (setLIntegral_mono' hs hdom).trans
    (lintegral_density_jacobian_le_one hs hF' hF p hp)

/-- Gamma-product specialization of the injective determinant-moment
transfer.  All normalization of the product density is discharged here. -/
theorem gammaProduct_lintegral_le_one_of_jacobian
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hF' : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF : Set.InjOn F s) {Y : (Fin n → ℝ) → ENNReal}
    (hYmeas : Measurable Y)
    (hdom : ∀ x ∈ s,
      gammaProductDensity n α α x * Y x ≤
        ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x)) :
    ∫⁻ x in s, Y x ∂gammaProductMeasure n α α ≤ 1 := by
  rw [gammaProductMeasure_eq_volume_withDensity]
  exact lintegral_under_density_le_one_of_jacobian hs hF' hF
    (measurable_gammaProductDensity n α α) hYmeas
    (lintegral_gammaProductDensity_eq_one n hα hα).le hdom

/-- Derivative of the coordinatewise multiplicative change map
`w ↦ w * (1 + t w)`. -/
theorem hasFDerivWithinAt_multiplicativeChange
    {n : ℕ} {s : Set (Fin n → ℝ)}
    {t : (Fin n → ℝ) → (Fin n → ℝ)}
    {t' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {w : Fin n → ℝ}
    (ht : HasFDerivWithinAt t t' s w) :
    HasFDerivWithinAt (fun v ↦ v * (1 + t v))
      (w • t' + (1 + t w) • ContinuousLinearMap.id ℝ (Fin n → ℝ)) s w := by
  convert (hasFDerivWithinAt_id w s).mul
    ((hasFDerivWithinAt_const (1 : Fin n → ℝ) w s).add ht) using 1 <;>
    ext <;> simp [mul_comm]

/-- Standard-basis matrix of the derivative of the multiplicative change
map.  This is `diag(1+t) + diag(w) Dt`. -/
theorem multiplicativeChangeDeriv_toMatrix
    {n : ℕ} (w u : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    LinearMap.toMatrix' (w • L + (1 + u) •
      ContinuousLinearMap.id ℝ (Fin n → ℝ)).toLinearMap =
      Matrix.diagonal (fun i ↦ 1 + u i) +
        Matrix.diagonal w * LinearMap.toMatrix' L.toLinearMap := by
  classical
  ext i j
  have hmul : (Matrix.diagonal w * LinearMap.toMatrix' L.toLinearMap) i j =
      w i * L (Pi.single j 1) i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [LinearMap.toMatrix'_apply]
    · intro b hb hbi
      simp [Ne.symm hbi]
    · simp
  rw [Matrix.add_apply, hmul]
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix'_apply]
    ring
  · simp [LinearMap.toMatrix'_apply, hij]

/-- The basis-free determinant of a continuous linear endomorphism agrees
with the determinant of its standard-basis matrix. -/
theorem continuousLinearMap_det_eq_toMatrix'
    {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    L.det = (LinearMap.toMatrix' L.toLinearMap).det := by
  rw [ContinuousLinearMap.det, LinearMap.det_toMatrix']

/-- Jacobian lower bound supplied by the paper's matrix-sensitivity
inequality.  The columns of `V` are orthonormal sensitivity directions, and
the square-root conjugated derivative `R` dominates their projection. -/
theorem multiplicativeChange_jacobian_lower
    {n : ℕ} {k : Type*} [Fintype k] [DecidableEq k]
    (w u : Fin n → ℝ) (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hw : ∀ i, 0 < w i) (hu : ∀ i, |u i| ≤ 1 / 8)
    (V : Matrix (Fin n) k ℝ) (hV : Matrix.conjTranspose V * V = 1)
    (hR : (Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
      LinearMap.toMatrix' L.toLinearMap *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i)) -
        V * Matrix.conjTranspose V).PosSemidef) :
    (∏ i, (1 + u i)) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      |(w • L + (1 + u) •
        ContinuousLinearMap.id ℝ (Fin n → ℝ)).det| := by
  let H : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix' L.toLinearMap
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt (w i)) * H *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  have hau0 : ∀ i, 0 < 1 + u i := by
    intro i
    have hi := neg_le_of_abs_le (hu i)
    norm_num at hi ⊢
    linarith
  have hauUpper : ∀ i, 1 + u i ≤ 9 / 8 := by
    intro i
    have hi := le_of_abs_le (hu i)
    norm_num at hi ⊢
    linarith
  have hmatrix : (∏ i, (1 + u i)) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      (Matrix.diagonal (fun i ↦ 1 + u i) + R).det :=
    determinant_diagonal_add_psd_projection_lower
      (fun i ↦ 1 + u i) hau0 hauUpper V hV R (by simpa [R, H] using hR)
  have hdetEq :
      (w • L + (1 + u) • ContinuousLinearMap.id ℝ (Fin n → ℝ)).det =
        (Matrix.diagonal (fun i ↦ 1 + u i) + R).det := by
    rw [continuousLinearMap_det_eq_toMatrix',
      multiplicativeChangeDeriv_toMatrix]
    exact det_diagonal_add_weight_mul_eq_sqrt_conj w (fun i ↦ 1 + u i) hw H
  calc
    (∏ i, (1 + u i)) * (17 / 9 : ℝ) ^ Fintype.card k ≤
        (Matrix.diagonal (fun i ↦ 1 + u i) + R).det := hmatrix
    _ = (w • L + (1 + u) •
        ContinuousLinearMap.id ℝ (Fin n → ℝ)).det := hdetEq.symm
    _ ≤ |(w • L + (1 + u) •
        ContinuousLinearMap.id ℝ (Fin n → ℝ)).det| := le_abs_self _

/-- Measurability of the Gamma determinant-moment integrand follows from
measurability of the displacement and determinant factor. -/
theorem measurable_gammaDeterminantIntegrand
    {n : ℕ} {α : ℝ}
    {t : (Fin n → ℝ) → (Fin n → ℝ)} {c : (Fin n → ℝ) → ℝ}
    (ht : Measurable t) (hc : Measurable c) :
    Measurable (fun w ↦ ENNReal.ofReal
      (c w * Real.exp (-α *
        (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))) := by
  fun_prop

/-- A coordinatewise multiplicative perturbation is injective on a positive
set whenever its perturbation field is monotone.  This is the injectivity
argument in the paper's change of variables: equality after perturbation
makes every monotonicity summand nonpositive, so monotonicity forces every
one of them to vanish. -/
theorem multiplicativeChange_injOn_of_monotone
    {n : ℕ} {s : Set (Fin n → ℝ)}
    (t : (Fin n → ℝ) → (Fin n → ℝ))
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (htpos : ∀ w ∈ s, ∀ i, 0 < 1 + t w i)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i)) :
    Set.InjOn (fun w i ↦ w i * (1 + t w i)) s := by
  intro w hws v hvs hF
  have hcoord (i : Fin n) :
      w i * (1 + t w i) = v i * (1 + t v i) := congrFun hF i
  have hnonpos (i : Fin n) :
      (w i - v i) * (t w i - t v i) ≤ 0 := by
    rcases le_total (t w i) (t v i) with huv | hvu
    · have hvw : v i ≤ w i := by
        by_contra hn
        have hwv : w i < v i := lt_of_not_ge hn
        have hfac : 1 + t w i ≤ 1 + t v i := by linarith
        have hlt : w i * (1 + t w i) < v i * (1 + t v i) :=
          (mul_lt_mul_of_pos_right hwv (htpos w hws i)).trans_le
            (mul_le_mul_of_nonneg_left hfac (hw v hvs i).le)
        exact (ne_of_lt hlt) (hcoord i)
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hvw) (sub_nonpos.mpr huv)
    · have hwv : w i ≤ v i := by
        by_contra hn
        have hvw : v i < w i := lt_of_not_ge hn
        have hfac : 1 + t v i ≤ 1 + t w i := by linarith
        have hlt : v i * (1 + t v i) < w i * (1 + t w i) :=
          (mul_lt_mul_of_pos_right hvw (htpos v hvs i)).trans_le
            (mul_le_mul_of_nonneg_left hfac (hw w hws i).le)
        exact (ne_of_lt hlt) (hcoord i).symm
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hwv) (sub_nonneg.mpr hvu)
  have hsum : (∑ i, (w i - v i) * (t w i - t v i)) = 0 :=
    le_antisymm (Finset.sum_nonpos fun i _ ↦ hnonpos i) (hmono w hws v hvs)
  have hzero (i : Fin n) : (w i - v i) * (t w i - t v i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun i (_hi : i ∈ Finset.univ) ↦ hnonpos i)).mp
      hsum i (Finset.mem_univ i)
  apply funext
  intro i
  rcases mul_eq_zero.mp (hzero i) with hwvi | htvi
  · exact sub_eq_zero.mp hwvi
  · have htwi : t w i = t v i := sub_eq_zero.mp htvi
    have heq := hcoord i
    rw [htwi] at heq
    exact mul_right_cancel₀ (ne_of_gt (htpos v hvs i)) heq

/-- Determinant-moment theorem in the exact coordinatewise form used by the
paper.  Once differentiability, injectivity, localization, and the Jacobian
lower bound have been established for the fitted-value change map, the full
Gamma expectation bound follows with no remaining measure-theoretic step. -/
theorem gamma_determinant_moment
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hF' : ∀ w ∈ s, HasFDerivWithinAt F (F' w) s w)
    (hF : Set.InjOn F s)
    (hFcoord : ∀ w ∈ s, F w = fun i ↦ w i * (1 + t w i))
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hc : ∀ w ∈ s, 0 ≤ c w)
    (hdet : ∀ w ∈ s,
      (∏ i, (1 + t w i)) * c w ≤ |(F' w).det|)
    (hYmeas : Measurable (fun w ↦ ENNReal.ofReal
      (c w * Real.exp (-α *
        (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2))))) :
    ∫⁻ w in s, ENNReal.ofReal
        (c w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  apply gammaProduct_lintegral_le_one_of_jacobian hα hs hF' hF hYmeas
  intro w hws
  rw [hFcoord w hws]
  exact gamma_density_jacobian_domination hα (hc w hws) (abs_nonneg _)
    w (t w) (hw w hws) (ht w hws) (hdet w hws)

/-- Paper-facing determinant-moment theorem.  Monotonicity of the
multiplicative displacement now supplies injectivity, rather than requiring
it as an independent hypothesis. -/
theorem gamma_determinant_moment_of_monotone
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hF' : ∀ w ∈ s, HasFDerivWithinAt F (F' w) s w)
    (hFcoord : ∀ w ∈ s, F w = fun i ↦ w i * (1 + t w i))
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i))
    (hc : ∀ w ∈ s, 0 ≤ c w)
    (hdet : ∀ w ∈ s,
      (∏ i, (1 + t w i)) * c w ≤ |(F' w).det|)
    (hYmeas : Measurable (fun w ↦ ENNReal.ofReal
      (c w * Real.exp (-α *
        (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2))))) :
    ∫⁻ w in s, ENNReal.ofReal
        (c w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  have htpos : ∀ w ∈ s, ∀ i, 0 < 1 + t w i := by
    intro w hws i
    have hi := neg_le_of_abs_le (ht w hws i)
    norm_num at hi ⊢
    linarith
  have hmul : Set.InjOn (fun w i ↦ w i * (1 + t w i)) s :=
    multiplicativeChange_injOn_of_monotone t hw htpos hmono
  have hFinj : Set.InjOn F s := by
    intro w hws v hvs hEq
    apply hmul hws hvs
    change (fun i ↦ w i * (1 + t w i)) = (fun i ↦ v i * (1 + t v i))
    calc
      _ = F w := (hFcoord w hws).symm
      _ = F v := hEq
      _ = _ := hFcoord v hvs
  exact gamma_determinant_moment hα hs t c hF' hFinj hFcoord hw ht hc hdet hYmeas

/-- Fully specialized change-of-variables theorem for a differentiable
monotone displacement field.  The derivative, injectivity, and integrand
measurability obligations are all discharged from structural hypotheses on
`t` and `c`; only the substantive Jacobian lower bound remains. -/
theorem gamma_determinant_moment_of_monotone_deriv
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (t' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (ht' : ∀ w ∈ s, HasFDerivWithinAt t (t' w) s w)
    (htmeas : Measurable t) (hcmeas : Measurable c)
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i))
    (hc : ∀ w ∈ s, 0 ≤ c w)
    (hdet : ∀ w ∈ s,
      (∏ i, (1 + t w i)) * c w ≤
        |(w • t' w + (1 + t w) •
          ContinuousLinearMap.id ℝ (Fin n → ℝ)).det|) :
    ∫⁻ w in s, ENNReal.ofReal
        (c w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  apply gamma_determinant_moment_of_monotone hα hs t c
    (F' := fun w ↦ w • t' w + (1 + t w) •
      ContinuousLinearMap.id ℝ (Fin n → ℝ))
  · exact fun w hws ↦ hasFDerivWithinAt_multiplicativeChange (ht' w hws)
  · intro w hws
    rfl
  · exact hw
  · exact ht
  · exact hmono
  · exact hc
  · exact hdet
  · exact measurable_gammaDeterminantIntegrand htmeas hcmeas

/-- Determinant moment with the Jacobian hypothesis discharged by the
paper's matrix-sensitivity inequality.  The measurable natural number
`m w` is the number of orthonormal sensitivity directions at `w`; its
contribution is the sharp factor `(17 / 9) ^ m w`. -/
theorem gamma_determinant_moment_of_matrix_sensitivity
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (m : (Fin n → ℝ) → ℕ)
    (t' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (ht' : ∀ w ∈ s, HasFDerivWithinAt t (t' w) s w)
    (htmeas : Measurable t) (hm : Measurable m)
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i))
    (V : (w : Fin n → ℝ) → Matrix (Fin n) (Fin (m w)) ℝ)
    (hV : ∀ w ∈ s, Matrix.conjTranspose (V w) * V w = 1)
    (hR : ∀ w ∈ s,
      (Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
        LinearMap.toMatrix' (t' w).toLinearMap *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i)) -
          V w * Matrix.conjTranspose (V w)).PosSemidef) :
    ∫⁻ w in s, ENNReal.ofReal
        ((17 / 9 : ℝ) ^ m w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  apply gamma_determinant_moment_of_monotone_deriv hα hs t
    (fun w ↦ (17 / 9 : ℝ) ^ m w) t' ht' htmeas
    (hm.const_pow (17 / 9 : ℝ)) hw ht hmono
  · intro w hws
    positivity
  · intro w hws
    simpa using multiplicativeChange_jacobian_lower w (t w) (t' w)
      (hw w hws) (ht w hws) (V w) (hV w hws) (hR w hws)

theorem gammaProduct_lintegral_le_one_of_ae_jacobian
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hF' : ∀ᵐ x ∂volume, x ∈ s → HasFDerivAt F (F' x) x)
    (hF : Set.InjOn F s) {Y : (Fin n → ℝ) → ENNReal}
    (hYmeas : Measurable Y)
    (hdom : ∀ᵐ x ∂volume, x ∈ s →
      gammaProductDensity n α α x * Y x ≤
        ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x)) :
    ∫⁻ x in s, Y x ∂gammaProductMeasure n α α ≤ 1 := by
  have hall : ∀ᵐ x ∂volume, x ∈ s →
      HasFDerivAt F (F' x) x ∧
        gammaProductDensity n α α x * Y x ≤
          ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x) := by
    filter_upwards [hF', hdom] with x hx hd hxs
    exact ⟨hx hxs, hd hxs⟩
  obtain ⟨d, hbad, hdmeas, hdnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  have hgood : ∀ x ∈ s \ d,
      HasFDerivAt F (F' x) x ∧
        gammaProductDensity n α α x * Y x ≤
          ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x) := by
    intro x hx
    have hh : x ∈ s → HasFDerivAt F (F' x) x ∧
        gammaProductDensity n α α x * Y x ≤
          ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x) := by
      by_contra hn
      exact hx.2 (hbad hn)
    exact hh hx.1
  have hsd : s \ d =ᵐ[volume] s := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hdnull] with x hx
    exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx⟩⟩
  have hsdGamma : s \ d =ᵐ[gammaProductMeasure n α α] s := by
    rw [gammaProductMeasure_eq_volume_withDensity]
    exact withDensity_absolutelyContinuous volume (gammaProductDensity n α α) hsd
  rw [← setLIntegral_congr hsdGamma]
  exact gammaProduct_lintegral_le_one_of_jacobian hα (hs.diff hdmeas)
    (fun x hx ↦ (hgood x hx).1.hasFDerivWithinAt)
    (hF.mono diff_subset) hYmeas (fun x hx ↦ (hgood x hx).2)

/-- The monotone Gamma change-of-variables theorem with only
almost-everywhere differentiability and Jacobian domination. -/
theorem gamma_determinant_moment_of_monotone_ae_deriv
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (t' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (ht' : ∀ᵐ w ∂volume, w ∈ s → HasFDerivAt t (t' w) w)
    (htmeas : Measurable t) (hcmeas : Measurable c)
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i))
    (hc : ∀ w ∈ s, 0 ≤ c w)
    (hdet : ∀ᵐ w ∂volume, w ∈ s →
      (∏ i, (1 + t w i)) * c w ≤
        |(w • t' w + (1 + t w) •
          ContinuousLinearMap.id ℝ (Fin n → ℝ)).det|) :
    ∫⁻ w in s, ENNReal.ofReal
        (c w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  let F := fun w ↦ w * (1 + t w)
  let F' := fun w ↦ w • t' w + (1 + t w) •
    ContinuousLinearMap.id ℝ (Fin n → ℝ)
  apply gammaProduct_lintegral_le_one_of_ae_jacobian hα hs (F := F) (F' := F')
  · filter_upwards [ht'] with w hw' hws
    exact (hasFDerivWithinAt_multiplicativeChange (s := univ)
      (hw' hws).hasFDerivWithinAt).hasFDerivAt_of_univ
  · apply multiplicativeChange_injOn_of_monotone t hw _ hmono
    intro w hws i
    have hi := neg_le_of_abs_le (ht w hws i)
    norm_num at hi ⊢
    linarith
  · exact measurable_gammaDeterminantIntegrand htmeas hcmeas
  · filter_upwards [hdet] with w hd hws
    exact gamma_density_jacobian_domination hα (hc w hws) (abs_nonneg _)
      w (t w) (hw w hws) (ht w hws) (hd hws)

end ReweightedNPMLE
