import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import ReweightedNPMLE.DirichletProposition

/-!
# Exact normalized-Gamma second moments

This file supplies the analytic calculation left open by the structural
Dirichlet development.  The proof uses the Laplace representation of an
inverse square and Tonelli/Fubini, avoiding a multivariate change of
variables.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators

namespace ReweightedNPMLE

/-- Integral of a translated negative real power over the positive half-line. -/
theorem integral_add_rpow_Ioi_zero_of_lt {a m : ℝ}
    (ha : a < -1) (hm : 0 < m) :
    ∫ x : ℝ in Ioi 0, (x + m) ^ a =
      -m ^ (a + 1) / (a + 1) := by
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t ↦ (t + m) ^ (a + 1) / (a + 1))
        ((x + m) ^ a) x := by
    intro x hx
    convert! (((hasDerivAt_id x).add_const m).rpow_const
      (Or.inl (by linarith [mem_Ici.mp hx] : x + m ≠ 0))).div_const
        (a + 1) using 1
    simp [show a + 1 ≠ 0 by linarith, mul_comm]
  have ht : Tendsto (fun t ↦ (t + m) ^ (a + 1) / (a + 1)) atTop
      (nhds (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ m tendsto_id) |>.div_const _
  have hint : IntegrableOn (fun x : ℝ ↦ (x + m) ^ a) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt ha (by linarith)
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht using 1
  · simp
    exact neg_div _ _

/-- Integrability companion to the elementary rational integral below. -/
theorem integrableOn_mul_add_rpow_Ioi_zero {q m : ℝ}
    (hq : 2 < q) (hm : 0 < m) :
    IntegrableOn (fun t : ℝ ↦ t * (t + m) ^ (-q)) (Ioi 0) := by
  have hq1 : -q + 1 < -1 := by linarith
  have hq0 : -q < -1 := by linarith
  have h1 : IntegrableOn (fun t : ℝ ↦ (t + m) ^ (-q + 1)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt hq1 (by linarith)
  have h2 : IntegrableOn (fun t : ℝ ↦ m * (t + m) ^ (-q)) (Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt hq0 (by linarith)).const_mul m
  apply (h1.sub h2).congr_fun _ measurableSet_Ioi
  intro t ht
  have htm : 0 < t + m := by linarith [mem_Ioi.mp ht]
  calc
    (t + m) ^ (-q + 1) - m * (t + m) ^ (-q) =
        (t + m) * (t + m) ^ (-q) - m * (t + m) ^ (-q) := by
      congr 1
      calc
        (t + m) ^ (-q + 1) = (t + m) ^ ((1 : ℝ) + (-q)) := by ring_nf
        _ = (t + m) ^ (1 : ℝ) * (t + m) ^ (-q) :=
          Real.rpow_add htm _ _
        _ = (t + m) * (t + m) ^ (-q) := by rw [Real.rpow_one]
    _ = t * (t + m) ^ (-q) := by ring

/-- The elementary rational integral occurring in the normalized-Gamma
second-moment calculation. -/
theorem integral_mul_add_rpow_Ioi_zero {q m : ℝ}
    (hq : 2 < q) (hm : 0 < m) :
    ∫ t : ℝ in Ioi 0, t * (t + m) ^ (-q) =
      m ^ (-q + 2) / ((q - 1) * (q - 2)) := by
  have hq1 : -q + 1 < -1 := by linarith
  have hq0 : -q < -1 := by linarith
  have h1 : IntegrableOn (fun t : ℝ ↦ (t + m) ^ (-q + 1)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt hq1 (by linarith)
  have h2base : IntegrableOn (fun t : ℝ ↦ (t + m) ^ (-q)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt hq0 (by linarith)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      t * (t + m) ^ (-q) =
        (t + m) ^ (-q + 1) - m * (t + m) ^ (-q) := by
    intro t ht
    have htm : 0 < t + m := by linarith [mem_Ioi.mp ht]
    calc
      t * (t + m) ^ (-q) = ((t + m) - m) * (t + m) ^ (-q) := by ring
      _ = (t + m) * (t + m) ^ (-q) - m * (t + m) ^ (-q) := by ring
      _ = (t + m) ^ (-q + 1) - m * (t + m) ^ (-q) := by
        congr 1
        calc
          (t + m) * (t + m) ^ (-q) =
              (t + m) ^ (1 : ℝ) * (t + m) ^ (-q) := by
                rw [Real.rpow_one]
          _ = (t + m) ^ ((1 : ℝ) + (-q)) :=
            (Real.rpow_add htm _ _).symm
          _ = (t + m) ^ (-q + 1) := by ring_nf
  calc
    (∫ t : ℝ in Ioi 0, t * (t + m) ^ (-q)) =
        ∫ t : ℝ in Ioi 0,
          ((t + m) ^ (-q + 1) - m * (t + m) ^ (-q)) := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = (∫ t : ℝ in Ioi 0, (t + m) ^ (-q + 1)) -
        m * (∫ t : ℝ in Ioi 0, (t + m) ^ (-q)) := by
      rw [integral_sub h1 (h2base.const_mul m), integral_const_mul]
    _ = -m ^ ((-q + 1) + 1) / ((-q + 1) + 1) -
        m * (-m ^ ((-q) + 1) / ((-q) + 1)) := by
      rw [integral_add_rpow_Ioi_zero_of_lt hq1 hm,
        integral_add_rpow_Ioi_zero_of_lt hq0 hm]
    _ = m ^ (-q + 2) / ((q - 1) * (q - 2)) := by
      have hpow : m * m ^ (-q + 1) = m ^ (-q + 2) := by
        calc
          m * m ^ (-q + 1) = m ^ (1 : ℝ) * m ^ (-q + 1) := by
            rw [Real.rpow_one]
          _ = m ^ ((1 : ℝ) + (-q + 1)) :=
            (Real.rpow_add hm _ _).symm
          _ = m ^ (-q + 2) := by ring_nf
      have hrewrite : m * (-m ^ (-q + 1) / (-q + 1)) =
          -(m * m ^ (-q + 1)) / (-q + 1) := by ring
      rw [show -q + 1 + 1 = -q + 2 by ring, hrewrite, hpow]
      have hq1ne : q - 1 ≠ 0 := by linarith
      have hq2ne : q - 2 ≠ 0 := by linarith
      have h1qne : 1 - q ≠ 0 := by linarith
      have h2qne : 2 - q ≠ 0 := by linarith
      have hfrac2 : -m ^ (2 - q) / (2 - q) =
          m ^ (2 - q) / (q - 2) := by
        field_simp [hq2ne, h2qne]
        ring
      have hfrac1 : -m ^ (2 - q) / (1 - q) =
          m ^ (2 - q) / (q - 1) := by
        field_simp [hq1ne, h1qne]
        ring
      rw [show -q + 2 = 2 - q by ring, show -q + 1 = 1 - q by ring]
      rw [hfrac2, hfrac1]
      field_simp [hq1ne, hq2ne]
      ring

/-- The Laplace integral representing an inverse square. -/
theorem integral_mul_exp_neg_mul_Ioi_zero {z : ℝ} (hz : 0 < z) :
    ∫ t : ℝ in Ioi 0, t * Real.exp (-(z * t)) = 1 / z ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := z) (by norm_num) hz
  have hG2 : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num,
      Real.Gamma_add_one one_ne_zero, Real.Gamma_one]
    norm_num
  norm_num [hG2] at h ⊢
  simpa [mul_comm] using h

/-- Integrability companion to the inverse-square Laplace integral. -/
theorem integrableOn_mul_exp_neg_mul_Ioi_zero {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(z * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := z) (by norm_num) hz
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

/-- At a fixed nonnegative Laplace parameter, independence of the Gamma
coordinates factors the weighted second-moment integrand. -/
theorem integral_sq_mul_exp_neg_total_gammaWeight
    {n : ℕ} (hn : 0 < n) {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (i : Fin n) :
    ∫ w : Fin n → ℝ, w i ^ 2 * Real.exp (-(t * total w))
        ∂gammaWeightMeasure n α =
      (α * (α + 1) / (α + t) ^ 2) *
        (α / (α + t)) ^ (α * n) := by
  classical
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let f : (j : Fin n) → ℝ → ℝ := fun j x ↦
    Real.exp (-(t * x)) * if j = i then x ^ 2 else 1
  have hpoint (w : Fin n → ℝ) :
      w i ^ 2 * Real.exp (-(t * total w)) = ∏ j, f j (w j) := by
    have hexp : ∏ j : Fin n, Real.exp (-(t * w j)) =
        Real.exp (-(t * total w)) := by
      rw [← Real.exp_sum]
      unfold total
      congr 1
      rw [Finset.mul_sum]
      simpa using
        (Finset.sum_neg_distrib :
          (∑ x : Fin n, -(t * w x)) = -(∑ x : Fin n, t * w x))
    have hsq : ∏ j : Fin n, (if j = i then w j ^ 2 else 1) = w i ^ 2 := by
      simpa using (Fintype.prod_ite_eq' i (fun j ↦ w j ^ 2))
    simp only [f, Finset.prod_mul_distrib, hexp, hsq]
    ring
  have hi : ∫ x : ℝ, f i x ∂gammaMeasure α α =
      α * (α + 1) * α ^ α * (1 / (α + t)) ^ (α + 2) := by
    simp only [f, if_pos]
    have h := integral_sq_mul_exp_gammaMeasure hα hα
      (show -t < α by linarith)
    simpa [sub_neg, neg_mul, mul_comm] using h
  have hj (j : Fin n) (hji : j ≠ i) :
      ∫ x : ℝ, f j x ∂gammaMeasure α α =
        (α / (α + t)) ^ α := by
    simp only [f, if_neg hji, mul_one]
    have h := gamma_mgf hα hα (show -t < α by linarith)
    simpa [sub_neg, neg_mul] using h
  have hprod : ∏ j : Fin n, ∫ x : ℝ, f j x ∂gammaMeasure α α =
      (α * (α + 1) * α ^ α * (1 / (α + t)) ^ (α + 2)) *
        ((α / (α + t)) ^ α) ^ (n - 1) := by
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i), hi]
    congr 1
    calc
      (∏ j ∈ Finset.univ \ {i},
          ∫ x : ℝ, f j x ∂gammaMeasure α α) =
          ∏ _j ∈ Finset.univ \ {i}, (α / (α + t)) ^ α := by
        apply Finset.prod_congr rfl
        intro j hjmem
        have hji : j ≠ i := by simpa using hjmem
        rw [hj j hji]
      _ = ((α / (α + t)) ^ α) ^ (n - 1) := by
        rw [Finset.prod_const]
        congr 1
        rw [Finset.card_sdiff]
        simp
  have hbase : 0 < α + t := by linarith
  have hA : α * (α + 1) * α ^ α * (1 / (α + t)) ^ (α + 2) =
      (α * (α + 1) / (α + t) ^ 2) * (α / (α + t)) ^ α := by
    rw [show α + 2 = α + (2 : ℝ) by ring,
      Real.rpow_add (one_div_pos.mpr hbase), Real.rpow_two]
    rw [show α * (α + 1) * α ^ α *
        ((1 / (α + t)) ^ α * (1 / (α + t)) ^ 2) =
        α * (α + 1) * (α ^ α * (1 / (α + t)) ^ α) *
          (1 / (α + t)) ^ 2 by ring]
    rw [← Real.mul_rpow hα.le (one_div_pos.mpr hbase).le]
    have hden : α + t ≠ 0 := hbase.ne'
    field_simp
  calc
    (∫ w : Fin n → ℝ, w i ^ 2 * Real.exp (-(t * total w))
        ∂gammaWeightMeasure n α) =
        ∫ w : Fin n → ℝ, ∏ j, f j (w j)
          ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∏ j : Fin n, ∫ x : ℝ, f j x ∂gammaMeasure α α := by
      exact integral_fintype_prod_eq_prod f
    _ = (α * (α + 1) / (α + t) ^ 2) *
        (α / (α + t)) ^ (α * n) := by
      rw [hprod, hA]
      have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      have hpowN : (α / (α + t)) ^ α *
          ((α / (α + t)) ^ α) ^ (n - 1) =
          ((α / (α + t)) ^ α) ^ n := by
        calc
          (α / (α + t)) ^ α * ((α / (α + t)) ^ α) ^ (n - 1) =
              ((α / (α + t)) ^ α) ^ (n - 1) *
                (α / (α + t)) ^ α := by ring
          _ = ((α / (α + t)) ^ α) ^ ((n - 1) + 1) :=
            (pow_succ _ _).symm
          _ = ((α / (α + t)) ^ α) ^ n := by rw [hnsub]
      rw [show (α * (α + 1) / (α + t) ^ 2) *
          (α / (α + t)) ^ α * ((α / (α + t)) ^ α) ^ (n - 1) =
          (α * (α + 1) / (α + t) ^ 2) *
            ((α / (α + t)) ^ α *
              ((α / (α + t)) ^ α) ^ (n - 1)) by ring,
        hpowN]
      congr 1
      exact (Real.rpow_mul_natCast (div_nonneg hα.le hbase.le) α n).symm

/-- Integrability of the fixed-parameter product integrand used above. -/
theorem integrable_sq_mul_exp_neg_total_gammaWeight
    {n : ℕ} {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t) (i : Fin n) :
    Integrable (fun w : Fin n → ℝ ↦
      w i ^ 2 * Real.exp (-(t * total w)))
      (gammaWeightMeasure n α) := by
  classical
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let f : (j : Fin n) → ℝ → ℝ := fun j x ↦
    Real.exp (-(t * x)) * if j = i then x ^ 2 else 1
  have hf (j : Fin n) : Integrable (f j) (gammaMeasure α α) := by
    by_cases hji : j = i
    · subst j
      simp only [f, if_pos]
      have h := integrable_sq_mul_exp_gammaMeasure hα hα
        (show -t < α by linarith)
      apply h.congr
      exact Filter.Eventually.of_forall fun x ↦ by
        simp only [neg_mul]
        ring
    · simp only [f, if_neg hji, mul_one]
      simpa [neg_mul] using
        integrable_exp_mul_gammaMeasure hα hα (show -t < α by linarith)
  have hprod : Integrable
      (fun w : Fin n → ℝ ↦ ∏ j, f j (w j))
      (Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) :=
    Integrable.fintype_prod hf
  apply hprod.congr
  exact Filter.Eventually.of_forall fun w ↦ by
    have hexp : ∏ j : Fin n, Real.exp (-(t * w j)) =
        Real.exp (-(t * total w)) := by
      rw [← Real.exp_sum]
      unfold total
      congr 1
      rw [Finset.mul_sum]
      simpa using
        (Finset.sum_neg_distrib :
          (∑ x : Fin n, -(t * w x)) = -(∑ x : Fin n, t * w x))
    have hsq : ∏ j : Fin n, (if j = i then w j ^ 2 else 1) = w i ^ 2 := by
      simpa using (Fintype.prod_ite_eq' i (fun j ↦ w j ^ 2))
    simp only [f, Finset.prod_mul_distrib, hexp, hsq]
    ring

/-- Pointwise closed form of the Laplace integrand after factoring the
independent Gamma coordinates. -/
theorem laplace_sq_total_gammaWeight_eq_rpow
    {n : ℕ} (hn : 0 < n) {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (i : Fin n) :
    t * (∫ w : Fin n → ℝ,
      w i ^ 2 * Real.exp (-(t * total w))
        ∂gammaWeightMeasure n α) =
      (α * (α + 1) * α ^ (α * n)) *
        (t * (t + α) ^ (-(α * n + 2))) := by
  rw [integral_sq_mul_exp_neg_total_gammaWeight hn hα ht i]
  have hbase : 0 < α + t := by linarith
  have hratio :
      (α * (α + 1) / (α + t) ^ 2) *
          (α / (α + t)) ^ (α * n) =
        α * (α + 1) * α ^ (α * n) *
          (t + α) ^ (-(α * n + 2)) := by
    rw [Real.div_rpow hα.le hbase.le]
    rw [show t + α = α + t by ring]
    rw [show -(α * (n : ℝ) + 2) =
        -(α * (n : ℝ)) + -(2 : ℝ) by ring,
      Real.rpow_add hbase]
    rw [Real.rpow_neg hbase.le, Real.rpow_neg hbase.le, Real.rpow_two]
    have hrpow : (α + t) ^ (α * (n : ℝ)) ≠ 0 :=
      (Real.rpow_pos_of_pos hbase _).ne'
    have hbase0 : α + t ≠ 0 := hbase.ne'
    field_simp
  rw [hratio]
  ring

/-- Integrating the factored Laplace transform gives the exact normalized
Gamma coordinate second moment. -/
theorem integral_laplace_sq_total_gammaWeight
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    ∫ t : ℝ in Ioi 0,
        t * (∫ w : Fin n → ℝ,
          w i ^ 2 * Real.exp (-(t * total w))
            ∂gammaWeightMeasure n α) =
      (α + 1) / ((n : ℝ) * ((n : ℝ) * α + 1)) := by
  let p : ℝ := α * n
  let q : ℝ := p + 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 2 < q := by dsimp [q]; linarith
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      t * (∫ w : Fin n → ℝ,
        w i ^ 2 * Real.exp (-(t * total w))
          ∂gammaWeightMeasure n α) =
        (α * (α + 1) * α ^ p) * (t * (t + α) ^ (-q)) := by
    intro t ht
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    simpa [p, q] using
      laplace_sq_total_gammaWeight_eq_rpow hn hα ht0 i
  calc
    (∫ t : ℝ in Ioi 0,
        t * (∫ w : Fin n → ℝ,
          w i ^ 2 * Real.exp (-(t * total w))
            ∂gammaWeightMeasure n α)) =
        ∫ t : ℝ in Ioi 0,
          (α * (α + 1) * α ^ p) * (t * (t + α) ^ (-q)) := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = (α * (α + 1) * α ^ p) *
        (∫ t : ℝ in Ioi 0, t * (t + α) ^ (-q)) := by
      rw [integral_const_mul]
    _ = (α * (α + 1) * α ^ p) *
        (α ^ (-q + 2) / ((q - 1) * (q - 2))) := by
      rw [integral_mul_add_rpow_Ioi_zero hq hα]
    _ = (α + 1) / ((n : ℝ) * ((n : ℝ) * α + 1)) := by
      have hpow : α ^ p * α ^ (-p) = 1 := by
        rw [← Real.rpow_add hα]
        norm_num
      have hp0 : p ≠ 0 := hp.ne'
      have hp10 : p + 1 ≠ 0 := by positivity
      dsimp [q]
      rw [show -(p + 2) + 2 = -p by ring]
      rw [show α * (α + 1) * α ^ p *
          (α ^ (-p) / ((p + 2 - 1) * (p + 2 - 2))) =
          α * (α + 1) * (α ^ p * α ^ (-p)) /
            ((p + 1) * p) by ring,
        hpow]
      dsimp [p]
      field_simp

/-- Nonnegative joint kernel whose `t`-integral is the square of a normalized
Gamma coordinate. -/
noncomputable def gammaRatioSecondMomentKernel {n : ℕ} (i : Fin n)
    (w : Fin n → ℝ) (t : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator
    (fun s ↦ s * (w i) ^ 2 * Real.exp (-(s * total w))) t

/-- The joint inverse-square Laplace kernel is integrable, so Fubini applies. -/
theorem integrable_gammaRatioSecondMomentKernel
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    Integrable (Function.uncurry (gammaRatioSecondMomentKernel i))
      ((gammaWeightMeasure n α).prod volume) := by
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  let p : ℝ := α * n
  let q : ℝ := p + 2
  let C : ℝ := α * (α + 1) * α ^ p
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 2 < q := by dsimp [q]; linarith
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (gammaRatioSecondMomentKernel i))
      ((gammaWeightMeasure n α).prod volume) := by
    have hset : MeasurableSet
        {z : (Fin n → ℝ) × ℝ | z.2 ∈ Ioi (0 : ℝ)} :=
      measurableSet_lt measurable_const measurable_snd
    have hfun : Measurable (fun z : (Fin n → ℝ) × ℝ ↦
        z.2 * (z.1 i) ^ 2 * Real.exp (-(z.2 * total z.1))) := by
      have hcoord : Measurable (fun z : (Fin n → ℝ) × ℝ ↦ z.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      have htot : Measurable (fun z : (Fin n → ℝ) × ℝ ↦ total z.1) :=
        measurable_total.comp measurable_fst
      exact (measurable_snd.mul (hcoord.pow_const 2)).mul
        ((measurable_snd.mul htot).neg.exp)
    have hind := hfun.indicator hset
    simpa [Function.uncurry, gammaRatioSecondMomentKernel, Set.indicator] using
      hind.aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards with t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [Function.uncurry_apply_pair,
        gammaRatioSecondMomentKernel, indicator_of_mem ht]
      have h := (integrable_sq_mul_exp_neg_total_gammaWeight
        hα (mem_Ioi.mp ht).le i).const_mul t
      apply h.congr
      exact Filter.Eventually.of_forall fun w ↦ by ring
    · simp [Function.uncurry_apply_pair,
        gammaRatioSecondMomentKernel, indicator_of_notMem ht]
  · have hclosedOn : IntegrableOn
        (fun t : ℝ ↦ C * (t * (t + α) ^ (-q))) (Ioi 0) :=
      (integrableOn_mul_add_rpow_Ioi_zero hq hα).const_mul C
    have hclosed : Integrable
        ((Ioi (0 : ℝ)).indicator
          (fun t : ℝ ↦ C * (t * (t + α) ^ (-q)))) volume :=
      (integrable_indicator_iff measurableSet_Ioi).2 hclosedOn
    apply hclosed.congr
    exact Filter.Eventually.of_forall fun t ↦ by
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht]
        simp only [Function.uncurry_apply_pair,
          gammaRatioSecondMomentKernel, indicator_of_mem ht]
        have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
        have hnonneg (w : Fin n → ℝ) :
            0 ≤ t * (w i) ^ 2 * Real.exp (-(t * total w)) := by positivity
        simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
        rw [show (∫ x : Fin n → ℝ,
            t * x i ^ 2 * Real.exp (-(t * total x))
              ∂gammaWeightMeasure n α) =
            t * (∫ x : Fin n → ℝ,
              x i ^ 2 * Real.exp (-(t * total x))
                ∂gammaWeightMeasure n α) by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun w ↦ by ring]
        simpa [C, p, q] using
          (laplace_sq_total_gammaWeight_eq_rpow hn hα ht0 i).symm
      · simp [gammaRatioSecondMomentKernel, indicator_of_notMem ht]

/-- Exact second moment of one coordinate in the normalized-Gamma
representation of the symmetric Dirichlet law. -/
theorem normalized_gamma_coordinate_second_moment
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    ∫ w : Fin n → ℝ, (normalize w i) ^ 2
        ∂gammaWeightMeasure n α =
      (α + 1) / ((n : ℝ) * ((n : ℝ) * α + 1)) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  have hF := integrable_gammaRatioSecondMomentKernel hn hα i
  have hswap := integral_integral_swap hF
  have hleft : ∀ᵐ w ∂gammaWeightMeasure n α,
      ∫ t : ℝ, gammaRatioSecondMomentKernel i w t =
        (normalize w i) ^ 2 := by
    filter_upwards [gammaWeightMeasure_ae_pos (n := n) hα] with w hw
    have htotal : 0 < total w := total_pos hw
    unfold gammaRatioSecondMomentKernel
    rw [integral_indicator measurableSet_Ioi]
    rw [show (∫ t : ℝ in Ioi 0,
        t * w i ^ 2 * Real.exp (-(t * total w))) =
        w i ^ 2 * (∫ t : ℝ in Ioi 0,
          t * Real.exp (-((total w) * t))) by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      ring_nf
      ]
    rw [integral_mul_exp_neg_mul_Ioi_zero htotal]
    unfold normalize
    field_simp [htotal.ne']
  have hright (t : ℝ) :
      (∫ w : Fin n → ℝ, gammaRatioSecondMomentKernel i w t
          ∂gammaWeightMeasure n α) =
        (Ioi (0 : ℝ)).indicator
          (fun s ↦ s * (∫ w : Fin n → ℝ,
            w i ^ 2 * Real.exp (-(s * total w))
              ∂gammaWeightMeasure n α)) t := by
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [gammaRatioSecondMomentKernel,
        indicator_of_mem ht]
      rw [show (∫ w : Fin n → ℝ,
          t * w i ^ 2 * Real.exp (-(t * total w))
            ∂gammaWeightMeasure n α) =
          t * (∫ w : Fin n → ℝ,
            w i ^ 2 * Real.exp (-(t * total w))
              ∂gammaWeightMeasure n α) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w ↦ by ring]
    · simp [gammaRatioSecondMomentKernel, indicator_of_notMem ht]
  calc
    (∫ w : Fin n → ℝ, (normalize w i) ^ 2
        ∂gammaWeightMeasure n α) =
        ∫ w : Fin n → ℝ,
          (∫ t : ℝ, gammaRatioSecondMomentKernel i w t)
            ∂gammaWeightMeasure n α := by
      apply integral_congr_ae
      exact Filter.EventuallyEq.symm hleft
    _ = ∫ t : ℝ, ∫ w : Fin n → ℝ,
        gammaRatioSecondMomentKernel i w t
          ∂gammaWeightMeasure n α := hswap
    _ = ∫ t : ℝ in Ioi 0,
        t * (∫ w : Fin n → ℝ,
          w i ^ 2 * Real.exp (-(t * total w))
            ∂gammaWeightMeasure n α) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hright
    _ = (α + 1) / ((n : ℝ) * ((n : ℝ) * α + 1)) :=
      integral_laplace_sq_total_gammaWeight hn hα i

/-- A squared normalized-Gamma coordinate is integrable. -/
theorem integrable_normalize_coord_sq_gammaWeightMeasure
    {n : ℕ} {α : ℝ} (hα : 0 < α) (i : Fin n) :
    Integrable (fun w : Fin n → ℝ ↦ (normalize w i) ^ 2)
      (gammaWeightMeasure n α) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  apply Integrable.of_bound
      (((measurable_pi_apply i).comp measurable_normalize).pow_const 2).aestronglyMeasurable 1
  filter_upwards [gammaWeightMeasure_ae_pos (n := n) hα] with w hw
  have hnonneg (j : Fin n) : 0 ≤ w j := (hw j).le
  have hwi : w i ≤ total w :=
    Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
  have htotal : 0 < total w := total_pos hw
  have hnorm0 : 0 ≤ normalize w i := (normalize_pos hw i).le
  have hnorm1 : normalize w i ≤ 1 := by
    rw [normalize, div_le_one htotal]
    exact hwi
  change ‖(normalize w i) ^ 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- Exact coordinate second moment under the symmetric Dirichlet pushforward. -/
theorem symmetricDirichlet_coordinate_second_moment
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    ∫ p : Fin n → ℝ, (p i) ^ 2 ∂symmetricDirichletMeasure n α =
      (α + 1) / ((n : ℝ) * ((n : ℝ) * α + 1)) := by
  rw [symmetricDirichletMeasure,
    integral_map measurable_normalize.aemeasurable
      ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable]
  exact normalized_gamma_coordinate_second_moment hn hα i

/-- Integrability of a squared Dirichlet coordinate. -/
theorem integrable_sq_coord_symmetricDirichletMeasure
    {n : ℕ} {α : ℝ} (hα : 0 < α) (i : Fin n) :
    Integrable (fun p : Fin n → ℝ ↦ (p i) ^ 2)
      (symmetricDirichletMeasure n α) := by
  rw [symmetricDirichletMeasure]
  apply (integrable_map_measure
    ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
    measurable_normalize.aemeasurable).2
  simpa [Function.comp_def] using
    integrable_normalize_coord_sq_gammaWeightMeasure hα i

/-- The diagonal entry of the actual normalized-Gamma covariance has the
standard symmetric Dirichlet value. -/
theorem symmetricDirichletActualCovariance_diag_exact
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    symmetricDirichletActualCovariance n α i i =
      ((n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1)) := by
  letI : IsProbabilityMeasure (symmetricDirichletMeasure n α) :=
    symmetricDirichletMeasure_isProbability n hα
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hden : (n : ℝ) * α + 1 ≠ 0 := by positivity
  unfold symmetricDirichletActualCovariance
  have hsq := integrable_sq_coord_symmetricDirichletMeasure hα i
  have hlin :=
    (integrable_coord_symmetricDirichletMeasure hα i).const_mul (2 / (n : ℝ))
  have hc : Integrable (fun _p : Fin n → ℝ ↦ (1 / (n : ℝ)) ^ 2)
      (symmetricDirichletMeasure n α) := integrable_const _
  calc
    (∫ p : Fin n → ℝ, (p i - 1 / n) * (p i - 1 / n)
        ∂symmetricDirichletMeasure n α) =
        ∫ p : Fin n → ℝ,
          (p i) ^ 2 - (2 / n) * p i + (1 / n) ^ 2
            ∂symmetricDirichletMeasure n α := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by ring
    _ = (∫ p : Fin n → ℝ, (p i) ^ 2
          ∂symmetricDirichletMeasure n α) -
        (2 / n) * (∫ p : Fin n → ℝ, p i
          ∂symmetricDirichletMeasure n α) + (1 / n) ^ 2 := by
      have hsum :
          (∫ p : Fin n → ℝ,
            (p i) ^ 2 - (2 / (n : ℝ)) * p i + (1 / (n : ℝ)) ^ 2
              ∂symmetricDirichletMeasure n α) =
          (∫ p : Fin n → ℝ, (p i) ^ 2 - (2 / (n : ℝ)) * p i
              ∂symmetricDirichletMeasure n α) +
            ∫ _p : Fin n → ℝ, (1 / (n : ℝ)) ^ 2
              ∂symmetricDirichletMeasure n α := by
        exact integral_add (hsq.sub hlin) hc
      have hsub :
          (∫ p : Fin n → ℝ, (p i) ^ 2 - (2 / n) * p i
              ∂symmetricDirichletMeasure n α) =
          (∫ p : Fin n → ℝ, (p i) ^ 2
              ∂symmetricDirichletMeasure n α) -
            ∫ p : Fin n → ℝ, (2 / n) * p i
              ∂symmetricDirichletMeasure n α := by
        exact integral_sub hsq hlin
      rw [hsum, hsub, integral_const_mul]
      simp
    _ = ((n : ℝ) - 1) /
        ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1)) := by
      rw [symmetricDirichlet_coordinate_second_moment hn hα,
        symmetricDirichlet_coordinate_mean hn hα]
      field_simp
      ring

/-- Unconditional identification of the full normalized-Gamma covariance
matrix with the standard symmetric Dirichlet covariance. -/
theorem symmetricDirichletActualCovariance_eq
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∀ i j : Fin n,
      symmetricDirichletActualCovariance n α i j =
        symmetricDirichletCovariance n α i j :=
  symmetricDirichletActualCovariance_eq_of_diag hn hα
    (symmetricDirichletActualCovariance_diag_exact hn hα)

/-- Exact variance formula for every symmetric-Dirichlet-weighted empirical
statistic. -/
theorem symmetricDirichlet_weighted_empirical_variance
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (h : Fin n → ℝ) :
    ∫ p : Fin n → ℝ,
        ((∑ i, p i * h i) - empiricalMean h) ^ 2
          ∂symmetricDirichletMeasure n α =
      (empiricalSecondMoment h - (empiricalMean h) ^ 2) /
        ((n : ℝ) * α + 1) :=
  symmetricDirichlet_weighted_empirical_variance_of_covariance_eq
    hn hα (symmetricDirichletActualCovariance_eq hn hα) h

/-- The manuscript's sharp expected total-variation deviation bound for
symmetric Dirichlet weights. -/
theorem symmetricDirichlet_expected_tv_le
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∫ p : Fin n → ℝ, symmetricDirichletTVDeviation p
        ∂symmetricDirichletMeasure n α ≤
      (1 / 2 : ℝ) * Real.sqrt (((n : ℝ) - 1) /
        ((n : ℝ) * α + 1)) :=
  symmetricDirichlet_expected_tv_le_of_covariance_eq
    hn hα (symmetricDirichletActualCovariance_eq hn hα)

end ReweightedNPMLE
