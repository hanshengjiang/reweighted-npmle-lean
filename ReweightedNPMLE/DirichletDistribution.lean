import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Group.Arithmetic
import ReweightedNPMLE.DirichletMoments
import ReweightedNPMLE.FiniteOptimizerFiber
import ReweightedNPMLE.GammaDistribution
import ReweightedNPMLE.MGFUniqueness
import ReweightedNPMLE.Weights
import Mathlib.Tactic

/-!
# Normalized Gamma and symmetric Dirichlet laws

We define the symmetric Dirichlet law canonically as the pushforward of an
independent Gamma product by coordinate normalization.  This makes the
Gamma--Dirichlet representation literal while keeping the development
dependent only on mathlib, which currently has Gamma but no Dirichlet measure.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ReweightedNPMLE

/-- Law of `n` independent shape--rate `Gamma(α,α)` weights. -/
noncomputable def gammaWeightMeasure (n : ℕ) (α : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)

theorem measurable_total {n : ℕ} :
    Measurable (total : (Fin n → ℝ) → ℝ) := by
  unfold total
  fun_prop

theorem measurable_normalize {n : ℕ} :
    Measurable (normalize : (Fin n → ℝ) → Fin n → ℝ) := by
  unfold normalize
  exact measurable_pi_lambda _ fun i ↦
    (measurable_pi_apply i).div measurable_total

/-- Reindexing a finite weight vector does not change its total mass. -/
theorem total_piCongrLeft {n : ℕ} (e : Equiv.Perm (Fin n))
    (w : Fin n → ℝ) :
    total (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e w) = total w := by
  classical
  unfold total
  rw [← Equiv.sum_comp e
    (fun i ↦ MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e w i)]
  apply Finset.sum_congr rfl
  intro i _
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin n ↦ ℝ) e w i

/-- Normalization commutes with a permutation of the coordinates. -/
theorem normalize_piCongrLeft {n : ℕ} (e : Equiv.Perm (Fin n))
    (w : Fin n → ℝ) (i : Fin n) :
    normalize (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e w) (e i) =
      normalize w i := by
  rw [normalize, total_piCongrLeft, normalize]
  congr 1
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin n ↦ ℝ) e w i

/-- Function-valued form of permutation equivariance of normalization. -/
theorem normalize_piCongrLeft_fun {n : ℕ} (e : Equiv.Perm (Fin n))
    (w : Fin n → ℝ) :
    normalize (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e w) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e (normalize w) := by
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  calc
    normalize (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e w) (e j) =
        normalize w j := normalize_piCongrLeft e w j
    _ = MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e (normalize w) (e j) :=
      (MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Fin n ↦ ℝ) e (normalize w) j).symm

/-- Symmetric Dirichlet law, defined by normalized independent Gamma weights. -/
noncomputable def symmetricDirichletMeasure (n : ℕ) (α : ℝ) :
    Measure (Fin n → ℝ) :=
  (gammaWeightMeasure n α).map normalize

/-- The normalized-Gamma representation is definitional for our Dirichlet law. -/
theorem normalized_gamma_has_symmetricDirichlet_law (n : ℕ) (α : ℝ) :
    (gammaWeightMeasure n α).map normalize =
      symmetricDirichletMeasure n α := rfl

theorem gammaWeightMeasure_isProbability (n : ℕ) {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (gammaWeightMeasure n α) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  exact Measure.pi.instIsProbabilityMeasure _

/-- Exponential integrability of the total independent Gamma weight below
the common rate. -/
theorem integrable_exp_mul_total_gammaWeight (n : ℕ) {α t : ℝ}
    (hα : 0 < α) (ht : t < α) :
    Integrable (fun w : Fin n → ℝ ↦ Real.exp (t * total w))
      (gammaWeightMeasure n α) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  have hprod : Integrable
      (fun w : Fin n → ℝ ↦ ∏ i, Real.exp (t * w i))
      (Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) :=
    Integrable.fintype_prod (fun _ ↦ integrable_exp_mul_gammaMeasure hα hα ht)
  apply hprod.congr
  exact Filter.Eventually.of_forall fun w ↦ by
    unfold total
    change (∏ i, Real.exp (t * w i)) = Real.exp (t * ∑ i, w i)
    rw [Finset.mul_sum, Real.exp_sum]

/-- MGF of the total of the independent Gamma weights. -/
theorem total_gammaWeight_mgf (n : ℕ) {α t : ℝ}
    (hα : 0 < α) (ht : t < α) :
    ∫ w : Fin n → ℝ, Real.exp (t * total w) ∂gammaWeightMeasure n α =
      (α / (α - t)) ^ (α * n) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  have hpoint (w : Fin n → ℝ) :
      Real.exp (t * total w) = ∏ i, Real.exp (t * w i) := by
    unfold total
    rw [Finset.mul_sum, Real.exp_sum]
  calc
    ∫ w : Fin n → ℝ, Real.exp (t * total w) ∂gammaWeightMeasure n α =
        ∫ w : Fin n → ℝ, ∏ i, Real.exp (t * w i)
          ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ = (∫ y : ℝ, Real.exp (t * y) ∂gammaMeasure α α) ^ n := by
      simpa using (integral_fintype_prod_eq_pow (ι := Fin n)
        (μ := gammaMeasure α α) (fun y : ℝ ↦ Real.exp (t * y)))
    _ = ((α / (α - t)) ^ α) ^ n := by rw [gamma_mgf hα hα ht]
    _ = (α / (α - t)) ^ (α * n) := by
      symm
      exact Real.rpow_mul_natCast (by positivity) α n

/-- The total-weight MGF agrees with `Gamma(nα,α)`. -/
theorem total_gammaWeight_mgf_eq_gamma (n : ℕ) (hn : 0 < n)
    {α t : ℝ} (hα : 0 < α) (ht : t < α) :
    ∫ w : Fin n → ℝ, Real.exp (t * total w) ∂gammaWeightMeasure n α =
      ∫ y : ℝ, Real.exp (t * y) ∂gammaMeasure (n * α) α := by
  rw [total_gammaWeight_mgf n hα ht,
    gamma_mgf (mul_pos (by exact_mod_cast hn) hα) hα ht]
  congr 1
  ring

/-- The total of the independent shape--rate `Gamma(α,α)` coordinates has
the exact `Gamma(nα,α)` law, not merely the same displayed MGF. -/
theorem total_gammaWeight_map_eq_gamma (n : ℕ) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) :
    (gammaWeightMeasure n α).map total = gammaMeasure (n * α) α := by
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  letI : IsProbabilityMeasure (gammaMeasure (n * α) α) :=
    isProbabilityMeasure_gammaMeasure (mul_pos (by exact_mod_cast hn) hα) hα
  have hmap := Measure.map_eq_of_mgf_eq_on_Ioo
    (μ := gammaWeightMeasure n α) (μ' := gammaMeasure (n * α) α)
    total id (l := -α) (u := α) (neg_lt_zero.mpr hα) hα
    measurable_total.aemeasurable aemeasurable_id
    (fun t ht ↦ integrable_exp_mul_total_gammaWeight n hα ht.2)
    (fun t ht ↦ by
      simpa only [id_eq] using
        integrable_exp_mul_gammaMeasure
          (mul_pos (by exact_mod_cast hn) hα) hα ht.2)
    (fun t ht ↦ by
      simpa only [mgf, id_eq] using
        total_gammaWeight_mgf_eq_gamma n hn hα ht.2)
  simpa using hmap

theorem symmetricDirichletMeasure_isProbability (n : ℕ) {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (symmetricDirichletMeasure n α) := by
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  exact Measure.isProbabilityMeasure_map measurable_normalize.aemeasurable

/-- Every coordinate of the independent Gamma vector is strictly positive
almost surely.  This is the null-boundary fact needed to normalize the vector. -/
theorem gammaWeightMeasure_ae_pos {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∀ᵐ w ∂gammaWeightMeasure n α, ∀ i, 0 < w i := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  rw [Filter.eventually_all]
  intro i
  apply (measurePreserving_eval
    (fun _ : Fin n ↦ gammaMeasure α α) i).quasiMeasurePreserving.ae
  rw [ae_iff]
  simpa only [not_lt, Set.setOf_mem_eq] using gammaMeasure_Iic_zero hα hα

/-- A normalized Gamma coordinate is integrable; in fact it lies in `[0,1]`
almost surely. -/
theorem integrable_normalize_coord_gammaWeightMeasure {n : ℕ} {α : ℝ}
    (hα : 0 < α) (i : Fin n) :
    Integrable (fun w : Fin n → ℝ ↦ normalize w i) (gammaWeightMeasure n α) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  apply Integrable.of_bound
      ((measurable_pi_apply i).comp measurable_normalize).aestronglyMeasurable 1
  filter_upwards [gammaWeightMeasure_ae_pos (n := n) hα] with w hw
  have hnonneg (j : Fin n) : 0 ≤ w j := (hw j).le
  have hwi : w i ≤ total w := by
    exact Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i)
  have htotal : 0 < total w := total_pos hw
  have hnorm_nonneg : 0 ≤ normalize w i := (normalize_pos hw i).le
  have hnorm_le : normalize w i ≤ 1 := by
    rw [normalize, div_le_one htotal]
    exact hwi
  simpa [Real.norm_eq_abs, abs_of_nonneg hnorm_nonneg] using hnorm_le

/-- The independent Gamma product is exchangeable under every permutation of
its coordinates. -/
theorem gammaWeightMeasure_measurePreserving_piCongrLeft {n : ℕ} {α : ℝ}
    (hα : 0 < α) (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e)
      (gammaWeightMeasure n α) (gammaWeightMeasure n α) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  simpa [gammaWeightMeasure] using
    (measurePreserving_piCongrLeft
      (fun _ : Fin n ↦ gammaMeasure α α) e)

/-- The full symmetric Dirichlet law, not merely its first moments, is
invariant under coordinate permutations. -/
theorem symmetricDirichletMeasure_map_piCongrLeft {n : ℕ} {α : ℝ}
    (hα : 0 < α) (e : Equiv.Perm (Fin n)) :
    (symmetricDirichletMeasure n α).map
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e) =
      symmetricDirichletMeasure n α := by
  let q : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hq : Measurable (q : (Fin n → ℝ) → Fin n → ℝ) := q.measurable
  have hpres := gammaWeightMeasure_measurePreserving_piCongrLeft hα e
  change ((gammaWeightMeasure n α).map normalize).map q =
    (gammaWeightMeasure n α).map normalize
  rw [Measure.map_map hq measurable_normalize]
  calc
    (gammaWeightMeasure n α).map (q ∘ normalize) =
        (gammaWeightMeasure n α).map (normalize ∘ q) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun w ↦
        (normalize_piCongrLeft_fun e w).symm
    _ = ((gammaWeightMeasure n α).map q).map normalize := by
      rw [Measure.map_map measurable_normalize hq]
    _ = (gammaWeightMeasure n α).map normalize := by rw [hpres.map_eq]

theorem measurableSet_finiteSimplex (n : ℕ) :
    MeasurableSet (finiteSimplex n) := by
  have hnonneg : MeasurableSet {p : Fin n → ℝ | ∀ i, 0 ≤ p i} := by
    exact measurableSet_setOf.mpr (by fun_prop)
  have hsum : MeasurableSet {p : Fin n → ℝ | ∑ i, p i = 1} :=
    measurableSet_eq_fun measurable_total measurable_const
  rw [show finiteSimplex n =
      {p : Fin n → ℝ | ∀ i, 0 ≤ p i} ∩ {p | ∑ i, p i = 1} by
    ext p
    simp [finiteSimplex]]
  exact hnonneg.inter hsum

/-- A draw from the normalized-Gamma Dirichlet law lies in the probability
simplex almost surely. -/
theorem symmetricDirichletMeasure_ae_mem_finiteSimplex
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∀ᵐ p ∂symmetricDirichletMeasure n α, p ∈ finiteSimplex n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  change ∀ᵐ p ∂(gammaWeightMeasure n α).map normalize,
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1
  have hs : MeasurableSet
      {p : Fin n → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1} := by
    simpa [finiteSimplex] using measurableSet_finiteSimplex n
  rw [ae_map_iff measurable_normalize.aemeasurable hs]
  filter_upwards [gammaWeightMeasure_ae_pos (n := n) hα] with w hw
  exact ⟨fun i ↦ (normalize_pos hw i).le, sum_normalize (total_ne_zero hw)⟩

/-- Exchangeability makes all normalized-Gamma coordinate expectations equal. -/
theorem integral_normalize_coord_eq {n : ℕ} {α : ℝ} (hα : 0 < α)
    (i j : Fin n) :
    ∫ w : Fin n → ℝ, normalize w i ∂gammaWeightMeasure n α =
      ∫ w : Fin n → ℝ, normalize w j ∂gammaWeightMeasure n α := by
  let e : Equiv.Perm (Fin n) := Equiv.swap i j
  let q : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hpoint (w : Fin n → ℝ) : normalize (q w) i = normalize w j := by
    have h := normalize_piCongrLeft e w j
    simpa [e, q] using h
  have hpres : MeasurePreserving q (gammaWeightMeasure n α)
      (gammaWeightMeasure n α) := by
    simpa [q] using gammaWeightMeasure_measurePreserving_piCongrLeft hα e
  calc
    (∫ w : Fin n → ℝ, normalize w i ∂gammaWeightMeasure n α) =
        ∫ w : Fin n → ℝ, normalize (q w) i ∂gammaWeightMeasure n α :=
      (hpres.integral_comp' (fun w : Fin n → ℝ ↦ normalize w i)).symm
    _ = ∫ w : Fin n → ℝ, normalize w j ∂gammaWeightMeasure n α := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint

/-- The actual first moment of a symmetric Dirichlet coordinate, proved from
the normalized-Gamma construction, exchangeability, and the simplex identity. -/
theorem normalized_gamma_coordinate_mean {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (i : Fin n) :
    ∫ w : Fin n → ℝ, normalize w i ∂gammaWeightMeasure n α =
      1 / n := by
  letI : Nonempty (Fin n) := ⟨i⟩
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  have hsum :
      ∑ j : Fin n,
          ∫ w : Fin n → ℝ, normalize w j ∂gammaWeightMeasure n α = 1 := by
    rw [← integral_finsetSum Finset.univ
      (fun j _ ↦ integrable_normalize_coord_gammaWeightMeasure hα j)]
    calc
      (∫ w : Fin n → ℝ, ∑ j, normalize w j ∂gammaWeightMeasure n α) =
          ∫ _w : Fin n → ℝ, (1 : ℝ) ∂gammaWeightMeasure n α := by
        apply integral_congr_ae
        filter_upwards [gammaWeightMeasure_ae_pos (n := n) hα] with w hw
        exact sum_normalize (total_ne_zero hw)
      _ = 1 := by simp
  have heq (j : Fin n) :
      (∫ w : Fin n → ℝ, normalize w j ∂gammaWeightMeasure n α) =
        ∫ w : Fin n → ℝ, normalize w i ∂gammaWeightMeasure n α :=
    integral_normalize_coord_eq hα j i
  simp_rw [heq] at hsum
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_mul_inv]
  simp only [one_mul]
  exact eq_inv_of_mul_eq_one_right (by simpa [mul_comm] using hsum)

/-- Hence a coordinate sampled from the symmetric Dirichlet law has mean
`1/n`. -/
theorem symmetricDirichlet_coordinate_mean {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (i : Fin n) :
    ∫ p : Fin n → ℝ, p i ∂symmetricDirichletMeasure n α = 1 / n := by
  rw [symmetricDirichletMeasure,
    integral_map measurable_normalize.aemeasurable
      (measurable_pi_apply i).aestronglyMeasurable]
  exact normalized_gamma_coordinate_mean hn hα i

theorem integrable_coord_symmetricDirichletMeasure {n : ℕ} {α : ℝ}
    (hα : 0 < α) (i : Fin n) :
    Integrable (fun p : Fin n → ℝ ↦ p i) (symmetricDirichletMeasure n α) := by
  rw [symmetricDirichletMeasure]
  apply (integrable_map_measure
    (measurable_pi_apply i).aestronglyMeasurable
    measurable_normalize.aemeasurable).2
  simpa [Function.comp_def] using
    integrable_normalize_coord_gammaWeightMeasure hα i

/-- Covariance of two coordinates of the normalized-Gamma Dirichlet law. -/
noncomputable def symmetricDirichletActualCovariance
    (n : ℕ) (α : ℝ) (i j : Fin n) : ℝ :=
  ∫ p : Fin n → ℝ, (p i - 1 / n) * (p j - 1 / n)
    ∂symmetricDirichletMeasure n α

/-- Permutation invariance of the actual covariance matrix. -/
theorem symmetricDirichletActualCovariance_perm
    {n : ℕ} {α : ℝ} (hα : 0 < α) (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    symmetricDirichletActualCovariance n α (e i) (e j) =
      symmetricDirichletActualCovariance n α i j := by
  let q : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hmap := symmetricDirichletMeasure_map_piCongrLeft hα e
  unfold symmetricDirichletActualCovariance
  let F : (Fin n → ℝ) → ℝ :=
    fun p ↦ (p (e i) - 1 / n) * (p (e j) - 1 / n)
  calc
    (∫ p : Fin n → ℝ, F p ∂symmetricDirichletMeasure n α) =
        ∫ p : Fin n → ℝ, F p
          ∂(symmetricDirichletMeasure n α).map q :=
      (congrArg (fun μ : Measure (Fin n → ℝ) ↦ ∫ p, F p ∂μ) hmap).symm
    _ = ∫ p : Fin n → ℝ, F (q p) ∂symmetricDirichletMeasure n α :=
      integral_map q.measurable.aemeasurable (by fun_prop)
    _ = ∫ p : Fin n → ℝ, (p i - 1 / n) * (p j - 1 / n)
          ∂symmetricDirichletMeasure n α := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by
        simp only [F, q, MeasurableEquiv.piCongrLeft_apply_apply]

theorem symmetricDirichletActualCovariance_diag_eq
    {n : ℕ} {α : ℝ} (hα : 0 < α) (i j : Fin n) :
    symmetricDirichletActualCovariance n α i i =
      symmetricDirichletActualCovariance n α j j := by
  simpa using
    (symmetricDirichletActualCovariance_perm hα (Equiv.swap i j) i i).symm

theorem symmetricDirichletActualCovariance_offdiag_eq
    {n : ℕ} {α : ℝ} (hα : 0 < α) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) :
    symmetricDirichletActualCovariance n α i j =
      symmetricDirichletActualCovariance n α i k := by
  have h := symmetricDirichletActualCovariance_perm hα (Equiv.swap j k) i j
  rw [Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left] at h
  exact h.symm

theorem integrable_centered_coord_symmetricDirichletMeasure
    {n : ℕ} {α : ℝ} (hα : 0 < α) (i : Fin n) :
    Integrable (fun p : Fin n → ℝ ↦ p i - 1 / n)
      (symmetricDirichletMeasure n α) := by
  letI : IsProbabilityMeasure (symmetricDirichletMeasure n α) :=
    symmetricDirichletMeasure_isProbability n hα
  exact (integrable_coord_symmetricDirichletMeasure hα i).sub (integrable_const _)

theorem integrable_centered_coord_mul_symmetricDirichletMeasure
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i j : Fin n) :
    Integrable (fun p : Fin n → ℝ ↦ (p i - 1 / n) * (p j - 1 / n))
      (symmetricDirichletMeasure n α) := by
  let μ := symmetricDirichletMeasure n α
  have hmeas : AEStronglyMeasurable (fun p : Fin n → ℝ ↦ p i - 1 / n) μ :=
    ((measurable_pi_apply i).sub measurable_const).aestronglyMeasurable
  apply (integrable_centered_coord_symmetricDirichletMeasure hα j).bdd_mul
    (c := 1) hmeas
  filter_upwards [symmetricDirichletMeasure_ae_mem_finiteSimplex hn hα] with p hp
  have hpi0 : 0 ≤ p i := hp.1 i
  have hpile : p i ≤ 1 := by
    have := Finset.single_le_sum (fun k _ ↦ hp.1 k) (Finset.mem_univ i)
    simpa [hp.2] using this
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv0 : 0 ≤ (1 / (n : ℝ)) := by positivity
  have hinv1 : (1 / (n : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hnreal
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The actual covariance matrix of the normalized-Gamma law annihilates the
all-one direction.  This follows solely from its simplex support and exact
coordinate mean, before evaluating the closed-form Dirichlet second moment. -/
theorem symmetricDirichletActualCovariance_row_sum
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    ∑ j, symmetricDirichletActualCovariance n α i j = 0 := by
  unfold symmetricDirichletActualCovariance
  rw [← integral_finsetSum Finset.univ
    (fun j _ ↦
      integrable_centered_coord_mul_symmetricDirichletMeasure hn hα i j)]
  apply integral_eq_zero_of_ae
  filter_upwards [symmetricDirichletMeasure_ae_mem_finiteSimplex hn hα] with p hp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    (∑ j : Fin n, (p i - 1 / n) * (p j - 1 / n)) =
        (p i - 1 / n) * ∑ j : Fin n, (p j - 1 / n) := by
      rw [Finset.mul_sum]
    _ = 0 := by
      rw [Finset.sum_sub_distrib, hp.2]
      simp [hn0]

/-- Once one off-diagonal coordinate is chosen, simplex support and
exchangeability force the usual diagonal/off-diagonal row relation. -/
theorem symmetricDirichletActualCovariance_diag_add_offdiag
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    {i j : Fin n} (hij : i ≠ j) :
    symmetricDirichletActualCovariance n α i i +
        (n - 1) * symmetricDirichletActualCovariance n α i j = 0 := by
  have hn1 : 1 ≤ n := by omega
  have hrow := symmetricDirichletActualCovariance_row_sum hn hα i
  have herase :
      ∑ k ∈ (Finset.univ.erase i), symmetricDirichletActualCovariance n α i k =
        (n - 1) * symmetricDirichletActualCovariance n α i j := by
    calc
      (∑ k ∈ (Finset.univ.erase i),
          symmetricDirichletActualCovariance n α i k) =
          ∑ _k ∈ (Finset.univ.erase i),
            symmetricDirichletActualCovariance n α i j := by
        apply Finset.sum_congr rfl
        intro k hk
        have hik : i ≠ k := (Finset.ne_of_mem_erase hk).symm
        exact symmetricDirichletActualCovariance_offdiag_eq hα hik hij
      _ = (n - 1) * symmetricDirichletActualCovariance n α i j := by
        simp [Nat.cast_sub hn1]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), herase] at hrow
  linarith

/-- The normalized Gamma/Dirichlet empirical criterion is centered at the
ordinary empirical mean for every fixed finite target. -/
theorem symmetricDirichlet_weighted_empirical_mean
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (h : Fin n → ℝ) :
    ∫ p : Fin n → ℝ, ∑ i, p i * h i ∂symmetricDirichletMeasure n α =
      empiricalMean h := by
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_mul_const, symmetricDirichlet_coordinate_mean hn hα]
    simp only [empiricalMean]
    rw [← Finset.mul_sum]
    ring
  · intro i _
    exact (integrable_coord_symmetricDirichletMeasure hα i).mul_const (h i)

/-- In particular, normalized Gamma reweighting leaves every fixed finite
log-likelihood criterion unchanged in expectation. -/
theorem symmetricDirichlet_weightedLogLikelihood_mean
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (v : Fin n → ℝ) :
    ∫ p : Fin n → ℝ, weightedLogLikelihood p v
        ∂symmetricDirichletMeasure n α =
      empiricalMean (fun i ↦ Real.log (v i)) := by
  simpa [weightedLogLikelihood] using
    symmetricDirichlet_weighted_empirical_mean hn hα
      (fun i ↦ Real.log (v i))

/-- Conditional on fixed data values `hᵢ`, the unnormalized Gamma-weighted
empirical criterion has exactly the ordinary empirical mean as its expectation. -/
theorem gamma_weighted_empirical_mean {n : ℕ} {α : ℝ} (hα : 0 < α)
    (h : Fin n → ℝ) :
    ∫ w : Fin n → ℝ, (∑ i, w i * h i) / n ∂gammaWeightMeasure n α =
      empiricalMean h := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let μn := gammaWeightMeasure n α
  have hcoord (i : Fin n) : Integrable (fun w : Fin n → ℝ ↦ w i) μn := by
    exact integrable_comp_eval (μ := fun _ : Fin n ↦ gammaMeasure α α)
      (integrable_id_gammaMeasure hα hα)
  have hterm (i : Fin n) :
      Integrable (fun w : Fin n → ℝ ↦ w i * h i) μn :=
    (hcoord i).mul_const (h i)
  have hsum :
      ∫ w : Fin n → ℝ, ∑ i, w i * h i ∂μn = ∑ i, h i := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hterm i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const]
    have heval := integral_comp_eval
      (μ := fun _ : Fin n ↦ gammaMeasure α α)
      (i := i) (integrable_id_gammaMeasure hα hα).aestronglyMeasurable
    change (∫ a : Fin n → ℝ, a i ∂Measure.pi
      (fun _ : Fin n ↦ gammaMeasure α α)) * h i = h i
    rw [heval, centered_gamma_mean hα, one_mul]
  change (∫ w : Fin n → ℝ, (∑ i, w i * h i) * (n : ℝ)⁻¹ ∂μn) =
    (∑ i, h i) / n
  rw [integral_mul_const, hsum]
  simp [div_eq_mul_inv]

/-- Therefore Gamma reweighting leaves every fixed finite likelihood target
unchanged in expectation. -/
theorem gamma_weighted_logLikelihood_mean {n : ℕ} {α : ℝ} (hα : 0 < α)
    (v : Fin n → ℝ) :
    ∫ w : Fin n → ℝ, weightedLogLikelihood w v / n
        ∂gammaWeightMeasure n α =
      empiricalMean (fun i ↦ Real.log (v i)) := by
  simpa [weightedLogLikelihood] using
    gamma_weighted_empirical_mean hα (fun i ↦ Real.log (v i))

end ReweightedNPMLE
