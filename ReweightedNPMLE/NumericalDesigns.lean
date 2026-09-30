import ReweightedNPMLE.FiniteProbabilityExtreme
import ReweightedNPMLE.GaussianMixtureMeasure
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The three numerical-study mixing models

These are genuine probability laws with the literal masses and locations in
Section 6, including the non-atomic uniform mixing design. Their support
constraints are proved independently of the recorded optimization outputs.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false

def numericalParameterBox (d : Nat) (B : ℝ) : Set (Point d) :=
  {x | ∀ i, x i ∈ Icc (-B) B}

theorem numerical_parameter_box_compact (d : Nat) (B : ℝ) :
    IsCompact (numericalParameterBox d B) := by
  exact (PiLp.homeomorph 2 (fun _ : Fin d ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_pi_infinite (fun _ ↦ isCompact_Icc))

theorem numerical_parameter_box_nonempty (d : Nat) {B : ℝ} (hB : 0 ≤ B) :
    (numericalParameterBox d B).Nonempty := by
  refine ⟨0, ?_⟩
  intro i
  change -B ≤ 0 ∧ 0 ≤ B
  exact ⟨neg_nonpos.mpr hB, hB⟩

def numericalEmbed1 (x : ℝ) : Point 1 := WithLp.toLp 2 (fun _ ↦ x)

theorem numerical_embed1_continuous : Continuous numericalEmbed1 := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
    (continuous_pi (fun _ ↦ continuous_id))

def numericalThreePointAtoms : Fin 3 → Point 1 :=
  ![numericalEmbed1 (-5 / 2), numericalEmbed1 0, numericalEmbed1 (5 / 2)]

def numericalThreePointMasses : Fin 3 → ℝ := ![1 / 4, 1 / 2, 1 / 4]

theorem numerical_three_point_masses_simplex :
    numericalThreePointMasses ∈ finiteSimplex 3 := by
  constructor
  · intro j
    fin_cases j <;> norm_num [numericalThreePointMasses]
  · norm_num [numericalThreePointMasses, Fin.sum_univ_succ]

noncomputable def numericalThreePointLaw : ProbabilityMeasure (Point 1) :=
  finiteProbabilityMeasure numericalThreePointAtoms numericalThreePointMasses
    numerical_three_point_masses_simplex

theorem numerical_three_point_atoms_in_box (j : Fin 3) :
    numericalThreePointAtoms j ∈ numericalParameterBox 1 4 := by
  intro i
  fin_cases j <;> fin_cases i <;>
    norm_num [numericalThreePointAtoms, numericalEmbed1]

theorem numerical_three_point_atoms_injective :
    Function.Injective numericalThreePointAtoms := by
  intro j k h
  fin_cases j <;> fin_cases k <;> first
  | rfl
  | have hh := congrArg (fun x : Point 1 ↦ x 0) h
    norm_num [numericalThreePointAtoms, numericalEmbed1] at hh

theorem numerical_three_point_singleton_masses (j : Fin 3) :
    (numericalThreePointLaw : Measure (Point 1)) {numericalThreePointAtoms j} =
      ENNReal.ofReal (numericalThreePointMasses j) := by
  exact finiteProbabilityMeasure_singleton_mass numericalThreePointAtoms
    numerical_three_point_atoms_injective numericalThreePointMasses
    numerical_three_point_masses_simplex j

theorem numerical_three_point_law_correctly_specified :
    ∀ᵐ x ∂(numericalThreePointLaw : Measure (Point 1)),
      x ∈ numericalParameterBox 1 4 := by
  filter_upwards [finiteProbabilityMeasure_ae_mem_range numericalThreePointAtoms
    numericalThreePointMasses numerical_three_point_masses_simplex] with x hx
  rcases hx with ⟨j, rfl⟩
  exact numerical_three_point_atoms_in_box j

def numericalSquareAtoms : Fin 4 → Point 2 :=
  ![WithLp.toLp 2 ![-7 / 4, -7 / 4], WithLp.toLp 2 ![-7 / 4, 7 / 4],
    WithLp.toLp 2 ![7 / 4, -7 / 4], WithLp.toLp 2 ![7 / 4, 7 / 4]]

def numericalSquareMasses : Fin 4 → ℝ := fun _ ↦ 1 / 4

theorem numerical_square_masses_simplex : numericalSquareMasses ∈ finiteSimplex 4 := by
  constructor
  · intro j
    norm_num [numericalSquareMasses]
  · norm_num [numericalSquareMasses, Fin.sum_univ_succ]

noncomputable def numericalSquareLaw : ProbabilityMeasure (Point 2) :=
  finiteProbabilityMeasure numericalSquareAtoms numericalSquareMasses
    numerical_square_masses_simplex

theorem numerical_square_atoms_in_box (j : Fin 4) :
    numericalSquareAtoms j ∈ numericalParameterBox 2 (7 / 2) := by
  intro i
  fin_cases j <;> fin_cases i <;> norm_num [numericalSquareAtoms]

theorem numerical_square_atoms_injective : Function.Injective numericalSquareAtoms := by
  intro j k h
  fin_cases j <;> fin_cases k <;> first
  | rfl
  | have h0 := congrArg (fun x : Point 2 ↦ x 0) h
    have h1 := congrArg (fun x : Point 2 ↦ x 1) h
    norm_num [numericalSquareAtoms] at h0 <;>
      norm_num [numericalSquareAtoms] at h1

theorem numerical_square_singleton_masses (j : Fin 4) :
    (numericalSquareLaw : Measure (Point 2)) {numericalSquareAtoms j} = 1 / 4 := by
  have h := finiteProbabilityMeasure_singleton_mass numericalSquareAtoms
    numerical_square_atoms_injective numericalSquareMasses numerical_square_masses_simplex j
  simpa [numericalSquareMasses] using h

theorem numerical_square_law_correctly_specified :
    ∀ᵐ x ∂(numericalSquareLaw : Measure (Point 2)),
      x ∈ numericalParameterBox 2 (7 / 2) := by
  filter_upwards [finiteProbabilityMeasure_ae_mem_range numericalSquareAtoms
    numericalSquareMasses numerical_square_masses_simplex] with x hx
  rcases hx with ⟨j, rfl⟩
  exact numerical_square_atoms_in_box j

noncomputable def numericalUniformRealLaw : ProbabilityMeasure ℝ := by
  refine ⟨ProbabilityTheory.cond volume (Icc (-5 / 2 : ℝ) (5 / 2)), ?_⟩
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite <;>
    norm_num [Real.volume_Icc]

/-- Lebesgue-uniform, not counting-uniform: the interval has length five. -/
theorem numerical_uniform_real_law_literal :
    (numericalUniformRealLaw : Measure ℝ) =
      (5 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-5 / 2 : ℝ) (5 / 2)) := by
  unfold numericalUniformRealLaw ProbabilityTheory.cond
  norm_num [Real.volume_Icc]

theorem numerical_uniform_real_singleton_zero (x : ℝ) :
    (numericalUniformRealLaw : Measure ℝ) {x} = 0 := by
  rw [numerical_uniform_real_law_literal, Measure.smul_apply]
  have hs : volume.restrict (Icc (-5 / 2 : ℝ) (5 / 2)) {x} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null inter_subset_left (by simp)
  simp [hs]

noncomputable def numericalUniformLaw : ProbabilityMeasure (Point 1) :=
  numericalUniformRealLaw.map numerical_embed1_continuous.measurable.aemeasurable

theorem numerical_uniform_singleton_zero (x : Point 1) :
    (numericalUniformLaw : Measure (Point 1)) {x} = 0 := by
  change ((numericalUniformRealLaw : Measure ℝ).map numericalEmbed1) {x} = 0
  rw [Measure.map_apply numerical_embed1_continuous.measurable (measurableSet_singleton x)]
  apply measure_mono_null (t := {x 0})
  · intro a ha
    have he : numericalEmbed1 a = x := ha
    have hh := congrArg (fun z : Point 1 ↦ z 0) he
    simpa [numericalEmbed1] using hh
  · exact numerical_uniform_real_singleton_zero (x 0)

theorem numerical_uniform_law_correctly_specified :
    ∀ᵐ x ∂(numericalUniformLaw : Measure (Point 1)),
      x ∈ numericalParameterBox 1 4 := by
  rw [show (numericalUniformLaw : Measure (Point 1)) =
    (numericalUniformRealLaw : Measure ℝ).map numericalEmbed1 from rfl]
  apply (ae_map_iff numerical_embed1_continuous.measurable.aemeasurable
    (numerical_parameter_box_compact 1 4).isClosed.measurableSet).mpr
  filter_upwards [ProbabilityTheory.ae_cond_mem
    (μ := (volume : Measure ℝ)) (s := Icc (-5 / 2 : ℝ) (5 / 2)) measurableSet_Icc]
    with x hx
  intro i
  change -4 ≤ x ∧ x ≤ 4
  constructor <;> linarith [hx.1, hx.2]

theorem numerical_design_densities_integrate_one :
    (∫ x, gaussianMixture (numericalThreePointLaw : Measure (Point 1)) id x) = 1 ∧
    (∫ x, gaussianMixture (numericalUniformLaw : Measure (Point 1)) id x) = 1 ∧
    (∫ x, gaussianMixture (numericalSquareLaw : Measure (Point 2)) id x) = 1 := by
  exact ⟨integral_gaussianMixture _ id measurable_id,
    integral_gaussianMixture _ id measurable_id,
    integral_gaussianMixture _ id measurable_id⟩

theorem numerical_tiny_shape_is_L_half (n : Nat) :
    (n : ℝ) ^ (2 * (1 / 2 : ℝ) + 2) = (n : ℝ) ^ (3 : Nat) := by
  norm_num [Real.rpow_ofNat]

/-- The numerical code normalizes to average one, not total one. -/
def numericalNormalizedWeights {n : Nat} (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ w i / (total w / (n : ℝ))

theorem numerical_normalized_weights_eq_nP {n : Nat} (w : Fin n → ℝ) (i : Fin n) :
    numericalNormalizedWeights w i = (n : ℝ) * normalize w i := by
  simp only [numericalNormalizedWeights, normalize, div_div_eq_mul_div]
  ring

theorem numerical_normalized_weights_sum_eq_n {n : Nat} (w : Fin n → ℝ)
    (hw : total w ≠ 0) : total (numericalNormalizedWeights w) = (n : ℝ) := by
  unfold total
  simp only [numerical_normalized_weights_eq_nP, ← Finset.mul_sum,
    sum_normalize hw, mul_one]

theorem numerical_normalization_optimizer_unchanged {n : Nat} (hn : 0 < n)
    {C : Set (Fin n → ℝ)} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    (v : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood (numericalNormalizedWeights w)) v ↔
      IsMaxOn C (weightedLogLikelihood w) v := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have he : numericalNormalizedWeights w = (n : ℝ) • normalize w := by
    funext i
    exact numerical_normalized_weights_eq_nP w i
  rw [he, isMaxOn_weight_smul_iff (show (0 : ℝ) < n by exact_mod_cast hn)]
  exact isMaxOn_normalize_iff hw v

end ReweightedNPMLE.NumericalStudy
