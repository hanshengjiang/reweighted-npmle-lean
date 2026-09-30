import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import ReweightedNPMLE.Gaussian
import ReweightedNPMLE.PolynomialMoments
import ReweightedNPMLE.Taylor
import Mathlib.Tactic

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

namespace ReweightedNPMLE

/-- Coordinatewise error `ε` gives Euclidean error at most `√n ε`. -/
theorem euclidean_norm_le_sqrt_card_mul {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    {eps : ℝ} (heps : 0 ≤ eps) (hx : ∀ i, |x i| ≤ eps) :
    ‖x‖ ≤ Real.sqrt n * eps := by
  have hsum : ∑ i, (x i) ^ 2 ≤ (n : ℝ) * eps ^ 2 := by
    calc
      ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin n, eps ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (eps - |x i|), sq_abs (x i), hx i, abs_nonneg (x i)]
      _ = (n : ℝ) * eps ^ 2 := by simp
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖x i‖ ^ 2) = Real.sqrt (∑ i, (x i) ^ 2) := by
      simp only [Real.norm_eq_abs, sq_abs]
    _ ≤ Real.sqrt ((n : ℝ) * eps ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * eps := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq heps]

/-- Orthogonal projection has no larger residual than any supplied subspace approximant. -/
theorem orthogonal_residual_le_approximant {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) :
    ‖x - V.starProjection x‖ ≤ ‖x - y‖ := by
  have hproj_y : V.orthogonal.starProjection y = 0 := by
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
        (V.le_orthogonal_orthogonal hy)]
    rfl
  calc
    ‖x - V.starProjection x‖ = ‖V.orthogonal.starProjection x‖ := by
      have hopen := DFunLike.congr_fun (Submodule.starProjection_orthogonal V) x
      change V.orthogonal.starProjection x = x - V.starProjection x at hopen
      exact congrArg norm hopen.symm
    _ = ‖V.orthogonal.starProjection (x - y)‖ := by
      rw [map_sub, hproj_y, sub_zero]
    _ ≤ ‖x - y‖ := V.orthogonal.norm_starProjection_apply_le _

/--
Uniform coordinatewise approximation by a subspace implies a relative-width
bound for the orthogonal projection onto that subspace.
-/
theorem relative_width_from_coordinate_approximants {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin n))) {eps : ℝ} (heps : 0 ≤ eps)
    (happrox : ∀ u ∈ U, ∃ y ∈ V, ∀ i, |u i - y i| ≤ eps) :
    ∀ u ∈ U, ‖u - V.starProjection u‖ ≤ Real.sqrt n * eps := by
  intro u hu
  obtain ⟨y, hy, hcoord⟩ := happrox u hu
  exact (orthogonal_residual_le_approximant V u y hy).trans
    (euclidean_norm_le_sqrt_card_mul (u - y) heps (by simpa using hcoord))

/-! ## The concrete Gaussian Taylor subspace -/

/-- Chosen monomial coefficients for the Taylor polynomial of
`exp ⟪xᵢ, θ⟫`. -/
noncomputable def truncatedInnerCoeff {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (i : Fin n) : MonomialCoord d L → ℝ :=
  Classical.choose (truncatedInnerExp_isPointMonomialCombination L (x i))

theorem truncatedInnerCoeff_spec {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (i : Fin n) (θ : Point d) :
    (∑ ell ∈ Finset.range (L + 1),
      (inner ℝ (x i) θ) ^ ell / ell.factorial) =
      ∑ m, truncatedInnerCoeff L x i m * pointMonomialEval θ m :=
  Classical.choose_spec (truncatedInnerExp_isPointMonomialCombination L (x i)) θ

/-- Generators of the paper's Gaussian approximation space.  `none` is the
constant vector and `some m` is the normalized coefficient vector of the
monomial `m`. -/
noncomputable def gaussianWidthGenerator {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    Option (MonomialCoord d L) → EuclideanSpace ℝ (Fin n)
  | none => WithLp.toLp 2 (fun _ ↦ 1)
  | some m => WithLp.toLp 2 (fun i ↦ truncatedInnerCoeff L x i m / v₀ i)

/-- The explicit Taylor subspace used in the Gaussian relative-width proof. -/
noncomputable def gaussianTaylorSubspace {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range (gaussianWidthGenerator L x v₀))

/-- The Taylor subspace contains the all-one vector. -/
theorem one_mem_gaussianTaylorSubspace {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈
      gaussianTaylorSubspace L x v₀ := by
  apply Submodule.subset_span
  exact ⟨none, rfl⟩

/-- Its rank is at most `1 + choose (L+d) d`, exactly as in Proposition 4.1. -/
theorem finrank_gaussianTaylorSubspace_le {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    Module.finrank ℝ (gaussianTaylorSubspace L x v₀) ≤
      1 + (L + d).choose d := by
  change Module.finrank ℝ
      (Submodule.span ℝ (Set.range (gaussianWidthGenerator L x v₀))) ≤ _
  calc
    _ ≤ Fintype.card (Option (MonomialCoord d L)) :=
      finrank_range_le_card (R := ℝ) (gaussianWidthGenerator L x v₀)
    _ = 1 + (L + d).choose d := by
      rw [Fintype.card_option, card_monomialCoord]
      omega

/-- Relative Gaussian atom after cancelling the common centered density. -/
noncomputable def relativeGaussianAtom {d n : ℕ}
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ Real.exp (gaussianScore (x i) θ) / v₀ i - 1)

/-- Taylor approximant to one relative Gaussian atom. -/
noncomputable def gaussianTaylorApproximant {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) :
    EuclideanSpace ℝ (Fin n) :=
  (∑ m : MonomialCoord d L,
      (Real.exp (-‖θ‖ ^ 2 / 2) * pointMonomialEval θ m) •
        gaussianWidthGenerator L x v₀ (some m)) -
    gaussianWidthGenerator L x v₀ none

theorem gaussianTaylorApproximant_mem {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) :
    gaussianTaylorApproximant L x v₀ θ ∈ gaussianTaylorSubspace L x v₀ := by
  apply Submodule.sub_mem
  · apply Submodule.sum_mem
    intro m _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨some m, rfl⟩
  · exact one_mem_gaussianTaylorSubspace L x v₀

/-- Coordinate formula for the explicit Taylor approximant. -/
theorem gaussianTaylorApproximant_apply {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) (i : Fin n) :
    gaussianTaylorApproximant L x v₀ θ i =
      Real.exp (-‖θ‖ ^ 2 / 2) *
          (∑ ell ∈ Finset.range (L + 1),
            (inner ℝ (x i) θ) ^ ell / ell.factorial) / v₀ i - 1 := by
  unfold gaussianTaylorApproximant
  simp only [WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul,
    PiLp.toLp_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, gaussianWidthGenerator]
  change (∑ m : MonomialCoord d L,
      (Real.exp (-‖θ‖ ^ 2 / 2) * pointMonomialEval θ m) *
        (truncatedInnerCoeff L x i m / v₀ i)) - 1 = _
  rw [truncatedInnerCoeff_spec L x i θ]
  apply congrArg (fun z ↦ z - 1)
  calc
    ∑ m, (Real.exp (-‖θ‖ ^ 2 / 2) * pointMonomialEval θ m) *
        (truncatedInnerCoeff L x i m / v₀ i) =
        (∑ m, Real.exp (-‖θ‖ ^ 2 / 2) *
          (truncatedInnerCoeff L x i m * pointMonomialEval θ m)) / v₀ i := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro m _
            ring
    _ = Real.exp (-‖θ‖ ^ 2 / 2) *
        (∑ m, truncatedInnerCoeff L x i m * pointMonomialEval θ m) / v₀ i := by
          rw [Finset.mul_sum]

/-- Exact coordinatewise Taylor error with the constant from Proposition 4.1. -/
theorem gaussianTaylorAtom_coordinate_error {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hθ : ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i) (i : Fin n) :
    |relativeGaussianAtom x v₀ θ i -
        gaussianTaylorApproximant L x v₀ θ i| ≤
      Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial := by
  let A : ℝ := T * S
  let trunc : ℝ := ∑ ell ∈ Finset.range (L + 1),
    (inner ℝ (x i) θ) ^ ell / ell.factorial
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hinner : |inner ℝ (x i) θ| ≤ A := by
    exact (abs_real_inner_le_norm (x i) θ).trans
      (mul_le_mul (hx i) hθ (norm_nonneg θ) hT)
  have hrem : |Real.exp (inner ℝ (x i) θ) - trunc| ≤
      Real.exp A * A ^ (L + 1) / (L + 1).factorial := by
    exact real_exp_taylor_remainder_bound L hA hinner
  have hvpos : 0 < v₀ i :=
    (Real.exp_pos (-(T * S + S ^ 2 / 2))).trans_le (hv₀ i)
  have hinv : (v₀ i)⁻¹ ≤ Real.exp (T * S + S ^ 2 / 2) := by
    calc
      (v₀ i)⁻¹ = 1 / v₀ i := by simp [one_div]
      _ ≤ 1 / Real.exp (-(T * S + S ^ 2 / 2)) :=
        one_div_le_one_div_of_le (Real.exp_pos _) (hv₀ i)
      _ = Real.exp (T * S + S ^ 2 / 2) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
  have heNeg : Real.exp (-‖θ‖ ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖θ‖]
  have hscore : Real.exp (gaussianScore (x i) θ) =
      Real.exp (-‖θ‖ ^ 2 / 2) * Real.exp (inner ℝ (x i) θ) := by
    rw [gaussianScore, ← Real.exp_add]
    congr 1
    ring
  have hdiff : relativeGaussianAtom x v₀ θ i -
      gaussianTaylorApproximant L x v₀ θ i =
        Real.exp (-‖θ‖ ^ 2 / 2) *
          (Real.exp (inner ℝ (x i) θ) - trunc) / v₀ i := by
    rw [relativeGaussianAtom, PiLp.toLp_apply,
      gaussianTaylorApproximant_apply, hscore]
    dsimp [trunc]
    ring
  rw [hdiff]
  calc
    |Real.exp (-‖θ‖ ^ 2 / 2) *
        (Real.exp (inner ℝ (x i) θ) - trunc) / v₀ i| =
        Real.exp (-‖θ‖ ^ 2 / 2) *
          |Real.exp (inner ℝ (x i) θ) - trunc| * (v₀ i)⁻¹ := by
            rw [abs_div, abs_mul, Real.abs_exp, abs_of_pos hvpos]
            simp [div_eq_mul_inv]
    _ ≤ 1 * (Real.exp A * A ^ (L + 1) / (L + 1).factorial) *
        Real.exp (T * S + S ^ 2 / 2) := by
          gcongr
    _ = Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial := by
          dsimp [A]
          rw [one_mul, show 2 * T * S + S ^ 2 / 2 =
            T * S + (T * S + S ^ 2 / 2) by ring]
          simp only [Real.exp_add]
          ring

/-- Residual-width bound for every individual Gaussian atom. -/
theorem gaussian_atom_projection_error {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hθ : ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i) :
    ‖relativeGaussianAtom x v₀ θ -
        (gaussianTaylorSubspace L x v₀).starProjection
          (relativeGaussianAtom x v₀ θ)‖ ≤
      Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial) := by
  let eps := Real.exp (2 * T * S + S ^ 2 / 2) *
    (T * S) ^ (L + 1) / (L + 1).factorial
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  exact (orthogonal_residual_le_approximant
    (gaussianTaylorSubspace L x v₀) (relativeGaussianAtom x v₀ θ)
      (gaussianTaylorApproximant L x v₀ θ)
      (gaussianTaylorApproximant_mem L x v₀ θ)).trans
    (euclidean_norm_le_sqrt_card_mul
      (relativeGaussianAtom x v₀ θ - gaussianTaylorApproximant L x v₀ θ)
      heps (fun i ↦ by
        simpa [eps] using
          gaussianTaylorAtom_coordinate_error L x v₀ θ hT hS hx hθ hv₀ i))

/-- The atomwise estimate extends to the entire convex hull, hence to every
Gaussian fitted vector.  This is the analytic content of Proposition 4.1. -/
theorem gaussian_convexHull_projection_error {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i)
    {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ convexHull ℝ (relativeGaussianAtom x v₀ '' K)) :
    ‖u - (gaussianTaylorSubspace L x v₀).starProjection u‖ ≤
      Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial) := by
  let V := gaussianTaylorSubspace L x v₀
  let Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.id ℝ _ - V.starProjection
  let eps := Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
    (T * S) ^ (L + 1) / (L + 1).factorial)
  have hconv : Convex ℝ (Q ⁻¹' Metric.closedBall 0 eps) :=
    (convex_closedBall 0 eps).linear_preimage Q.toLinearMap
  have hsubset : relativeGaussianAtom x v₀ '' K ⊆
      Q ⁻¹' Metric.closedBall 0 eps := by
    intro y hy
    rcases hy with ⟨θ, hθK, rfl⟩
    rw [Set.mem_preimage, Metric.mem_closedBall]
    simpa [Q, V, eps, dist_eq_norm] using
      gaussian_atom_projection_error L x v₀ θ hT hS hx (hK θ hθK) hv₀
  have humem : u ∈ Q ⁻¹' Metric.closedBall 0 eps :=
    convexHull_min hsubset hconv hu
  rw [Set.mem_preimage, Metric.mem_closedBall] at humem
  simpa [Q, V, eps, dist_eq_norm] using humem

/-- Bundled Gaussian relative-width proposition: the constructed projection
contains the constants, has the stated binomial rank, and controls the full
convex fitted-value class with the exact Taylor remainder. -/
theorem gaussian_relative_width_bound {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i) :
    Module.finrank ℝ (gaussianTaylorSubspace L x v₀) ≤
        1 + (L + d).choose d ∧
      WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈
        gaussianTaylorSubspace L x v₀ ∧
      ∀ u ∈ convexHull ℝ (relativeGaussianAtom x v₀ '' K),
        ‖u - (gaussianTaylorSubspace L x v₀).starProjection u‖ ≤
          Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
            (T * S) ^ (L + 1) / (L + 1).factorial) := by
  exact ⟨finrank_gaussianTaylorSubspace_le L x v₀,
    one_mem_gaussianTaylorSubspace L x v₀,
    fun _ hu ↦ gaussian_convexHull_projection_error L x v₀ K hT hS hx hK hv₀ hu⟩

end ReweightedNPMLE
