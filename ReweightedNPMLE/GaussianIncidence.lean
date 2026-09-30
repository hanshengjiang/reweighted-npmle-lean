import ReweightedNPMLE.GaussianIdentifiability
import ReweightedNPMLE.FiniteProbabilityExtreme
import ReweightedNPMLE.AnalyticIncidence
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-!
# Nontrivial Gaussian families for the generic incidence argument

Distinct Gaussian translates are linearly independent as functions on the
whole observation space. This is proved using Gaussian mixture identifiability
and a positive finite-probability perturbation, so no choice of a separating
direction or Vandermonde derivative calculation is required.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

theorem gaussianMixture_finiteProbabilityMeasure {d k : ℕ}
    (θ : Fin k → Point d) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k) :
    gaussianMixture (finiteProbabilityMeasure θ p hp : Measure (Point d)) id =
      finiteGaussianMixture p θ := by
  funext x
  change (∫ a, gaussianKernel d x a ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp.1 _),
      finiteGaussianMixture, smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem finiteGaussianMixture_coefficients_zero_of_eq_zero {d k : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) (c : Fin k → ℝ)
    (hzero : ∀ x, finiteGaussianMixture c θ x = 0) : ∀ j, c j = 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    intro j
    exact Fin.elim0 j
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hsum : ∑ j, c j = 0 := by
    rw [← integral_finiteGaussianMixture c θ]
    simp only [hzero, integral_zero]
  let b : ℝ := 1 / (k : ℝ)
  let M : ℝ := ∑ j, |c j|
  let t : ℝ := b / (2 * (1 + M))
  let p : Fin k → ℝ := fun _ ↦ b
  let q : Fin k → ℝ := fun j ↦ b + t * c j
  have hb : 0 < b := by dsimp [b]; positivity
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (c j))
  have ht : 0 < t := by dsimp [t]; positivity
  have htEq : t * (1 + M) = b / 2 := by
    dsimp [t]
    field_simp
  have hbound : ∀ j, |c j| ≤ M := fun j ↦
    Finset.single_le_sum (fun l _ ↦ abs_nonneg (c l)) (Finset.mem_univ j)
  have hp : p ∈ finiteSimplex k := by
    refine ⟨fun _ ↦ hb.le, ?_⟩
    simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, b]
    field_simp
  have hq : q ∈ finiteSimplex k := by
    constructor
    · intro j
      have hc : -M ≤ c j := by linarith [(abs_le.mp (hbound j)).1]
      have hh := mul_le_mul_of_nonneg_left hc ht.le
      dsimp [q]
      nlinarith
    · simp only [q, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]
      exact hp.2
  have hdensity : finiteGaussianMixture q θ = finiteGaussianMixture p θ := by
    funext x
    have heq : finiteGaussianMixture q θ x =
        finiteGaussianMixture p θ x + t * finiteGaussianMixture c θ x := by
      simp only [finiteGaussianMixture, q, p, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, hzero, mul_zero, add_zero]
  have hmeas : (finiteProbabilityMeasure θ q hq : Measure (Point d)) =
      (finiteProbabilityMeasure θ p hp : Measure (Point d)) := by
    apply gaussianMixture_identifiable_of_ae_eq
    rw [gaussianMixture_finiteProbabilityMeasure, gaussianMixture_finiteProbabilityMeasure, hdensity]
  have hlaw : finiteProbabilityMeasure θ q hq = finiteProbabilityMeasure θ p hp :=
    ProbabilityMeasure.toMeasure_injective hmeas
  have hcoeff := finiteProbabilityMeasure_coefficients_injective θ hθ q p hq hp hlaw
  intro j
  have hj := congrFun hcoeff j
  change b + t * c j = b at hj
  exact (mul_eq_zero.mp (by linarith : t * c j = 0)).resolve_left ht.ne'

/-- Nonzero normalized coefficients cannot define an identically zero family,
uniformly over every distinct location list. -/
theorem finiteGaussianMixture_not_identically_zero {d k : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) (c : Fin k → ℝ)
    (hc : ∃ j, c j ≠ 0) : ∃ x, finiteGaussianMixture c θ x ≠ 0 := by
  by_contra hn
  have hzero : ∀ x, finiteGaussianMixture c θ x = 0 := by simpa using hn
  obtain ⟨j, hj⟩ := hc
  exact hj (finiteGaussianMixture_coefficients_zero_of_eq_zero θ hθ c hzero j)

theorem linearIndependent_gaussianKernel_functions {d k : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) :
    LinearIndependent ℝ (fun j ↦ fun x ↦ gaussianKernel d x (θ j)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  apply finiteGaussianMixture_coefficients_zero_of_eq_zero θ hθ c _ j
  intro x
  have hx := congrFun hc x
  simpa only [finiteGaussianMixture, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] using hx

theorem analyticAt_gaussianKernel_joint {d : ℕ} (z : Point d × Point d) :
    AnalyticAt ℝ (fun p : Point d × Point d ↦ gaussianKernel d p.1 p.2) z := by
  have hnorm : AnalyticAt ℝ
      (fun p : Point d × Point d ↦ inner ℝ (p.1 - p.2) (p.1 - p.2)) z := by
    have hpair : AnalyticAt ℝ
        (fun p : Point d × Point d ↦ (p.1 - p.2, p.1 - p.2)) z :=
      (analyticAt_fst.sub analyticAt_snd).prod (analyticAt_fst.sub analyticAt_snd)
    exact ((innerSL ℝ (E := Point d)).analyticAt_bilinear
      (z.1 - z.2, z.1 - z.2)).comp
        (f := fun p : Point d × Point d ↦ (p.1 - p.2, p.1 - p.2)) (x := z) hpair
  have hsq : AnalyticAt ℝ (fun p : Point d × Point d ↦ ‖p.1 - p.2‖ ^ 2) z := by
    simpa only [real_inner_self_eq_norm_sq] using hnorm
  unfold gaussianKernel
  exact analyticAt_const.mul ((hsq.neg.div_const (c := 2)).rexp')

theorem analyticAt_finiteGaussianMixture_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ}
    (θ : Fin k → E → Point d) (c : Fin k → E → ℝ) (y : E → Point d) (e : E)
    (hθ : ∀ j, AnalyticAt ℝ (θ j) e) (hc : ∀ j, AnalyticAt ℝ (c j) e)
    (hy : AnalyticAt ℝ y e) :
    AnalyticAt ℝ (fun a ↦ finiteGaussianMixture (fun j ↦ c j a) (fun j ↦ θ j a) (y a)) e := by
  unfold finiteGaussianMixture
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (hc j).mul ((analyticAt_gaussianKernel_joint (y e, θ j e)).comp
    (f := fun a ↦ (y a, θ j a)) (hy.prod (hθ j)))

theorem analyticOnNhd_finiteGaussianMixture {d k : ℕ}
    (θ : Fin k → Point d) (c : Fin k → ℝ) :
    AnalyticOnNhd ℝ (finiteGaussianMixture c θ) univ := by
  intro x _
  exact analyticAt_finiteGaussianMixture_parameter (fun j _ ↦ θ j) (fun j _ ↦ c j) id x
    (fun _ ↦ analyticAt_const) (fun _ ↦ analyticAt_const) analyticAt_id

theorem finiteGaussianMixture_exists_nonzero_derivative {d k : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) (c : Fin k → ℝ)
    (hc : ∃ j, c j ≠ 0) (x : Point d) :
    ∃ m : ℕ, iteratedFDeriv ℝ m (finiteGaussianMixture c θ) x ≠ 0 :=
  exists_iteratedFDeriv_ne_zero_of_analytic_nontrivial _
    (analyticOnNhd_finiteGaussianMixture θ c)
    (finiteGaussianMixture_not_identically_zero θ hθ c hc) x

/-- A coefficient chart has all location coordinates but omits the normalized
coefficient at `j₀`. -/
abbrev GaussianDependenceParameter (d k : ℕ) (j₀ : Fin k) :=
  (Fin k → Point d) × ({j : Fin k // j ≠ j₀} → ℝ)

noncomputable def normalizedGaussianCoefficients {k : ℕ} (j₀ : Fin k)
    (b : {j : Fin k // j ≠ j₀} → ℝ) : Fin k → ℝ :=
  fun j ↦ if hj : j = j₀ then 1 else b ⟨j, hj⟩

def gaussianDependenceDomain {d k : ℕ} (j₀ : Fin k) :
    Set (GaussianDependenceParameter d k j₀) := {η | Function.Injective η.1}

noncomputable def gaussianDependenceFamily {d k : ℕ} (j₀ : Fin k)
    (η : GaussianDependenceParameter d k j₀) (y : Point d) : ℝ :=
  finiteGaussianMixture (normalizedGaussianCoefficients j₀ η.2) η.1 y

theorem finrank_gaussianDependenceParameter {d k : ℕ} (j₀ : Fin k) :
    Module.finrank ℝ (GaussianDependenceParameter d k j₀) = k * d + (k - 1) := by
  have hcard : Fintype.card {j : Fin k // j ≠ j₀} = k - 1 := by
    simpa using Fintype.card_subtype_compl (fun j : Fin k ↦ j = j₀)
  simp [GaussianDependenceParameter, Module.finrank_prod, Module.finrank_pi_fintype,
    hcard]

theorem finrank_gaussianDependenceParameter_lt {d k n : ℕ} (j₀ : Fin k)
    (hkn : k * (d + 1) ≤ n) :
    Module.finrank ℝ (GaussianDependenceParameter d k j₀) < n := by
  rw [finrank_gaussianDependenceParameter]
  have hk : 0 < k := Fin.pos j₀
  rw [Nat.mul_add, Nat.mul_one] at hkn
  omega

theorem isOpen_gaussianDependenceDomain {d k : ℕ} (j₀ : Fin k) :
    IsOpen (gaussianDependenceDomain (d := d) j₀) := by
  have heq : gaussianDependenceDomain (d := d) j₀ =
      ⋂ j : Fin k, ⋂ l : Fin k,
        {η : GaussianDependenceParameter d k j₀ | j = l ∨ η.1 j ≠ η.1 l} := by
    ext η
    simp only [gaussianDependenceDomain, mem_setOf_eq, mem_iInter]
    constructor
    · intro h j l
      by_cases hjl : j = l
      · exact Or.inl hjl
      · exact Or.inr (fun hh ↦ hjl (h hh))
    · intro h j l hjl
      exact (h j l).resolve_right (not_not.mpr hjl)
  rw [heq]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro l
  by_cases hjl : j = l
  · simp only [hjl, true_or, setOf_true]
    exact isOpen_univ
  · simp only [hjl, false_or]
    exact isOpen_ne_fun (by fun_prop) (by fun_prop)

theorem analyticAt_gaussianDependenceFamily_joint {d k : ℕ} (j₀ : Fin k)
    (z : GaussianDependenceParameter d k j₀ × Point d) :
    AnalyticAt ℝ (fun p ↦ gaussianDependenceFamily j₀ p.1 p.2) z := by
  have hloc : AnalyticAt ℝ
      (fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.1) z :=
    (analyticAt_fst : AnalyticAt ℝ
      (fun η : GaussianDependenceParameter d k j₀ ↦ η.1) z.1).comp
        (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1) analyticAt_fst
  have hcoef : AnalyticAt ℝ
      (fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.2) z :=
    (analyticAt_snd : AnalyticAt ℝ
      (fun η : GaussianDependenceParameter d k j₀ ↦ η.2) z.1).comp
        (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1) analyticAt_fst
  unfold gaussianDependenceFamily
  apply analyticAt_finiteGaussianMixture_parameter
  · intro j
    exact ((ContinuousLinearMap.proj j : (Fin k → Point d) →L[ℝ] Point d).analyticAt z.1.1).comp
      (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.1) hloc
  · intro j
    by_cases hj : j = j₀
    · simp only [normalizedGaussianCoefficients, dif_pos hj]
      exact analyticAt_const
    · simp only [normalizedGaussianCoefficients, dif_neg hj]
      exact ((ContinuousLinearMap.proj ⟨j, hj⟩ :
        ({j : Fin k // j ≠ j₀} → ℝ) →L[ℝ] ℝ).analyticAt z.1.2).comp
        (f := fun p : GaussianDependenceParameter d k j₀ × Point d ↦ p.1.2) hcoef
  · exact analyticAt_snd

theorem gaussianDependenceFamily_nontrivial {d k : ℕ} (j₀ : Fin k)
    (η : GaussianDependenceParameter d k j₀) (hη : η ∈ gaussianDependenceDomain j₀) :
    ∃ y, gaussianDependenceFamily j₀ η y ≠ 0 := by
  apply finiteGaussianMixture_not_identically_zero η.1 hη
  refine ⟨j₀, ?_⟩
  simp [normalizedGaussianCoefficients]

theorem gaussianDependenceFamily_regular_derivative_at_zero {d k : ℕ} (j₀ : Fin k)
    (η : GaussianDependenceParameter d k j₀) (hη : η ∈ gaussianDependenceDomain j₀)
    (x : Point d) (hx : gaussianDependenceFamily j₀ η x = 0) :
    ∃ (m : ℕ) (ℓ : Fin d) (σ : Fin m → Fin d),
      iteratedFDeriv ℝ m (gaussianDependenceFamily j₀ η) x
        (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (σ i)) = 0 ∧
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ m (gaussianDependenceFamily j₀ η) y
        (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (σ i))) x
          ((EuclideanSpace.basisFun (Fin d) ℝ) ℓ) ≠ 0 := by
  exact exists_regular_iterated_derivative_of_analytic_zero
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis _
    (analyticOnNhd_finiteGaussianMixture η.1 (normalizedGaussianCoefficients j₀ η.2))
    (gaussianDependenceFamily_nontrivial j₀ η hη) x hx

theorem gaussian_evaluation_dependence_has_normalized_chart {d k n : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) (x : Fin n → Point d)
    (hdep : ¬LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (θ j))) :
    ∃ (j₀ : Fin k) (η : GaussianDependenceParameter d k j₀),
      η ∈ gaussianDependenceDomain j₀ ∧ ∀ i, gaussianDependenceFamily j₀ η (x i) = 0 := by
  classical
  obtain ⟨c, hc, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let η : GaussianDependenceParameter d k j₀ := (θ, fun j ↦ c j.val / c j₀)
  have hcoeff : normalizedGaussianCoefficients j₀ η.2 = (fun j ↦ c j / c j₀) := by
    funext j
    by_cases hj : j = j₀
    · subst j
      simp [normalizedGaussianCoefficients, hj₀]
    · simp [normalizedGaussianCoefficients, hj, η]
  refine ⟨j₀, η, hθ, ?_⟩
  intro i
  have hi := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  change finiteGaussianMixture (normalizedGaussianCoefficients j₀ η.2) θ (x i) = 0
  rw [hcoeff]
  unfold finiteGaussianMixture
  have heq : (∑ j, (c j / c j₀) * gaussianKernel d (x i) (θ j)) =
      (∑ j, c j * gaussianKernel d (x i) (θ j)) / c j₀ := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, hi, zero_div]

end ReweightedNPMLE
