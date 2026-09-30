import ReweightedNPMLE.FittedHessian
import ReweightedNPMLE.SupportSensitivity
import ReweightedNPMLE.MatrixSensitivity
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE

/-- Along a multiplicative fitted-value path `vᵢ(1+t uᵢ)` and an affine
weight path `w+t h`, the weighted log likelihood has the paper's exact
second-order expansion. -/
theorem weightedLogLikelihood_multiplicative_secondOrder {n : ℕ}
    (w h v u : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    (fun t : ℝ ↦
      weightedLogLikelihood (w + t • h) (fun i ↦ v i * (1 + t * u i)) -
        weightedLogLikelihood w v -
        t * ((∑ i, h i * Real.log (v i)) + ∑ i, w i * u i) -
        t ^ 2 * ((∑ i, h i * u i) - (1 / 2 : ℝ) * ∑ i, w i * u i ^ 2))
      =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
  have hlog (i : Fin n) :
      (fun t : ℝ ↦ Real.log (1 + t * u i) - t * u i +
          (t ^ 2 / 2) * u i ^ 2) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) :=
    log_one_add_secondOrder_isLittleO (u i)
  have hsum :
      (fun t : ℝ ↦ ∑ i, w i *
        (Real.log (1 + t * u i) - t * u i +
          (t ^ 2 / 2) * u i ^ 2)) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) := by
    apply IsLittleO.sum
    intro i _
    exact (hlog i).const_mul_left (w i)
  have hsmall (i : Fin n) :
      (fun t : ℝ ↦ t * h i *
        (Real.log (1 + t * u i) - t * u i)) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) := by
    have hd : HasDerivAt (fun t : ℝ ↦ Real.log (1 + t * u i)) (u i) 0 := by
      convert (((hasDerivAt_id 0).mul_const (u i)).const_add 1).log (by norm_num) using 1 <;>
        simp [id_eq]
    have hlo :
        (fun t : ℝ ↦ Real.log (1 + t * u i) - t * u i) =o[nhdsWithin 0 (Ioi 0)]
          (fun t : ℝ ↦ t) := by
      convert hd.isLittleO.mono nhdsWithin_le_nhds using 1 <;> simp [smul_eq_mul]
    have htO : (fun t : ℝ ↦ t * h i) =O[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t) := by
      simpa [mul_comm] using
        (isBigO_refl (fun t : ℝ ↦ t) (nhdsWithin 0 (Ioi 0))).const_mul_left (h i)
    convert htO.mul_isLittleO hlo using 1 <;> ext t <;> ring
  have hsmallSum :
      (fun t : ℝ ↦ ∑ i, t * h i *
        (Real.log (1 + t * u i) - t * u i)) =o[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ ↦ t ^ 2) := by
    apply IsLittleO.sum
    intro i _
    exact hsmall i
  have hall := hsum.add hsmallSum
  refine hall.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hden : ∀ᶠ t in nhds (0 : ℝ), ∀ i, 1 + t * u i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun t : ℝ ↦ 1 + t * u i) 0 := by fun_prop
    simpa using hc.eventually_ne (y := (0 : ℝ)) (by norm_num)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hden] with t ht
  unfold weightedLogLikelihood
  simp_rw [Real.log_mul (hv _).ne' (ht _)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A finite convex combination of dictionary atoms lies in their convex
hull. -/
theorem finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex
    {k : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin k → E) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k) :
    finiteMixtureValue A p ∈ convexHull ℝ (Set.range A) := by
  apply (convex_convexHull ℝ (Set.range A)).sum_mem (fun i _ ↦ hp.1 i) hp.2
  intro i _
  exact subset_convexHull ℝ (Set.range A) ⟨i, rfl⟩

/-- A zero-total perturbation of a strictly positive probability vector stays
in the simplex for all sufficiently small scalar parameters. -/
theorem eventually_mem_finiteSimplex_add_smul_zeroSum
    {k : ℕ} (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k)
    (hpfull : ∀ j, 0 < p j) (c : zeroSumCoefficients k) :
    ∀ᶠ t : ℝ in nhds 0, p + t • c.1 ∈ finiteSimplex k := by
  have hpos : ∀ᶠ t : ℝ in nhds 0, ∀ j, 0 < p j + t * c.1 j := by
    rw [Filter.eventually_all]
    intro j
    have hc : ContinuousAt (fun t : ℝ ↦ p j + t * c.1 j) 0 := by fun_prop
    have hzero : 0 < p j + (0 : ℝ) * c.1 j := by simpa using hpfull j
    have ht := hc.tendsto (Ioi_mem_nhds hzero)
    simpa using ht
  filter_upwards [hpos] with t ht
  constructor
  · intro j
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (ht j).le
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib]
    rw [hp.2]
    have hc : ∑ j, c.1 j = 0 := c.property
    rw [← Finset.mul_sum, hc]
    simp

/-- The fitted-value change produced by an affine coefficient perturbation is
the multiplicative relative-dictionary path. -/
theorem finiteMixtureValue_add_smul_eq_mul_one_add_relative
    {k n : ℕ} (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (p : Fin k → ℝ) (hpv : finiteMixtureValue A p = v)
    (hv : ∀ i, v i ≠ 0) (c : Fin k → ℝ) (t : ℝ) :
    finiteMixtureValue A (p + t • c) =
      fun i ↦ v i * (1 + t * relativeDictionaryMap A v c i) := by
  funext i
  have hpvi := congrFun hpv i
  unfold finiteMixtureValue at hpvi ⊢
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    relativeDictionaryMap_apply] at hpvi ⊢
  have hexpand : (∑ x, (p x + t * c x) * A x i) =
      (∑ x, p x * A x i) + t * ∑ x, c x * A x i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, hpvi]
  field_simp [hv i]

/-- Consequently every active zero-mass tangent gives a locally feasible
fitted-value path in the dictionary convex hull. -/
theorem eventually_multiplicative_tangent_mem_convexHull
    {k n : ℕ} (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (p : Fin k → ℝ) (hp : p ∈ finiteMixtureFiber A v)
    (hpfull : ∀ j, 0 < p j) (hv : ∀ i, v i ≠ 0)
    (c : zeroSumCoefficients k) :
    ∀ᶠ t : ℝ in nhds 0,
      (fun i ↦ v i * (1 + t * relativeDictionaryMap A v c.1 i)) ∈
        convexHull ℝ (Set.range A) := by
  filter_upwards [eventually_mem_finiteSimplex_add_smul_zeroSum p hp.1 hpfull c]
    with t ht
  rw [← finiteMixtureValue_add_smul_eq_mul_one_add_relative A v p hp.2 hv c.1 t]
  exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A _ ht

/-- If two second-order expansions are eventually ordered on the positive
side, then their quadratic coefficients have the same order. -/
theorem secondOrderCoefficient_le
    (f g : ℝ → ℝ) (a b : ℝ)
    (hf : f =o[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ t ^ 2)
    (hg : g =o[nhdsWithin 0 (Ioi 0)] fun t : ℝ ↦ t ^ 2)
    (hle : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      f t + t ^ 2 * a ≤ g t + t ^ 2 * b) :
    a ≤ b := by
  have hfa : Tendsto (fun t : ℝ ↦ f t / t ^ 2 + a)
      (nhdsWithin 0 (Ioi 0)) (nhds a) := by
    simpa using hf.tendsto_div_nhds_zero.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ a)
        (nhdsWithin 0 (Ioi 0)) (nhds a))
  have hgb : Tendsto (fun t : ℝ ↦ g t / t ^ 2 + b)
      (nhdsWithin 0 (Ioi 0)) (nhds b) := by
    simpa using hg.tendsto_div_nhds_zero.add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ b)
        (nhdsWithin 0 (Ioi 0)) (nhds b))
  apply le_of_tendsto_of_tendsto hfa hgb
  filter_upwards [hle, self_mem_nhdsWithin] with t ht htp
  have ht0 : t ≠ 0 := ne_of_gt htp
  have hspos : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  calc
    f t / t ^ 2 + a = (f t + t ^ 2 * a) / t ^ 2 := by
      field_simp [ht0]
    _ ≤ (g t + t ^ 2 * b) / t ^ 2 :=
      (div_le_div_iff_of_pos_right hspos).2 ht
    _ = g t / t ^ 2 + b := by
      field_simp [ht0]

/-- The core directional support-sensitivity inequality.  Every
mass-preserving active-support tangent is dominated by the Hessian quadratic
form of the fitted log map. -/
theorem finite_optimizer_directional_sensitivity_lower
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (h : Fin n → ℝ) (c : zeroSumCoefficients k) :
    2 * ∑ i, h i * relativeDictionaryMap A v c.1 i -
        ∑ i, w i * (relativeDictionaryMap A v c.1 i) ^ 2 ≤
      ∑ i, h i * J h i := by
  let u : Fin n → ℝ := relativeDictionaryMap A v c.1
  let ell : ℝ := ∑ i, h i * Real.log (v i)
  let ac : ℝ := (∑ i, h i * u i) - (1 / 2 : ℝ) * ∑ i, w i * u i ^ 2
  let af : ℝ := (1 / 2 : ℝ) * ∑ i, h i * J h i
  let fc : ℝ → ℝ := fun t ↦
    weightedLogLikelihood (w + t • h) (fun i ↦ v i * (1 + t * u i)) -
      weightedLogLikelihood w v - t * ell - t ^ 2 * ac
  let ff : ℝ → ℝ := fun t ↦
    fittedOptimalValue vhat (w + t • h) - fittedOptimalValue vhat w -
      t * ell - t ^ 2 * af
  have hsubset : convexHull ℝ (Set.range A) ⊆ C := convexHull_min hA hC
  have hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v := by
    refine ⟨?_, ?_⟩
    · rw [← hp.2]
      exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
    · intro q hq
      simpa [hvw] using (hmax w).2 q (hsubset hq)
  have hcontact := finite_optimizer_full_support_raw_contact
    A v p w hw hp hpfull hvpos hApos hvmax
  have hwu : ∑ i, w i * u i = 0 := by
    exact relativeDictionary_weighted_sum_eq_zero_of_contact A v w hcontact c
  have hfc : fc =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
    have hcand := weightedLogLikelihood_multiplicative_secondOrder
      w h v u hvpos
    convert hcand using 1
    ext t
    dsimp [fc, ell, ac]
    rw [hwu]
    ring
  have hff : ff =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
    have hfit := fittedValue_secondOrderExpansion_of_eventually
      (fittedOptimalValue vhat) (fun q i ↦ Real.log (vhat q i)) hpsi hz h
    convert hfit using 1
    ext t
    dsimp [ff, ell, af]
    rw [hvw]
    ring
  have hfeas := eventually_multiplicative_tangent_mem_convexHull
    A v p hp hpfull (fun i ↦ (hvpos i).ne') c
  have hdom : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      fc t + t ^ 2 * ac ≤ ff t + t ^ 2 * af := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hfeas] with t ht
    have hm := (hmax (w + t • h)).2
      (fun i ↦ v i * (1 + t * u i)) (hsubset ht)
    have hm' : weightedLogLikelihood (w + t • h)
        (fun i ↦ v i * (1 + t * u i)) ≤
        fittedOptimalValue vhat (w + t • h) := by
      simpa [fittedOptimalValue] using hm
    dsimp [fc, ff]
    have hbase : fittedOptimalValue vhat w = weightedLogLikelihood w v := by
      simp [fittedOptimalValue, hvw]
    rw [hbase]
    linarith
  have hab : ac ≤ af := secondOrderCoefficient_le fc ff ac af hfc hff hdom
  dsimp [ac, af, u] at hab ⊢
  linarith

/-- Multiplying by the orthogonal-projection matrix associated with the
canonical orthonormal basis of a submodule produces a vector in that
submodule. -/
theorem submodule_projection_mulVec_mem {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    WithLp.toLp 2 (((submoduleOrthonormalMatrix S) *
      (submoduleOrthonormalMatrix S)ᴴ) *ᵥ x) ∈ S := by
  let V := submoduleOrthonormalMatrix S
  let b : Fin (Module.finrank ℝ S) → ℝ := Vᴴ *ᵥ x
  have hsum : WithLp.toLp 2 (V *ᵥ b) =
      ∑ j, b j • matrixColumnEuclidean V j := by
    apply PiLp.ext
    intro i
    simp [Matrix.mulVec, dotProduct, matrixColumnEuclidean, mul_comm]
  change WithLp.toLp 2 ((V * Vᴴ) *ᵥ x) ∈ S
  rw [← Matrix.mulVec_mulVec]
  change WithLp.toLp 2 (V *ᵥ b) ∈ S
  rw [hsum]
  exact S.sum_mem fun j _ ↦ S.smul_mem (b j)
    (submoduleOrthonormalMatrix_column_mem S j)

/-- The projection `V Vᴴ` associated with orthonormal columns is idempotent
and satisfies `⟨Px,Px⟩ = ⟨x,Px⟩`. -/
theorem projection_mulVec_dot_self_eq {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq k]
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) (x : n → ℝ) :
    let s := (V * Vᴴ) *ᵥ x
    dotProduct s s = dotProduct x s := by
  let P : Matrix n n ℝ := V * Vᴴ
  let s : n → ℝ := P *ᵥ x
  have hP2 : P * P = P := by
    dsimp [P]
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hs : P *ᵥ s = s := by
    change P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec, hP2]
  have hVs : Vᴴ *ᵥ s = Vᴴ *ᵥ x := by
    change Vᴴ *ᵥ ((V * Vᴴ) *ᵥ x) = Vᴴ *ᵥ x
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  change dotProduct s s = dotProduct x s
  calc
    dotProduct s s = dotProduct s (P *ᵥ s) := by rw [hs]
    _ = ∑ j, (∑ i, V i j * s i) ^ 2 := by
      simpa [P] using projectionQuadratic_eq_sum_sq V s
    _ = ∑ j, (∑ i, V i j * x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      have hj := congrFun hVs j
      simpa [Matrix.mulVec, dotProduct] using hj
    _ = dotProduct x (P *ᵥ x) := by
      simpa [P] using (projectionQuadratic_eq_sum_sq V x).symm
    _ = dotProduct x s := rfl

/-- Coordinatewise quadratic lower bound of the conjugated fitted-log
Hessian by the active tangent projection. -/
theorem finite_optimizer_hessian_projection_quadratic_lower
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (x : Fin n → ℝ) :
    let S := weightedRelativeTangentSpace A v w
    let V := submoduleOrthonormalMatrix S
    let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
      fittedLogDerivativeMatrix J *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    (∑ j, (∑ i, V i j * x i) ^ 2) ≤ dotProduct x (R *ᵥ x) := by
  let S := weightedRelativeTangentSpace A v w
  let V := submoduleOrthonormalMatrix S
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  let R : Matrix (Fin n) (Fin n) ℝ := D * fittedLogDerivativeMatrix J * D
  let s : Fin n → ℝ := (V * Vᴴ) *ᵥ x
  have hsmem : WithLp.toLp 2 s ∈ S := by
    exact submodule_projection_mulVec_mem S x
  rcases hsmem with ⟨c, hc⟩
  let u : Fin n → ℝ := relativeDictionaryMap A v c.1
  have hsu (i : Fin n) : Real.sqrt (w i) * u i = s i := by
    have hi := congrArg (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) hc
    simpa [S, weightedRelativeTangentSpace,
      weightedMassPreservingRelativeMap, weightedRelativeDictionaryMap,
      u, s] using hi
  let h : Fin n → ℝ := fun i ↦ Real.sqrt (w i) * x i
  have hdir := finite_optimizer_directional_sensitivity_lower
    A v p w hw hp hpfull hvpos hApos vhat hC hA hmax hvw hpsi hz h c
  have hcross : (∑ i, h i * u i) = dotProduct x s := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [h]
    rw [← hsu i]
    ring
  have hnorm : (∑ i, w i * u i ^ 2) = dotProduct s s := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hsu i]
    nlinarith [Real.sq_sqrt (hw i).le]
  have hproj : dotProduct s s = dotProduct x s := by
    exact projection_mulVec_dot_self_eq V
      (submoduleOrthonormalMatrix_conjTranspose_mul S) x
  have hdiag : D *ᵥ x = h := by
    funext i
    exact Matrix.mulVec_diagonal _ _ _
  have hRmul : R *ᵥ x = fun i ↦ Real.sqrt (w i) * J h i := by
    calc
      R *ᵥ x = D *ᵥ (fittedLogDerivativeMatrix J *ᵥ (D *ᵥ x)) := by
        dsimp [R]
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = D *ᵥ (J h) := by rw [hdiag, fittedLogDerivativeMatrix_mulVec]
      _ = fun i ↦ Real.sqrt (w i) * J h i := by
        funext i
        exact Matrix.mulVec_diagonal _ _ _
  have hrhs : (∑ i, h i * J h i) = dotProduct x (R *ᵥ x) := by
    rw [hRmul, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [h]
    ring
  change (∑ j, (∑ i, V i j * x i) ^ 2) ≤ dotProduct x (R *ᵥ x)
  calc
    (∑ j, (∑ i, V i j * x i) ^ 2) = dotProduct x s := by
      simpa [s] using (projectionQuadratic_eq_sum_sq V x).symm
    _ = 2 * dotProduct x s - dotProduct s s := by rw [hproj]; ring
    _ = 2 * ∑ i, h i * u i - ∑ i, w i * u i ^ 2 := by
      rw [hcross, hnorm]
    _ ≤ ∑ i, h i * J h i := hdir
    _ = dotProduct x (R *ᵥ x) := hrhs

/-- Loewner domination of the active-support tangent projection by the
square-root-conjugated fitted-log Hessian. -/
theorem finite_optimizer_hessian_sub_projection_posSemidef
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w) :
    let S := weightedRelativeTangentSpace A v w
    let V := submoduleOrthonormalMatrix S
    let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
      fittedLogDerivativeMatrix J *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    (R - V * Vᴴ).PosSemidef := by
  let S := weightedRelativeTangentSpace A v w
  let V := submoduleOrthonormalMatrix S
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  let R : Matrix (Fin n) (Fin n) ℝ := D * fittedLogDerivativeMatrix J * D
  have hJ : (fittedLogDerivativeMatrix J).IsHermitian :=
    fittedLogDerivativeMatrix_isHermitian_of_eventually (fittedOptimalValue vhat)
      (fun q i ↦ Real.log (vhat q i)) hpsi hz
  have hD : D.IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have hR : R.IsHermitian := by
    have hc := Matrix.isHermitian_conjTranspose_mul_mul D hJ
    rw [hD.eq] at hc
    exact hc
  apply matrix_sub_projection_posSemidef_of_quadratic_lower R hR V
  intro x
  exact finite_optimizer_hessian_projection_quadratic_lower
    A v p w hw hp hpfull hvpos hApos vhat hC hA hmax hvw hpsi hz x

/-- A `k`-atom extreme optimizer contributes the exact `(17/9)^(k-1)`
determinant gain in the paper's matrix-sensitivity lemma. -/
theorem finite_extreme_optimizer_hessian_determinant_lower
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
        fittedLogDerivativeMatrix J *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i))).det := by
  let S := weightedRelativeTangentSpace A v w
  let V := submoduleOrthonormalMatrix S
  let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
    fittedLogDerivativeMatrix J * Matrix.diagonal (fun i ↦ Real.sqrt (w i))
  have hprojection : (R - V * Vᴴ).PosSemidef :=
    finite_optimizer_hessian_sub_projection_posSemidef
      A v p w hw hp hpfull hvpos hApos vhat hC hA hmax hvw hpsi hz
  have hsubset : convexHull ℝ (Set.range A) ⊆ C := convexHull_min hA hC
  have hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v := by
    refine ⟨?_, ?_⟩
    · rw [← hp.2]
      exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
    · intro q hq
      simpa [hvw] using (hmax w).2 q (hsubset hq)
  have hdim : Module.finrank ℝ S = k - 1 :=
    finite_extreme_optimizer_weighted_tangent_finrank
      A v p w hw hp hpfull hvpos hApos hvmax hextreme
  have hdet := determinant_diagonal_add_psd_projection_lower a ha0 haUpper
    V (submoduleOrthonormalMatrix_conjTranspose_mul S) R hprojection
  simpa only [Fintype.card_fin, hdim] using hdet

/-- The same determinant gain for the paper's nonsymmetric Jacobian matrix
`diag(a) + diag(w) Dz`. -/
theorem finite_extreme_optimizer_jacobian_determinant_lower
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by
  rw [det_diagonal_add_weight_mul_eq_sqrt_conj w a hw]
  exact finite_extreme_optimizer_hessian_determinant_lower
    A v p w hw hp hpfull hvpos hApos hextreme vhat hC hA hmax hvw hpsi hz
      a ha0 haUpper

/-- Canonical fitted-value version of the Jacobian bound.  The envelope
identity and positivity of the fitted vector are consequences of compact
positive convex feasibility, not additional analytic assumptions. -/
theorem canonical_finite_extreme_optimizer_jacobian_determinant_lower
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (A : Fin k → Fin n → ℝ) (hA : Set.range A ⊆ C)
    (p : Fin k → ℝ) (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hp : p ∈ finiteMixtureFiber A (fittedValueSelection C hCcompact hCnonempty hCpos w))
    (hpfull : ∀ j, 0 < p j)
    (hextreme : p ∈ (finiteMixtureFiber A
      (fittedValueSelection C hCcompact hCnonempty hCpos w)).extremePoints ℝ)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by
  exact finite_extreme_optimizer_jacobian_determinant_lower
    A (fittedValueSelection C hCcompact hCnonempty hCpos w) p w hw hp hpfull
    (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
    (fun j ↦ hCpos (hA (mem_range_self j))) hextreme
    (fittedValueSelection C hCcompact hCnonempty hCpos) hC hA
    (fun q ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q) rfl
    (eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
      C hC hCcompact hCnonempty hCpos w hw) hz a ha0 haUpper

end ReweightedNPMLE
