import ReweightedNPMLE.FittedRegularity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

namespace ReweightedNPMLE

def coefficientTotalLinearMap (k : ℕ) : (Fin k → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ j, c j
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.mul_sum]

@[simp] theorem coefficientTotalLinearMap_apply (k : ℕ) (c : Fin k → ℝ) :
    coefficientTotalLinearMap k c = ∑ j, c j := rfl

def zeroSumCoefficients (k : ℕ) : Submodule ℝ (Fin k → ℝ) :=
  LinearMap.ker (coefficientTotalLinearMap k)

@[simp] theorem mem_zeroSumCoefficients {k : ℕ} (c : Fin k → ℝ) :
    c ∈ zeroSumCoefficients k ↔ ∑ j, c j = 0 := by
  rfl

theorem finrank_zeroSumCoefficients_add_one (k : ℕ) [Nonempty (Fin k)] :
    Module.finrank ℝ (zeroSumCoefficients k) + 1 = k := by
  have hne : coefficientTotalLinearMap k ≠ 0 := by
    intro hzero
    have happ := LinearMap.congr_fun hzero (fun _ : Fin k ↦ (1 : ℝ))
    simp [coefficientTotalLinearMap] at happ
    have hkpos : 0 < k := by
      simpa using (Fintype.card_pos : 0 < Fintype.card (Fin k))
    omega
  simpa [zeroSumCoefficients, Module.finrank_fin_fun] using
    Module.Dual.finrank_ker_add_one_of_ne_zero hne

theorem finrank_zeroSumCoefficients (k : ℕ) [Nonempty (Fin k)] :
    Module.finrank ℝ (zeroSumCoefficients k) = k - 1 := by
  have h := finrank_zeroSumCoefficients_add_one k
  omega

noncomputable def relativeDictionaryMap {k n : ℕ} (A : Fin k → Fin n → ℝ)
    (v : Fin n → ℝ) : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun c i := (∑ j, c j * A j i) / v i
  map_add' c d := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ x, r * c x * A x i) / v i =
          (r * ∑ x, c x * A x i) / v i := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = r * ((∑ j, c j * A j i) / v i) := by ring

@[simp] theorem relativeDictionaryMap_apply {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (c : Fin k → ℝ) (i : Fin n) :
    relativeDictionaryMap A v c i = (∑ j, c j * A j i) / v i := rfl

theorem relativeDictionaryMap_injective {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0) :
    Function.Injective (relativeDictionaryMap A v) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro c hc
    have hzero : ∑ j, c j • A j = 0 := by
      funext i
      have hi := congrFun (show relativeDictionaryMap A v c = 0 from hc) i
      simp only [relativeDictionaryMap_apply, Pi.zero_apply, div_eq_zero_iff] at hi
      simpa [smul_eq_mul] using hi.resolve_right (hv i)
    have hc0 := (Fintype.linearIndependent_iff.mp hlin) c hzero
    simpa only [Submodule.mem_bot] using funext hc0
  · exact bot_le

noncomputable def massPreservingRelativeMap {k n : ℕ} (A : Fin k → Fin n → ℝ)
    (v : Fin n → ℝ) : zeroSumCoefficients k →ₗ[ℝ] (Fin n → ℝ) :=
  (relativeDictionaryMap A v).comp (zeroSumCoefficients k).subtype

noncomputable def relativeTangentSpace {k n : ℕ} (A : Fin k → Fin n → ℝ)
    (v : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range (massPreservingRelativeMap A v)

theorem massPreservingRelativeMap_injective {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0) :
    Function.Injective (massPreservingRelativeMap A v) := by
  intro c d hcd
  apply Subtype.ext
  exact relativeDictionaryMap_injective A v hlin hv hcd

theorem finrank_relativeTangentSpace {k n : ℕ} [Nonempty (Fin k)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0) :
    Module.finrank ℝ (relativeTangentSpace A v) = k - 1 := by
  rw [relativeTangentSpace,
    LinearMap.finrank_range_of_inj (massPreservingRelativeMap_injective A v hlin hv)]
  exact finrank_zeroSumCoefficients k

theorem relativeDictionary_weighted_sum_eq_zero_of_contact {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hcontact : ∀ j, ∑ i, w i * (A j i / v i) = total w)
    (c : zeroSumCoefficients k) :
    ∑ i, w i * relativeDictionaryMap A v c i = 0 := by
  classical
  calc
    (∑ i, w i * relativeDictionaryMap A v c i) =
        ∑ i, ∑ j, c.1 j * (w i * (A j i / v i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [relativeDictionaryMap_apply]
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, c.1 j * ∑ i, w i * (A j i / v i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j, c.1 j * total w := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcontact j]
    _ = 0 := by
      have hc : ∑ j, c.1 j = 0 := by
        have hc' := c.property
        change coefficientTotalLinearMap k c.1 = 0 at hc'
        exact hc'
      rw [← Finset.sum_mul, hc]
      simp

noncomputable def weightedRelativeDictionaryMap {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ) :
    (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun c := WithLp.toLp 2 fun i ↦
    Real.sqrt (w i) * relativeDictionaryMap A v c i
  map_add' c d := by
    apply PiLp.ext
    intro i
    change Real.sqrt (w i) * relativeDictionaryMap A v (c + d) i = _
    rw [map_add]
    simp [Pi.add_apply]
    ring
  map_smul' r c := by
    apply PiLp.ext
    intro i
    change Real.sqrt (w i) * relativeDictionaryMap A v (r • c) i = _
    rw [map_smul]
    simp [Pi.smul_apply]
    ring

noncomputable def weightedMassPreservingRelativeMap {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ) :
    zeroSumCoefficients k →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (weightedRelativeDictionaryMap A v w).comp (zeroSumCoefficients k).subtype

noncomputable def weightedRelativeTangentSpace {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (weightedMassPreservingRelativeMap A v w)

theorem weightedMassPreservingRelativeMap_injective {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0)
    (hw : ∀ i, 0 < w i) :
    Function.Injective (weightedMassPreservingRelativeMap A v w) := by
  intro c d hcd
  apply Subtype.ext
  apply relativeDictionaryMap_injective A v hlin hv
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) hcd
  change Real.sqrt (w i) * relativeDictionaryMap A v c.1 i =
    Real.sqrt (w i) * relativeDictionaryMap A v d.1 i at hi
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (hw i)).ne' hi

theorem finrank_weightedRelativeTangentSpace {k n : ℕ} [Nonempty (Fin k)]
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0)
    (hw : ∀ i, 0 < w i) :
    Module.finrank ℝ (weightedRelativeTangentSpace A v w) = k - 1 := by
  rw [weightedRelativeTangentSpace,
    LinearMap.finrank_range_of_inj
      (weightedMassPreservingRelativeMap_injective A v w hlin hv hw)]
  exact finrank_zeroSumCoefficients k

theorem weightedRelativeDictionary_orthogonal_of_contact {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hcontact : ∀ j, ∑ i, w i * (A j i / v i) = total w)
    (c : zeroSumCoefficients k) :
    ∑ i, Real.sqrt (w i) * weightedRelativeDictionaryMap A v w c.1 i = 0 := by
  calc
    (∑ i, Real.sqrt (w i) * weightedRelativeDictionaryMap A v w c.1 i) =
        ∑ i, w i * relativeDictionaryMap A v c.1 i := by
      apply Finset.sum_congr rfl
      intro i _
      change Real.sqrt (w i) *
          (Real.sqrt (w i) * relativeDictionaryMap A v c.1 i) = _
      rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
    _ = 0 := relativeDictionary_weighted_sum_eq_zero_of_contact A v w hcontact c

noncomputable def submoduleOrthonormalMatrix {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin (Module.finrank ℝ S)) ℝ :=
  fun i j ↦ ((stdOrthonormalBasis ℝ S j : S) : Fin n → ℝ) i

theorem submoduleOrthonormalMatrix_conjTranspose_mul {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    (submoduleOrthonormalMatrix S)ᴴ * submoduleOrthonormalMatrix S = 1 := by
  classical
  ext j l
  rw [Matrix.mul_apply]
  change (∑ i, ((stdOrthonormalBasis ℝ S j : S) : Fin n → ℝ) i *
      ((stdOrthonormalBasis ℝ S l : S) : Fin n → ℝ) i) = _
  simp_rw [← Real.inner_apply]
  rw [← PiLp.inner_apply]
  change inner ℝ (stdOrthonormalBasis ℝ S j) (stdOrthonormalBasis ℝ S l) = _
  exact (orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ S).orthonormal j l).trans
    (by simp [Matrix.one_apply])

noncomputable def matrixColumnEuclidean {n m : ℕ}
    (V : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ V i j)

@[simp] theorem matrixColumnEuclidean_apply {n m : ℕ}
    (V : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) (i : Fin n) :
    matrixColumnEuclidean V j i = V i j := rfl

theorem submoduleOrthonormalMatrix_column_mem {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (j : Fin (Module.finrank ℝ S)) :
    matrixColumnEuclidean (submoduleOrthonormalMatrix S) j ∈ S := by
  change ((stdOrthonormalBasis ℝ S j : S) : EuclideanSpace ℝ (Fin n)) ∈ S
  exact (stdOrthonormalBasis ℝ S j).property

theorem exists_submodule_orthonormal_matrix {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ V : Matrix (Fin n) (Fin (Module.finrank ℝ S)) ℝ,
      Vᴴ * V = 1 ∧ ∀ j, matrixColumnEuclidean V j ∈ S := by
  exact ⟨submoduleOrthonormalMatrix S,
    submoduleOrthonormalMatrix_conjTranspose_mul S,
    submoduleOrthonormalMatrix_column_mem S⟩

noncomputable def sqrtWeightVector {n : ℕ} (w : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ Real.sqrt (w i)

theorem likelihoodContactNumerator_eq_total_of_functional_eq_one
    {n : ℕ} [Nonempty (Fin n)] (w v a : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hcontact : likelihoodContactFunctional w v a = 1) :
    likelihoodContactNumerator w v a = total w := by
  have hrewrite : likelihoodContactFunctional w v a =
      likelihoodContactNumerator w v a / total w := by
    rw [likelihoodContactFunctional_apply]
    unfold likelihoodContactNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hv i).ne', (total_pos hw).ne']
  rw [hrewrite] at hcontact
  field_simp [(total_pos hw).ne'] at hcontact
  exact hcontact

theorem finite_optimizer_full_support_raw_contact
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    ∀ j, ∑ i, w i * (A j i / v i) = total w := by
  intro j
  have hfun := likelihood_contact_on_finite_optimizer_support
    A v p w hw hp hvpos hApos hvmax j
      (by simp [coefficientSupport, (hpfull j).ne'])
  exact likelihoodContactNumerator_eq_total_of_functional_eq_one
    w v (A j) hw hvpos hfun

theorem finite_optimizer_weighted_tangent_orthogonal
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v)
    (c : zeroSumCoefficients k) :
    ∑ i, Real.sqrt (w i) * weightedRelativeDictionaryMap A v w c.1 i = 0 := by
  apply weightedRelativeDictionary_orthogonal_of_contact A v w
  · exact fun i ↦ (hw i).le
  · exact finite_optimizer_full_support_raw_contact
      A v p w hw hp hpfull hvpos hApos hvmax

theorem finite_optimizer_weighted_tangentSpace_orthogonal
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    ∀ x ∈ weightedRelativeTangentSpace A v w,
      inner ℝ (sqrtWeightVector w) x = 0 := by
  intro x hx
  rcases hx with ⟨c, rfl⟩
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  exact finite_optimizer_weighted_tangent_orthogonal
    A v p w hw hp hpfull hvpos hApos hvmax c

theorem finite_extreme_optimizer_weighted_tangent_finrank
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    Module.finrank ℝ (weightedRelativeTangentSpace A v w) = k - 1 := by
  have hlin : LinearIndependent ℝ A := by
    have hsupp : coefficientSupport p = Finset.univ := by
      ext j
      simp only [mem_coefficientSupport, Finset.mem_univ, iff_true]
      exact (hpfull j).ne'
    have hlinOn := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
      A v p w hw hp hvpos hApos hvmax).mp hextreme
    rw [hsupp] at hlinOn
    simpa using hlinOn
  exact finrank_weightedRelativeTangentSpace A v w hlin
    (fun i ↦ (hvpos i).ne') hw

end ReweightedNPMLE
