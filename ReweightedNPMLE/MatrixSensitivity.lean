import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Determinant monotonicity for sensitivity matrices

This file supplies the positive-definite determinant comparison used in the
paper's support--sensitivity argument.  Mathlib provides the spectral theorem
and positivity of eigenvalues; the two lemmas below package them into the
Loewner monotonicity statement needed by the Jacobian estimate.
-/

open Matrix
open scoped MatrixOrder

namespace ReweightedNPMLE

/-- Adding a positive-semidefinite matrix to the identity cannot decrease its
determinant. -/
theorem det_one_add_posSemidef_ge_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.PosSemidef) :
    1 ≤ (1 + C).det := by
  let U := hC.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℝ := diagonal hC.isHermitian.eigenvalues
  have hspec : C = U * D * star (U : Matrix n n ℝ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hC.isHermitian.spectral_theorem
  have hunit : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have hdet : (1 + C).det = (1 + D).det := by
    rw [hspec]
    have heq : (1 : Matrix n n ℝ) +
        (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) =
        (U : Matrix n n ℝ) * (1 + D) * star (U : Matrix n n ℝ) := by
      calc
        (1 : Matrix n n ℝ) + (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) =
            (U : Matrix n n ℝ) * 1 * star (U : Matrix n n ℝ) +
              U * D * star (U : Matrix n n ℝ) := by rw [Matrix.mul_one, hunit]
        _ = (U : Matrix n n ℝ) * (1 + D) * star (U : Matrix n n ℝ) := by
          noncomm_ring
    rw [heq, Matrix.det_mul, Matrix.det_mul]
    calc
      (U : Matrix n n ℝ).det * (1 + D).det * (star (U : Matrix n n ℝ)).det =
          ((U : Matrix n n ℝ).det * (star (U : Matrix n n ℝ)).det) *
            (1 + D).det := by ring
      _ = ((U : Matrix n n ℝ) * star (U : Matrix n n ℝ)).det * (1 + D).det := by
        rw [Matrix.det_mul]
      _ = (1 + D).det := by rw [hunit, Matrix.det_one, one_mul]
  rw [hdet]
  rw [show (1 + D) = diagonal (fun i ↦ 1 + hC.isHermitian.eigenvalues i) by
    classical
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]]
  rw [det_diagonal]
  apply Finset.one_le_prod
  intro i hi
  linarith [hC.eigenvalues_nonneg i]

/-- Determinant is monotone in Loewner order above a positive-definite base. -/
theorem det_mono_of_posDef_of_sub_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hBA : (B - A).PosSemidef) :
    A.det ≤ B.det := by
  let C := B - A
  let S := CFC.sqrt A
  have hSnonneg : (0 : Matrix n n ℝ) ≤ S := CFC.sqrt_nonneg A
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hSnonneg
  have hSinvHerm : (S⁻¹)ᴴ = S⁻¹ := hSpsd.isHermitian.inv.eq
  have hCconj : (S⁻¹ * C * S⁻¹).PosSemidef := by
    have h := hBA.conjTranspose_mul_mul_same S⁻¹
    rw [hSinvHerm] at h
    exact h
  have hsq : S * S = A := by
    simpa [S, pow_two] using CFC.sq_sqrt A
  have hinv : A⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← hsq, Matrix.mul_inv_rev]
  have hone : 1 ≤ (1 + A⁻¹ * C).det := by
    rw [hinv, Matrix.mul_assoc,
      Matrix.det_one_add_mul_comm S⁻¹ (S⁻¹ * C)]
    exact det_one_add_posSemidef_ge_one hCconj
  have hAunitdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA.isUnit
  have hfactor : B.det = A.det * (1 + A⁻¹ * C).det := by
    have hB : B = A + C * (1 : Matrix n n ℝ) := by simp [C]
    rw [hB, Matrix.det_add_mul C 1 hAunitdet]
    simp
  rw [hfactor]
  exact (le_mul_iff_one_le_right hA.det_pos).2 hone

/-- The quantitative determinant gain from an orthonormal family of
sensitivity directions.  The upper diagonal bound `9/8` gives the inverse
bound `8/9`; adding the identity therefore contributes `17/9` in every
direction. -/
theorem determinant_diagonal_add_projection_lower
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (a : n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8)
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      (diagonal a + V * Vᴴ).det := by
  let A : Matrix n n ℝ := diagonal a
  let G : Matrix k k ℝ := Vᴴ * A⁻¹ * V
  let c : ℝ := 8 / 9
  have hApos : A.PosDef := by
    dsimp [A]
    rw [Matrix.posDef_diagonal_iff]
    exact ha0
  have haunit : IsUnit a := Pi.isUnit_iff.mpr fun i ↦
    isUnit_iff_ne_zero.mpr (ha0 i).ne'
  have hAdiag : A.det = ∏ i, a i := by simp [A, Matrix.det_diagonal]
  have hAinvLower : (A⁻¹ - c • (1 : Matrix n n ℝ)).PosSemidef := by
    have heq : A⁻¹ - c • (1 : Matrix n n ℝ) =
        diagonal (fun i ↦ (a i)⁻¹ - c) := by
      classical
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [A, Matrix.inv_diagonal, Matrix.sub_apply, Matrix.diagonal_apply_eq,
          Matrix.smul_apply, Matrix.one_apply_eq]
        rw [Ring.inverse_of_isUnit haunit, haunit.val_inv_apply]
        simp
      · simp [A, c, Matrix.inv_diagonal, hij]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hinv : c ≤ (a i)⁻¹ := by
      rw [show (a i)⁻¹ = 1 / a i by simp, le_div_iff₀ (ha0 i)]
      dsimp [c]
      nlinarith [haUpper i]
    exact sub_nonneg.mpr hinv
  have hGsub : (G - c • (1 : Matrix k k ℝ)).PosSemidef := by
    have h := hAinvLower.conjTranspose_mul_mul_same V
    have hscalar : Vᴴ * (c • (1 : Matrix n n ℝ)) * V =
        c • (1 : Matrix k k ℝ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV]
    have heq : Vᴴ * (A⁻¹ - c • (1 : Matrix n n ℝ)) * V =
        G - c • (1 : Matrix k k ℝ) := by
      dsimp [G]
      calc
        Vᴴ * (A⁻¹ - c • (1 : Matrix n n ℝ)) * V =
            Vᴴ * A⁻¹ * V - Vᴴ * (c • (1 : Matrix n n ℝ)) * V := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = Vᴴ * A⁻¹ * V - c • (1 : Matrix k k ℝ) := by rw [hscalar]
    rw [heq] at h
    exact h
  have hbase : (1 + c • (1 : Matrix k k ℝ)).PosDef := by
    have heq : (1 + c • (1 : Matrix k k ℝ)) =
        diagonal (fun _ ↦ 1 + c) := by
      classical
      ext i j
      by_cases hij : i = j
      · subst j
        simp [c]
      · simp [hij]
    rw [heq, Matrix.posDef_diagonal_iff]
    intro i
    norm_num [c]
  have horder : ((1 + G) - (1 + c • (1 : Matrix k k ℝ))).PosSemidef := by
    have heq : (1 + G) - (1 + c • (1 : Matrix k k ℝ)) =
        G - c • (1 : Matrix k k ℝ) := by abel
    rw [heq]
    exact hGsub
  have hdetG : (17 / 9 : ℝ) ^ Fintype.card k ≤ (1 + G).det := by
    have hmono := det_mono_of_posDef_of_sub_posSemidef hbase horder
    have hbaseDet : (1 + c • (1 : Matrix k k ℝ)).det =
        (17 / 9 : ℝ) ^ Fintype.card k := by
      have heq : (1 + c • (1 : Matrix k k ℝ)) =
          diagonal (fun _ ↦ (17 / 9 : ℝ)) := by
        classical
        ext i j
        by_cases hij : i = j
        · subst j
          norm_num [c]
        · simp [hij]
      rw [heq, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
    rwa [hbaseDet] at hmono
  have hfactor : (diagonal a + V * Vᴴ).det = (∏ i, a i) * (1 + G).det := by
    have hAunitdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hApos.isUnit
    have h := Matrix.det_add_mul V Vᴴ hAunitdet
    rw [hAdiag] at h
    simpa [A, G] using h
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hdetG
    (Finset.prod_nonneg fun i _ ↦ (ha0 i).le)

/-- Matrix-sensitivity form of the Jacobian lower bound.  If `R` dominates
the orthogonal projection `V Vᴴ`, its determinant is at least the same
`(17/9)^k` gain over the diagonal factor. -/
theorem determinant_diagonal_add_psd_projection_lower
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (a : n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8)
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) (R : Matrix n n ℝ)
    (hR : (R - V * Vᴴ).PosSemidef) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      (diagonal a + R).det := by
  have hbase : (diagonal a + V * Vᴴ).PosDef :=
    (Matrix.PosDef.diagonal ha0).add_posSemidef
      (Matrix.posSemidef_self_mul_conjTranspose V)
  have hsub : ((diagonal a + R) - (diagonal a + V * Vᴴ)).PosSemidef := by
    have heq : (diagonal a + R) - (diagonal a + V * Vᴴ) = R - V * Vᴴ := by abel
    rwa [heq]
  exact (determinant_diagonal_add_projection_lower a ha0 haUpper V hV).trans
    (det_mono_of_posDef_of_sub_posSemidef hbase hsub)

/-- The nonsymmetric Jacobian matrix `diag(a) + diag(w) H` has the same
determinant as its square-root conjugate
`diag(a) + diag(√w) H diag(√w)`. -/
theorem det_diagonal_add_weight_mul_eq_sqrt_conj
    {n : Type*} [Fintype n] [DecidableEq n]
    (w a : n → ℝ) (hw : ∀ i, 0 < w i) (H : Matrix n n ℝ) :
    (Matrix.diagonal a + Matrix.diagonal w * H).det =
      (Matrix.diagonal a + Matrix.diagonal (fun i ↦ Real.sqrt (w i)) * H *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i))).det := by
  let s : n → ℝ := fun i ↦ Real.sqrt (w i)
  let S : Matrix n n ℝ := Matrix.diagonal s
  have hdiagMul (x y : n → ℝ) :
      Matrix.diagonal x * Matrix.diagonal y = Matrix.diagonal (fun i ↦ x i * y i) := by
    classical
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    · intro b hb hbi
      simp [Ne.symm hbi]
    · simp
  have hSsq : S * S = Matrix.diagonal w := by
    change Matrix.diagonal s * Matrix.diagonal s = Matrix.diagonal w
    rw [hdiagMul]
    congr 1
    funext i
    dsimp [s]
    nlinarith [Real.sq_sqrt (hw i).le]
  have hAS : Matrix.diagonal a * S = S * Matrix.diagonal a := by
    change Matrix.diagonal a * Matrix.diagonal s =
      Matrix.diagonal s * Matrix.diagonal a
    rw [hdiagMul, hdiagMul]
    congr 1
    funext i
    ring
  have hmul : (Matrix.diagonal a + Matrix.diagonal w * H) * S =
      S * (Matrix.diagonal a + S * H * S) := by
    rw [← hSsq]
    calc
      (Matrix.diagonal a + S * S * H) * S =
          Matrix.diagonal a * S + S * S * H * S := by rw [Matrix.add_mul]
      _ = S * Matrix.diagonal a + S * S * H * S := by rw [hAS]
      _ = S * (Matrix.diagonal a + S * H * S) := by noncomm_ring
  have hSdet : 0 < S.det := by
    change 0 < (Matrix.diagonal s).det
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos fun i _ ↦ Real.sqrt_pos.2 (hw i)
  have hdet := congrArg Matrix.det hmul
  simp only [Matrix.det_mul] at hdet
  apply mul_right_cancel₀ hSdet.ne'
  calc
    (Matrix.diagonal a + Matrix.diagonal w * H).det * S.det =
        S.det * (Matrix.diagonal a + S * H * S).det := hdet
    _ = (Matrix.diagonal a + S * H * S).det * S.det := mul_comm _ _

/-- The quadratic form of `V Vᴴ` is the sum of the squared coordinates
against the columns of `V`. -/
theorem projectionQuadratic_eq_sum_sq
    {n k : Type*} [Fintype n] [Fintype k]
    (V : Matrix n k ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((V * Vᴴ) *ᵥ x) = ∑ j, (∑ i, V i j * x i) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_conjTranspose]
  simp [dotProduct, vecMul, pow_two, mul_comm]

/-- A coordinatewise quadratic lower bound by the columns of `V` is
equivalent to Loewner domination of the projection-shaped matrix `V Vᴴ`.
This packages the final linear-algebra step of the support-sensitivity
argument. -/
theorem matrix_sub_projection_posSemidef_of_quadratic_lower
    {n k : Type*} [Fintype n] [Fintype k]
    (R : Matrix n n ℝ) (hR : R.IsHermitian)
    (V : Matrix n k ℝ)
    (hquad : ∀ x : n → ℝ,
      (∑ j, (∑ i, V i j * x i) ^ 2) ≤ x ⬝ᵥ (R *ᵥ x)) :
    (R - V * Vᴴ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact hR.sub (Matrix.isHermitian_mul_conjTranspose_self V)
  · intro x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    rw [projectionQuadratic_eq_sum_sq]
    exact sub_nonneg.mpr (hquad x)

end ReweightedNPMLE
