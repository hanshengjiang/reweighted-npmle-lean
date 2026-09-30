import ReweightedNPMLE.NumericalRegressionArithmetic

/-! # Mathematical least-squares correspondence for the numerical slopes -/

open scoped BigOperators

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false

noncomputable def numericalOLSIntercept (N : Nat) (x y : Nat → ℝ) : ℝ :=
  ((∑ i ∈ Finset.range N, y i) - numericalOLSSlope N x y * (∑ i ∈ Finset.range N, x i)) / N

theorem numerical_ols_moment_equations (N : Nat) (x y : Nat → ℝ) (hN : 0 < N)
    (hD : 0 < N * (∑ i ∈ Finset.range N, (x i) ^ 2) - (∑ i ∈ Finset.range N, x i) ^ 2) :
    numericalOLSSlope N x y * (∑ i ∈ Finset.range N, (x i) ^ 2) +
      numericalOLSIntercept N x y * (∑ i ∈ Finset.range N, x i) =
        ∑ i ∈ Finset.range N, x i * y i ∧
    numericalOLSSlope N x y * (∑ i ∈ Finset.range N, x i) +
      numericalOLSIntercept N x y * N = ∑ i ∈ Finset.range N, y i := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hd := hD.ne'
  dsimp only [numericalOLSIntercept, numericalOLSSlope]
  constructor <;> field_simp [hn, hd] <;> ring

theorem numerical_least_squares_optimal_of_normal_equations
    (N : Nat) (x y : Nat → ℝ) (a b : ℝ)
    (hr : (∑ i ∈ Finset.range N, (y i - (a * x i + b))) = 0)
    (hxr : (∑ i ∈ Finset.range N, x i * (y i - (a * x i + b))) = 0)
    (A B : ℝ) :
    (∑ i ∈ Finset.range N, (y i - (a * x i + b)) ^ 2) ≤
      ∑ i ∈ Finset.range N, (y i - (A * x i + B)) ^ 2 := by
  let r := fun i ↦ y i - (a * x i + b)
  let g := fun i ↦ (a - A) * x i + (b - B)
  have hc : (∑ i ∈ Finset.range N, r i * g i) = 0 := by
    calc
      (∑ i ∈ Finset.range N, r i * g i) =
          ∑ i ∈ Finset.range N, ((a - A) * (x i * r i) + (b - B) * r i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [g]
        ring
      _ = (a - A) * (∑ i ∈ Finset.range N, x i * r i) +
          (b - B) * (∑ i ∈ Finset.range N, r i) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 0 := by rw [show (∑ i ∈ Finset.range N, x i * r i) = 0 from hxr,
          show (∑ i ∈ Finset.range N, r i) = 0 from hr]; ring
  have hs : (∑ i ∈ Finset.range N, (y i - (A * x i + B)) ^ 2) =
      (∑ i ∈ Finset.range N, (r i) ^ 2) + (∑ i ∈ Finset.range N, (g i) ^ 2) := by
    calc
      (∑ i ∈ Finset.range N, (y i - (A * x i + B)) ^ 2) =
          ∑ i ∈ Finset.range N, ((r i) ^ 2 + 2 * (r i * g i) + (g i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [r, g]
        ring
      _ = (∑ i ∈ Finset.range N, (r i) ^ 2) +
          2 * (∑ i ∈ Finset.range N, r i * g i) + (∑ i ∈ Finset.range N, (g i) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hc]; ring
  have hg : 0 ≤ ∑ i ∈ Finset.range N, (g i) ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  change (∑ i ∈ Finset.range N, (r i) ^ 2) ≤ _
  linarith

theorem numerical_ols_globally_minimizes_squared_error
    (N : Nat) (x y : Nat → ℝ) (hN : 0 < N)
    (hD : 0 < N * (∑ i ∈ Finset.range N, (x i) ^ 2) - (∑ i ∈ Finset.range N, x i) ^ 2)
    (A B : ℝ) :
    (∑ i ∈ Finset.range N,
      (y i - (numericalOLSSlope N x y * x i + numericalOLSIntercept N x y)) ^ 2) ≤
      ∑ i ∈ Finset.range N, (y i - (A * x i + B)) ^ 2 := by
  let a := numericalOLSSlope N x y
  let b := numericalOLSIntercept N x y
  have hm := numerical_ols_moment_equations N x y hN hD
  change a * (∑ i ∈ Finset.range N, (x i) ^ 2) + b * (∑ i ∈ Finset.range N, x i) =
    (∑ i ∈ Finset.range N, x i * y i) ∧
    a * (∑ i ∈ Finset.range N, x i) + b * N = (∑ i ∈ Finset.range N, y i) at hm
  apply numerical_least_squares_optimal_of_normal_equations N x y a b
  · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith [hm.2]
  · have hx : (∑ i ∈ Finset.range N, x i * (a * x i + b)) =
        a * (∑ i ∈ Finset.range N, (x i) ^ 2) + b * (∑ i ∈ Finset.range N, x i) := by
      calc
        (∑ i ∈ Finset.range N, x i * (a * x i + b)) =
            ∑ i ∈ Finset.range N, (a * (x i) ^ 2 + b * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hx, hm.1]
    ring

def numericalOLSNumeratorExpression (N : Nat) : NumericalExpr :=
  let sx := numericalExprSum (fun i ↦ .input (2 * i)) N
  let sy := numericalExprSum (fun i ↦ .input (2 * i + 1)) N
  let sxy := numericalExprSum (fun i ↦ .mul (.input (2 * i)) (.input (2 * i + 1))) N
  .sub (.mul (.constant N) sxy) (.mul sx sy)

def numericalOLSDenominatorExpression (N : Nat) : NumericalExpr :=
  let sx := numericalExprSum (fun i ↦ .input (2 * i)) N
  let sxx := numericalExprSum (fun i ↦ .mul (.input (2 * i)) (.input (2 * i))) N
  .sub (.mul (.constant N) sxx) (.mul sx sx)

theorem numericalOLSExpression_div (N : Nat) :
    numericalOLSExpression N = .div (numericalOLSNumeratorExpression N) (numericalOLSDenominatorExpression N) := rfl

theorem numericalOLSDenominatorExpression_eval (N : Nat) (values : Nat → ℝ) :
    (numericalOLSDenominatorExpression N).eval values =
      N * (∑ i ∈ Finset.range N, (values (2 * i)) ^ 2) -
        (∑ i ∈ Finset.range N, values (2 * i)) ^ 2 := by
  simp [numericalOLSDenominatorExpression, NumericalExpr.eval, pow_two]

end ReweightedNPMLE.NumericalStudy
