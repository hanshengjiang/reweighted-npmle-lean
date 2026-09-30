import ReweightedNPMLE.NumericalIntervals
import ReweightedNPMLE.NumericalLogBounds

/-! # Exact finite least-squares expressions and regression input records -/

open scoped BigOperators

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false

structure NumericalRegressionPoint where
  alpha : ℚ
  rawSamples : List ℚ
  permutation : List Nat
  sortedSamples : List ℚ
  xLog : NumericalLogCertificate
  yLog : NumericalLogCertificate

structure NumericalRegressionDataset where
  metric : String
  points : List NumericalRegressionPoint
  printed : ℚ
  slopeEnclosure : NumericalInterval

def numericalRegressionMedian (p : NumericalRegressionPoint) : ℚ :=
  (p.sortedSamples.getD 14 0 + p.sortedSamples.getD 15 0) / 2

def numericalExprSum (f : Nat → NumericalExpr) : Nat → NumericalExpr
  | 0 => .constant 0
  | N + 1 => .add (numericalExprSum f N) (f N)

@[simp] theorem numericalExprSum_eval (f : Nat → NumericalExpr) (N : Nat)
    (values : Nat → ℝ) :
    (numericalExprSum f N).eval values = ∑ i ∈ Finset.range N, (f i).eval values := by
  induction N with
  | zero => simp [numericalExprSum, NumericalExpr.eval]
  | succ N ih => simp [numericalExprSum, NumericalExpr.eval, ih, Finset.sum_range_succ]

def numericalOLSExpression (N : Nat) : NumericalExpr :=
  let sx := numericalExprSum (fun i ↦ .input (2 * i)) N
  let sy := numericalExprSum (fun i ↦ .input (2 * i + 1)) N
  let sxy := numericalExprSum (fun i ↦ .mul (.input (2 * i)) (.input (2 * i + 1))) N
  let sxx := numericalExprSum (fun i ↦ .mul (.input (2 * i)) (.input (2 * i))) N
  .div (.sub (.mul (.constant N) sxy) (.mul sx sy))
    (.sub (.mul (.constant N) sxx) (.mul sx sx))

noncomputable def numericalOLSSlope (N : Nat) (x y : Nat → ℝ) : ℝ :=
  (N * (∑ i ∈ Finset.range N, x i * y i) -
    (∑ i ∈ Finset.range N, x i) * (∑ i ∈ Finset.range N, y i)) /
  (N * (∑ i ∈ Finset.range N, (x i) ^ 2) - (∑ i ∈ Finset.range N, x i) ^ 2)

theorem numericalOLSExpression_eval (N : Nat) (values : Nat → ℝ) :
    (numericalOLSExpression N).eval values = numericalOLSSlope N
      (fun i ↦ values (2 * i)) (fun i ↦ values (2 * i + 1)) := by
  simp [numericalOLSExpression, NumericalExpr.eval, numericalOLSSlope, pow_two]

def numericalRegressionFallbackCertificate : NumericalLogCertificate := ⟨1, false, 0, 0, 0⟩

def numericalRegressionCertificate (d : NumericalRegressionDataset) (i : Nat) : NumericalLogCertificate :=
  match d.points[i / 2]? with
  | none => numericalRegressionFallbackCertificate
  | some p => if i % 2 = 0 then p.xLog else p.yLog

def numericalRegressionIntervals (d : NumericalRegressionDataset) (i : Nat) : NumericalInterval :=
  let c := numericalRegressionCertificate d i
  ⟨c.lower, c.upper⟩

noncomputable def numericalRegressionValues (d : NumericalRegressionDataset) (i : Nat) : ℝ :=
  Real.log (numericalRegressionCertificate d i).argument

end ReweightedNPMLE.NumericalStudy
