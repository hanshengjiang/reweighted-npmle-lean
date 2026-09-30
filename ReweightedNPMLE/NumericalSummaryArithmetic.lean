import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Basic

/-! # Raw Monte Carlo inputs for whole-design reporting checks -/

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false

/-- Recorded draws, before any averaging or risk-ratio computation. All lists
use the same replication order; support sizes are integers. -/
structure NumericalSummaryCell where
  scenario : String
  dimension : Nat
  sampleSize : Nat
  replications : List Nat
  ordinaryRisk : List ℚ
  balancedRisk : List ℚ
  tinyRisk : List ℚ
  bbRisk : List ℚ
  ordinarySupport : List Nat
  balancedSupport : List Nat
  tinySupport : List Nat
  bbSupport : List Nat
  balancedHellinger : List ℚ
  tinyHellinger : List ℚ
  balancedGap : List ℚ
  bbGap : List ℚ
  balancedLogfit : List ℚ

end ReweightedNPMLE.NumericalStudy
