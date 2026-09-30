import ReweightedNPMLE.NumericalTable

/-! # Real interpretation of exact rational sample means -/

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false

noncomputable def numericalRealSampleMean (xs : List ℚ) : ℝ :=
  (xs.map (fun (x : ℚ) ↦ (x : ℝ))).sum / (xs.length : ℝ)

theorem numerical_real_sample_mean_eq_cast (xs : List ℚ) :
    numericalRealSampleMean xs = (numericalSampleMean xs : ℝ) := by
  have hs : (xs.map (fun (x : ℚ) ↦ (x : ℝ))).sum = (xs.sum : ℝ) := by
    induction xs with
    | nil => simp only [List.map_nil, List.sum_nil, Rat.cast_zero]
    | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]
  unfold numericalRealSampleMean numericalSampleMean
  rw [hs]
  simp only [Rat.cast_div, Rat.cast_natCast]

theorem numerical_real_ratio_within_2p1_percent {q : ℚ}
    (hl : 1 ≤ q) (hu : q ≤ 1021 / 1000) : |(q : ℝ) - 1| ≤ 21 / 1000 := by
  have hrl : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hl
  have hru : (q : ℝ) ≤ (1021 : ℝ) / 1000 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hu
  rw [abs_le]
  constructor <;> linarith

end ReweightedNPMLE.NumericalStudy
