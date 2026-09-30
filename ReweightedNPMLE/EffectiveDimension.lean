import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import ReweightedNPMLE.FittedDeterminantMoment
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Probability assembly for effective-dimension sparsification

This file formalizes the Markov and event-union steps used after the radial
localization and determinant-moment estimates in Theorem 3.1.
-/

open MeasureTheory Set

namespace ReweightedNPMLE

/-- Markov transfer in the exact exponential normalization used in the determinant argument. -/
theorem markov_event_bound_exp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (E : Set Ω) (q : ℝ)
    (hYnonneg : 0 ≤ᵐ[μ] Y) (hYint : Integrable Y μ)
    (hmean : ∫ ω, Y ω ∂μ ≤ 1)
    (hlarge : E ⊆ {ω | Real.exp q ≤ Y ω}) :
    μ.real E ≤ Real.exp (-q) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hYnonneg hYint (Real.exp q)
  have hmono : μ.real E ≤ μ.real {ω | Real.exp q ≤ Y ω} :=
    measureReal_mono hlarge (by finiteness)
  have hprod : Real.exp q * μ.real {ω | Real.exp q ≤ Y ω} ≤ 1 :=
    hmarkov.trans hmean
  calc
    μ.real E ≤ μ.real {ω | Real.exp q ≤ Y ω} := hmono
    _ = Real.exp (-q) *
        (Real.exp q * μ.real {ω | Real.exp q ≤ Y ω}) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (-q) * 1 :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-q) := mul_one _

/--
The determinant moment gives an exponential support tail once the localization
event bounds its cost.
-/
theorem support_tail_from_determinant_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (localized : Set Ω) (support : Ω → ℕ) (cost : Ω → ℝ)
    {kappa H q : ℝ} (hkappa : 0 < kappa)
    (hcost : ∀ ω ∈ localized, cost ω ≤ H)
    (Y : Ω → ℝ)
    (hY : ∀ ω ∈ localized,
      Y ω = Real.exp (kappa * ((support ω : ℝ) - 1) - cost ω))
    (hYnonneg : 0 ≤ᵐ[μ] Y) (hYint : Integrable Y μ)
    (hmean : ∫ ω, Y ω ∂μ ≤ 1) :
    μ.real {ω | ω ∈ localized ∧
      H + q ≤ kappa * ((support ω : ℝ) - 1)} ≤ Real.exp (-q) := by
  apply markov_event_bound_exp μ Y _ q hYnonneg hYint hmean
  intro ω hω
  change ω ∈ localized ∧
    H + q ≤ kappa * ((support ω : ℝ) - 1) at hω
  rcases hω with ⟨hloc, hsupp⟩
  change Real.exp q ≤ Y ω
  rw [hY ω hloc]
  apply Real.exp_le_exp.mpr
  linarith [hcost ω hloc]

/-- Three exponentially small failure events have total probability at most `3e⁻ᵖ`. -/
theorem three_failure_events_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E₁ E₂ E₃ : Set Ω) (q : ℝ)
    (h₁ : μ.real E₁ ≤ Real.exp (-q))
    (h₂ : μ.real E₂ ≤ Real.exp (-q))
    (h₃ : μ.real E₃ ≤ Real.exp (-q)) :
    μ.real (E₁ ∪ E₂ ∪ E₃) ≤ 3 * Real.exp (-q) := by
  calc
    μ.real (E₁ ∪ E₂ ∪ E₃) ≤ μ.real (E₁ ∪ E₂) + μ.real E₃ :=
      measureReal_union_le _ _
    _ ≤ (μ.real E₁ + μ.real E₂) + μ.real E₃ := by
      gcongr
      exact measureReal_union_le _ _
    _ ≤ (Real.exp (-q) + Real.exp (-q)) + Real.exp (-q) := by linarith
    _ = 3 * Real.exp (-q) := by ring

/-- If every violation is covered by the three failure events, the same bound controls it. -/
theorem effective_dimension_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad E₁ E₂ E₃ : Set Ω) (q : ℝ)
    (hbad : bad ⊆ E₁ ∪ E₂ ∪ E₃)
    (h₁ : μ.real E₁ ≤ Real.exp (-q))
    (h₂ : μ.real E₂ ≤ Real.exp (-q))
    (h₃ : μ.real E₃ ≤ Real.exp (-q)) :
    μ.real bad ≤ 3 * Real.exp (-q) :=
  (measureReal_mono hbad (by finiteness)).trans
    (three_failure_events_bound μ E₁ E₂ E₃ q h₁ h₂ h₃)

theorem markov_event_bound_exp_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ENNReal) (E : Set Ω) (q : ℝ)
    (hYmeas : Measurable Y) (hmean : ∫⁻ ω, Y ω ∂μ ≤ 1)
    (hlarge : E ⊆ {ω | ENNReal.ofReal (Real.exp q) ≤ Y ω}) :
    μ.real E ≤ Real.exp (-q) := by
  have hε : ENNReal.ofReal (Real.exp q) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos q)
  have hbound : μ E ≤ 1 / ENNReal.ofReal (Real.exp q) := by
    calc
      μ E ≤ μ {ω | ENNReal.ofReal (Real.exp q) ≤ Y ω} := measure_mono hlarge
      _ ≤ (∫⁻ ω, Y ω ∂μ) / ENNReal.ofReal (Real.exp q) :=
        meas_ge_le_lintegral_div hYmeas.aemeasurable hε ENNReal.ofReal_ne_top
      _ ≤ 1 / ENNReal.ofReal (Real.exp q) := by gcongr
  rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos q), ← Real.exp_neg] at hbound
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa [measureReal_def, (Real.exp_pos (-q)).le] using hh

theorem canonical_maximumIndependentSupport_gamma_tail
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8)
    (H q : ℝ)
    (hcost : ∀ w ∈ s,
      α * (∑ i, (w i - 1) * fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i +
        ∑ i, (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i) ^ 2) ≤ H) :
    let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
    (gammaProductMeasure n α α).real {w | w ∈ s ∧
      H + q ≤ Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)} ≤ Real.exp (-q) := by
  classical
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
  let Y₀ : (Fin n → ℝ) → ENNReal := fun w ↦ ENNReal.ofReal
    ((17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
      (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
  let Y := s.indicator Y₀
  have htmeas := measurable_fittedLogDisplacement C hC hCcompact hCnonempty hCpos z₀
  have hkmeas := measurable_maximumIndependentSupport D hDclosed
    (fittedValueSelection C hCcompact hCnonempty hCpos)
    (canonicalFittedValue_continuousOn C hC hCcompact hCnonempty hCpos)
  have hY₀meas : Measurable Y₀ := measurable_gammaDeterminantIntegrand
    htmeas ((hkmeas.sub_const 1).const_pow _)
  apply markov_event_bound_exp_lintegral (gammaProductMeasure n α α) Y _ q (hY₀meas.indicator hs)
  · rw [lintegral_indicator hs]
    exact canonical_maximumIndependentSupport_gamma_moment
      hα C hC hCcompact hCnonempty hCpos D hDclosed hD z₀ hs hspos ht
  · intro w hw
    rcases hw with ⟨hws, hlarge⟩
    change ENNReal.ofReal (Real.exp q) ≤ Y w
    rw [show Y w = Y₀ w from indicator_of_mem hws Y₀]
    apply ENNReal.ofReal_le_ofReal
    change Real.exp q ≤ (17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
      (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2))
    have hpow : (17 / 9 : ℝ) ^ (k w - 1) =
        Real.exp (Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 17 / 9)]
    rw [hpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc := hcost w hws
    change α * (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2) ≤ H at hc
    linarith

end ReweightedNPMLE
