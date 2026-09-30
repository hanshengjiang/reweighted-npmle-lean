import Mathlib.Probability.Moments.ComplexMGF

/-!
# Local moment-generating-function uniqueness

Mathlib proves that the complex MGF determines a finite law.  For probability
work one usually knows the real MGF only on an open interval around zero.  The
lemma below supplies that standard bridge by analytic continuation and then
restricting to the imaginary axis.
 -/

open MeasureTheory Filter Set Real Complex
open ProbabilityTheory
open scoped Topology

namespace ReweightedNPMLE

/-- Two real random variables with equal MGFs on an open interval around zero
have the same distribution. -/
theorem Measure.map_eq_of_mgf_eq_on_Ioo
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (X : Ω → ℝ) (Y : Ω' → ℝ) {l u : ℝ}
    (hl : l < 0) (hu : 0 < u)
    (hXmeas : AEMeasurable X μ) (hYmeas : AEMeasurable Y μ')
    (hXint : ∀ t ∈ Ioo l u, Integrable (fun ω ↦ Real.exp (t * X ω)) μ)
    (hYint : ∀ t ∈ Ioo l u, Integrable (fun ω ↦ Real.exp (t * Y ω)) μ')
    (hmgf : ∀ t ∈ Ioo l u, mgf X μ t = mgf Y μ' t) :
    μ.map X = μ'.map Y := by
  let strip : Set ℂ := {z | z.re ∈ Ioo l u}
  have hXsubset : Ioo l u ⊆ integrableExpSet X μ := by
    intro t ht
    exact hXint t ht
  have hYsubset : Ioo l u ⊆ integrableExpSet Y μ' := by
    intro t ht
    exact hYint t ht
  have hXinterior : Ioo l u ⊆ interior (integrableExpSet X μ) :=
    interior_maximal hXsubset isOpen_Ioo
  have hYinterior : Ioo l u ⊆ interior (integrableExpSet Y μ') :=
    interior_maximal hYsubset isOpen_Ioo
  have hXanalytic : AnalyticOnNhd ℂ (complexMGF X μ) strip := by
    apply analyticOnNhd_complexMGF.mono
    intro z hz
    exact hXinterior hz
  have hYanalytic : AnalyticOnNhd ℂ (complexMGF Y μ') strip := by
    apply analyticOnNhd_complexMGF.mono
    intro z hz
    exact hYinterior hz
  have hreal : ∃ᶠ (x : ℝ) in 𝓝[≠] 0,
      complexMGF X μ x = complexMGF Y μ' x := by
    have hnear : ∀ᶠ x : ℝ in 𝓝[≠] 0, x ∈ Ioo l u :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hl hu)
    apply hnear.frequently.mono
    intro x hx
    simpa only [complexMGF_ofReal] using
      congrArg (fun r : ℝ ↦ (r : ℂ)) (hmgf x hx)
  have hcomplex : ∃ᶠ (z : ℂ) in 𝓝[≠] 0,
      complexMGF X μ z = complexMGF Y μ' z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hreal
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hxs ⊢
      constructor
      · simpa using (Complex.continuous_ofReal.tendsto 0).comp hxs.1
      · simpa using hxs.2
    · simpa using heq n
  have hzero : (0 : ℂ) ∈ strip := by
    exact ⟨hl, hu⟩
  have hEqOn : Set.EqOn (complexMGF X μ) (complexMGF Y μ') strip :=
    hXanalytic.eqOn_of_preconnected_of_frequently_eq hYanalytic
      ((convex_Ioo l u).linear_preimage reLm).isPreconnected hzero hcomplex
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hXmeas t, ← complexMGF_mul_I hYmeas t]
  apply hEqOn
  change (((t : ℂ) * I).re ∈ Ioo l u)
  simpa using And.intro hl hu

end ReweightedNPMLE
