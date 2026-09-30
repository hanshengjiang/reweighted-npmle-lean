import ReweightedNPMLE.GaussianJointTheorems
import Mathlib.Tactic

/-! # Joint arbitrarily-small perturbations

The failure event quantifies over all probability laws, so the joint theorem
requires neither a chosen optimizer nor a data-dependent measurable selection.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

def gaussianTinyStructuralFailure {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (R a : ℝ) : Set (GaussianDataWeight d n) :=
  {p | ¬((∀ i, |p.2 i - 1| ≤ a) ∧ p.2 ∈ positiveVectors n)} ∪
  {p | ∃ μ ν : ProbabilityMeasure Θ,
    μ ∈ gaussianProbabilityOptimizerSet θ p ∧ ν ∈ gaussianProbabilityOptimizerSet θ p ∧ μ ≠ ν} ∪
  {p | ∃ μ : ProbabilityMeasure Θ, μ ∈ gaussianProbabilityOptimizerSet θ p ∧
    ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} ∪
  {p | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
    μ.1 ∈ gaussianProbabilityOptimizerSet θ p ∧ 1 < gaussianOrdinaryLikelihoodGap θ (p, μ)}

theorem measurableSet_gaussianTinyStructuralFailure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    MeasurableSet (gaussianTinyStructuralFailure (n := n) θ R a) := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  have hcoord : MeasurableSet {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} := by
    have heq : {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | |p.2 i - 1| ≤ a} := by ext p; simp
    rw [heq]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_le
      (continuous_abs.comp (((continuous_apply i).comp continuous_snd).sub continuous_const)).measurable
      measurable_const)
  have hpos : MeasurableSet {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} := by
    have heq : {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | 0 < p.2 i} := by ext p; simp [positiveVectors]
    rw [heq]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const
      ((measurable_pi_apply i).comp measurable_snd))
  have hgap : MeasurableSet {p : GaussianDataWeight d n |
      ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
        μ.1 ∈ gaussianProbabilityOptimizerSet θ p ∧ 1 < gaussianOrdinaryLikelihoodGap θ (p, μ)} := by
    let T : Set (GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :=
      {p | p.2.1 ∈ gaussianProbabilityOptimizerSet θ p.1}
    have hT : IsClosed T := (isClosed_compactOptimizerGraph _
      (continuous_gaussianProbabilityLogLikelihood θ hθ)).preimage
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have h := measurableSet_exists_closed_relation_strict_gap T hT
      (fun p ↦ gaussianOrdinaryLikelihoodGap θ p - 1)
      ((continuous_gaussianOrdinaryLikelihoodGap θ hθ).sub continuous_const)
    simpa only [T, mem_setOf_eq, sub_pos] using h
  exact (((hcoord.inter hpos).compl.union (measurableSet_gaussian_optimizer_nonunique θ hθ)).union
    (measurableSet_gaussian_optimizer_support_failure θ hθ hR)).union hgap

theorem notMem_gaussianTinyStructuralFailure_of_unique_nearMLE {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {d n : ℕ}
    (θ : Θ → Point d) (x : Fin n → Point d) (w : Fin n → ℝ) (R a : ℝ)
    (hcoord : ∀ i, |w i - 1| ≤ a) (hpos : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (huniq : gaussianProbabilityOptimizerSet θ (x, w) = {μ})
    (hfinite : (μ : Measure Θ).support.Finite) (hcard : ((μ : Measure Θ).support.ncard : ℝ) ≤ R)
    (hnear : ∀ ν : ProbabilityMeasure Θ,
      gaussianProbabilityLogLikelihood θ ((x, 1), ν) - 1 ≤
        gaussianProbabilityLogLikelihood θ ((x, 1), μ)) :
    (x, w) ∉ gaussianTinyStructuralFailure θ R a := by
  intro hbad
  simp only [gaussianTinyStructuralFailure, mem_union, mem_setOf_eq] at hbad
  rcases hbad with ((hweight | hnonunique) | hsupport) | hgap
  · exact hweight ⟨hcoord, hpos⟩
  · obtain ⟨μ₁, μ₂, h₁, h₂, hne⟩ := hnonunique
    rw [huniq, mem_singleton_iff] at h₁ h₂
    exact hne (h₁.trans h₂.symm)
  · obtain ⟨ν, hν, hfail⟩ := hsupport
    rw [huniq, mem_singleton_iff] at hν
    subst ν
    exact hfail ⟨hfinite, hcard⟩
  · obtain ⟨⟨ν, ρ⟩, hν, hfail⟩ := hgap
    rw [huniq, mem_singleton_iff] at hν
    change ν = μ at hν
    subst ν
    have hh := hnear ρ
    change 1 < gaussianProbabilityLogLikelihood θ ((x, 1), ρ) -
      gaussianProbabilityLogLikelihood θ ((x, 1), μ) at hfail
    linarith

theorem gaussian_tiny_conclusions_of_notMem_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (R a : ℝ)
    (hgood : (x, w) ∉ gaussianTinyStructuralFailure θ R a) :
    (∀ i, |w i - 1| ≤ a) ∧ w ∈ positiveVectors n ∧
    ∃ μ : ProbabilityMeasure Θ, gaussianProbabilityOptimizerSet θ (x, w) = {μ} ∧
      (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R ∧
      ∀ ν : ProbabilityMeasure Θ,
        gaussianProbabilityLogLikelihood θ ((x, 1), ν) - 1 ≤
          gaussianProbabilityLogLikelihood θ ((x, 1), μ) := by
  classical
  simp only [gaussianTinyStructuralFailure, mem_union, mem_setOf_eq, not_or] at hgood
  obtain ⟨⟨⟨hweight, hnonunique⟩, hsupport⟩, hgap⟩ := hgood
  have hw := not_not.mp hweight
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit := gaussianCanonicalFit_isMax x θ hθ w
  obtain ⟨μ, hμ⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA
    (gaussianCanonicalFit x θ hθ w) hfit.1
  have hopt : μ ∈ gaussianProbabilityOptimizerSet θ (x, w) :=
    (gaussian_probability_optimizer_iff_score_fiber x θ hθ w _ hw.2 hfit μ).mpr hμ
  have huniq : ∀ ν ∈ gaussianProbabilityOptimizerSet θ (x, w), ν = μ := by
    intro ν hν
    by_contra hne
    exact hnonunique ⟨ν, μ, hν, hopt, hne⟩
  have hs : (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R := by
    by_contra hbad
    exact hsupport ⟨μ, hopt, hbad⟩
  refine ⟨hw.1, hw.2, μ, ?_, hs.1, hs.2, ?_⟩
  · ext ν
    simp only [mem_singleton_iff]
    exact ⟨fun hν ↦ huniq ν hν, fun hν ↦ hν ▸ hopt⟩
  · intro ν
    have hle : gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, ν)) ≤ 1 :=
      le_of_not_gt (fun h ↦ hgap ⟨(μ, ν), hopt, h⟩)
    change gaussianProbabilityLogLikelihood θ ((x, 1), ν) -
      gaussianProbabilityLogLikelihood θ ((x, 1), μ) ≤ 1 at hle
    linarith

/-- Arbitrarily inverse-polynomially small perturbations, with uniqueness,
polylogarithmic finite support, and global Hellinger risk on one joint event. -/
theorem gaussian_exact_regularization_joint_tiny_explicit
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b L : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hL : 0 < L)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n ((n : ℝ) ^ (2 * L + 2))).real Gᶜ ≤
          (4 * (d : ℝ) + 5) * (n : ℝ) ^ (-(b + 2)) ∧
        ∀ p ∈ G, (∀ i, |p.2 i - 1| ≤ (n : ℝ) ^ (-L)) ∧ p.2 ∈ positiveVectors n ∧
          ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              gaussianPaperSupportConstant d (8 * (2 * L + 6)) b *
                gaussianPaperAugmentedDimension d n ∧
            hellingerSq volume (compactGaussianMixtureDensity μ)
              (compactGaussianMixtureDensity Gstar) ≤
                gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d * Real.log n / n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : Nonempty K := hKnonempty.to_subtype
  let θ := fun a : K ↦ (a : Point d)
  have hθ : Continuous θ := continuous_subtype_val
  have hθbound : ∀ a : K, ‖θ a‖ ≤ S := fun a ↦ hKbound a.val a.property
  filter_upwards [gaussian_exact_regularization_conditional_tiny d hS hb hL θ hθ
      Subtype.val_injective hθbound,
    compactGaussianMixture_measurable_uniform_nearMLE_event hd K hKcompact hKnonempty hS hb hKbound,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with n hcond hrisk hdim hlog hn
  intro Gstar
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let P := compactGaussianSampleMeasure Gstar n
  let α := (n : ℝ) ^ (2 * L + 2)
  have hα : 0 < α := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
    infer_instance
  let E : Set (GaussianDataWeight d n) := gaussianTinyStructuralFailure θ
    (gaussianPaperSupportConstant d (8 * (2 * L + 6)) b * gaussianPaperAugmentedDimension d n)
    ((n : ℝ) ^ (-L))
  have hE : MeasurableSet E := measurableSet_gaussianTinyStructuralFailure θ hθ
    (by unfold gaussianPaperSupportConstant; positivity) _
  obtain ⟨X, hX, hnull, hcond⟩ := hcond
  let D := Xᶜ ∪ {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
  have hrad : MeasurableSet {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} := by
    have heq : {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} =
        ⋃ i : Fin n, {x : Fin n → Point d | gaussianPaperSampleRadius d S b n < ‖x i‖} := by ext x; simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const
      ((continuous_apply i).norm.measurable))
  have hD : MeasurableSet D := hX.compl.union hrad
  have hXzero : P.real Xᶜ = 0 := by
    change ((compactGaussianSampleMeasure Gstar n) Xᶜ).toReal = 0
    rw [compactGaussianSampleMeasure_absolutelyContinuous Gstar n hnull, ENNReal.toReal_zero]
  have hDprob : P.real D ≤ (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
    have h := measureReal_union_le (μ := P) Xᶜ {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
    rw [hXzero, zero_add] at h
    exact h.trans (compactGaussianSampleMeasure_paper_radius_tail Gstar hS hb hKbound hlog hn)
  have hsections : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ 3 * (n : ℝ) ^ (-(b + 2)) := by
    intro x hx
    have hxX : x ∈ X := by
      by_contra h
      exact hx (Or.inl h)
    have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n := by
      intro i
      by_contra h
      exact hx (Or.inr ⟨i, lt_of_not_ge h⟩)
    obtain ⟨H, hH, hHprob, hgood⟩ := hcond x hxX hxrad
    apply le_trans (measureReal_mono (μ := Q) (s₂ := Hᶜ) ?_) hHprob
    intro w hw
    by_contra hwH
    obtain ⟨hcoord, hwpos, μ, huniq, hfinite, hcard, hnear⟩ := hgood w (not_not.mp hwH)
    exact notMem_gaussianTinyStructuralFailure_of_unique_nearMLE θ x w _ _ hcoord hwpos
      μ huniq hfinite hcard hnear hw
  have hEprob : (P.prod Q).real E ≤ (2 * (d : ℝ) + 4) * (n : ℝ) ^ (-(b + 2)) := by
    have h := measureReal_prod_le_of_uniform_section_bound P Q E hE D hD
      (show 0 ≤ 3 * (n : ℝ) ^ (-(b + 2)) by positivity) hsections
    exact h.trans (by linarith)
  obtain ⟨N, hN, hNprob, hNgood⟩ := hrisk Gstar
  refine ⟨(E ∪ (N ×ˢ univ))ᶜ, (hE.union (hN.prod MeasurableSet.univ)).compl, ?_, ?_⟩
  · simp only [compl_compl]
    have hNprod : (P.prod Q).real (N ×ˢ univ) = P.real N := by simp
    have h := measureReal_union_le (μ := P.prod Q) E (N ×ˢ univ)
    rw [hNprod] at h
    exact h.trans (by linarith)
  · intro p hp
    have hpE : p ∉ E := fun h ↦ hp (Or.inl h)
    have hpN : p.1 ∉ N := fun h ↦ hp (Or.inr ⟨h, mem_univ _⟩)
    obtain ⟨hcoord, hpos, μ, huniq, hfinite, hcard, hnear⟩ :=
      gaussian_tiny_conclusions_of_notMem_failure θ hθ p.1 p.2 _ _ hpE
    refine ⟨hcoord, hpos, μ, huniq, hfinite, hcard, ?_⟩
    have hh := hnear Gstar
    rw [gaussianProbabilityLogLikelihood_one, gaussianProbabilityLogLikelihood_one] at hh
    exact hNgood p.1 hpN μ hh

end ReweightedNPMLE
