import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import ReweightedNPMLE.GaussianRadius
import ReweightedNPMLE.Hellinger

/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace ReweightedNPMLE

/-- A compatible metric realizing weak convergence on bundled probability
measures.  This local instance is used only to state convergence in
probability via mathlib's `TendstoInMeasure`. -/
noncomputable local instance {d : ℕ} {K : Set (Point d)} :
    MetricSpace (ProbabilityMeasure K) :=
  TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure K)

/-- The generative Gaussian-mixture law is convolution of the location law
with the standard Gaussian law. -/
theorem gaussianLocationMixtureLaw_id_eq_convolution
    {d : ℕ} (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    gaussianLocationMixtureLaw μ id =
      (μ.prod (stdGaussian (Point d))).map (fun p ↦ p.1 + p.2) := by
  let γd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  rw [gaussianLocationMixtureLaw]
  change (μ.prod γd).map (fun q ↦ q.1 + WithLp.toLp 2 q.2) = _
  rw [show (μ.prod γd).map (fun q ↦ q.1 + WithLp.toLp 2 q.2) =
      ((μ.prod γd).map (Prod.map id (WithLp.toLp 2))).map
        (fun p ↦ p.1 + p.2) by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl]
  rw [← Measure.map_prod_map μ γd measurable_id (by fun_prop),
    Measure.map_id, ProbabilityTheory.map_pi_eq_stdGaussian]

/-- Convolution with a standard Gaussian determines the location law. -/
theorem gaussianLocationMixtureLaw_injective
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : gaussianLocationMixtureLaw μ id =
      gaussianLocationMixtureLaw ν id) : μ = ν := by
  rw [gaussianLocationMixtureLaw_id_eq_convolution μ,
    gaussianLocationMixtureLaw_id_eq_convolution ν] at h
  have hchar := congrArg charFun h
  rw [charFun_map_add_prod_eq_mul, charFun_map_add_prod_eq_mul] at hchar
  apply Measure.ext_of_charFun
  funext t
  have ht := congrFun hchar t
  simp only [Pi.mul_apply] at ht
  exact mul_right_cancel₀ (by
    rw [charFun_stdGaussian]
    exact Complex.exp_ne_zero _) ht

/-- Two probability mixing laws with almost-everywhere equal Gaussian
location-mixture densities are equal. -/
theorem gaussianMixture_identifiable_of_ae_eq
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : gaussianMixture μ id =ᵐ[volume] gaussianMixture ν id) : μ = ν := by
  apply gaussianLocationMixtureLaw_injective μ ν
  rw [gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
      μ id measurable_id,
    gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
      ν id measurable_id]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Vanishing squared Hellinger distance between two Gaussian-mixture
densities identifies their mixing laws. -/
theorem gaussianMixture_identifiable_of_hellingerSq_eq_zero
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : hellingerSq volume (gaussianMixture μ id)
      (gaussianMixture ν id) = 0) : μ = ν := by
  apply gaussianMixture_identifiable_of_ae_eq μ ν
  exact (hellingerSq_eq_zero_iff_ae_eq volume
    (gaussianMixture μ id) (gaussianMixture ν id)
    (measurable_gaussianMixture μ id measurable_id).aestronglyMeasurable
    (measurable_gaussianMixture ν id measurable_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (gaussianMixture_pos μ id measurable_id x).le)
    (Filter.Eventually.of_forall fun x ↦ (gaussianMixture_pos ν id measurable_id x).le)
    (gaussianMixture_integrable μ id measurable_id)
    (gaussianMixture_integrable ν id measurable_id)).mp h

/-- Identifiability is invariant under a measurable embedding of the mixing
parameter space into Euclidean location space. -/
theorem gaussianMixture_identifiable_of_measurableEmbedding
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : Measure Θ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (θ : Θ → Point d) (hθ : MeasurableEmbedding θ)
    (h : gaussianMixture μ θ =ᵐ[volume] gaussianMixture ν θ) : μ = ν := by
  have hdensity (ρ : Measure Θ) [IsProbabilityMeasure ρ] :
      gaussianMixture (ρ.map θ) id = gaussianMixture ρ θ := by
    funext x
    unfold gaussianMixture
    rw [hθ.integral_map]
    rfl
  letI : IsProbabilityMeasure (μ.map θ) :=
    Measure.isProbabilityMeasure_map hθ.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map θ) :=
    Measure.isProbabilityMeasure_map hθ.measurable.aemeasurable
  have hmap : μ.map θ = ν.map θ := by
    apply gaussianMixture_identifiable_of_ae_eq
    rw [hdensity μ, hdensity ν]
    exact h
  exact hθ.map_injective hmap

/-- Weak convergence of compactly supported mixing laws implies pointwise
convergence of their Gaussian-mixture densities. -/
theorem tendsto_gaussianMixture_eval_of_tendsto_probabilityMeasure
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    {ι : Type*} {F : Filter ι}
    {Gs : ι → ProbabilityMeasure K} {G : ProbabilityMeasure K}
    (hG : Tendsto Gs F (𝓝 G)) (x : Point d) :
    Tendsto (fun i ↦ gaussianMixture (Gs i : Measure K)
        (fun θ : K ↦ (θ : Point d)) x) F
      (𝓝 (gaussianMixture (G : Measure K)
        (fun θ : K ↦ (θ : Point d)) x)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let f : C(K, ℝ) :=
    ⟨fun θ ↦ gaussianKernel d x (θ : Point d), by
      unfold gaussianKernel
      fun_prop⟩
  let fb : K →ᵇ ℝ := ContinuousMap.equivBoundedOfCompact K ℝ f
  have ht :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hG) fb
  simpa only [gaussianMixture, fb, f,
    ContinuousMap.equivBoundedOfCompact_apply] using ht

/-- On a compact location set, convergence of Gaussian-mixture densities in
squared Hellinger distance forces weak convergence of the mixing laws.  This
is the consistency bridge used after the paper's risk bound. -/
theorem tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gs : ℕ → ProbabilityMeasure K) (Gstar : ProbabilityMeasure K)
    (hhell : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs n : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))))
      atTop (𝓝 0)) :
    Tendsto Gs atTop (𝓝 Gstar) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let θ : K → Point d := fun z ↦ (z : Point d)
  have hθmeas : Measurable θ := measurable_subtype_coe
  have hθemb : MeasurableEmbedding θ :=
    MeasurableEmbedding.subtype_coe hKcompact.measurableSet
  refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun n ↦ Set.mem_univ (Gs n)) ?_
  intro G _ hGcluster
  rcases hGcluster.tendsto_subseq with ⟨φ, hφmono, hφ⟩
  have hscheffe : Tendsto (fun n ↦ ∫ x,
        |gaussianMixture (Gs (φ n) : Measure K) θ x -
          gaussianMixture (G : Measure K) θ x|)
      atTop (𝓝 0) := by
    apply tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
    · intro n
      exact (measurable_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas).aestronglyMeasurable
    · exact (measurable_gaussianMixture (G : Measure K) θ hθmeas).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun x ↦
        (gaussianMixture_pos (Gs (φ n) : Measure K) θ hθmeas x).le
    · exact Filter.Eventually.of_forall fun x ↦
        (gaussianMixture_pos (G : Measure K) θ hθmeas x).le
    · intro n
      exact gaussianMixture_integrable (Gs (φ n) : Measure K) θ hθmeas
    · exact gaussianMixture_integrable (G : Measure K) θ hθmeas
    · intro n
      exact integral_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas
    · exact integral_gaussianMixture (G : Measure K) θ hθmeas
    · exact Filter.Eventually.of_forall fun x ↦
        tendsto_gaussianMixture_eval_of_tendsto_probabilityMeasure
          hKcompact hφ x
  have hhellsub : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs (φ n) : Measure K) θ)
        (gaussianMixture (Gstar : Measure K) θ)) atTop (𝓝 0) := by
    simpa only [θ, Function.comp_apply] using hhell.comp hφmono.tendsto_atTop
  have hupper : Tendsto (fun n ↦ 2 * Real.sqrt (hellingerSq volume
        (gaussianMixture (Gs (φ n) : Measure K) θ)
        (gaussianMixture (Gstar : Measure K) θ))) atTop (𝓝 0) := by
    have hsqrt := hhellsub.sqrt
    simpa using hsqrt.const_mul 2
  have hl1star : Tendsto (fun n ↦ ∫ x,
        |gaussianMixture (Gs (φ n) : Measure K) θ x -
          gaussianMixture (Gstar : Measure K) θ x|)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact integral_nonneg fun x ↦ abs_nonneg _
    · intro n
      exact integral_abs_sub_le_two_mul_sqrt_hellingerSq volume
        (gaussianMixture (Gs (φ n) : Measure K) θ)
        (gaussianMixture (Gstar : Measure K) θ)
        (measurable_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas).aestronglyMeasurable
        (measurable_gaussianMixture (Gstar : Measure K) θ hθmeas).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦
          (gaussianMixture_pos (Gs (φ n) : Measure K) θ hθmeas x).le)
        (Filter.Eventually.of_forall fun x ↦
          (gaussianMixture_pos (Gstar : Measure K) θ hθmeas x).le)
        (gaussianMixture_integrable (Gs (φ n) : Measure K) θ hθmeas)
        (gaussianMixture_integrable (Gstar : Measure K) θ hθmeas)
        (integral_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas)
        (integral_gaussianMixture (Gstar : Measure K) θ hθmeas)
    · exact hupper
  let c : ℝ := ∫ x,
    |gaussianMixture (G : Measure K) θ x -
      gaussianMixture (Gstar : Measure K) θ x|
  have htri : ∀ n, c ≤
      (∫ x, |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gs (φ n) : Measure K) θ x|) +
      ∫ x, |gaussianMixture (Gs (φ n) : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x| := by
    intro n
    have hGint := gaussianMixture_integrable (G : Measure K) θ hθmeas
    have hnint := gaussianMixture_integrable (Gs (φ n) : Measure K) θ hθmeas
    have hstarint := gaussianMixture_integrable (Gstar : Measure K) θ hθmeas
    have hleft := abs_sub_integrable_of_integrable volume
      (gaussianMixture (G : Measure K) θ)
      (gaussianMixture (Gstar : Measure K) θ) hGint hstarint
    have hfirst := abs_sub_integrable_of_integrable volume
      (gaussianMixture (G : Measure K) θ)
      (gaussianMixture (Gs (φ n) : Measure K) θ) hGint hnint
    have hsecond := abs_sub_integrable_of_integrable volume
      (gaussianMixture (Gs (φ n) : Measure K) θ)
      (gaussianMixture (Gstar : Measure K) θ) hnint hstarint
    calc
      c ≤ ∫ x, |gaussianMixture (G : Measure K) θ x -
          gaussianMixture (Gs (φ n) : Measure K) θ x| +
          |gaussianMixture (Gs (φ n) : Measure K) θ x -
            gaussianMixture (Gstar : Measure K) θ x| := by
        dsimp [c]
        apply integral_mono_ae hleft (hfirst.add hsecond)
        exact Filter.Eventually.of_forall fun x ↦ by
          calc
            |gaussianMixture (G : Measure K) θ x -
                gaussianMixture (Gstar : Measure K) θ x| =
              |(gaussianMixture (G : Measure K) θ x -
                  gaussianMixture (Gs (φ n) : Measure K) θ x) +
                (gaussianMixture (Gs (φ n) : Measure K) θ x -
                  gaussianMixture (Gstar : Measure K) θ x)| := by congr 1 <;> ring
            _ ≤ _ := abs_add_le _ _
      _ = (∫ x, |gaussianMixture (G : Measure K) θ x -
            gaussianMixture (Gs (φ n) : Measure K) θ x|) +
          ∫ x, |gaussianMixture (Gs (φ n) : Measure K) θ x -
            gaussianMixture (Gstar : Measure K) θ x| :=
        integral_add hfirst hsecond
  have hsum : Tendsto (fun n ↦
      (∫ x, |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gs (φ n) : Measure K) θ x|) +
      ∫ x, |gaussianMixture (Gs (φ n) : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x|) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun n ↦ ∫ x,
        |gaussianMixture (G : Measure K) θ x -
          gaussianMixture (Gs (φ n) : Measure K) θ x|) atTop (𝓝 0) := by
      simpa only [abs_sub_comm] using hscheffe
    simpa using hfirst.add hl1star
  have hcle : c ≤ 0 := ge_of_tendsto hsum (Filter.Eventually.of_forall htri)
  have hcge : 0 ≤ c := by
    dsimp [c]
    exact integral_nonneg fun x ↦ abs_nonneg _
  have hc : c = 0 := le_antisymm hcle hcge
  have hdiffint : Integrable (fun x ↦
      |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x|) volume :=
    abs_sub_integrable_of_integrable volume
      (gaussianMixture (G : Measure K) θ)
      (gaussianMixture (Gstar : Measure K) θ)
      (gaussianMixture_integrable (G : Measure K) θ hθmeas)
      (gaussianMixture_integrable (Gstar : Measure K) θ hθmeas)
  have habs : (fun x ↦
      |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x|) =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hdiffint).mp
    exact hc
  have hae : gaussianMixture (G : Measure K) θ =ᵐ[volume]
      gaussianMixture (Gstar : Measure K) θ := by
    filter_upwards [habs] with x hx
    simpa only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] using hx
  apply ProbabilityMeasure.toMeasure_injective
  exact gaussianMixture_identifiable_of_measurableEmbedding
    (G : Measure K) (Gstar : Measure K) θ hθemb hae

/-- Uniform topological inverse at the true mixing law: every weak
neighborhood contains a sufficiently small squared-Hellinger ball of
Gaussian-mixture densities.  Compactness and identifiability are essential. -/
theorem exists_hellingerSq_ball_subset_probabilityMeasure_nhds
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gstar : ProbabilityMeasure K) {U : Set (ProbabilityMeasure K)}
    (hU : U ∈ 𝓝 Gstar) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : ProbabilityMeasure K,
      hellingerSq volume
          (gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d)))
          (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))) < δ →
        G ∈ U := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hchoice : ∀ n : ℕ, ∃ G : ProbabilityMeasure K,
      hellingerSq volume
          (gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d)))
          (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))) <
        1 / ((n : ℝ) + 1) ∧ G ∉ U := by
    intro n
    exact hcontra (1 / ((n : ℝ) + 1)) (by positivity)
  choose Gs hsmall hout using hchoice
  have hhell : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs n : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))))
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact hellingerSq_nonneg volume _ _
    · intro n
      exact (hsmall n).le
    · simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hGs :=
    tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
      hKcompact Gs Gstar hhell
  have hboth : ∀ᶠ n in atTop, Gs n ∈ U ∧ Gs n ∉ U := by
    filter_upwards [hGs hU] with n hn
    exact ⟨hn, hout n⟩
  rcases hboth.exists with ⟨n, hn, hnout⟩
  exact hnout hn

/-- Weak consistency in probability, in the exact subsequence form used by
the paper.  Convergence in probability of squared Hellinger loss implies
convergence in probability of the compactly supported mixing law. -/
theorem tendstoInMeasure_probabilityMeasure_of_gaussianMixture_hellingerSq
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Gs : ℕ → Ω → ProbabilityMeasure K) (Gstar : ProbabilityMeasure K)
    (hGsmeas : ∀ n, AEStronglyMeasurable (Gs n) μ)
    (hhell : TendstoInMeasure μ (fun n ω ↦ hellingerSq volume
        (gaussianMixture (Gs n ω : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))))
      atTop 0) :
    TendstoInMeasure μ Gs atTop (fun _ ↦ Gstar) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  apply (exists_seq_tendstoInMeasure_atTop_iff hGsmeas).2
  intro ns hns
  have hsub := hhell.comp hns.tendsto_atTop
  rcases hsub.exists_seq_tendsto_ae with ⟨ns', hns', hae⟩
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with ω hω
  apply tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
    hKcompact (fun i ↦ Gs (ns (ns' i)) ω) Gstar
  simpa only [Function.comp_apply, Pi.zero_apply] using hω

/-- Weak consistency in probability for a triangular sequence of experiments.
The sample space may vary with `n` (as it does for `Fin n → Point d`).  The
conclusion is expressed intrinsically: the probability of leaving any weak
neighborhood of `Gstar` tends to zero. -/
theorem gaussianMixture_weak_consistency_of_hellingerSq_tails
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gstar : ProbabilityMeasure K)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (Ghat : ∀ n, Ω n → ProbabilityMeasure K)
    (hhell : ∀ δ : ℝ, 0 < δ → Tendsto (fun n ↦ (μ n).real
      {ω | δ ≤ hellingerSq volume
        (gaussianMixture (Ghat n ω : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d)))})
      atTop (𝓝 0)) :
    ∀ U ∈ 𝓝 Gstar,
      Tendsto (fun n ↦ (μ n).real {ω | Ghat n ω ∉ U}) atTop (𝓝 0) := by
  intro U hU
  obtain ⟨δ, hδ, hδU⟩ :=
    exists_hellingerSq_ball_subset_probabilityMeasure_nhds
      hKcompact Gstar hU
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (hhell δ hδ)
  ·
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change Ghat n ω ∉ U at hω
    change δ ≤ hellingerSq volume
      (gaussianMixture (Ghat n ω : Measure K) (fun θ : K ↦ (θ : Point d)))
      (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d)))
    exact not_lt.mp (fun hlt ↦ hω (hδU (Ghat n ω) hlt))

end ReweightedNPMLE
