import ReweightedNPMLE.GaussianMixtureNet
import ReweightedNPMLE.SimplexGrid
import ReweightedNPMLE.EuclideanLocationNet
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Finite Gaussian-mixture grids

This module combines a finite location set with the denominator simplex grid.
It produces an actual finite set of Gaussian-mixture densities, proves the
entropy count used in the likelihood-net argument, and packages the local
log-density and global Hellinger rounding estimates for members of that set.
-/

open scoped BigOperators
open MeasureTheory

namespace ReweightedNPMLE

/-- A finite internal cover set supplied by compactness. -/
noncomputable def compactLocationCoverSet {d : ℕ} (K : Set (Point d))
    (hKcompact : IsCompact K) (ε : ℝ) (hε : 0 < ε) : Set (Point d) :=
  (hKcompact.finite_cover_balls hε).choose

theorem compactLocationCoverSet_subset {d : ℕ} (K : Set (Point d))
    (hKcompact : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    compactLocationCoverSet K hKcompact ε hε ⊆ K :=
  (hKcompact.finite_cover_balls hε).choose_spec.1

theorem compactLocationCoverSet_finite {d : ℕ} (K : Set (Point d))
    (hKcompact : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    (compactLocationCoverSet K hKcompact ε hε).Finite :=
  (hKcompact.finite_cover_balls hε).choose_spec.2.1

/-- A concrete finite set of locations inside a compact parameter set. -/
noncomputable def compactLocationNet {d : ℕ} (K : Set (Point d))
    (hKcompact : IsCompact K) (ε : ℝ) (hε : 0 < ε) : Finset (Point d) :=
  (compactLocationCoverSet_finite K hKcompact ε hε).toFinset

theorem compactLocationNet_subset {d : ℕ} (K : Set (Point d))
    (hKcompact : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ↑(compactLocationNet K hKcompact ε hε) ⊆ K := by
  simpa [compactLocationNet] using
    (compactLocationCoverSet_subset K hKcompact ε hε)

/-- Every point of the compact set is strictly within `ε` of a point of the
finite internal location net. -/
theorem exists_mem_compactLocationNet_dist_lt {d : ℕ} (K : Set (Point d))
    (hKcompact : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    {θ : Point d} (hθ : θ ∈ K) :
    ∃ η ∈ compactLocationNet K hKcompact ε hε, dist θ η < ε := by
  have hcover := (hKcompact.finite_cover_balls hε).choose_spec.2.2 hθ
  change θ ∈ ⋃ x ∈ compactLocationCoverSet K hKcompact ε hε,
      Metric.ball x ε at hcover
  rcases Set.mem_iUnion.mp hcover with ⟨η, hcover⟩
  rcases Set.mem_iUnion.mp hcover with ⟨hη, hθη⟩
  refine ⟨η, ?_, ?_⟩
  · simpa [compactLocationNet] using hη
  · simpa [Metric.mem_ball, dist_comm] using hθη

/-- Number of free nonconstant moments in the order-`2L` Carathéodory
construction. -/
noncomputable abbrev gaussianMomentDimension (d L : ℕ) : ℕ :=
  Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ)

/-- Global squared-Hellinger error of the order-`2L` moment-matched mixture. -/
noncomputable def gaussianMomentHellingerError (S : ℝ) (L : ℕ) : ℝ :=
  (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
    (2 * L + 1).factorial)) ^ (1 / 2 : ℝ)

/-- Local relative-density error of the order-`L` moment approximation. -/
noncomputable def gaussianMomentRelativeError (T S : ℝ) (L : ℕ) : ℝ :=
  2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
    ((T * S + S ^ 2 / 2) ^ (L + 1) / (L + 1).factorial)

/-- All `(k+1)`-component Gaussian mixtures whose locations belong to `Q`
and whose weights belong to the valid denominator-`M` simplex grid. -/
noncomputable def finiteGaussianMixtureGrid (d k M : ℕ)
    (Q : Finset (Point d)) : Finset (Point d → ℝ) := by
  classical
  exact ((Finset.univ : Finset (Fin (k + 1) → Q)).product
        (validSimplexWeightGrid k M)).image fun z ↦
      finiteGaussianMixture z.2 (fun i ↦ (z.1 i : Point d))

/-- Cartesian counting gives the explicit entropy bound for the finite
mixture grid. -/
theorem card_finiteGaussianMixtureGrid_le (d k M : ℕ)
    (Q : Finset (Point d)) :
    (finiteGaussianMixtureGrid d k M Q).card ≤
      Q.card ^ (k + 1) * (M + 1) ^ k := by
  classical
  calc
    (finiteGaussianMixtureGrid d k M Q).card ≤
        (((Finset.univ : Finset (Fin (k + 1) → Q)).product
          (validSimplexWeightGrid k M)).card) := by
      exact Finset.card_image_le
    _ = Q.card ^ (k + 1) * (validSimplexWeightGrid k M).card := by
      simp
    _ ≤ Q.card ^ (k + 1) * (M + 1) ^ k :=
      Nat.mul_le_mul_left _ (card_validSimplexWeightGrid_le k M)

/-- Fully explicit entropy count when the location set is the coordinate-cell
net of a bounded set. -/
theorem card_finiteGaussianMixtureGrid_boundedLocationNet_le
    {d : ℕ} (k M : ℕ) (K : Set (Point d))
    (hKnonempty : K.Nonempty) {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    (finiteGaussianMixtureGrid d k M
      (boundedLocationNet K hKnonempty S ε hε hKbound)).card ≤
        ((boundedLocationCellCount d S ε) ^ d) ^ (k + 1) *
          (M + 1) ^ k := by
  calc
    (finiteGaussianMixtureGrid d k M
      (boundedLocationNet K hKnonempty S ε hε hKbound)).card ≤
        (boundedLocationNet K hKnonempty S ε hε hKbound).card ^ (k + 1) *
          (M + 1) ^ k :=
      card_finiteGaussianMixtureGrid_le d k M _
    _ ≤ ((boundedLocationCellCount d S ε) ^ d) ^ (k + 1) *
          (M + 1) ^ k := by
      gcongr
      exact card_boundedLocationNet_le K hKnonempty hε hKbound

/-- Any mixture using locations from `Q` and a valid grid weight belongs to
the finite mixture grid. -/
theorem finiteGaussianMixture_mem_grid {d k M : ℕ}
    (Q : Finset (Point d)) (v : Fin (k + 1) → ℝ)
    (η : Fin (k + 1) → Point d)
    (hv : v ∈ validSimplexWeightGrid k M)
    (hη : ∀ i, η i ∈ Q) :
    finiteGaussianMixture v η ∈ finiteGaussianMixtureGrid d k M Q := by
  classical
  let z : Fin (k + 1) → Q := fun i ↦ ⟨η i, hη i⟩
  rw [finiteGaussianMixtureGrid, Finset.mem_image]
  refine ⟨(z, v), Finset.mem_product.mpr ⟨Finset.mem_univ z, hv⟩, ?_⟩
  congr

theorem mem_finiteGaussianMixtureGrid_iff {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ} :
    p ∈ finiteGaussianMixtureGrid d k M Q ↔
      ∃ (z : Fin (k + 1) → Q) (v : Fin (k + 1) → ℝ),
        v ∈ validSimplexWeightGrid k M ∧
        p = finiteGaussianMixture v (fun i ↦ (z i : Point d)) := by
  classical
  rw [finiteGaussianMixtureGrid, Finset.mem_image]
  constructor
  · rintro ⟨⟨z, v⟩, hzv, rfl⟩
    exact ⟨z, v, (Finset.mem_product.mp hzv).2, rfl⟩
  · rintro ⟨z, v, hv, rfl⟩
    exact ⟨(z, v), Finset.mem_product.mpr ⟨Finset.mem_univ z, hv⟩, rfl⟩

theorem finiteGaussianMixtureGrid_pos {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ}
    (hp : p ∈ finiteGaussianMixtureGrid d k M Q) (x : Point d) :
    0 < p x := by
  rcases (mem_finiteGaussianMixtureGrid_iff Q).mp hp with ⟨z, v, hv, rfl⟩
  exact finiteGaussianMixture_pos _
    (fun i ↦ validSimplexWeightGrid_nonneg hv i)
    (validSimplexWeightGrid_sum hv) x

theorem finiteGaussianMixtureGrid_integrable {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ}
    (hp : p ∈ finiteGaussianMixtureGrid d k M Q) :
    Integrable p := by
  rcases (mem_finiteGaussianMixtureGrid_iff Q).mp hp with ⟨z, v, _hv, rfl⟩
  exact finiteGaussianMixture_integrable v (fun i ↦ (z i : Point d))

theorem integral_finiteGaussianMixtureGrid {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ}
    (hp : p ∈ finiteGaussianMixtureGrid d k M Q) :
    ∫ x, p x = 1 := by
  rcases (mem_finiteGaussianMixtureGrid_iff Q).mp hp with ⟨z, v, hv, rfl⟩
  rw [integral_finiteGaussianMixture]
  exact validSimplexWeightGrid_sum hv

/-- Coordinatewise location rounding followed by denominator rounding of the
weights lands in the finite Gaussian-mixture grid. -/
theorem finiteGaussianMixture_rounding_mem_grid {d k M : ℕ}
    (hM : 0 < M) (Q : Finset (Point d))
    (w : Fin (k + 1) → ℝ) (η : Fin (k + 1) → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hη : ∀ i, η i ∈ Q) :
    finiteGaussianMixture (simplexGridRound k M w) η ∈
      finiteGaussianMixtureGrid d k M Q :=
  finiteGaussianMixture_mem_grid Q _ η
    (simplexGridRound_mem_validSimplexWeightGrid hM w hw hwsum) hη

/-- A member of the finite mixture grid simultaneously provides the local
log-density approximation obtained by rounding locations and weights. -/
theorem exists_finiteGaussianMixtureGrid_log_approximation
    {d k M : ℕ} (hM : 0 < M) (Q : Finset (Point d))
    (w : Fin (k + 1) → ℝ) (θ η : Fin (k + 1) → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hηQ : ∀ i, η i ∈ Q)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * k / M) ≤ 1 / 2) :
    ∃ p ∈ finiteGaussianMixtureGrid d k M Q,
      ∀ x, ‖x‖ ≤ T →
        |Real.log (p x) - Real.log (finiteGaussianMixture w θ x)| ≤
          (T + S) * ε +
            2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * (2 * k / M) := by
  let v := simplexGridRound k M w
  refine ⟨finiteGaussianMixture v η,
    finiteGaussianMixture_rounding_mem_grid hM Q w η hw hwsum hηQ, ?_⟩
  intro x hx
  have hvnonneg : ∀ i, 0 ≤ v i := simplexGridRound_nonneg hM w hw hwsum
  have hvsum : ∑ i, v i = 1 := sum_simplexGridRound w
  have hl1 : ∑ i, |v i - w i| ≤ 2 * k / M :=
    sum_abs_simplexGridRound_sub_le hM w hw hwsum
  have hsmall' : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hl1 (Real.exp_pos _).le).trans hsmall
  have hmass :
      2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| ≤
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * (2 * k / M) :=
    mul_le_mul_of_nonneg_left hl1 (by positivity)
  calc
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (finiteGaussianMixture w θ x)| ≤
        (T + S) * ε +
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| :=
      abs_log_finiteGaussianMixture_rounding_le
        w v θ η x hw hvnonneg hwsum hvsum hT hS hε hx hθ hη hθη hsmall'
    _ ≤ (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * (2 * k / M) :=
      by linarith

/-- The same rounded grid member has a global squared-Hellinger error bound. -/
theorem exists_finiteGaussianMixtureGrid_hellinger_approximation
    {d k M : ℕ} (hM : 0 < M) (Q : Finset (Point d))
    (w : Fin (k + 1) → ℝ) (θ η : Fin (k + 1) → Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hηQ : ∀ i, η i ∈ Q)
    {ε : ℝ} (hε : 0 ≤ ε) (hθη : ∀ i, ‖θ i - η i‖ ≤ ε) :
    ∃ p ∈ finiteGaussianMixtureGrid d k M Q,
      hellingerSq volume (finiteGaussianMixture w θ) p ≤
        ε ^ 2 / 2 + 2 * (2 * k / M) := by
  let v := simplexGridRound k M w
  refine ⟨finiteGaussianMixture v η,
    finiteGaussianMixture_rounding_mem_grid hM Q w η hw hwsum hηQ, ?_⟩
  have hvnonneg : ∀ i, 0 ≤ v i := simplexGridRound_nonneg hM w hw hwsum
  have hvsum : ∑ i, v i = 1 := sum_simplexGridRound w
  have hl1 : ∑ i, |w i - v i| ≤ 2 * k / M := by
    simpa only [abs_sub_comm] using
      (sum_abs_simplexGridRound_sub_le hM w hw hwsum)
  have hmass : 2 * ∑ i, |w i - v i| ≤ 2 * (2 * k / M) :=
    mul_le_mul_of_nonneg_left hl1 (by norm_num)
  exact (hellingerSq_finiteGaussianMixture_rounding
    w v θ η hw hvnonneg hwsum hvsum hε hθη).trans
      (by linarith)

/-- End-to-end deterministic finite-net theorem for a supplied finite internal
location cover.  An arbitrary compactly supported mixing law is first
replaced by a simultaneous moment-matched finite mixture, then its locations
and weights are rounded into one concrete member of the finite Gaussian-
mixture grid. -/
theorem exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
    {d L M : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d)) (Q : Finset (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hQK : ↑Q ⊆ K)
    (hQcover : ∀ u ∈ K, ∃ v ∈ Q, ‖u - v‖ ≤ ε)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2) :
    ∃ p ∈ finiteGaussianMixtureGrid d (gaussianMomentDimension d L) M Q,
      hellingerSq volume (gaussianMixture μ ϑ) p ≤
          2 * gaussianMomentHellingerError S L + ε ^ 2 +
            4 * (2 * gaussianMomentDimension d L / M) ∧
      ∀ x ∈ X,
        |Real.log (p x) - Real.log (gaussianMixture μ ϑ x)| ≤
          (T + S) * ε +
            2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
              (2 * gaussianMomentDimension d L / M) +
            2 * gaussianMomentRelativeError T S L := by
  obtain ⟨w, z, hw, hzK, hglobal0, hrelative0⟩ :=
    exists_finite_gaussianMixture_simultaneous_approximation
      μ ϑ hϑmeas K X hKcompact hKnonempty hϑK hT hS hKbound hXbound
  have hchoice : ∀ i, ∃ η ∈ Q, ‖z i - η‖ ≤ ε := by
    intro i
    exact hQcover (z i) (hzK i)
  choose η hηQ hθη using hchoice
  have hηK : ∀ i, η i ∈ K := fun i ↦ hQK (hηQ i)
  let v := simplexGridRound (gaussianMomentDimension d L) M w
  have hvnonneg : ∀ i, 0 ≤ v i :=
    simplexGridRound_nonneg hM w hw.1 hw.2
  have hvsum : ∑ i, v i = 1 := sum_simplexGridRound w
  have hl1vw : ∑ i, |v i - w i| ≤
      2 * gaussianMomentDimension d L / M :=
    sum_abs_simplexGridRound_sub_le hM w hw.1 hw.2
  have hl1wv : ∑ i, |w i - v i| ≤
      2 * gaussianMomentDimension d L / M := by
    simpa only [abs_sub_comm] using hl1vw
  refine ⟨finiteGaussianMixture v η,
    finiteGaussianMixture_rounding_mem_grid hM Q w η hw.1 hw.2 hηQ,
    ?_, ?_⟩
  · have hglobal : hellingerSq volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture w z) ≤ gaussianMomentHellingerError S L := by
      simpa only [gaussianMomentHellingerError] using hglobal0
    have hround := hellingerSq_gaussianMixture_finite_rounding_le
      μ ϑ hϑmeas w v z η hw.1 hvnonneg hw.2 hvsum hε.le hθη hglobal
    have hmass : 4 * ∑ i, |w i - v i| ≤
        4 * (2 * gaussianMomentDimension d L / M) :=
      mul_le_mul_of_nonneg_left hl1wv (by norm_num)
    exact hround.trans (by linarith)
  · intro x hxX
    have hrelative :
        |finiteGaussianMixture w z x / gaussianMixture μ ϑ x - 1| ≤
          gaussianMomentRelativeError T S L := by
      simpa only [gaussianMomentRelativeError] using hrelative0 x hxX
    have hrelativeNonneg : 0 ≤ gaussianMomentRelativeError T S L := by
      unfold gaussianMomentRelativeError
      have hB : 0 ≤ T * S + S ^ 2 / 2 := by positivity
      positivity
    have hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
        ∑ i, |v i - w i| ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hl1vw (Real.exp_pos _).le).trans hweightSmall
    have hlog := abs_log_rounded_finiteGaussianMixture_sub_gaussianMixture_le
      μ ϑ hϑmeas w v z η x hw.1 hvnonneg hw.2 hvsum
      hT hS hε.le (hXbound x hxX)
      (fun i ↦ hKbound (z i) (hzK i))
      (fun i ↦ hKbound (η i) (hηK i)) hθη hsmall
      hrelativeNonneg hrelativeHalf hrelative
    have hmass :
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| ≤
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) :=
      mul_le_mul_of_nonneg_left hl1vw (by positivity)
    exact hlog.trans (by linarith)

/-- The finite-cover theorem specialized to the internal cover supplied by
compactness. -/
theorem exists_mem_compactGaussianMixtureGrid_simultaneous_approximation
    {d L M : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2) :
    ∃ p ∈ finiteGaussianMixtureGrid d (gaussianMomentDimension d L) M
        (compactLocationNet K hKcompact ε hε),
      hellingerSq volume (gaussianMixture μ ϑ) p ≤
          2 * gaussianMomentHellingerError S L + ε ^ 2 +
            4 * (2 * gaussianMomentDimension d L / M) ∧
      ∀ x ∈ X,
        |Real.log (p x) - Real.log (gaussianMixture μ ϑ x)| ≤
          (T + S) * ε +
            2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
              (2 * gaussianMomentDimension d L / M) +
            2 * gaussianMomentRelativeError T S L := by
  apply exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
    μ ϑ hϑmeas K X (compactLocationNet K hKcompact ε hε)
    hKcompact hKnonempty hϑK hT hS hε hKbound hXbound
    (compactLocationNet_subset K hKcompact ε hε)
    _ hM hrelativeHalf hweightSmall
  intro u hu
  obtain ⟨v, hv, huv⟩ :=
    exists_mem_compactLocationNet_dist_lt K hKcompact hε hu
  exact ⟨v, hv, by simpa only [dist_eq_norm] using huv.le⟩

/-- End-to-end deterministic approximation using the explicit coordinate-cell
location net.  Both its approximation errors and grid cardinality are now
concrete functions of `d`, `S`, `ε`, `L`, and `M`. -/
theorem exists_mem_boundedGaussianMixtureGrid_simultaneous_approximation
    {d L M : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2) :
    ∃ p ∈ finiteGaussianMixtureGrid d (gaussianMomentDimension d L) M
        (boundedLocationNet K hKnonempty S ε hε hKbound),
      hellingerSq volume (gaussianMixture μ ϑ) p ≤
          2 * gaussianMomentHellingerError S L + ε ^ 2 +
            4 * (2 * gaussianMomentDimension d L / M) ∧
      ∀ x ∈ X,
        |Real.log (p x) - Real.log (gaussianMixture μ ϑ x)| ≤
          (T + S) * ε +
            2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
              (2 * gaussianMomentDimension d L / M) +
            2 * gaussianMomentRelativeError T S L := by
  exact exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
    μ ϑ hϑmeas K X
    (boundedLocationNet K hKnonempty S ε hε hKbound)
    hKcompact hKnonempty hϑK hT hS hε hKbound hXbound
    (boundedLocationNet_subset K hKnonempty hε hKbound)
    (exists_mem_boundedLocationNet_norm_sub_le K hKnonempty hε hKbound)
    hM hrelativeHalf hweightSmall

end ReweightedNPMLE
