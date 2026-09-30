import Mathlib.Topology.Maps.Proper.Basic
import ReweightedNPMLE.Weights
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Measurable parameterized optimizer events

Continuous optimization on a compact law space has a closed optimizer graph.
Compact projection and countable distance thresholds make failure of
uniqueness and strict optimizer inequalities Borel events. These results are
used to integrate conditional conclusions without assuming a measurable
choice of the conditional good sets.
-/

open Set
open scoped Topology

namespace ReweightedNPMLE

def compactOptimizerGraph {X M : Type*} (U : X × M → ℝ) : Set (X × M) :=
  {p | IsMaxOn univ (fun μ ↦ U (p.1, μ)) p.2}

theorem isClosed_compactOptimizerGraph {X M : Type*}
    [TopologicalSpace X] [TopologicalSpace M] (U : X × M → ℝ) (hU : Continuous U) :
    IsClosed (compactOptimizerGraph U) := by
  have heq : compactOptimizerGraph U = ⋂ μ : M, {p | U (p.1, μ) ≤ U p} := by
    ext p
    constructor
    · intro hp
      exact mem_iInter.mpr (fun μ ↦ hp.2 μ (mem_univ μ))
    · intro hp
      exact ⟨mem_univ p.2, fun μ _ ↦ mem_iInter.mp hp μ⟩
  rw [heq]
  exact isClosed_iInter (fun μ ↦ isClosed_le
    (hU.comp (continuous_fst.prodMk continuous_const)) hU)

/-- A positive strict gap can be detected by a natural-number threshold. -/
theorem positive_iff_exists_nat_mul_ge_one {t : ℝ} :
    0 < t ↔ ∃ j : ℕ, 1 ≤ ((j : ℝ) + 1) * t := by
  constructor
  · intro ht
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / t)
    refine ⟨j, ?_⟩
    have hle : 1 / t ≤ (j : ℝ) + 1 := by linarith
    exact (div_le_iff₀ ht).mp hle
  · rintro ⟨j, hj⟩
    by_contra ht
    have hnonpos : t ≤ 0 := not_lt.mp ht
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (j : ℝ) + 1 by positivity) hnonpos
    linarith

theorem measurableSet_compactOptimizer_nonunique {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace M] [CompactSpace M]
    (U : X × M → ℝ) (hU : Continuous U) :
    MeasurableSet {x | ∃ μ ν : M, (x, μ) ∈ compactOptimizerGraph U ∧
      (x, ν) ∈ compactOptimizerGraph U ∧ μ ≠ ν} := by
  let S := fun j : ℕ ↦ {p : X × (M × M) |
    (p.1, p.2.1) ∈ compactOptimizerGraph U ∧
    (p.1, p.2.2) ∈ compactOptimizerGraph U ∧
    1 ≤ ((j : ℝ) + 1) * dist p.2.1 p.2.2}
  have hS : ∀ j, IsClosed (S j) := by
    intro j
    exact ((isClosed_compactOptimizerGraph U hU).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
      (((isClosed_compactOptimizerGraph U hU).preimage
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).inter
        (isClosed_le continuous_const (continuous_const.mul
          ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd)))))
  have heq : {x | ∃ μ ν : M, (x, μ) ∈ compactOptimizerGraph U ∧
      (x, ν) ∈ compactOptimizerGraph U ∧ μ ≠ ν} = ⋃ j : ℕ, Prod.fst '' S j := by
    ext x
    constructor
    · rintro ⟨μ, ν, hμ, hν, hneq⟩
      obtain ⟨j, hj⟩ := positive_iff_exists_nat_mul_ge_one.mp (dist_pos.mpr hneq)
      exact mem_iUnion.mpr ⟨j, ⟨(x, μ, ν), ⟨hμ, hν, hj⟩, rfl⟩⟩
    · intro hx
      obtain ⟨j, p, hp, rfl⟩ := mem_iUnion.mp hx
      refine ⟨p.2.1, p.2.2, hp.1, hp.2.1, ?_⟩
      exact dist_pos.mp (positive_iff_exists_nat_mul_ge_one.mpr ⟨j, hp.2.2⟩)
  rw [heq]
  exact MeasurableSet.iUnion (fun j ↦ (isClosedMap_fst_of_compactSpace _ (hS j)).measurableSet)

/-- Strict inequalities for some optimizing law are Borel, even though the
optimizing law itself has not been chosen measurably. -/
theorem measurableSet_exists_compactOptimizer_strict_gap {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [CompactSpace M]
    (U V : X × M → ℝ) (hU : Continuous U) (hV : Continuous V) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < V (x, μ)} := by
  let S := fun j : ℕ ↦ compactOptimizerGraph U ∩ {p | 1 ≤ ((j : ℝ) + 1) * V p}
  have hS : ∀ j, IsClosed (S j) := fun j ↦
    (isClosed_compactOptimizerGraph U hU).inter
      (isClosed_le continuous_const (continuous_const.mul hV))
  have heq : {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < V (x, μ)} =
      ⋃ j : ℕ, Prod.fst '' S j := by
    ext x
    constructor
    · rintro ⟨μ, hμ, hVμ⟩
      obtain ⟨j, hj⟩ := positive_iff_exists_nat_mul_ge_one.mp hVμ
      exact mem_iUnion.mpr ⟨j, ⟨(x, μ), ⟨hμ, hj⟩, rfl⟩⟩
    · intro hx
      obtain ⟨j, p, hp, rfl⟩ := mem_iUnion.mp hx
      exact ⟨p.2, hp.1, positive_iff_exists_nat_mul_ge_one.mpr ⟨j, hp.2⟩⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun j ↦ (isClosedMap_fst_of_compactSpace _ (hS j)).measurableSet)

/-- Existence of an optimizing law outside any fixed closed law set is
Borel. Applied to the compact at-most-`m`-atom laws, this measures support
failure without assuming finite support of arbitrary optimizers. -/
theorem measurableSet_exists_compactOptimizer_outside_closed {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace M] [CompactSpace M]
    (U : X × M → ℝ) (hU : Continuous U) (F : Set M) (hF : IsClosed F) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} := by
  by_cases hne : F.Nonempty
  · have heq : {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} =
        {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ 0 < Metric.infDist μ F} := by
      ext x
      simp only [mem_setOf_eq, hF.notMem_iff_infDist_pos hne]
    rw [heq]
    exact measurableSet_exists_compactOptimizer_strict_gap U
      (fun p ↦ Metric.infDist p.2 F) hU ((Metric.continuous_infDist_pt F).comp continuous_snd)
  · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hne
    have heq : {x | ∃ μ : M, (x, μ) ∈ compactOptimizerGraph U ∧ μ ∉ F} =
        Prod.fst '' compactOptimizerGraph U := by
      ext x
      simp only [hFempty, mem_empty_iff_false, not_false_eq_true, and_true,
        mem_setOf_eq, mem_image]
      constructor
      · rintro ⟨μ, hμ⟩
        exact ⟨(x, μ), hμ, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.2, hp⟩
    rw [heq]
    exact (isClosedMap_fst_of_compactSpace _ (isClosed_compactOptimizerGraph U hU)).measurableSet

/-- Strict gaps on any closed compact-law relation are Borel after
projection. In particular, two different optimization constraints can be
imposed on a pair of laws before testing an ordinary likelihood gap. -/
theorem measurableSet_exists_closed_relation_strict_gap {X M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace M] [CompactSpace M]
    (R : Set (X × M)) (hR : IsClosed R)
    (V : X × M → ℝ) (hV : Continuous V) :
    MeasurableSet {x | ∃ μ : M, (x, μ) ∈ R ∧ 0 < V (x, μ)} := by
  let S := fun j : ℕ ↦ R ∩ {p | 1 ≤ ((j : ℝ) + 1) * V p}
  have hS : ∀ j, IsClosed (S j) := fun j ↦
    hR.inter (isClosed_le continuous_const (continuous_const.mul hV))
  have heq : {x | ∃ μ : M, (x, μ) ∈ R ∧ 0 < V (x, μ)} =
      ⋃ j : ℕ, Prod.fst '' S j := by
    ext x
    constructor
    · rintro ⟨μ, hμ, hVμ⟩
      obtain ⟨j, hj⟩ := positive_iff_exists_nat_mul_ge_one.mp hVμ
      exact mem_iUnion.mpr ⟨j, ⟨(x, μ), ⟨hμ, hj⟩, rfl⟩⟩
    · intro hx
      obtain ⟨j, p, hp, rfl⟩ := mem_iUnion.mp hx
      exact ⟨p.2, hp.1, positive_iff_exists_nat_mul_ge_one.mpr ⟨j, hp.2⟩⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun j ↦ (isClosedMap_fst_of_compactSpace _ (hS j)).measurableSet)

end ReweightedNPMLE
