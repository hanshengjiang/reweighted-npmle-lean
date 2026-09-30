import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Integrating uniform conditional exceptional-event bounds

A measurable joint bad event whose sections have probability at most `eps`
off a data exceptional set has total probability at most the data failure
plus `eps`. The section bounds may come from arbitrary pointwise witnesses;
no measurable choice of those witnesses is required.
-/

open Set MeasureTheory
open scoped ENNReal

namespace ReweightedNPMLE

theorem measureReal_prod_le_of_uniform_section_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Set (X × Y)) (hE : MeasurableSet E)
    (D : Set X) (hD : MeasurableSet D) {eps : ℝ} (heps : 0 ≤ eps)
    (hsection : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ eps) :
    (P.prod Q).real E ≤ P.real D + eps := by
  let S := E ∩ (Dᶜ ×ˢ (univ : Set Y))
  have hS : MeasurableSet S := hE.inter (hD.compl.prod MeasurableSet.univ)
  have hSbound : (P.prod Q) S ≤ ENNReal.ofReal eps := by
    rw [Measure.prod_apply hS]
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal eps ∂P := by
        apply lintegral_mono
        intro x
        dsimp only
        by_cases hx : x ∈ D
        · have hpre : Prod.mk x ⁻¹' S = ∅ := by
            ext y
            simp only [S, mem_preimage, mem_inter_iff, mem_prod, mem_compl_iff,
              mem_univ, and_true, hx, not_true_eq_false, and_false, mem_empty_iff_false]
          rw [hpre, measure_empty]
          exact bot_le
        · have hsub : Prod.mk x ⁻¹' S ⊆ Prod.mk x ⁻¹' E := fun y hy ↦ hy.1
          have hh : Q (Prod.mk x ⁻¹' E) ≤ ENNReal.ofReal eps :=
            (ENNReal.le_ofReal_iff_toReal_le (by finiteness) heps).mpr (hsection x hx)
          exact (measure_mono hsub).trans hh
      _ = ENNReal.ofReal eps := by simp
  have hSreal : (P.prod Q).real S ≤ eps := by
    exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) heps).mp hSbound
  have hcover : E ⊆ (D ×ˢ (univ : Set Y)) ∪ S := by
    intro p hp
    by_cases hx : p.1 ∈ D
    · exact Or.inl ⟨hx, mem_univ p.2⟩
    · exact Or.inr ⟨hp, hx, mem_univ p.2⟩
  calc
    _ ≤ (P.prod Q).real ((D ×ˢ (univ : Set Y)) ∪ S) := measureReal_mono hcover
    _ ≤ (P.prod Q).real (D ×ˢ (univ : Set Y)) + (P.prod Q).real S :=
      measureReal_union_le _ _
    _ ≤ P.real D + eps := by
      rw [measureReal_prod_prod, probReal_univ, mul_one]
      linarith

/-- Absolute continuity is preserved by a finite homogeneous product.
This transfers the simultaneous Lebesgue-conull Gaussian event to the
joint sample law. -/
theorem absolutelyContinuous_finiteProduct {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ μ) ≪ Measure.pi (fun _ : Fin n ↦ ν) := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ X) 0).symm
      have hm : ((μ.prod (Measure.pi (fun _ : Fin n ↦ μ))).map e) =
          Measure.pi (fun _ : Fin (n + 1) ↦ μ) := by
        exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0).symm.map_eq
      have hn : ((ν.prod (Measure.pi (fun _ : Fin n ↦ ν))).map e) =
          Measure.pi (fun _ : Fin (n + 1) ↦ ν) := by
        exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ν) 0).symm.map_eq
      have hh := e.measurableEmbedding.absolutelyContinuous_map (h.prod ih)
      rw [hm, hn] at hh
      exact hh

end ReweightedNPMLE
