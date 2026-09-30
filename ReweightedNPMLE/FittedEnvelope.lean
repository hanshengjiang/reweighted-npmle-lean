import ReweightedNPMLE.FittedRegularity
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic

/-!
# Envelope theorem for fitted likelihood values

The optimized weighted likelihood is a convex function of the weight vector.
The two optimizer inequalities squeeze its first-order remainder between zero
and a product involving the change in the fitted log-vector.  Consequently,
continuity of the fitted log-vector implies that it is the Fréchet derivative
of the optimal-value function.  Combining this envelope argument with the
local Lipschitz estimates from `FittedRegularity` gives the paper's gradient
identity on every locally bounded positive weight box.
-/

open Set Filter Asymptotics
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def fittedOptimalValue {n : ℕ}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) : ℝ :=
  weightedLogLikelihood w (vhat w)

noncomputable def fittedLogLinearFunctional {n : ℕ} (z : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, z i • ContinuousLinearMap.proj i

@[simp] theorem fittedLogLinearFunctional_apply {n : ℕ}
    (z h : Fin n → ℝ) :
    fittedLogLinearFunctional z h = ∑ i, h i * z i := by
  simp [fittedLogLinearFunctional, mul_comm]

theorem fittedOptimalValue_remainder_nonneg {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w u : Fin n → ℝ)
    (hw : IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hu : IsMaxOn C (weightedLogLikelihood u) (vhat u)) :
    0 ≤ fittedOptimalValue vhat u - fittedOptimalValue vhat w -
      weightedLogLikelihood (u - w) (vhat w) := by
  have hmax := hu.2 (vhat w) hw.1
  unfold fittedOptimalValue weightedLogLikelihood at hmax ⊢
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  linarith

theorem fittedOptimalValue_remainder_le {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w u : Fin n → ℝ)
    (hw : IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hu : IsMaxOn C (weightedLogLikelihood u) (vhat u)) :
    fittedOptimalValue vhat u - fittedOptimalValue vhat w -
        weightedLogLikelihood (u - w) (vhat w) ≤
      ∑ i, (u i - w i) *
        (Real.log (vhat u i) - Real.log (vhat w i)) := by
  have hmax := hw.2 (vhat u) hu.1
  unfold fittedOptimalValue weightedLogLikelihood at hmax ⊢
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  linarith

theorem fittedOptimalValue_convexOn_univ {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ w, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    ConvexOn ℝ Set.univ (fittedOptimalValue vhat) := by
  refine ⟨convex_univ, ?_⟩
  intro w _ u _ a b ha hb hab
  let q := a • w + b • u
  have hw := (hmax w).2 (vhat q) (hmax q).1
  have hu := (hmax u).2 (vhat q) (hmax q).1
  unfold fittedOptimalValue weightedLogLikelihood at hw hu ⊢
  simp only [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    ∑ i, (a * w i + b * u i) * Real.log (vhat q i) =
        a * (∑ i, w i * Real.log (vhat q i)) +
          b * (∑ i, u i * Real.log (vhat q i)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ a * (∑ i, w i * Real.log (vhat w i)) +
          b * (∑ i, u i * Real.log (vhat u i)) :=
      add_le_add (mul_le_mul_of_nonneg_left hw ha)
        (mul_le_mul_of_nonneg_left hu hb)
    _ = ∑ i, (a * (w i * Real.log (vhat w i)) +
        b * (u i * Real.log (vhat u i))) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

theorem abs_sum_mul_le_card_mul_norm {n : ℕ}
    (a b : Fin n → ℝ) :
    |∑ i, a i * b i| ≤ (n : ℝ) * ‖a‖ * ‖b‖ := by
  calc
    |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖a‖ * ‖b‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i)
        (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * ‖a‖ * ‖b‖ := by
      simp [mul_assoc]

theorem fittedOptimalValue_remainder_abs_le {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w u : Fin n → ℝ)
    (hw : IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hu : IsMaxOn C (weightedLogLikelihood u) (vhat u)) :
    |fittedOptimalValue vhat u - fittedOptimalValue vhat w -
        weightedLogLikelihood (u - w) (vhat w)| ≤
      (n : ℝ) * ‖u - w‖ *
        ‖(fun i ↦ Real.log (vhat u i)) -
          (fun i ↦ Real.log (vhat w i))‖ := by
  let r := fittedOptimalValue vhat u - fittedOptimalValue vhat w -
    weightedLogLikelihood (u - w) (vhat w)
  let b : Fin n → ℝ := fun i ↦
    Real.log (vhat u i) - Real.log (vhat w i)
  have hr0 : 0 ≤ r := fittedOptimalValue_remainder_nonneg vhat w u hw hu
  have hrle : r ≤ ∑ i, (u i - w i) * b i :=
    fittedOptimalValue_remainder_le vhat w u hw hu
  calc
    |r| = r := abs_of_nonneg hr0
    _ ≤ ∑ i, (u i - w i) * b i := hrle
    _ ≤ |∑ i, (u i - w i) * b i| := le_abs_self _
    _ ≤ (n : ℝ) * ‖u - w‖ * ‖b‖ :=
      abs_sum_mul_le_card_mul_norm (u - w) b
    _ = _ := rfl

theorem fittedOptimalValue_hasFDerivAt {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ)
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    (hzcont : ContinuousAt
      (fun u i ↦ Real.log (vhat u i)) w) :
    HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat w i))) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  let z : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun u i ↦ Real.log (vhat u i)
  have hz0 : Tendsto (fun h ↦ z (w + h) - z w) (𝓝 0) (𝓝 0) := by
    have hcomp : ContinuousAt (fun h ↦ z (w + h)) 0 := by
      apply hzcont.comp_of_eq
      · fun_prop
      · simp [z]
    have hconst : ContinuousAt (fun _h : Fin n → ℝ ↦ z w) 0 :=
      continuousAt_const
    have hsub := hcomp.sub hconst
    change Tendsto (fun h ↦ z (w + h) - z w) (𝓝 0)
      (𝓝 (z (w + 0) - z w)) at hsub
    simpa using hsub
  have heps : 0 < c / ((n : ℝ) + 1) := by positivity
  have hevent : ∀ᶠ h : Fin n → ℝ in 𝓝 0,
      ‖z (w + h) - z w‖ < c / ((n : ℝ) + 1) := by
    have hball := hz0 (Metric.ball_mem_nhds (0 : Fin n → ℝ) heps)
    filter_upwards [hball] with h hh
    simpa [Metric.mem_ball, dist_zero] using hh
  filter_upwards [hevent] with h hh
  have hrem := fittedOptimalValue_remainder_abs_le vhat w (w + h)
    (hmax w) (hmax (w + h))
  have hdiff : w + h - w = h := by abel
  have hcoef : (n : ℝ) * ‖z (w + h) - z w‖ ≤ c := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hnorm : 0 ≤ ‖z (w + h) - z w‖ := norm_nonneg _
    have hnlt : (n : ℝ) < (n : ℝ) + 1 := by linarith
    have := mul_lt_mul_of_pos_left hh (show (0 : ℝ) < n + 1 by positivity)
    rw [div_eq_mul_inv] at this
    have hden : ((n : ℝ) + 1) * (c * ((n : ℝ) + 1)⁻¹) = c := by
      field_simp
    rw [hden] at this
    nlinarith
  rw [fittedLogLinearFunctional_apply]
  have hlikelihood : weightedLogLikelihood h (vhat w) =
      ∑ i, h i * Real.log (vhat w i) := rfl
  rw [← hlikelihood]
  rw [hdiff] at hrem
  change ‖fittedOptimalValue vhat (w + h) - fittedOptimalValue vhat w -
      weightedLogLikelihood h (vhat w)‖ ≤ c * ‖h‖
  rw [Real.norm_eq_abs]
  calc
    |fittedOptimalValue vhat (w + h) - fittedOptimalValue vhat w -
        weightedLogLikelihood h (vhat w)| ≤
        (n : ℝ) * ‖h‖ * ‖z (w + h) - z w‖ := by
      simpa [z] using hrem
    _ = ‖h‖ * ((n : ℝ) * ‖z (w + h) - z w‖) := by ring
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)
    _ = c * ‖h‖ := mul_comm _ _

theorem canonicalFittedOptimalValue_hasFDerivAt {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (w : Fin n → ℝ)
    (hzcont : ContinuousAt
      (fittedLogSelection C hCcompact hCnonempty hCpos) w) :
    HasFDerivAt
      (fittedOptimalValue
        (fittedValueSelection C hCcompact hCnonempty hCpos))
      (fittedLogLinearFunctional
        (fittedLogSelection C hCcompact hCnonempty hCpos w)) w := by
  exact fittedOptimalValue_hasFDerivAt
    (fittedValueSelection C hCcompact hCnonempty hCpos) w
    (fun u ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos u)
    hzcont

theorem canonicalFittedOptimalValue_hasFDerivAt_of_local_bounds
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    {s : Set (Fin n → ℝ)} {w : Fin n → ℝ} (hws : s ∈ 𝓝 w)
    {a c B : ℝ} (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ u ∈ s, ∀ i, a ≤ u i)
    (hvc : ∀ u ∈ s, ∀ i,
      c ≤ fittedValueSelection C hCcompact hCnonempty hCpos u i)
    (hvB : ∀ u ∈ s, ∀ i,
      fittedValueSelection C hCcompact hCnonempty hCpos u i ≤ B) :
    HasFDerivAt
      (fittedOptimalValue
        (fittedValueSelection C hCcompact hCnonempty hCpos))
      (fittedLogLinearFunctional
        (fittedLogSelection C hCcompact hCnonempty hCpos w)) w := by
  apply canonicalFittedOptimalValue_hasFDerivAt
  have hlip := fittedLog_lipschitzOn hC hCpos
    (fittedValueSelection C hCcompact hCnonempty hCpos)
    ha hc hB hwa hvc hvB
    (fun u _hu ↦ fittedValueSelection_isMax
      C hCcompact hCnonempty hCpos u)
  exact hlip.continuousOn.continuousAt hws

/-- The canonical envelope identity at every positive weight.  Compact
positive fitted sets automatically provide all local coordinate bounds. -/
theorem canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    HasFDerivAt
      (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
      (fittedLogLinearFunctional (fittedLogSelection C hCcompact hCnonempty hCpos w)) w := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  obtain ⟨a, ha, s, hs, hwa⟩ := exists_local_positive_weight_lower_bound w hw
  apply canonicalFittedOptimalValue_hasFDerivAt_of_local_bounds C hC hCcompact hCnonempty hCpos
    hs ha hc hB hwa
  · intro u _ i
    exact (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).1
  · intro u _ i
    exact (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).2

theorem eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n) :
    ∀ᶠ q in nhds w,
      HasFDerivAt
        (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
        (fittedLogLinearFunctional (fittedLogSelection C hCcompact hCnonempty hCpos q)) q := by
  filter_upwards [(isOpen_positiveVectors n).mem_nhds hw] with q hq
  exact canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    C hC hCcompact hCnonempty hCpos q hq

end ReweightedNPMLE
