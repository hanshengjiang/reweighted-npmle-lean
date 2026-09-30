import ReweightedNPMLE.Localization
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators
open Set

namespace ReweightedNPMLE

theorem abs_le_sqrt_sum_sq {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    |u i| ≤ Real.sqrt (∑ j, u j ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)

theorem euclidean_norm_toLp_eq_sqrt_sum_sq {n : ℕ} (u : Fin n → ℝ) :
    ‖WithLp.toLp 2 u‖ = Real.sqrt (∑ i, u i ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [sq_abs]

theorem projection_pairing_le {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (ξ u : Fin n → ℝ) (η : ℝ)
    (hres : ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    ∑ i, ξ i * u i ≤
      ‖V.starProjection (WithLp.toLp 2 ξ)‖ *
          Real.sqrt (∑ i, u i ^ 2) +
        η * ‖WithLp.toLp 2 ξ‖ := by
  let X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 ξ
  let U : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u
  have hinner : inner ℝ X U =
      inner ℝ (V.starProjection X) U +
        inner ℝ X (U - V.starProjection U) := by
    rw [V.inner_starProjection_left_eq_right]
    rw [inner_sub_right, add_sub_cancel]
  have hfirst := real_inner_le_norm (V.starProjection X) U
  have hsecond := real_inner_le_norm X (U - V.starProjection U)
  have hsecond' : inner ℝ X (U - V.starProjection U) ≤ ‖X‖ * η :=
    hsecond.trans (mul_le_mul_of_nonneg_left hres (norm_nonneg X))
  have hnormU : ‖U‖ = Real.sqrt (∑ i, u i ^ 2) :=
    euclidean_norm_toLp_eq_sqrt_sum_sq u
  have hdot : inner ℝ X U = ∑ i, ξ i * u i := by
    simp [X, U, PiLp.inner_apply, mul_comm]
  rw [← hdot, hinner]
  change _ ≤ ‖V.starProjection X‖ * Real.sqrt (∑ i, u i ^ 2) + η * ‖X‖
  rw [← hnormU]
  calc
    _ ≤ ‖V.starProjection X‖ * ‖U‖ + ‖X‖ * η := add_le_add hfirst hsecond'
    _ = _ := by ring

theorem abs_log_one_add_sub_self_le {u : ℝ} (hu : |u| ≤ 1 / 16) :
    |Real.log (1 + u) - u| ≤ (16 / 15 : ℝ) * u ^ 2 := by
  have hu1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hseries := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 1
  norm_num [Finset.sum_range_succ] at hseries
  have hden : 0 < 1 - |u| := by positivity
  have hfrac : u ^ 2 / (1 - |u|) ≤ (16 / 15 : ℝ) * u ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg u, abs_nonneg u]
  simpa [sub_eq_add_neg, add_comm] using hseries.trans hfrac

theorem log_one_add_smul_ge {u a : ℝ} (hu : 0 < 1 + u)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a * Real.log (1 + u) ≤ Real.log (1 + a * u) := by
  have hconc := strictConcaveOn_log_Ioi.concaveOn
  have h := hconc.2 hu (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    ha0 (sub_nonneg.mpr ha1)
    (by ring : a + (1 - a) = 1)
  calc
    a * Real.log (1 + u) ≤
        Real.log (a * (1 + u) + (1 - a) * 1) := by
      simpa [smul_eq_mul] using h
    _ = Real.log (1 + a * u) := by congr 1 <;> ring

theorem radial_objective_upper {n : ℕ}
    (w u : Fin n → ℝ) (A E : ℝ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hu : ∀ i, |u i| ≤ 1 / 4)
    (hfirst : ∑ i, u i ≤ 0)
    (hpair : ∑ i, (w i - 1) * u i ≤
      A * Real.sqrt (∑ i, u i ^ 2) + E) :
    ∑ i, w i * Real.log (1 + u i) ≤
      A * Real.sqrt (∑ i, u i ^ 2) + E -
        (1 / 6 : ℝ) * ∑ i, u i ^ 2 := by
  have hwpos (i : Fin n) : 0 ≤ w i := by
    have hi := neg_le_of_abs_le (hw i)
    linarith
  calc
    ∑ i, w i * Real.log (1 + u i) ≤
        ∑ i, w i * (u i - u i ^ 2 / 3) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (log_one_add_le_sub_sq_third (hu i)) (hwpos i)
    _ = ∑ i, (u i + (w i - 1) * u i - w i * u i ^ 2 / 3) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, u i) + (∑ i, (w i - 1) * u i) -
        ∑ i, w i * u i ^ 2 / 3 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ ≤ (∑ i, (w i - 1) * u i) -
        (1 / 6 : ℝ) * ∑ i, u i ^ 2 := by
      have hsquare : (1 / 6 : ℝ) * ∑ i, u i ^ 2 ≤
          ∑ i, w i * u i ^ 2 / 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hi := neg_le_of_abs_le (hw i)
        have hs := sq_nonneg (u i)
        nlinarith
      linarith
    _ ≤ A * Real.sqrt (∑ i, u i ^ 2) + E -
        (1 / 6 : ℝ) * ∑ i, u i ^ 2 := by linarith

theorem radial_localization_sq {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (A E τ : ℝ) (hτ0 : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : A ≤ (1 / 16 : ℝ) / 24)
    (hE : E ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hpair : ∀ v ∈ U, ∑ i, (w i - 1) * v i ≤
      A * Real.sqrt (∑ i, v i ^ 2) + E)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : -τ ≤ ∑ i, w i * Real.log (1 + u i)) :
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
      ∑ i, u i ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ := by
  let x : ℝ := Real.sqrt (∑ i, u i ^ 2)
  have hsq : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (u i)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxSq : x ^ 2 = ∑ i, u i ^ 2 := Real.sq_sqrt hsq
  have hlocal : x < 1 / 16 := by
    by_contra hn
    have hρx : (1 / 16 : ℝ) ≤ x := le_of_not_gt hn
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hρx
    let a : ℝ := (1 / 16 : ℝ) / x
    let q : Fin n → ℝ := a • u
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one hxpos]
      exact hρx
    have hqU : q ∈ U := by
      have hc := hU hzero huU (sub_nonneg.mpr ha1) ha0
        (by ring : (1 - a) + a = 1)
      simpa [q] using hc
    have hqSq : ∑ i, q i ^ 2 = (1 / 16 : ℝ) ^ 2 := by
      calc
        ∑ i, q i ^ 2 = a ^ 2 * ∑ i, u i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [q]
          ring
        _ = a ^ 2 * x ^ 2 := by rw [hxSq]
        _ = (1 / 16 : ℝ) ^ 2 := by
          dsimp [a]
          field_simp
    have hqNorm : Real.sqrt (∑ i, q i ^ 2) = (1 / 16 : ℝ) := by
      rw [hqSq, Real.sqrt_sq]
      norm_num
    have hqabs : ∀ i, |q i| ≤ 1 / 4 := by
      intro i
      exact (abs_le_sqrt_sum_sq q i).trans (by rw [hqNorm]; norm_num)
    have hupper := radial_objective_upper w q A E hw hqabs
      (hfirst q hqU) (hpair q hqU)
    rw [hqNorm, hqSq] at hupper
    have hupper' : ∑ i, w i * Real.log (1 + q i) ≤
        -((1 / 16 : ℝ) ^ 2 / 12) := by
      calc
        ∑ i, w i * Real.log (1 + q i) ≤
            A * (1 / 16 : ℝ) + E - (1 / 6 : ℝ) * (1 / 16 : ℝ) ^ 2 := hupper
        _ ≤ -((1 / 16 : ℝ) ^ 2 / 12) := by nlinarith
    have hw0 (i : Fin n) : 0 ≤ w i := by
      have hi := neg_le_of_abs_le (hw i)
      linarith
    have hscale : a * (∑ i, w i * Real.log (1 + u i)) ≤
        ∑ i, w i * Real.log (1 + q i) := by
      calc
        a * (∑ i, w i * Real.log (1 + u i)) =
            ∑ i, w i * (a * Real.log (1 + u i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ∑ i, w i * Real.log (1 + a * u i) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (log_one_add_smul_ge (hupos i) ha0 ha1) (hw0 i)
        _ = ∑ i, w i * Real.log (1 + q i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [q]
    have hlower : -τ ≤ ∑ i, w i * Real.log (1 + q i) := by
      calc
        -τ ≤ a * (-τ) := by nlinarith
        _ ≤ a * (∑ i, w i * Real.log (1 + u i)) :=
          mul_le_mul_of_nonneg_left hnear ha0
        _ ≤ _ := hscale
    linarith
  have huabs : ∀ i, |u i| ≤ 1 / 4 := by
    intro i
    exact (abs_le_sqrt_sum_sq u i).trans
      (by dsimp [x] at hlocal; exact hlocal.le.trans (by norm_num))
  have hupper := radial_objective_upper w u A E hw huabs
    (hfirst u huU) (hpair u huU)
  change x < 1 / 16 at hlocal
  change (∑ i, w i * Real.log (1 + u i)) ≤
    A * x + E - (1 / 6 : ℝ) * (∑ i, u i ^ 2) at hupper
  have hquad : x ^ 2 ≤ 6 * (A * x + E + τ) := by
    rw [hxSq]
    linarith
  have hbound := radial_quadratic_bound hquad
  rw [hxSq] at hbound
  exact ⟨by simpa [x] using hlocal, hbound⟩

theorem radial_localization {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (A E τ : ℝ) (hE0 : 0 ≤ E) (hτ0 : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : A ≤ (1 / 16 : ℝ) / 24)
    (hE : E ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hpair : ∀ v ∈ U, ∑ i, (w i - 1) * v i ≤
      A * Real.sqrt (∑ i, v i ^ 2) + E)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : -τ ≤ ∑ i, w i * Real.log (1 + u i)) :
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
      ∑ i, u i ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ ∧
      0 ≤ -(∑ i, Real.log (1 + u i)) ∧
      -(∑ i, Real.log (1 + u i)) ≤
        37 * A ^ 2 + 13 * E + 13 * τ ∧
      ∑ i, Real.log (1 + u i) ^ 2 ≤
        72 * A ^ 2 + 24 * E + 24 * τ ∧
      ∑ i, (w i - 1) * Real.log (1 + u i) ≤
        37 * A ^ 2 + 13 * E + 12 * τ := by
  obtain ⟨hlocal, hsq⟩ := radial_localization_sq U hU hzero w u huU hupos
    A E τ hτ0 hw hA hE hfirst hpair hτ hnear
  let x : ℝ := Real.sqrt (∑ i, u i ^ 2)
  have hsumSq0 : 0 ≤ ∑ i, u i ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg (u i)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxSq : x ^ 2 = ∑ i, u i ^ 2 := Real.sq_sqrt hsumSq0
  have hu16 : ∀ i, |u i| ≤ 1 / 16 := by
    intro i
    exact (abs_le_sqrt_sum_sq u i).trans hlocal.le
  have hlogsum : ∑ i, Real.log (1 + u i) ≤ 0 := by
    calc
      ∑ i, Real.log (1 + u i) ≤ ∑ i, u i := by
        apply Finset.sum_le_sum
        intro i _
        simpa using Real.log_le_sub_one_of_pos (hupos i)
      _ ≤ 0 := hfirst u huU
  have hpairlogIdentity :
      ∑ i, (w i - 1) * Real.log (1 + u i) =
        (∑ i, (w i - 1) * u i) +
          ∑ i, (w i - 1) * (Real.log (1 + u i) - u i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrem : ∑ i, (w i - 1) * (Real.log (1 + u i) - u i) ≤
      (1 / 15 : ℝ) * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      (w i - 1) * (Real.log (1 + u i) - u i) ≤
          |w i - 1| * |Real.log (1 + u i) - u i| := by
        rw [← abs_mul]
        exact le_abs_self _
      _ ≤ (1 / 16 : ℝ) * |Real.log (1 + u i) - u i| :=
        mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)
      _ ≤ (1 / 16 : ℝ) * ((16 / 15 : ℝ) * u i ^ 2) :=
        mul_le_mul_of_nonneg_left
          (abs_log_one_add_sub_self_le (hu16 i)) (by norm_num)
      _ = (1 / 15 : ℝ) * u i ^ 2 := by ring
  have hpairlogRaw : ∑ i, (w i - 1) * Real.log (1 + u i) ≤
      A * x + E + (1 / 15 : ℝ) * x ^ 2 := by
    rw [hpairlogIdentity]
    change (∑ i, (w i - 1) * u i) +
        ∑ i, (w i - 1) * (Real.log (1 + u i) - u i) ≤ _
    have hp := hpair u huU
    change (∑ i, (w i - 1) * u i) ≤ A * x + E at hp
    rw [hxSq]
    linarith
  have hpairlog : ∑ i, (w i - 1) * Real.log (1 + u i) ≤
      37 * A ^ 2 + 13 * E + 12 * τ := by
    have hsq' : x ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ := by
      rw [hxSq]
      exact hsq
    nlinarith [sq_nonneg (x - 36 * A)]
  have hloss : -(∑ i, Real.log (1 + u i)) ≤
      37 * A ^ 2 + 13 * E + 13 * τ := by
    have hdecomp : ∑ i, w i * Real.log (1 + u i) =
        (∑ i, Real.log (1 + u i)) +
          ∑ i, (w i - 1) * Real.log (1 + u i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdecomp] at hnear
    linarith
  have hlogSq := sum_log_one_add_sq_le_two_sum_sq u hu16
  refine ⟨hlocal, hsq, by linarith, hloss, ?_, hpairlog⟩
  calc
    ∑ i, Real.log (1 + u i) ^ 2 ≤ 2 * ∑ i, u i ^ 2 := hlogSq
    _ ≤ 72 * A ^ 2 + 24 * E + 24 * τ := by linarith

theorem radial_localization_exact_cost {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (A E : ℝ) (hE0 : 0 ≤ E)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : A ≤ (1 / 16 : ℝ) / 24)
    (hE : E ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hpair : ∀ v ∈ U, ∑ i, (w i - 1) * v i ≤
      A * Real.sqrt (∑ i, v i ^ 2) + E)
    (hoptimal : 0 ≤ ∑ i, w i * Real.log (1 + u i)) :
    0 ≤ ∑ i, (w i - 1) * Real.log (1 + u i) ∧
      ∑ i, (w i - 1) * Real.log (1 + u i) ≤
        37 * A ^ 2 + 13 * E := by
  have hloc := radial_localization U hU hzero w u huU hupos A E 0
    hE0 (by positivity) hw hA hE hfirst hpair (by norm_num) (by simpa using hoptimal)
  rcases hloc with ⟨_, _, hloss0, _, _, hcost⟩
  have hdecomp : ∑ i, w i * Real.log (1 + u i) =
      (∑ i, Real.log (1 + u i)) +
        ∑ i, (w i - 1) * Real.log (1 + u i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdecomp] at hoptimal
  constructor
  · linarith
  · simpa using hcost

theorem radial_localization_of_projection {n : ℕ}
    (U : Set (Fin n → ℝ)) (hU : Convex ℝ U) (hzero : (0 : Fin n → ℝ) ∈ U)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ) (hη : 0 ≤ η)
    (hwidth : ∀ v ∈ U,
      ‖WithLp.toLp 2 v - V.starProjection (WithLp.toLp 2 v)‖ ≤ η)
    (w u : Fin n → ℝ) (huU : u ∈ U) (hupos : ∀ i, 0 < 1 + u i)
    (τ : ℝ) (hτ0 : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ≤
      (1 / 16 : ℝ) / 24)
    (hE : η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖ ≤
      (1 / 16 : ℝ) ^ 2 / 24)
    (hfirst : ∀ v ∈ U, ∑ i, v i ≤ 0)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : -τ ≤ ∑ i, w i * Real.log (1 + u i)) :
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
      ∑ i, u i ^ 2 ≤
        36 * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ^ 2 +
          12 * (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) + 12 * τ ∧
      0 ≤ -(∑ i, Real.log (1 + u i)) ∧
      -(∑ i, Real.log (1 + u i)) ≤
        37 * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ^ 2 +
          13 * (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) + 13 * τ ∧
      ∑ i, Real.log (1 + u i) ^ 2 ≤
        72 * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ^ 2 +
          24 * (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) + 24 * τ ∧
      ∑ i, (w i - 1) * Real.log (1 + u i) ≤
        37 * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ^ 2 +
          13 * (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) + 12 * τ := by
  apply radial_localization U hU hzero w u huU hupos
    ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) τ
    (mul_nonneg hη (norm_nonneg _)) hτ0 hw hA hE hfirst
  · intro v hv
    exact projection_pairing_le V (fun i ↦ w i - 1) v η (hwidth v hv)
  · exact hτ
  · exact hnear

end ReweightedNPMLE

