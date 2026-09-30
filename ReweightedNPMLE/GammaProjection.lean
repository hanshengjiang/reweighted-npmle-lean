import ReweightedNPMLE.DirichletIndependence
import ReweightedNPMLE.RadialLocalization
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace ReweightedNPMLE

theorem log_one_add_ge_sub_sq_half {u : ℝ}
    (hlower : -(1 / 2 : ℝ) ≤ u) :
    u - u ^ 2 ≤ Real.log (1 + u) := by
  let f : ℝ → ℝ := fun x ↦ Real.log (1 + x) - x + x ^ 2
  have hfderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt f (x * (1 + 2 * x) / (1 + x)) x := by
    intro x hx
    have hne : 1 + x ≠ 0 := by linarith
    have hlog := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hne
    convert (hlog.sub (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [Pi.add_apply, Pi.one_apply, id_eq] <;> field_simp <;> ring
  by_cases hu0 : 0 ≤ u
  · have hmono : MonotoneOn f (Set.Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      · intro x hx
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        exact div_nonneg (mul_nonneg hx.1.le (by linarith [hx.1])) (by linarith [hx.1])
    have h := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
    dsimp [f] at h
    norm_num at h
    linarith
  · have hule : u ≤ 0 := le_of_not_ge hu0
    have hanti : AntitoneOn f (Set.Icc u 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc u 0)
      · intro x hx
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        have hlin : 0 ≤ 1 + 2 * x := by linarith [hx.1]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hx.2.le hlin) (by linarith [hx.1])
    have h := hanti (left_mem_Icc.mpr hule) (right_mem_Icc.mpr hule) hule
    dsimp [f] at h
    norm_num at h
    linarith

theorem centered_gamma_mgf_le_exp_sq {α t : ℝ} (hα : 0 < α)
    (ht : |t| ≤ α / 2) :
    ∫ x, Real.exp (t * (x - 1)) ∂gammaMeasure α α ≤
      Real.exp (t ^ 2 / α) := by
  have htlt : t < α := by
    have := le_abs_self t
    linarith
  rw [centered_gamma_mgf hα htlt]
  let y : ℝ := t / α
  have hyabs : |y| ≤ 1 / 2 := by
    dsimp [y]
    rw [abs_div, abs_of_pos hα]
    exact (div_le_iff₀ hα).2 (by nlinarith)
  have hypos : 0 < 1 - y := by
    have := le_abs_self y
    linarith
  have hlog : -y - Real.log (1 - y) ≤ y ^ 2 := by
    have h := log_one_add_ge_sub_sq_half (u := -y) (by
      have := le_of_abs_le hyabs
      linarith)
    have h' : -y - y ^ 2 ≤ Real.log (1 - y) := by
      simpa [sub_eq_add_neg] using h
    linarith
  rw [Real.rpow_def_of_pos hypos]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [y] at hlog ⊢
  have hscaled := mul_le_mul_of_nonneg_left hlog hα.le
  field_simp [hα.ne'] at hscaled ⊢
  nlinarith

theorem gamma_linear_mgf_le {n : ℕ} {α lam : ℝ} (hα : 0 < α)
    (hlam : |lam| ≤ Real.sqrt α / 2) (v : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 ≤ 1) :
    ∫ w, Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1))
        ∂gammaProductMeasure n α α ≤ Real.exp (lam ^ 2) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let t : Fin n → ℝ := fun i ↦ lam * Real.sqrt α * v i
  have hαsqrt : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have habsv (i : Fin n) : |v i| ≤ 1 := by
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
    have : v i ^ 2 ≤ 1 := hi.trans hv
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  have ht (i : Fin n) : |t i| ≤ α / 2 := by
    rw [show |t i| = |lam| * Real.sqrt α * |v i| by
      simp [t, abs_mul, abs_of_nonneg (Real.sqrt_nonneg α)]]
    calc
      |lam| * Real.sqrt α * |v i| ≤
          (Real.sqrt α / 2) * Real.sqrt α * |v i| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlam (Real.sqrt_nonneg α)) (abs_nonneg _)
      _ ≤ (Real.sqrt α / 2) * Real.sqrt α * 1 := by
        exact mul_le_mul_of_nonneg_left (habsv i) (by positivity)
      _ = Real.sqrt α ^ 2 / 2 := by ring
      _ = α / 2 := by rw [hαsqrt]
  have htlt (i : Fin n) : t i < α := by
    have hi := le_abs_self (t i)
    linarith [ht i]
  have hfun : (fun w : Fin n → ℝ ↦
      Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1))) =
      (fun w ↦ ∏ i, Real.exp (t i * (w i - 1))) := by
    funext w
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [t]
    ring
  rw [hfun]
  change (∫ w, ∏ i, Real.exp (t i * (w i - 1))
      ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) ≤ _
  have hfactor :
      (∫ w, ∏ i, Real.exp (t i * (w i - 1))
        ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) =
      ∏ i, ∫ x, Real.exp (t i * (x - 1)) ∂gammaMeasure α α :=
    integral_fintype_prod_eq_prod
      (fun i : Fin n ↦ fun x : ℝ ↦ Real.exp (t i * (x - 1)))
  rw [hfactor]
  calc
    ∏ i, ∫ x, Real.exp (t i * (x - 1)) ∂gammaMeasure α α ≤
        ∏ i, Real.exp ((t i) ^ 2 / α) := by
      apply Finset.prod_le_prod
      · intro i _
        rw [centered_gamma_mgf hα (htlt i)]
        have hbase : 0 < 1 - t i / α := by
          rw [sub_pos, div_lt_one hα]
          exact htlt i
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hbase.le _)
      · intro i _
        exact centered_gamma_mgf_le_exp_sq hα (ht i)
    _ = Real.exp (∑ i, (t i) ^ 2 / α) := by rw [Real.exp_sum]
    _ ≤ Real.exp (lam ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsum : (∑ i, (t i) ^ 2 / α) = lam ^ 2 * ∑ i, v i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [t]
        rw [div_eq_iff hα.ne']
        rw [show (lam * Real.sqrt α * v i) ^ 2 =
          lam ^ 2 * Real.sqrt α ^ 2 * v i ^ 2 by ring, hαsqrt]
        ring
      rw [hsum]
      exact mul_le_of_le_one_right (sq_nonneg lam) hv

theorem integrable_gamma_linear_exp {n : ℕ} {α lam : ℝ} (hα : 0 < α)
    (hlam : |lam| ≤ Real.sqrt α / 2) (v : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 ≤ 1) :
    Integrable (fun w ↦
      Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1)))
      (gammaProductMeasure n α α) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  let t : Fin n → ℝ := fun i ↦ lam * Real.sqrt α * v i
  have hαsqrt : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  have habsv (i : Fin n) : |v i| ≤ 1 := by
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
    have hi' := hi.trans hv
    nlinarith [abs_nonneg (v i), sq_abs (v i)]
  have htlt (i : Fin n) : t i < α := by
    have ht : |t i| ≤ α / 2 := by
      rw [show |t i| = |lam| * Real.sqrt α * |v i| by
        simp [t, abs_mul, abs_of_nonneg (Real.sqrt_nonneg α)]]
      calc
        |lam| * Real.sqrt α * |v i| ≤
            (Real.sqrt α / 2) * Real.sqrt α * |v i| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlam (Real.sqrt_nonneg α)) (abs_nonneg _)
        _ ≤ (Real.sqrt α / 2) * Real.sqrt α * 1 := by
          exact mul_le_mul_of_nonneg_left (habsv i) (by positivity)
        _ = Real.sqrt α ^ 2 / 2 := by ring
        _ = α / 2 := by rw [hαsqrt]
    have hi := le_abs_self (t i)
    linarith
  have hprod : Integrable
      (fun w : Fin n → ℝ ↦ ∏ i, Real.exp (t i * (w i - 1)))
      (Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)) := by
    exact Integrable.fintype_prod fun i ↦
      integrable_centered_gamma_exp hα (htlt i)
  apply hprod.congr
  filter_upwards with w
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [t]
  ring

theorem gamma_linear_upper_tail {n : ℕ} {α u : ℝ}
    (hα : 0 < α) (hu : 0 < u) (huα : u ≤ Real.sqrt α)
    (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 ≤ 1) :
    (gammaProductMeasure n α α).real
        {w | u ≤ Real.sqrt α * ∑ i, v i * (w i - 1)} ≤
      Real.exp (-u ^ 2 / 4) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
    dsimp [gammaProductMeasure]
    infer_instance
  let lam : ℝ := u / 2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlamBound : |lam| ≤ Real.sqrt α / 2 := by
    rw [abs_of_pos hlam]
    exact div_le_div_of_nonneg_right huα (by norm_num)
  let X : (Fin n → ℝ) → ℝ := fun w ↦
    Real.sqrt α * ∑ i, v i * (w i - 1)
  have hint : Integrable (fun w ↦ Real.exp (lam * X w))
      (gammaProductMeasure n α α) := by
    simpa [X, mul_assoc] using
      integrable_gamma_linear_exp hα hlamBound v hv
  have hmark := exponential_markov_upper (gammaProductMeasure n α α)
    X hlam hint (c := u)
  have hmgf := gamma_linear_mgf_le hα hlamBound v hv
  change (gammaProductMeasure n α α).real {w | u ≤ X w} ≤ _
  calc
    (gammaProductMeasure n α α).real {w | u ≤ X w} ≤
        Real.exp (-lam * u) *
          ∫ w, Real.exp (lam * X w) ∂gammaProductMeasure n α α := hmark
    _ ≤ Real.exp (-lam * u) * Real.exp (lam ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [X, mul_assoc] using hmgf
      · positivity
    _ = Real.exp (-u ^ 2 / 4) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      ring

theorem gamma_projected_norm_tail_of_finite_net {n : ℕ} {α R q : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hRα : 4 * R ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hNunit : ∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1)
    (hnet : ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y)
    (hcard : (N.card : ℝ) * Real.exp (-R) ≤ Real.exp (-q)) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt R < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
    dsimp [gammaProductMeasure]
    infer_instance
  let μ := gammaProductMeasure n α α
  let E : ↥N → Set (Fin n → ℝ) := fun v ↦
    {w | 2 * Real.sqrt R ≤ Real.sqrt α *
      ∑ i, v.1 i * (w i - 1)}
  have hu : 0 < 2 * Real.sqrt R := mul_pos (by norm_num) (Real.sqrt_pos.2 hR)
  have huα : 2 * Real.sqrt R ≤ Real.sqrt α := by
    have hsqR := Real.sq_sqrt hR.le
    have hsqα := Real.sq_sqrt hα.le
    nlinarith [Real.sqrt_nonneg R, Real.sqrt_nonneg α]
  have hEtail (v : ↥N) : μ.real (E v) ≤ Real.exp (-R) := by
    have hv := hNunit v.1 v.2
    have htail := gamma_linear_upper_tail hα hu huα
      (fun i ↦ v.1 i) hv
    have hexp : -(2 * Real.sqrt R) ^ 2 / 4 = -R := by
      nlinarith [Real.sq_sqrt hR.le]
    rw [hexp] at htail
    change μ.real (E v) ≤ _
    simpa [μ, E] using htail
  have hsubset : {w : Fin n → ℝ |
      4 * Real.sqrt R < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ⊆
      ⋃ v : ↥N, E v := by
    intro w hwbad
    let X : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i ↦ w i - 1)
    let y : EuclideanSpace ℝ (Fin n) := V.starProjection X
    have hyV : y ∈ V := V.starProjection_apply_mem X
    obtain ⟨v, hvN, hvV, hvbound⟩ := hnet y hyV
    let vs : ↥N := ⟨v, hvN⟩
    apply Set.mem_iUnion.mpr
    refine ⟨vs, ?_⟩
    change 2 * Real.sqrt R ≤ Real.sqrt α *
      ∑ i, v i * (w i - 1)
    have hvfix : V.starProjection v = v :=
      Submodule.starProjection_eq_self_iff.mpr hvV
    have hinner : inner ℝ v y = ∑ i, v i * (w i - 1) := by
      calc
        inner ℝ v y = inner ℝ v (V.starProjection X) := rfl
        _ = inner ℝ (V.starProjection v) X :=
          (V.inner_starProjection_left_eq_right v X).symm
        _ = inner ℝ v X := by rw [hvfix]
        _ = ∑ i, v i * (w i - 1) := by
          simp [X, PiLp.inner_apply, mul_comm]
    have hscaled := mul_le_mul_of_nonneg_left hvbound (Real.sqrt_nonneg α)
    change 4 * Real.sqrt R < Real.sqrt α * ‖y‖ at hwbad
    rw [hinner] at hscaled
    nlinarith
  calc
    μ.real {w : Fin n → ℝ |
        4 * Real.sqrt R < Real.sqrt α *
          ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
        μ.real (⋃ v : ↥N, E v) := measureReal_mono hsubset (by finiteness)
    _ ≤ ∑ v : ↥N, μ.real (E v) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _v : ↥N, Real.exp (-R) := Finset.sum_le_sum fun v _ ↦ hEtail v
    _ = (N.card : ℝ) * Real.exp (-R) := by simp
    _ ≤ Real.exp (-q) := hcard

theorem card_mul_exp_neg_rank_log_five
    (Ncard r : ℕ) (q : ℝ) (hcard : Ncard ≤ 5 ^ r) :
    (Ncard : ℝ) * Real.exp (-((r : ℝ) * Real.log 5 + q)) ≤
      Real.exp (-q) := by
  have hcast : (Ncard : ℝ) ≤ (5 : ℝ) ^ r := by exact_mod_cast hcard
  calc
    (Ncard : ℝ) * Real.exp (-((r : ℝ) * Real.log 5 + q)) ≤
        (5 : ℝ) ^ r * Real.exp (-((r : ℝ) * Real.log 5 + q)) :=
      mul_le_mul_of_nonneg_right hcast (Real.exp_pos _).le
    _ = Real.exp ((r : ℝ) * Real.log 5) *
        Real.exp (-((r : ℝ) * Real.log 5 + q)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
    _ = Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem gamma_projected_norm_tail {n r : ℕ} {α q : ℝ}
    (hα : 0 < α) (hq : 0 < (r : ℝ) * Real.log 5 + q)
    (hscale : 4 * ((r : ℝ) * Real.log 5 + q) ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hNcard : N.card ≤ 5 ^ r)
    (hNunit : ∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1)
    (hnet : ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt ((r : ℝ) * Real.log 5 + q) < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by
  apply gamma_projected_norm_tail_of_finite_net hα hq hscale V N
    hNunit hnet
  exact card_mul_exp_neg_rank_log_five N.card r q hNcard

/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/

/-- A half-separated subset of a finite-dimensional unit sphere has at most `5 ^ d` points.
This is the standard disjoint-ball volume argument behind the paper's net bound. -/
theorem half_separated_sphere_card_le_five_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (C : Finset E)
    (hSphere : ∀ x ∈ C, ‖x‖ = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (1 / 2 : ℝ) < dist x y) :
    C.card ≤ 5 ^ Module.finrank ℝ E := by
  have hdisj : (C : Set E).PairwiseDisjoint
      (fun x ↦ Metric.ball x (1 / 4 : ℝ)) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by nlinarith [hsep x hx y hy hxy])
  have hunion : (⋃ x ∈ C, Metric.ball x (1 / 4 : ℝ)) ⊆
      Metric.ball (0 : E) (5 / 4 : ℝ) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx⟩ := hz
    obtain ⟨hxC, hzx⟩ := hx
    rw [Metric.mem_ball] at hzx ⊢
    rw [dist_zero_right]
    calc
      ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < (1 / 4 : ℝ) + 1 := by
        rw [hSphere x hxC]
        simpa [dist_eq_norm] using hzx
      _ = 5 / 4 := by norm_num
  have hmeasure :
      ∑ x ∈ C, volume (Metric.ball x (1 / 4 : ℝ)) ≤
        volume (Metric.ball (0 : E) (5 / 4 : ℝ)) := by
    rw [← measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_ball)]
    exact measure_mono hunion
  simp_rw [Measure.addHaar_ball_of_pos volume _
    (by norm_num : (0 : ℝ) < 1 / 4)] at hmeasure
  rw [Measure.addHaar_ball_of_pos volume 0
    (by norm_num : (0 : ℝ) < 5 / 4)] at hmeasure
  simp only [Finset.sum_const, nsmul_eq_mul] at hmeasure
  let d := Module.finrank ℝ E
  have hb0 : volume (Metric.ball (0 : E) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : E) (by norm_num)).ne'
  have hbtop : volume (Metric.ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hcancel : (C.card : ENNReal) * ENNReal.ofReal ((1 / 4 : ℝ) ^ d) ≤
      ENNReal.ofReal ((5 / 4 : ℝ) ^ d) := by
    apply (ENNReal.mul_le_mul_iff_left hb0 hbtop).mp
    simpa only [d, mul_assoc] using hmeasure
  have hreal : (C.card : ℝ) ≤ (5 : ℝ) ^ d := by
    have h := ENNReal.toReal_le_of_le_ofReal
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) d) hcancel
    simpa [div_eq_mul_inv, mul_pow] using h
  exact_mod_cast hreal

/-- Every nontrivial finite-dimensional real inner-product space has an internal half-net of its
unit sphere with at most `5 ^ d` points. -/
theorem exists_half_sphere_net
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    ∃ N : Finset E,
      N.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ v ∈ N, ‖v‖ = 1) ∧
      ∀ u : E, ‖u‖ = 1 → ∃ v ∈ N, dist u v ≤ (1 / 2 : ℝ) := by
  let S : Set E := Metric.sphere (0 : E) 1
  obtain ⟨T, _hTS, hTfinite, hTcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := (1 / 4 : ℝ≥0)) (by norm_num) (isCompact_sphere (0 : E) 1)
  have hpack_le : Metric.packingNumber (1 / 2 : ℝ≥0) S ≤ T.encard := by
    calc
      Metric.packingNumber (1 / 2 : ℝ≥0) S =
          Metric.packingNumber (2 * (1 / 4 : ℝ≥0)) S := by norm_num
      _ ≤ Metric.externalCoveringNumber (1 / 4 : ℝ≥0) S :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ T.encard := hTcover.externalCoveringNumber_le_encard
  have hpack : Metric.packingNumber (1 / 2 : ℝ≥0) S ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hpack_le (Set.encard_lt_top_iff.mpr hTfinite))
  let C : Set E := Metric.maximalSeparatedSet (1 / 2 : ℝ≥0) S
  have hCfinite : C.Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [show C.encard = Metric.packingNumber (1 / 2 : ℝ≥0) S by
      exact Metric.encard_maximalSeparatedSet hpack]
    exact hpack
  let N : Finset E := hCfinite.toFinset
  have hNmem {x : E} : x ∈ N ↔ x ∈ C := hCfinite.mem_toFinset
  have hNunit : ∀ x ∈ N, ‖x‖ = 1 := by
    intro x hx
    have hxS : x ∈ S := Metric.maximalSeparatedSet_subset (hNmem.mp hx)
    simpa [S, Metric.mem_sphere, dist_zero_right] using hxS
  have hNsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → (1 / 2 : ℝ) < dist x y := by
    intro x hx y hy hxy
    have h := Metric.isSeparated_maximalSeparatedSet
      (hNmem.mp hx) (hNmem.mp hy) hxy
    change (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) < edist x y at h
    rw [edist_dist, ENNReal.coe_nnreal_eq] at h
    exact (ENNReal.ofReal_lt_ofReal_iff').mp h |>.1
  refine ⟨N, half_separated_sphere_card_le_five_pow N hNunit hNsep,
    hNunit, ?_⟩
  intro u hu
  have huS : u ∈ S := by simpa [S, Metric.mem_sphere, dist_zero_right]
  obtain ⟨v, hvC, huv⟩ := Metric.isCover_maximalSeparatedSet hpack huS
  refine ⟨v, hNmem.mpr hvC, ?_⟩
  change edist u v ≤ (↑(1 / 2 : ℝ≥0) : ℝ≥0∞) at huv
  rw [edist_dist, ENNReal.coe_nnreal_eq] at huv
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp huv

/-- A half-net controls the norm by twice one of its directional inner products. -/
theorem exists_half_directional_net
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    ∃ N : Finset E,
      N.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ v ∈ N, ‖v‖ = 1) ∧
      ∀ y : E, ∃ v ∈ N, ‖y‖ ≤ 2 * inner ℝ v y := by
  obtain ⟨N, hNcard, hNunit, hNcover⟩ := exists_half_sphere_net (E := E)
  refine ⟨N, hNcard, hNunit, ?_⟩
  intro y
  by_cases hy : y = 0
  · obtain ⟨z, hz⟩ := exists_ne (0 : E)
    let u : E := (‖z‖⁻¹ : ℝ) • z
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hz
    obtain ⟨v, hvN, _hvdist⟩ := hNcover u hu
    exact ⟨v, hvN, by simp [hy]⟩
  · let u : E := (‖y‖⁻¹ : ℝ) • y
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hy
    obtain ⟨v, hvN, hvdist⟩ := hNcover u hu
    have hv : ‖v‖ = 1 := hNunit v hvN
    have hdistnorm : ‖u - v‖ ≤ (1 / 2 : ℝ) := by
      simpa [dist_eq_norm] using hvdist
    have hnormsq := norm_sub_sq_real u v
    have hsquare : ‖u - v‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      nlinarith [norm_nonneg (u - v)]
    have huv : (1 / 2 : ℝ) ≤ inner ℝ v u := by
      rw [hu, hv] at hnormsq
      rw [real_inner_comm]
      nlinarith
    have hyrep : y = ‖y‖ • u := by
      dsimp [u]
      rw [smul_smul]
      simp [hy]
    refine ⟨v, hvN, ?_⟩
    have hynorm : 0 ≤ ‖y‖ := norm_nonneg y
    have hinner : inner ℝ v y = ‖y‖ * inner ℝ v u := by
      calc
        inner ℝ v y = inner ℝ v (‖y‖ • u) := congrArg (inner ℝ v) hyrep
        _ = ‖y‖ * inner ℝ v u := by rw [inner_smul_right]
    rw [hinner]
    nlinarith

/-- A rank-`r` Euclidean subspace has the finite directional net required by the projected Gamma
concentration argument. The zero-dimensional case is handled by the singleton `{0}`. -/
theorem exists_submodule_directional_net {n r : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hrank : Module.finrank ℝ V ≤ r) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      N.card ≤ 5 ^ r ∧
      (∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1) ∧
      ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y := by
  classical
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    obtain ⟨Nsub, hNsubcard, hNsubunit, hNsubnet⟩ :=
      exists_half_directional_net (E := V)
    let N : Finset (EuclideanSpace ℝ (Fin n)) :=
      Nsub.image (fun v : V ↦ (v : EuclideanSpace ℝ (Fin n)))
    refine ⟨N, ?_, ?_, ?_⟩
    · calc
        N.card ≤ Nsub.card := Finset.card_image_le
        _ ≤ 5 ^ Module.finrank ℝ V := hNsubcard
        _ ≤ 5 ^ r := pow_le_pow_right' (by norm_num) hrank
    · intro v hv
      simp only [N, Finset.mem_image] at hv
      obtain ⟨z, hzN, rfl⟩ := hv
      rw [← EuclideanSpace.real_norm_sq_eq]
      have hzunit : ‖(z : EuclideanSpace ℝ (Fin n))‖ = 1 := hNsubunit z hzN
      rw [hzunit]
      norm_num
    · intro y hyV
      let ys : V := ⟨y, hyV⟩
      obtain ⟨v, hvNsub, hvbound⟩ := hNsubnet ys
      refine ⟨(v : EuclideanSpace ℝ (Fin n)), ?_, v.2, ?_⟩
      · exact Finset.mem_image.mpr ⟨v, hvNsub, rfl⟩
      · simpa [ys] using hvbound
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    refine ⟨{0}, ?_, ?_, ?_⟩
    · simp only [Finset.card_singleton]
      have : 0 < 5 ^ r := pow_pos (by norm_num) r
      omega
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      simp
    · intro y hyV
      refine ⟨0, Finset.mem_singleton_self 0, V.zero_mem, ?_⟩
      have hy0 : y = 0 := by
        exact congrArg Subtype.val (Subsingleton.elim (⟨y, hyV⟩ : V) 0)
      simp [hy0]

/-- The paper's projected Gamma concentration bound, requiring only a subspace rank bound. -/
theorem gamma_projected_norm_tail_of_finrank {n r : ℕ} {α q : ℝ}
    (hα : 0 < α) (hq : 0 < (r : ℝ) * Real.log 5 + q)
    (hscale : 4 * ((r : ℝ) * Real.log 5 + q) ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hrank : Module.finrank ℝ V ≤ r) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt ((r : ℝ) * Real.log 5 + q) < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by
  obtain ⟨N, hNcard, hNunit, hnet⟩ := exists_submodule_directional_net V hrank
  exact gamma_projected_norm_tail hα hq hscale V N hNcard hNunit hnet

end ReweightedNPMLE
