import ReweightedNPMLE.FittedEnvelope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE

/-- The scalar logarithm expansion used in the support-sensitivity argument. -/
theorem tendsto_log_one_add_sub_linear_div_sq (q : ℝ) :
    Tendsto (fun t : ℝ ↦ (Real.log (1 + t * q) - t * q) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (-(q ^ 2) / 2)) := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 + t * q) - t * q
  let f' : ℝ → ℝ := fun t ↦ q / (1 + t * q) - q
  let g : ℝ → ℝ := fun t ↦ t ^ 2
  let g' : ℝ → ℝ := fun t ↦ 2 * t
  have hden : ∀ᶠ t in nhds (0 : ℝ), 1 + t * q ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ ↦ 1 + t * q) 0 := by fun_prop
    simpa using hc.eventually_ne (y := (0 : ℝ)) (by norm_num)
  have hff' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt f (f' t) t := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hden] with t ht
    dsimp [f, f']
    convert (((hasDerivAt_id t).mul_const q).const_add 1).log ht |>.sub
      ((hasDerivAt_id t).mul_const q) using 1 <;> simp [id_eq]
  have hgg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt g (g' t) t := by
    filter_upwards [] with t
    dsimp [g, g']
    convert (hasDerivAt_id t).pow 2 using 1 <;> simp [id_eq]
  have hg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, g' t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht
  have hfa : Tendsto f (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt f 0 := by
      dsimp [f]
      exact (((hasDerivAt_id 0).mul_const q).const_add 1).log (by norm_num) |>.sub
        ((hasDerivAt_id 0).mul_const q) |>.continuousAt
    simpa [f] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hga : Tendsto g (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt g 0 := by
      dsimp [g]
      fun_prop
    simpa [g] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun t ↦ f' t / g' t) (nhdsWithin (0 : ℝ) {0}ᶜ)
      (nhds (-(q ^ 2) / 2)) := by
    have hc : Tendsto (fun t : ℝ ↦ -(q ^ 2) / (2 * (1 + t * q)))
        (nhdsWithin 0 {0}ᶜ) (nhds (-(q ^ 2) / 2)) := by
      have hcont : ContinuousAt (fun t : ℝ ↦ -(q ^ 2) / (2 * (1 + t * q))) 0 := by
        fun_prop (disch := norm_num)
      convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds hden] with t ht htden
    have ht0 : t ≠ 0 := by simpa using ht
    have htden' : 1 + q * t ≠ 0 := by simpa [mul_comm] using htden
    dsimp [f', g']
    field_simp [ht0, htden'] <;> ring
  exact HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv

/-- `log (1+tq) = tq - t²q²/2 + o(t²)` on the positive side. -/
theorem log_one_add_secondOrder_isLittleO (q : ℝ) :
    (fun t : ℝ ↦ Real.log (1 + t * q) - t * q +
        (t ^ 2 / 2) * q ^ 2) =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
  rw [isLittleO_iff_tendsto]
  · have hbase := (tendsto_log_one_add_sub_linear_div_sq q).mono_left
        (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ by
          intro t ht
          simp only [mem_compl_iff, mem_singleton_iff]
          exact ne_of_gt ht))
    have hadd : Tendsto
        (fun t : ℝ ↦ (Real.log (1 + t * q) - t * q) / t ^ 2 + q ^ 2 / 2)
        (nhdsWithin 0 (Ioi 0)) (nhds (-(q ^ 2) / 2 + q ^ 2 / 2)) :=
      hbase.add tendsto_const_nhds
    have hzero : -(q ^ 2) / 2 + q ^ 2 / 2 = 0 := by ring
    rw [hzero] at hadd
    apply hadd.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp [ht0]
  · intro t ht
    have ht0 : t = 0 := sq_eq_zero_iff.mp ht
    subst t
    simp

noncomputable def fittedLogFunctionalMap (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fittedLogLinearFunctional
    map_add' := by
      intro z y
      ext h
      simp only [fittedLogLinearFunctional_apply, Pi.add_apply,
        ContinuousLinearMap.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    map_smul' := by
      intro r z
      ext h
      simp [fittedLogLinearFunctional_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring }

@[simp] theorem fittedLogFunctionalMap_apply (n : ℕ)
    (z h : Fin n → ℝ) :
    fittedLogFunctionalMap n z h = ∑ i, h i * z i := by
  simp [fittedLogFunctionalMap, fittedLogLinearFunctional_apply]

noncomputable def fittedSecondDerivativeOfLogDerivative {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  (fittedLogFunctionalMap n).comp J

@[simp] theorem fittedSecondDerivativeOfLogDerivative_apply {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (h k : Fin n → ℝ) :
    fittedSecondDerivativeOfLogDerivative J h k = ∑ i, k i * J h i := by
  simp [fittedSecondDerivativeOfLogDerivative]

theorem hasFDerivAt_fittedLogLinearFunctional {n : ℕ}
    {z : (Fin n → ℝ) → (Fin n → ℝ)} {w : Fin n → ℝ}
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) :
    HasFDerivAt (fun u ↦ fittedLogLinearFunctional (z u))
      (fittedSecondDerivativeOfLogDerivative J) w := by
  have hcomp := (fittedLogFunctionalMap n).hasFDerivAt.comp w hz
  simpa [Function.comp_def, fittedSecondDerivativeOfLogDerivative] using hcomp

/-- Second-order expansion of the optimized value along a line, obtained by
composing its fitted-log derivative with the derivative of the fitted log. -/
theorem fittedValue_secondOrderExpansion {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    (hpsi : ∀ u, HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h : Fin n → ℝ) :
    (fun t : ℝ ↦ psi (w + t • h) - psi w -
        t * (∑ i, h i * z w i) -
        (t ^ 2 / 2) * (∑ i, h i * J h i)) =o[nhdsWithin 0 (Ioi 0)]
      (fun t : ℝ ↦ t ^ 2) := by
  have hsecond := hasFDerivAt_fittedLogLinearFunctional hz
  have ht := (convex_univ : Convex ℝ (Set.univ : Set (Fin n → ℝ))).taylor_approx_two_segment
    (f := psi) (f' := fun u ↦ fittedLogLinearFunctional (z u))
    (f'' := fittedSecondDerivativeOfLogDerivative J)
    (x := w) (v := (0 : Fin n → ℝ)) (w := h)
    (fun u _ ↦ hpsi u) (Set.mem_univ w)
    hsecond.hasFDerivWithinAt (by simp) (by simp)
  convert ht using 1
  ext t
  simp only [smul_zero, add_zero, fittedLogLinearFunctional_apply,
    fittedSecondDerivativeOfLogDerivative_apply, map_zero,
    ContinuousLinearMap.zero_apply]
  ring

/-- Local second-order envelope expansion.  Only the gradient identity in a
neighborhood of the base weight is needed, not differentiability at every
weight vector. -/
theorem fittedValue_secondOrderExpansion_of_eventually {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt psi (fittedLogLinearFunctional (z q)) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h : Fin n → ℝ) :
    (fun t : ℝ ↦ psi (w + t • h) - psi w -
        t * (∑ i, h i * z w i) -
        (t ^ 2 / 2) * (∑ i, h i * J h i)) =o[nhdsWithin 0 (Ioi 0)]
      (fun t : ℝ ↦ t ^ 2) := by
  let path : ℝ → (Fin n → ℝ) := fun t ↦ w + t • h
  let ell : ℝ := ∑ i, h i * z w i
  let H : ℝ := ∑ i, h i * J h i
  let a : ℝ → ℝ := fun t ↦ fittedLogLinearFunctional h (z (path t))
  let f : ℝ → ℝ := fun t ↦ psi (path t) - psi w - t * ell
  let f' : ℝ → ℝ := fun t ↦ a t - ell
  let g : ℝ → ℝ := fun t ↦ t ^ 2
  let g' : ℝ → ℝ := fun t ↦ 2 * t
  have hpath (t : ℝ) : HasDerivAt path h t := by
    simpa [path] using (hasDerivAt_id (x := t)).smul_const h |>.const_add w
  have htend : Tendsto path (nhds 0) (nhds w) := by
    simpa [path] using (hpath 0).continuousAt.tendsto
  have hnear : ∀ᶠ t in nhds (0 : ℝ),
      HasFDerivAt psi (fittedLogLinearFunctional (z (path t))) (path t) :=
    htend.eventually hpsi
  have hff' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt f (f' t) t := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear] with t ht
    have hc := ht.comp_hasDerivAt t (hpath t)
    have hd := (hc.sub_const (psi w)).sub ((hasDerivAt_id t).mul_const ell)
    simpa [f, f', a, Function.comp_def, fittedLogLinearFunctional_apply,
      mul_comm] using hd
  have hgg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, HasDerivAt g (g' t) t := by
    filter_upwards [] with t
    simpa [g, g', id_eq] using (hasDerivAt_id t).pow 2
  have hg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, g' t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht
  have hfa : Tendsto f (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hpsi0 := hpsi.self_of_nhds
    have hp0 : HasFDerivAt psi (fittedLogLinearFunctional (z w)) (path 0) := by
      simpa [path] using hpsi0
    have hc := (hp0.comp_hasDerivAt 0 (hpath 0)).continuousAt
    have hfcont : ContinuousAt f 0 := by
      exact (hc.sub continuousAt_const).sub (by fun_prop)
    simpa [f, path] using hfcont.tendsto.mono_left nhdsWithin_le_nhds
  have hga : Tendsto g (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt g 0 := by fun_prop
    simpa [g] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hz0 : HasFDerivAt z J (path 0) := by simpa [path] using hz
  have hline : HasDerivAt (fun t ↦ z (path t)) (J h) 0 := by
    simpa [Function.comp_def] using hz0.comp_hasDerivAt 0 (hpath 0)
  have ha : HasDerivAt a H 0 := by
    have hc := (fittedLogLinearFunctional h).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa [a, H, Function.comp_def, fittedLogLinearFunctional_apply, mul_comm] using hc
  have ha0 : a 0 = ell := by
    simp [a, path, ell, fittedLogLinearFunctional_apply, mul_comm]
  have hdiv : Tendsto (fun t ↦ f' t / g' t)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (H / 2)) := by
    have hs := ha.tendsto_slope_zero.div_const (2 : ℝ)
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    dsimp [f', g']
    simp only [zero_add, ha0, smul_eq_mul]
    field_simp [ht0]
  have hlim : Tendsto (fun t ↦ f t / t ^ 2)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (H / 2)) :=
    HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv
  rw [isLittleO_iff_tendsto]
  · have hbase := hlim.mono_left
        (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ by
          intro t ht
          exact ne_of_gt ht))
    have hsub : Tendsto (fun t ↦ f t / t ^ 2 - H / 2)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using hbase.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ H / 2)
          (nhdsWithin 0 (Ioi 0)) (nhds (H / 2)))
    apply hsub.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    dsimp [f, path, ell, H]
    field_simp [ht0]
  · intro t ht
    have ht0 : t = 0 := sq_eq_zero_iff.mp ht
    subst t
    simp

theorem fittedLogDerivative_symmetric {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    (hpsi : ∀ u, HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h k : Fin n → ℝ) :
    ∑ i, k i * J h i = ∑ i, h i * J k i := by
  have hsecond := hasFDerivAt_fittedLogLinearFunctional hz
  simpa only [fittedSecondDerivativeOfLogDerivative_apply] using
    second_derivative_symmetric hpsi hsecond h k

theorem fittedLogDerivative_symmetric_of_eventually {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w,
      HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) (h k : Fin n → ℝ) :
    ∑ i, k i * J h i = ∑ i, h i * J k i := by
  have hsecond := hasFDerivAt_fittedLogLinearFunctional hz
  simpa only [fittedSecondDerivativeOfLogDerivative_apply] using
    second_derivative_symmetric_of_eventually hpsi hsecond h k

theorem fittedLogDerivative_quadratic_nonneg {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J w)
    (h : Fin n → ℝ) :
    0 ≤ ∑ i, h i * J h i := by
  let z : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun u i ↦ Real.log (vhat u i)
  have hmono : ∀ u,
      0 ≤ ∑ i, (u i - w i) * (z u i - z w i) := by
    intro u
    exact fittedLog_monotone vhat
      (s := Set.univ) (fun q _ ↦ hmax q) u (Set.mem_univ u) w (Set.mem_univ w)
  have haffine : HasDerivAt (fun t : ℝ ↦ w + t • h) h 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (x := 0)).smul_const h |>.const_add w
  have hline : HasDerivAt (fun t : ℝ ↦ z (w + t • h)) (J h) 0 := by
    have hz0 : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J
        ((fun t : ℝ ↦ w + t • h) 0) := by simpa using hz
    have hcomp := hz0.comp_hasDerivAt 0 haffine
    convert hcomp using 1 <;> simp [z, Function.comp_def]
  have htendVec := hline.tendsto_slope_zero
  have htend : Tendsto
      (fun t : ℝ ↦ fittedLogLinearFunctional h
        (t⁻¹ • (z (w + (0 + t) • h) - z (w + 0 • h))))
      (𝓝[≠] 0) (𝓝 (fittedLogLinearFunctional h (J h))) := by
    have hcont : Tendsto (fittedLogLinearFunctional h) (𝓝 (J h))
        (𝓝 (fittedLogLinearFunctional h (J h))) :=
      (fittedLogLinearFunctional h).continuous.tendsto (J h)
    have hcomp := hcont.comp htendVec
    simpa [Function.comp_def] using hcomp
  have hnonneg : 0 ≤ fittedLogLinearFunctional h (J h) := by
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ht
    have hm := hmono (w + t • h)
    have hm' : 0 ≤ t * ∑ i, h i * (z (w + t • h) i - z w i) := by
      convert hm using 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have heq : fittedLogLinearFunctional h
        (t⁻¹ • (z (w + (0 + t) • h) - z (w + 0 • h))) =
        (t * ∑ i, h i * (z (w + t • h) i - z w i)) / t ^ 2 := by
      rw [fittedLogLinearFunctional_apply]
      simp only [zero_add, zero_smul, add_zero, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
      calc
        (∑ i, t⁻¹ * (z (w + t • h) i - z w i) * h i) =
            t⁻¹ * ∑ i, h i * (z (w + t • h) i - z w i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (t * ∑ i, h i * (z (w + t • h) i - z w i)) / t ^ 2 := by
          field_simp [htne]
    rw [heq]
    exact div_nonneg hm' (sq_nonneg t)
  simpa [fittedLogLinearFunctional_apply, mul_comm] using hnonneg

noncomputable def fittedLogDerivativeMatrix {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' J.toLinearMap

@[simp] theorem fittedLogDerivativeMatrix_mulVec {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (h : Fin n → ℝ) :
    fittedLogDerivativeMatrix J *ᵥ h = J h := by
  exact LinearMap.toMatrix'_mulVec J.toLinearMap h

theorem fittedLogDerivativeMatrix_isHermitian {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    (hpsi : ∀ u, HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) :
    (fittedLogDerivativeMatrix J).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  let e : Fin n → Fin n → ℝ := fun j ↦ (Pi.single j 1 : Fin n → ℝ)
  simp only [star_trivial, fittedLogDerivativeMatrix, LinearMap.toMatrix'_apply]
  change J (e i) j = J (e j) i
  have hsingle (a : Fin n → ℝ) (r : Fin n) :
      ∑ l, e r l * a l = a r := by
    rw [Finset.sum_eq_single r]
    · simp [e]
    · intro l _ hl
      simp [e, hl]
    · simp
  have hs := fittedLogDerivative_symmetric psi z hpsi hz
    (e j) (e i)
  calc
    J (e i) j = ∑ l, e j l * J (e i) l := (hsingle (J (e i)) j).symm
    _ = ∑ l, e i l * J (e j) l := hs.symm
    _ = J (e j) i := hsingle (J (e j)) i

theorem fittedLogDerivativeMatrix_isHermitian_of_eventually {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w,
      HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) :
    (fittedLogDerivativeMatrix J).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  let e : Fin n → Fin n → ℝ := fun j ↦ (Pi.single j 1 : Fin n → ℝ)
  simp only [star_trivial, fittedLogDerivativeMatrix, LinearMap.toMatrix'_apply]
  change J (e i) j = J (e j) i
  have hsingle (a : Fin n → ℝ) (r : Fin n) :
      ∑ l, e r l * a l = a r := by
    rw [Finset.sum_eq_single r]
    · simp [e]
    · intro l _ hl
      simp [e, hl]
    · simp
  have hs := fittedLogDerivative_symmetric_of_eventually psi z hpsi hz
    (e j) (e i)
  calc
    J (e i) j = ∑ l, e j l * J (e i) l := (hsingle (J (e i)) j).symm
    _ = ∑ l, e i l * J (e j) l := hs.symm
    _ = J (e j) i := hsingle (J (e j)) i

theorem fittedLogDerivativeMatrix_posSemidef {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    (psi : (Fin n → ℝ) → ℝ)
    (hpsi : ∀ u, HasFDerivAt psi
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat u i))) u)
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J w) :
    (fittedLogDerivativeMatrix J).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact fittedLogDerivativeMatrix_isHermitian psi
      (fun u i ↦ Real.log (vhat u i)) hpsi hz
  · intro h
    rw [fittedLogDerivativeMatrix_mulVec]
    simp only [star_trivial]
    simpa [dotProduct, mul_comm] using
      fittedLogDerivative_quadratic_nonneg vhat hmax hz h

theorem fittedLogDerivativeMatrix_posSemidef_of_eventually
    {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    (psi : (Fin n → ℝ) → ℝ) {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w, HasFDerivAt psi
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat u i))) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J w) :
    (fittedLogDerivativeMatrix J).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact fittedLogDerivativeMatrix_isHermitian_of_eventually psi
      (fun u i ↦ Real.log (vhat u i)) hpsi hz
  · intro h
    rw [fittedLogDerivativeMatrix_mulVec]
    simp only [star_trivial]
    simpa [dotProduct, mul_comm] using
      fittedLogDerivative_quadratic_nonneg vhat hmax hz h

end ReweightedNPMLE
