import ReweightedNPMLE.DirichletSecondMoment
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Scale invariance behind Gamma--Dirichlet independence

The normalized Gamma vector is unchanged by a common positive rescaling.
This file first proves the corresponding exact scaling laws for scalar and
finite-product Gamma measures.  These are the measure-theoretic core of the
remaining independence statement in Proposition 2.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ReweightedNPMLE

/-- Scaling a shape--rate Gamma variable by `c > 0` divides its rate by `c`. -/
theorem gammaMeasure_map_mul_left {a r c : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    (gammaMeasure a r).map (fun x : ℝ ↦ c * x) =
      gammaMeasure a (r / c) := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure a (r / c)) :=
    isProbabilityMeasure_gammaMeasure ha (div_pos hr hc)
  have hmap := Measure.map_eq_of_mgf_eq_on_Ioo
    (μ := gammaMeasure a r) (μ' := gammaMeasure a (r / c))
    (fun x : ℝ ↦ c * x) id
    (l := -(r / c)) (u := r / c)
    (neg_lt_zero.mpr (div_pos hr hc)) (div_pos hr hc)
    (by fun_prop) aemeasurable_id
    (fun t ht ↦ by
      have hbase := integrable_exp_mul_gammaMeasure ha hr
        ((lt_div_iff₀ hc).mp ht.2)
      apply hbase.congr
      exact Filter.Eventually.of_forall fun x ↦ by
        congr 1
        ring)
    (fun t ht ↦ by
      simpa only [id_eq] using
        integrable_exp_mul_gammaMeasure ha (div_pos hr hc) ht.2)
    (fun t ht ↦ by
      change (∫ x : ℝ, Real.exp (t * (c * x)) ∂gammaMeasure a r) =
        ∫ x : ℝ, Real.exp (t * x) ∂gammaMeasure a (r / c)
      calc
        (∫ x : ℝ, Real.exp (t * (c * x)) ∂gammaMeasure a r) =
            ∫ x : ℝ, Real.exp ((t * c) * x) ∂gammaMeasure a r := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by ring_nf
        _ = (r / (r - t * c)) ^ a := by
          rw [gamma_mgf ha hr]
          exact (lt_div_iff₀ hc).mp ht.2
        _ = ((r / c) / (r / c - t)) ^ a := by
          congr 1
          field_simp [hc.ne']
        _ = ∫ x : ℝ, Real.exp (t * x) ∂gammaMeasure a (r / c) := by
          rw [gamma_mgf ha (div_pos hr hc) ht.2])
  simpa using hmap

/-- Exponential tilting of a shape--rate Gamma law by `x ↦ t x`
subtracts `t` from its rate. -/
theorem gammaMeasure_tilted_linear {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    (gammaMeasure a r).tilted (fun x : ℝ ↦ t * x) = gammaMeasure a (r - t) := by
  have hrt : 0 < r - t := sub_pos.mpr ht
  have htilt : Integrable (fun x : ℝ ↦ Real.exp (t * x)) (gammaMeasure a r) :=
    integrable_exp_mul_gammaMeasure ha hr ht
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure ((gammaMeasure a r).tilted (fun x : ℝ ↦ t * x)) :=
    isProbabilityMeasure_tilted htilt
  letI : IsProbabilityMeasure (gammaMeasure a (r - t)) :=
    isProbabilityMeasure_gammaMeasure ha hrt
  have hmap := Measure.map_eq_of_mgf_eq_on_Ioo
    (μ := (gammaMeasure a r).tilted (fun x : ℝ ↦ t * x))
    (μ' := gammaMeasure a (r - t)) id id
    (l := -(r - t) / 2) (u := (r - t) / 2)
    (by linarith) (by linarith) aemeasurable_id aemeasurable_id
    (fun s hs ↦ by
      rw [integrable_tilted_iff htilt]
      have hsr : t + s < r := by linarith [hs.2]
      have hi := integrable_exp_mul_gammaMeasure ha hr hsr
      apply hi.congr
      exact Filter.Eventually.of_forall fun x ↦ by
        simp only [id_eq, smul_eq_mul]
        rw [← Real.exp_add]
        congr 1
        ring)
    (fun s hs ↦ integrable_exp_mul_gammaMeasure ha hrt (by linarith [hs.2]))
    (fun s hs ↦ by
      change (∫ x : ℝ, Real.exp (s * x)
          ∂(gammaMeasure a r).tilted (fun x : ℝ ↦ t * x)) =
        ∫ x : ℝ, Real.exp (s * x) ∂gammaMeasure a (r - t)
      rw [integral_exp_tilted]
      simp only [Pi.add_apply]
      have hsr : t + s < r := by linarith [hs.2]
      have hden1 : 0 ≤ r / (r - (t + s)) :=
        (div_pos hr (sub_pos.mpr hsr)).le
      have hden2 : 0 ≤ r / (r - t) := (div_pos hr hrt).le
      rw [show (fun x : ℝ ↦ Real.exp (t * x + s * x)) =
          (fun x : ℝ ↦ Real.exp ((t + s) * x)) by
            funext x; congr 1 <;> ring,
        gamma_mgf ha hr hsr, gamma_mgf ha hr ht,
        gamma_mgf ha hrt (by linarith [hs.2]),
        ← Real.div_rpow hden1 hden2]
      congr 1
      have hden3 : r - t - s ≠ 0 := by linarith
      have heq : r - (t + s) = r - t - s := by ring
      rw [heq]
      field_simp [hr.ne', hrt.ne', hden3])
  simpa using hmap

/-- Product law of independent shape `a`, rate `r` Gamma coordinates. -/
noncomputable def gammaProductMeasure (n : ℕ) (a r : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gammaMeasure a r)

/-- Finite-dimensional Tonelli factorization for nonnegative coordinate
products.  This complements mathlib's real/complex Bochner version. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [lintegral_prod _ (by fun_prop)]
          have htail : Measurable
              (fun y : (i : Fin n) → E i.succ ↦ ∏ i, f i.succ (y i)) := by
            fun_prop
          calc
            (∫⁻ x : E 0, ∫⁻ y : (i : Fin n) → E i.succ,
                f 0 x * ∏ i, f i.succ (y i) ∂Measure.pi (fun i ↦ μ i.succ) ∂μ 0) =
                ∫⁻ x : E 0, f 0 x *
                  (∫⁻ y : (i : Fin n) → E i.succ, ∏ i, f i.succ (y i)
                    ∂Measure.pi (fun i ↦ μ i.succ)) ∂μ 0 := by
              apply lintegral_congr
              intro x
              exact lintegral_const_mul (f 0 x) htail
            _ = (∫⁻ x, f 0 x ∂μ 0) *
                ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
              rw [ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)]
              exact lintegral_mul_const _ (hf 0)
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- A finite product of absolutely continuous measures has density equal to
the product of the coordinate densities. -/
theorem pi_withDensity_prod_eq {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ENNReal)
    (hf : ∀ i, Measurable (f i)) (hftop : ∀ i x, f i x ≠ ⊤) :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  letI (i : Fin n) : SigmaFinite ((μ i).withDensity (f i)) :=
    SigmaFinite.withDensity_of_ne_top' (hftop i)
  apply Measure.pi_eq
  intro s hs
  have hspi : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hspi]
  rw [← lintegral_indicator hspi]
  have hind : (Set.pi Set.univ s).indicator (fun x ↦ ∏ i, f i (x i)) =
      (fun x ↦ ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · have hall : ∀ i, x i ∈ s i := by
        intro i
        exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
      simp [hall]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] using hx
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Set.indicator_of_notMem hi _
  rw [hind, lintegral_fin_prod_eq_prod _ (fun i ↦ (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

/-- Product density of independent shape `a`, rate `r` Gamma coordinates. -/
noncomputable def gammaProductDensity (n : ℕ) (a r : ℝ)
    (w : Fin n → ℝ) : ENNReal :=
  ∏ i, gammaPDF a r (w i)

/-- Real-valued version of the product Gamma density. -/
noncomputable def gammaProductDensityReal (n : ℕ) (a r : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  ∏ i, gammaPDFReal a r (w i)

theorem gammaProductDensity_eq_ofReal (n : ℕ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (w : Fin n → ℝ) :
    gammaProductDensity n a r w =
      ENNReal.ofReal (gammaProductDensityReal n a r w) := by
  unfold gammaProductDensity gammaProductDensityReal gammaPDF
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i hi
  exact gammaPDFReal_nonneg ha hr _

/-- Scalar density ratio identity under the multiplicative displacement
`w ↦ w(1+t)`. -/
theorem gammaPDFReal_mul_one_add {α w t : ℝ}
    (hw : 0 < w) (ht : 0 < 1 + t) :
    gammaPDFReal α α (w * (1 + t)) =
      gammaPDFReal α α w * (1 + t) ^ (α - 1) *
        Real.exp (-α * w * t) := by
  simp only [gammaPDFReal, if_pos hw.le, if_pos (mul_pos hw ht).le]
  rw [Real.mul_rpow hw.le ht.le]
  have hexp : Real.exp (-(α * (w * (1 + t)))) =
      Real.exp (-(α * w)) * Real.exp (-α * w * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Product-density ratio identity for the paper's coordinatewise
change-of-variables map. -/
theorem gammaProductDensityReal_mul_one_add {n : ℕ} {α : ℝ}
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ht : ∀ i, 0 < 1 + t i) :
    gammaProductDensityReal n α α (fun i ↦ w i * (1 + t i)) =
      gammaProductDensityReal n α α w *
        (∏ i, (1 + t i) ^ (α - 1)) *
          Real.exp (-α * ∑ i, w i * t i) := by
  unfold gammaProductDensityReal
  simp_rw [gammaPDFReal_mul_one_add (hw _) (ht _)]
  simp only [Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  ring

theorem measurable_gammaProductDensity (n : ℕ) (a r : ℝ) :
    Measurable (gammaProductDensity n a r) := by
  unfold gammaProductDensity gammaPDF
  fun_prop

/-- The independent Gamma product has the expected product density with
respect to Lebesgue measure on `ℝⁿ`. -/
theorem gammaProductMeasure_eq_volume_withDensity (n : ℕ) (a r : ℝ) :
    gammaProductMeasure n a r =
      volume.withDensity (gammaProductDensity n a r) := by
  rw [gammaProductMeasure, gammaMeasure, volume_pi]
  exact pi_withDensity_prod_eq
    (fun _i : Fin n ↦ gammaPDF a r)
    (fun _i ↦ (measurable_gammaPDFReal a r).ennreal_ofReal)
    (fun _i _x ↦ ENNReal.ofReal_ne_top)

/-- The product Gamma density integrates to one for positive shape and rate. -/
theorem lintegral_gammaProductDensity_eq_one (n : ℕ)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ w : Fin n → ℝ, gammaProductDensity n a r w ∂volume = 1 := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaProductMeasure n a r) := by
    dsimp [gammaProductMeasure]
    infer_instance
  have h : gammaProductMeasure n a r Set.univ = 1 := measure_univ
  rw [gammaProductMeasure_eq_volume_withDensity,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h

theorem gammaWeightMeasure_eq_gammaProductMeasure (n : ℕ) (α : ℝ) :
    gammaWeightMeasure n α = gammaProductMeasure n α α := rfl

/-- Tilting an independent Gamma product by its total mass changes the common
rate and nothing else. -/
theorem gammaProductMeasure_tilted_total
    (n : ℕ) {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    (gammaProductMeasure n a r).tilted (fun w ↦ t * total w) =
      gammaProductMeasure n a (r - t) := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaProductMeasure n a r) := by
    dsimp [gammaProductMeasure]
    infer_instance
  let d : Fin n → ℝ → ENNReal := fun _ x ↦
    ↑(NNReal.mk (Real.exp (t * x) /
      ∫ y : ℝ, Real.exp (t * y) ∂gammaMeasure a r) (by positivity))
  have hdmeas (i : Fin n) : Measurable (d i) := by
    dsimp [d]
    fun_prop
  have hdtop (i : Fin n) (x : ℝ) : d i x ≠ ⊤ := by
    simp [d]
  have hden :
      (∫ w : Fin n → ℝ, Real.exp (t * total w) ∂gammaProductMeasure n a r) =
        ∏ _i : Fin n, ∫ x : ℝ, Real.exp (t * x) ∂gammaMeasure a r := by
    change (∫ w : Fin n → ℝ, Real.exp (t * total w)
      ∂Measure.pi (fun _ : Fin n ↦ gammaMeasure a r)) = _
    rw [show (fun w : Fin n → ℝ ↦ Real.exp (t * total w)) =
        (fun w ↦ ∏ i : Fin n, Real.exp (t * w i)) by
      funext w
      rw [← Real.exp_sum]
      congr 1
      simp [total, Finset.mul_sum]]
    exact integral_fintype_prod_eq_prod
      (fun _i : Fin n ↦ fun x : ℝ ↦ Real.exp (t * x))
  have hdensity :
      (fun w : Fin n → ℝ ↦
        (↑(NNReal.mk (Real.exp (t * total w) /
          ∫ z : Fin n → ℝ, Real.exp (t * total z) ∂gammaProductMeasure n a r)
          (by positivity)) : ENNReal)) =
      (fun w ↦ ∏ i, d i (w i)) := by
    funext w
    dsimp [d]
    rw [← ENNReal.coe_finsetProd]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mk, NNReal.coe_prod]
    rw [hden, Finset.prod_div_distrib]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    simp [total, Finset.mul_sum]
  calc
    (gammaProductMeasure n a r).tilted (fun w ↦ t * total w) =
        (gammaProductMeasure n a r).withDensity
          (fun w ↦ ∏ i, d i (w i)) := by
      rw [tilted_eq_withDensity_nnreal]
      congr 1
    _ = Measure.pi (fun i : Fin n ↦ (gammaMeasure a r).withDensity (d i)) := by
      exact (pi_withDensity_prod_eq d hdmeas hdtop).symm
    _ = gammaProductMeasure n a (r - t) := by
      congr 1
      funext i
      calc
        (gammaMeasure a r).withDensity (d i) =
            (gammaMeasure a r).tilted (fun x : ℝ ↦ t * x) := by
          rw [tilted_eq_withDensity_nnreal]
        _ = gammaMeasure a (r - t) := by
          exact gammaMeasure_tilted_linear ha hr ht

/-- Common coordinatewise scaling divides the rate of an independent Gamma
product by the same factor. -/
theorem gammaProductMeasure_map_smul
    (n : ℕ) {a r c : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    (gammaProductMeasure n a r).map (fun w : Fin n → ℝ ↦ c • w) =
      gammaProductMeasure n a (r / c) := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure a (r / c)) :=
    isProbabilityMeasure_gammaMeasure ha (div_pos hr hc)
  have hpi := Measure.pi_map_pi
    (μ := fun _ : Fin n ↦ gammaMeasure a r)
    (f := fun _ : Fin n ↦ fun x : ℝ ↦ c * x)
    (fun _ ↦ (measurable_const.mul measurable_id).aemeasurable)
  change (Measure.pi (fun _ : Fin n ↦ gammaMeasure a r)).map
      (fun w : Fin n → ℝ ↦ c • w) =
    Measure.pi (fun _ : Fin n ↦ gammaMeasure a (r / c))
  rw [show (fun w : Fin n → ℝ ↦ c • w) =
      (fun w i ↦ c * w i) by rfl, hpi]
  congr 1
  funext i
  exact gammaMeasure_map_mul_left ha hr hc

/-- The law of the normalized Gamma vector does not depend on its common
positive rate. -/
theorem gammaProductMeasure_map_normalize_rate_invariant
    {n : ℕ} [Nonempty (Fin n)] {a r r' : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hr' : 0 < r') :
    (gammaProductMeasure n a r).map normalize =
      (gammaProductMeasure n a r').map normalize := by
  let c : ℝ := r / r'
  have hc : 0 < c := div_pos hr hr'
  have hscale := gammaProductMeasure_map_smul n ha hr hc
  have hrate : r / c = r' := by
    dsimp [c]
    field_simp [hr.ne', hr'.ne']
  rw [hrate] at hscale
  calc
    (gammaProductMeasure n a r).map normalize =
        (gammaProductMeasure n a r).map (normalize ∘ fun w : Fin n → ℝ ↦ c • w) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun w ↦ by
        simp only [Function.comp_apply, normalize_smul hc.ne']
    _ = ((gammaProductMeasure n a r).map (fun w : Fin n → ℝ ↦ c • w)).map
          normalize := by
      rw [Measure.map_map measurable_normalize]
      fun_prop
    _ = (gammaProductMeasure n a r').map normalize := by rw [hscale]

/-- Every common positive rate gives the same symmetric Dirichlet
pushforward after normalization. -/
theorem gammaProductMeasure_map_normalize_eq_symmetricDirichlet
    {n : ℕ} (hn : 0 < n) {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    (gammaProductMeasure n α r).map normalize =
      symmetricDirichletMeasure n α := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  calc
    (gammaProductMeasure n α r).map normalize =
        (gammaProductMeasure n α α).map normalize :=
      gammaProductMeasure_map_normalize_rate_invariant hα hr hα
    _ = symmetricDirichletMeasure n α := rfl

/-- A normalized event is invariant under every admissible exponential tilt
by the total mass.  This is the event-level form of scale--shape separation. -/
theorem gammaProduct_tilted_normalize_preimage
    {n : ℕ} (hn : 0 < n) {α t : ℝ} (hα : 0 < α) (ht : t < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    ((gammaProductMeasure n α α).tilted (fun w ↦ t * total w))
        (normalize ⁻¹' s) =
      gammaProductMeasure n α α (normalize ⁻¹' s) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hrate := gammaProductMeasure_map_normalize_rate_invariant
    (n := n) hα (sub_pos.mpr ht) hα
  rw [gammaProductMeasure_tilted_total n hα hα ht,
    ← Measure.map_apply measurable_normalize hs,
    ← Measure.map_apply measurable_normalize hs]
  exact congrArg (fun m : Measure (Fin n → ℝ) ↦ m s) hrate

/-- On an event determined by the normalized vector, the exponential moment
of the total mass factors into the event probability and the unconditional
exponential moment. -/
theorem gammaProduct_setIntegral_exp_total_normalize_preimage
    {n : ℕ} (hn : 0 < n) {α t : ℝ} (hα : 0 < α) (ht : t < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    (∫ w in normalize ⁻¹' s, Real.exp (t * total w)
        ∂gammaProductMeasure n α α) =
      (gammaProductMeasure n α α).real (normalize ⁻¹' s) *
        ∫ w, Real.exp (t * total w) ∂gammaProductMeasure n α α := by
  let μ := gammaProductMeasure n α α
  let E := normalize ⁻¹' s
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, gammaProductMeasure]
    infer_instance
  have hE : MeasurableSet E := hs.preimage measurable_normalize
  have hInt : Integrable (fun w : Fin n → ℝ ↦ Real.exp (t * total w)) μ := by
    simpa [μ, gammaWeightMeasure_eq_gammaProductMeasure] using
      integrable_exp_mul_total_gammaWeight n hα ht
  have hMpos : 0 < ∫ w : Fin n → ℝ, Real.exp (t * total w) ∂μ :=
    integral_exp_pos hInt
  have hEvt : (μ.tilted (fun w ↦ t * total w)) E = μ E := by
    simpa [μ, E] using
      gammaProduct_tilted_normalize_preimage (α := α) (t := t) hn hα ht hs
  have hofReal : ENNReal.ofReal
      (∫ w in E, Real.exp (t * total w) /
        (∫ z : Fin n → ℝ, Real.exp (t * total z) ∂μ) ∂μ) = μ E := by
    exact (tilted_apply_eq_ofReal_integral'
      (μ := μ) (fun w ↦ t * total w) hE).symm.trans hEvt
  have hnonneg : 0 ≤ ∫ w in E, Real.exp (t * total w) /
      (∫ z : Fin n → ℝ, Real.exp (t * total z) ∂μ) ∂μ := by
    apply integral_nonneg
    intro w
    positivity
  have hratio :
      (∫ w in E, Real.exp (t * total w) /
        (∫ z : Fin n → ℝ, Real.exp (t * total z) ∂μ) ∂μ) = μ.real E := by
    have h := congrArg ENNReal.toReal hofReal
    simpa only [ENNReal.toReal_ofReal hnonneg, Measure.real] using h
  rw [integral_div] at hratio
  have hfinal := (div_eq_iff hMpos.ne').mp hratio
  simpa [μ, E] using hfinal

/-- Restricting the Gamma product to an event determined by the normalized
vector scales, but otherwise does not alter, the law of the total mass. -/
theorem gammaProduct_total_restrict_normalize_preimage_map_eq
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    ((gammaProductMeasure n α α).restrict (normalize ⁻¹' s)).map total =
      gammaProductMeasure n α α (normalize ⁻¹' s) •
        (gammaProductMeasure n α α).map total := by
  let μ := gammaProductMeasure n α α
  let E := normalize ⁻¹' s
  let c : ENNReal := μ E
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, gammaProductMeasure]
    infer_instance
  letI : IsFiniteMeasure (μ.restrict E) := inferInstance
  letI : IsFiniteMeasure (c • μ) :=
    Measure.smul_finite μ (by dsimp [c]; exact measure_ne_top μ E)
  have hmap := Measure.map_eq_of_mgf_eq_on_Ioo
    (μ := μ.restrict E) (μ' := c • μ) total total
    (l := -α / 2) (u := α / 2)
    (by linarith) (by linarith) measurable_total.aemeasurable
    measurable_total.aemeasurable
    (fun t ht ↦ by
      have hbase : Integrable (fun w : Fin n → ℝ ↦ Real.exp (t * total w)) μ := by
        simpa [μ, gammaWeightMeasure_eq_gammaProductMeasure] using
          integrable_exp_mul_total_gammaWeight n hα (by linarith [ht.2])
      exact hbase.mono_measure Measure.restrict_le_self)
    (fun t ht ↦ by
      have hbase : Integrable (fun w : Fin n → ℝ ↦ Real.exp (t * total w)) μ := by
        simpa [μ, gammaWeightMeasure_eq_gammaProductMeasure] using
          integrable_exp_mul_total_gammaWeight n hα (by linarith [ht.2])
      exact hbase.smul_measure (by dsimp [c]; exact measure_ne_top μ E))
    (fun t ht ↦ by
      change (∫ w : Fin n → ℝ, Real.exp (t * total w) ∂μ.restrict E) =
        ∫ w : Fin n → ℝ, Real.exp (t * total w) ∂c • μ
      rw [integral_smul_measure]
      change (∫ w in E, Real.exp (t * total w) ∂μ) =
        (μ E).toReal * ∫ w, Real.exp (t * total w) ∂μ
      simpa [μ, E, Measure.real] using
        gammaProduct_setIntegral_exp_total_normalize_preimage
          (α := α) (t := t) hn hα (by linarith [ht.2]) hs)
  simpa [μ, E, c, Measure.map_smul] using hmap

/-- The normalized vector and total mass of independent shape--rate
`Gamma(α, α)` variables are independent. -/
theorem gammaProduct_normalize_indep_total
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    normalize ⟂ᵢ[gammaProductMeasure n α α] total := by
  let μ := gammaProductMeasure n α α
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, gammaProductMeasure]
    infer_instance
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hmap :
      (μ.restrict (normalize ⁻¹' s)).map total =
        μ (normalize ⁻¹' s) • μ.map total := by
    simpa [μ] using
      gammaProduct_total_restrict_normalize_preimage_map_eq hn hα hs
  have heval := congrArg (fun m : Measure ℝ ↦ m t) hmap
  dsimp only at heval
  rw [Measure.map_apply measurable_total ht,
    Measure.restrict_apply (ht.preimage measurable_total),
    Measure.smul_apply, Measure.map_apply measurable_total ht] at heval
  simpa [μ, inter_comm, smul_eq_mul] using heval

/-- The normalization and total of the Gamma weights in Proposition 2.1 are
independent. -/
theorem gammaWeight_normalize_indep_total
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    normalize ⟂ᵢ[gammaWeightMeasure n α] total := by
  simpa [gammaWeightMeasure_eq_gammaProductMeasure] using
    gammaProduct_normalize_indep_total hn hα

/-- Exact joint law in the Gamma--Dirichlet construction: normalized weights
have the symmetric Dirichlet law, the total has the stated Gamma law, and the
two components form a product measure. -/
theorem gammaWeight_normalize_total_joint_law
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    (gammaWeightMeasure n α).map (fun w ↦ (normalize w, total w)) =
      (symmetricDirichletMeasure n α).prod (gammaMeasure (n * α) α) := by
  letI : IsProbabilityMeasure (gammaWeightMeasure n α) :=
    gammaWeightMeasure_isProbability n hα
  calc
    (gammaWeightMeasure n α).map (fun w ↦ (normalize w, total w)) =
        ((gammaWeightMeasure n α).map normalize).prod
          ((gammaWeightMeasure n α).map total) :=
      (gammaWeight_normalize_indep_total hn hα).map_prod_eq_prod_map_map
        measurable_normalize.aemeasurable measurable_total.aemeasurable
    _ = (symmetricDirichletMeasure n α).prod
          (gammaMeasure (n * α) α) := by
      rw [total_gammaWeight_map_eq_gamma n hn hα]
      rfl

end ReweightedNPMLE
